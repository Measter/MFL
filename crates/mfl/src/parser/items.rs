use flagset::FlagSet;
use lasso::Spur;
use lexer::{BracketKind, Token};
use stores::{
    items::ItemId,
    source::{Spanned, WithSpan},
};

use crate::{
    error_signal::ErrorSignal,
    ir::{
        Arithmetic, Basic, Control, EnumDef, IdentPathRoot, OpCode, StructDef, StructDefField,
        UnresolvedIdent, UnresolvedOp, UnresolvedType,
    },
    lexer::{TokenTree, TreeGroup},
    stores::{
        diagnostics::Diagnostic,
        item::{ItemAttribute, LangItem},
        ops::OpId,
        signatures::StackDefItemUnresolved,
        types::{IntWidth, Integer},
    },
    Stores,
};

use super::{
    matcher::{attribute_tokens, IdentPathMatch, IsMatch, Matcher},
    parse_item_body_contents,
    utils::{
        parse_ident, parse_proc_entry_stack_def, parse_stack_def, parse_unresolved_type,
        try_parse_generic_pramas, validate_trailing_comma, TokenIter, TokenTreeOptionExt,
        TrailingCommaResult, TreeGroupResultExt,
    },
    Recover,
};

struct ParsedAttributes {
    attributes: FlagSet<ItemAttribute>,
    lang_item: Option<LangItem>,
    last_token: Spanned<Token>,
}
impl ParsedAttributes {
    fn fallback(prev_token: Spanned<Token>) -> Self {
        Self {
            attributes: FlagSet::default(),
            lang_item: None,
            last_token: prev_token,
        }
    }
}

fn try_get_attributes(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    prev_token: Spanned<Token>,
) -> Result<ParsedAttributes, ()> {
    if !token_iter.next_is_group(BracketKind::Paren) {
        return Ok(ParsedAttributes {
            attributes: FlagSet::default(),
            lang_item: None,
            last_token: prev_token,
        });
    }

    let mut had_error = ErrorSignal::new();
    let fallback = TreeGroup::fallback(BracketKind::Paren, prev_token);
    let attribute_group = token_iter
        .expect_group(stores, item_id, BracketKind::Paren, prev_token)
        .with_kinds(stores, item_id, Matcher("attribute", attribute_tokens))
        .recover(&mut had_error, &fallback);

    let mut attributes = FlagSet::default();
    let mut lang_item = None;

    let mut token_iter = TokenIter::new(attribute_group.tokens.iter());
    let mut prev_token = attribute_group.first_token();
    while let Some(token) = token_iter.next() {
        match token {
            TokenTree::Single(tk) => match tk.inner {
                Token::Extern => {
                    if attributes.contains(ItemAttribute::Extern) {
                        Diagnostic::warning(tk.location, "item already extern")
                            .attached(stores.diags, item_id);
                    }

                    attributes |= ItemAttribute::Extern;
                    prev_token = *tk;
                }
                Token::Ident => {
                    let lexeme = stores.source.get_str(tk.location);
                    match ItemAttribute::from_str(lexeme) {
                        Some(i) => {
                            if attributes.contains(i) {
                                Diagnostic::warning(tk.location, "item already has this attribute")
                                    .attached(stores.diags, item_id);
                            }
                            attributes |= i;
                        }
                        None => {
                            Diagnostic::error(tk.location, "unknown attribute")
                                .attached(stores.diags, item_id);
                            had_error.set();
                        }
                    }

                    prev_token = *tk;
                }
                Token::LangItem => {
                    let Ok(group) = token_iter
                        .expect_group(stores, item_id, BracketKind::Paren, prev_token)
                        .with_kinds(stores, item_id, Token::Ident)
                        .with_length(stores, item_id, 1)
                    else {
                        // expect call already handled error.
                        continue;
                    };

                    let item_token = group.tokens[0].unwrap_single();
                    prev_token = group.last_token();
                    let item_token_lexeme = stores.get_lexeme(item_token.location);

                    if let Some(prev_lang_item) = lang_item.replace(item_token_lexeme) {
                        Diagnostic::error(item_token.location, "multiple lang item attributes")
                            .with_help_label(prev_lang_item.location, "previously set here")
                            .attached(stores.diags, item_id);
                        had_error.set();
                    }
                }
                _ => unreachable!(),
            },
            TokenTree::Group(tg) => {
                Diagnostic::error(tg.span(), "expected attribute, found bracket group")
                    .attached(stores.diags, item_id);
                had_error.set()
            }
        }
    }

    let lang_item = lang_item.and_then(|li| {
        let string = stores.strings.resolve(li.inner);
        let Ok(lang_item) = LangItem::from_str(string) else {
            Diagnostic::error(li.location, format!("unknown lang item `{string}`"))
                .attached(stores.diags, item_id);
            had_error.set();
            return None;
        };
        Some(lang_item)
    });

    if had_error.into_err() {
        Err(())
    } else {
        Ok(ParsedAttributes {
            attributes,
            lang_item,
            last_token: attribute_group.last_token(),
        })
    }
}

fn parse_item_body(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    name_token: Spanned<Token>,
    parent_id: ItemId,
) -> Vec<OpId> {
    let fallback = TreeGroup::fallback(BracketKind::Brace, name_token);
    let delim = token_iter
        .expect_group(stores, parent_id, BracketKind::Brace, name_token)
        .recover(had_error, &fallback);

    let mut body =
        parse_item_body_contents(stores, &mut TokenIter::new(delim.tokens.iter()), parent_id)
            .recover(had_error, Vec::new());

    // Makes later logic easier if we always have a prologue and epilogue.
    body.insert(
        0,
        stores.ops.new_op(
            OpCode::Basic(Basic::Control(Control::Prologue)),
            delim.open.location,
        ),
    );
    body.push(stores.ops.new_op(
        OpCode::Basic(Basic::Control(Control::Epilogue)),
        delim.last_token().location,
    ));

    body
}

pub fn parse_function(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let attributes = try_get_attributes(stores, token_iter, parent_id, keyword)
        .recover(&mut had_error, ParsedAttributes::fallback(keyword));

    let name_token = token_iter
        .expect_single(
            stores,
            parent_id,
            Token::Ident,
            attributes.last_token.location,
        )
        .recover(&mut had_error, attributes.last_token);

    let (generic_params, last_token) =
        try_parse_generic_pramas(stores, &mut had_error, token_iter, parent_id, name_token)
            .recover(&mut had_error, (Vec::new(), name_token));

    let entry_stack =
        parse_proc_entry_stack_def(stores, &mut had_error, token_iter, parent_id, last_token);

    let to_token = token_iter
        .expect_single(stores, parent_id, Token::GoesTo, name_token.location)
        .recover(&mut had_error, name_token);

    let exit_stack = parse_stack_def(stores, &mut had_error, token_iter, parent_id, to_token);

    let has_body = token_iter.next_is_group(BracketKind::Brace);

    let function_name = stores.get_lexeme(name_token.location);
    if attributes.attributes.contains(ItemAttribute::Extern) && !has_body {
        stores.items.new_function_decl(
            stores.sigs,
            function_name,
            parent_id,
            attributes.attributes,
            entry_stack,
            exit_stack,
        );
    } else {
        let item_id = if generic_params.is_empty() {
            stores.items.new_function(
                stores.sigs,
                function_name,
                parent_id,
                attributes.attributes,
                entry_stack.clone(),
                exit_stack,
            )
        } else {
            stores.items.new_generic_function(
                stores.sigs,
                function_name,
                parent_id,
                attributes.attributes,
                entry_stack.clone(),
                exit_stack,
                generic_params,
            )
        };

        for stack_def in entry_stack.inner {
            let StackDefItemUnresolved::Var { name, kind } = stack_def else {
                continue;
            };

            stores
                .items
                .new_variable(stores.sigs, name, item_id, FlagSet::default(), kind);
        }

        if let Some(lang_item_id) = attributes.lang_item {
            stores.items.set_lang_item(lang_item_id, item_id);
        }

        if !attributes.attributes.contains(ItemAttribute::Extern) && !has_body {
            Diagnostic::error(name_token.location, "non-extern functions must have a body")
                .attached(stores.diags, item_id);
            had_error.set();
        } else {
            let body = parse_item_body(stores, &mut had_error, token_iter, name_token, item_id);
            let body_block_id = stores.blocks.new_block(body);
            stores.items.set_item_body(item_id, body_block_id);
        }
    }

    if had_error.into_err() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_assert(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let name_token = token_iter
        .expect_single(stores, parent_id, Token::Ident, keyword.location)
        .recover(&mut had_error, keyword);
    let assert_name = stores.get_lexeme(name_token.location);

    let item_id = stores.items.new_assert(stores.sigs, assert_name, parent_id);

    let body = parse_item_body(stores, &mut had_error, token_iter, name_token, item_id);
    let body_block_id = stores.blocks.new_block(body);
    stores.items.set_item_body(item_id, body_block_id);

    if had_error.into_err() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_const(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();
    let name_token = token_iter
        .expect_single(stores, parent_id, Token::Ident, keyword.location)
        .recover(&mut had_error, keyword);

    let exit_stack = parse_stack_def(stores, &mut had_error, token_iter, parent_id, name_token);
    let exit_stack = exit_stack.map(|st| st.into_iter().collect());
    let const_name = stores.get_lexeme(name_token.location);

    let item_id = stores
        .items
        .new_const(stores.sigs, const_name, parent_id, exit_stack);

    let body = parse_item_body(stores, &mut had_error, token_iter, name_token, item_id);
    let body_block_id = stores.blocks.new_block(body);
    stores.items.set_item_body(item_id, body_block_id);

    if had_error.into_err() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_variable(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let attributes = try_get_attributes(stores, token_iter, parent_id, keyword)
        .recover(&mut had_error, ParsedAttributes::fallback(keyword));

    let name_token = token_iter
        .expect_single(
            stores,
            parent_id,
            Token::Ident,
            attributes.last_token.location,
        )
        .recover(&mut had_error, attributes.last_token);

    let colon = token_iter
        .expect_single(stores, parent_id, Token::Colon, name_token.location)
        .recover(&mut had_error, name_token);

    let Ok((variable_type, _)) = parse_unresolved_type(
        token_iter,
        stores,
        parent_id,
        colon.location,
        &mut had_error,
    ) else {
        had_error.forget();
        return Err(());
    };

    let variable_name = stores.get_lexeme(name_token.location);
    stores.items.new_variable(
        stores.sigs,
        variable_name,
        parent_id,
        attributes.attributes,
        variable_type,
    );

    if had_error.into_err() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_struct_or_union(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    module_id: ItemId,
    keyword: Spanned<Token>,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let attributes = try_get_attributes(stores, token_iter, module_id, keyword)
        .recover(&mut had_error, ParsedAttributes::fallback(keyword));

    let name_token = token_iter
        .expect_single(
            stores,
            module_id,
            Token::Ident,
            attributes.last_token.location,
        )
        .recover(&mut had_error, attributes.last_token);

    let (generic_params, last_token) =
        try_parse_generic_pramas(stores, &mut had_error, token_iter, module_id, name_token)
            .recover(&mut had_error, (Vec::new(), name_token));

    let fallback = TreeGroup::fallback(BracketKind::Brace, last_token);
    let struct_name = stores.get_lexeme(name_token.location);

    let item_id = stores.items.new_struct(
        stores.sigs,
        module_id,
        struct_name,
        !generic_params.is_empty(),
        attributes.attributes,
    );

    if let Some(lang_item_id) = attributes.lang_item {
        stores.items.set_lang_item(lang_item_id, item_id);
    }

    let struct_body = token_iter
        .expect_group(stores, module_id, BracketKind::Brace, last_token)
        .recover(&mut had_error, &fallback);

    let mut field_iter = TokenIter::new(struct_body.tokens.iter());
    let mut fields = Vec::new();
    let mut prev_token = struct_body.first_token();

    loop {
        if field_iter.next_is(Token::Proc) {
            let keyword = field_iter.next().unwrap_single();
            if parse_function(stores, &mut field_iter, keyword, item_id).is_err() {
                had_error.set();
            }

            if field_iter.peek().is_none() {
                break;
            }
        } else if field_iter.next_is(Matcher("struct or union", |t: Spanned<Token>| {
            if matches!(t.inner, Token::Struct | Token::Union) {
                IsMatch::Yes
            } else {
                IsMatch::No(t.inner.kind_str(), t.location)
            }
        })) {
            let keyword = field_iter.next().unwrap_single();
            if parse_struct_or_union(stores, &mut field_iter, item_id, keyword).is_err() {
                had_error.set();
            }

            if field_iter.peek().is_none() {
                break;
            }
        } else if field_iter.next_is(Token::Enum) {
            let keyword = field_iter.next().unwrap_single();
            if parse_enum(stores, &mut field_iter, item_id, keyword).is_err() {
                had_error.set();
            }

            if field_iter.peek().is_none() {
                break;
            }
        } else {
            let name_token = field_iter
                .expect_single(stores, item_id, Token::Ident, prev_token.location)
                .recover(&mut had_error, prev_token);

            let colon = field_iter
                .expect_single(stores, item_id, Token::Colon, name_token.location)
                .recover(&mut had_error, name_token);

            let Ok((unresolved_store_type, last_token)) = parse_unresolved_type(
                &mut field_iter,
                stores,
                item_id,
                colon.location,
                &mut had_error,
            ) else {
                break;
            };

            let field_name = stores.get_lexeme(name_token.location);

            fields.push(StructDefField {
                name: field_name,
                kind: unresolved_store_type,
            });
            prev_token = last_token;

            if TrailingCommaResult::Break
                == validate_trailing_comma(
                    &mut field_iter,
                    stores,
                    &mut had_error,
                    item_id,
                    "fields",
                )
            {
                break;
            }
        }
    }

    let struct_def = StructDef {
        name: struct_name,
        fields,
        generic_params,
        is_union: keyword.inner == Token::Union,
    };

    stores.sigs.urir.set_struct(item_id, struct_def);

    if had_error.into_err() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_enum(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    module_id: ItemId,
    keyword: Spanned<Token>,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let attributes = try_get_attributes(stores, token_iter, module_id, keyword)
        .recover(&mut had_error, ParsedAttributes::fallback(keyword));

    let name_token = token_iter
        .expect_single(
            stores,
            module_id,
            Token::Ident,
            attributes.last_token.location,
        )
        .recover(&mut had_error, attributes.last_token);

    let fallback = TreeGroup::fallback(BracketKind::Brace, name_token);
    let enum_name = stores.get_lexeme(name_token.location);

    let item_id = stores
        .items
        .new_enum(stores.sigs, module_id, enum_name, attributes.attributes);

    if let Some(lang_item_id) = attributes.lang_item {
        stores.items.set_lang_item(lang_item_id, item_id);
    }

    let struct_body = token_iter
        .expect_group(stores, module_id, BracketKind::Brace, name_token)
        .recover(&mut had_error, &fallback);

    let mut variant_iter = TokenIter::new(struct_body.tokens.iter());
    let mut variants = Vec::new();
    let mut prev_token = struct_body.first_token();
    let mut prev_variant_ident: Option<Spanned<Spur>> = None;
    let u8_token = stores.strings.intern("u8");

    let const_exit_stack_type = UnresolvedType::Simple(UnresolvedIdent {
        span: name_token.location,
        path_root: IdentPathRoot::CurrentScope,
        path: vec![enum_name],
        generic_params: Vec::new(),
    });

    let pack_enum_op = OpCode::Complex(UnresolvedOp::PackEnum(UnresolvedType::Simple(
        UnresolvedIdent {
            span: name_token.location,
            path_root: IdentPathRoot::CurrentScope,
            path: vec![enum_name],
            generic_params: Vec::new(),
        },
    )));

    loop {
        if variant_iter.next_is(Token::Proc) {
            let keyword = variant_iter.next().unwrap_single();
            if parse_function(stores, &mut variant_iter, keyword, item_id).is_err() {
                had_error.set();
            }

            if variant_iter.peek().is_none() {
                break;
            }
        } else {
            // Parse a variant.
            let Ok(name_token) =
                variant_iter.expect_single(stores, item_id, Token::Ident, prev_token.location)
            else {
                // Invalid token.
                // Consume token so we can progress.
                if variant_iter.next().is_none() {
                    break;
                }

                continue;
            };

            prev_token = name_token;

            let exit_stack = vec![const_exit_stack_type.clone().with_span(name_token.location)]
                .with_span(name_token.location);

            let variant_name = stores.get_lexeme(name_token.location);

            let variant_const_id =
                stores
                    .items
                    .new_const(stores.sigs, variant_name, item_id, exit_stack);

            let const_body_id = if variant_iter.next_is_group(BracketKind::Brace) {
                let body_block = variant_iter.next().unwrap_group();
                let mut body = parse_item_body_contents(
                    stores,
                    &mut TokenIter::new(body_block.tokens.iter()),
                    variant_const_id,
                )
                .recover(&mut had_error, Vec::new());

                body.push(stores.ops.new_op(pack_enum_op.clone(), name_token.location));

                stores.blocks.new_block(body)
            } else if let Some(prev_ident) = prev_variant_ident {
                // Build up the body `<PREV> cast(u8) 1+`

                let prev_op = OpCode::Complex(UnresolvedOp::Ident(UnresolvedIdent {
                    span: name_token.location,
                    path_root: IdentPathRoot::CurrentScope,
                    path: vec![prev_ident.inner.with_span(name_token.location)],
                    generic_params: Vec::new(),
                }));

                let cast_op = OpCode::Complex(UnresolvedOp::Cast {
                    id: UnresolvedType::Simple(UnresolvedIdent {
                        span: name_token.location,
                        path_root: IdentPathRoot::CurrentScope,
                        path: vec![u8_token.with_span(name_token.location)],
                        generic_params: Vec::new(),
                    }),
                });

                let int_op = OpCode::Basic(Basic::PushInt {
                    width: IntWidth::I8,
                    value: Integer::Unsigned(1),
                });

                let plus_op = OpCode::Basic(Basic::Arithmetic(Arithmetic::Add));

                let body = vec![
                    stores.ops.new_op(prev_op, name_token.location),
                    stores.ops.new_op(cast_op, name_token.location),
                    stores.ops.new_op(int_op, name_token.location),
                    stores.ops.new_op(plus_op, name_token.location),
                    stores.ops.new_op(pack_enum_op.clone(), name_token.location),
                ];
                stores.blocks.new_block(body)
            } else {
                // We don't have a previous variant, so we just start at 0.
                let int_op = OpCode::Basic(Basic::PushInt {
                    width: IntWidth::I8,
                    value: Integer::Unsigned(0),
                });

                let body = vec![
                    stores.ops.new_op(int_op, name_token.location),
                    stores.ops.new_op(pack_enum_op.clone(), name_token.location),
                ];
                stores.blocks.new_block(body)
            };

            stores.items.set_item_body(variant_const_id, const_body_id);

            prev_variant_ident = Some(variant_name);
            variants.push((variant_name, variant_const_id));

            if TrailingCommaResult::Break
                == validate_trailing_comma(
                    &mut variant_iter,
                    stores,
                    &mut had_error,
                    item_id,
                    "variants",
                )
            {
                break;
            }
        }
    }

    let enum_def = EnumDef {
        name: enum_name,
        variants,
    };

    stores.sigs.urir.set_enum(item_id, enum_def);

    if had_error.into_err() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_import(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
    module_id: ItemId,
) -> Result<(), ()> {
    let root_name = token_iter.expect_single(stores, module_id, IdentPathMatch, token.location)?;

    let Ok((path, _)) = parse_ident(stores, had_error, module_id, token_iter, root_name) else {
        had_error.set();
        return Ok(());
    };

    stores
        .sigs
        .urir
        .get_scope_mut(module_id)
        .add_unresolved_import(path);

    Ok(())
}
