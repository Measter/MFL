use flagset::FlagSet;
use lexer::{BracketKind, Token, TokenKind};
use stores::{items::ItemId, source::Spanned};

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Basic, Control, OpCode, StructDef, StructDefField},
    lexer::{TokenTree, TreeGroup},
    stores::{
        diagnostics::Diagnostic,
        item::{ItemAttribute, LangItem},
        ops::OpId,
        signatures::StackDefItemUnresolved,
    },
    Stores,
};

use super::{
    matcher::{attribute_tokens, IsMatch, Matcher},
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
            TokenTree::Single(tk) => match tk.inner.kind {
                TokenKind::Extern => {
                    if attributes.contains(ItemAttribute::Extern) {
                        Diagnostic::warning(tk.location, "item already extern")
                            .attached(stores.diags, item_id);
                    }

                    attributes |= ItemAttribute::Extern;
                    prev_token = *tk;
                }
                TokenKind::Ident => {
                    Diagnostic::error(tk.location, "unknown attribute")
                        .attached(stores.diags, item_id);
                    had_error.set();
                }
                TokenKind::LangItem => {
                    let Ok(group) = token_iter
                        .expect_group(stores, item_id, BracketKind::Paren, prev_token)
                        .with_kinds(stores, item_id, TokenKind::Ident)
                        .with_length(stores, item_id, 1)
                    else {
                        // expect call already handled error.
                        continue;
                    };

                    let item_token = group.tokens[0].unwrap_single();
                    prev_token = group.last_token();

                    if let Some(prev_lang_item) = lang_item.replace(item_token.map(|t| t.lexeme)) {
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
        parse_item_body_contents(stores, &delim.tokens, parent_id).recover(had_error, Vec::new());

    // Makes later logic easier if we always have a prologue and epilogue.
    body.insert(
        0,
        stores.ops.new_op(
            OpCode::Basic(Basic::Control(Control::Prologue)),
            delim.open.map(|t| t.lexeme),
        ),
    );
    body.push(stores.ops.new_op(
        OpCode::Basic(Basic::Control(Control::Epilogue)),
        delim.last_token().map(|t| t.lexeme),
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
            TokenKind::Ident,
            attributes.last_token.location,
        )
        .recover(&mut had_error, attributes.last_token);

    let (generic_params, last_token) =
        try_parse_generic_pramas(stores, &mut had_error, token_iter, parent_id, name_token)
            .recover(&mut had_error, (Vec::new(), name_token));

    let entry_stack =
        parse_proc_entry_stack_def(stores, &mut had_error, token_iter, parent_id, last_token);

    let to_token = token_iter
        .expect_single(stores, parent_id, TokenKind::GoesTo, name_token.location)
        .recover(&mut had_error, name_token);

    let exit_stack = parse_stack_def(stores, &mut had_error, token_iter, parent_id, to_token);

    let has_body = token_iter.next_is_group(BracketKind::Brace);

    if !has_body {
        let (item_id, prev_def) = stores.items.new_function_decl(
            stores.sigs,
            &mut had_error,
            name_token.map(|t| t.lexeme),
            parent_id,
            attributes.attributes,
            entry_stack,
            exit_stack,
        );
        diagnostics::handle_symbol_redef_error(stores, &mut had_error, item_id, prev_def);
    } else {
        let (item_id, prev_def) = if generic_params.is_empty() {
            stores.items.new_function(
                stores.sigs,
                &mut had_error,
                name_token.map(|t| t.lexeme),
                parent_id,
                attributes.attributes,
                entry_stack.clone(),
                exit_stack,
            )
        } else {
            stores.items.new_generic_function(
                stores.sigs,
                &mut had_error,
                name_token.map(|t| t.lexeme),
                parent_id,
                attributes.attributes,
                entry_stack.clone(),
                exit_stack,
                generic_params,
            )
        };

        diagnostics::handle_symbol_redef_error(stores, &mut had_error, item_id, prev_def);

        for stack_def in entry_stack.inner {
            let StackDefItemUnresolved::Var { name, kind } = stack_def else {
                continue;
            };

            let (var_item_id, prev_def) = stores.items.new_variable(
                stores.sigs,
                &mut had_error,
                name,
                item_id,
                FlagSet::default(),
                kind,
            );
            diagnostics::handle_symbol_redef_error(stores, &mut had_error, var_item_id, prev_def);
        }

        if let Some(lang_item_id) = attributes.lang_item {
            stores.items.set_lang_item(lang_item_id, item_id);
        }

        let body = parse_item_body(stores, &mut had_error, token_iter, name_token, item_id);
        let body_block_id = stores.blocks.new_block(body);
        stores.items.set_item_body(item_id, body_block_id);
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
        .expect_single(stores, parent_id, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

    let (item_id, prev_def) = stores.items.new_assert(
        stores.sigs,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
    );
    diagnostics::handle_symbol_redef_error(stores, &mut had_error, item_id, prev_def);

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
        .expect_single(stores, parent_id, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

    let exit_stack = parse_stack_def(stores, &mut had_error, token_iter, parent_id, name_token);
    let exit_stack = exit_stack.map(|st| st.into_iter().collect());

    let (item_id, prev_def) = stores.items.new_const(
        stores.sigs,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        exit_stack,
    );
    diagnostics::handle_symbol_redef_error(stores, &mut had_error, item_id, prev_def);

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
            TokenKind::Ident,
            attributes.last_token.location,
        )
        .recover(&mut had_error, attributes.last_token);

    let Ok((variable_type, _)) = parse_unresolved_type(
        token_iter,
        stores,
        parent_id,
        name_token.location,
        &mut had_error,
    ) else {
        had_error.forget();
        return Err(());
    };

    let (var_item_id, prev_def) = stores.items.new_variable(
        stores.sigs,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        attributes.attributes,
        variable_type,
    );
    diagnostics::handle_symbol_redef_error(stores, &mut had_error, var_item_id, prev_def);

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
            TokenKind::Ident,
            attributes.last_token.location,
        )
        .recover(&mut had_error, attributes.last_token);

    let (generic_params, last_token) =
        try_parse_generic_pramas(stores, &mut had_error, token_iter, module_id, name_token)
            .recover(&mut had_error, (Vec::new(), name_token));

    let fallback = TreeGroup::fallback(BracketKind::Brace, last_token);

    let (item_id, prev_def) = stores.items.new_struct(
        stores.sigs,
        &mut had_error,
        module_id,
        name_token.map(|t| t.lexeme),
        !generic_params.is_empty(),
        attributes.attributes,
    );

    diagnostics::handle_symbol_redef_error(stores, &mut had_error, item_id, prev_def);

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
        if field_iter.next_is(TokenKind::Proc) {
            let keyword = field_iter.next().unwrap_single();
            if parse_function(stores, &mut field_iter, keyword, item_id).is_err() {
                had_error.set();
            }

            if field_iter.peek().is_none() {
                break;
            }
        } else if field_iter.next_is(Matcher("struct or union", |t: Spanned<TokenKind>| {
            if matches!(t.inner, TokenKind::Struct | TokenKind::Union) {
                IsMatch::Yes
            } else {
                IsMatch::No(t.inner.kind_str(), t.location)
            }
        })) {
            //
            let keyword = field_iter.next().unwrap_single();
            if parse_struct_or_union(stores, &mut field_iter, item_id, keyword).is_err() {
                had_error.set();
            }

            if field_iter.peek().is_none() {
                break;
            }
        } else {
            let name_token = field_iter
                .expect_single(stores, item_id, TokenKind::Ident, prev_token.location)
                .recover(&mut had_error, prev_token);

            let Ok((unresolved_store_type, last_token)) = parse_unresolved_type(
                &mut field_iter,
                stores,
                item_id,
                name_token.location,
                &mut had_error,
            ) else {
                break;
            };

            fields.push(StructDefField {
                name: name_token.map(|t| t.lexeme),
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
        name: name_token.map(|t| t.lexeme),
        fields,
        generic_params,
        is_union: keyword.inner.kind == TokenKind::Union,
    };

    stores.sigs.urir.set_struct(item_id, struct_def);

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
    let root_name = token_iter.expect_single(
        stores,
        module_id,
        Matcher("ident", |t: Spanned<TokenKind>| {
            if matches!(t.inner, TokenKind::Ident | TokenKind::ColonColon) {
                IsMatch::Yes
            } else {
                IsMatch::No(t.inner.kind_str(), t.location)
            }
        }),
        token.location,
    )?;

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
