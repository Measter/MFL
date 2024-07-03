use ariadne::{Color, Label};
use lasso::Spur;
use tracing::debug_span;

use crate::{
    context::{make_symbol_redef_error, Context, ItemId, ItemKind, NameResolvedItemSignature},
    diagnostics,
    ir::{If, NameResolvedOp, Op, OpCode, TerminalBlock, UnresolvedIdent, UnresolvedOp, While},
    source_file::{FileId, Spanned, WithSpan},
    type_store::{
        BuiltinTypes, UnresolvedField, UnresolvedStruct, UnresolvedType, UnresolvedTypeIds,
        UnresolvedTypeTokens,
    },
    Stores,
};

fn resolved_single_ident(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
    ident: &UnresolvedIdent,
) -> Result<ItemId, ()> {
    let [first_ident, rest @ ..] = ident.path.as_slice() else {
        unreachable!()
    };

    let mut current_item = if ident.is_from_root {
        let Some(tlm) = ctx.get_top_level_module(first_ident.inner) else {
            let item_name = stores.strings.resolve(first_ident.inner);
            diagnostics::emit_error(
                stores,
                first_ident.location,
                format!("symbol `{item_name}` not found"),
                [Label::new(first_ident.location).with_color(Color::Red)],
                None,
            );
            *had_error = true;
            return Err(());
        };
        tlm
    } else {
        let header = ctx.get_item_header(cur_id);
        let Some(start_item) = ctx.get_visible_symbol(header, first_ident.inner) else {
            // TODO: Handle naming builtins here
            let item_name = stores.strings.resolve(first_ident.inner);
            diagnostics::emit_error(
                stores,
                first_ident.location,
                format!("symbol `{item_name}` not found"),
                [Label::new(first_ident.location).with_color(Color::Red)],
                None,
            );

            *had_error = true;
            return Err(());
        };
        start_item
    };

    let mut last_ident = *first_ident;
    for sub_ident in rest {
        let current_item_header = ctx.get_item_header(current_item);
        if current_item_header.kind != ItemKind::Module {
            diagnostics::emit_error(
                stores,
                sub_ident.location,
                "cannot path into non-module item",
                [
                    Label::new(sub_ident.location).with_color(Color::Red),
                    Label::new(last_ident.location)
                        .with_color(Color::Cyan)
                        .with_message("not a module"),
                ],
                None,
            );
            *had_error = true;
            return Err(());
        }

        let scope = ctx.nrir().get_scope(current_item_header.id);
        let Some(sub_item) = scope.get_symbol(sub_ident.inner) else {
            diagnostics::emit_error(
                stores,
                sub_ident.location,
                "symbol not found",
                [Label::new(sub_ident.location).with_color(Color::Red)],
                None,
            );
            *had_error = true;
            return Err(());
        };

        last_ident = *sub_ident;
        current_item = sub_item;
    }

    Ok(current_item)
}

fn resolve_idents_in_type(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
    unresolved_type: &UnresolvedTypeTokens,
    generic_params: Option<&[Spanned<Spur>]>,
) -> Result<UnresolvedTypeIds, ()> {
    let res = match unresolved_type {
        UnresolvedTypeTokens::Simple(unresolved_ident) => {
            let item_name = unresolved_ident
                .path
                .last()
                .expect("ICE: empty unresolved ident");

            let name = stores.strings.resolve(item_name.inner);
            let builtin_name = BuiltinTypes::from_name(name);

            if (unresolved_ident.path.len() > 1
                || unresolved_ident.is_from_root
                || unresolved_ident.generic_params.is_some())
                && builtin_name.is_some()
            {
                // Emit error
                diagnostics::emit_error(
                    stores,
                    unresolved_ident.span,
                    "cannot name builtin with a path",
                    [Label::new(unresolved_ident.span).with_color(Color::Red)],
                    None,
                );
                *had_error = true;
                return Err(());
            }

            if let Some(builtin) = builtin_name {
                UnresolvedTypeIds::SimpleBuiltin(builtin)
            } else if unresolved_ident.path.len() == 1
                && !unresolved_ident.is_from_root
                && unresolved_ident.generic_params.is_none()
                && generic_params
                    .and_then(|t| t.iter().find(|tp| tp.inner == item_name.inner))
                    .is_some()
            {
                UnresolvedTypeIds::SimpleGenericParam(*item_name)
            } else {
                let ident =
                    resolved_single_ident(ctx, stores, had_error, cur_id, unresolved_ident)?;

                match &unresolved_ident.generic_params {
                    Some(params) => {
                        let params: Vec<_> = params
                            .iter()
                            .map(|p| {
                                resolve_idents_in_type(
                                    ctx,
                                    stores,
                                    had_error,
                                    cur_id,
                                    p,
                                    generic_params,
                                )
                            })
                            .collect::<Result<_, _>>()?;

                        UnresolvedTypeIds::GenericInstance {
                            id: ident,
                            id_token: item_name.inner.with_span(unresolved_ident.span),
                            params,
                        }
                    }
                    None => UnresolvedTypeIds::SimpleCustom {
                        id: ident,
                        token: item_name.inner.with_span(unresolved_ident.span),
                    },
                }
            }
        }
        UnresolvedTypeTokens::Array(sub_type, length) => {
            let sub_type =
                resolve_idents_in_type(ctx, stores, had_error, cur_id, sub_type, generic_params)?;
            UnresolvedTypeIds::Array(Box::new(sub_type), *length)
        }
        UnresolvedTypeTokens::Pointer(sub_type) => {
            let sub_type =
                resolve_idents_in_type(ctx, stores, had_error, cur_id, sub_type, generic_params)?;
            UnresolvedTypeIds::Pointer(Box::new(sub_type))
        }
    };

    Ok(res)
}

fn resolve_idents_in_struct_def(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
    def: &UnresolvedStruct,
) -> UnresolvedStruct {
    let mut resolved = UnresolvedStruct {
        name: def.name,
        fields: Vec::new(),
        generic_params: def.generic_params.clone(),
        is_union: def.is_union,
    };

    for field in &def.fields {
        let UnresolvedType::Tokens(field_kind) = &field.kind else {
            unreachable!()
        };

        let Ok(new_kind) = resolve_idents_in_type(
            ctx,
            stores,
            had_error,
            cur_id,
            field_kind,
            def.generic_params.as_deref(),
        ) else {
            *had_error = true;
            continue;
        };

        resolved.fields.push(UnresolvedField {
            name: field.name,
            kind: UnresolvedType::Id(new_kind),
        });
    }

    resolved
}

fn resolve_idents_in_module_imports(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
) {
    let unresolved_imports = ctx.urir().get_scope(cur_id).imports().to_owned();

    for import in unresolved_imports {
        let Ok(resolved_item_id) = resolved_single_ident(ctx, stores, had_error, cur_id, &import)
        else {
            *had_error = true;
            continue;
        };

        let item_name = ctx.get_item_header(resolved_item_id).name;
        let resolved_scope = ctx.nrir_mut().get_scope_mut(cur_id);
        match resolved_scope
            .add_visible_symbol(item_name.inner.with_span(import.span), resolved_item_id)
        {
            Ok(_) => {}
            Err(prev_loc) => {
                *had_error = true;
                make_symbol_redef_error(stores, import.span, prev_loc);
            }
        }
    }
}

pub fn resolve_signature(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
) {
    let _span = debug_span!("Ident Resolve Signature", ?cur_id);

    let header = ctx.get_item_header(cur_id);
    match header.kind {
        ItemKind::StructDef => {
            let def = ctx.urir().get_struct(cur_id);
            let resolved = resolve_idents_in_struct_def(ctx, stores, had_error, cur_id, def);
            ctx.nrir_mut().set_struct(cur_id, resolved);
        }
        ItemKind::Memory => {
            let generic_params = match header.parent {
                Some(parent_id)
                    if ctx.get_item_header(parent_id).kind == ItemKind::GenericFunction =>
                {
                    Some(ctx.get_function_template_paramaters(parent_id))
                }
                _ => None,
            };

            let unresolved_memory_type = ctx.urir().get_memory_type(cur_id);

            let Ok(new_kind) = resolve_idents_in_type(
                ctx,
                stores,
                had_error,
                cur_id,
                unresolved_memory_type.inner,
                generic_params,
            ) else {
                *had_error = true;
                return;
            };

            ctx.nrir_mut().set_memory_type(cur_id, new_kind);
        }
        ItemKind::Module => {
            resolve_idents_in_module_imports(ctx, stores, had_error, cur_id);
        }
        // These are all treated the same.
        ItemKind::Assert | ItemKind::Const | ItemKind::Function | ItemKind::GenericFunction => {
            let unresolved_sig = ctx.urir().get_item_signature(cur_id);

            let generic_params = if header.kind == ItemKind::GenericFunction {
                Some(ctx.get_function_template_paramaters(cur_id))
            } else {
                None
            };

            let mut resolved_sig = NameResolvedItemSignature {
                exit: Vec::new(),
                entry: Vec::new(),
            };

            let mut local_had_error = false;

            let mut process_sig =
                |unresolved: &[Spanned<UnresolvedTypeTokens>],
                 resolved: &mut Vec<UnresolvedTypeIds>| {
                    for kind in unresolved {
                        let Ok(new_kind) = resolve_idents_in_type(
                            ctx,
                            stores,
                            had_error,
                            cur_id,
                            &kind.inner,
                            generic_params,
                        ) else {
                            local_had_error = true;
                            continue;
                        };

                        resolved.push(new_kind);
                    }
                };

            process_sig(&unresolved_sig.entry.inner, &mut resolved_sig.entry);
            process_sig(&unresolved_sig.exit.inner, &mut resolved_sig.exit);

            *had_error |= local_had_error;
            if local_had_error {
                return;
            }

            ctx.nrir_mut().set_item_signature(cur_id, resolved_sig);
        }
    };
}

fn resolve_idents_in_block(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
    block: &[Op<UnresolvedOp>],
    generic_params: Option<&[Spanned<Spur>]>,
) -> Vec<Op<NameResolvedOp>> {
    let mut resolved_block = Vec::with_capacity(block.len());

    for op in block {
        match &op.code {
            // These don't get resolved, so just copy it onward.
            OpCode::Basic(bo) => resolved_block.push(Op {
                code: OpCode::Basic(*bo),
                id: op.id,
                token: op.token,
            }),
            OpCode::Complex(comp) => match comp {
                UnresolvedOp::If(if_op) => {
                    let condition = resolve_idents_in_block(
                        ctx,
                        stores,
                        had_error,
                        cur_id,
                        &if_op.condition.block,
                        generic_params,
                    );
                    let then_block = resolve_idents_in_block(
                        ctx,
                        stores,
                        had_error,
                        cur_id,
                        &if_op.then_block.block,
                        generic_params,
                    );
                    let else_block = resolve_idents_in_block(
                        ctx,
                        stores,
                        had_error,
                        cur_id,
                        &if_op.else_block.block,
                        generic_params,
                    );

                    resolved_block.push(Op {
                        code: OpCode::Complex(NameResolvedOp::If(Box::new(If {
                            tokens: (),
                            condition: TerminalBlock {
                                block: condition,
                                is_terminal: false,
                            },
                            then_block: TerminalBlock {
                                block: then_block,
                                is_terminal: false,
                            },
                            else_block: TerminalBlock {
                                block: else_block,
                                is_terminal: false,
                            },
                        }))),
                        id: op.id,
                        token: op.token,
                    });
                }
                UnresolvedOp::While(while_op) => {
                    let condition = resolve_idents_in_block(
                        ctx,
                        stores,
                        had_error,
                        cur_id,
                        &while_op.condition.block,
                        generic_params,
                    );
                    let body = resolve_idents_in_block(
                        ctx,
                        stores,
                        had_error,
                        cur_id,
                        &while_op.body_block.block,
                        generic_params,
                    );

                    resolved_block.push(Op {
                        code: OpCode::Complex(NameResolvedOp::While(Box::new(While {
                            tokens: (),
                            condition: TerminalBlock {
                                block: condition,
                                is_terminal: false,
                            },
                            body_block: TerminalBlock {
                                block: body,
                                is_terminal: false,
                            },
                        }))),
                        id: op.id,
                        token: op.token,
                    });
                }

                UnresolvedOp::Cast { id } => {
                    let Ok(new_ty) =
                        resolve_idents_in_type(ctx, stores, had_error, cur_id, id, generic_params)
                    else {
                        *had_error = true;
                        continue;
                    };

                    resolved_block.push(Op {
                        code: OpCode::Complex(NameResolvedOp::Cast { id: new_ty }),
                        id: op.id,
                        token: op.token,
                    });
                }
                UnresolvedOp::PackStruct { id } => {
                    let Ok(new_ty) =
                        resolve_idents_in_type(ctx, stores, had_error, cur_id, id, generic_params)
                    else {
                        *had_error = true;
                        continue;
                    };

                    resolved_block.push(Op {
                        code: OpCode::Complex(NameResolvedOp::PackStruct { id: new_ty }),
                        id: op.id,
                        token: op.token,
                    });
                }
                UnresolvedOp::SizeOf { id } => {
                    let Ok(new_ty) =
                        resolve_idents_in_type(ctx, stores, had_error, cur_id, id, generic_params)
                    else {
                        *had_error = true;
                        continue;
                    };

                    resolved_block.push(Op {
                        code: OpCode::Complex(NameResolvedOp::SizeOf { id: new_ty }),
                        id: op.id,
                        token: op.token,
                    });
                }

                UnresolvedOp::Ident(ident) => {
                    let Ok(resolved_ident) =
                        resolved_single_ident(ctx, stores, had_error, cur_id, ident)
                    else {
                        continue;
                    };

                    let resolved_generic_params = ident.generic_params.as_ref().map(|v| {
                        let mut resolved_generic_params = Vec::new();
                        for param in v {
                            let Ok(f) = resolve_idents_in_type(
                                ctx,
                                stores,
                                had_error,
                                cur_id,
                                param,
                                generic_params,
                            ) else {
                                continue;
                            };

                            resolved_generic_params.push(f);
                        }
                        resolved_generic_params
                    });

                    let found_item_header = ctx.get_item_header(resolved_ident);
                    let new_code = match found_item_header.kind {
                        ItemKind::Const => NameResolvedOp::Const { id: resolved_ident },
                        ItemKind::Function | ItemKind::GenericFunction => {
                            // Generic functions can't get type resolved, only their instantiations.
                            // This means we'll need to abort type resolving our body on a generic call.
                            NameResolvedOp::CallFunction {
                                id: resolved_ident,
                                generic_params: resolved_generic_params,
                            }
                        }
                        ItemKind::Memory => NameResolvedOp::Memory {
                            id: resolved_ident,
                            is_global: found_item_header.parent.is_none(),
                        },

                        // This is the same as PackStruct
                        ItemKind::StructDef => {
                            let ty = UnresolvedTypeTokens::Simple(ident.clone());
                            let Ok(new_ty) = resolve_idents_in_type(
                                ctx,
                                stores,
                                had_error,
                                cur_id,
                                &ty,
                                generic_params,
                            ) else {
                                *had_error = true;
                                continue;
                            };

                            NameResolvedOp::PackStruct { id: new_ty }
                        }

                        ItemKind::Assert | ItemKind::Module => {
                            *had_error = true;
                            let mut labels =
                                vec![Label::new(op.token.location).with_color(Color::Red)];
                            // This would be the case if the item was a top-level mmodule.
                            let note = if found_item_header.name.location.file_id != FileId::dud() {
                                labels.push(
                                    Label::new(found_item_header.name.location)
                                        .with_color(Color::Cyan)
                                        .with_message(format!(
                                            "item is a {:?}",
                                            found_item_header.kind
                                        )),
                                );
                                String::new()
                            } else {
                                let name = stores.strings.resolve(found_item_header.name.inner);
                                format!("`{name}` is a top-level module")
                            };

                            diagnostics::emit_error(
                                stores,
                                op.token.location,
                                format!("cannot refer to a {:?} here", found_item_header.kind),
                                labels,
                                note,
                            );
                            continue;
                        }
                    };

                    resolved_block.push(Op {
                        code: OpCode::Complex(new_code),
                        id: op.id,
                        token: op.token,
                    });
                }
            },
        }
    }

    resolved_block
}

pub fn resolve_body(ctx: &mut Context, stores: &mut Stores, had_error: &mut bool, cur_id: ItemId) {
    let _span = debug_span!("Ident Resolve Body", ?cur_id);

    let header = ctx.get_item_header(cur_id);
    match header.kind {
        ItemKind::Memory | ItemKind::Module | ItemKind::StructDef => {
            // Nothing to do.
        }
        ItemKind::Assert | ItemKind::Const | ItemKind::Function | ItemKind::GenericFunction => {
            let generic_params = if header.kind == ItemKind::GenericFunction {
                Some(ctx.get_function_template_paramaters(cur_id))
            } else {
                None
            };

            let body = ctx.urir().get_item_body(cur_id);
            let resolved_body =
                resolve_idents_in_block(ctx, stores, had_error, cur_id, body, generic_params);
            ctx.nrir_mut().set_item_body(cur_id, resolved_body);
        }
    }
}
