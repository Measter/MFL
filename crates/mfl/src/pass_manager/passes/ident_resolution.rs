use ariadne::{Color, Label};
use lasso::Spur;

use crate::{
    diagnostics::{self, NameCollision},
    error_signal::ErrorSignal,
    ir::{
        Basic, Control, NameResolvedOp, NameResolvedType, OpCode, StructDef, StructDefField,
        UnresolvedIdent, UnresolvedOp, UnresolvedType,
    },
    pass_manager::PassManager,
    stores::{
        block::BlockId,
        item::{ItemId, ItemKind, ItemStore},
        signatures::NameResolvedItemSignature,
        source::{FileId, SourceLocation, Spanned, WithSpan},
        types::BuiltinTypes,
    },
    Stores,
};

fn invalid_generic_count_diag(
    stores: &mut Stores,
    error_span: SourceLocation,
    expected: usize,
    actual: usize,
    extra_labels: &[(SourceLocation, &str)],
) {
    let mut labels: Vec<_> = extra_labels
        .iter()
        .map(|(loc, msg)| Label::new(*loc).with_color(Color::Cyan).with_message(msg))
        .collect();
    labels.push(Label::new(error_span).with_color(Color::Red));

    diagnostics::emit_error(
        stores,
        error_span,
        format!("expected {expected} generic parameters, found {actual}",),
        labels,
        None,
    );
}

fn resolved_single_ident(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
    ident: &UnresolvedIdent,
) -> Result<ItemId, ()> {
    let [first_ident, rest @ ..] = ident.path.as_slice() else {
        unreachable!()
    };

    let mut current_item = if ident.is_from_root {
        let Some(tlm) = stores.items.get_top_level_module(first_ident.inner) else {
            let item_name = stores.strings.resolve(first_ident.inner);
            diagnostics::emit_error(
                stores,
                first_ident.location,
                format!("symbol `{item_name}` not found"),
                [Label::new(first_ident.location).with_color(Color::Red)],
                None,
            );
            had_error.set();
            return Err(());
        };
        tlm
    } else {
        let header = stores.items.get_item_header(cur_id);
        let Some(start_item) =
            stores
                .items
                .get_visible_symbol(stores.sigs, header, first_ident.inner)
        else {
            let item_name = stores.strings.resolve(first_ident.inner);
            diagnostics::emit_error(
                stores,
                first_ident.location,
                format!("symbol `{item_name}` not found"),
                [Label::new(first_ident.location).with_color(Color::Red)],
                None,
            );

            had_error.set();
            return Err(());
        };
        start_item
    };

    let mut last_ident = *first_ident;
    for sub_ident in rest {
        let current_item_header = stores.items.get_item_header(current_item);
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
            had_error.set();
            return Err(());
        }

        let scope = stores.sigs.nrir.get_scope(current_item_header.id);
        let Some(sub_item) = scope.get_symbol(sub_ident.inner) else {
            diagnostics::emit_error(
                stores,
                sub_ident.location,
                "symbol not found",
                [Label::new(sub_ident.location).with_color(Color::Red)],
                None,
            );
            had_error.set();
            return Err(());
        };

        last_ident = *sub_ident;
        current_item = sub_item;
    }

    Ok(current_item)
}

fn resolve_idents_in_type(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
    unresolved_type: &UnresolvedType,
    generic_params: &[Spanned<Spur>],
) -> Result<NameResolvedType, ()> {
    let res = match unresolved_type {
        UnresolvedType::Simple(unresolved_ident) => {
            let item_name = unresolved_ident
                .path
                .last()
                .expect("ICE: empty unresolved ident");

            let name = stores.strings.resolve(item_name.inner);
            let builtin_name = BuiltinTypes::from_name(name);

            if (unresolved_ident.path.len() > 1
                || unresolved_ident.is_from_root
                || !unresolved_ident.generic_params.is_empty())
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
                had_error.set();
                return Err(());
            }

            if let Some(builtin) = builtin_name {
                NameResolvedType::SimpleBuiltin(builtin)
            } else if unresolved_ident.path.len() == 1
                && !unresolved_ident.is_from_root
                && unresolved_ident.generic_params.is_empty()
                && generic_params.iter().any(|tp| tp.inner == item_name.inner)
            {
                NameResolvedType::SimpleGenericParam(*item_name)
            } else {
                let ident = resolved_single_ident(stores, had_error, cur_id, unresolved_ident)?;

                let params = unresolved_ident
                    .generic_params
                    .iter()
                    .map(|p| resolve_idents_in_type(stores, had_error, cur_id, p, generic_params))
                    .collect::<Result<Vec<_>, _>>()?;

                if params.is_empty() {
                    NameResolvedType::SimpleCustom {
                        id: ident,
                        token: item_name.inner.with_span(unresolved_ident.span),
                    }
                } else {
                    NameResolvedType::GenericInstance {
                        id: ident,
                        id_token: item_name.inner.with_span(unresolved_ident.span),
                        params,
                    }
                }
            }
        }
        UnresolvedType::Array(sub_type, length) => {
            let sub_type =
                resolve_idents_in_type(stores, had_error, cur_id, sub_type, generic_params)?;
            NameResolvedType::Array(Box::new(sub_type), *length)
        }
        UnresolvedType::MultiPointer(sub_type) => {
            let sub_type =
                resolve_idents_in_type(stores, had_error, cur_id, sub_type, generic_params)?;
            NameResolvedType::MultiPointer(Box::new(sub_type))
        }
        UnresolvedType::SinglePointer(sub_type) => {
            let sub_type =
                resolve_idents_in_type(stores, had_error, cur_id, sub_type, generic_params)?;
            NameResolvedType::SinglePointer(Box::new(sub_type))
        }
    };

    Ok(res)
}

fn check_generic_param_length(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    kind: &NameResolvedType,
    kind_span: SourceLocation,
    can_infer: bool,
) {
    match kind {
        NameResolvedType::SimpleCustom { id, .. } => {
            let struct_def = stores.sigs.urir.get_struct(*id);
            let kind_str = if struct_def.is_union {
                "union"
            } else {
                "struct"
            };
            if !struct_def.generic_params.is_empty() && !can_infer {
                invalid_generic_count_diag(
                    stores,
                    kind_span,
                    struct_def.generic_params.len(),
                    0,
                    &[(
                        struct_def.name.location,
                        &format!("{kind_str} defined here"),
                    )],
                );
                had_error.set();
            }
        }
        NameResolvedType::GenericInstance { id, params, .. } => {
            let struct_def = stores.sigs.urir.get_struct(*id);
            let kind_str = if struct_def.is_union {
                "union"
            } else {
                "struct"
            };
            if struct_def.generic_params.len() != params.len() {
                invalid_generic_count_diag(
                    stores,
                    kind_span,
                    struct_def.generic_params.len(),
                    params.len(),
                    &[(
                        struct_def.name.location,
                        &format!("{kind_str} defined here"),
                    )],
                );
                had_error.set();
            }
        }
        NameResolvedType::Array(inner, _)
        | NameResolvedType::MultiPointer(inner)
        | NameResolvedType::SinglePointer(inner) => {
            check_generic_param_length(stores, had_error, inner, kind_span, can_infer)
        }

        // Nothing to do here.
        NameResolvedType::SimpleGenericParam(_) | NameResolvedType::SimpleBuiltin(_) => {}
    }
}

fn resolve_idents_in_struct_def(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
    def: &StructDef<UnresolvedType>,
) -> StructDef<NameResolvedType> {
    let mut resolved = StructDef {
        name: def.name,
        fields: Vec::new(),
        generic_params: def.generic_params.clone(),
        is_union: def.is_union,
    };

    for field in &def.fields {
        let Ok(new_kind) = resolve_idents_in_type(
            stores,
            had_error,
            cur_id,
            &field.kind.inner,
            &def.generic_params,
        ) else {
            had_error.set();
            continue;
        };

        check_generic_param_length(stores, had_error, &new_kind, field.kind.location, false);

        resolved.fields.push(StructDefField {
            name: field.name,
            kind: new_kind.with_span(field.kind.location),
        });
    }

    resolved
}

fn resolve_idents_in_module_imports(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let unresolved_imports = stores.sigs.urir.get_scope(cur_id).imports().to_owned();

    for import in unresolved_imports {
        if !import.generic_params.is_empty() {
            diagnostics::emit_error(
                stores,
                import.span,
                "import cannot have generic parameters",
                [Label::new(import.span).with_color(Color::Red)],
                None,
            );
            had_error.set();
        }

        let Ok(resolved_item_id) = resolved_single_ident(stores, had_error, cur_id, &import) else {
            had_error.set();
            continue;
        };

        let item_name = stores.items.get_item_header(resolved_item_id).name;
        let resolved_scope = stores.sigs.nrir.get_scope_mut(cur_id);
        match resolved_scope
            .add_visible_symbol(item_name.inner.with_span(import.span), resolved_item_id)
        {
            Ok(_) => {}
            Err(prev_loc) => {
                had_error.set();
                diagnostics::handle_symbol_redef_error(
                    stores,
                    had_error,
                    Some(NameCollision {
                        prev: prev_loc,
                        new: import.span,
                    }),
                );
            }
        }
    }
}

fn get_parent_module(item_store: &ItemStore, mut cur_id: ItemId) -> ItemId {
    loop {
        let header = item_store.get_item_header(cur_id);
        let Some(parent_id) = header.parent else {
            panic!("ICE: Tried to get parent of orphaned item {:?}", header.id);
        };

        let parent_header = item_store.get_item_header(parent_id);
        if parent_header.kind == ItemKind::Module {
            return parent_header.id;
        }

        cur_id = parent_id;
    }
}

pub fn resolve_signature(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let header = stores.items.get_item_header(cur_id);
    match header.kind {
        ItemKind::StructDef => {
            let parent_module = get_parent_module(stores.items, cur_id);
            // Just give a best-effort if this fails.
            let _ = pass_manager.ensure_ident_resolved_signature(stores, parent_module);

            let def = stores.sigs.urir.get_struct(cur_id).clone();
            let resolved = resolve_idents_in_struct_def(stores, had_error, cur_id, &def);
            stores.sigs.nrir.set_struct(cur_id, resolved);
        }
        ItemKind::Variable => {
            let parent_module = get_parent_module(stores.items, cur_id);
            // Just give a best-effort if this fails.
            let _ = pass_manager.ensure_ident_resolved_signature(stores, parent_module);

            let generic_params = match header.parent {
                Some(parent_id)
                    if stores.items.get_item_header(parent_id).kind
                        == ItemKind::GenericFunction =>
                {
                    stores
                        .items
                        .get_function_template_paramaters(parent_id)
                        .to_owned()
                }
                _ => Vec::new(),
            };

            let unresolved_variable_type = stores
                .sigs
                .urir
                .get_variable_type(cur_id)
                .map(|i| i.clone());

            let Ok(new_kind) = resolve_idents_in_type(
                stores,
                had_error,
                cur_id,
                &unresolved_variable_type.inner,
                &generic_params,
            ) else {
                had_error.set();
                return;
            };

            check_generic_param_length(
                stores,
                had_error,
                &new_kind,
                unresolved_variable_type.location,
                false,
            );

            stores.sigs.nrir.set_variable_type(cur_id, new_kind);
        }
        ItemKind::Module => {
            resolve_idents_in_module_imports(stores, had_error, cur_id);
        }
        // These are all treated the same.
        ItemKind::Assert
        | ItemKind::Const
        | ItemKind::Function { .. }
        | ItemKind::FunctionDecl
        | ItemKind::GenericFunction => {
            let parent_module = get_parent_module(stores.items, cur_id);
            // Just give a best-effort if this fails.
            let _ = pass_manager.ensure_ident_resolved_signature(stores, parent_module);

            let unresolved_sig = stores.sigs.urir.get_item_signature(cur_id).clone();
            let generic_params = stores
                .items
                .get_function_template_paramaters(cur_id)
                .to_owned();

            let mut resolved_sig = NameResolvedItemSignature {
                exit: Vec::new(),
                entry: Vec::new(),

                // We only use this after instantiation, so leave it empty.
                generic_params: Vec::new(),
            };

            let mut local_had_error = ErrorSignal::new();

            let mut process_sig =
                |unresolved: &[Spanned<UnresolvedType>], resolved: &mut Vec<NameResolvedType>| {
                    for kind in unresolved {
                        let Ok(new_kind) = resolve_idents_in_type(
                            stores,
                            had_error,
                            cur_id,
                            &kind.inner,
                            &generic_params,
                        ) else {
                            local_had_error.set();
                            continue;
                        };

                        check_generic_param_length(
                            stores,
                            had_error,
                            &new_kind,
                            kind.location,
                            false,
                        );

                        resolved.push(new_kind);
                    }
                };

            process_sig(&unresolved_sig.entry.inner, &mut resolved_sig.entry);
            process_sig(&unresolved_sig.exit.inner, &mut resolved_sig.exit);

            if local_had_error.into_bool() {
                had_error.set();
                return;
            }

            stores.sigs.nrir.set_item_signature(cur_id, resolved_sig);
        }
    };
}

fn resolve_idents_in_block(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
    block_id: BlockId,
    generic_params: &[Spanned<Spur>],
) {
    let block = stores.blocks.get_block(block_id).clone();
    for op_id in block.ops {
        // TODO: Try to avoid this clone.
        let old_code = stores.ops.get_unresolved(op_id).clone();
        let op_token = stores.ops.get_token(op_id);
        let new_code = match old_code {
            // These don't get resolved, so just copy it onward.
            OpCode::Basic(bo) => {
                match bo {
                    Basic::Control(Control::If(if_op)) => {
                        resolve_idents_in_block(
                            stores,
                            had_error,
                            cur_id,
                            if_op.condition,
                            generic_params,
                        );
                        resolve_idents_in_block(
                            stores,
                            had_error,
                            cur_id,
                            if_op.then_block,
                            generic_params,
                        );
                        resolve_idents_in_block(
                            stores,
                            had_error,
                            cur_id,
                            if_op.else_block,
                            generic_params,
                        );
                    }
                    Basic::Control(Control::While(while_op)) => {
                        resolve_idents_in_block(
                            stores,
                            had_error,
                            cur_id,
                            while_op.condition,
                            generic_params,
                        );
                        resolve_idents_in_block(
                            stores,
                            had_error,
                            cur_id,
                            while_op.body_block,
                            generic_params,
                        );
                    }
                    _ => {}
                }

                OpCode::Basic(bo)
            }

            OpCode::Complex(comp) => match comp {
                UnresolvedOp::Cast { id } => {
                    let Ok(new_ty) =
                        resolve_idents_in_type(stores, had_error, cur_id, &id, generic_params)
                    else {
                        had_error.set();
                        continue;
                    };

                    check_generic_param_length(
                        stores,
                        had_error,
                        &new_ty,
                        op_token.location,
                        false,
                    );

                    OpCode::Complex(NameResolvedOp::Cast { id: new_ty })
                }
                UnresolvedOp::SizeOf { id } => {
                    let Ok(new_ty) =
                        resolve_idents_in_type(stores, had_error, cur_id, &id, generic_params)
                    else {
                        had_error.set();
                        continue;
                    };

                    check_generic_param_length(
                        stores,
                        had_error,
                        &new_ty,
                        op_token.location,
                        false,
                    );

                    OpCode::Complex(NameResolvedOp::SizeOf { id: new_ty })
                }

                UnresolvedOp::Ident(ident) => {
                    let Ok(resolved_ident) =
                        resolved_single_ident(stores, had_error, cur_id, &ident)
                    else {
                        continue;
                    };

                    let resolved_generic_params = ident
                        .generic_params
                        .iter()
                        .filter_map(|param| {
                            let Ok(new_kind) = resolve_idents_in_type(
                                stores,
                                had_error,
                                cur_id,
                                param,
                                generic_params,
                            ) else {
                                return None;
                            };

                            check_generic_param_length(
                                stores,
                                had_error,
                                &new_kind,
                                op_token.location,
                                true,
                            );

                            Some(new_kind)
                        })
                        .collect();

                    let found_item_header = stores.items.get_item_header(resolved_ident);
                    let new_code = match found_item_header.kind {
                        ItemKind::Const => NameResolvedOp::Const { id: resolved_ident },
                        ItemKind::Function { .. } | ItemKind::FunctionDecl => {
                            if !ident.generic_params.is_empty() {
                                invalid_generic_count_diag(
                                    stores,
                                    op_token.location,
                                    0,
                                    ident.generic_params.len(),
                                    &[(found_item_header.name.location, "function defined here")],
                                );
                                had_error.set();
                            }
                            NameResolvedOp::CallFunction {
                                id: resolved_ident,
                                generic_params: resolved_generic_params,
                            }
                        }
                        ItemKind::GenericFunction => {
                            let expected_params_len = stores
                                .items
                                .get_function_template_paramaters(resolved_ident)
                                .len();

                            if ident.generic_params.len() != expected_params_len
                                && !ident.generic_params.is_empty()
                            {
                                invalid_generic_count_diag(
                                    stores,
                                    op_token.location,
                                    expected_params_len,
                                    ident.generic_params.len(),
                                    &[(found_item_header.name.location, "function defined here")],
                                );
                                had_error.set();
                            }

                            NameResolvedOp::CallFunction {
                                id: resolved_ident,
                                generic_params: resolved_generic_params,
                            }
                        }
                        ItemKind::Variable => {
                            let parent_id = found_item_header.parent.unwrap(); // Only top-level modules don't have a parent.
                            let parent_header = stores.items.get_item_header(parent_id);

                            if !ident.generic_params.is_empty() {
                                invalid_generic_count_diag(
                                    stores,
                                    op_token.location,
                                    0,
                                    ident.generic_params.len(),
                                    &[(found_item_header.name.location, "function defined here")],
                                );
                                had_error.set();
                            }

                            NameResolvedOp::Variable {
                                id: resolved_ident,
                                is_global: parent_header.kind == ItemKind::Module,
                            }
                        }

                        // This is the same as PackStruct
                        ItemKind::StructDef => {
                            let ty = UnresolvedType::Simple(ident.clone());
                            let Ok(new_ty) = resolve_idents_in_type(
                                stores,
                                had_error,
                                cur_id,
                                &ty,
                                generic_params,
                            ) else {
                                had_error.set();
                                continue;
                            };

                            check_generic_param_length(
                                stores, had_error, &new_ty, ident.span, true,
                            );

                            NameResolvedOp::PackStruct { id: new_ty }
                        }

                        ItemKind::Assert | ItemKind::Module => {
                            had_error.set();
                            let op_loc = stores.ops.get_token(op_id).location;
                            let mut labels = vec![Label::new(op_loc).with_color(Color::Red)];
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
                                op_loc,
                                format!("cannot refer to a {:?} here", found_item_header.kind),
                                labels,
                                note,
                            );
                            continue;
                        }
                    };

                    OpCode::Complex(new_code)
                }
            },
        };

        stores.ops.set_name_resolved(op_id, new_code);
    }
}

pub fn resolve_body(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let header = stores.items.get_item_header(cur_id);
    match header.kind {
        ItemKind::Variable | ItemKind::Module | ItemKind::StructDef | ItemKind::FunctionDecl => {
            // Nothing to do.
        }
        ItemKind::Assert
        | ItemKind::Const
        | ItemKind::Function { .. }
        | ItemKind::GenericFunction => {
            let parent_module = get_parent_module(stores.items, cur_id);
            // Just give a best-effort if this fails.
            let _ = pass_manager.ensure_ident_resolved_signature(stores, parent_module);

            let generic_params = stores
                .items
                .get_function_template_paramaters(cur_id)
                .to_owned();
            let body = stores.items.get_item_body(cur_id);
            resolve_idents_in_block(stores, had_error, cur_id, body, &generic_params);
        }
    }
}
