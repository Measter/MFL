use lasso::Spur;
use stores::{
    items::ItemId,
    source::{FileId, SourceLocation, Spanned, WithSpan},
};

use crate::{
    diagnostics::{self, NameCollision},
    error_signal::ErrorSignal,
    ir::{
        Basic, Control, IdentPathRoot, NameResolvedOp, NameResolvedType, OpCode, StructDef,
        StructDefField, UnresolvedIdent, UnresolvedOp, UnresolvedType,
    },
    pass_manager::PassManager,
    stores::{
        block::BlockId,
        diagnostics::Diagnostic,
        item::{ItemHeader, ItemKind, ItemStore, LangItem},
        signatures::{
            ImportStrength, NameResolvedItemSignature, StackDefItemNameResolved,
            StackDefItemUnresolved,
        },
    },
    Stores,
};

fn invalid_generic_count_diag(
    stores: &mut Stores,
    item_id: ItemId,
    error_span: SourceLocation,
    expected: usize,
    actual: usize,
    extra_labels: &[(SourceLocation, &str)],
) {
    let mut diag = Diagnostic::error(
        error_span,
        format!("expected {expected} generic parameters, found {actual}",),
    );

    for &(label_loc, label_msg) in extra_labels {
        diag.add_help_label(label_loc, label_msg);
    }

    diag.attached(stores.diags, item_id);
}

fn get_visible_symbol(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    from: ItemHeader,
    symbol: Spur,
) -> Option<ItemId> {
    // 1. Check ourselves
    if from.name.inner == symbol {
        return Some(from.id);
    }

    // 2. Check our children
    let own_scope = stores.sigs.nrir.get_scope(from.id);
    if let Some(child) = own_scope.get_symbol(symbol) {
        return Some(child);
    }

    // 3. If we're not a module traverse up the tree checking siblings until we hit a module.
    if from.kind != ItemKind::Module {
        let mut parent = from.parent;
        while let Some(parent_id) = parent {
            // We can just let this fail and fail ident resolution.
            let _ = pass_manager.ensure_ident_resolved_scope(stores, parent_id);

            let parent_scope = stores.sigs.nrir.get_scope(parent_id);
            if let Some(child) = parent_scope.get_symbol(symbol) {
                return Some(child);
            }

            let parent_header = stores.items.get_item_header(parent_id);
            if parent_header.kind == ItemKind::Module {
                break;
            }
            parent = parent_header.parent;
        }
    }

    // 4. Check top level modules
    stores.items.get_top_level_module(symbol)
}

fn resolved_single_ident(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
    ident: &UnresolvedIdent,
) -> Result<ItemId, ()> {
    let [first_ident, rest @ ..] = ident.path.as_slice() else {
        unreachable!()
    };

    let (mut current_item, rest) = match ident.path_root {
        IdentPathRoot::CurrentScope => {
            let header = stores.items.get_item_header(cur_id);
            let Some(start_item) =
                get_visible_symbol(stores, pass_manager, header, first_ident.inner)
            else {
                let item_name = stores.strings.resolve(first_ident.inner);
                Diagnostic::error(
                    first_ident.location,
                    format!("symbol `{item_name}` not found"),
                )
                .attached(stores.diags, cur_id);

                had_error.set();
                return Err(());
            };
            (start_item, rest)
        }
        IdentPathRoot::CurrentLib => {
            let mut current_item = cur_id;
            // Go up the tree until we find we have no parent. This will get us to the root of the library.
            loop {
                let cur_header = stores.items.get_item_header(current_item);
                if let Some(parent) = cur_header.parent {
                    current_item = parent;
                } else {
                    break;
                }
            }

            (current_item, ident.path.as_slice())
        }
        IdentPathRoot::Root => {
            let Some(tlm) = stores.items.get_top_level_module(first_ident.inner) else {
                let item_name = stores.strings.resolve(first_ident.inner);
                Diagnostic::error(
                    first_ident.location,
                    format!("symbol `{item_name}` not found"),
                )
                .attached(stores.diags, cur_id);
                had_error.set();
                return Err(());
            };
            (tlm, rest)
        }
        IdentPathRoot::CurrentModule => {
            let current_item_kind = stores.items.get_item_header(cur_id).kind;
            let id = if current_item_kind == ItemKind::Module {
                cur_id
            } else {
                get_parent_module(stores.items, cur_id)
            };

            (id, ident.path.as_slice())
        }
    };

    let mut last_ident = *first_ident;
    for sub_ident in rest {
        let current_item_header = stores.items.get_item_header(current_item);
        // Nothing to do if this fails.
        let _ = pass_manager.ensure_ident_resolved_scope(stores, current_item);

        match current_item_header.kind {
            ItemKind::StructDef | ItemKind::Module | ItemKind::Primitive(_) => {}
            ItemKind::Enum => {
                // If this fails, just make a best effort.
                let _ = pass_manager.ensure_declare_enums(stores, current_item_header.id);
            }

            ItemKind::Assert
            | ItemKind::Const
            | ItemKind::Variable
            | ItemKind::Function
            | ItemKind::FunctionDecl
            | ItemKind::GenericFunction => {
                Diagnostic::error(
                    sub_ident.location,
                    format!("cannot path into {}", current_item_header.kind.kind_str()),
                )
                .with_help_label(
                    last_ident.location,
                    format!("is a {}", current_item_header.kind.kind_str()),
                )
                .attached(stores.diags, cur_id);
                had_error.set();
                return Err(());
            }
        }

        let scope = stores.sigs.nrir.get_scope(current_item_header.id);
        let Some(sub_item) = scope.get_symbol(sub_ident.inner) else {
            Diagnostic::error(sub_ident.location, "symbol not found")
                .attached(stores.diags, cur_id);
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
    pass_manager: &mut PassManager,
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

            if unresolved_ident.path.len() == 1
                && unresolved_ident.path_root == IdentPathRoot::CurrentScope
                && unresolved_ident.generic_params.is_empty()
                && generic_params.iter().any(|tp| tp.inner == item_name.inner)
            {
                NameResolvedType::SimpleGenericParam(*item_name)
            } else {
                let ident = resolved_single_ident(
                    stores,
                    pass_manager,
                    had_error,
                    cur_id,
                    unresolved_ident,
                )?;

                let params = unresolved_ident
                    .generic_params
                    .iter()
                    .map(|p| {
                        resolve_idents_in_type(
                            stores,
                            pass_manager,
                            had_error,
                            cur_id,
                            p,
                            generic_params,
                        )
                    })
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
        UnresolvedType::FunctionPointer { inputs, outputs } => {
            let inputs = inputs
                .iter()
                .map(|t| {
                    resolve_idents_in_type(
                        stores,
                        pass_manager,
                        had_error,
                        cur_id,
                        t,
                        generic_params,
                    )
                })
                .collect::<Result<_, _>>()?;

            let outputs = outputs
                .iter()
                .map(|t| {
                    resolve_idents_in_type(
                        stores,
                        pass_manager,
                        had_error,
                        cur_id,
                        t,
                        generic_params,
                    )
                })
                .collect::<Result<_, _>>()?;

            NameResolvedType::FunctionPointer { inputs, outputs }
        }
        UnresolvedType::Array(sub_type, length) => {
            let sub_type = resolve_idents_in_type(
                stores,
                pass_manager,
                had_error,
                cur_id,
                sub_type,
                generic_params,
            )?;
            NameResolvedType::Array(Box::new(sub_type), *length)
        }
        UnresolvedType::MultiPointer(sub_type) => {
            let sub_type = resolve_idents_in_type(
                stores,
                pass_manager,
                had_error,
                cur_id,
                sub_type,
                generic_params,
            )?;
            NameResolvedType::MultiPointer(Box::new(sub_type))
        }
        UnresolvedType::SinglePointer(sub_type) => {
            let sub_type = resolve_idents_in_type(
                stores,
                pass_manager,
                had_error,
                cur_id,
                sub_type,
                generic_params,
            )?;
            NameResolvedType::SinglePointer(Box::new(sub_type))
        }
    };

    Ok(res)
}

fn check_generic_param_length(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
    kind: &NameResolvedType,
    kind_span: SourceLocation,
    can_infer: bool,
) {
    match kind {
        NameResolvedType::SimpleCustom { id, .. } => {
            match stores.items.get_item_header(*id).kind {
                ItemKind::StructDef => {
                    let struct_def = stores.sigs.urir.get_struct(*id);
                    let kind_str = if struct_def.is_union {
                        "union"
                    } else {
                        "struct"
                    };
                    if !struct_def.generic_params.is_empty() && !can_infer {
                        invalid_generic_count_diag(
                            stores,
                            cur_id,
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
                // Nothing to do here
                ItemKind::Enum | ItemKind::Primitive(_) => {}
                _ => unreachable!(),
            };
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
                    cur_id,
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
        NameResolvedType::FunctionPointer { inputs, outputs } => {
            inputs.iter().chain(outputs).for_each(|kind| {
                check_generic_param_length(stores, had_error, cur_id, kind, kind_span, can_infer);
            });
        }
        NameResolvedType::Array(inner, _)
        | NameResolvedType::MultiPointer(inner)
        | NameResolvedType::SinglePointer(inner) => {
            check_generic_param_length(stores, had_error, cur_id, inner, kind_span, can_infer)
        }

        // Nothing to do here.
        NameResolvedType::SimpleGenericParam(_) => {}
    }
}

fn resolve_idents_in_struct_def(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
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
            pass_manager,
            had_error,
            cur_id,
            &field.kind.inner,
            &def.generic_params,
        ) else {
            had_error.set();
            continue;
        };

        check_generic_param_length(
            stores,
            had_error,
            cur_id,
            &new_kind,
            field.kind.location,
            false,
        );

        resolved.fields.push(StructDefField {
            name: field.name,
            kind: new_kind.with_span(field.kind.location),
        });
    }

    resolved
}

pub fn resolve_idents_in_scope(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    {
        // Let's first weakly import the builtin types (ints, float, bool, string).
        let string_lang_item = stores.items.get_lang_items()[&LangItem::String];
        let string_header = stores.items.get_item_header(string_lang_item);

        let resolved_scope = stores.sigs.nrir.get_scope_mut(cur_id);
        resolved_scope
            .add_visible_symbol(string_header.name, string_lang_item, ImportStrength::Weak)
            .expect("ICE: builtin import failed");

        for &builtin_id in stores.items.get_primitives() {
            let builtin_header = stores.items.get_item_header(builtin_id);
            resolved_scope
                .add_visible_symbol(builtin_header.name, builtin_id, ImportStrength::Weak)
                .expect("ICE: builtin import failed");
        }
    }

    let unresolved_imports = stores.sigs.urir.get_scope(cur_id).imports().to_owned();

    for import in unresolved_imports {
        if !import.generic_params.is_empty() {
            Diagnostic::error(import.span, "import cannot have generic parameters")
                .attached(stores.diags, cur_id);
            had_error.set();
        }

        let Ok(resolved_item_id) =
            resolved_single_ident(stores, pass_manager, had_error, cur_id, &import)
        else {
            had_error.set();
            continue;
        };

        let item_name = stores.items.get_item_header(resolved_item_id).name;
        let resolved_scope = stores.sigs.nrir.get_scope_mut(cur_id);
        match resolved_scope.add_visible_symbol(
            item_name.inner.with_span(import.span),
            resolved_item_id,
            ImportStrength::Strong,
        ) {
            Ok(_) => {}
            Err(prev_loc) => {
                had_error.set();
                diagnostics::handle_symbol_redef_error(
                    stores,
                    had_error,
                    cur_id,
                    Some(NameCollision {
                        prev: prev_loc,
                        new: import.span,
                    }),
                );
            }
        }
    }

    // Now we add our children to our visible symbols. Doing it this way lets children
    // overwrite weak imports.

    // Ugh..
    let child_items = stores
        .sigs
        .nrir
        .get_scope_mut(cur_id)
        .get_child_items()
        .to_owned();

    for child_id in child_items {
        let resolved_scope = stores.sigs.nrir.get_scope_mut(cur_id);
        let child_header = stores.items.get_item_header(child_id);
        if let Err(prev_loc) =
            resolved_scope.add_visible_symbol(child_header.name, child_id, ImportStrength::Strong)
        {
            had_error.set();
            diagnostics::handle_symbol_redef_error(
                stores,
                had_error,
                cur_id,
                Some(NameCollision {
                    prev: prev_loc,
                    new: child_header.name.location,
                }),
            );
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
            let resolved =
                resolve_idents_in_struct_def(stores, pass_manager, had_error, cur_id, &def);
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
                pass_manager,
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
                cur_id,
                &new_kind,
                unresolved_variable_type.location,
                false,
            );

            stores.sigs.nrir.set_variable_type(cur_id, new_kind);
        }

        // Nothing to do here.
        ItemKind::Module | ItemKind::Enum | ItemKind::Primitive(_) => {}

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

            let mut process_sig_kind =
                |stores: &mut Stores, kind: &Spanned<UnresolvedType>| -> Option<NameResolvedType> {
                    let Ok(new_kind) = resolve_idents_in_type(
                        stores,
                        pass_manager,
                        had_error,
                        cur_id,
                        &kind.inner,
                        &generic_params,
                    ) else {
                        local_had_error.set();
                        return None;
                    };

                    check_generic_param_length(
                        stores,
                        had_error,
                        cur_id,
                        &new_kind,
                        kind.location,
                        false,
                    );
                    Some(new_kind)
                };

            for kind in &unresolved_sig.entry.inner {
                let new_kind = match kind {
                    StackDefItemUnresolved::Var { name, kind } => {
                        let scope = stores.sigs.nrir.get_scope(cur_id);
                        let Some(var_id) = scope.get_symbol(name.inner) else {
                            panic!("ICE: Failed to find name of parameter variable")
                        };

                        let Some(new_kind) = process_sig_kind(stores, kind) else {
                            continue;
                        };

                        StackDefItemNameResolved::Var {
                            name: var_id,
                            kind: new_kind,
                        }
                    }
                    StackDefItemUnresolved::Stack(kind) => {
                        let Some(new_kind) = process_sig_kind(stores, kind) else {
                            continue;
                        };
                        StackDefItemNameResolved::Stack(new_kind)
                    }
                };

                resolved_sig.entry.push(new_kind);
            }

            for kind in &unresolved_sig.exit.inner {
                if let Some(new_kind) = process_sig_kind(stores, kind) {
                    resolved_sig.exit.push(new_kind);
                }
            }

            if local_had_error.into_err() {
                had_error.set();
                return;
            }

            stores.sigs.nrir.set_item_signature(cur_id, resolved_sig);
        }
    };
}

fn resolve_idents_in_block(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
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
                    Basic::Control(Control::Cond(ref cond_op)) => {
                        for arm in &cond_op.arms {
                            resolve_idents_in_block(
                                stores,
                                pass_manager,
                                had_error,
                                cur_id,
                                arm.condition,
                                generic_params,
                            );
                            resolve_idents_in_block(
                                stores,
                                pass_manager,
                                had_error,
                                cur_id,
                                arm.block,
                                generic_params,
                            );
                        }

                        resolve_idents_in_block(
                            stores,
                            pass_manager,
                            had_error,
                            cur_id,
                            cond_op.else_block,
                            generic_params,
                        );
                    }
                    Basic::Control(Control::While(while_op)) => {
                        resolve_idents_in_block(
                            stores,
                            pass_manager,
                            had_error,
                            cur_id,
                            while_op.condition,
                            generic_params,
                        );
                        resolve_idents_in_block(
                            stores,
                            pass_manager,
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
                ref cp @ (UnresolvedOp::PackEnum(ref id) | UnresolvedOp::Cast { ref id }) => {
                    let Ok(new_ty) = resolve_idents_in_type(
                        stores,
                        pass_manager,
                        had_error,
                        cur_id,
                        id,
                        generic_params,
                    ) else {
                        had_error.set();
                        continue;
                    };

                    check_generic_param_length(
                        stores,
                        had_error,
                        cur_id,
                        &new_ty,
                        op_token.location,
                        false,
                    );

                    match cp {
                        UnresolvedOp::Cast { .. } => {
                            OpCode::Complex(NameResolvedOp::Cast { id: new_ty })
                        }
                        UnresolvedOp::PackEnum(..) => {
                            OpCode::Complex(NameResolvedOp::PackEnum { id: new_ty })
                        }
                        _ => unreachable!(),
                    }
                }
                UnresolvedOp::SizeOf { id } => {
                    let Ok(new_ty) = resolve_idents_in_type(
                        stores,
                        pass_manager,
                        had_error,
                        cur_id,
                        &id,
                        generic_params,
                    ) else {
                        had_error.set();
                        continue;
                    };

                    check_generic_param_length(
                        stores,
                        had_error,
                        cur_id,
                        &new_ty,
                        op_token.location,
                        false,
                    );

                    OpCode::Complex(NameResolvedOp::SizeOf { id: new_ty })
                }

                UnresolvedOp::Ident(ident) => {
                    let Ok(resolved_ident) =
                        resolved_single_ident(stores, pass_manager, had_error, cur_id, &ident)
                    else {
                        continue;
                    };

                    let resolved_generic_params = ident
                        .generic_params
                        .iter()
                        .filter_map(|param| {
                            let Ok(new_kind) = resolve_idents_in_type(
                                stores,
                                pass_manager,
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
                                cur_id,
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
                                    cur_id,
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
                                    cur_id,
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
                                    cur_id,
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
                                pass_manager,
                                had_error,
                                cur_id,
                                &ty,
                                generic_params,
                            ) else {
                                had_error.set();
                                continue;
                            };

                            check_generic_param_length(
                                stores, had_error, cur_id, &new_ty, ident.span, true,
                            );

                            NameResolvedOp::PackStruct { id: new_ty }
                        }

                        ItemKind::Primitive(_) | ItemKind::Enum => {
                            had_error.set();
                            let op_loc = stores.ops.get_token(op_id).location;
                            let name = stores.strings.resolve(found_item_header.name.inner);
                            Diagnostic::error(
                                op_loc,
                                format!("{name} cannot be used in an expression context"),
                            )
                            .attached(stores.diags, cur_id);

                            continue;
                        }

                        ItemKind::Assert | ItemKind::Module => {
                            had_error.set();
                            let op_loc = stores.ops.get_token(op_id).location;
                            let mut diag = Diagnostic::error(
                                op_loc,
                                format!(
                                    "cannot refer to a {} here",
                                    found_item_header.kind.kind_str()
                                ),
                            );

                            // This would be the case if the item was a top-level mmodule.
                            let note = if found_item_header.name.location.file_id != FileId::dud() {
                                diag.add_help_label(
                                    found_item_header.name.location,
                                    format!("item is a {:?}", found_item_header.kind),
                                );
                                String::new()
                            } else {
                                let name = stores.strings.resolve(found_item_header.name.inner);
                                format!("`{name}` is a top-level module")
                            };

                            diag.with_note(note).attached(stores.diags, cur_id);

                            continue;
                        }
                    };

                    OpCode::Complex(new_code)
                }
                UnresolvedOp::FunctionPointer(ident) => {
                    let Ok(resolved_ident) =
                        resolved_single_ident(stores, pass_manager, had_error, cur_id, &ident)
                    else {
                        continue;
                    };

                    let resolved_generic_params = ident
                        .generic_params
                        .iter()
                        .filter_map(|param| {
                            let Ok(new_kind) = resolve_idents_in_type(
                                stores,
                                pass_manager,
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
                                cur_id,
                                &new_kind,
                                op_token.location,
                                true,
                            );

                            Some(new_kind)
                        })
                        .collect();

                    let found_item_header = stores.items.get_item_header(resolved_ident);

                    match found_item_header.kind {
                        ItemKind::Function | ItemKind::FunctionDecl => {
                            if !ident.generic_params.is_empty() {
                                invalid_generic_count_diag(
                                    stores,
                                    cur_id,
                                    op_token.location,
                                    0,
                                    ident.generic_params.len(),
                                    &[(found_item_header.name.location, "function defined here")],
                                );
                                had_error.set();
                            }
                        }
                        ItemKind::GenericFunction => {
                            let expected_params_len = stores
                                .items
                                .get_function_template_paramaters(resolved_ident)
                                .len();

                            if ident.generic_params.len() != expected_params_len {
                                invalid_generic_count_diag(
                                    stores,
                                    cur_id,
                                    op_token.location,
                                    expected_params_len,
                                    ident.generic_params.len(),
                                    &[(found_item_header.name.location, "function defined here")],
                                );
                                had_error.set();
                            }
                        }

                        ItemKind::Assert
                        | ItemKind::Const
                        | ItemKind::Variable
                        | ItemKind::StructDef
                        | ItemKind::Enum
                        | ItemKind::Module
                        | ItemKind::Primitive(_) => {
                            had_error.set();
                            let op_loc = stores.ops.get_token(op_id).location;
                            Diagnostic::error(
                                op_loc,
                                format!(
                                    "cannot create function pointer to a {:?}",
                                    found_item_header.kind
                                ),
                            )
                            .attached(stores.diags, cur_id);

                            continue;
                        }
                    }

                    OpCode::Complex(NameResolvedOp::FunctionPointer {
                        id: resolved_ident,
                        generic_params: resolved_generic_params,
                    })
                }
                UnresolvedOp::AssumeInit(ident) => {
                    let Ok(resolved_ident) =
                        resolved_single_ident(stores, pass_manager, had_error, cur_id, &ident)
                    else {
                        continue;
                    };

                    ident.generic_params.iter().for_each(|param| {
                        let Ok(new_kind) = resolve_idents_in_type(
                            stores,
                            pass_manager,
                            had_error,
                            cur_id,
                            param,
                            generic_params,
                        ) else {
                            return;
                        };

                        check_generic_param_length(
                            stores,
                            had_error,
                            cur_id,
                            &new_kind,
                            op_token.location,
                            true,
                        );
                    });

                    let found_item_header = stores.items.get_item_header(resolved_ident);
                    match found_item_header.kind {
                        ItemKind::Variable => {
                            let parent_id = found_item_header.parent.unwrap(); // Only top-level modules don't have a parent.
                            if parent_id != cur_id {
                                Diagnostic::error(
                                    op_token.location,
                                    "`init` only support local variable",
                                )
                                .with_help_label(
                                    found_item_header.name.location,
                                    "variable is a global",
                                )
                                .attached(stores.diags, cur_id);

                                had_error.set();
                                continue;
                            }

                            OpCode::Complex(NameResolvedOp::AssumeInit { id: resolved_ident })
                        }
                        ItemKind::Assert
                        | ItemKind::Const
                        | ItemKind::Function
                        | ItemKind::FunctionDecl
                        | ItemKind::GenericFunction
                        | ItemKind::StructDef
                        | ItemKind::Enum
                        | ItemKind::Module
                        | ItemKind::Primitive(_) => {
                            Diagnostic::error(
                                op_token.location,
                                "`init` only supports local variables",
                            )
                            .with_help_label(
                                found_item_header.name.location,
                                format!("item is a {}", found_item_header.kind.kind_str()),
                            )
                            .attached(stores.diags, cur_id);
                            continue;
                        }
                    }
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
        ItemKind::Variable
        | ItemKind::Module
        | ItemKind::StructDef
        | ItemKind::Enum
        | ItemKind::FunctionDecl
        | ItemKind::Primitive(_) => {
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
            resolve_idents_in_block(
                stores,
                pass_manager,
                had_error,
                cur_id,
                body,
                &generic_params,
            );
        }
    }
}
