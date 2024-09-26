use smallvec::SmallVec;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::{
        Basic, Control, NameResolvedOp, NameResolvedType, OpCode, PartiallyResolvedOp,
        TypeResolvedOp,
    },
    pass_manager::{static_analysis::ensure_types_declared_in_type, PassManager},
    stores::{
        block::BlockId,
        diagnostics::Diagnostic,
        item::ItemKind,
        signatures::{
            PartiallyTypeResolvedItemSignature, StackDefItemNameResolved, TypeResolvedItemSignature,
        },
    },
    Stores,
};

pub fn resolve_signature(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let cur_item_header = stores.items.get_item_header(cur_id);
    match cur_item_header.kind {
        ItemKind::Enum | ItemKind::Module | ItemKind::StructDef | ItemKind::Builtin(_) => {
            panic!(
                "ICE: Tried to resolve_signature on a {:?}",
                cur_item_header.kind
            )
        }

        ItemKind::GenericFunction => {
            let unresolved_sig = stores.sigs.nrir.get_item_signature(cur_id).clone();
            let mut resolved_sig = PartiallyTypeResolvedItemSignature {
                exit: Vec::new(),
                entry: Vec::new(),
            };

            let mut local_had_error = ErrorSignal::new();

            let mut process_sig = |kind: &NameResolvedType| {
                {
                    let mut single_check_error = ErrorSignal::new();
                    ensure_types_declared_in_type(
                        stores,
                        pass_manager,
                        &mut single_check_error,
                        kind,
                    );
                    if single_check_error.into_err() {
                        local_had_error.set();
                        return None;
                    }
                }

                let partial_type = match stores
                    .types
                    .partially_resolve_generic_type(stores.strings, kind)
                {
                    Ok(info) => info,
                    Err(tk) => {
                        local_had_error.set();
                        Diagnostic::type_error(stores, tk);
                        return None;
                    }
                };

                Some(partial_type)
            };

            for kind in &unresolved_sig.entry {
                let (StackDefItemNameResolved::Stack(kind)
                | StackDefItemNameResolved::Var { kind, .. }) = kind;

                if let Some(new_kind) = process_sig(kind) {
                    resolved_sig.entry.push(new_kind);
                }
            }

            for kind in &unresolved_sig.exit {
                if let Some(new_kind) = process_sig(kind) {
                    resolved_sig.exit.push(new_kind);
                }
            }

            if local_had_error.into_err() {
                had_error.set();
                return;
            }

            stores
                .sigs
                .trir
                .set_partial_item_signature(cur_id, resolved_sig);
        }

        ItemKind::Assert | ItemKind::Const | ItemKind::Function { .. } | ItemKind::FunctionDecl => {
            let unresolved_sig = stores.sigs.nrir.get_item_signature(cur_id).clone();
            let mut resolved_sig = TypeResolvedItemSignature {
                exit: Vec::new(),
                entry: Vec::new(),
                generic_params: unresolved_sig.generic_params,
            };

            let mut local_had_error = ErrorSignal::new();

            let mut process_sig = |kind: &NameResolvedType| {
                {
                    let mut single_check_error = ErrorSignal::new();
                    ensure_types_declared_in_type(
                        stores,
                        pass_manager,
                        &mut single_check_error,
                        kind,
                    );
                    if single_check_error.into_err() {
                        local_had_error.set();
                        return None;
                    }
                }

                let info = match stores.types.resolve_type(stores.strings, kind) {
                    Ok(info) => info,
                    Err(tk) => {
                        local_had_error.set();
                        Diagnostic::type_error(stores, tk);
                        return None;
                    }
                };

                Some(info.id)
            };

            for kind in &unresolved_sig.entry {
                let (StackDefItemNameResolved::Stack(kind)
                | StackDefItemNameResolved::Var { kind, .. }) = kind;

                if let Some(new_kind) = process_sig(kind) {
                    resolved_sig.entry.push(new_kind);
                }
            }

            for kind in &unresolved_sig.exit {
                if let Some(new_kind) = process_sig(kind) {
                    resolved_sig.exit.push(new_kind);
                }
            }

            if local_had_error.into_err() {
                had_error.set();
                return;
            }

            stores.sigs.trir.set_item_signature(cur_id, resolved_sig);
        }
        ItemKind::Variable => {
            let variable_type_unresolved = stores.sigs.nrir.get_variable_type(cur_id).clone();
            if let Some(type_item) = variable_type_unresolved.item_id() {
                let kind = stores.items.get_item_header(type_item).kind;
                match kind {
                    ItemKind::StructDef => {
                        if pass_manager
                            .ensure_declare_structs(stores, type_item)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }
                    ItemKind::Enum => {
                        if pass_manager
                            .ensure_declare_enums(stores, type_item)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }
                    _ => unreachable!(),
                }
            }

            let parent_id = cur_item_header.parent.unwrap(); // It's a variable, it must have a parent.
            let parent_header = stores.items.get_item_header(parent_id);

            if parent_header.kind == ItemKind::GenericFunction {
                let partial_type = match stores
                    .types
                    .partially_resolve_generic_type(stores.strings, &variable_type_unresolved)
                {
                    Ok(pt) => pt,
                    Err(tk) => {
                        had_error.set();
                        Diagnostic::type_error(stores, tk);
                        return;
                    }
                };

                stores
                    .sigs
                    .trir
                    .set_partial_variable_type(cur_id, partial_type);
            } else {
                let info = match stores
                    .types
                    .resolve_type(stores.strings, &variable_type_unresolved)
                {
                    Ok(info) => info,
                    Err(tk) => {
                        had_error.set();
                        Diagnostic::type_error(stores, tk);
                        return;
                    }
                };

                stores.sigs.trir.set_variable_type(cur_id, info.id);
            }
        }
    }
}

fn fully_resolve_block(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    unresolved_block_id: BlockId,
) {
    let block = stores.blocks.get_block(unresolved_block_id).clone();
    for op_id in block.ops {
        let old_code = stores.ops.get_name_resolved(op_id).clone();
        let new_code = match old_code {
            OpCode::Basic(bo) => {
                match bo {
                    Basic::Control(Control::Cond(ref cond_op)) => {
                        for arm in &cond_op.arms {
                            fully_resolve_block(stores, pass_manager, had_error, arm.condition);
                            fully_resolve_block(stores, pass_manager, had_error, arm.block);
                        }
                        fully_resolve_block(stores, pass_manager, had_error, cond_op.else_block);
                    }
                    Basic::Control(Control::While(while_op)) => {
                        fully_resolve_block(stores, pass_manager, had_error, while_op.condition);
                        fully_resolve_block(stores, pass_manager, had_error, while_op.body_block);
                    }
                    _ => {}
                }
                OpCode::Basic(bo)
            }

            OpCode::Complex(NameResolvedOp::CallFunction { id, generic_params }) => {
                let called_item_header = stores.items.get_item_header(id);
                if called_item_header.kind != ItemKind::GenericFunction || generic_params.is_empty()
                {
                    OpCode::Complex(TypeResolvedOp::CallFunction {
                        id,
                        generic_params: Vec::new(),
                    })
                } else {
                    let unresolved_generic_params = &generic_params;
                    let mut resolved_generic_params = Vec::new();
                    let mut unresolved_generic_params_sm = SmallVec::<[NameResolvedType; 4]>::new();

                    for ugp in unresolved_generic_params {
                        let mut local_had_error = ErrorSignal::new();
                        ensure_types_declared_in_type(
                            stores,
                            pass_manager,
                            &mut local_had_error,
                            ugp,
                        );
                        if local_had_error.into_err() {
                            had_error.set();
                            continue;
                        }

                        let type_info = match stores.types.resolve_type(stores.strings, ugp) {
                            Ok(info) => info,
                            Err(err_token) => {
                                Diagnostic::type_error(stores, err_token);
                                had_error.set();
                                continue;
                            }
                        };

                        resolved_generic_params.push(type_info.id);
                        unresolved_generic_params_sm.push(ugp.clone());
                    }

                    let Ok(new_id) = stores.get_generic_function_instance(
                        pass_manager,
                        had_error,
                        id,
                        &resolved_generic_params,
                    ) else {
                        had_error.set();
                        continue;
                    };

                    OpCode::Complex(TypeResolvedOp::CallFunction {
                        id: new_id,
                        generic_params: resolved_generic_params,
                    })
                }
            }
            OpCode::Complex(NameResolvedOp::FunctionPointer { id, generic_params }) => {
                let function_item_header = stores.items.get_item_header(id);
                if function_item_header.kind != ItemKind::GenericFunction {
                    OpCode::Complex(TypeResolvedOp::FunctionPointer {
                        id,
                        generic_params: Vec::new(),
                    })
                } else {
                    let unresolved_generic_params = &generic_params;
                    let mut resolved_generic_params = Vec::new();
                    let mut unresolved_generic_params_sm = SmallVec::<[NameResolvedType; 4]>::new();

                    for ugp in unresolved_generic_params {
                        let mut local_had_error = ErrorSignal::new();
                        ensure_types_declared_in_type(
                            stores,
                            pass_manager,
                            &mut local_had_error,
                            ugp,
                        );
                        if local_had_error.into_err() {
                            had_error.set();
                            continue;
                        }

                        let type_info = match stores.types.resolve_type(stores.strings, ugp) {
                            Ok(info) => info,
                            Err(err_token) => {
                                Diagnostic::type_error(stores, err_token);
                                had_error.set();
                                continue;
                            }
                        };

                        resolved_generic_params.push(type_info.id);
                        unresolved_generic_params_sm.push(ugp.clone());
                    }

                    let Ok(new_id) = stores.get_generic_function_instance(
                        pass_manager,
                        had_error,
                        id,
                        &resolved_generic_params,
                    ) else {
                        had_error.set();
                        continue;
                    };

                    OpCode::Complex(TypeResolvedOp::FunctionPointer {
                        id: new_id,
                        generic_params: resolved_generic_params,
                    })
                }
            }

            OpCode::Complex(NameResolvedOp::Const { id }) => {
                OpCode::Complex(TypeResolvedOp::Const { id })
            }
            OpCode::Complex(NameResolvedOp::Variable { id, is_global }) => {
                OpCode::Complex(TypeResolvedOp::Variable { id, is_global })
            }
            OpCode::Complex(NameResolvedOp::AssumeInit { id }) => {
                OpCode::Complex(TypeResolvedOp::AssumeInit { id })
            }

            OpCode::Complex(
                NameResolvedOp::Cast { ref id }
                | NameResolvedOp::PackEnum { ref id }
                | NameResolvedOp::PackStruct { ref id }
                | NameResolvedOp::SizeOf { ref id },
            ) => {
                let mut local_had_error = ErrorSignal::new();
                ensure_types_declared_in_type(stores, pass_manager, &mut local_had_error, id);
                if local_had_error.into_err() {
                    had_error.set();
                    continue;
                }

                let type_info = match stores.types.resolve_type(stores.strings, id) {
                    Ok(info) => info,
                    Err(err_token) => {
                        Diagnostic::type_error(stores, err_token);
                        had_error.set();
                        continue;
                    }
                };
                let new_code = match old_code {
                    OpCode::Complex(NameResolvedOp::Cast { .. }) => {
                        TypeResolvedOp::Cast { id: type_info.id }
                    }
                    OpCode::Complex(NameResolvedOp::PackEnum { .. }) => {
                        TypeResolvedOp::PackEnum { id: type_info.id }
                    }
                    OpCode::Complex(NameResolvedOp::PackStruct { .. }) => {
                        TypeResolvedOp::PackStruct { id: type_info.id }
                    }
                    OpCode::Complex(NameResolvedOp::SizeOf { .. }) => {
                        TypeResolvedOp::SizeOf { id: type_info.id }
                    }
                    _ => unreachable!(),
                };

                OpCode::Complex(new_code)
            }
        };

        stores.ops.set_type_resolved(op_id, new_code);
    }
}

fn partially_resolve_block(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    unresolved_block_id: BlockId,
) {
    let block = stores.blocks.get_block(unresolved_block_id).clone();
    for op_id in block.ops {
        let old_code = stores.ops.get_name_resolved(op_id).clone();
        let new_code = match old_code {
            OpCode::Basic(bo) => {
                match bo {
                    Basic::Control(Control::Cond(ref cond_op)) => {
                        for arm in &cond_op.arms {
                            partially_resolve_block(stores, pass_manager, had_error, arm.condition);
                            partially_resolve_block(stores, pass_manager, had_error, arm.block);
                        }

                        partially_resolve_block(
                            stores,
                            pass_manager,
                            had_error,
                            cond_op.else_block,
                        );
                    }
                    Basic::Control(Control::While(while_op)) => {
                        partially_resolve_block(
                            stores,
                            pass_manager,
                            had_error,
                            while_op.condition,
                        );
                        partially_resolve_block(
                            stores,
                            pass_manager,
                            had_error,
                            while_op.body_block,
                        );
                    }
                    _ => {}
                }
                OpCode::Basic(bo)
            }

            OpCode::Complex(NameResolvedOp::CallFunction { id, generic_params }) => {
                let called_item_header = stores.items.get_item_header(id);
                if called_item_header.kind != ItemKind::GenericFunction {
                    OpCode::Complex(PartiallyResolvedOp::CallFunction {
                        id,
                        generic_params: Vec::new(),
                    })
                } else if !generic_params.is_empty() {
                    let unresolved_generic_params = &generic_params;
                    let mut resolved_generic_params = Vec::new();

                    for ugp in unresolved_generic_params {
                        let mut local_had_error = ErrorSignal::new();
                        ensure_types_declared_in_type(
                            stores,
                            pass_manager,
                            &mut local_had_error,
                            ugp,
                        );
                        if local_had_error.into_err() {
                            had_error.set();
                            continue;
                        }

                        let type_info = match stores
                            .types
                            .partially_resolve_generic_type(stores.strings, ugp)
                        {
                            Ok(info) => info,
                            Err(err_token) => {
                                Diagnostic::type_error(stores, err_token);
                                had_error.set();
                                continue;
                            }
                        };

                        resolved_generic_params.push(type_info);
                    }

                    OpCode::Complex(PartiallyResolvedOp::CallFunction {
                        id,
                        generic_params: resolved_generic_params,
                    })
                } else {
                    // No parameters were provided, we'll try to resolve this during type checking.
                    OpCode::Complex(PartiallyResolvedOp::CallFunction {
                        id,
                        generic_params: Vec::new(),
                    })
                }
            }
            OpCode::Complex(NameResolvedOp::FunctionPointer { .. }) => todo!(),
            OpCode::Complex(NameResolvedOp::Const { id }) => {
                OpCode::Complex(PartiallyResolvedOp::Const { id })
            }
            OpCode::Complex(NameResolvedOp::Variable { id, is_global }) => {
                OpCode::Complex(PartiallyResolvedOp::Variable { id, is_global })
            }
            OpCode::Complex(NameResolvedOp::AssumeInit { id }) => {
                OpCode::Complex(PartiallyResolvedOp::AssumeInit { id })
            }
            OpCode::Complex(
                NameResolvedOp::Cast { ref id }
                | NameResolvedOp::PackEnum { ref id }
                | NameResolvedOp::PackStruct { ref id }
                | NameResolvedOp::SizeOf { ref id },
            ) => {
                let mut local_had_error = ErrorSignal::new();
                ensure_types_declared_in_type(stores, pass_manager, &mut local_had_error, id);
                if local_had_error.into_err() {
                    had_error.set();
                    continue;
                }

                let resolved_type = match stores
                    .types
                    .partially_resolve_generic_type(stores.strings, id)
                {
                    Ok(info) => info,
                    Err(err_token) => {
                        Diagnostic::type_error(stores, err_token);
                        had_error.set();
                        continue;
                    }
                };
                let new_code = match old_code {
                    OpCode::Complex(NameResolvedOp::Cast { .. }) => {
                        PartiallyResolvedOp::Cast { id: resolved_type }
                    }
                    OpCode::Complex(NameResolvedOp::PackEnum { .. }) => {
                        PartiallyResolvedOp::PackEnum { id: resolved_type }
                    }
                    OpCode::Complex(NameResolvedOp::PackStruct { .. }) => {
                        PartiallyResolvedOp::PackStruct { id: resolved_type }
                    }
                    OpCode::Complex(NameResolvedOp::SizeOf { .. }) => {
                        PartiallyResolvedOp::SizeOf { id: resolved_type }
                    }
                    _ => unreachable!(),
                };

                OpCode::Complex(new_code)
            }
        };

        stores.ops.set_partially_type_resolved(op_id, new_code);
    }
}

pub fn resolve_body(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let cur_item_header = stores.items.get_item_header(cur_id);
    match cur_item_header.kind {
        ItemKind::Variable
        | ItemKind::Module
        | ItemKind::StructDef
        | ItemKind::Enum
        | ItemKind::FunctionDecl
        | ItemKind::Builtin(_) => {
            panic!(
                "ICE: Tried to body type-resolve a {:?}",
                cur_item_header.kind
            );
        }

        ItemKind::GenericFunction => {
            let unresolved_body = stores.items.get_item_body(cur_id);
            partially_resolve_block(stores, pass_manager, had_error, unresolved_body);
        }

        ItemKind::Assert | ItemKind::Const | ItemKind::Function { .. } => {
            let unresolved_body = stores.items.get_item_body(cur_id);
            fully_resolve_block(stores, pass_manager, had_error, unresolved_body);
        }
    };
}
