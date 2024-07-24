use smallvec::SmallVec;

use crate::{
    context::{Context, ItemId, ItemKind, TypeResolvedItemSignature},
    error_signal::ErrorSignal,
    ir::{NameResolvedOp, NameResolvedType, OpCode, TypeResolvedOp},
    pass_manager::PassContext,
    stores::{
        ops::OpId,
        types::{emit_type_error_diag, TypeId},
    },
    Stores,
};

fn ensure_structs_declared_in_type(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    unresolved: &NameResolvedType,
) {
    match unresolved {
        NameResolvedType::SimpleCustom { id, .. } => {
            if pass_ctx.ensure_declare_structs(ctx, stores, *id).is_err() {
                had_error.set();
            }
        }
        NameResolvedType::GenericInstance { id, params, .. } => {
            if pass_ctx.ensure_declare_structs(ctx, stores, *id).is_err() {
                had_error.set();
            }
            for p in params {
                ensure_structs_declared_in_type(ctx, stores, pass_ctx, had_error, p);
            }
        }
        NameResolvedType::SimpleBuiltin(_) | NameResolvedType::SimpleGenericParam(_) => {}
        NameResolvedType::Array(sub_type, _) | NameResolvedType::Pointer(sub_type) => {
            ensure_structs_declared_in_type(ctx, stores, pass_ctx, had_error, sub_type);
        }
    };
}

pub fn resolve_signature(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let cur_item_header = ctx.get_item_header(cur_id);
    match cur_item_header.kind {
        ItemKind::GenericFunction | ItemKind::Module | ItemKind::StructDef => {
            panic!(
                "ICE: Tried to resolve_signature on a {:?}",
                cur_item_header.kind
            )
        }

        ItemKind::Assert | ItemKind::Const | ItemKind::Function => {
            let unresolved_sig = ctx.nrir().get_item_signature(cur_id).clone();
            let mut resolved_sig = TypeResolvedItemSignature {
                exit: Vec::new(),
                entry: Vec::new(),
            };

            let mut local_had_error = ErrorSignal::new();

            let mut process_sig = |unresolved: &[NameResolvedType], resolved: &mut Vec<TypeId>| {
                for kind in unresolved {
                    {
                        let mut single_check_error = ErrorSignal::new();
                        ensure_structs_declared_in_type(
                            ctx,
                            stores,
                            pass_ctx,
                            &mut single_check_error,
                            kind,
                        );
                        if single_check_error.into_bool() {
                            local_had_error.set();
                            continue;
                        }
                    }

                    let info = match stores.types.resolve_type(&mut stores.strings, kind) {
                        Ok(info) => info,
                        Err(tk) => {
                            local_had_error.set();
                            dbg!();
                            emit_type_error_diag(stores, tk);
                            continue;
                        }
                    };

                    resolved.push(info.id);
                }
            };

            process_sig(&unresolved_sig.entry, &mut resolved_sig.entry);
            process_sig(&unresolved_sig.exit, &mut resolved_sig.exit);

            if local_had_error.into_bool() {
                had_error.set();
                return;
            }

            ctx.trir_mut().set_item_signature(cur_id, resolved_sig);
        }
        ItemKind::Memory => {
            if cur_item_header
                .parent
                .is_some_and(|ph| ctx.get_item_header(ph).kind == ItemKind::GenericFunction)
            {
                // These shouldn't be processed at all until instantiation.
                return;
            }

            let memory_type_unresolved = ctx.nrir().get_memory_type(cur_id).clone();
            if let Some(type_item) = memory_type_unresolved.item_id() {
                if pass_ctx
                    .ensure_declare_structs(ctx, stores, type_item)
                    .is_err()
                {
                    had_error.set();
                }
            }
            let info = match stores
                .types
                .resolve_type(&mut stores.strings, &memory_type_unresolved)
            {
                Ok(info) => info,
                Err(tk) => {
                    had_error.set();
                    emit_type_error_diag(stores, tk);
                    return;
                }
            };

            ctx.trir_mut().set_memory_type(cur_id, info.id);
        }
    }
}

fn resolve_block(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    unresolved_block: &[OpId],
) {
    for &op_id in unresolved_block {
        let old_code = stores.ops.get_name_resolved(op_id).clone();
        let new_code = match old_code {
            OpCode::Basic(bo) => OpCode::Basic(bo),

            OpCode::Complex(NameResolvedOp::CallFunction { id, generic_params }) => {
                let called_item_header = ctx.get_item_header(id);
                if called_item_header.kind != ItemKind::GenericFunction {
                    OpCode::Complex(TypeResolvedOp::CallFunction { id })
                } else if let Some(unresolved_generic_params) = generic_params.as_deref() {
                    let mut resolved_generic_params = SmallVec::<[TypeId; 4]>::new();
                    let mut unresolved_generic_params_sm = SmallVec::<[NameResolvedType; 4]>::new();

                    for ugp in unresolved_generic_params {
                        let mut local_had_error = ErrorSignal::new();
                        ensure_structs_declared_in_type(
                            ctx,
                            stores,
                            pass_ctx,
                            &mut local_had_error,
                            ugp,
                        );
                        if local_had_error.into_bool() {
                            had_error.set();
                            continue;
                        }

                        let type_info = match stores.types.resolve_type(&mut stores.strings, ugp) {
                            Ok(info) => info,
                            Err(err_token) => {
                                emit_type_error_diag(stores, err_token);
                                had_error.set();
                                continue;
                            }
                        };

                        resolved_generic_params.push(type_info.id);
                        unresolved_generic_params_sm.push(ugp.clone());
                    }

                    let Ok(new_id) = ctx.get_generic_function_instance(
                        stores,
                        pass_ctx,
                        had_error,
                        id,
                        resolved_generic_params,
                        unresolved_generic_params_sm,
                    ) else {
                        had_error.set();
                        continue;
                    };

                    OpCode::Complex(TypeResolvedOp::CallFunction { id: new_id })
                } else {
                    // No parameters were provided, we'll try to resolve this during type checking.
                    OpCode::Complex(TypeResolvedOp::CallFunction { id })
                }
            }
            OpCode::Complex(NameResolvedOp::Const { id }) => {
                OpCode::Complex(TypeResolvedOp::Const { id })
            }
            OpCode::Complex(NameResolvedOp::Memory { id, is_global }) => {
                OpCode::Complex(TypeResolvedOp::Memory { id, is_global })
            }

            OpCode::Complex(NameResolvedOp::If(if_op)) => {
                resolve_block(ctx, stores, pass_ctx, had_error, &if_op.condition.block);
                resolve_block(ctx, stores, pass_ctx, had_error, &if_op.then_block.block);
                resolve_block(ctx, stores, pass_ctx, had_error, &if_op.else_block.block);
                OpCode::Complex(TypeResolvedOp::If(if_op.clone()))
            }
            OpCode::Complex(NameResolvedOp::While(while_op)) => {
                resolve_block(ctx, stores, pass_ctx, had_error, &while_op.condition.block);
                resolve_block(ctx, stores, pass_ctx, had_error, &while_op.body_block.block);
                OpCode::Complex(TypeResolvedOp::While(while_op.clone()))
            }

            OpCode::Complex(NameResolvedOp::Cast { ref id })
            | OpCode::Complex(NameResolvedOp::PackStruct { ref id })
            | OpCode::Complex(NameResolvedOp::SizeOf { ref id }) => {
                let mut local_had_error = ErrorSignal::new();
                ensure_structs_declared_in_type(ctx, stores, pass_ctx, &mut local_had_error, id);
                if local_had_error.into_bool() {
                    had_error.set();
                    continue;
                }

                let type_info = match stores.types.resolve_type(&mut stores.strings, id) {
                    Ok(info) => info,
                    Err(err_token) => {
                        emit_type_error_diag(stores, err_token);
                        had_error.set();
                        continue;
                    }
                };
                let new_code = match old_code {
                    OpCode::Complex(NameResolvedOp::Cast { .. }) => {
                        TypeResolvedOp::Cast { id: type_info.id }
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

pub fn resolve_body(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let cur_item_header = ctx.get_item_header(cur_id);
    match cur_item_header.kind {
        ItemKind::GenericFunction | ItemKind::Memory | ItemKind::Module | ItemKind::StructDef => {
            panic!(
                "ICE: Tried to body type-resolve a {:?}",
                cur_item_header.kind
            );
        }

        ItemKind::Assert | ItemKind::Const | ItemKind::Function => {
            let unresolved_body = ctx.get_item_body(cur_id).to_owned();
            resolve_block(ctx, stores, pass_ctx, had_error, &unresolved_body);
        }
    };
}
