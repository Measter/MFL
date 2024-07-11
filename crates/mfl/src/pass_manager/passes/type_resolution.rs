use smallvec::SmallVec;

use crate::{
    context::{Context, ItemId, ItemKind, TypeResolvedItemSignature},
    ir::{If, NameResolvedOp, Op, OpCode, TerminalBlock, TypeResolvedOp, While},
    pass_manager::PassContext,
    type_store::{emit_type_error_diag, TypeId, UnresolvedTypeIds},
    Stores,
};

pub fn resolve_signature(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
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

            let mut local_had_error = false;

            let mut process_sig = |unresolved: &[UnresolvedTypeIds], resolved: &mut Vec<TypeId>| {
                for kind in unresolved {
                    if let Some(type_item) = kind.item_id() {
                        *had_error |= pass_ctx
                            .ensure_declare_structs(ctx, stores, type_item)
                            .is_err();
                    }

                    let info = match stores.types.resolve_type(&mut stores.strings, kind) {
                        Ok(info) => info,
                        Err(tk) => {
                            local_had_error = true;
                            emit_type_error_diag(stores, tk);
                            continue;
                        }
                    };

                    resolved.push(info.id);
                }
            };

            process_sig(&unresolved_sig.entry, &mut resolved_sig.entry);
            process_sig(&unresolved_sig.exit, &mut resolved_sig.exit);

            *had_error |= local_had_error;
            if local_had_error {
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
                *had_error |= pass_ctx
                    .ensure_declare_structs(ctx, stores, type_item)
                    .is_err();
            }
            let info = match stores
                .types
                .resolve_type(&mut stores.strings, &memory_type_unresolved)
            {
                Ok(info) => info,
                Err(tk) => {
                    *had_error = true;
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
    had_error: &mut bool,
    unresolved_block: &[Op<NameResolvedOp>],
) -> Vec<Op<TypeResolvedOp>> {
    let mut resolved_block = Vec::new();

    for op in unresolved_block {
        match &op.code {
            OpCode::Basic(bo) => {
                resolved_block.push(Op {
                    code: OpCode::Basic(*bo),
                    id: op.id,
                    token: op.token,
                });
            }

            OpCode::Complex(NameResolvedOp::CallFunction { id, generic_params }) => {
                let called_item_header = ctx.get_item_header(*id);
                if called_item_header.kind != ItemKind::GenericFunction {
                    resolved_block.push(Op {
                        code: OpCode::Complex(TypeResolvedOp::CallFunction { id: *id }),
                        id: op.id,
                        token: op.token,
                    });
                } else if let Some(unresolved_generic_params) = generic_params.as_deref() {
                    dbg!(unresolved_generic_params);
                    let mut resolved_generic_params = SmallVec::<[TypeId; 4]>::new();
                    let mut unresolved_generic_params_sm =
                        SmallVec::<[UnresolvedTypeIds; 4]>::new();

                    for ugp in unresolved_generic_params {
                        if let Some(type_item) = ugp.item_id() {
                            *had_error |= pass_ctx
                                .ensure_declare_structs(ctx, stores, type_item)
                                .is_err();
                        }

                        let type_info = match stores.types.resolve_type(&mut stores.strings, ugp) {
                            Ok(info) => info,
                            Err(err_token) => {
                                emit_type_error_diag(stores, err_token);
                                *had_error = true;
                                continue;
                            }
                        };

                        resolved_generic_params.push(type_info.id);
                        unresolved_generic_params_sm.push(ugp.clone());
                    }

                    let new_id = ctx.get_generic_function_instance(
                        stores,
                        pass_ctx,
                        *id,
                        resolved_generic_params,
                        unresolved_generic_params_sm,
                    );

                    resolved_block.push(Op {
                        code: OpCode::Complex(TypeResolvedOp::CallFunction { id: new_id }),
                        id: op.id,
                        token: op.token,
                    });
                } else {
                    // No parameters were provided, we'll try to resolve this during type checking.
                    resolved_block.push(Op {
                        code: OpCode::Complex(TypeResolvedOp::CallFunction { id: *id }),
                        id: op.id,
                        token: op.token,
                    });
                }
            }
            OpCode::Complex(NameResolvedOp::Const { id }) => resolved_block.push(Op {
                code: OpCode::Complex(TypeResolvedOp::Const { id: *id }),
                id: op.id,
                token: op.token,
            }),
            OpCode::Complex(NameResolvedOp::Memory { id, is_global }) => resolved_block.push(Op {
                code: OpCode::Complex(TypeResolvedOp::Memory {
                    id: *id,
                    is_global: *is_global,
                }),
                id: op.id,
                token: op.token,
            }),

            OpCode::Complex(NameResolvedOp::If(if_op)) => {
                let resolved_condition =
                    resolve_block(ctx, stores, pass_ctx, had_error, &if_op.condition.block);
                let resolved_then =
                    resolve_block(ctx, stores, pass_ctx, had_error, &if_op.then_block.block);
                let resolved_else =
                    resolve_block(ctx, stores, pass_ctx, had_error, &if_op.else_block.block);

                resolved_block.push(Op {
                    code: OpCode::Complex(TypeResolvedOp::If(Box::new(If {
                        tokens: if_op.tokens,
                        condition: TerminalBlock {
                            block: resolved_condition,
                            is_terminal: false,
                        },
                        then_block: TerminalBlock {
                            block: resolved_then,
                            is_terminal: false,
                        },
                        else_block: TerminalBlock {
                            block: resolved_else,
                            is_terminal: false,
                        },
                    }))),
                    id: op.id,
                    token: op.token,
                })
            }
            OpCode::Complex(NameResolvedOp::While(while_op)) => {
                let resolved_condition =
                    resolve_block(ctx, stores, pass_ctx, had_error, &while_op.condition.block);
                let resolved_body =
                    resolve_block(ctx, stores, pass_ctx, had_error, &while_op.body_block.block);

                resolved_block.push(Op {
                    code: OpCode::Complex(TypeResolvedOp::While(Box::new(While {
                        tokens: while_op.tokens,
                        condition: TerminalBlock {
                            block: resolved_condition,
                            is_terminal: false,
                        },
                        body_block: TerminalBlock {
                            block: resolved_body,
                            is_terminal: false,
                        },
                    }))),
                    id: op.id,
                    token: op.token,
                })
            }

            OpCode::Complex(NameResolvedOp::Cast { id })
            | OpCode::Complex(NameResolvedOp::PackStruct { id })
            | OpCode::Complex(NameResolvedOp::SizeOf { id }) => {
                if let Some(type_item) = id.item_id() {
                    *had_error |= pass_ctx
                        .ensure_declare_structs(ctx, stores, type_item)
                        .is_err();
                }
                let type_info = match stores.types.resolve_type(&mut stores.strings, id) {
                    Ok(info) => info,
                    Err(err_token) => {
                        emit_type_error_diag(stores, err_token);
                        *had_error = true;
                        continue;
                    }
                };
                let new_code = match &op.code {
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

                resolved_block.push(Op {
                    code: OpCode::Complex(new_code),
                    id: op.id,
                    token: op.token,
                });
            }
        }
    }

    resolved_block
}

pub fn resolve_body(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
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
            let unresolved_body = ctx.nrir().get_item_body(cur_id).to_owned();
            let resolved_body = resolve_block(ctx, stores, pass_ctx, had_error, &unresolved_body);
            ctx.trir_mut().set_item_body(cur_id, resolved_body);
        }
    };
}
