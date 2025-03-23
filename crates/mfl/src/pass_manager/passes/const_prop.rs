use hashbrown::HashMap;
use intcast::IntCast;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Compare, Control, Memory, OpCode, Stack, TypeResolvedOp},
    pass_manager::PassManager,
    stores::{
        block::BlockId,
        item::ItemKind,
        types::{TypeId, TypeKind, TypeStore},
        values::{ConstVal, Offset},
    },
    Stores,
};

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

fn write_const_val_to_variable(
    type_store: &mut TypeStore,
    state: &mut ConstVal,
    to_store_value: &ConstVal,
    cur_pointed_at_type: TypeId,
    mut offsets: std::slice::Iter<'_, Offset>,
) {
    if let Some(next) = offsets.next() {
        let var_type_info = type_store.get_type_info(cur_pointed_at_type);
        match var_type_info.kind {
            TypeKind::Array { type_id, .. } => {
                let ConstVal::Aggregate { sub_values } = state else {
                    unreachable!()
                };

                match next {
                    Offset::Unknown => {
                        // We are in an array, but don't know where in the array we are writing to.
                        // We should iterate over each index in the array, and write a final ConstVal::Unknown.
                        for sv in sub_values {
                            write_const_val_to_variable(
                                type_store,
                                sv,
                                &ConstVal::Unknown,
                                type_id,
                                offsets.clone(),
                            );
                        }
                    }
                    Offset::Known(offset) => {
                        write_const_val_to_variable(
                            type_store,
                            &mut sub_values[offset.to_usize()],
                            to_store_value,
                            type_id,
                            offsets,
                        );
                    }
                }
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let ConstVal::Aggregate { sub_values } = state else {
                    unreachable!()
                };

                let struct_def = type_store.get_struct_def(cur_pointed_at_type);
                let Offset::Known(offset) = next else {
                    panic!("ICE: struct field offset is unknown")
                };
                write_const_val_to_variable(
                    type_store,
                    &mut sub_values[offset.to_usize()],
                    to_store_value,
                    struct_def.fields[offset.to_usize()].kind.inner,
                    offsets,
                );
            }

            _ => unreachable!(),
        }
    } else {
        // No more offsets to go, we've reached the final destination
        *state = to_store_value.clone();
    }
}

fn analyze_block(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    block_id: BlockId,
) {
    let block = stores.blocks.get_block(block_id).clone();
    for op_id in block.ops {
        let op_code = stores.ops.get_type_resolved(op_id).clone();
        match op_code {
            OpCode::Basic(bo) => match bo {
                Basic::Arithmetic(ao) => match ao {
                    Arithmetic::Add => arithmetic::add(stores, op_id, ao),
                    Arithmetic::BitAnd | Arithmetic::BitOr | Arithmetic::BitXor => {
                        arithmetic::bitand_bitor_bitxor(stores, op_id, ao)
                    }
                    Arithmetic::BitNot => arithmetic::bitnot(stores, op_id),
                    Arithmetic::Div
                    | Arithmetic::Multiply
                    | Arithmetic::Rem
                    | Arithmetic::ShiftLeft
                    | Arithmetic::ShiftRight => {
                        arithmetic::multiply_div_rem_shift(stores, had_error, item_id, op_id, ao)
                    }
                    Arithmetic::Subtract => {
                        arithmetic::subtract(stores, had_error, item_id, op_id, ao)
                    }
                },
                Basic::Compare(co) => match co {
                    Compare::Equal | Compare::NotEq => {
                        comparative::equal(stores, had_error, item_id, op_id, co)
                    }
                    Compare::Less
                    | Compare::LessEqual
                    | Compare::Greater
                    | Compare::GreaterEqual => {
                        comparative::compare(stores, had_error, item_id, op_id, co)
                    }
                    Compare::IsNull => comparative::is_null(stores, op_id),
                },
                Basic::Stack(so) => match so {
                    Stack::Dup { .. }
                    | Stack::Over { .. }
                    | Stack::Reverse { .. }
                    | Stack::Rotate { .. }
                    | Stack::Swap { .. } => stack_ops::dup_over_rotate_swap_reverse(stores, op_id),

                    // No work to do here
                    Stack::Drop { .. } | Stack::Emit { .. } => {}
                },
                Basic::Control(co) => match co {
                    Control::Epilogue | Control::Return => {
                        control::epilogue_return(stores, had_error, item_id, op_id);

                        // We're terminated the current block, so don't process any remaining ops.
                        break;
                    }

                    Control::Prologue => {
                        control::prologue(
                            stores,
                            pass_manager,
                            had_error,
                            variable_state,
                            item_id,
                            op_id,
                        );
                    }
                    Control::Exit(_) => {
                        // We're terminating the current block, so don't process any remaning ops.
                        break;
                    }
                    Control::MethodCall { .. } => control::call_function(
                        stores,
                        pass_manager,
                        variable_state,
                        had_error,
                        op_id,
                    ),

                    // Nothing to do here.
                    Control::SysCall { .. } => {}
                    Control::Cond(cond_op) => {
                        let is_all_terminal = cond_op.is_all_terminal(stores);

                        control::analyze_cond(
                            stores,
                            pass_manager,
                            variable_state,
                            had_error,
                            item_id,
                            op_id,
                            cond_op,
                        );

                        if is_all_terminal {
                            break;
                        }
                    }
                    Control::While(while_op) => {
                        control::analyze_while(
                            stores,
                            pass_manager,
                            variable_state,
                            had_error,
                            item_id,
                            op_id,
                            while_op,
                        );
                    }
                },
                Basic::Memory(mo) => match mo {
                    Memory::Index => memory::index(stores, had_error, item_id, op_id),
                    Memory::FieldAccess { field_name } => {
                        memory::field_access(stores, field_name.inner, op_id)
                    }
                    Memory::InitArray { count } => memory::init_array(stores, op_id, count),
                    Memory::InsertArray { .. } => {
                        memory::insert_array(
                            stores,
                            pass_manager,
                            had_error,
                            variable_state,
                            item_id,
                            op_id,
                        );
                    }
                    Memory::ExtractArray { .. } => memory::extract_array(
                        stores,
                        pass_manager,
                        had_error,
                        variable_state,
                        item_id,
                        op_id,
                    ),
                    Memory::Load => {
                        memory::load(
                            stores,
                            pass_manager,
                            variable_state,
                            had_error,
                            item_id,
                            op_id,
                        );
                    }
                    Memory::Store => {
                        memory::store(stores, variable_state, op_id);
                    }
                    Memory::PackArray { .. } => memory::pack_struct_and_array(stores, op_id),
                    Memory::InsertStruct { field_name, .. } => {
                        memory::insert_struct(stores, variable_state, op_id, field_name.inner)
                    }
                    Memory::ExtractStruct { field_name, .. } => memory::extract_struct(
                        stores,
                        pass_manager,
                        had_error,
                        variable_state,
                        op_id,
                        field_name.inner,
                    ),
                    Memory::Unpack => memory::unpack(stores, op_id),
                },
                Basic::PushBool(value) => stack_ops::push_bool(stores, op_id, value),
                Basic::PushInt { value, .. } => stack_ops::push_int(stores, op_id, value),
                Basic::PushFloat { value, .. } => stack_ops::push_float(stores, op_id, value),
                Basic::PushStr { .. } | Basic::Here => {
                    stack_ops::push_str(stores, pass_manager, had_error, item_id, op_id)
                }
            },
            OpCode::Complex(co) => match co {
                TypeResolvedOp::Cast { id } => stack_ops::cast(stores, op_id, id),
                TypeResolvedOp::Const { id } => control::cp_const(stores, pass_manager, op_id, id),
                TypeResolvedOp::PackEnum { id } => memory::pack_enum(stores, op_id, id),
                TypeResolvedOp::Variable { id, .. } => control::variable(stores, op_id, id),
                TypeResolvedOp::SizeOf { id } => {
                    stack_ops::size_of(stores, pass_manager, op_id, id)
                }
                TypeResolvedOp::AssumeInit { id } => {
                    memory::init_local(stores, pass_manager, had_error, variable_state, id);
                }
                TypeResolvedOp::CallFunction { .. } => {
                    control::call_function(stores, pass_manager, variable_state, had_error, op_id)
                }
                TypeResolvedOp::PackStruct { .. } => memory::pack_struct_and_array(stores, op_id),
                // Nothing to do here.
                TypeResolvedOp::FunctionPointer { .. } => {}
            },
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ConstFieldInitState {
    Unknown,
    Uninitialized,
}

impl From<ConstFieldInitState> for ConstVal {
    fn from(value: ConstFieldInitState) -> Self {
        match value {
            ConstFieldInitState::Unknown => ConstVal::Unknown,
            ConstFieldInitState::Uninitialized => ConstVal::Uninitialized,
        }
    }
}

fn new_const_val_for_type(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    type_id: TypeId,
    initial_value: ConstFieldInitState,
) -> ConstVal {
    let type_info = stores.types.get_type_info(type_id);
    match type_info.kind {
        TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::FunctionPointer
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_)
        | TypeKind::Bool
        | TypeKind::Enum(_) => initial_value.into(),

        TypeKind::Array { type_id, length } => {
            let elems = (0..length)
                .map(|_| {
                    new_const_val_for_type(stores, pass_manager, had_error, type_id, initial_value)
                })
                .collect();
            ConstVal::Aggregate { sub_values: elems }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            // Generic instances are always defined, so we should only handle non-generic structs for this
            if let TypeKind::Struct(struct_id) = type_info.kind {
                if pass_manager
                    .ensure_define_structs(stores, struct_id)
                    .is_err()
                {
                    had_error.set();
                    return initial_value.into();
                }
            }

            let mut elems = Vec::new();
            let struct_def = stores.types.get_struct_def(type_id).clone();
            if struct_def.is_union {
                elems.push(initial_value.into());
            } else {
                for field in &struct_def.fields {
                    elems.push(new_const_val_for_type(
                        stores,
                        pass_manager,
                        had_error,
                        field.kind.inner,
                        initial_value,
                    ));
                }
            }

            ConstVal::Aggregate { sub_values: elems }
        }

        TypeKind::GenericStructBase(_) => unreachable!(),
    }
}

pub fn analyze_item(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
) {
    let mut variable_state = HashMap::new();
    let function_children = stores
        .sigs
        .nrir
        .get_scope(item_id)
        .get_child_items()
        .to_owned();

    for child_id in function_children {
        if pass_manager
            .ensure_type_resolved_signature(stores, child_id)
            .is_err()
        {
            variable_state.insert(child_id, ConstVal::Uninitialized);
            had_error.set();
            continue;
        }

        let child_header = stores.items.get_item_header(child_id);
        if child_header.kind == ItemKind::Variable {
            let var_type = stores.sigs.trir.get_variable_type(child_id);

            variable_state.insert(
                child_id,
                new_const_val_for_type(
                    stores,
                    pass_manager,
                    had_error,
                    var_type,
                    ConstFieldInitState::Uninitialized,
                ),
            );
        }
    }

    let block_id = stores.items.get_item_body(item_id);
    analyze_block(
        stores,
        pass_manager,
        &mut variable_state,
        had_error,
        item_id,
        block_id,
    );
}
