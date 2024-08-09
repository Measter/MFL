use hashbrown::HashMap;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Compare, Control, Memory, OpCode, Stack, TypeResolvedOp},
    pass_manager::PassManager,
    stores::{block::BlockId, item::ItemKind, values::ConstVal},
    Stores,
};

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

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
                        arithmetic::multiply_div_rem_shift(stores, had_error, op_id, ao)
                    }
                    Arithmetic::Subtract => arithmetic::subtract(stores, had_error, op_id, ao),
                },
                Basic::Compare(co) => match co {
                    Compare::Equal | Compare::NotEq => {
                        comparative::equal(stores, had_error, op_id, co)
                    }
                    Compare::Less
                    | Compare::LessEqual
                    | Compare::Greater
                    | Compare::GreaterEqual => comparative::compare(stores, had_error, op_id, co),
                    Compare::IsNull => comparative::is_null(stores, op_id),
                },
                Basic::Stack(so) => match so {
                    Stack::Dup { .. } | Stack::Over { .. } => stack_ops::dup_over(stores, op_id),

                    // These just change the order of the virtual stack, so there's no work to do here.
                    Stack::Drop { .. }
                    | Stack::Emit { .. }
                    | Stack::Reverse { .. }
                    | Stack::Rotate { .. }
                    | Stack::Swap { .. } => {}
                },
                Basic::Control(co) => match co {
                    Control::Epilogue | Control::Return => {
                        control::epilogue_return(stores, had_error, op_id);

                        // We're terminated the current block, so don't process any remaining ops.
                        break;
                    }

                    Control::Prologue => {
                        control::prologue(stores, variable_state, item_id);
                    }
                    // Nothing to do here.
                    Control::Exit | Control::SysCall { .. } => {}
                    Control::If(if_op) => {
                        control::analyze_if(
                            stores,
                            pass_manager,
                            variable_state,
                            had_error,
                            item_id,
                            if_op,
                        );

                        if stores.blocks.is_terminal(if_op.else_block)
                            && stores.blocks.is_terminal(if_op.then_block)
                        {
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
                            while_op,
                        );
                    }
                },
                Basic::Memory(mo) => match mo {
                    Memory::ExtractArray { .. } | Memory::InsertArray { .. } => {
                        memory::insert_extract_array(stores, had_error, op_id)
                    }
                    Memory::Load => {
                        memory::load(stores, variable_state, had_error, op_id);
                    }
                    Memory::Store => {
                        memory::store(stores, variable_state, op_id);
                    }

                    // Nothing to do here.
                    Memory::ExtractStruct { .. }
                    | Memory::InsertStruct { .. }
                    | Memory::FieldAccess { .. }
                    | Memory::PackArray { .. }
                    | Memory::Unpack => {}
                },
                Basic::PushBool(value) => stack_ops::push_bool(stores, op_id, value),
                Basic::PushInt { value, .. } => stack_ops::push_int(stores, op_id, value),
                Basic::PushFloat { value, .. } => stack_ops::push_float(stores, op_id, value),
                Basic::PushStr { .. } => {}
            },
            OpCode::Complex(co) => match co {
                TypeResolvedOp::Cast { id } => stack_ops::cast(stores, op_id, id),
                TypeResolvedOp::Const { id } => control::cp_const(stores, pass_manager, op_id, id),
                TypeResolvedOp::Variable { id, .. } => control::variable(stores, op_id, id),
                TypeResolvedOp::SizeOf { id } => {
                    stack_ops::size_of(stores, pass_manager, op_id, id)
                }
                TypeResolvedOp::AssumeInit { id } => {
                    memory::init_local(variable_state, id);
                }

                // Nothing to do here.
                TypeResolvedOp::CallFunction { .. } | TypeResolvedOp::PackStruct { .. } => {}
            },
        }
    }
}

pub fn analyze_item(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
) {
    let mut variable_state = HashMap::new();
    for (_, &child_id) in stores.sigs.nrir.get_scope(item_id).get_child_items() {
        let child_header = stores.items.get_item_header(child_id.inner);
        if child_header.kind == ItemKind::Variable {
            variable_state.insert(child_id.inner, ConstVal::Uninitialized);
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
