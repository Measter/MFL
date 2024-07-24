use crate::{
    context::{Context, ItemId, ItemKind},
    ir::{Basic, Control, OpCode, UnresolvedOp},
    stores::{block::BlockId, Stores},
};

pub fn determine_terminal_blocks(ctx: &mut Context, stores: &mut Stores, cur_id: ItemId) {
    let item_header = ctx.get_item_header(cur_id);
    match item_header.kind {
        ItemKind::StructDef | ItemKind::Memory | ItemKind::Module => return,
        ItemKind::Assert | ItemKind::Const | ItemKind::Function | ItemKind::GenericFunction => (),
    }

    let body = ctx.get_item_body(cur_id).to_owned();
    determine_terminal_blocks_in_block(stores, body);
}

fn determine_terminal_blocks_in_block(stores: &mut Stores, block_id: BlockId) -> bool {
    let block = stores.blocks.get_block(block_id).clone();
    for op_id in block.ops {
        let op_code = stores.ops.get_unresolved(op_id);
        match op_code {
            OpCode::Basic(Basic::Control(Control::Exit | Control::Return)) => {
                stores.blocks.set_terminal(block_id);
                return true;
            }
            OpCode::Complex(UnresolvedOp::If(if_op)) => {
                let condition_id = if_op.condition;
                let then_id = if_op.then_block;
                let else_id = if_op.else_block;

                let condition_terminal = determine_terminal_blocks_in_block(stores, condition_id);
                let else_terminal = determine_terminal_blocks_in_block(stores, else_id);
                let then_terminal = determine_terminal_blocks_in_block(stores, then_id);

                if condition_terminal || (then_terminal && else_terminal) {
                    stores.blocks.set_terminal(block_id);
                    return true;
                }
            }
            OpCode::Complex(UnresolvedOp::While(while_op)) => {
                let condition_id = while_op.condition;
                let body_id = while_op.body_block;

                let condition_terminal = determine_terminal_blocks_in_block(stores, condition_id);
                determine_terminal_blocks_in_block(stores, body_id);

                if condition_terminal {
                    stores.blocks.set_terminal(block_id);
                    return true;
                }
            }
            _ => {}
        }
    }

    false
}
