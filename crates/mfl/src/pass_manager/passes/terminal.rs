use crate::{
    context::{Context, ItemId, ItemKind},
    ir::{Basic, Control, OpCode, UnresolvedOp},
    stores::{ops::OpId, Stores},
};

pub fn determine_terminal_blocks(ctx: &mut Context, stores: &mut Stores, cur_id: ItemId) {
    let item_header = ctx.get_item_header(cur_id);
    match item_header.kind {
        ItemKind::StructDef | ItemKind::Memory | ItemKind::Module => return,
        ItemKind::Assert | ItemKind::Const | ItemKind::Function | ItemKind::GenericFunction => (),
    }

    let body = ctx.get_item_body(cur_id).to_owned();
    determine_terminal_blocks_in_block(stores, &body);
}

fn determine_terminal_blocks_in_block(stores: &mut Stores, block: &[OpId]) -> bool {
    for &op_id in block {
        let op_code = stores.ops.get_unresolved(op_id);
        match op_code {
            OpCode::Basic(Basic::Control(Control::Exit | Control::Return)) => return true,
            OpCode::Complex(UnresolvedOp::If(if_op)) => {
                todo!()
                // if_op.condition.is_terminal =
                //     determine_terminal_blocks_in_block(&mut if_op.condition.block);
                // if_op.then_block.is_terminal =
                //     determine_terminal_blocks_in_block(&mut if_op.then_block.block);
                // if_op.else_block.is_terminal =
                //     determine_terminal_blocks_in_block(&mut if_op.else_block.block);

                // if if_op.condition.is_terminal
                //     | (if_op.then_block.is_terminal && if_op.else_block.is_terminal)
                // {
                //     return true;
                // }
            }
            OpCode::Complex(UnresolvedOp::While(while_op)) => {
                todo!()
                // while_op.condition.is_terminal =
                //     determine_terminal_blocks_in_block(&mut while_op.condition.block);
                // while_op.body_block.is_terminal =
                //     determine_terminal_blocks_in_block(&mut while_op.body_block.block);
                // if while_op.condition.is_terminal || while_op.body_block.is_terminal {
                //     return true;
                // }
            }
            _ => {}
        }
    }

    false
}
