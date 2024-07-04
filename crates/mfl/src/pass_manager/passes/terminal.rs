use crate::{
    context::{Context, ItemId, ItemKind},
    ir::{Basic, Control, Op, OpCode, TypeResolvedOp},
};

pub fn determine_terminal_blocks(ctx: &mut Context, cur_id: ItemId) {
    let item_header = ctx.get_item_header(cur_id);
    match item_header.kind {
        ItemKind::StructDef | ItemKind::Memory | ItemKind::Module => return,
        ItemKind::Assert | ItemKind::Const | ItemKind::Function | ItemKind::GenericFunction => (),
    }

    let body = ctx.trir_mut().get_item_body_mut(cur_id);
    determine_terminal_blocks_in_block(body);
}

fn determine_terminal_blocks_in_block(block: &mut [Op<TypeResolvedOp>]) -> bool {
    for op in block {
        match &mut op.code {
            OpCode::Basic(Basic::Control(Control::Exit | Control::Return)) => return true,
            OpCode::Complex(TypeResolvedOp::If(if_op)) => {
                if_op.condition.is_terminal =
                    determine_terminal_blocks_in_block(&mut if_op.condition.block);
                if_op.then_block.is_terminal =
                    determine_terminal_blocks_in_block(&mut if_op.then_block.block);
                if_op.else_block.is_terminal =
                    determine_terminal_blocks_in_block(&mut if_op.else_block.block);

                if if_op.condition.is_terminal
                    | (if_op.then_block.is_terminal && if_op.else_block.is_terminal)
                {
                    return true;
                }
            }
            OpCode::Complex(TypeResolvedOp::While(while_op)) => {
                while_op.condition.is_terminal =
                    determine_terminal_blocks_in_block(&mut while_op.condition.block);
                while_op.body_block.is_terminal =
                    determine_terminal_blocks_in_block(&mut while_op.body_block.block);
                if while_op.condition.is_terminal || while_op.body_block.is_terminal {
                    return true;
                }
            }
            _ => {}
        }
    }

    false
}
