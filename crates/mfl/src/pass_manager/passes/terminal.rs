use stores::items::ItemId;

use crate::{
    ir::{Basic, Control, OpCode},
    stores::{block::BlockId, item::ItemKind, Stores},
};

pub fn determine_terminal_blocks(stores: &mut Stores, cur_id: ItemId) {
    let item_header = stores.items.get_item_header(cur_id);
    match item_header.kind {
        ItemKind::StructDef | ItemKind::Variable | ItemKind::Module | ItemKind::FunctionDecl => {
            return
        }
        ItemKind::Assert
        | ItemKind::Const
        | ItemKind::Function { .. }
        | ItemKind::GenericFunction => (),
    }

    let body = stores.items.get_item_body(cur_id);
    determine_terminal_blocks_in_block(stores, body);
}

fn determine_terminal_blocks_in_block(stores: &mut Stores, block_id: BlockId) -> bool {
    let block = stores.blocks.get_block(block_id).clone();
    for op_id in block.ops {
        let op_code = stores.ops.get_unresolved(op_id);
        let OpCode::Basic(Basic::Control(cont_op)) = op_code else {
            continue;
        };

        match cont_op {
            Control::Exit(_) | Control::Return => {
                stores.blocks.set_terminal(block_id);
                return true;
            }
            Control::Cond(cond_op) => {
                let else_block = cond_op.else_block;
                let arms = cond_op.arms.clone();

                let mut all_arms_terminal = determine_terminal_blocks_in_block(stores, else_block);
                for arm in arms {
                    let condition_terminal =
                        determine_terminal_blocks_in_block(stores, arm.condition);
                    let block_terminal = determine_terminal_blocks_in_block(stores, arm.block);
                    all_arms_terminal &= condition_terminal | block_terminal;
                }

                if all_arms_terminal {
                    stores.blocks.set_terminal(block_id);
                    return true;
                }
            }
            Control::While(while_op) => {
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
