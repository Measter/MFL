use ariadne::{Color, Label};
use hashbrown::HashSet;

use crate::{
    context::{Context, ItemHeader, ItemId, ItemKind},
    diagnostics,
    ir::{NameResolvedOp, Op, OpCode},
    pass_manager::PassContext,
    Stores,
};

pub fn check_invalid_cycles(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    cur_id: ItemId,
) {
    let root_header = ctx.get_item_header(cur_id);

    if !matches!(root_header.kind, ItemKind::Assert | ItemKind::Const) {
        // Nothing to do here.
        return;
    }

    let mut check_queue = vec![cur_id];
    let mut checked_items = HashSet::new();

    while let Some(item) = check_queue.pop() {
        let header = ctx.get_item_header(cur_id);
        if item != cur_id {
            *had_error |= pass_ctx
                .ensure_ident_resolved_body(ctx, stores, item)
                .is_err();
        }

        check_invalid_cyclic_refs_in_block(
            stores,
            had_error,
            root_header,
            ctx.nrir().get_item_body(item),
            header,
            &mut checked_items,
            &mut check_queue,
        );
    }
}

fn check_invalid_cyclic_refs_in_block(
    stores: &mut Stores,
    had_error: &mut bool,
    root_header: ItemHeader,
    block: &[Op<NameResolvedOp>],
    cur_header: ItemHeader,
    checked_items: &mut HashSet<ItemId>,
    check_queue: &mut Vec<ItemId>,
) {
    let kind_str = match root_header.kind {
        ItemKind::Assert => "assert",
        ItemKind::Const => "const",
        _ => unreachable!(),
    };

    for op in block {
        match &op.code {
            OpCode::Complex(NameResolvedOp::If(if_op)) => {
                check_invalid_cyclic_refs_in_block(
                    stores,
                    had_error,
                    root_header,
                    &if_op.condition.block,
                    cur_header,
                    checked_items,
                    check_queue,
                );
                check_invalid_cyclic_refs_in_block(
                    stores,
                    had_error,
                    root_header,
                    &if_op.then_block.block,
                    cur_header,
                    checked_items,
                    check_queue,
                );
                check_invalid_cyclic_refs_in_block(
                    stores,
                    had_error,
                    root_header,
                    &if_op.else_block.block,
                    cur_header,
                    checked_items,
                    check_queue,
                );
            }
            OpCode::Complex(NameResolvedOp::While(while_op)) => {
                check_invalid_cyclic_refs_in_block(
                    stores,
                    had_error,
                    root_header,
                    &while_op.condition.block,
                    cur_header,
                    checked_items,
                    check_queue,
                );
                check_invalid_cyclic_refs_in_block(
                    stores,
                    had_error,
                    root_header,
                    &while_op.body_block.block,
                    cur_header,
                    checked_items,
                    check_queue,
                );
            }
            OpCode::Complex(NameResolvedOp::Const { id }) => {
                // False means that the value was already in the set.
                #[allow(clippy::bool_comparison)]
                if checked_items.insert(*id) == false {
                    continue;
                }

                if *id == root_header.id {
                    *had_error = true;
                    diagnostics::emit_error(
                        stores,
                        cur_header.name.location,
                        format!("cyclic {kind_str} detected"),
                        [
                            Label::new(root_header.name.location)
                                .with_color(Color::Red)
                                .with_message(format!("in this {kind_str}")),
                            Label::new(op.token.location)
                                .with_color(Color::Cyan)
                                .with_message("cyclic reference"),
                        ],
                        None,
                    );
                } else {
                    check_queue.push(*id);
                }
            }
            _ => (),
        }
    }
}
