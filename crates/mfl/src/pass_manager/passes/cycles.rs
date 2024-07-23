use ariadne::{Color, Label};
use hashbrown::HashSet;

use crate::{
    context::{Context, ItemHeader, ItemId, ItemKind},
    diagnostics,
    error_signal::ErrorSignal,
    ir::{NameResolvedOp, Op, OpCode},
    pass_manager::PassContext,
    Stores,
};

pub fn check_invalid_cycles(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let root_header = ctx.get_item_header(cur_id);

    match root_header.kind {
        ItemKind::Assert | ItemKind::Const => {
            check_invalid_cycles_const_assert(ctx, stores, pass_ctx, had_error, cur_id)
        }
        ItemKind::StructDef => {
            check_invalid_cycles_structs(ctx, stores, pass_ctx, had_error, cur_id)
        }
        // Nothing to do here.
        ItemKind::Memory | ItemKind::Function | ItemKind::GenericFunction | ItemKind::Module => {}
    }
}

fn check_invalid_cycles_structs(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    // todo!()
}

fn check_invalid_cycles_const_assert(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    root_id: ItemId,
) {
    let root_header = ctx.get_item_header(root_id);
    let mut check_queue = vec![root_id];
    let mut checked_items = HashSet::new();

    while let Some(item) = check_queue.pop() {
        let header = ctx.get_item_header(root_id);
        if item != root_id
            && pass_ctx
                .ensure_ident_resolved_body(ctx, stores, item)
                .is_err()
        {
            had_error.set();
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
    had_error: &mut ErrorSignal,
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
                    had_error.set();
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
