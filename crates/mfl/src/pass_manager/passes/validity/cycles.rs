use hashbrown::HashSet;
use stores::{items::ItemId, source::SourceLocation};

use crate::{
    error_signal::ErrorSignal,
    ir::{Basic, Control, NameResolvedOp, NameResolvedType, OpCode},
    pass_manager::PassManager,
    stores::{
        block::BlockId,
        diagnostics::Diagnostic,
        item::{ItemHeader, ItemKind},
    },
    Stores,
};

pub fn check_invalid_cycles(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let root_header = stores.items.get_item_header(cur_id);

    match root_header.kind {
        ItemKind::Assert | ItemKind::Const => {
            check_invalid_cycles_const_assert(stores, pass_manager, had_error, cur_id)
        }
        ItemKind::StructDef => {
            check_invalid_cycles_structs(stores, pass_manager, had_error, cur_id)
        }
        // Nothing to do here.
        ItemKind::Variable
        | ItemKind::Function
        | ItemKind::FunctionDecl
        | ItemKind::GenericFunction
        | ItemKind::Enum
        | ItemKind::Module
        | ItemKind::Primitive(_) => {}
    }
}

fn check_invalid_cycles_structs(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    root_id: ItemId,
) {
    let root_struct_def = stores.sigs.nrir.get_struct(root_id);
    let name_location = root_struct_def.name.location;
    let mut check_queue = vec![root_id];
    let mut checked_items = HashSet::new();

    while let Some(item) = check_queue.pop() {
        if item != root_id
            && pass_manager
                .ensure_ident_resolved_signature(stores, item)
                .is_err()
        {
            had_error.set();
        }

        let struct_def = stores.sigs.nrir.get_struct(item).clone();
        for field in &struct_def.fields {
            check_invalid_cyclic_refs_in_field_kind(
                stores,
                had_error,
                root_id,
                name_location,
                field.name.location,
                &field.kind.inner,
                &mut check_queue,
                &mut checked_items,
            );
        }
    }
}

fn check_invalid_cyclic_refs_in_field_kind(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    root_id: ItemId,
    root_name_location: SourceLocation,
    field_name_location: SourceLocation,
    field_kind: &NameResolvedType,
    check_queue: &mut Vec<ItemId>,
    checked_items: &mut HashSet<ItemId>,
) {
    match field_kind {
        NameResolvedType::SimpleCustom { id, .. }
        | NameResolvedType::GenericInstance { id, .. } => {
            let referred_kind = stores.items.get_item_header(*id).kind;
            if referred_kind != ItemKind::StructDef {
                return;
            }

            #[allow(clippy::bool_comparison)]
            if checked_items.insert(*id) == false {
                return;
            }
            // False means that the value was already in the set.

            if *id == root_id {
                had_error.set();
                Diagnostic::error(field_name_location, "recursive struct")
                    .primary_label_message("in this field")
                    .with_help_label(root_name_location, "in this struct")
                    .attached(stores.diags, root_id);
            } else {
                check_queue.push(*id);
            }
        }
        NameResolvedType::Array(id, _) => {
            let mut inner_array_id = id;

            while let NameResolvedType::Array(inner, _) = &**inner_array_id {
                inner_array_id = inner;
            }

            // We've now reached the innermost type of the array.
            check_invalid_cyclic_refs_in_field_kind(
                stores,
                had_error,
                root_id,
                root_name_location,
                field_name_location,
                inner_array_id,
                check_queue,
                checked_items,
            );
        }
        // All these are indirect, so fine.
        NameResolvedType::MultiPointer(_)
        | NameResolvedType::SinglePointer(_)
        | NameResolvedType::FunctionPointer { .. }
        | NameResolvedType::SimpleGenericParam(_) => {}
    }
}

fn check_invalid_cycles_const_assert(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    root_id: ItemId,
) {
    let root_header = stores.items.get_item_header(root_id);
    let mut check_queue = vec![root_id];
    let mut checked_items = HashSet::new();

    while let Some(item) = check_queue.pop() {
        let header = stores.items.get_item_header(root_id);
        if item != root_id
            && pass_manager
                .ensure_ident_resolved_body(stores, item)
                .is_err()
        {
            had_error.set();
        }

        let block_id = stores.items.get_item_body(item);
        check_invalid_cyclic_refs_in_block(
            stores,
            had_error,
            root_header,
            block_id,
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
    block_id: BlockId,
    cur_header: ItemHeader,
    checked_items: &mut HashSet<ItemId>,
    check_queue: &mut Vec<ItemId>,
) {
    let kind_str = match root_header.kind {
        ItemKind::Assert => "assert",
        ItemKind::Const => "const",
        _ => unreachable!(),
    };

    let block = stores.blocks.get_block(block_id).clone();
    for op_id in block.ops {
        let op_code = stores.ops.get_name_resolved(op_id).clone();
        match op_code {
            // OpCode::Basic(Basic::Control(Control::If(if_op))) => {
            //     check_invalid_cyclic_refs_in_block(
            //         stores,
            //         had_error,
            //         root_header,
            //         if_op.condition,
            //         cur_header,
            //         checked_items,
            //         check_queue,
            //     );
            //     check_invalid_cyclic_refs_in_block(
            //         stores,
            //         had_error,
            //         root_header,
            //         if_op.then_block,
            //         cur_header,
            //         checked_items,
            //         check_queue,
            //     );
            //     check_invalid_cyclic_refs_in_block(
            //         stores,
            //         had_error,
            //         root_header,
            //         if_op.else_block,
            //         cur_header,
            //         checked_items,
            //         check_queue,
            //     );
            // }
            OpCode::Basic(Basic::Control(Control::Cond(_))) => {
                todo!();
            }
            OpCode::Basic(Basic::Control(Control::While(while_op))) => {
                check_invalid_cyclic_refs_in_block(
                    stores,
                    had_error,
                    root_header,
                    while_op.condition,
                    cur_header,
                    checked_items,
                    check_queue,
                );
                check_invalid_cyclic_refs_in_block(
                    stores,
                    had_error,
                    root_header,
                    while_op.body_block,
                    cur_header,
                    checked_items,
                    check_queue,
                );
            }
            OpCode::Complex(NameResolvedOp::Const { id }) => {
                // False means that the value was already in the set.
                #[allow(clippy::bool_comparison)]
                if checked_items.insert(id) == false {
                    continue;
                }

                if id == root_header.id {
                    had_error.set();
                    let op_loc = stores.ops.get_token(op_id).location;
                    Diagnostic::error(
                        cur_header.name.location,
                        format!("cyclic {kind_str} detected"),
                    )
                    .primary_label_message(format!("in this {kind_str}"))
                    .with_help_label(op_loc, "cyclic reference")
                    .attached(stores.diags, root_header.id);
                } else {
                    check_queue.push(id);
                }
            }
            _ => (),
        }
    }
}
