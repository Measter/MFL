use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    error_signal::ErrorSignal,
    ir::{If, While},
    pass_manager::{
        static_analysis::{
            can_promote_int_bidirectional, can_promote_int_unidirectional,
            failed_compare_stack_types, promote_int_type_bidirectional, Analyzer, ValueId,
        },
        PassContext,
    },
    stores::{
        ops::OpId,
        source::SourceLocation,
        types::{BuiltinTypes, TypeId, TypeKind},
    },
    Stores,
};

pub(crate) fn epilogue_return(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    item_id: ItemId,
) {
    let item_urir_sig = ctx.urir().get_item_signature(item_id);
    let item_trir_sig = ctx.trir().get_item_signature(item_id);
    let op_data = analyzer.get_op_io(op_id);

    for (&expected_type_id, &actual_value_id) in item_trir_sig.exit.iter().zip(&op_data.inputs) {
        let Some([actual_type_id]) = analyzer.value_types([actual_value_id]) else {
            continue;
        };

        if actual_type_id != expected_type_id {
            let actual_type_info = stores.types.get_type_info(actual_type_id);
            let expected_type_info = stores.types.get_type_info(expected_type_id);

            if !matches!((actual_type_info.kind, expected_type_info.kind),
                (TypeKind::Integer(actual), TypeKind::Integer(expected))
                if can_promote_int_unidirectional(actual, expected))
            {
                failed_compare_stack_types(
                    stores,
                    analyzer,
                    &op_data.inputs,
                    &item_trir_sig.exit,
                    item_urir_sig.exit.location,
                    stores.ops.get_token(op_id).location,
                    "item return stack mismatch",
                );
                had_error.set();
                break;
            }
        }
    }
}

pub(crate) fn prologue(ctx: &mut Context, analyzer: &mut Analyzer, op_id: OpId, item_id: ItemId) {
    let op_data = analyzer.get_op_io(op_id);
    let sigs = ctx.trir().get_item_signature(item_id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(&sigs.entry) {
        analyzer.set_value_type(output_id, output_type);
    }
}

pub(crate) fn syscall(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op_id: OpId,
) {
    let op_data = analyzer.get_op_io(op_id);

    for (idx, &input_value_id) in op_data.inputs.iter().enumerate() {
        let Some([input_type_id]) = analyzer.value_types([input_value_id]) else {
            continue;
        };

        let input_type_info = stores.types.get_type_info(input_type_id);
        if matches!(
            input_type_info.kind,
            TypeKind::Integer(_) | TypeKind::Pointer(_) | TypeKind::Bool
        ) {
            continue;
        }

        let type_name = stores.strings.resolve(input_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(input_value_id, idx.to_u64(), type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        let op_loc = stores.ops.get_token(op_id).location;
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(stores, op_loc, "invalid syscall parameter", labels, None);
        had_error.set();
    }

    // The output is always an int
    analyzer.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(BuiltinTypes::U64).id,
    );
}

pub(crate) fn call_function_const(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    callee_id: ItemId,
) {
    if pass_ctx
        .ensure_type_resolved_signature(ctx, stores, callee_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let op_data = analyzer.get_op_io(op_id);
    let callee_sig_urir = ctx.urir().get_item_signature(callee_id);
    let callee_sig_trir = ctx.trir().get_item_signature(callee_id);

    for (&actual_value_id, &expected_type_id) in op_data.inputs.iter().zip(&callee_sig_trir.entry) {
        let Some([actual_type_id]) = analyzer.value_types([actual_value_id]) else {
            continue;
        };

        if actual_type_id != expected_type_id {
            let actual_type_info = stores.types.get_type_info(actual_type_id);
            let expected_type_info = stores.types.get_type_info(expected_type_id);

            if !matches!((actual_type_info.kind, expected_type_info.kind),
                (
                    TypeKind::Integer(actual),
                    TypeKind::Integer(expected)
                ) if can_promote_int_unidirectional(actual, expected))
            {
                failed_compare_stack_types(
                    stores,
                    analyzer,
                    &op_data.inputs,
                    &callee_sig_trir.entry,
                    callee_sig_urir.entry.location,
                    stores.ops.get_token(op_id).location,
                    "procedure call signature mismatch",
                );
                had_error.set();
                // Break because the above call lists all inputs/args.
                break;
            }
        }
    }

    let ouput_ids = op_data.outputs.clone();
    for (&output_type_id, output_value_id) in callee_sig_trir.exit.iter().zip(ouput_ids) {
        analyzer.set_value_type(output_value_id, output_type_id);
    }
}

pub(crate) fn memory(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    memory_item_id: ItemId,
) {
    if pass_ctx
        .ensure_type_resolved_signature(ctx, stores, memory_item_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let op_data = analyzer.get_op_io(op_id);
    let output_value_id = op_data.outputs[0];

    let memory_type_id = ctx.trir().get_memory_type(memory_item_id);

    let ptr_type_id = stores
        .types
        .get_pointer(&mut stores.strings, memory_type_id);
    analyzer.set_value_type(output_value_id, ptr_type_id.id);
}

pub(crate) fn analyze_if(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    if_op: &If,
) {
    // The stack check has already done the full check on each block, so we don't have to repeat it here.

    // All conditions are stored in the op inputs.
    let op_data = analyzer.get_op_io(op_id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type_id]) = analyzer.value_types([condition_value_id]) {
        condition_type_check(
            condition_type_id,
            stores,
            analyzer,
            condition_value_id,
            if_op.tokens.do_token,
            had_error,
        );
    }

    let Some(merges) = analyzer.get_if_merges(op_id).cloned() else {
        panic!("ICE: Missing merges in If block")
    };

    for merge_pair in merges {
        let [then_value_info] = analyzer.values([merge_pair.then_value]);
        let Some([then_type_id, else_type_id]) =
            analyzer.value_types([merge_pair.then_value, merge_pair.else_value])
        else {
            continue;
        };

        let then_type_info = stores.types.get_type_info(then_type_id);
        let else_type_info = stores.types.get_type_info(else_type_id);

        let final_type_id = match (then_type_info.kind, else_type_info.kind) {
            (TypeKind::Integer(then_int), TypeKind::Integer(else_int))
                if can_promote_int_bidirectional(then_int, else_int) =>
            {
                let kind = promote_int_type_bidirectional(then_int, else_int).unwrap();
                stores.types.get_builtin(kind.into()).id
            }
            _ if then_type_id != else_type_id => {
                let then_type_name = stores.strings.resolve(then_type_info.name);
                let else_type_name = stores.strings.resolve(else_type_info.name);

                let labels = diagnostics::build_creator_label_chain(
                    analyzer,
                    [
                        (merge_pair.then_value, 0, then_type_name),
                        (merge_pair.else_value, 1, else_type_name),
                    ],
                    Color::Yellow,
                    Color::Cyan,
                );

                diagnostics::emit_error(
                    stores,
                    then_value_info.source_location,
                    "conditional body cannot change types on the stack",
                    labels,
                    None,
                );

                had_error.set();
                then_type_id
            }
            _ => then_type_id,
        };

        analyzer.set_value_type(merge_pair.output_value, final_type_id);
    }
}

pub(crate) fn analyze_while(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    while_op: &While,
) {
    // The stack check has already done the full check on each block, so we don't have to repeat it here.

    let op_data = analyzer.get_op_io(op_id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type_id]) = analyzer.value_types([condition_value_id]) {
        condition_type_check(
            condition_type_id,
            stores,
            analyzer,
            condition_value_id,
            while_op.tokens.do_token,
            had_error,
        );
    }

    let Some(merge_info) = analyzer.get_while_merges(op_id).cloned() else {
        panic!("ICE: While block should have merge info");
    };

    // Unlike the If-block handling above, this is not setting the type, only checking that
    // they are compatible.
    for merge_pair in merge_info.condition.iter().chain(&merge_info.body) {
        let [condition_value_info] = analyzer.values([merge_pair.condition_value]);
        let Some([pre_type_id, condition_type_id]) =
            analyzer.value_types([merge_pair.pre_value, merge_pair.condition_value])
        else {
            continue;
        };

        let pre_type_info = stores.types.get_type_info(pre_type_id);
        let condition_type_info = stores.types.get_type_info(condition_type_id);

        if pre_type_id != condition_type_id
            && !matches!(
                (pre_type_info.kind, condition_type_info.kind),
                (TypeKind::Integer(pre_int), TypeKind::Integer(condition_int))
                if can_promote_int_unidirectional(condition_int, pre_int)
            )
        {
            let pre_type_name = stores.strings.resolve(pre_type_info.name);
            let condition_type_name = stores.strings.resolve(condition_type_info.name);

            let labels = diagnostics::build_creator_label_chain(
                analyzer,
                [
                    (merge_pair.pre_value, 0, pre_type_name),
                    (merge_pair.condition_value, 1, condition_type_name),
                ],
                Color::Yellow,
                Color::Cyan,
            );

            diagnostics::emit_error(
                stores,
                condition_value_info.source_location,
                "while loop condition or body may not change types on the stack",
                labels,
                None,
            );

            had_error.set();
        }
    }
}

fn condition_type_check(
    condition_type_id: TypeId,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    condition_value_id: ValueId,
    error_location: SourceLocation,
    had_error: &mut ErrorSignal,
) {
    if condition_type_id != stores.types.get_builtin(BuiltinTypes::Bool).id {
        let condition_type_info = stores.types.get_type_info(condition_type_id);
        let condition_type_name = stores.strings.resolve(condition_type_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(condition_value_id, 0, condition_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(error_location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            error_location,
            "condition must evaluate to a boolean",
            labels,
            None,
        );

        had_error.set();
    }
}
