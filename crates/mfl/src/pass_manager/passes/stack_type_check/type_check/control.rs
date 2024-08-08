use std::ops::ControlFlow;

use ariadne::{Color, Label};
use intcast::IntCast;
use stores::{items::ItemId, source::SourceLocation};

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{If, OpCode, TypeResolvedOp, While},
    pass_manager::{
        static_analysis::{
            can_promote_float_unidirectional, can_promote_int_bidirectional,
            can_promote_int_unidirectional, failed_compare_stack_types,
            promote_int_type_bidirectional,
        },
        PassManager,
    },
    stores::{
        item::ItemKind,
        ops::OpId,
        types::{BuiltinTypes, TypeId, TypeKind},
        values::ValueId,
    },
    Stores,
};

pub(crate) fn epilogue_return(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    item_id: ItemId,
) {
    let item_urir_sig = stores.sigs.urir.get_item_signature(item_id);
    let item_trir_sig = stores.sigs.trir.get_item_signature(item_id);
    let op_data = stores.ops.get_op_io(op_id);

    for (&expected_type_id, &actual_value_id) in item_trir_sig.exit.iter().zip(&op_data.inputs) {
        let Some([actual_type_id]) = stores.values.value_types([actual_value_id]) else {
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

pub(crate) fn prologue(stores: &mut Stores, op_id: OpId, item_id: ItemId) {
    let op_data = stores.ops.get_op_io(op_id);
    let sigs = stores.sigs.trir.get_item_signature(item_id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(&sigs.entry) {
        stores.values.set_value_type(output_id, output_type);
    }
}

pub(crate) fn syscall(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);

    for (idx, &input_value_id) in op_data.inputs.iter().enumerate() {
        let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
            continue;
        };

        let input_type_info = stores.types.get_type_info(input_type_id);
        if matches!(
            input_type_info.kind,
            TypeKind::Integer(_)
                | TypeKind::MultiPointer(_)
                | TypeKind::SinglePointer(_)
                | TypeKind::Bool
        ) {
            continue;
        }

        let type_name = stores.strings.resolve(input_type_info.friendly_name);
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
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
    stores.values.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(BuiltinTypes::U64).id,
    );
}

pub(crate) fn call_function_const(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    callee_id: ItemId,
) {
    let callee_header = stores.items.get_item_header(callee_id);

    let callee_id = if callee_header.kind == ItemKind::GenericFunction {
        if pass_manager
            .ensure_partially_resolve_types(stores, callee_id)
            .is_err()
        {
            had_error.set();
            return;
        }

        let ControlFlow::Continue(id) =
            call_generic_function_infer_params(stores, pass_manager, had_error, callee_id, op_id)
        else {
            return;
        };

        // Need to update the op to point at the correct new function ID.
        stores.ops.overwrite_type_resolved(
            op_id,
            OpCode::Complex(TypeResolvedOp::CallFunction {
                id,
                generic_params: Vec::new(),
            }),
        );
        id
    } else {
        callee_id
    };

    if pass_manager
        .ensure_type_resolved_signature(stores, callee_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let op_data = stores.ops.get_op_io(op_id);
    let callee_sig_urir = stores.sigs.urir.get_item_signature(callee_id);
    let callee_sig_trir = stores.sigs.trir.get_item_signature(callee_id);

    for (&actual_value_id, &expected_type_id) in op_data.inputs.iter().zip(&callee_sig_trir.entry) {
        let Some([actual_type_id]) = stores.values.value_types([actual_value_id]) else {
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
                && !matches!(
                    (actual_type_info.kind, expected_type_info.kind),
                    (TypeKind::Float(actual), TypeKind::Float(expected))
                    if can_promote_float_unidirectional(actual, expected)
                )
            {
                failed_compare_stack_types(
                    stores,
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
        stores
            .values
            .set_value_type(output_value_id, output_type_id);
    }
}

fn call_generic_function_infer_params(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    callee_id: ItemId,
    op_id: OpId,
) -> ControlFlow<(), ItemId> {
    let generic_sig = stores.sigs.trir.get_partial_item_signature(callee_id);
    let op_data = stores.ops.get_op_io(op_id);
    let inputs = &op_data.inputs;
    let generic_params = stores.items.get_function_template_paramaters(callee_id);

    let mut param_types = Vec::new();

    // Essentially, iterate over each parameter, then search the signature looking for
    // a type we can pattern match against to infer the generic type parameter.
    // If we find one, break and search for the next parameter.
    let mut local_had_error = ErrorSignal::new();

    for param in generic_params {
        let mut found_param = false;
        let sig_iter = generic_sig.entry.iter().chain(&generic_sig.exit);
        for (sig_type, &input_value_id) in sig_iter.zip(inputs) {
            let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
                continue;
            };
            let input_type_info = stores.types.get_type_info(input_type_id);

            let Some(inferred_type_id) =
                sig_type.match_generic_type(stores, param.inner, input_type_info)
            else {
                // Not an inferreable pattern.
                continue;
            };

            param_types.push(inferred_type_id);
            found_param = true;
            break;
        }

        if !found_param {
            let op_loc = stores.ops.get_token(op_id).location;
            diagnostics::emit_error(
                stores,
                op_loc,
                "unable to infer type parameter",
                [
                    Label::new(op_loc).with_color(Color::Red),
                    Label::new(param.location).with_color(Color::Cyan),
                ],
                None,
            );

            local_had_error.set();
        }
    }

    if local_had_error.into_bool() {
        had_error.set();
        return ControlFlow::Break(());
    }

    let Ok(new_id) =
        stores.get_generic_function_instance(pass_manager, had_error, callee_id, &param_types)
    else {
        had_error.set();
        return ControlFlow::Break(());
    };

    ControlFlow::Continue(new_id)
}

pub(crate) fn variable(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    variable_item_id: ItemId,
) {
    if pass_manager
        .ensure_type_resolved_signature(stores, variable_item_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let op_data = stores.ops.get_op_io(op_id);
    let output_value_id = op_data.outputs[0];

    let variable_type_id = stores.sigs.trir.get_variable_type(variable_item_id);

    let ptr_type_id = stores
        .types
        .get_single_pointer(stores.strings, variable_type_id);
    stores
        .values
        .set_value_type(output_value_id, ptr_type_id.id);
}

pub(crate) fn analyze_if(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    if_op: &If,
) {
    // The stack check has already done the full check on each block, so we don't have to repeat it here.

    // All conditions are stored in the op inputs.
    let op_data = stores.ops.get_op_io(op_id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type_id]) = stores.values.value_types([condition_value_id]) {
        condition_type_check(
            condition_type_id,
            stores,
            condition_value_id,
            if_op.tokens.do_token,
            had_error,
        );
    }

    let Some(merges) = stores.values.get_merge_values(op_id).cloned() else {
        panic!("ICE: Missing merges in If block")
    };

    for merge_pair in merges {
        let [then_value_info] = stores.values.values([merge_pair.a_in]);
        let Some([then_type_id, else_type_id]) = stores
            .values
            .value_types([merge_pair.a_in, merge_pair.b_in])
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
                let then_type_name = stores.strings.resolve(then_type_info.friendly_name);
                let else_type_name = stores.strings.resolve(else_type_info.friendly_name);

                let labels = diagnostics::build_creator_label_chain(
                    stores,
                    [
                        (merge_pair.a_in, 0, then_type_name),
                        (merge_pair.b_in, 1, else_type_name),
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

        stores.values.set_value_type(merge_pair.out, final_type_id);
    }
}

pub(crate) fn analyze_while(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    while_op: &While,
) {
    // The stack check has already done the full check on each block, so we don't have to repeat it here.

    let op_data = stores.ops.get_op_io(op_id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type_id]) = stores.values.value_types([condition_value_id]) {
        condition_type_check(
            condition_type_id,
            stores,
            condition_value_id,
            while_op.tokens.do_token,
            had_error,
        );
    }

    let Some(merge_values) = stores.values.get_merge_values(op_id).cloned() else {
        panic!("ICE: While block should have merge info");
    };

    // Unlike the If-block handling above, this is not setting the type, only checking that
    // they are compatible.
    for merge_pair in merge_values {
        let [b_in_value_info] = stores.values.values([merge_pair.b_in]);
        let Some([a_in_type_id, b_in_type_id]) = stores
            .values
            .value_types([merge_pair.a_in, merge_pair.b_in])
        else {
            continue;
        };

        let a_in_type_info = stores.types.get_type_info(a_in_type_id);
        let b_in_type_info = stores.types.get_type_info(b_in_type_id);

        if a_in_type_id != b_in_type_id
            && !matches!(
                (a_in_type_info.kind, b_in_type_info.kind),
                (TypeKind::Integer(a_in_int), TypeKind::Integer(b_in_int))
                if can_promote_int_unidirectional(b_in_int, a_in_int)
            )
        {
            let a_in_type_name = stores.strings.resolve(a_in_type_info.friendly_name);
            let b_in_type_name = stores.strings.resolve(b_in_type_info.friendly_name);

            let labels = diagnostics::build_creator_label_chain(
                stores,
                [
                    (merge_pair.a_in, 0, a_in_type_name),
                    (merge_pair.b_in, 1, b_in_type_name),
                ],
                Color::Yellow,
                Color::Cyan,
            );

            diagnostics::emit_error(
                stores,
                b_in_value_info.source_location,
                "while loop body may not change types on the stack",
                labels,
                None,
            );

            had_error.set();
        }

        // Our output type is the same as a_in because the body can't change the existing type.
        stores.values.set_value_type(merge_pair.out, a_in_type_id);
    }
}

fn condition_type_check(
    condition_type_id: TypeId,
    stores: &mut Stores,
    condition_value_id: ValueId,
    error_location: SourceLocation,
    had_error: &mut ErrorSignal,
) {
    if condition_type_id != stores.types.get_builtin(BuiltinTypes::Bool).id {
        let condition_type_info = stores.types.get_type_info(condition_type_id);
        let condition_type_name = stores.strings.resolve(condition_type_info.friendly_name);

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
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
