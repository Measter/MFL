use std::ops::ControlFlow;

use intcast::IntCast;
use stores::{items::ItemId, source::SourceLocation};

use crate::{
    error_signal::ErrorSignal,
    ir::{Cond, OpCode, TypeResolvedOp, While},
    pass_manager::{
        static_analysis::{
            can_promote_float_unidirectional, can_promote_int_bidirectional,
            can_promote_int_unidirectional, failed_compare_stack_types,
            promote_int_type_bidirectional,
        },
        PassManager,
    },
    stores::{
        diagnostics::Diagnostic,
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
    let item_trir_sig = stores.sigs.trir.get_item_signature(item_id).clone();
    let op_data = stores.ops.get_op_io(op_id).clone();

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
                    item_id,
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

pub(crate) fn syscall(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
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
        let op_loc = stores.ops.get_token(op_id).location;

        Diagnostic::error(op_loc, "invalid syscall parameter")
            .with_label_chain(input_value_id, idx.to_u64(), type_name)
            .attached(stores.diags, item_id);

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
    item_id: ItemId,
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

        let ControlFlow::Continue(id) = call_generic_function_infer_params(
            stores,
            pass_manager,
            had_error,
            item_id,
            callee_id,
            op_id,
        ) else {
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

    let op_data = stores.ops.get_op_io(op_id).clone();
    let callee_sig_urir = stores.sigs.urir.get_item_signature(callee_id);
    let callee_sig_trir = stores.sigs.trir.get_item_signature(callee_id).clone();

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
                    item_id,
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

pub(crate) fn method_call(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let callee_id = stores.ops.get_method_callee(op_id);
    call_function_const(stores, pass_manager, had_error, item_id, op_id, callee_id);
}

fn call_generic_function_infer_params(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    callee_id: ItemId,
    op_id: OpId,
) -> ControlFlow<(), ItemId> {
    let generic_sig = stores.sigs.trir.get_partial_item_signature(callee_id);
    let op_data = stores.ops.get_op_io(op_id);
    let inputs = &op_data.inputs;
    let generic_params = stores.items.get_function_template_paramaters(callee_id);

    let mut inferred_params = generic_params
        .iter()
        .map(|i| (i.inner, Vec::new()))
        .collect();

    // We first iterate over all the input parameters and values, and try to infer
    // all uses of type paramaters. We may end up collecting multiple instances of
    // the same type ID for each parameter, which we handle later.
    for (sig_type, &input_value_id) in generic_sig.entry.iter().zip(inputs) {
        let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
            continue;
        };
        let input_type_info = stores.types.get_type_info(input_type_id);

        sig_type.match_generic_type_new(
            stores,
            &mut inferred_params,
            input_type_info,
            input_value_id,
        );
    }

    // Now we check that we managed to infer one, and only one, type ID for each parameter.
    let mut param_types = Vec::new();
    let mut local_had_error = ErrorSignal::new();
    for param in generic_params {
        let inferred_types: &mut Vec<_> = inferred_params.get_mut(&param.inner).unwrap();
        inferred_types.sort_by_key(|f| f.1);
        inferred_types.dedup_by_key(|f| f.1);

        match inferred_types.len() {
            1 => param_types.push(inferred_types[0].1),
            0 => {
                let op_loc = stores.ops.get_token(op_id).location;
                Diagnostic::error(op_loc, "unable to infer type parameter")
                    .primary_label_message("this call")
                    .with_help_label(param.location, "this parameter")
                    .attached(stores.diags, item_id);

                local_had_error.set();
            }
            _ => {
                let op_loc = stores.ops.get_token(op_id).location;
                let param_name = stores.strings.resolve(param.inner);
                let mut diag = Diagnostic::error(
                    op_loc,
                    format!(
                        "unable to infer type parameter `{param_name}` due to conflicting inputs",
                    ),
                )
                .primary_label_message("this call")
                .with_secondary_label(param.location, "this parameter");

                for (idx, &(input_value_id, inferred_type_id)) in inferred_types.iter().enumerate()
                {
                    let inferred_type_info = stores.types.get_type_info(inferred_type_id);
                    let inferred_type_name =
                        stores.strings.resolve(inferred_type_info.friendly_name);

                    let [input_value_location] = stores.values.values_headers([input_value_id]);
                    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
                        continue;
                    };
                    let input_type_info = stores.types.get_type_info(input_type_id);
                    let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

                    diag.add_label_chain(input_value_id, idx.to_u64(), input_type_name);
                    diag.add_help_label(
                        input_value_location.source_location,
                        format!("inferred `{inferred_type_name}` from this value"),
                    );
                }

                diag.attached(stores.diags, item_id);
                local_had_error.set();

                // Just so we can continue, just assume the first one.
                param_types.push(inferred_types[0].1)
            }
        }
    }

    if local_had_error.into_err() {
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

pub(crate) fn analyze_cond(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    cond_op: &Cond,
) {
    // The stack check has already done the full check on each block, so we don't have to repeat it here.

    // All conditions are stored in the op inputs.
    let op_data = stores.ops.get_op_io(op_id);
    for (arm, condition_value_id) in cond_op.arms.iter().zip(op_data.inputs.clone()) {
        if let Some([condition_type_id]) = stores.values.value_types([condition_value_id]) {
            condition_type_check(
                condition_type_id,
                stores,
                item_id,
                condition_value_id,
                arm.open,
                had_error,
            );
        }
    }

    let Some(merges) = stores.values.get_merge_values(op_id).cloned() else {
        panic!("ICE: Missing merges in Cond block")
    };

    for merge in merges {
        // If we have an implicit-else, and one of the merges is from the implicit-else
        // then that value came from before the cond, and this is what we point to for errors,
        // and is also our start point for our expected type.
        // Otherwise our expected type comes from the first arm.
        let (expected_value_id, other_inputs) =
            if cond_op.implicit_else && merge.block_input(cond_op.else_block).is_some() {
                // The else-block is always last
                (
                    merge.block_input(cond_op.else_block).unwrap(),
                    &merge.inputs[..merge.inputs.len() - 1],
                )
            } else {
                (merge.inputs[0].1, &merge.inputs[1..])
            };

        let Some([mut expected_type_id]) = stores.values.value_types([expected_value_id]) else {
            // We don't know our expected output type.
            // We'll just bail for now. Maybe see if there's a better way?
            continue;
        };

        let mut expected_type_info = stores.types.get_type_info(expected_type_id);

        for &(_, other_input_value_id) in other_inputs {
            let Some([input_type_id]) = stores.values.value_types([other_input_value_id]) else {
                continue;
            };

            let input_type_info = stores.types.get_type_info(input_type_id);
            match (expected_type_info.kind, input_type_info.kind) {
                (TypeKind::Integer(expected_int), TypeKind::Integer(other_int))
                    if can_promote_int_bidirectional(expected_int, other_int) =>
                {
                    let kind = promote_int_type_bidirectional(expected_int, other_int).unwrap();
                    expected_type_id = stores.types.get_builtin(kind.into()).id;
                    expected_type_info = stores.types.get_type_info(expected_type_id);
                }
                (TypeKind::Float(expected_flt), TypeKind::Float(other_flt)) => {
                    // Take the widest type
                    if other_flt > expected_flt {
                        expected_type_id = input_type_id;
                        expected_type_info = input_type_info;
                    }
                }
                _ if expected_type_id != input_type_id => {
                    let expected_type_name =
                        stores.strings.resolve(expected_type_info.friendly_name);
                    let other_input_type_name =
                        stores.strings.resolve(input_type_info.friendly_name);
                    let [other_input_value_info] =
                        stores.values.values_headers([other_input_value_id]);

                    Diagnostic::error(
                        other_input_value_info.source_location,
                        "conditional body cannot change types on the stack",
                    )
                    .with_label_chain(expected_value_id, 0, expected_type_name)
                    .with_label_chain(other_input_value_id, 0, other_input_type_name)
                    .attached(stores.diags, item_id);

                    had_error.set();
                }
                _ => (),
            }
        }

        stores.values.set_value_type(merge.output, expected_type_id);
    }
}

pub(crate) fn analyze_while(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    while_op: &While,
) {
    // The stack check has already done the full check on each block, so we don't have to repeat it here.

    let Some(merge_values) = stores.values.get_merge_values(op_id).cloned() else {
        panic!("ICE: While block should have merge info");
    };

    for merge_pair in merge_values {
        // While loop merges only have two inputs, so we can just make that assumption.
        let [b_in_value_info] = stores.values.values_headers([merge_pair.inputs[1].1]);
        let Some([a_in_type_id, b_in_type_id]) = stores
            .values
            .value_types([merge_pair.inputs[0].1, merge_pair.inputs[1].1])
        else {
            continue;
        };

        let a_in_type_info = stores.types.get_type_info(a_in_type_id);
        let b_in_type_info = stores.types.get_type_info(b_in_type_id);

        if a_in_type_id != b_in_type_id
            && (!matches!(
                (a_in_type_info.kind, b_in_type_info.kind),
                (TypeKind::Integer(a_in_int), TypeKind::Integer(b_in_int))
                if can_promote_int_unidirectional(b_in_int, a_in_int)
            ) || !matches!(
                (a_in_type_info.kind, b_in_type_info.kind),
                (TypeKind::Float(a_in_flt), TypeKind::Float(b_in_flt))
                if a_in_flt >= b_in_flt
            ))
        {
            let a_in_type_name = stores.strings.resolve(a_in_type_info.friendly_name);
            let b_in_type_name = stores.strings.resolve(b_in_type_info.friendly_name);

            Diagnostic::error(
                b_in_value_info.source_location,
                "while loop body may not change types on the stack",
            )
            .with_label_chain(merge_pair.inputs[0].1, 0, a_in_type_name)
            .with_label_chain(merge_pair.inputs[1].1, 1, b_in_type_name)
            .attached(stores.diags, item_id);

            had_error.set();
        }

        // Our output type is the same as a_in because the body can't change the existing type.
        stores
            .values
            .set_value_type(merge_pair.output, a_in_type_id);
    }

    // Check after the merge values have been done so that if the condition is a merge value it will have a type.
    let op_data = stores.ops.get_op_io(op_id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type_id]) = stores.values.value_types([condition_value_id]) {
        condition_type_check(
            condition_type_id,
            stores,
            item_id,
            condition_value_id,
            while_op.tokens.do_token,
            had_error,
        );
    }
}

fn condition_type_check(
    condition_type_id: TypeId,
    stores: &mut Stores,
    item_id: ItemId,
    condition_value_id: ValueId,
    error_location: SourceLocation,
    had_error: &mut ErrorSignal,
) {
    if condition_type_id != stores.types.get_builtin(BuiltinTypes::Bool).id {
        let condition_type_info = stores.types.get_type_info(condition_type_id);
        let condition_type_name = stores.strings.resolve(condition_type_info.friendly_name);

        Diagnostic::error(error_location, "condition must evaluate to a boolean")
            .with_label_chain(condition_value_id, 0, condition_type_name)
            .attached(stores.diags, item_id);

        had_error.set();
    }
}
