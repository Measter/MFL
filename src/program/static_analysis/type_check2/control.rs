use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{failed_compare_stack_types, Analyzer, IntWidth, PorthTypeKind},
        ProcedureId, ProcedureKind, ProcedureSignatureResolved, Program,
    },
    source_file::SourceStorage,
};

pub(super) fn epilogue_return(
    program: &Program,
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    proc_id: ProcedureId,
) {
    let proc_sig = program.get_proc_signature_resolved(proc_id);
    let proc_sig_tokens = program.get_proc_signature_unresolved(proc_id);
    let op_data = analyzer.get_op_io(op.id);

    for (&expected, actual_id) in proc_sig.exit_stack().iter().zip(&op_data.inputs) {
        let actual_type = analyzer.value_types([*actual_id]);

        if actual_type != Some([expected]) {
            failed_compare_stack_types(
                analyzer,
                source_store,
                &op_data.inputs,
                proc_sig.exit_stack(),
                proc_sig_tokens.exit_stack_location(),
                op.token.location,
                "procedure return stack mismatch",
            );
            *had_error = true;
            break;
        }
    }
}

pub(super) fn prologue(analyzer: &mut Analyzer, op: &Op, proc_sig: &ProcedureSignatureResolved) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(proc_sig.entry_stack()) {
        analyzer.set_value_type(output_id, output_type);
    }
}

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    proc_id: ProcedureId,
) {
    let referenced_proc = program.get_proc_header(proc_id);
    let referenced_proc_sig = program.get_proc_signature_resolved(proc_id);
    let referenced_proc_sig_tokens = program.get_proc_signature_unresolved(proc_id);
    let op_data = analyzer.get_op_io(op.id);

    match referenced_proc.kind() {
        ProcedureKind::Memory => {
            let output_id = op_data.outputs[0];
            analyzer.set_value_type(output_id, PorthTypeKind::Ptr);
        }
        _ => {
            for (&expected, actual_id) in referenced_proc_sig
                .entry_stack()
                .iter()
                .zip(&op_data.inputs)
            {
                let actual_type = analyzer.value_types([*actual_id]);

                if actual_type != Some([expected]) {
                    failed_compare_stack_types(
                        analyzer,
                        source_store,
                        &op_data.inputs,
                        referenced_proc_sig.entry_stack(),
                        referenced_proc_sig_tokens.entry_stack_location(),
                        op.token.location,
                        "procedure call signature mismatch",
                    );
                    *had_error = true;
                    break;
                }
            }

            let output_ids = op_data.outputs.clone();

            for (&output_type, output_id) in referenced_proc_sig.exit_stack().iter().zip(output_ids)
            {
                analyzer.set_value_type(output_id, output_type);
            }
        }
    }
}

pub(super) fn syscall(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);

    // All syscall inputs are untyped.
    // The output is always an int.

    analyzer.set_value_type(op_data.outputs[0], PorthTypeKind::Int(IntWidth::I64));
}

pub(super) fn analyze_while(
    program: &Program,
    proc_id: ProcedureId,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    body: &ConditionalBlock,
) {
    let Some(merge_info) = analyzer.get_while_merges(op.id).map(Clone::clone) else {
        panic!("ICE: While block should have merge info");
    };

    // We don't need to worry about the order of evaluation here as they don't effect eachother.
    // Evaluate the condition.
    super::analyze_block(
        program,
        proc_id,
        &body.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    // Evaluate the body.
    super::analyze_block(
        program,
        proc_id,
        &body.block,
        analyzer,
        had_error,
        interner,
        source_store,
    );

    // We expect a boolean to be the result of evaluating the condition.
    let op_data = analyzer.get_op_io(op.id);
    let condition_inputs = *op_data.inputs.as_arr::<1>();
    let Some([condition_type]) = analyzer.value_types(condition_inputs) else { return };

    if condition_type != PorthTypeKind::Bool {
        *had_error = true;
        let [value] = analyzer.values(condition_inputs);

        diagnostics::emit_error(
            body.do_token.location,
            "condition must evaluate to a boolean",
            [
                Label::new(body.do_token.location)
                    .with_color(Color::Cyan)
                    .with_message("expected here"),
                Label::new(value.creator_token.location)
                    .with_color(Color::Red)
                    .with_message(condition_type.name_str())
                    .with_order(1),
            ],
            None,
            source_store,
        );
    }

    for merge_pair in merge_info.condition.iter().chain(&merge_info.body) {
        let [pre_value, condition_value] =
            analyzer.values([merge_pair.pre_value, merge_pair.condition_value]);
        let Some([pre_type, condition_type]) = analyzer.value_types([merge_pair.pre_value, merge_pair.condition_value,]) else { continue };

        if pre_type != condition_type {
            *had_error = true;
            diagnostics::emit_error(
                condition_value.creator_token.location,
                "while loop condition or body may not change types on the stack",
                [
                    Label::new(condition_value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(condition_type.name_str()),
                    Label::new(pre_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(pre_type.name_str())
                        .with_order(1),
                ],
                None,
                source_store,
            );
        }
    }
}

pub(super) fn analyze_if(
    program: &Program,
    proc_id: ProcedureId,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    conditional: &ConditionalBlock,
    else_block: &[Op],
) {
    // Evaluate all the blocks.
    // Thankfully the order is unimportant here.
    super::analyze_block(
        program,
        proc_id,
        &conditional.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    super::analyze_block(
        program,
        proc_id,
        &conditional.block,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    super::analyze_block(
        program,
        proc_id,
        else_block,
        analyzer,
        had_error,
        interner,
        source_store,
    );

    // All the conditions are stored in the op inputs.
    let op_data = analyzer.get_op_io(op.id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type]) = analyzer.value_types([condition_value_id]) {
        if condition_type != PorthTypeKind::Bool {
            *had_error = true;
            let [value] = analyzer.values([condition_value_id]);

            diagnostics::emit_error(
                conditional.do_token.location,
                "condition must evaluate to a boolean",
                [
                    Label::new(conditional.do_token.location)
                        .with_color(Color::Cyan)
                        .with_message("expected here"),
                    Label::new(value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(condition_type.name_str())
                        .with_order(1),
                ],
                None,
                source_store,
            );
        }
    }

    // Now to type check all the merging values to make sure they have the correct types.
    let Some(merges) = analyzer.get_if_merges(op.id).map(Clone::clone) else {
        panic!("ICE: Missing merges in If block");
    };

    for merge_pair in merges {
        let [then_value, else_value] =
            analyzer.values([merge_pair.then_value, merge_pair.else_value]);
        let Some([then_type, else_type]) = analyzer.value_types([merge_pair.then_value, merge_pair.else_value]) else { continue };

        if then_type != else_type {
            *had_error = true;
            diagnostics::emit_error(
                then_value.creator_token.location,
                "conditional body cannot change types on the stack",
                [
                    Label::new(then_value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(then_type.name_str()),
                    Label::new(else_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(else_type.name_str())
                        .with_order(1),
                ],
                None,
                source_store,
            );
        }

        analyzer.set_value_type(merge_pair.output_value, then_type);
    }
}
