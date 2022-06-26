use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{failed_compare_stack_types, Analyzer, MergeInfo, PorthTypeKind},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

pub(super) fn epilogue_return(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    proc: &Procedure,
) {
    let op_data = analyzer.get_op_io(op.id);

    for (expected, actual_id) in proc.exit_stack().iter().zip(&op_data.inputs) {
        let actual_type = analyzer.value_types([*actual_id]);

        if actual_type != Some([expected.kind]) {
            let expected_kinds: Vec<_> = proc.exit_stack().iter().map(|t| t.kind).collect();

            failed_compare_stack_types(
                analyzer,
                source_store,
                &op_data.inputs,
                &expected_kinds,
                proc.exit_stack_location(),
                op.token.location,
                "procedure return stack mismatch",
            );
            *had_error = true;
            break;
        }
    }
}

pub(super) fn prologue(analyzer: &mut Analyzer, op: &Op, proc: &Procedure) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(proc.entry_stack()) {
        analyzer.set_value_type(output_id, output_type.kind);
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
    let referenced_proc = program.get_proc(proc_id);
    let op_data = analyzer.get_op_io(op.id);

    match referenced_proc.kind() {
        ProcedureKind::Memory => {
            let output_id = op_data.outputs[0];
            analyzer.set_value_type(output_id, PorthTypeKind::Ptr);
        }
        _ => {
            for (expected, actual_id) in referenced_proc.entry_stack().iter().zip(&op_data.inputs) {
                let actual_type = analyzer.value_types([*actual_id]);

                if actual_type != Some([expected.kind]) {
                    let expected_kinds: Vec<_> = referenced_proc
                        .entry_stack()
                        .iter()
                        .map(|t| t.kind)
                        .collect();

                    failed_compare_stack_types(
                        analyzer,
                        source_store,
                        &op_data.inputs,
                        &expected_kinds,
                        referenced_proc.entry_stack_location(),
                        op.token.location,
                        "procedure call signature mismatch",
                    );
                    *had_error = true;
                    break;
                }
            }

            let output_ids = op_data.outputs.clone();

            for (&output_type, output_id) in referenced_proc.exit_stack().iter().zip(output_ids) {
                analyzer.set_value_type(output_id, output_type.kind);
            }
        }
    }
}

pub(super) fn syscall(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);

    // All syscall inputs are untyped.
    // The output is always an int.

    analyzer.set_value_type(op_data.outputs[0], PorthTypeKind::Int);
}

pub(super) fn analyze_while(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    body: &ConditionalBlock,
) {
    // Evaluate the condition.
    super::analyze_block(
        program,
        proc,
        &body.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    // Evaluate the body.
    super::analyze_block(
        program,
        proc,
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

    // Now to confirm that all the new created values have the same type as what they merge with.
    let Some(MergeInfo::While(merge_info)) = analyzer.get_op_merges(op.id) else {
        panic!("ICE: While block should have merge info");
    };

    for merge_pair in merge_info
        .condition_merges
        .iter()
        .chain(&merge_info.body_merges)
    {
        let [new_value, old_value] = analyzer.values([merge_pair.src, merge_pair.dst]);
        let Some([new_type, old_type]) = analyzer.value_types([merge_pair.src, merge_pair.dst]) else { continue };

        if new_type != old_type {
            *had_error = true;
            diagnostics::emit_error(
                new_value.creator_token.location,
                "conditional body cannot change types on the stack",
                [
                    Label::new(new_value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(new_type.name_str()),
                    Label::new(old_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(old_type.name_str())
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
    proc: &Procedure,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    main: &ConditionalBlock,
    elifs: &[ConditionalBlock],
    else_block: Option<&[Op]>,
) {
    // Evaluate all the blocks.
    // Thankfully the order is unimportant here.
    super::analyze_block(
        program,
        proc,
        &main.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    super::analyze_block(
        program,
        proc,
        &main.block,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    for elif_block in elifs {
        super::analyze_block(
            program,
            proc,
            &elif_block.condition,
            analyzer,
            had_error,
            interner,
            source_store,
        );
        super::analyze_block(
            program,
            proc,
            &elif_block.block,
            analyzer,
            had_error,
            interner,
            source_store,
        );
    }
    if let Some(else_block) = else_block {
        super::analyze_block(
            program,
            proc,
            else_block,
            analyzer,
            had_error,
            interner,
            source_store,
        );
    }

    // All the conditions are stored in the op inputs.
    let conditions_iter = std::iter::once(main).chain(elifs);
    let op_data = analyzer.get_op_io(op.id);
    for (&condition_id, block) in op_data.inputs.iter().zip(conditions_iter) {
        let Some([condition_type]) = analyzer.value_types([condition_id]) else { continue };
        if condition_type != PorthTypeKind::Bool {
            *had_error = true;
            let [value] = analyzer.values([condition_id]);

            diagnostics::emit_error(
                block.do_token.location,
                "condition must evaluate to a boolean",
                [
                    Label::new(block.do_token.location)
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

    // Now to type check all the merging values.
    let Some(MergeInfo::If(merges)) = analyzer.get_op_merges(op.id) else {
        panic!("ICE: Missing merges in If block");
    };

    let pairs = merges
        .main
        .condition_merges
        .iter()
        .chain(&merges.main.body_merges)
        .chain(
            merges
                .elifs
                .iter()
                .flat_map(|m| m.condition_merges.iter().chain(&m.body_merges)),
        )
        .chain(&merges.else_block.body_merges);

    for merge_pair in pairs {
        let [new_value, old_value] = analyzer.values([merge_pair.src, merge_pair.dst]);
        let Some([new_type, old_type]) = analyzer.value_types([merge_pair.src, merge_pair.dst]) else { continue };

        if new_type != old_type {
            *had_error = true;
            diagnostics::emit_error(
                new_value.creator_token.location,
                "conditional body cannot change types on the stack",
                [
                    Label::new(new_value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(new_type.name_str()),
                    Label::new(old_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(old_type.name_str())
                        .with_order(1),
                ],
                None,
                source_store,
            );
        }
    }
}
