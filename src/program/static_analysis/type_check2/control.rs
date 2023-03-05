use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{If, Op, While},
    program::{
        static_analysis::{can_promote_int, failed_compare_stack_types, Analyzer},
        ItemId, ItemKind, ItemSignatureResolved, Program,
    },
    source_file::SourceStorage,
    type_store::{BuiltinTypes, TypeKind, TypeStore},
};

pub(super) fn epilogue_return(
    program: &Program,
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    item_id: ItemId,
) {
    let item_sig = program.get_item_signature_resolved(item_id);
    let item_sig_tokens = program.get_item_signature_unresolved(item_id);
    let op_data = analyzer.get_op_io(op.id);

    for (&expected, actual_id) in item_sig.exit_stack().iter().zip(&op_data.inputs) {
        let Some(actual_type) = analyzer.value_types([*actual_id]) else {continue};

        if actual_type != [expected] {
            failed_compare_stack_types(
                analyzer,
                interner,
                source_store,
                type_store,
                &op_data.inputs,
                item_sig.exit_stack(),
                item_sig_tokens.exit_stack_location(),
                op.token.location,
                "item return stack mismatch",
            );
            *had_error = true;
            break;
        }
    }
}

pub(super) fn prologue(analyzer: &mut Analyzer, op: &Op, item_sig: &ItemSignatureResolved) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(item_sig.entry_stack()) {
        analyzer.set_value_type(output_id, output_type);
    }
}

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
    item_id: ItemId,
) {
    let referenced_item = program.get_item_header(item_id);
    let referenced_item_sig = program.get_item_signature_resolved(item_id);
    let referenced_item_sig_tokens = program.get_item_signature_unresolved(item_id);
    let op_data = analyzer.get_op_io(op.id);

    match referenced_item.kind() {
        ItemKind::Memory => {
            let pointer_type = referenced_item_sig.memory_type();

            let output_id = op_data.outputs[0];
            analyzer.set_value_type(output_id, type_store.get_pointer(interner, pointer_type).id);
        }
        _ => {
            for (&expected, actual_id) in referenced_item_sig
                .entry_stack()
                .iter()
                .zip(&op_data.inputs)
            {
                let Some([actual_type]) = analyzer.value_types([*actual_id]) else {
                    continue;
                };

                if actual_type != expected {
                    let actual_type_info = type_store.get_type_info(actual_type);
                    let expected_type_info = type_store.get_type_info(expected);

                    if !matches!((actual_type_info.kind, expected_type_info.kind), (
                        TypeKind::Integer { width: actual_width, signed: actual_signed },
                        TypeKind::Integer { width: expected_width, signed: expected_signed }
                    ) if can_promote_int(actual_width, actual_signed, expected_width, expected_signed ))
                    {
                        failed_compare_stack_types(
                            analyzer,
                            interner,
                            source_store,
                            type_store,
                            &op_data.inputs,
                            referenced_item_sig.entry_stack(),
                            referenced_item_sig_tokens.entry_stack_location(),
                            op.token.location,
                            "procedure call signature mismatch",
                        );
                        *had_error = true;
                        break;
                    }
                }
            }

            let output_ids = op_data.outputs.clone();

            for (&output_type, output_id) in referenced_item_sig.exit_stack().iter().zip(output_ids)
            {
                analyzer.set_value_type(output_id, output_type);
            }
        }
    }
}

pub(super) fn syscall(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);

    // All syscall inputs are untyped.
    // The output is always an int.

    analyzer.set_value_type(
        op_data.outputs[0],
        type_store.get_builtin(BuiltinTypes::U64).id,
    );
}

pub(super) fn analyze_while(
    program: &Program,
    item_id: ItemId,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    op: &Op,
    while_op: &While,
) {
    let Some(merge_info) = analyzer.get_while_merges(op.id).map(Clone::clone) else {
        panic!("ICE: While block should have merge info");
    };

    // We don't need to worry about the order of evaluation here as they don't effect eachother.
    // Evaluate the condition.
    super::analyze_block(
        program,
        item_id,
        &while_op.condition,
        analyzer,
        had_error,
        interner,
        source_store,
        type_store,
    );
    // Evaluate the body.
    super::analyze_block(
        program,
        item_id,
        &while_op.body_block,
        analyzer,
        had_error,
        interner,
        source_store,
        type_store,
    );

    // We expect a boolean to be the result of evaluating the condition.
    let op_data = analyzer.get_op_io(op.id);
    let condition_inputs = *op_data.inputs.as_arr::<1>();
    let Some([condition_type]) = analyzer.value_types(condition_inputs) else { return };

    if condition_type != type_store.get_builtin(BuiltinTypes::Bool).id {
        *had_error = true;
        let [value] = analyzer.values(condition_inputs);
        let condition_info = type_store.get_type_info(condition_type);
        let condition_type_name = interner.resolve_lexeme(condition_info.name);

        diagnostics::emit_error(
            while_op.do_token.location,
            "condition must evaluate to a boolean",
            [
                Label::new(while_op.do_token.location)
                    .with_color(Color::Cyan)
                    .with_message("expected here"),
                Label::new(value.creator_token.location)
                    .with_color(Color::Red)
                    .with_message(condition_type_name)
                    .with_order(1),
            ],
            None,
            source_store,
        );
    }

    for merge_pair in merge_info.condition.iter().chain(&merge_info.body) {
        let [pre_value, condition_value] =
            analyzer.values([merge_pair.pre_value, merge_pair.condition_value]);
        let Some(input_type_ids @ [pre_type, condition_type]) = analyzer.value_types([merge_pair.pre_value, merge_pair.condition_value,]) else { continue };

        if pre_type != condition_type {
            let [pre_type_name, condition_type_name] = input_type_ids.map(|id| {
                let info = type_store.get_type_info(id);
                interner.resolve_lexeme(info.name)
            });
            *had_error = true;
            diagnostics::emit_error(
                condition_value.creator_token.location,
                "while loop condition or body may not change types on the stack",
                [
                    Label::new(condition_value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(condition_type_name),
                    Label::new(pre_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(pre_type_name)
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
    item_id: ItemId,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    op: &Op,
    if_op: &If,
) {
    // Evaluate all the blocks.
    // Thankfully the order is unimportant here.
    super::analyze_block(
        program,
        item_id,
        &if_op.condition,
        analyzer,
        had_error,
        interner,
        source_store,
        type_store,
    );
    super::analyze_block(
        program,
        item_id,
        &if_op.then_block,
        analyzer,
        had_error,
        interner,
        source_store,
        type_store,
    );
    super::analyze_block(
        program,
        item_id,
        &if_op.else_block,
        analyzer,
        had_error,
        interner,
        source_store,
        type_store,
    );

    // All the conditions are stored in the op inputs.
    let op_data = analyzer.get_op_io(op.id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type]) = analyzer.value_types([condition_value_id]) {
        if condition_type != type_store.get_builtin(BuiltinTypes::Bool).id {
            *had_error = true;
            let [value] = analyzer.values([condition_value_id]);
            let condition_type_info = type_store.get_type_info(condition_type);
            let condition_type_name = interner.resolve_lexeme(condition_type_info.name);

            diagnostics::emit_error(
                if_op.do_token.location,
                "condition must evaluate to a boolean",
                [
                    Label::new(if_op.do_token.location)
                        .with_color(Color::Cyan)
                        .with_message("expected here"),
                    Label::new(value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(condition_type_name)
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
        let Some(input_type_ids @ [then_type, else_type]) = analyzer.value_types([merge_pair.then_value, merge_pair.else_value]) else { continue };

        if then_type != else_type {
            let [then_type_name, else_type_name] = input_type_ids.map(|id| {
                let info = type_store.get_type_info(id);
                interner.resolve_lexeme(info.name)
            });

            *had_error = true;
            diagnostics::emit_error(
                then_value.creator_token.location,
                "conditional body cannot change types on the stack",
                [
                    Label::new(then_value.creator_token.location)
                        .with_color(Color::Red)
                        .with_message(then_type_name),
                    Label::new(else_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(else_type_name)
                        .with_order(1),
                ],
                None,
                source_store,
            );
        }

        analyzer.set_value_type(merge_pair.output_value, then_type);
    }
}
