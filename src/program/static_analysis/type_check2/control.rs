use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{If, Op, While},
    program::{
        static_analysis::{
            can_promote_int_bidirectional, can_promote_int_unidirectional,
            failed_compare_stack_types, promote_int_type_bidirectional, Analyzer,
        },
        ItemId, ItemKind, ItemSignatureResolved, Program,
    },
    source_file::SourceStorage,
    type_store::{BuiltinTypes, TypeKind, TypeStore},
};

pub fn epilogue_return(
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
        let Some([actual_type]) = analyzer.value_types([*actual_id]) else {continue};

        if actual_type != expected {
            let actual_type_info = type_store.get_type_info(actual_type);
            let expected_type_info = type_store.get_type_info(expected);

            if !matches!((actual_type_info.kind, expected_type_info.kind), (
                        TypeKind::Integer { width: actual_width, signed: actual_signed },
                        TypeKind::Integer { width: expected_width, signed: expected_signed }
                    ) if can_promote_int_unidirectional(actual_width, actual_signed, expected_width, expected_signed ))
            {
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
}

pub fn prologue(analyzer: &mut Analyzer, op: &Op, item_sig: &ItemSignatureResolved) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(item_sig.entry_stack()) {
        analyzer.set_value_type(output_id, output_type);
    }
}

pub fn resolved_ident(
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
    let op_data = analyzer.get_op_io(op.id);

    match referenced_item.kind() {
        ItemKind::Memory => {
            let reference_item_memory_type = program.get_memory_type_resolved(item_id);

            let output_id = op_data.outputs[0];
            let ptr_type = type_store.get_pointer(interner, reference_item_memory_type);
            analyzer.set_value_type(output_id, ptr_type.id);
        }
        ItemKind::Function | ItemKind::Const => {
            let referenced_item_sig = program.get_item_signature_resolved(item_id);
            let referenced_item_sig_tokens = program.get_item_signature_unresolved(item_id);

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
                    ) if can_promote_int_unidirectional(actual_width, actual_signed, expected_width, expected_signed ))
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
        _ => panic!("ICE: Unexpected item kind: {:?}", referenced_item.kind()),
    }
}

pub fn syscall(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);

    for (idx, input_value) in op_data.inputs().iter().enumerate() {
        let Some([type_id]) = analyzer.value_types([*input_value]) else { continue };
        let type_info = type_store.get_type_info(type_id);
        match type_info.kind {
            TypeKind::Integer { .. } | TypeKind::Pointer(_) | TypeKind::Bool => {}

            _ => {
                let type_name = interner.resolve_lexeme(type_info.name);
                let mut labels = diagnostics::build_creator_label_chain(
                    analyzer,
                    [(*input_value, idx.to_u64(), type_name)],
                    Color::Yellow,
                    Color::Cyan,
                );

                labels.push(Label::new(op.token.location).with_color(Color::Red));

                diagnostics::emit_error(
                    op.token.location,
                    "invalid syscall parameter",
                    labels,
                    None,
                    source_store,
                );
                *had_error = true;
            }
        }
    }

    // The output is always an int.

    analyzer.set_value_type(
        op_data.outputs[0],
        type_store.get_builtin(BuiltinTypes::U64).id,
    );
}

pub fn analyze_while(
    had_error: &mut bool,
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    op: &Op,
    while_op: &While,
) {
    let Some(merge_info) = analyzer.get_while_merges(op.id).map(Clone::clone) else {
        panic!("ICE: While block should have merge info");
    };

    // The data-flow analysis has already analyzed the sub-blocks. We only need to concern
    // ourselves with our merges.

    // We expect a boolean to be the result of evaluating the condition.
    let op_data = analyzer.get_op_io(op.id);
    let condition_inputs = *op_data.inputs.as_arr::<1>();
    let Some([condition_type]) = analyzer.value_types(condition_inputs) else { return };

    if condition_type != type_store.get_builtin(BuiltinTypes::Bool).id {
        *had_error = true;
        let condition_info = type_store.get_type_info(condition_type);
        let condition_type_name = interner.resolve_lexeme(condition_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(condition_inputs[0], 0, condition_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(while_op.do_token).with_color(Color::Red));

        diagnostics::emit_error(
            while_op.do_token,
            "condition must evaluate to a boolean",
            labels,
            None,
            source_store,
        );
    }

    for merge_pair in merge_info.condition.iter().chain(&merge_info.body) {
        let [condition_value] = analyzer.values([merge_pair.condition_value]);
        let Some(input_type_ids @ [pre_type, condition_type]) = analyzer.value_types([merge_pair.pre_value, merge_pair.condition_value,]) else { continue };
        let pre_type_info = type_store.get_type_info(pre_type);
        let condition_type_info = type_store.get_type_info(condition_type);

        if pre_type != condition_type
            && !matches!((pre_type_info.kind, condition_type_info.kind), (
                        TypeKind::Integer { width: pre_width, signed: pre_signed },
                        TypeKind::Integer { width: condition_width, signed: condition_signed }
                    ) if can_promote_int_unidirectional(condition_width, condition_signed, pre_width, pre_signed ))
        {
            let [pre_type_name, condition_type_name] = input_type_ids.map(|id| {
                let info = type_store.get_type_info(id);
                interner.resolve_lexeme(info.name)
            });

            let labels = diagnostics::build_creator_label_chain(
                analyzer,
                [
                    (merge_pair.pre_value, 0, pre_type_name),
                    (merge_pair.condition_value, 1, condition_type_name),
                ],
                Color::Yellow,
                Color::Cyan,
            );

            *had_error = true;
            diagnostics::emit_error(
                condition_value.source_location,
                "while loop condition or body may not change types on the stack",
                labels,
                None,
                source_store,
            );
        }
    }
}

pub fn analyze_if(
    had_error: &mut bool,
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    op: &Op,
    if_op: &If,
) {
    // The data-flow analysis has already done the full check on each block, so we don't have to do it here.

    // All the conditions are stored in the op inputs.
    let op_data = analyzer.get_op_io(op.id);
    let condition_value_id = op_data.inputs[0];
    if let Some([condition_type]) = analyzer.value_types([condition_value_id]) {
        if condition_type != type_store.get_builtin(BuiltinTypes::Bool).id {
            *had_error = true;
            let condition_type_info = type_store.get_type_info(condition_type);
            let condition_type_name = interner.resolve_lexeme(condition_type_info.name);

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(condition_value_id, 0, condition_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(if_op.do_token).with_color(Color::Red));

            diagnostics::emit_error(
                if_op.do_token,
                "condition must evaluate to a boolean",
                labels,
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
        let [then_value] = analyzer.values([merge_pair.then_value]);
        let Some(input_type_ids @ [then_type, else_type]) = analyzer.value_types([merge_pair.then_value, merge_pair.else_value]) else { continue };
        let then_type_info = type_store.get_type_info(then_type);
        let else_type_info = type_store.get_type_info(else_type);

        let final_type = match (then_type_info.kind, else_type_info.kind) {
            (
                TypeKind::Integer {
                    width: then_width,
                    signed: then_signed,
                },
                TypeKind::Integer {
                    width: else_width,
                    signed: else_signed,
                },
            ) if (can_promote_int_bidirectional(
                then_width,
                then_signed,
                else_width,
                else_signed,
            )) =>
            {
                let kind = promote_int_type_bidirectional(
                    then_width,
                    then_signed,
                    else_width,
                    else_signed,
                )
                .unwrap();

                type_store.get_builtin(kind.into()).id
            }
            _ => {
                if then_type != else_type {
                    let [then_type_name, else_type_name] = input_type_ids.map(|id| {
                        let info = type_store.get_type_info(id);
                        interner.resolve_lexeme(info.name)
                    });

                    let labels = diagnostics::build_creator_label_chain(
                        analyzer,
                        [
                            (merge_pair.then_value, 0, then_type_name),
                            (merge_pair.else_value, 1, else_type_name),
                        ],
                        Color::Yellow,
                        Color::Cyan,
                    );

                    *had_error = true;
                    diagnostics::emit_error(
                        then_value.source_location,
                        "conditional body cannot change types on the stack",
                        labels,
                        None,
                        source_store,
                    );
                }

                then_type
            }
        };

        analyzer.set_value_type(merge_pair.output_value, final_type);
    }
}
