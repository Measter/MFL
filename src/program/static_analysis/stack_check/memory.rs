use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{SliceNOps, VecNOps},
    opcode::Op,
    source_file::SourceStorage,
    type_store::{TypeId, TypeKind, TypeStore},
};

use super::{
    super::{Analyzer, ValueId},
    ensure_stack_depth,
};

pub fn pack_array(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: u8,
) {
    ensure_stack_depth(
        analyzer,
        stack,
        source_store,
        had_error,
        op,
        count.to_usize(),
    );

    let mut inputs = Vec::new();
    let input_ids = stack.lastn(count.to_usize()).unwrap();
    for &id in input_ids {
        inputs.push(id);
        analyzer.consume_value(id, op.id);
    }

    stack.truncate(stack.len() - input_ids.len());

    let output = analyzer.new_value(op);
    stack.push(output);
    analyzer.set_op_io(op, &inputs, &[output]);
}

pub fn pack_struct(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
    type_id: TypeId,
) {
    let type_info = type_store.get_type_info(type_id);
    if !matches!(type_info.kind, TypeKind::Struct(_)) {
        diagnostics::emit_error(
            op.token.location,
            "cannot unpack that type",
            [Label::new(op.token.location).with_color(Color::Red)],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }
    let struct_info = type_store.get_struct_def(type_id);

    ensure_stack_depth(
        analyzer,
        stack,
        source_store,
        had_error,
        op,
        struct_info.fields.len(),
    );

    let mut inputs = Vec::new();
    let input_ids = stack.lastn(struct_info.fields.len()).unwrap();
    for &id in input_ids {
        inputs.push(id);
        analyzer.consume_value(id, op.id);
    }

    stack.truncate(stack.len() - input_ids.len());

    let output = analyzer.new_value(op);
    stack.push(output);
    analyzer.set_op_io(op, &inputs, &[output]);
}

pub fn extract_array(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let [array_id, idx] = stack.popn().unwrap();
    analyzer.consume_value(array_id, op.id);
    analyzer.consume_value(idx, op.id);

    let output_array = analyzer.new_value(op);
    stack.push(output_array);

    let output_value = analyzer.new_value(op);
    stack.push(output_value);

    analyzer.set_op_io(op, &[array_id, idx], &[output_array, output_value]);
}

pub fn insert_array(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<3>().unwrap();
    for id in inputs {
        analyzer.consume_value(id, op.id);
    }

    // Leave the array on the stack so the user can continue using it.
    let output = analyzer.new_value(op);
    stack.push(output);

    analyzer.set_op_io(op, &inputs, &[output]);
}

pub fn insert_struct(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for id in inputs {
        analyzer.consume_value(id, op.id);
    }

    // Leave the struct on the stack so the user can continue using it.
    let output = analyzer.new_value(op);
    stack.push(output);

    analyzer.set_op_io(op, &inputs, &[output]);
}

pub fn unpack(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 1);
    let input_id = stack.pop().unwrap();

    // To find out how many values we create, we need to look up the type of our input.
    let Some([input_type_id]) = analyzer.value_types([input_id]) else {
        analyzer.set_op_io(op, &[input_id], &[]);
        return;
    };

    let input_type_info = type_store.get_type_info(input_type_id);

    let length = match input_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::Struct(_) => {
            let struct_info = type_store.get_struct_def(input_type_id);
            struct_info.fields.len()
        }
        _ => {
            *had_error = true;
            let mut labels = Vec::new();
            let value_type_name = interner.resolve_lexeme(input_type_info.name);
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                input_id,
                0,
                value_type_name,
            );
            diagnostics::emit_error(
                op.token.location,
                format!("unable to unpack a `{value_type_name}`",),
                labels,
                "value must be an array or struct".to_owned(),
                source_store,
            );
            0
        }
    };

    let mut outputs = Vec::new();

    for _ in 0..length {
        let id = analyzer.new_value(op);
        stack.push(id);
        outputs.push(id);
    }

    analyzer.set_op_io(op, &[input_id], &outputs);
}

pub fn store(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }

    analyzer.set_op_io(op, &inputs, &[]);
}
