use ariadne::{Color, Label};

use crate::{
    diagnostics,
    opcode::Op,
    program::{
        static_analysis::{Analyzer, ConstVal, PtrId},
        ItemId, ItemKind, Program,
    },
    source_file::SourceStorage,
};

pub fn resolved_ident(program: &Program, analyzer: &mut Analyzer, op: &Op, item_id: ItemId) {
    let referenced_item = program.get_item_header(item_id);
    let op_data = analyzer.get_op_io(op.id);

    if let ItemKind::Memory = referenced_item.kind() {
        let output_id = op_data.outputs[0];
        analyzer.set_value_const(
            output_id,
            ConstVal::Ptr {
                id: PtrId::Mem(item_id),
                src_op_loc: op.token.location,
                offset: Some(0),
            },
        );
    }
}

pub fn epilogue_return(
    program: &Program,
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    let op_io = analyzer.get_op_io(op.id);

    for &value_id in op_io.inputs() {
        let Some([ConstVal::Ptr { id: PtrId::Mem(id), ..}]) = analyzer.value_consts([value_id]) else {
            continue;
        };

        let item = program.get_item_header(id);
        // We know it's a memory item, and only local allocations have a parent item.
        // The only items we can see with a parent are our own children, so this must be
        // an allocation within our stack frame.
        if item.parent().is_some() {
            *had_error = true;

            let mut creators = analyzer.get_creator_token(value_id);
            let mut labels = Vec::new();

            let root = creators.pop().unwrap();
            labels.push(Label::new(op.token.location).with_color(Color::Red));
            labels.push(
                Label::new(root.location)
                    .with_color(Color::Yellow)
                    .with_message(format!("Id: {}", value_id.0)),
            );
            for creator in creators {
                labels.push(
                    Label::new(creator.location)
                        .with_color(Color::Cyan)
                        .with_message(format!("Id: {}", value_id.0)),
                );
            }

            diagnostics::emit_error(
                op.token.location,
                "returning pointer to local memory",
                labels,
                None,
                source_store,
            )
        }
    }
}
