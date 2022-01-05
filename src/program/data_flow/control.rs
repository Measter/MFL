use crate::{opcode::Op, program::Procedure};

use super::{Analyzer, ValueId};

pub(super) fn prologue(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    op_idx: usize,
    op: &Op,
    proc: &Procedure,
) {
    let mut outputs = Vec::new();
    for input_type in proc.entry_stack() {
        let (new_id, _) = analyzer.new_value(input_type.kind, op_idx, op.token);
        outputs.push(new_id);
        stack.push(new_id);
    }

    analyzer.set_io(op_idx, op.token, &[], &outputs);
}
