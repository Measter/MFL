use lasso::Spur;

use crate::{
    interners::Interners,
    opcode::Op,
    program::static_analysis::{Analyzer, ValueId},
    source_file::SourceStorage,
};

pub(super) fn cast_int(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}
pub(super) fn cast_ptr(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}
pub(super) fn dup(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
    depth: usize,
) {
    todo!()
}

pub(super) fn dup_pair(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    todo!()
}
