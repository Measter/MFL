use lasso::Spur;

use crate::{
    interners::Interners, opcode::Op, program::static_analysis::Analyzer,
    source_file::SourceStorage,
};

pub(super) fn push_bool(analyzer: &mut Analyzer, op: &Op, value: bool) {
    todo!()
}
pub(super) fn push_int(analyzer: &mut Analyzer, op: &Op, value: u64) {
    todo!()
}

pub(super) fn push_str(
    analyzer: &mut Analyzer,
    interner: &Interners,
    op: &Op,
    is_c_str: bool,
    str_id: Spur,
) {
    todo!()
}
pub(super) fn push_argc(analyzer: &mut Analyzer, op: &Op) {
    todo!()
}
pub(super) fn push_argv(analyzer: &mut Analyzer, op: &Op) {
    todo!()
}
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
