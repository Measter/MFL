use crate::{
    interners::Interners, opcode::Op, program::static_analysis::Analyzer,
    source_file::SourceStorage,
};

pub(super) fn compare(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn equal(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}
