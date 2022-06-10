use crate::{
    interners::Interners, opcode::Op, program::static_analysis::Analyzer,
    source_file::SourceStorage,
};

pub(super) fn add(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn subtract(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn bitand_bitor(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn multiply_and_shift(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}
