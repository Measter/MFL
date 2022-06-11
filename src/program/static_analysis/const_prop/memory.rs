use crate::{
    interners::Interners,
    opcode::Op,
    program::static_analysis::{Analyzer, PorthTypeKind},
    source_file::SourceStorage,
    Width,
};

pub(super) fn load(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    width: Width,
    kind: PorthTypeKind,
) {
    todo!()
}
pub(super) fn store(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    kind: PorthTypeKind,
) {
    todo!()
}
