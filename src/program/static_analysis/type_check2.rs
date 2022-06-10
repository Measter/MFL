use lasso::Interner;

use crate::{
    interners::Interners,
    opcode::Op,
    program::{Procedure, Program},
    source_file::SourceStorage,
};

use super::Analyzer;

pub(super) fn analyze_block(
    program: &Program,
    proc: &Procedure,
    block: &[Op],
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    todo!()
}
