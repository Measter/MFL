use crate::{
    ir::{Op, TypeResolvedOp},
    pass_manager::static_analysis::Analyzer,
    Stores,
};

pub(crate) fn add(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    local_had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    todo!()
}

pub(crate) fn multiply_div_rem_shift(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    local_had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    todo!()
}

pub(crate) fn subtract(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    local_had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    todo!()
}

pub(crate) fn bitnot(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    local_had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    todo!()
}

pub(crate) fn bitand_bitor_bitxor(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    local_had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    todo!()
}
