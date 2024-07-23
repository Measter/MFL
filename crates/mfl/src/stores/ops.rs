use std::fmt::Display;

use lasso::Spur;

use crate::ir::OpCode;

use super::source::Spanned;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OpId(pub u32);

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Op")?;
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct Op<T> {
    pub code: OpCode<T>,
    pub id: OpId,
    pub token: Spanned<Spur>,
}

impl<T> Op<T> {
    pub fn new(id: OpId, code: OpCode<T>, token: Spanned<Spur>) -> Self {
        Self { id, code, token }
    }
}

pub struct OpStore {}

impl OpStore {
    pub fn new() -> Self {
        Self {}
    }
}
