use std::{collections::HashMap, fmt::Display};

use intcast::IntCast;
use lasso::Spur;

use crate::{
    ir::{NameResolvedOp, OpCode, TypeResolvedOp, UnresolvedOp},
    option::OptionExt,
};

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

pub struct OpStore {
    unresolved: Vec<Op<UnresolvedOp>>,
    name_resolved: HashMap<OpId, Op<NameResolvedOp>>,
    type_resolved: HashMap<OpId, Op<TypeResolvedOp>>,
}

impl OpStore {
    pub fn new() -> Self {
        Self {
            unresolved: Vec::new(),
            name_resolved: HashMap::new(),
            type_resolved: HashMap::new(),
        }
    }

    pub fn new_op(&mut self, code: OpCode<UnresolvedOp>, token: Spanned<Spur>) -> OpId {
        let new_id = OpId(self.unresolved.len().to_u32().expect("ICE: OpID overflow"));

        let op = Op {
            code,
            id: new_id,
            token,
        };

        self.unresolved.push(op);

        new_id
    }

    #[inline]
    #[track_caller]
    pub fn get_unresolved(&self, id: OpId) -> &Op<UnresolvedOp> {
        &self.unresolved[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_name_resolved(&self, id: OpId) -> &Op<NameResolvedOp> {
        &self.name_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_name_resolved(&mut self, id: OpId, op: Op<NameResolvedOp>) {
        self.name_resolved
            .insert(id, op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn get_type_resolved(&self, id: OpId) -> &Op<TypeResolvedOp> {
        &self.type_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_type_resolved(&mut self, id: OpId, op: Op<TypeResolvedOp>) {
        self.type_resolved
            .insert(id, op)
            .expect_none("ICE: Inserted multiple ops at id");
    }
}
