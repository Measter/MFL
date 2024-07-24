use std::{collections::HashMap, fmt::Display};

use intcast::IntCast;
use lasso::Spur;

use crate::{
    ir::{NameResolvedOp, OpCode, TypeResolvedOp, UnresolvedOp},
    option::OptionExt,
};

use super::source::Spanned;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OpId(u32);

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Op")?;
        self.0.fmt(f)
    }
}

pub struct OpStore {
    tokens: Vec<Spanned<Spur>>,
    unresolved: Vec<OpCode<UnresolvedOp>>,
    name_resolved: HashMap<OpId, OpCode<NameResolvedOp>>,
    type_resolved: HashMap<OpId, OpCode<TypeResolvedOp>>,
}

impl OpStore {
    pub fn new() -> Self {
        Self {
            tokens: Vec::new(),
            unresolved: Vec::new(),
            name_resolved: HashMap::new(),
            type_resolved: HashMap::new(),
        }
    }

    pub fn new_op(&mut self, code: OpCode<UnresolvedOp>, token: Spanned<Spur>) -> OpId {
        let new_id = OpId(self.unresolved.len().to_u32().expect("ICE: OpID overflow"));

        self.unresolved.push(code);
        self.tokens.push(token);

        new_id
    }

    #[inline]
    #[track_caller]
    pub fn get_token(&self, id: OpId) -> Spanned<Spur> {
        self.tokens[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_unresolved(&self, id: OpId) -> &OpCode<UnresolvedOp> {
        &self.unresolved[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_name_resolved(&self, id: OpId) -> &OpCode<NameResolvedOp> {
        &self.name_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_name_resolved(&mut self, id: OpId, op: OpCode<NameResolvedOp>) {
        self.name_resolved
            .insert(id, op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn get_type_resolved(&self, id: OpId) -> &OpCode<TypeResolvedOp> {
        &self.type_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_type_resolved(&mut self, id: OpId, op: OpCode<TypeResolvedOp>) {
        self.type_resolved
            .insert(id, op)
            .expect_none("ICE: Inserted multiple ops at id");
    }
}
