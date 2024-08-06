use std::{collections::HashMap, fmt::Display};

use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;
use stores::source::Spanned;

use crate::{
    ir::{NameResolvedOp, OpCode, PartiallyResolvedOp, TypeResolvedOp, UnresolvedOp},
    option::OptionExt,
};

use super::values::ValueId;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OpId(u32);

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Op")?;
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct OpIoValues {
    pub inputs: SmallVec<[ValueId; 8]>,
    pub outputs: SmallVec<[ValueId; 8]>,
}

impl OpIoValues {
    #[inline]
    pub fn inputs(&self) -> &[ValueId] {
        self.inputs.as_ref()
    }

    #[inline]
    pub fn outputs(&self) -> &[ValueId] {
        self.outputs.as_ref()
    }
}

pub struct OpStore {
    tokens: Vec<Spanned<Spur>>,
    unresolved: Vec<OpCode<UnresolvedOp>>,
    name_resolved: HashMap<OpId, OpCode<NameResolvedOp>>,
    partial_type_resolved: HashMap<OpId, OpCode<PartiallyResolvedOp>>,
    type_resolved: HashMap<OpId, OpCode<TypeResolvedOp>>,
    op_io: HashMap<OpId, OpIoValues>,
}

impl OpStore {
    pub fn new() -> Self {
        Self {
            tokens: Vec::new(),
            unresolved: Vec::new(),
            name_resolved: HashMap::new(),
            partial_type_resolved: HashMap::new(),
            type_resolved: HashMap::new(),
            op_io: HashMap::new(),
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
    pub fn get_partially_type_resolved(&self, id: OpId) -> &OpCode<PartiallyResolvedOp> {
        &self.partial_type_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_partially_type_resolved(&mut self, id: OpId, op: OpCode<PartiallyResolvedOp>) {
        self.partial_type_resolved
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

    #[inline]
    #[track_caller]
    pub fn overwrite_type_resolved(&mut self, id: OpId, op: OpCode<TypeResolvedOp>) {
        self.type_resolved.insert(id, op);
    }

    #[track_caller]
    pub fn set_op_io(&mut self, op_id: OpId, inputs: &[ValueId], outputs: &[ValueId]) {
        let new_data = OpIoValues {
            inputs: inputs.into(),
            outputs: outputs.into(),
        };
        if let Some(prev) = self.op_io.get(&op_id) {
            panic!("Set operands twice - cur_token: {op_id}, new_data: {new_data:#?}, prev_data: {prev:#?}");
        }
        self.op_io.insert(op_id, new_data);
    }

    #[inline]
    #[track_caller]
    pub fn get_op_io(&self, op_idx: OpId) -> &OpIoValues {
        &self.op_io[&op_idx]
    }
}
