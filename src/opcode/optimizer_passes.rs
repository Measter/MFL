use crate::lexer::TokenKind;

use super::{Op, OpCode};

use OpCode::*;

type PassFunction = fn(&[Op]) -> Option<(Vec<Op>, &[Op])>;

pub(super) const PASSES: &[PassFunction] = &[binary_ops, memory_offset];

/// [Push(a), Push(b), BinOp] -> [Push(a BinOp b)]
pub(super) fn binary_ops(ops: &[Op]) -> Option<(Vec<Op>, &[Op])> {
    let (a_loc, a_val, b_val, op, xs) = match ops {
        [Op {
            code: Push(a_val),
            location: a_loc,
            ..
        }, Op {
            code: Push(b_val), ..
        }, op, xs @ ..]
            if op.code.is_binary_op() =>
        {
            (*a_loc, *a_val, *b_val, op, xs)
        }
        _ => return None,
    };

    let opt = Op {
        code: Push(op.code.get_binary_op()(a_val, b_val)),
        token: TokenKind::Ident,
        location: a_loc.merge(op.location),
    };

    Some((vec![opt], xs))
}

///   [Mem(a), Push(b), Add/Sub]
/// | [Push(a), Mem(b), Add/Sub] -> [Mem(a Add/Sub b)]
pub(super) fn memory_offset(ops: &[Op]) -> Option<(Vec<Op>, &[Op])> {
    let (a_loc, a_val, b_val, op, xs) = match ops {
        [Op {
            code: Push(a_val),
            location: a_loc,
            ..
        }, Op {
            code: Mem { offset: b_val },
            ..
        }, op @ Op {
            code: Add | Subtract,
            ..
        }, xs @ ..] => (*a_loc, *a_val, *b_val as u64, op, xs),
        [Op {
            code: Mem { offset: a_val },
            location: a_loc,
            ..
        }, Op {
            code: Push(b_val), ..
        }, op @ Op {
            code: Add | Subtract,
            ..
        }, xs @ ..] => (*a_loc, *a_val as u64, *b_val, op, xs),
        _ => return None,
    };

    let opt = Op {
        code: Mem {
            offset: op.code.get_binary_op()(a_val, b_val) as _,
        },
        token: TokenKind::Mem,
        location: a_loc.merge(op.location),
    };

    Some((vec![opt], xs))
}
