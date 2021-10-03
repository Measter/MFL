use crate::lexer::TokenKind;

use super::{Op, OpCode};

use OpCode::*;

type PassFunction = fn(&[Op]) -> Option<(Vec<Op>, &[Op])>;

pub(super) const PASSES: &[PassFunction] = &[binary_ops, memory_offset];

/// [Push(a), Push(b), BinOp] -> [Push(a BinOp b)]
pub(super) fn binary_ops(ops: &[Op]) -> Option<(Vec<Op>, &[Op])> {
    let (a, b, op, xs) = match ops {
        [a, b, op, xs @ ..] if a.code.is_push() && b.code.is_push() && op.code.is_binary_op() => {
            (a, b, op, xs)
        }

        _ => return None,
    };

    let a_val = a.code.unwrap_push();
    let b_val = b.code.unwrap_push();

    let opt = Op {
        code: Push(op.code.get_binary_op()(a_val, b_val)),
        token: TokenKind::Ident,
        location: a.location.merge(op.location),
    };

    Some((vec![opt], xs))
}

///   [Mem(a), Push(b), Add/Sub]
/// | [Push(a), Mem(b), Add/Sub] -> [Mem(a Add/Sub b)]
pub(super) fn memory_offset(ops: &[Op]) -> Option<(Vec<Op>, &[Op])> {
    let (a, b, op, xs) = match ops {
        [a, b, op, xs @ ..]
            if a.code.is_push() && b.code.is_mem() && matches!(op.code, Add | Subtract) =>
        {
            (a, b, op, xs)
        }
        [a, b, op, xs @ ..]
            if a.code.is_mem() && b.code.is_push() && matches!(op.code, Add | Subtract) =>
        {
            (a, b, op, xs)
        }
        _ => return None,
    };

    let a_val = a.code.push().unwrap_or_else(|| a.code.unwrap_mem() as u64);
    let b_val = b.code.push().unwrap_or_else(|| b.code.unwrap_mem() as u64);

    let opt = Op {
        code: Mem {
            offset: op.code.get_binary_op()(a_val, b_val) as _,
        },
        token: TokenKind::Mem,
        location: a.location.merge(op.location),
    };

    Some((vec![opt], xs))
}
