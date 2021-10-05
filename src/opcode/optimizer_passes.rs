use crate::lexer::TokenKind;

use super::{Op, OpCode};

use OpCode::*;

type PassFunction = fn(&[Op]) -> Option<(Vec<Op>, &[Op])>;

pub(super) const PASSES: &[PassFunction] = &[push_push_divmod, binary_ops, memory_offset];

pub(super) fn push_push_divmod(ops: &[Op]) -> Option<(Vec<Op>, &[Op])> {
    let (a, b, op, xs) = match ops {
        [a, b, op, xs @ ..]
            if a.code.is_push_int() && b.code.is_push_int() && op.code.is_div_mod() =>
        {
            (a, b, op, xs)
        }
        _ => return None,
    };

    let a_val = a.code.unwrap_push_int();
    let b_val = b.code.unwrap_push_int();

    let rem = a_val % b_val;
    let quot = a_val / b_val;

    let rem_opt = Op {
        code: PushInt(rem),
        token: TokenKind::Integer(rem),
        location: a.location.merge(op.location),
    };
    let quot_opt = Op {
        code: PushInt(quot),
        token: TokenKind::Integer(quot),
        location: a.location.merge(op.location),
    };

    Some((vec![quot_opt, rem_opt], xs))
}

/// [PushInt(a), PushInt(b), BinOp] -> [Push(a BinOp b)]
pub(super) fn binary_ops(ops: &[Op]) -> Option<(Vec<Op>, &[Op])> {
    let (a, b, op, xs) = match ops {
        [a, b, op, xs @ ..]
            if a.code.is_push_int() && b.code.is_push_int() && op.code.is_binary_op() =>
        {
            (a, b, op, xs)
        }

        _ => return None,
    };

    let a_val = a.code.unwrap_push_int();
    let b_val = b.code.unwrap_push_int();

    let opt = Op {
        code: PushInt(op.code.get_binary_op()(a_val, b_val)),
        token: TokenKind::Ident,
        location: a.location.merge(op.location),
    };

    Some((vec![opt], xs))
}

///   [Mem(a), PushInt(b), Add/Sub]
/// | [PushInt(a), Mem(b), Add/Sub] -> [Mem(a Add/Sub b)]
pub(super) fn memory_offset(ops: &[Op]) -> Option<(Vec<Op>, &[Op])> {
    let (a, b, op, xs) = match ops {
        [a, b, op, xs @ ..]
            if a.code.is_push_int() && b.code.is_mem() && matches!(op.code, Add | Subtract) =>
        {
            (a, b, op, xs)
        }
        [a, b, op, xs @ ..]
            if a.code.is_mem() && b.code.is_push_int() && matches!(op.code, Add | Subtract) =>
        {
            (a, b, op, xs)
        }
        _ => return None,
    };

    let a_val = a
        .code
        .push_int()
        .unwrap_or_else(|| a.code.unwrap_mem() as u64);
    let b_val = b
        .code
        .push_int()
        .unwrap_or_else(|| b.code.unwrap_mem() as u64);

    let opt = Op {
        code: Mem {
            offset: op.code.get_binary_op()(a_val, b_val) as _,
        },
        token: TokenKind::Mem,
        location: a.location.merge(op.location),
    };

    Some((vec![opt], xs))
}
