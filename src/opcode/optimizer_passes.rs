use crate::{
    interners::Interners,
    lexer::{Token, TokenKind},
    source_file::SourceStorage,
};

use super::{Op, OpCode};

use codespan_reporting::files::Files;
use OpCode::*;

type PassFunction =
    for<'a> fn(&'a [Op], &mut Interners, &SourceStorage) -> Option<(Vec<Op>, &'a [Op])>;

pub(super) const PASSES: &[PassFunction] =
    &[over_over, push_push_divmod, binary_ops, memory_offset];

/// [Over, Over] -> [DupPair]
fn over_over<'a>(
    ops: &'a [Op],
    interners: &mut Interners,
    sources: &SourceStorage,
) -> Option<(Vec<Op>, &'a [Op])> {
    let (a, b, xs) = match ops {
        [a, b, xs @ ..]
            if a.code == OpCode::Dup { depth: 1 } && b.code == OpCode::Dup { depth: 1 } =>
        {
            (a, b, xs)
        }
        _ => return None,
    };

    let location = if a.token.location.file_id != b.token.location.file_id {
        b.token.location
    } else {
        a.token.location.merge(b.token.location)
    };
    let lexeme = &sources.source(location.file_id).unwrap()[location.range()];
    let lexeme = interners.intern_lexeme(lexeme);

    let token = Token {
        kind: TokenKind::DupPair,
        lexeme,
        location,
    };

    let op = Op {
        code: OpCode::DupPair,
        token,
        expansions: Vec::new(),
    };

    Some((vec![op], xs))
}

/// [PushInt(a), PushInt(b) DivMod] -> [PushInt(a / b), PushInt(a % b)]
fn push_push_divmod<'a>(
    ops: &'a [Op],
    interners: &mut Interners,
    sources: &SourceStorage,
) -> Option<(Vec<Op>, &'a [Op])> {
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

    let location = if a.token.location.file_id != op.token.location.file_id {
        op.token.location
    } else {
        a.token.location.merge(op.token.location)
    };
    let lexeme = &sources.source(location.file_id).unwrap()[location.range()];
    let lexeme = interners.intern_lexeme(lexeme);

    let rem_token = Token {
        kind: TokenKind::Integer(rem),
        lexeme,
        location,
    };
    let quot_token = Token {
        kind: TokenKind::Integer(quot),
        lexeme,
        location,
    };

    let rem_opt = Op {
        code: PushInt(rem),
        token: rem_token,
        expansions: Vec::new(),
    };
    let quot_opt = Op {
        code: PushInt(quot),
        token: quot_token,
        expansions: Vec::new(),
    };

    Some((vec![quot_opt, rem_opt], xs))
}

/// [PushInt(a), PushInt(b), BinOp] -> [Push(a BinOp b)]
fn binary_ops<'a>(
    ops: &'a [Op],
    interners: &mut Interners,
    sources: &SourceStorage,
) -> Option<(Vec<Op>, &'a [Op])> {
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
    let res = op.code.get_binary_op()(a_val, b_val);

    let location = if a.token.location.file_id != op.token.location.file_id {
        op.token.location
    } else {
        a.token.location.merge(op.token.location)
    };
    let lexeme = &sources.source(location.file_id).unwrap()[location.range()];
    let lexeme = interners.intern_lexeme(lexeme);

    let token = Token {
        kind: TokenKind::Integer(res),
        lexeme,
        location,
    };

    let code = if op.code.is_boolean_op() {
        PushBool(res != 0)
    } else {
        PushInt(res)
    };

    let opt = Op {
        code,
        token,
        expansions: Vec::new(),
    };

    Some((vec![opt], xs))
}

///   [Mem(a), PushInt(b), Add/Sub]
/// | [PushInt(a), Mem(b), Add/Sub] -> [Mem(a Add/Sub b)]
fn memory_offset<'a>(
    ops: &'a [Op],
    interners: &mut Interners,
    sources: &SourceStorage,
) -> Option<(Vec<Op>, &'a [Op])> {
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
    let res = op.code.get_binary_op()(a_val, b_val);

    let location = if a.token.location.file_id != op.token.location.file_id {
        op.token.location
    } else {
        a.token.location.merge(op.token.location)
    };

    let lexeme = &sources.source(location.file_id).unwrap()[location.range()];
    let lexeme = interners.intern_lexeme(lexeme);

    let token = Token {
        kind: TokenKind::Mem,
        lexeme,
        location,
    };

    let opt = Op {
        code: Mem { offset: res as _ },
        token,
        expansions: Vec::new(),
    };

    Some((vec![opt], xs))
}
