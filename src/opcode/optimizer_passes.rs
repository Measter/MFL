use crate::{
    interners::Interners,
    lexer::{Token, TokenKind},
    n_ops::NOps,
    source_file::SourceStorage,
};

use super::{Op, OpCode};

use OpCode::*;

type PassFunction =
    for<'a> fn(&'a [Op], &mut Interners, &SourceStorage) -> Option<(Vec<Op>, &'a [Op])>;

pub(super) const PASSES: &[PassFunction] = &[
    over_over,
    push_not,
    push_push_divmod,
    binary_ops,
    memory_offset,
];

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
    let lexeme = &sources.source(location.file_id)[location.range()];
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

/// [PushInt(a), BitNot] -> [PushInt(!a)]
fn push_not<'a>(
    ops: &'a [Op],
    interners: &mut Interners,
    sources: &SourceStorage,
) -> Option<(Vec<Op>, &'a [Op])> {
    let (start, rest) = ops.firstn()?;
    let (int, not) = match start {
        [int, not] if int.code.is_push_int() && not.code.is_bit_not() => (int, not),
        _ => return None,
    };

    let int_val = !int.code.unwrap_push_int();
    let location = if int.token.location.file_id != not.token.location.file_id {
        not.token.location
    } else {
        int.token.location.merge(not.token.location)
    };
    let lexeme = &sources.source(location.file_id)[location.range()];
    let lexeme = interners.intern_lexeme(lexeme);

    let token = Token {
        kind: TokenKind::Integer(int_val),
        lexeme,
        location,
    };
    let op = Op {
        code: PushInt(int_val),
        token,
        expansions: Vec::new(),
    };

    Some((vec![op], rest))
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
    let lexeme = &sources.source(location.file_id)[location.range()];
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
    let lexeme = &sources.source(location.file_id)[location.range()];
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

///   [Memory(a), PushInt(b), Add/Sub]
/// | [PushInt(a), Memory(b), Add/Sub] -> [Memory(a Add/Sub b)]
fn memory_offset<'a>(
    ops: &'a [Op],
    interners: &mut Interners,
    sources: &SourceStorage,
) -> Option<(Vec<Op>, &'a [Op])> {
    let (start, rest) = ops.firstn()?;
    let (int, mem, op, mem_first) = match start {
        [int, mem, op]
            if int.code.is_push_int()
                && mem.code.is_memory()
                && matches!(op.code, Add | Subtract) =>
        {
            (int, mem, op, false)
        }
        [mem, int, op]
            if mem.code.is_memory()
                && int.code.is_push_int()
                && matches!(op.code, Add | Subtract) =>
        {
            (int, mem, op, true)
        }
        _ => return None,
    };

    let int_val = int.code.unwrap_push_int();
    let (module_id, proc_id, mem_offset, global) = mem.code.unwrap_memory();
    let res = mem_first
        .then(|| op.code.get_binary_op()(mem_offset as u64, int_val))
        .unwrap_or_else(|| op.code.get_binary_op()(int_val, mem_offset as u64));

    let location = if int.token.location.file_id != op.token.location.file_id {
        op.token.location
    } else {
        int.token.location.merge(op.token.location)
    };

    let lexeme = &sources.source(location.file_id)[location.range()];
    let lexeme = interners.intern_lexeme(lexeme);

    let token = Token {
        kind: TokenKind::Memory,
        lexeme,
        location,
    };

    let opt = Op {
        code: Memory {
            module_id,
            proc_id,
            offset: res as _,
            global,
        },
        token,
        expansions: Vec::new(),
    };

    Some((vec![opt], rest))
}
