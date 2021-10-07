use std::collections::{HashMap, HashSet};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    interners::Interners,
    lexer::{Token, TokenKind},
    source_file::{FileId, SourceLocation},
};

use self::optimizer_passes::PASSES;

mod optimizer_passes;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Variantly)]
pub enum OpCode {
    Add,
    BitOr,
    BitAnd,
    DivMod,
    Drop,
    Do { end_ip: usize, condition_ip: usize },
    Dup { depth: usize },
    DupPair,
    End { ip: usize },
    Equal,
    Ident(Spur),
    If { end_ip: usize },
    Include(Spur),
    Else { else_start: usize, end_ip: usize },
    EndIf { ip: usize },
    EndWhile { condition_ip: usize, end_ip: usize },
    Less,
    LessEqual,
    Load,
    Load64,
    Greater,
    GreaterEqual,
    Mem { offset: usize },
    Multiply,
    NotEq,
    Print,
    PushInt(u64),
    PushStr(Spur),
    ShiftLeft,
    ShiftRight,
    Store,
    Store64,
    Subtract,
    Swap,
    SysCall(usize),
    While { ip: usize },
}

impl OpCode {
    pub fn pop_count(self) -> usize {
        match self {
            OpCode::Add
            | OpCode::BitOr
            | OpCode::BitAnd
            | OpCode::DivMod
            | OpCode::Equal
            | OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Multiply
            | OpCode::NotEq
            | OpCode::ShiftLeft
            | OpCode::ShiftRight
            | OpCode::Store
            | OpCode::Store64
            | OpCode::Subtract => 2,

            OpCode::Drop
            | OpCode::Do { .. }
            | OpCode::Print
            | OpCode::If { .. }
            | OpCode::Load
            | OpCode::Load64 => 1,

            OpCode::Dup { depth } => depth + 1,
            OpCode::DupPair
            | OpCode::Else { .. }
            | OpCode::End { .. }
            | OpCode::EndIf { .. }
            | OpCode::EndWhile { .. }
            | OpCode::Ident(_)
            | OpCode::Include(_)
            | OpCode::Mem { .. }
            | OpCode::PushInt(_)
            | OpCode::PushStr(_)
            | OpCode::Swap
            | OpCode::While { .. } => 0,

            OpCode::SysCall(a) => a + 1,
        }
    }

    pub fn push_count(self) -> usize {
        match self {
            OpCode::Dup { depth } => depth + 2,

            OpCode::Add
            | OpCode::BitOr
            | OpCode::BitAnd
            | OpCode::Equal
            | OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Load
            | OpCode::Load64
            | OpCode::Mem { .. }
            | OpCode::Multiply
            | OpCode::NotEq
            | OpCode::PushInt(_)
            | OpCode::ShiftLeft
            | OpCode::ShiftRight
            | OpCode::Subtract
            | OpCode::SysCall(_) => 1,

            OpCode::DivMod | OpCode::DupPair | OpCode::PushStr(_) => 2,

            OpCode::Drop
            | OpCode::Do { .. }
            | OpCode::Print
            | OpCode::End { .. }
            | OpCode::Ident(_)
            | OpCode::If { .. }
            | OpCode::Include(_)
            | OpCode::Else { .. }
            | OpCode::EndIf { .. }
            | OpCode::EndWhile { .. }
            | OpCode::Store
            | OpCode::Store64
            | OpCode::Swap
            | OpCode::While { .. } => 0,
        }
    }

    // Used by the opcode optimizer to detect whether it can optimize Push-Push-Op.
    fn is_binary_op(self) -> bool {
        use OpCode::*;
        match self {
            Add | Subtract | Multiply | BitOr | BitAnd | Equal | Greater | GreaterEqual | Less
            | LessEqual | NotEq | ShiftLeft | ShiftRight => true,

            DivMod
            | Do { .. }
            | Drop
            | Print
            | Dup { .. }
            | DupPair
            | End { .. }
            | Ident(_)
            | If { .. }
            | Include(_)
            | Else { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Load
            | Load64
            | Mem { .. }
            | PushInt(_)
            | PushStr(_)
            | Store
            | Store64
            | Swap
            | SysCall(_)
            | While { .. } => false,
        }
    }

    fn get_binary_op(self) -> fn(u64, u64) -> u64 {
        use OpCode::*;
        match self {
            Add => |a, b| a + b,
            Subtract => |a, b| a - b,
            Multiply => |a, b| a * b,
            BitOr => |a, b| a | b,
            BitAnd => |a, b| a & b,
            ShiftLeft => |a, b| a << b,
            ShiftRight => |a, b| a >> b,
            Equal => |a, b| (a == b) as u64,
            Greater => |a, b| (a > b) as u64,
            GreaterEqual => |a, b| (a >= b) as u64,
            Less => |a, b| (a < b) as u64,
            LessEqual => |a, b| (a <= b) as u64,
            NotEq => |a, b| (a != b) as u64,

            DivMod
            | Do { .. }
            | Drop
            | Print
            | Dup { .. }
            | DupPair
            | End { .. }
            | Ident(_)
            | If { .. }
            | Include { .. }
            | Else { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Load
            | Load64
            | Mem { .. }
            | PushInt(_)
            | PushStr(_)
            | Store
            | Store64
            | Swap
            | SysCall(_)
            | While { .. } => {
                panic!("ICE: Attempted to get the binary_op of a {:?}", self)
            }
        }
    }

    // Used by the compiler optimization passes to detect whether it can optimize further.
    pub fn is_compiler_opt_arithmetic(self) -> bool {
        use OpCode::*;
        match self {
            Add | Subtract | BitOr | BitAnd | ShiftLeft | ShiftRight => true,

            DivMod
            | Do { .. }
            | Drop
            | Print
            | Dup { .. }
            | DupPair
            | End { .. }
            | Equal
            | Ident(_)
            | If { .. }
            | Include(_)
            | Else { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Less
            | LessEqual
            | Load
            | Load64
            | Greater
            | GreaterEqual
            | Mem { .. }
            | Multiply
            | NotEq
            | PushInt(_)
            | PushStr(_)
            | Store
            | Store64
            | Swap
            | SysCall(_)
            | While { .. } => false,
        }
    }

    pub fn is_compare(self) -> bool {
        use OpCode::*;
        match self {
            Equal | Greater | GreaterEqual | Less | LessEqual | NotEq => true,

            Add
            | BitOr
            | BitAnd
            | DivMod
            | Drop
            | Do { .. }
            | Print
            | Dup { .. }
            | DupPair
            | End { .. }
            | Ident(_)
            | If { .. }
            | Include(_)
            | Else { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Load
            | Load64
            | Mem { .. }
            | Multiply
            | PushInt(_)
            | PushStr(_)
            | ShiftLeft
            | ShiftRight
            | Store
            | Store64
            | Subtract
            | Swap
            | SysCall(_)
            | While { .. } => false,
        }
    }

    pub fn unwrap_mem(self) -> usize {
        match self {
            Self::Mem { offset } => offset,
            _ => panic!("expected OpCode::Mem"),
        }
    }

    pub fn unwrap_dup(self) -> usize {
        match self {
            Self::Dup { depth } => depth,
            _ => panic!("expected OpCode::Dup"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Op {
    pub code: OpCode,
    pub token: TokenKind,
    pub location: SourceLocation,
}

impl Op {
    fn new(code: OpCode, token: TokenKind, location: SourceLocation) -> Self {
        Self {
            code,
            token,
            location,
        }
    }
}

fn expect_token<'a>(
    tokens: &mut impl Iterator<Item = (usize, &'a Token)>,
    kind_str: &str,
    expected: fn(TokenKind) -> bool,
    prev: Token,
    interner: &Interners,
) -> Result<(usize, Token), Diagnostic<FileId>> {
    match tokens.next() {
        Some((idx, ident)) if expected(ident.kind) => Ok((idx, *ident)),
        Some((_, ident)) => {
            let diag = Diagnostic::error()
                .with_message(format!(
                    "expected {}, found '{}'",
                    kind_str,
                    interner.resolve_lexeme(ident.lexeme)
                ))
                .with_labels(vec![Label::primary(
                    ident.location.file_id,
                    ident.location.range(),
                )]);

            Err(diag)
        }
        None => {
            let diag = Diagnostic::error()
                .with_message("unexpected end of file")
                .with_labels(vec![Label::primary(
                    prev.location.file_id,
                    prev.location.range(),
                )]);

            Err(diag)
        }
    }
}

fn parse_macro<'a>(
    macros: &mut HashMap<Spur, (Token, Vec<Op>)>,
    token_iter: &mut impl Iterator<Item = (usize, &'a Token)>,
    tokens: &'a [Token],
    keyword: Token,
    interner: &Interners,
    include_list: &mut Vec<(Token, Spur)>,
) -> Result<(Token, Vec<Op>), Vec<Diagnostic<FileId>>> {
    let (ident_idx, ident_token) = match expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        keyword,
        interner,
    ) {
        Ok(a) => a,
        Err(diag) => return Err(vec![diag]),
    };

    let body_start_idx = ident_idx + 1;
    let mut block_depth = 1;
    let mut end_idx = body_start_idx;
    let mut last_token = ident_token;

    // We need to keep track of whether we're in an if or while block, because they
    // should be usable inside a macro block.
    for (idx, token) in token_iter {
        if token.kind.new_block() {
            block_depth += 1;
        } else if token.kind.end_block() {
            block_depth -= 1;
        }

        end_idx = idx;
        last_token = *token;

        if block_depth == 0 {
            break;
        }
    }

    if last_token.kind != TokenKind::End {
        let diag = Diagnostic::error()
            .with_message("unexpected end of file")
            .with_labels(vec![Label::primary(
                last_token.location.file_id,
                last_token.location.range(),
            )]);

        return Err(vec![diag]);
    }

    let body_tokens = &tokens[body_start_idx..end_idx];
    let body_ops = parse_token(macros, body_tokens, interner, include_list)?;

    Ok((ident_token, body_ops))
}

pub fn parse_token(
    macros: &mut HashMap<Spur, (Token, Vec<Op>)>,
    tokens: &[Token],
    interner: &Interners,
    include_list: &mut Vec<(Token, Spur)>,
) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    let mut ops = Vec::new();
    let mut diags = Vec::new();

    let mut token_iter = tokens.iter().enumerate();
    while let Some((_, token)) = token_iter.next() {
        match token.kind {
            TokenKind::Drop => ops.push(Op::new(OpCode::Drop, token.kind, token.location)),
            TokenKind::Print => ops.push(Op::new(OpCode::Print, token.kind, token.location)),
            TokenKind::Dup(depth) => {
                ops.push(Op::new(OpCode::Dup { depth }, token.kind, token.location))
            }
            TokenKind::DupPair => ops.push(Op::new(OpCode::DupPair, token.kind, token.location)),
            TokenKind::Swap => ops.push(Op::new(OpCode::Swap, token.kind, token.location)),

            TokenKind::Mem => ops.push(Op::new(
                OpCode::Mem { offset: 0 },
                token.kind,
                token.location,
            )),
            TokenKind::Load => ops.push(Op::new(OpCode::Load, token.kind, token.location)),
            TokenKind::Load64 => ops.push(Op::new(OpCode::Load64, token.kind, token.location)),
            TokenKind::Store => ops.push(Op::new(OpCode::Store, token.kind, token.location)),
            TokenKind::Store64 => ops.push(Op::new(OpCode::Store64, token.kind, token.location)),

            TokenKind::Equal => ops.push(Op::new(OpCode::Equal, token.kind, token.location)),
            TokenKind::Greater => ops.push(Op::new(OpCode::Greater, token.kind, token.location)),
            TokenKind::GreaterEqual => {
                ops.push(Op::new(OpCode::GreaterEqual, token.kind, token.location))
            }
            TokenKind::Less => ops.push(Op::new(OpCode::Less, token.kind, token.location)),
            TokenKind::LessEqual => {
                ops.push(Op::new(OpCode::LessEqual, token.kind, token.location))
            }
            TokenKind::NotEqual => ops.push(Op::new(OpCode::NotEq, token.kind, token.location)),

            TokenKind::Ident => {
                ops.push(Op::new(
                    OpCode::Ident(token.lexeme),
                    token.kind,
                    token.location,
                ));
            }
            TokenKind::Integer(value) => {
                ops.push(Op::new(OpCode::PushInt(value), token.kind, token.location))
            }
            TokenKind::String(id) => {
                ops.push(Op::new(OpCode::PushStr(id), token.kind, token.location))
            }

            TokenKind::While => ops.push(Op::new(
                OpCode::While { ip: usize::MAX },
                token.kind,
                token.location,
            )),
            TokenKind::Do => ops.push(Op::new(
                OpCode::Do {
                    end_ip: usize::MAX,
                    condition_ip: usize::MAX,
                },
                token.kind,
                token.location,
            )),

            TokenKind::Macro => {
                let (name, body) = match parse_macro(
                    macros,
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    include_list,
                ) {
                    Ok(a) => a,
                    Err(mut e) => {
                        diags.append(&mut e);
                        continue;
                    }
                };

                if let Some((prev_name, _)) = macros.insert(name.lexeme, (name, body)) {
                    let diag = Diagnostic::error()
                        .with_message("macro defined multiple times")
                        .with_labels(vec![
                            Label::primary(name.location.file_id, name.location.range())
                                .with_message("defined here"),
                            Label::secondary(
                                prev_name.location.file_id,
                                prev_name.location.range(),
                            )
                            .with_message("also defined here"),
                        ]);
                    diags.push(diag);
                }
            }
            TokenKind::Include => {
                let (_, path_token) = match expect_token(
                    &mut token_iter,
                    "string",
                    |k| matches!(k, TokenKind::String(_)),
                    *token,
                    interner,
                ) {
                    Ok(ident) => ident,
                    Err(diag) => {
                        diags.push(diag);
                        continue;
                    }
                };

                let literal = match path_token.kind {
                    TokenKind::String(id) => id,
                    _ => unreachable!(),
                };

                include_list.push((path_token, literal));
                ops.push(Op::new(
                    OpCode::Include(literal),
                    token.kind,
                    token.location,
                ));
            }

            TokenKind::If => ops.push(Op::new(
                OpCode::If { end_ip: usize::MAX },
                token.kind,
                token.location,
            )),
            TokenKind::Else => ops.push(Op::new(
                OpCode::Else {
                    else_start: usize::MAX,
                    end_ip: usize::MAX,
                },
                token.kind,
                token.location,
            )),
            TokenKind::End => ops.push(Op::new(
                OpCode::End { ip: usize::MAX },
                token.kind,
                token.location,
            )),

            TokenKind::Minus => ops.push(Op::new(OpCode::Subtract, token.kind, token.location)),
            TokenKind::Plus => ops.push(Op::new(OpCode::Add, token.kind, token.location)),
            TokenKind::Star => ops.push(Op::new(OpCode::Multiply, token.kind, token.location)),
            TokenKind::DivMod => ops.push(Op::new(OpCode::DivMod, token.kind, token.location)),

            TokenKind::BitAnd => ops.push(Op::new(OpCode::BitAnd, token.kind, token.location)),
            TokenKind::BitOr => ops.push(Op::new(OpCode::BitOr, token.kind, token.location)),
            TokenKind::ShiftLeft => {
                ops.push(Op::new(OpCode::ShiftLeft, token.kind, token.location))
            }
            TokenKind::ShiftRight => {
                ops.push(Op::new(OpCode::ShiftRight, token.kind, token.location))
            }

            TokenKind::SysCall(id) => {
                ops.push(Op::new(OpCode::SysCall(id), token.kind, token.location))
            }
        }
    }

    diags.is_empty().then(|| ops).ok_or(diags)
}

pub fn generate_jump_labels(ops: &mut [Op]) -> Result<(), Vec<Diagnostic<FileId>>> {
    let mut jump_ip_stack: Vec<(usize, TokenKind, SourceLocation)> = Vec::new();
    let mut diags = Vec::new();

    for ip in 0..ops.len() {
        let op = ops[ip];
        match op.code {
            OpCode::Do { .. } => {
                let while_ip = match jump_ip_stack.pop() {
                    Some((id, TokenKind::While, _)) => id,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`do` requires a preceeding `while`")
                            .with_labels(vec![Label::primary(
                                op.location.file_id,
                                op.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                jump_ip_stack.push((ip, op.token, op.location));
                match &mut ops[ip].code {
                    OpCode::Do { condition_ip, .. } => *condition_ip = while_ip,
                    _ => unreachable!(),
                }
            }
            OpCode::While { .. } => {
                // Update our own IP.
                match &mut ops[ip].code {
                    OpCode::While { ip: while_ip } => *while_ip = ip,
                    _ => unreachable!(),
                }
                jump_ip_stack.push((ip, op.token, op.location));
            }

            OpCode::If { .. } => jump_ip_stack.push((ip, op.token, op.location)),
            OpCode::Else { .. } => {
                let if_idx = match jump_ip_stack.pop() {
                    Some((if_idx, TokenKind::If, _)) => if_idx,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`else` requires a preceding `if`")
                            .with_labels(vec![Label::primary(
                                op.location.file_id,
                                op.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                // Update our own IP.
                match &mut ops[ip].code {
                    OpCode::Else { else_start, .. } => *else_start = ip,
                    _ => unreachable!(),
                }
                match &mut ops[if_idx].code {
                    OpCode::If { end_ip } => *end_ip = ip,
                    _ => unreachable!(),
                }

                jump_ip_stack.push((ip, op.token, op.location));
            }

            OpCode::End { .. } => {
                let src_ip = match jump_ip_stack.pop() {
                    Some((id, TokenKind::If | TokenKind::Else | TokenKind::Do, _)) => id,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`end` requires a preceding `if`, `else`, or `while-do`")
                            .with_labels(vec![Label::primary(
                                op.location.file_id,
                                op.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                match &mut ops[src_ip].code {
                    OpCode::Do {
                        end_ip,
                        condition_ip,
                    } => {
                        *end_ip = ip;
                        let while_ip = *condition_ip;
                        ops[ip].code = OpCode::EndWhile {
                            condition_ip: while_ip,
                            end_ip: ip,
                        };
                    }
                    OpCode::If { end_ip } | OpCode::Else { end_ip, .. } => {
                        *end_ip = ip;
                        ops[ip].code = OpCode::EndIf { ip };
                    }
                    _ => unreachable!(),
                }
            }

            _ => {}
        }
    }

    while let Some((_, _, loc)) = jump_ip_stack.pop() {
        let diag = Diagnostic::error()
            .with_message("unclosed `if`, `else`, or `while-do` block")
            .with_labels(vec![Label::primary(loc.file_id, loc.range())]);
        diags.push(diag);
    }

    diags.is_empty().then(|| ()).ok_or(diags)
}

pub fn optimize(ops: &[Op]) -> Vec<Op> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec: Vec<Op> = Vec::with_capacity(ops.len());

    // Keep making passes until we get no changes.
    loop {
        let mut src = src_vec.as_slice();
        let mut changed = false;

        while !src.is_empty() {
            if let Some((ops, xs)) = PASSES.iter().filter_map(|pass| pass(src)).next() {
                dst_vec.extend(ops);
                src = xs;
                changed = true;
            } else if let [op, xs @ ..] = src {
                dst_vec.push(*op);
                src = xs;
            }
        }

        if !changed {
            break;
        }

        src_vec.clear();
        std::mem::swap(&mut src_vec, &mut dst_vec);
    }

    dst_vec
}

pub fn expand_includes(included_files: &HashMap<Spur, Vec<Op>>, ops: &[Op]) -> Vec<Op> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec = Vec::with_capacity(ops.len());
    let mut already_included = HashSet::new();

    loop {
        let mut changed = false;

        for op in src_vec.drain(..) {
            match op.code {
                OpCode::Include(id) => {
                    changed = true;
                    if !already_included.contains(&id) {
                        dst_vec.extend_from_slice(&included_files[&id]);
                        already_included.insert(id);
                    }
                }
                _ => dst_vec.push(op),
            }
        }

        if !changed {
            break;
        }

        std::mem::swap(&mut src_vec, &mut dst_vec);
    }

    dst_vec
}

pub fn expand_macros(
    macros: &HashMap<Spur, (Token, Vec<Op>)>,
    ops: &[Op],
) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec = Vec::with_capacity(ops.len());
    let mut diags = Vec::new();

    // Keep making changes until we get no changes.
    let mut num_expansions = 0;
    let mut last_changed_macros = Vec::new();
    loop {
        let mut changed = false;
        last_changed_macros.clear();

        for op in src_vec.drain(..) {
            match op.code {
                OpCode::Ident(id) => {
                    changed = true;
                    match macros.get(&id) {
                        Some((name, body)) => {
                            last_changed_macros.push(*name);
                            dst_vec.extend_from_slice(body);
                        }
                        None => {
                            let diag = Diagnostic::error()
                                .with_message("unknown macro")
                                .with_labels(vec![Label::primary(
                                    op.location.file_id,
                                    op.location.range(),
                                )]);
                            diags.push(diag);
                        }
                    }
                }
                _ => dst_vec.push(op),
            }
        }

        if !changed {
            break;
        }

        if num_expansions > 128 {
            let mut labels = Vec::new();

            for mac in last_changed_macros {
                labels.push(Label::primary(mac.location.file_id, mac.location.range()));
            }

            let diag = Diagnostic::error()
                .with_message("depth of macro expansion exceeded 128")
                .with_labels(labels);

            diags.push(diag);
            break;
        }

        num_expansions += 1;

        std::mem::swap(&mut src_vec, &mut dst_vec);
    }

    diags.is_empty().then(|| dst_vec).ok_or(diags)
}
