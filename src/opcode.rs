use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
    generate_error,
    lexer::{Token, TokenKind},
    source_file::{FileId, SourceLocation},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    Add,
    BitOr,
    BitAnd,
    Drop,
    Do { end_ip: usize, condition_ip: usize },
    Dump,
    Dup,
    DupPair,
    End { ip: usize },
    Equal,
    If { end_ip: usize },
    Else { else_start: usize, end_ip: usize },
    EndIf { ip: usize },
    EndWhile { condition_ip: usize, end_ip: usize },
    Less,
    Load,
    Greater,
    Mem,
    Over,
    Push(u64),
    ShiftLeft,
    ShiftRight,
    Store,
    Subtract,
    Swap,
    SysCall(usize),
    While { ip: usize },
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

pub fn parse_token(tokens: &[Token<'_>]) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    let mut ops = Vec::new();
    let mut diags = Vec::new();

    for token in tokens {
        match token.kind {
            TokenKind::Drop => ops.push(Op::new(OpCode::Drop, token.kind, token.location)),
            TokenKind::Dump => ops.push(Op::new(OpCode::Dump, token.kind, token.location)),
            TokenKind::Dup => ops.push(Op::new(OpCode::Dup, token.kind, token.location)),
            TokenKind::DupPair => ops.push(Op::new(OpCode::DupPair, token.kind, token.location)),
            TokenKind::Over => ops.push(Op::new(OpCode::Over, token.kind, token.location)),
            TokenKind::Swap => ops.push(Op::new(OpCode::Swap, token.kind, token.location)),

            TokenKind::Mem => ops.push(Op::new(OpCode::Mem, token.kind, token.location)),
            TokenKind::Load => ops.push(Op::new(OpCode::Load, token.kind, token.location)),
            TokenKind::Store => ops.push(Op::new(OpCode::Store, token.kind, token.location)),

            TokenKind::Equal => ops.push(Op::new(OpCode::Equal, token.kind, token.location)),
            TokenKind::Greater => ops.push(Op::new(OpCode::Greater, token.kind, token.location)),
            TokenKind::Less => ops.push(Op::new(OpCode::Less, token.kind, token.location)),

            TokenKind::Ident => {
                let num = match token.lexeme.parse() {
                    Ok(num) => num,
                    Err(_) => {
                        let diag = Diagnostic::error()
                            .with_message("invalid number")
                            .with_labels(vec![Label::primary(
                                token.location.file_id,
                                token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                ops.push(Op::new(OpCode::Push(num), token.kind, token.location));
            }

            TokenKind::While => ops.push(Op::new(
                OpCode::While { ip: ops.len() },
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

            TokenKind::If => ops.push(Op::new(
                OpCode::If { end_ip: usize::MAX },
                token.kind,
                token.location,
            )),
            TokenKind::Else => ops.push(Op::new(
                OpCode::Else {
                    else_start: ops.len(),
                    end_ip: usize::MAX,
                },
                token.kind,
                token.location,
            )),
            TokenKind::End => ops.push(Op::new(
                OpCode::End { ip: ops.len() },
                token.kind,
                token.location,
            )),

            TokenKind::Minus => ops.push(Op::new(OpCode::Subtract, token.kind, token.location)),
            TokenKind::Plus => ops.push(Op::new(OpCode::Add, token.kind, token.location)),

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
            OpCode::While { .. } => jump_ip_stack.push((ip, op.token, op.location)),

            OpCode::If { .. } => jump_ip_stack.push((ip, op.token, op.location)),
            OpCode::Else { else_start, .. } => {
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

                match &mut ops[if_idx].code {
                    OpCode::If { end_ip } => *end_ip = else_start,
                    _ => unreachable!(),
                }

                jump_ip_stack.push((ip, op.token, op.location));
            }

            OpCode::End { ip } => {
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

pub fn check_stack(ops: &[Op]) -> Result<(), Vec<Diagnostic<FileId>>> {
    let mut stack_depth = 0;
    let mut diags = Vec::new();

    for op in ops {
        match op.code {
            OpCode::Add
            | OpCode::Subtract
            | OpCode::BitOr
            | OpCode::BitAnd
            | OpCode::ShiftLeft
            | OpCode::ShiftRight
            | OpCode::Equal
            | OpCode::Less
            | OpCode::Greater => {
                if stack_depth < 2 {
                    diags.push(generate_error(
                        format!("2 operands expected, found {}", stack_depth),
                        op.location,
                    ));
                    stack_depth = 1;
                } else {
                    stack_depth -= 1;
                }
            }

            OpCode::Push(_) | OpCode::Mem => stack_depth += 1,
            OpCode::Dup | OpCode::Over => {
                if stack_depth < 1 {
                    diags.push(generate_error(
                        format!("1 operands expected, found {}", stack_depth),
                        op.location,
                    ));
                    stack_depth = 1;
                } else {
                    stack_depth += 1;
                }
            }
            OpCode::DupPair => {
                if stack_depth < 2 {
                    diags.push(generate_error(
                        format!("2 operands expected, found {}", stack_depth),
                        op.location,
                    ));
                    stack_depth = 2;
                } else {
                    stack_depth += 2;
                }
            }

            OpCode::Drop | OpCode::Dump | OpCode::Do { .. } | OpCode::If { .. } => {
                if stack_depth < 1 {
                    diags.push(generate_error(
                        format!("1 operands expected, found {}", stack_depth),
                        op.location,
                    ));
                } else {
                    stack_depth -= 1;
                }
            }

            OpCode::Load => {
                if stack_depth < 1 {
                    diags.push(generate_error(
                        format!("1 operands expected, found {}", stack_depth),
                        op.location,
                    ));
                    stack_depth = 1;
                }
            }
            OpCode::Store => {
                if stack_depth < 2 {
                    diags.push(generate_error(
                        format!("2 operands expected, found {}", stack_depth),
                        op.location,
                    ));
                    stack_depth = 0;
                }
            }

            OpCode::SysCall(a @ 0..=6) => {
                if stack_depth < a + 1 {
                    diags.push(generate_error(
                        format!("{} operands expected, found {}", a + 1, stack_depth),
                        op.location,
                    ));
                    stack_depth = 0;
                }
            }
            OpCode::SysCall(a) => {
                diags.push(generate_error(
                    format!("invalid syscall({})", a),
                    op.location,
                ));
                stack_depth = 0;
            }

            OpCode::Else { .. }
            | OpCode::End { .. }
            | OpCode::EndIf { .. }
            | OpCode::EndWhile { .. }
            | OpCode::Swap
            | OpCode::While { .. } => {}
        }
    }

    diags.is_empty().then(|| ()).ok_or(diags)
}
