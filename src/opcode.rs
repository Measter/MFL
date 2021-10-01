use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
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
    Equal,
    If { end_ip: usize, had_else: bool },
    Else { else_start: usize, end_ip: usize },
    EndIf { ip: usize },
    EndWhile { condition_ip: usize, end_ip: usize },
    Less,
    Load,
    Greater,
    Mem,
    Push(u64),
    ShiftLeft,
    ShiftRight,
    Store,
    Subtract,
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
    let mut block_kind_stack = Vec::new();
    let mut diags = Vec::new();

    for token in tokens {
        match token.kind {
            TokenKind::Drop => ops.push(Op::new(OpCode::Drop, token.kind, token.location)),
            TokenKind::Dump => ops.push(Op::new(OpCode::Dump, token.kind, token.location)),
            TokenKind::Dup => ops.push(Op::new(OpCode::Dup, token.kind, token.location)),
            TokenKind::DupPair => ops.push(Op::new(OpCode::DupPair, token.kind, token.location)),
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

            TokenKind::While => {
                let ip = ops.len();
                block_kind_stack.push((ip, token.kind));
                ops.push(Op::new(OpCode::While { ip }, token.kind, token.location));
            }
            TokenKind::Do => {
                match block_kind_stack.pop() {
                    Some((_, TokenKind::While)) => {}
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`do` requires a preceeding `while`")
                            .with_labels(vec![Label::primary(
                                token.location.file_id,
                                token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                block_kind_stack.push((ops.len(), token.kind));
                ops.push(Op::new(
                    OpCode::Do {
                        end_ip: usize::MAX,
                        condition_ip: usize::MAX,
                    },
                    token.kind,
                    token.location,
                ));
            }

            TokenKind::If => {
                block_kind_stack.push((ops.len(), token.kind));
                ops.push(Op::new(
                    OpCode::If {
                        end_ip: usize::MAX,
                        had_else: false,
                    },
                    token.kind,
                    token.location,
                ));
            }
            TokenKind::Else => {
                match block_kind_stack.pop() {
                    Some((_, TokenKind::If)) => {}
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`else` requires a preceding `if`")
                            .with_labels(vec![Label::primary(
                                token.location.file_id,
                                token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                }

                let ip = ops.len();
                block_kind_stack.push((ip, token.kind));
                ops.push(Op::new(
                    OpCode::Else {
                        else_start: ip,
                        end_ip: usize::MAX,
                    },
                    token.kind,
                    token.location,
                ));
            }
            TokenKind::End => {
                let dest_idx = match block_kind_stack.pop() {
                    Some((id, TokenKind::If | TokenKind::Else | TokenKind::Do)) => id,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`end` requires a preceding `if`, `else`, or `while-do`")
                            .with_labels(vec![Label::primary(
                                token.location.file_id,
                                token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                let ip = ops.len();
                match &mut ops[dest_idx].code {
                    OpCode::If { .. } | OpCode::Else { .. } => {
                        ops.push(Op::new(OpCode::EndIf { ip }, token.kind, token.location));
                    }
                    OpCode::Do { .. } => {
                        ops.push(Op::new(
                            OpCode::EndWhile {
                                condition_ip: usize::MAX,
                                end_ip: ip,
                            },
                            token.kind,
                            token.location,
                        ));
                    }
                    _ => unreachable!(),
                }
            }

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
            OpCode::EndWhile { .. } => {
                let do_ip = match jump_ip_stack.pop() {
                    Some((id, TokenKind::Do, _)) => id,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`end` requires a preceeding `while-do`")
                            .with_labels(vec![Label::primary(
                                op.location.file_id,
                                op.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                let while_ip = match &mut ops[do_ip].code {
                    OpCode::Do {
                        condition_ip,
                        end_ip,
                        ..
                    } => {
                        *end_ip = ip;
                        *condition_ip
                    }
                    _ => unreachable!(),
                };

                match &mut ops[ip].code {
                    OpCode::EndWhile { condition_ip, .. } => *condition_ip = while_ip,
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

                match &mut ops[if_idx] {
                    Op {
                        code: OpCode::If { end_ip, had_else },
                        ..
                    } => {
                        *end_ip = else_start;
                        *had_else = true;
                    }
                    _ => unreachable!(),
                }

                jump_ip_stack.push((ip, op.token, op.location));
            }
            OpCode::EndIf { ip } => {
                let if_else_idx = match jump_ip_stack.pop() {
                    Some((id, TokenKind::If | TokenKind::Else, _)) => id,
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

                match &mut ops[if_else_idx].code {
                    OpCode::If { end_ip, .. } | OpCode::Else { end_ip, .. } => {
                        *end_ip = ip;
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
