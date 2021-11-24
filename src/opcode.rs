use std::{
    collections::{HashMap, HashSet},
    ops::Not,
};

use ariadne::{Color, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    program::{ModuleId, Procedure, ProcedureId, ProcedureKind},
    source_file::{SourceLocation, SourceStorage},
    type_check::PorthTypeKind,
    Module, Width,
};

use self::optimizer_passes::PASSES;

mod optimizer_passes;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Variantly)]
pub enum OpCode {
    Add,
    ArgC,
    ArgV,
    BitAnd,
    BitNot,
    BitOr,
    CallProc(ProcedureId),
    CastBool,
    CastInt,
    CastPtr,
    DivMod,
    Do,
    DoIf {
        end_ip: usize,
    },
    DoWhile {
        end_ip: usize,
        condition_ip: usize,
    },
    Dup {
        depth: usize,
    },
    DupPair,
    Drop,
    Elif {
        else_start: usize,
        end_ip: usize,
    },
    Else {
        else_start: usize,
        end_ip: usize,
    },
    End,
    EndIf {
        ip: usize,
    },
    EndWhile {
        condition_ip: usize,
        end_ip: usize,
    },
    Epilogue,
    Equal,
    If,
    Include(Spur),
    Less,
    LessEqual,
    Load(Width),
    Greater,
    GreaterEqual,
    Memory {
        name: Spur,
        offset: usize,
        global: bool,
    },
    Multiply,
    NotEq,
    Prologue,
    PushBool(bool),
    PushInt(u64),
    PushStr {
        id: Spur,
        is_c_str: bool,
    },
    ResolvedIdent {
        module: ModuleId,
        proc_id: ProcedureId,
    },
    Return,
    Rot,
    ShiftLeft,
    ShiftRight,
    Store(Width),
    Subtract,
    Swap,
    SysCall(usize),
    UnresolvedIdent {
        token: Token,
        sub_token: Option<Token>,
    },
    While {
        ip: usize,
    },
}

impl OpCode {
    pub fn pop_count(self) -> usize {
        match self {
            OpCode::Rot => 3,

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
            | OpCode::Store(_)
            | OpCode::Swap
            | OpCode::Subtract => 2,

            OpCode::BitNot
            | OpCode::CastBool
            | OpCode::CastInt
            | OpCode::CastPtr
            | OpCode::Do
            | OpCode::DoIf { .. }
            | OpCode::DoWhile { .. }
            | OpCode::Drop
            | OpCode::Load(_) => 1,

            OpCode::Dup { depth } => depth + 1,

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::DupPair
            | OpCode::Elif { .. }
            | OpCode::Else { .. }
            | OpCode::End { .. }
            | OpCode::EndIf { .. }
            | OpCode::EndWhile { .. }
            | OpCode::UnresolvedIdent(_)
            | OpCode::If
            | OpCode::Include(_)
            | OpCode::Memory { .. }
            | OpCode::PushBool(_)
            | OpCode::PushInt(_)
            | OpCode::PushStr { .. }
            | OpCode::While { .. } => 0,

            OpCode::CallProc(_) | OpCode::Return | OpCode::Prologue | OpCode::Epilogue => todo!(),

            OpCode::SysCall(a) => a + 1,
        }
    }

    pub fn is_const(self) -> bool {
        match self {
            OpCode::Add
            | OpCode::BitAnd
            | OpCode::BitNot
            | OpCode::BitOr
            | OpCode::CastBool
            | OpCode::CastInt
            | OpCode::CastPtr
            | OpCode::DivMod
            | OpCode::Do
            | OpCode::DoIf { .. }
            | OpCode::DoWhile { .. }
            | OpCode::Dup { .. }
            | OpCode::DupPair
            | OpCode::Drop
            | OpCode::Elif { .. }
            | OpCode::Else { .. }
            | OpCode::End
            | OpCode::EndIf { .. }
            | OpCode::EndWhile { .. }
            | OpCode::Epilogue
            | OpCode::Equal
            | OpCode::UnresolvedIdent(_)
            | OpCode::If
            | OpCode::Include(_)
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Multiply
            | OpCode::NotEq
            | OpCode::Prologue
            | OpCode::PushBool(_)
            | OpCode::PushInt(_)
            | OpCode::PushStr { .. }
            | OpCode::Return
            | OpCode::Rot
            | OpCode::ShiftLeft
            | OpCode::ShiftRight
            | OpCode::Subtract
            | OpCode::Swap
            | OpCode::While { .. } => true,

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::CallProc(_)
            | OpCode::Load(_)
            | OpCode::Memory { .. }
            | OpCode::Store(_)
            | OpCode::SysCall(_) => false,
        }
    }

    // Used by the opcode optimizer to detect whether it can optimize Push-Push-Op.
    fn is_binary_op(self) -> bool {
        use OpCode::*;
        match self {
            Add | BitAnd | BitOr | Equal | Greater | GreaterEqual | Less | LessEqual | Multiply
            | NotEq | ShiftLeft | ShiftRight | Subtract => true,

            ArgC
            | ArgV
            | BitNot
            | CallProc(_)
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | DoWhile { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Epilogue
            | UnresolvedIdent(_)
            | If
            | Include(_)
            | Load(_)
            | Memory { .. }
            | Prologue
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | Return
            | Rot
            | Store(_)
            | Swap
            | SysCall(_)
            | While { .. } => false,
        }
    }

    fn is_boolean_op(self) -> bool {
        use OpCode::*;
        match self {
            Equal | Greater | GreaterEqual | Less | LessEqual | NotEq => true,

            Add
            | ArgC
            | ArgV
            | BitAnd
            | BitNot
            | BitOr
            | CallProc(_)
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | DoWhile { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Epilogue
            | UnresolvedIdent(_)
            | If
            | Include(_)
            | Load(_)
            | Memory { .. }
            | Multiply
            | Prologue
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | Return
            | Rot
            | ShiftLeft
            | ShiftRight
            | Store(_)
            | Subtract
            | Swap
            | SysCall(_)
            | While { .. } => false,
        }
    }

    fn get_binary_op(self) -> fn(u64, u64) -> u64 {
        use OpCode::*;
        match self {
            Add => |a, b| a + b,
            BitOr => |a, b| a | b,
            BitAnd => |a, b| a & b,
            Equal => |a, b| (a == b) as u64,
            Greater => |a, b| (a > b) as u64,
            GreaterEqual => |a, b| (a >= b) as u64,
            Less => |a, b| (a < b) as u64,
            LessEqual => |a, b| (a <= b) as u64,
            Multiply => |a, b| a * b,
            NotEq => |a, b| (a != b) as u64,
            ShiftLeft => |a, b| a << b,
            ShiftRight => |a, b| a >> b,
            Subtract => |a, b| a - b,

            ArgC
            | ArgV
            | BitNot
            | CallProc(_)
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | DoWhile { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Epilogue
            | UnresolvedIdent(_)
            | If
            | Include { .. }
            | Load(_)
            | Memory { .. }
            | Prologue
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | Return
            | Rot
            | Store(_)
            | Swap
            | SysCall(_)
            | While { .. } => {
                panic!("ICE: Attempted to get the binary_op of a {:?}", self)
            }
        }
    }

    pub fn unwrap_memory(self) -> (Spur, usize, bool) {
        match self {
            Self::Memory {
                name,
                offset,
                global,
            } => (name, offset, global),
            _ => panic!("expected OpCode::Memory"),
        }
    }

    pub fn unwrap_dup(self) -> usize {
        match self {
            OpCode::Dup { depth } => depth,
            _ => panic!("expected OpCode::Dup"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Op {
    pub code: OpCode,
    pub token: Token,
    pub expansions: Vec<SourceLocation>,
}

impl Op {
    pub fn new(code: OpCode, token: Token) -> Self {
        Self {
            code,
            token,
            expansions: Vec::new(),
        }
    }
}

struct JumpIpStack {
    ip: usize,
    kind: TokenKind,
    location: SourceLocation,
}

pub fn generate_jump_labels(ops: &mut [Op], source_store: &SourceStorage) -> Result<(), ()> {
    let mut jump_ip_stack: Vec<JumpIpStack> = Vec::new();
    // Stores the IPs of the Elif opcodes so we can update their end IPs when we encounter an End opcode.
    let mut if_blocks_stack_ips: Vec<Vec<usize>> = Vec::new();
    let mut had_error = false;

    for ip in 0..ops.len() {
        let op = &ops[ip];
        match op.code {
            OpCode::While { .. } => {
                jump_ip_stack.push(JumpIpStack {
                    ip,
                    kind: op.token.kind,
                    location: op.token.location,
                });
                // Update our own IP.
                match &mut ops[ip].code {
                    OpCode::While { ip: while_ip } => *while_ip = ip,
                    _ => unreachable!(),
                }
            }

            OpCode::If => {
                if_blocks_stack_ips.push(Vec::new());
                jump_ip_stack.push(JumpIpStack {
                    ip,
                    kind: op.token.kind,
                    location: op.token.location,
                })
            }
            OpCode::Elif { .. } => {
                let if_idx = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip: if_idx,
                        kind: TokenKind::Do,
                        ..
                    }) => if_idx,
                    _ => {
                        diagnostics::emit(
                            op.token.location,
                            "`elif` requires a preceding `if-do`",
                            Some(Label::new(op.token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        had_error = true;
                        continue;
                    }
                };

                let kind = op.token.kind;
                let location = op.token.location;

                // update our own IP.
                match &mut ops[ip].code {
                    OpCode::Elif { else_start, .. } => *else_start = ip,
                    _ => unreachable!(),
                };
                match &mut ops[if_idx].code {
                    OpCode::DoIf { end_ip } => *end_ip = ip,
                    OpCode::DoWhile { .. } => {
                        let while_token = &ops[if_idx].token;

                        diagnostics::emit(
                            location,
                            "`elif` can only be used with `if` blocks",
                            [
                                Label::new(location).with_color(Color::Red),
                                Label::new(while_token.location)
                                    .with_color(Color::Blue)
                                    .with_message("opened here"),
                            ],
                            None,
                            source_store,
                        );
                        had_error = true;
                        continue;
                    }
                    _ => unreachable!(),
                };

                if_blocks_stack_ips.last_mut().unwrap().push(ip);
                jump_ip_stack.push(JumpIpStack { ip, kind, location });
            }
            OpCode::Else { .. } => {
                let if_idx = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip: if_idx,
                        kind: TokenKind::Do,
                        ..
                    }) => if_idx,
                    _ => {
                        diagnostics::emit(
                            op.token.location,
                            "`else` requires a preceding `if-do`",
                            Some(Label::new(op.token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        had_error = true;
                        continue;
                    }
                };

                let kind = op.token.kind;
                let location = op.token.location;

                // Update our own IP.
                match &mut ops[ip].code {
                    OpCode::Else { else_start, .. } => *else_start = ip,
                    _ => unreachable!(),
                }
                match &mut ops[if_idx].code {
                    OpCode::DoIf { end_ip } => *end_ip = ip,
                    _ => unreachable!(),
                }

                jump_ip_stack.push(JumpIpStack { ip, kind, location });
            }

            OpCode::Do => {
                let src_ip = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip,
                        kind: TokenKind::Elif | TokenKind::If | TokenKind::While,
                        ..
                    }) => ip,
                    _ => {
                        diagnostics::emit(
                            op.token.location,
                            "`do` requires a preceding `if`, `elif` or `while`",
                            Some(Label::new(op.token.location)),
                            None,
                            source_store,
                        );
                        had_error = true;
                        continue;
                    }
                };

                jump_ip_stack.push(JumpIpStack {
                    ip,
                    kind: op.token.kind,
                    location: op.token.location,
                });

                // Now we need to specialize our own type based on our source.
                match &mut ops[src_ip].code {
                    OpCode::While { ip: condition_ip } => {
                        ops[ip].code = OpCode::DoWhile {
                            end_ip: usize::MAX,
                            condition_ip: *condition_ip,
                        };
                    }
                    OpCode::Elif { .. } | OpCode::If => {
                        ops[ip].code = OpCode::DoIf { end_ip: usize::MAX }
                    }
                    _ => unreachable!(),
                }
            }

            OpCode::End { .. } => {
                let src_ip = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip,
                        kind: TokenKind::Else | TokenKind::Do,
                        ..
                    }) => ip,
                    _ => {
                        diagnostics::emit(
                            op.token.location,
                            "`end` requires a preceding `if-do`, `else`, or `while-do`",
                            Some(Label::new(op.token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        had_error = true;
                        continue;
                    }
                };

                // Now we need to specialize our own type based on our source.
                match &mut ops[src_ip].code {
                    OpCode::DoWhile {
                        end_ip,
                        condition_ip,
                    } => {
                        *end_ip = ip;
                        ops[ip].code = OpCode::EndWhile {
                            condition_ip: *condition_ip,
                            end_ip: ip,
                        };
                    }
                    OpCode::DoIf { end_ip } | OpCode::Else { end_ip, .. } => {
                        *end_ip = ip;
                        ops[ip].code = OpCode::EndIf { ip };

                        // Update any Elifs in the block.
                        for elif_ip in if_blocks_stack_ips.pop().unwrap() {
                            match &mut ops[elif_ip].code {
                                OpCode::Elif { end_ip, .. } => *end_ip = ip,
                                _ => unreachable!(),
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            }

            _ => {}
        }
    }

    while let Some(JumpIpStack { location, .. }) = jump_ip_stack.pop() {
        diagnostics::emit(
            location,
            "unclosed `if`, `else`, or `while-do` block",
            Some(Label::new(location).with_color(Color::Red)),
            None,
            source_store,
        );
        had_error = true;
    }

    had_error.not().then(|| ()).ok_or(())
}

pub fn optimize(ops: &[Op], interner: &mut Interners, sources: &SourceStorage) -> Vec<Op> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec: Vec<Op> = Vec::with_capacity(ops.len());

    // Keep making passes until we get no changes.
    loop {
        let mut src = src_vec.as_slice();
        let mut changed = false;

        while !src.is_empty() {
            if let Some((ops, xs)) = PASSES
                .iter()
                .filter_map(|pass| pass(src, interner, sources))
                .next()
            {
                dst_vec.extend(ops);
                src = xs;
                changed = true;
            } else if let [op, xs @ ..] = src {
                dst_vec.push(op.clone());
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

pub fn expand_sub_blocks(
    program: &Module,
    interner: &Interners,
    proc: &Procedure,
    source_store: &SourceStorage,
) -> Result<(Vec<Op>, bool), ()> {
    let mut src_vec = proc.body().to_owned();
    let mut dst_vec = Vec::with_capacity(src_vec.len());
    let mut had_error = false;

    // Keep making changes until we get no changes.
    let mut num_expansions = 0;
    let mut last_changed_macros = Vec::new();
    let mut failed_const_expansion = false;
    loop {
        let mut expanded_macro = false;
        last_changed_macros.clear();

        for op in src_vec.drain(..) {
            let ident_id = match op.code {
                OpCode::UnresolvedIdent(id) => id,
                _ => {
                    dst_vec.push(op);
                    continue;
                }
            };

            let found_proc_id = match proc.get_visible_symbol(ident_id) {
                Some(id) => id,
                None => {
                    diagnostics::emit(
                        op.token.location,
                        format!("unknown symbol `{}`", interner.resolve_lexeme(ident_id)),
                        Some(Label::new(op.token.location).with_color(Color::Red)),
                        None,
                        source_store,
                    );
                    had_error = true;
                    continue;
                }
            };

            let found_proc = if found_proc_id == proc.id() {
                proc
            } else {
                program.get_proc(found_proc_id)
            };

            match found_proc.kind() {
                ProcedureKind::Macro => {
                    expanded_macro = true;
                    last_changed_macros.push(found_proc.name());
                    dst_vec.extend(found_proc.body().iter().map(|new_op| {
                        let mut new_op = new_op.clone();
                        new_op.expansions.push(op.token.location);
                        new_op.expansions.extend_from_slice(&op.expansions);
                        new_op
                    }));
                }
                ProcedureKind::Const { const_val: None } => {
                    failed_const_expansion = true;
                    dst_vec.push(op);
                }
                ProcedureKind::Const {
                    const_val: Some(vals),
                } => {
                    for (kind, val) in vals {
                        let code = match kind {
                            PorthTypeKind::Int => OpCode::PushInt(*val),
                            PorthTypeKind::Bool => OpCode::PushBool(*val != 0),
                            PorthTypeKind::Ptr => panic!("ICE: Const pointers not supported"),
                            PorthTypeKind::Unknown => panic!("ICE: Unknown const type"),
                        };
                        dst_vec.push(Op {
                            code,
                            token: op.token,
                            expansions: op.expansions.clone(),
                        });
                    }
                }

                ProcedureKind::Memory => {
                    dst_vec.push(Op {
                        code: OpCode::Memory {
                            name: ident_id,
                            offset: 0,
                            global: found_proc.parent().is_none(),
                        },
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
                ProcedureKind::Proc(_) => {
                    dst_vec.push(Op {
                        code: OpCode::CallProc(found_proc_id),
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
            }
        }

        if !expanded_macro {
            break;
        }

        if num_expansions > 128 {
            let mut labels = Vec::new();

            let first_loc = last_changed_macros[0];
            for mac in last_changed_macros {
                labels.push(Label::new(mac.location).with_color(Color::Red));
            }

            diagnostics::emit(
                first_loc.location,
                "depth of macro expansion exceeded 128",
                labels,
                None,
                source_store,
            );
            had_error = true;
            break;
        }

        num_expansions += 1;

        std::mem::swap(&mut src_vec, &mut dst_vec);
    }

    had_error
        .not()
        .then(|| (dst_vec, failed_const_expansion))
        .ok_or(())
}
