use std::{
    collections::HashMap,
    fmt::{self, Write},
    ops::Not,
};

use ariadne::{Color, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    n_ops::{NOps, PopN},
    opcode::{Op, OpCode},
    program::{Procedure, Program},
    source_file::{SourceLocation, SourceStorage},
};

use super::ProcedureId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Variantly)]
pub enum PtrId {
    Mem(ProcedureId),
    Str(Spur),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Variantly)]
pub enum ConstVal {
    Int(u64),
    Bool(bool),
    Ptr {
        id: PtrId,
        source_op_location: SourceLocation,
        offset: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PorthTypeKind {
    Int,
    Ptr,
    Bool,
    Unknown,
}

impl fmt::Display for PorthTypeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PorthTypeKind::Int => "Int".fmt(f),
            PorthTypeKind::Ptr => "Ptr".fmt(f),
            PorthTypeKind::Bool => "Bool".fmt(f),
            PorthTypeKind::Unknown => "Unknown".fmt(f),
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct ValueId(usize);

#[derive(Debug)]
struct Value {
    value_id: ValueId,
    creator_op_idx: usize,
    creator_token: Token,
    porth_type: PorthTypeKind,
    const_val: Option<ConstVal>,
    users: Vec<usize>,
    consumer: Option<usize>,
}

#[derive(Debug, Default)]
struct Analyzer {
    values: HashMap<ValueId, Value>,
    current_id: usize,
}

impl Analyzer {
    fn new_value(
        &mut self,
        porth_type: PorthTypeKind,
        creator_idx: usize,
        creator_token: Token,
    ) -> (ValueId, &mut Value) {
        let id = ValueId(self.current_id);
        self.current_id += 1;
        (
            id,
            self.values.entry(id).or_insert(Value {
                value_id: id,
                creator_op_idx: creator_idx,
                creator_token,
                porth_type,
                const_val: None,
                users: Vec::new(),
                consumer: None,
            }),
        )
    }

    fn get_values<const N: usize>(&self, ids: [ValueId; N]) -> [&Value; N] {
        ids.map(|id| &self.values[&id])
    }
}

fn generate_type_mismatch_diag(
    source_store: &SourceStorage,
    operator_str: &str,
    op: &Op,
    types: &[&Value],
) {
    let mut message = format!("cannot use `{}` on ", operator_str);
    match types {
        [] => unreachable!(),
        [a] => write!(&mut message, "`{}`", a.porth_type).unwrap(),
        [a, b] => write!(&mut message, "`{}` and `{}`", a.porth_type, b.porth_type).unwrap(),
        [xs @ .., last] => {
            for x in xs {
                write!(&mut message, "`{}`, ", x.porth_type).unwrap();
            }

            write!(&mut message, "and `{}`", last.porth_type).unwrap();
        }
    }

    let mut labels = vec![Label::new(op.token.location)
        .with_color(Color::Red)
        .with_message(" ")];

    for source in op.expansions.iter() {
        labels.push(
            Label::new(*source)
                .with_color(Color::Blue)
                .with_message("expanded from here"),
        );
    }

    for (value, order) in types.iter().rev().zip(1..) {
        labels.push(
            Label::new(value.creator_token.location)
                .with_color(Color::Yellow)
                .with_message(format!("{}", value.porth_type))
                .with_order(order),
        )
    }

    diagnostics::emit(op.token.location, message, labels, None, source_store);
}

fn generate_stack_exhaustion_diag(
    source_store: &SourceStorage,
    op: &Op,
    actual: usize,
    expected: usize,
) {
    let message = format!("expected {} items, found {}", expected, actual);

    let mut labels = vec![Label::new(op.token.location)
        .with_color(Color::Red)
        .with_message("here")];

    for source in op.expansions.iter() {
        labels.push(
            Label::new(*source)
                .with_color(Color::Blue)
                .with_message("expanded from here"),
        );
    }

    diagnostics::emit(op.token.location, message, labels, None, source_store);
}

macro_rules! type_pattern {
    ($( $const_name:tt @ $p:pat_param ),+) => {
        [
            $( Value { porth_type: $p, const_val: $const_name, .. } ),+
        ]
    };
}

pub fn analyze(
    program: &Program,
    proc: &Procedure,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut analyzer = Analyzer::default();
    let mut stack = Vec::new();
    let mut had_error = false;

    for (op_idx, op) in proc.body().iter().enumerate() {
        match op.code {
            OpCode::Add => {
                for value_id in stack.lastn(2).unwrap_or(&stack) {
                    let value = analyzer.values.get_mut(value_id).unwrap();
                    value.users.push(op_idx);
                    value.consumer = Some(op_idx);
                }

                let (new_type, const_val) = match stack.popn::<2>() {
                    None => {
                        generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
                        had_error = true;

                        (PorthTypeKind::Unknown, None)
                    }
                    Some(vals) => {
                        let new_tv = match analyzer.get_values(vals) {
                            type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                                (PorthTypeKind::Int, (*a).zip(*b))
                            }

                            type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Int)
                            | type_pattern!(b @ PorthTypeKind::Int, a @ PorthTypeKind::Ptr) => {
                                (PorthTypeKind::Ptr, (*a).zip(*b))
                            }
                            vals => {
                                // Type mismatch
                                had_error = true;
                                // Don't emit an diagnostic here if any are Unknown, as it's a result of
                                // an earlier error.
                                if vals.iter().all(|v| v.porth_type != PorthTypeKind::Unknown) {
                                    let lexeme = interner.resolve_lexeme(op.token.lexeme);
                                    generate_type_mismatch_diag(source_store, lexeme, op, &vals);
                                }
                                (PorthTypeKind::Unknown, None)
                            }
                        };

                        new_tv
                    }
                };

                let const_val = const_val.map(|mut cv| {
                    match &mut cv {
                        (ConstVal::Int(a), ConstVal::Int(b)) => *a += *b,
                        (ConstVal::Ptr { offset, .. }, ConstVal::Int(v)) => *offset += *v,
                        _ => unreachable!(),
                    }
                    cv.0
                });

                let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
                new_value.const_val = const_val;
                stack.push(new_id);
            }
            OpCode::Subtract => {
                for value_id in stack.lastn(2).unwrap_or(&stack) {
                    let value = analyzer.values.get_mut(value_id).unwrap();
                    value.users.push(op_idx);
                    value.consumer = Some(op_idx);
                }

                let (new_type, const_val) = match stack.popn::<2>() {
                    None => {
                        generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
                        had_error = true;

                        (PorthTypeKind::Unknown, None)
                    }
                    Some(vals) => {
                        let new_tv = match analyzer.get_values(vals) {
                            type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                                (PorthTypeKind::Int, (*a).zip(*b))
                            }
                            type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Ptr) => {
                                (PorthTypeKind::Int, (*a).zip(*b))
                            }
                            type_pattern!(b @ PorthTypeKind::Ptr, a @ PorthTypeKind::Int) => {
                                (PorthTypeKind::Ptr, (*a).zip(*b))
                            }
                            vals => {
                                // Type mismatch
                                had_error = true;
                                // Don't emit an diagnostic here if any are Unknown, as it's a result of
                                // an earlier error.
                                if vals.iter().all(|v| v.porth_type != PorthTypeKind::Unknown) {
                                    let lexeme = interner.resolve_lexeme(op.token.lexeme);
                                    generate_type_mismatch_diag(source_store, lexeme, op, &vals);
                                }
                                (PorthTypeKind::Unknown, None)
                            }
                        };
                        new_tv
                    }
                };

                let const_val = const_val.map(|mut cv| {
                    match &mut cv {
                        (ConstVal::Int(a), ConstVal::Int(b)) => *a -= *b,
                        (
                            ConstVal::Ptr {
                                id,
                                source_op_location,
                                offset,
                                ..
                            },
                            ConstVal::Ptr {
                                id: id2,
                                source_op_location: source_op_location2,
                                offset: offset2,
                                ..
                            },
                        ) => {
                            if id != id2 {
                                diagnostics::emit(
                                    op.token.location,
                                    "subtracting pointers of different sources",
                                    [
                                        Label::new(op.token.location)
                                            .with_color(Color::Red)
                                            .with_message("here"),
                                        Label::new(*source_op_location)
                                            .with_color(Color::Cyan)
                                            .with_message("...from this")
                                            .with_order(2),
                                        Label::new(*source_op_location2)
                                            .with_color(Color::Cyan)
                                            .with_message("subtracting this...")
                                            .with_order(1),
                                    ],
                                    None,
                                    source_store,
                                );
                                had_error = true;
                            } else if offset2 > offset {
                                diagnostics::emit(
                                    op.token.location,
                                    "subtracting out of bounds",
                                    [
                                        Label::new(op.token.location)
                                            .with_color(Color::Red)
                                            .with_message("here"),
                                        Label::new(*source_op_location)
                                            .with_color(Color::Cyan)
                                            .with_message(format!("...from this offset {}", offset))
                                            .with_order(2),
                                        Label::new(*source_op_location2)
                                            .with_color(Color::Cyan)
                                            .with_message(format!(
                                                "subtracting offset {}...",
                                                offset2
                                            ))
                                            .with_order(1),
                                    ],
                                    None,
                                    source_store,
                                );
                                had_error = true;
                            }
                        }
                        (ConstVal::Ptr { offset, .. }, ConstVal::Int(v)) => *offset -= *v,
                        _ => unreachable!(),
                    }
                    cv.0
                });

                let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
                new_value.const_val = const_val;
                stack.push(new_id);
            }

            OpCode::PushBool(v) => {
                let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Bool, op_idx, op.token);
                new_value.const_val = Some(ConstVal::Bool(v));
                stack.push(new_id);
            }
            OpCode::PushInt(v) => {
                let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
                new_value.const_val = Some(ConstVal::Int(v));
                stack.push(new_id);
            }
            OpCode::PushStr { is_c_str, id } => {
                if !is_c_str {
                    let (new_id, new_value) =
                        analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
                    let string = interner.resolve_literal(id);
                    new_value.const_val = Some(ConstVal::Int((string.len() - 1) as u64));
                    stack.push(new_id);
                }

                let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Ptr, op_idx, op.token);
                new_value.const_val = Some(ConstVal::Ptr {
                    id: PtrId::Str(id),
                    source_op_location: op.token.location,
                    offset: 0,
                });
                stack.push(new_id);
            }
            OpCode::Drop => match stack.pop() {
                None => {
                    generate_stack_exhaustion_diag(source_store, op, 0, 1);
                    had_error = true;
                }
                Some(val_id) => {
                    let value = analyzer.values.get_mut(&val_id).unwrap();
                    value.consumer = Some(op_idx);
                    value.users.push(op_idx);
                }
            },

            OpCode::Swap => match stack.as_mut_slice() {
                [.., a, b] => {
                    analyzer.values.get_mut(a).unwrap().users.push(op_idx);
                    analyzer.values.get_mut(b).unwrap().users.push(op_idx);
                    std::mem::swap(a, b);
                }
                _ => {
                    generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
                    had_error = true;
                    for vid in &stack {
                        analyzer.values.get_mut(vid).unwrap().users.push(op_idx);
                    }
                    stack.resize_with(2, || {
                        analyzer
                            .new_value(PorthTypeKind::Unknown, op_idx, op.token)
                            .0
                    });
                }
            },

            OpCode::Load(width) => match stack.pop() {
                None => {
                    generate_stack_exhaustion_diag(source_store, op, 0, 1);
                    had_error = true;
                    let (new_id, _) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
                    stack.push(new_id);
                }
                Some(val_id) => {
                    match analyzer.values.get(&val_id).unwrap() {
                        Value {
                            porth_type: PorthTypeKind::Ptr,
                            const_val,
                            ..
                        } => {
                            // Look at handling memory at some point?
                            if let Some(ConstVal::Ptr {
                                id: PtrId::Str(spur),
                                source_op_location,
                                offset,
                            }) = *const_val
                            {
                                let string = interner.resolve_literal(spur);
                                let end_idx = offset + width.byte_size();
                                if end_idx > string.len() as u64 - 1 {
                                    diagnostics::emit(
                                        op.token.location,
                                        "index out of bounds",
                                        [
                                            Label::new(op.token.location)
                                                .with_color(Color::Red)
                                                .with_message(format!("index: {}", offset,)),
                                            Label::new(source_op_location)
                                                .with_color(Color::Cyan)
                                                .with_message(format!(
                                                    "length: {}",
                                                    string.len() - 1
                                                ))
                                                .with_order(1),
                                        ],
                                        None,
                                        source_store,
                                    );

                                    had_error = true;
                                }
                            }
                        }
                        val => {
                            // Type mismatch
                            had_error = true;
                            // Unknown is the result of a previous error.
                            if val.porth_type != PorthTypeKind::Unknown {
                                let lexeme = interner.resolve_lexeme(op.token.lexeme);
                                generate_type_mismatch_diag(source_store, lexeme, op, &[val]);
                            }
                        }
                    };

                    let (new_id, _) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
                    stack.push(new_id);
                }
            },

            OpCode::Prologue | OpCode::Epilogue => {
                // TODO: These should do some handling
            }
            OpCode::Return { implicit: true } => {}
            _ => unimplemented!("{:?}", op.code),
        }
    }

    // dbg!(analyzer);

    had_error.not().then(|| ()).ok_or(())
}
