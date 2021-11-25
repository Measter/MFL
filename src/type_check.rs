use std::{
    cmp::Ordering,
    fmt::{self, Write},
    ops::Not,
};

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{NOps, PopN},
    opcode::{Op, OpCode},
    program::{Procedure, ProcedureKind, Program},
    source_file::{SourceLocation, SourceStorage},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PorthTypeKind {
    Int,
    Ptr,
    Bool,
    Unknown,
}

#[derive(Debug, Clone, Copy, Eq)]
pub struct PorthType {
    pub kind: PorthTypeKind,
    pub location: SourceLocation,
}

impl PorthType {
    fn new(kind: PorthTypeKind, location: SourceLocation) -> Self {
        Self { kind, location }
    }
}

impl PartialEq for PorthType {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
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

fn generate_type_mismatch(
    source_store: &SourceStorage,
    operator_str: &str,
    op: &Op,
    types: &[PorthType],
) {
    let mut message = format!("cannot use `{}` on ", operator_str);
    match types {
        [] => unreachable!(),
        [a] => write!(&mut message, "`{:?}`", a.kind).unwrap(),
        [a, b] => write!(&mut message, "`{}` and `{}`", a.kind, b.kind).unwrap(),
        [xs @ .., last] => {
            for x in xs {
                write!(&mut message, "`{:?}`, ", x.kind).unwrap();
            }

            write!(&mut message, "and `{:?}`", last.kind).unwrap();
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

    for (ty, order) in types.iter().rev().zip(1..) {
        labels.push(
            Label::new(ty.location)
                .with_color(Color::Yellow)
                .with_message(format!("{}", ty.kind))
                .with_order(order),
        )
    }

    diagnostics::emit(op.token.location, message, labels, None, source_store);
}

fn generate_stack_exhaustion(
    source_store: &SourceStorage,
    op: &Op,
    actual: usize,
    expected: usize,
) {
    let message = format!("expected {} items, found {}", expected, actual);

    let mut labels = vec![Label::new(op.token.location).with_color(Color::Red)];

    for source in op.expansions.iter() {
        labels.push(
            Label::new(*source)
                .with_color(Color::Blue)
                .with_message("expanded from here"),
        );
    }

    diagnostics::emit(op.token.location, message, labels, None, source_store);
}

fn generate_block_depth_mismatch(
    source_store: &SourceStorage,
    open_loc: SourceLocation,
    close_loc: SourceLocation,
    expected: usize,
    actual: usize,
    msg: &str,
) {
    diagnostics::emit(
        open_loc,
        msg,
        [
            Label::new(open_loc)
                .with_color(Color::Cyan)
                .with_message(format!("depth here: {}", expected)),
            Label::new(close_loc)
                .with_color(Color::Cyan)
                .with_message(format!("depth here: {}", actual)),
        ],
        None,
        source_store,
    );
}

fn failed_compare_stack_types(
    expected_stack: &[PorthType],
    actual_stack: &[PorthType],
    open_block_loc: SourceLocation,
    op: &Op,
    msg: &str,
    source_store: &SourceStorage,
) {
    let mut note = "\n\t\tIDX  | Expected |   Actual\n\
        \t\t_____|__________|_________"
        .to_owned();

    if expected_stack[0] == actual_stack[0] {
        note.push_str("\n\t\t...");
    }

    let mut pairs = expected_stack
        .iter()
        .zip(actual_stack)
        .enumerate()
        .peekable();
    while matches!(pairs.peek(), Some((_, (a, b))) if a == b) {
        pairs.next();
    }

    for (idx, (a, b)) in pairs {
        write!(
            &mut note,
            "\n\t\t{:<4} | {:<8} | {:>8}",
            actual_stack.len() - idx - 1,
            a.kind,
            b.kind
        )
        .unwrap();
    }

    diagnostics::emit(
        open_block_loc,
        msg,
        [
            Label::new(op.token.location)
                .with_color(Color::Red)
                .with_message("called here"),
            Label::new(open_block_loc)
                .with_color(Color::Cyan)
                .with_message("defined here"),
        ],
        note,
        source_store,
    );
}

#[must_use]
fn compare_expected_stacks(
    expected_stack: &[PorthType],
    actual_stack: &[PorthType],
    open_loc: SourceLocation,
    op: &Op,
    msg: &str,
    source_store: &SourceStorage,
) -> bool {
    match expected_stack.len().cmp(&actual_stack.len()) {
        Ordering::Less | Ordering::Greater => {
            generate_block_depth_mismatch(
                source_store,
                open_loc,
                op.token.location,
                expected_stack.len(),
                actual_stack.len(),
                msg,
            );
            true
        }
        Ordering::Equal if expected_stack != actual_stack => {
            failed_compare_stack_types(
                expected_stack,
                actual_stack,
                open_loc,
                op,
                msg,
                source_store,
            );
            true
        }
        _ => false,
    }
}

macro_rules! stack_check {
    ($source_store:ident, $had_error: ident, $stack:ident, $interners:ident, $op:ident, $($expected:pat_param)|+) => {
        match $stack.popn() {
            Some( $(a @ $expected)|+) => Some(a),
            #[allow(unreachable_patterns)]
            Some(ts) if ts.iter().any(|ty| ty.kind == PorthTypeKind::Unknown) => {
                // This means one or more operands were the result of a failed type check.
                // In order to avoid flooding the user with errors that resulted from the
                // original failure, we'll not emit an error here.
                $had_error = true;
                None
            }
            #[allow(unreachable_patterns)]
            Some(ts) => {
                let lexeme = $interners.resolve_lexeme($op.token.lexeme);
                generate_type_mismatch($source_store, lexeme, $op, &ts);
                $had_error = true;
                None
            }
            None => {
                generate_stack_exhaustion(
                    $source_store,
                    $op,
                    $stack.len(),
                    $op.code.pop_count(),
                );
                $had_error = true;
                $stack.clear();
                None
            }
        }
    };
}

macro_rules! kind_pat {
    ($( [ $( $p:pat_param ),+ ] )|+ ) => {
        $(
            [
                $( PorthType { kind: $p, .. } ),+
            ]
        )|+
    };
}

#[must_use]
fn final_stack_check(
    procedure: &Procedure,
    stack: &[PorthType],
    source_store: &SourceStorage,
) -> bool {
    let make_labels = || {
        procedure
            .body()
            .last()
            .map(|op| {
                let mut labels = vec![Label::new(op.token.location).with_color(Color::Red)];

                for source in op.expansions.iter() {
                    labels.push(
                        Label::new(*source)
                            .with_color(Color::Blue)
                            .with_message("expanded from here"),
                    );
                }

                labels
            })
            .unwrap_or_else(|| vec![Label::new(procedure.name().location).with_color(Color::Red)])
    };

    if stack.len() != procedure.exit_stack().len() {
        diagnostics::emit(
            procedure.name().location,
            format!(
                "expected {} elements on stack, found {}",
                procedure.exit_stack().len(),
                stack.len()
            ),
            make_labels(),
            None,
            source_store,
        );

        return true;
    }

    if stack != procedure.exit_stack() {
        failed_compare_stack_types(
            procedure.exit_stack(),
            stack,
            procedure.name().location,
            procedure.body().last().unwrap(),
            "procedure return stack mismatch",
            source_store,
        );

        return true;
    }

    false
}
struct BlockStackState {
    open_location: SourceLocation,
    entry_stack: Vec<PorthType>,
    true_stack: Option<Vec<PorthType>>,
}

pub fn type_check(
    program: &Program,
    proc: &Procedure,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut stack: Vec<PorthType> = proc.entry_stack().to_owned();
    let mut block_stack_states: Vec<BlockStackState> = Vec::new();
    let mut had_error = false;

    for op in proc.body() {
        match op.code {
            OpCode::Add => {
                let res = stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!(
                        [PorthTypeKind::Int, PorthTypeKind::Int]
                            | [PorthTypeKind::Int, PorthTypeKind::Ptr]
                            | [PorthTypeKind::Ptr, PorthTypeKind::Int]
                    )
                );

                match res {
                    Some(kind_pat!([PorthTypeKind::Int, PorthTypeKind::Int])) => {
                        stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
                    }
                    Some(kind_pat!([PorthTypeKind::Ptr, PorthTypeKind::Int])) => {
                        stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
                    }
                    Some(kind_pat!([PorthTypeKind::Int, PorthTypeKind::Ptr])) => {
                        stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
                    }
                    Some(_) => unreachable!(),
                    None => stack.push(PorthType::new(PorthTypeKind::Unknown, op.token.location)),
                }
            }
            OpCode::Subtract => {
                let res = stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!(
                        [PorthTypeKind::Int, PorthTypeKind::Int]
                            | [PorthTypeKind::Ptr, PorthTypeKind::Ptr]
                            | [PorthTypeKind::Ptr, PorthTypeKind::Int]
                    )
                );

                match res {
                    Some(kind_pat!([PorthTypeKind::Int, PorthTypeKind::Int])) => {
                        stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
                    }
                    Some(kind_pat!([PorthTypeKind::Ptr, PorthTypeKind::Ptr])) => {
                        stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
                    }
                    Some(kind_pat!([PorthTypeKind::Ptr, PorthTypeKind::Int])) => {
                        stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
                    }
                    Some(_) => unreachable!(),
                    None => stack.push(PorthType::new(PorthTypeKind::Unknown, op.token.location)),
                }
            }

            OpCode::BitOr | OpCode::BitAnd => {
                let res = stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!(
                        [PorthTypeKind::Int, PorthTypeKind::Int]
                            | [PorthTypeKind::Bool, PorthTypeKind::Bool]
                    )
                );

                match res {
                    Some(kind_pat!([PorthTypeKind::Int, PorthTypeKind::Int])) => {
                        stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
                    }
                    Some(kind_pat!([PorthTypeKind::Bool, PorthTypeKind::Bool])) => {
                        stack.push(PorthType::new(PorthTypeKind::Bool, op.token.location));
                    }
                    _ => {
                        stack.push(PorthType::new(PorthTypeKind::Unknown, op.token.location));
                    }
                }
            }
            OpCode::BitNot => {
                let res = stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int] | [PorthTypeKind::Bool])
                );
                match res {
                    Some(kind_pat!([PorthTypeKind::Int])) => {
                        stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
                    }
                    Some(kind_pat!([PorthTypeKind::Bool])) => {
                        stack.push(PorthType::new(PorthTypeKind::Bool, op.token.location));
                    }
                    _ => {
                        stack.push(PorthType::new(PorthTypeKind::Unknown, op.token.location));
                    }
                }
            }
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int, PorthTypeKind::Int])
                );

                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }

            OpCode::DivMod => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int, PorthTypeKind::Int])
                );

                stack.extend_from_slice(&[
                    PorthType::new(PorthTypeKind::Int, op.token.location),
                    PorthType::new(PorthTypeKind::Int, op.token.location),
                ]);
            }

            OpCode::PushBool(_) => {
                stack.push(PorthType::new(PorthTypeKind::Bool, op.token.location))
            }
            OpCode::PushInt(_) => stack.push(PorthType::new(PorthTypeKind::Int, op.token.location)),
            OpCode::PushStr { is_c_str, .. } => {
                if !is_c_str {
                    stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
                }
                stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
            }
            OpCode::Drop => {
                stack_check!(source_store, had_error, stack, interner, op, [_]);
            }

            OpCode::While { .. } => {
                block_stack_states.push(BlockStackState {
                    open_location: op.token.location,
                    entry_stack: stack.clone(),
                    true_stack: None,
                });
            }
            OpCode::DoWhile { .. } => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Bool])
                );
                let entry_stack_state = block_stack_states
                    .last()
                    .expect("ICE: DoWhile requires a stack depth");

                had_error |= compare_expected_stacks(
                    &entry_stack_state.entry_stack,
                    &stack,
                    entry_stack_state.open_location,
                    op,
                    "while-do condition must leave the stack in the same state it entered with",
                    source_store,
                );

                // Restore the stack so that we know it's the expected state before the body executes.
                stack.clear();
                stack.extend_from_slice(&entry_stack_state.entry_stack);
            }
            OpCode::EndWhile { .. } => {
                let entry_stack_state = block_stack_states
                    .pop()
                    .expect("ICE: EndWhile/EndIf requires a stack depth");

                had_error |= compare_expected_stacks(
                    &entry_stack_state.entry_stack,
                    &stack,
                    entry_stack_state.open_location,
                    op,
                    "while-do blocks must leave the stack in the same state it entered with",
                    source_store,
                );

                // Now that we've checked, we need to restore the stack to the state it was in
                // prior to the branch, so that the remainder of the code can operate as if
                // we never went down it.
                stack = entry_stack_state.entry_stack;
            }

            OpCode::If => {
                block_stack_states.push(BlockStackState {
                    open_location: op.token.location,
                    entry_stack: stack.clone(),
                    true_stack: None,
                });
            }
            OpCode::DoIf { .. } => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Bool])
                );
                let entry_stack_state = block_stack_states
                    .last()
                    .expect("ICE: DoIf requires a stack depth");

                had_error |= compare_expected_stacks(
                    &entry_stack_state.entry_stack,
                    &stack,
                    entry_stack_state.open_location,
                    op,
                    "if-do condition must leave the stack in the same state it entered with",
                    source_store,
                );

                // Restore the stack so that we know it's the expected state before the body executes.
                stack.clear();
                stack.extend_from_slice(&entry_stack_state.entry_stack);
            }
            OpCode::Elif { .. } | OpCode::Else { .. } => {
                // If the if-expr has an else- or elif-branch, then all branches are allowed to alter the
                // state of the stack *as long as* all alter it in the same way.
                // We need to restore the stack to how it was when we entered the if-expr, but need to store
                // the exit state of the first branch to enforce that all branches leave the stack in the same
                // state.

                let entry_stack_state = block_stack_states
                    .last_mut()
                    .expect("ICE: Else/Elif requires a stack depth");

                // As there can be arbitrarily many branches, we should treat each elif-else opcode
                // as if it were an end-branch and check the stack state.
                match &mut entry_stack_state.true_stack {
                    Some(expected_stack) => {
                        had_error |= compare_expected_stacks(
                            expected_stack,
                            &stack,
                            entry_stack_state.open_location,
                            op,
                            "all if-elif-else blocks must leave the stack in the same state",
                            source_store,
                        );
                    }
                    true_stack => {
                        *true_stack = Some(stack.clone());
                        entry_stack_state.open_location = op.token.location;
                    }
                }

                // Now we need to restore the stack to the state it was in prior to entering the if-expr, so
                // that the subsequent branches can operate on the same state.
                stack.clear();
                stack.extend_from_slice(&entry_stack_state.entry_stack);
            }
            OpCode::EndIf { .. } => {
                let entry_stack_state = block_stack_states
                    .pop()
                    .expect("ICE: EndWhile/EndIf requires a stack depth");

                let (msg, expected_stack) = if let Some(true_stack) = entry_stack_state.true_stack {
                    (
                        "all if-elif-else blocks must leave the stack in the same state",
                        true_stack,
                    )
                } else {
                    (
                        "if-end blocks must leave the stack in the same state it entered with",
                        entry_stack_state.entry_stack,
                    )
                };

                had_error |= compare_expected_stacks(
                    &expected_stack,
                    &stack,
                    entry_stack_state.open_location,
                    op,
                    msg,
                    source_store,
                );

                // Now that we've checked, we need to restore the stack to the state it was in
                // prior to the branch, so that the remainder of the code can operate as if
                // we never went down it.
                stack = expected_stack;
            }

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!(
                        [PorthTypeKind::Int, PorthTypeKind::Int]
                            | [PorthTypeKind::Ptr, PorthTypeKind::Ptr]
                    )
                );
                stack.push(PorthType::new(PorthTypeKind::Bool, op.token.location));
            }
            OpCode::Equal | OpCode::NotEq => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!(
                        [PorthTypeKind::Int, PorthTypeKind::Int]
                            | [PorthTypeKind::Bool, PorthTypeKind::Bool]
                            | [PorthTypeKind::Ptr, PorthTypeKind::Ptr]
                    )
                );

                stack.push(PorthType::new(PorthTypeKind::Bool, op.token.location));
            }

            OpCode::Dup { depth } => {
                if stack.len() < (depth + 1) {
                    generate_stack_exhaustion(source_store, op, stack.len(), depth + 1);
                    had_error = true;
                    // We don't know what was expected, but we need something there.
                    stack.push(PorthType::new(PorthTypeKind::Unknown, op.token.location));
                } else {
                    let ty = stack[stack.len() - 1 - depth];
                    stack.push(ty);
                }
            }
            OpCode::DupPair => match &*stack {
                [.., a, b] => {
                    let a = *a;
                    let b = *b;
                    stack.extend_from_slice(&[a, b]);
                }
                [a] => {
                    let a = *a;
                    generate_stack_exhaustion(source_store, op, stack.len(), op.code.pop_count());
                    had_error = true;
                    stack.extend_from_slice(&[
                        PorthType::new(PorthTypeKind::Unknown, op.token.location),
                        a,
                    ]);
                }
                [] => {
                    generate_stack_exhaustion(source_store, op, 0, op.code.pop_count());
                    had_error = true;
                    stack.extend_from_slice(&[
                        PorthType::new(PorthTypeKind::Unknown, op.token.location),
                        PorthType::new(PorthTypeKind::Unknown, op.token.location),
                    ]);
                }
            },
            OpCode::Rot => {
                match &*stack {
                    [.., _, _, _] => {}
                    _ => {
                        generate_stack_exhaustion(
                            source_store,
                            op,
                            stack.len(),
                            op.code.pop_count(),
                        );
                        had_error = true;
                        stack.resize(3, PorthType::new(PorthTypeKind::Unknown, op.token.location));
                    }
                }
                let start = stack.len() - 3;
                stack[start..].rotate_left(1);
            }
            OpCode::Swap => match stack.as_mut_slice() {
                [.., a, b] => {
                    std::mem::swap(a, b);
                }
                _ => {
                    generate_stack_exhaustion(source_store, op, stack.len(), op.code.pop_count());
                    had_error = true;
                    stack.resize(2, PorthType::new(PorthTypeKind::Unknown, op.token.location));
                }
            },

            OpCode::Load(_) => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Ptr])
                );
                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }
            OpCode::Store(_) => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!(
                        [PorthTypeKind::Int, PorthTypeKind::Ptr]
                            | [PorthTypeKind::Ptr, PorthTypeKind::Ptr]
                            | [PorthTypeKind::Bool, PorthTypeKind::Ptr]
                    )
                );
            }

            OpCode::ArgC => stack.push(PorthType::new(PorthTypeKind::Int, op.token.location)),
            OpCode::ArgV => stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location)),

            OpCode::CastBool => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Bool] | [PorthTypeKind::Int])
                );
                stack.push(PorthType::new(PorthTypeKind::Bool, op.token.location));
            }
            OpCode::CastInt => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int] | [PorthTypeKind::Ptr] | [PorthTypeKind::Bool])
                );
                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }
            OpCode::CastPtr => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int] | [PorthTypeKind::Ptr])
                );
                stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
            }

            OpCode::ResolvedIdent { proc_id, .. } => {
                let referenced_proc = program.get_proc(proc_id);

                match referenced_proc.kind() {
                    ProcedureKind::Memory => {
                        stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
                    }
                    _ => {
                        if stack.len() < referenced_proc.entry_stack().len() {
                            generate_stack_exhaustion(
                                source_store,
                                op,
                                stack.len(),
                                referenced_proc.entry_stack().len(),
                            );
                            had_error = true;
                            stack.clear();
                        } else {
                            let last_n = stack.lastn(referenced_proc.entry_stack().len()).unwrap();
                            if last_n != referenced_proc.entry_stack() {
                                failed_compare_stack_types(
                                    referenced_proc.entry_stack(),
                                    last_n,
                                    referenced_proc.name().location,
                                    op,
                                    "incorrect types on stack",
                                    source_store,
                                );
                                had_error = true;
                            }
                            stack.truncate(stack.len() - referenced_proc.entry_stack().len());
                        }

                        stack.extend_from_slice(referenced_proc.exit_stack());
                    }
                }
            }

            OpCode::Epilogue | OpCode::Prologue => {}
            OpCode::Return => {
                had_error |= final_stack_check(proc, &stack, source_store);
            }

            OpCode::SysCall(num_args @ 0..=6) => {
                let required = num_args + 1; //
                if stack.len() < required {
                    generate_stack_exhaustion(source_store, op, stack.len(), required);
                    had_error = true;
                    stack.clear();
                } else {
                    stack.truncate(stack.len() - required);
                }

                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }

            OpCode::SysCall(_)
            | OpCode::CallProc{..} // These haven't been generated yet
            | OpCode::Memory{..} // These haven't been generated yet
            | OpCode::UnresolvedIdent { .. }
            | OpCode::Include(_)
            | OpCode::End
            | OpCode::Do => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }

    had_error |= final_stack_check(proc, &stack, source_store);

    had_error.not().then(|| ()).ok_or(())
}
