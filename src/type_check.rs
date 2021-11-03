use std::{
    cmp::Ordering,
    fmt::{self, Write},
};

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
    interners::Interners,
    n_ops::PopN,
    opcode::{Op, OpCode},
    source_file::{FileId, SourceLocation},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PorthTypeKind {
    Int,
    Ptr,
    Bool,
    Unknown,
}

#[derive(Debug, Clone, Copy, Eq)]
struct PorthType {
    kind: PorthTypeKind,
    location: SourceLocation,
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
    diags: &mut Vec<Diagnostic<FileId>>,
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

    let mut labels = vec![Label::primary(
        op.token.location.file_id,
        op.token.location.range(),
    )];

    for source in op.expansions.iter().skip(1) {
        labels.push(
            Label::secondary(source.file_id, source.range()).with_message("expanded from here"),
        );
    }

    for ty in types {
        labels.push(
            Label::secondary(ty.location.file_id, ty.location.range())
                .with_message(format!("{}", ty.kind)),
        )
    }

    let diag = Diagnostic::error()
        .with_message(message)
        .with_labels(labels);

    diags.push(diag);
}

fn generate_stack_exhaustion(
    diags: &mut Vec<Diagnostic<FileId>>,
    op: &Op,
    actual: usize,
    expected: usize,
) {
    let message = format!("expected {} items, found {}", expected, actual);

    let mut labels = vec![Label::primary(
        op.token.location.file_id,
        op.token.location.range(),
    )];

    for source in op.expansions.iter().skip(1) {
        labels.push(
            Label::secondary(source.file_id, source.range()).with_message("expanded from here"),
        );
    }

    let diag = Diagnostic::error()
        .with_message(message)
        .with_labels(labels);

    diags.push(diag);
}

fn generate_block_depth_mismatch(
    diags: &mut Vec<Diagnostic<FileId>>,
    open_loc: SourceLocation,
    close_loc: SourceLocation,
    expected: usize,
    actual: usize,
    msg: &str,
) {
    let diag = Diagnostic::error().with_message(msg).with_labels(vec![
        Label::primary(open_loc.file_id, open_loc.range())
            .with_message(format!("depth here: {}", expected)),
        Label::primary(close_loc.file_id, close_loc.range())
            .with_message(format!("depth here: {}", actual)),
    ]);
    diags.push(diag);
}

fn compare_expected_stacks(
    expected_stack: &[PorthType],
    actual_stack: &[PorthType],
    diags: &mut Vec<Diagnostic<FileId>>,
    open_loc: SourceLocation,
    op: &Op,
    msg: &str,
) {
    match expected_stack.len().cmp(&actual_stack.len()) {
        Ordering::Less | Ordering::Greater => {
            generate_block_depth_mismatch(
                diags,
                open_loc,
                op.token.location,
                expected_stack.len(),
                actual_stack.len(),
                msg,
            );
        }
        Ordering::Equal if expected_stack != actual_stack => {
            let mut diag = Diagnostic::error().with_message(msg).with_labels(vec![
                Label::primary(open_loc.file_id, open_loc.range()),
                Label::primary(op.token.location.file_id, op.token.location.range()),
            ]);

            diag.notes.push("IDX  | Expected |   Actual".to_owned());
            diag.notes.push("_____|__________|_________".to_owned());

            if expected_stack[0] == actual_stack[0] {
                diag.notes.push("...".to_owned());
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
                diag.notes.push(format!(
                    "{:<4} | {:<8} | {:>8}",
                    actual_stack.len() - idx - 1,
                    a.kind,
                    b.kind
                ));
            }

            diags.push(diag);
        }
        _ => {}
    }
}

macro_rules! stack_check {
    ($errors:ident, $stack:ident, $interners:ident, $op:ident, $($expected:pat_param)|+) => {
        match $stack.popn() {
            Some( $(a @ $expected)|+) => Some(a),
            #[allow(unreachable_patterns)]
            Some(ts) if ts.iter().any(|ty| ty.kind == PorthTypeKind::Unknown) => {
                // This means one or more operands were the result of a failed type check.
                // In order to avoid flooding the user with errors that resulted from the
                // original failure, we'll not emit an error here.
                None
            }
            #[allow(unreachable_patterns)]
            Some(ts) => {
                let lexeme = $interners.resolve_lexeme($op.token.lexeme);
                generate_type_mismatch(&mut $errors, lexeme, $op, &ts);
                None
            }
            None => {
                generate_stack_exhaustion(
                    &mut $errors,
                    $op,
                    $stack.len(),
                    $op.code.pop_count(),
                );
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

struct BlockStackState {
    open_location: SourceLocation,
    entry_stack: Vec<PorthType>,
    true_stack: Option<Vec<PorthType>>,
}

pub fn type_check(ops: &[Op], interner: &Interners) -> Result<(), Vec<Diagnostic<FileId>>> {
    let mut stack: Vec<PorthType> = Vec::new();
    let mut block_stack_states: Vec<BlockStackState> = Vec::new();
    let mut diags = Vec::new();

    for op in ops {
        match op.code {
            OpCode::Add => {
                let res = stack_check!(
                    diags,
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
                    diags,
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
                        stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
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
                    diags,
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
                    diags,
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
                    diags,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int, PorthTypeKind::Int])
                );

                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }

            OpCode::DivMod => {
                stack_check!(
                    diags,
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
            OpCode::PushStr(_) => stack.extend_from_slice(&[
                PorthType::new(PorthTypeKind::Int, op.token.location),
                PorthType::new(PorthTypeKind::Ptr, op.token.location),
            ]),
            OpCode::Drop => {
                stack_check!(diags, stack, interner, op, [_]);
            }

            OpCode::While { .. } => {
                block_stack_states.push(BlockStackState {
                    open_location: op.token.location,
                    entry_stack: stack.clone(),
                    true_stack: None,
                });
            }
            OpCode::DoWhile { .. } => {
                stack_check!(diags, stack, interner, op, kind_pat!([PorthTypeKind::Bool]));
                let entry_stack_state = block_stack_states
                    .last()
                    .expect("ICE: DoWhile requires a stack depth");

                compare_expected_stacks(
                    &entry_stack_state.entry_stack,
                    &stack,
                    &mut diags,
                    entry_stack_state.open_location,
                    op,
                    "while-do condition must leave the stack in the same state it entered with",
                );

                // Restore the stack so that we know it's the expected state before the body executes.
                stack.clear();
                stack.extend_from_slice(&entry_stack_state.entry_stack);
            }
            OpCode::EndWhile { .. } => {
                let entry_stack_state = block_stack_states
                    .pop()
                    .expect("ICE: EndWhile/EndIf requires a stack depth");

                compare_expected_stacks(
                    &entry_stack_state.entry_stack,
                    &stack,
                    &mut diags,
                    entry_stack_state.open_location,
                    op,
                    "while-do blocks must leave the stack in the same state it entered with",
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
                stack_check!(diags, stack, interner, op, kind_pat!([PorthTypeKind::Bool]));
                let entry_stack_state = block_stack_states
                    .last()
                    .expect("ICE: DoIf requires a stack depth");

                compare_expected_stacks(
                    &entry_stack_state.entry_stack,
                    &stack,
                    &mut diags,
                    entry_stack_state.open_location,
                    op,
                    "if-do condition must leave the stack in the same state it entered with",
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
                        compare_expected_stacks(
                            expected_stack,
                            &stack,
                            &mut diags,
                            entry_stack_state.open_location,
                            op,
                            "all if-elif-else blocks must leave the stack in the same state",
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

                compare_expected_stacks(
                    &expected_stack,
                    &stack,
                    &mut diags,
                    entry_stack_state.open_location,
                    op,
                    msg,
                );

                // Now that we've checked, we need to restore the stack to the state it was in
                // prior to the branch, so that the remainder of the code can operate as if
                // we never went down it.
                stack = expected_stack;
            }

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => {
                stack_check!(
                    diags,
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
                    diags,
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

            OpCode::Print => {
                stack_check!(diags, stack, interner, op, kind_pat!([PorthTypeKind::Int]));
            }
            OpCode::Dup { depth } => {
                if stack.len() < (depth + 1) {
                    generate_stack_exhaustion(&mut diags, op, stack.len(), depth + 1);
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
                    generate_stack_exhaustion(&mut diags, op, stack.len(), op.code.pop_count());
                    stack.extend_from_slice(&[
                        PorthType::new(PorthTypeKind::Unknown, op.token.location),
                        a,
                    ]);
                }
                [] => {
                    generate_stack_exhaustion(&mut diags, op, 0, op.code.pop_count());
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
                        generate_stack_exhaustion(&mut diags, op, stack.len(), op.code.pop_count());
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
                    generate_stack_exhaustion(&mut diags, op, stack.len(), op.code.pop_count());
                    stack.resize(2, PorthType::new(PorthTypeKind::Unknown, op.token.location));
                }
            },

            OpCode::Memory { .. } => {
                stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location))
            }
            OpCode::Load(_) => {
                stack_check!(diags, stack, interner, op, kind_pat!([PorthTypeKind::Ptr]));
                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }
            OpCode::Store(_) => {
                stack_check!(
                    diags,
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
                    diags,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Bool] | [PorthTypeKind::Int])
                );
                stack.push(PorthType::new(PorthTypeKind::Bool, op.token.location));
            }
            OpCode::CastInt => {
                stack_check!(
                    diags,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int] | [PorthTypeKind::Ptr] | [PorthTypeKind::Bool])
                );
                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }
            OpCode::CastPtr => {
                stack_check!(
                    diags,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Int] | [PorthTypeKind::Ptr])
                );
                stack.push(PorthType::new(PorthTypeKind::Ptr, op.token.location));
            }

            OpCode::SysCall(num_args @ 0..=6) => {
                let required = num_args + 1; //
                if stack.len() < required {
                    generate_stack_exhaustion(&mut diags, op, stack.len(), required);
                    stack.clear();
                } else {
                    stack.truncate(stack.len() - required);
                }

                stack.push(PorthType::new(PorthTypeKind::Int, op.token.location));
            }

            OpCode::SysCall(_)
            | OpCode::Ident(_)
            | OpCode::Include(_)
            | OpCode::End
            | OpCode::Do => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }

    if !stack.is_empty() {
        let label = ops
            .last()
            .map(|op| {
                let mut labels = vec![Label::primary(
                    op.token.location.file_id,
                    op.token.location.range(),
                )];

                for source in op.expansions.iter() {
                    labels.push(
                        Label::secondary(source.file_id, source.range())
                            .with_message("expanded from here"),
                    );
                }

                labels
            })
            .unwrap_or_else(Vec::new);

        diags.push(
            Diagnostic::error()
                .with_message(format!("{} elements left on the stack", stack.len()))
                .with_labels(label),
        );
    }

    diags.is_empty().then(|| ()).ok_or(diags)
}
