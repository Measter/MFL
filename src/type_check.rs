use std::{
    cmp::Ordering,
    fmt::{self, Write},
};

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    popn::PopN,
    source_file::{FileId, SourceLocation},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PorthType {
    Int,
    Ptr,
    Bool,
    Unknown,
}

impl fmt::Display for PorthType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PorthType::Int => "Int".fmt(f),
            PorthType::Ptr => "Ptr".fmt(f),
            PorthType::Bool => "Bool".fmt(f),
            PorthType::Unknown => "Unknown".fmt(f),
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
        [a] => write!(&mut message, "`{:?}`", a).unwrap(),
        [a, b] => write!(&mut message, "`{:?}` and `{:?}`", a, b).unwrap(),
        [xs @ .., last] => {
            for x in xs {
                write!(&mut message, "`{:?}`, ", x).unwrap();
            }

            write!(&mut message, "and `{:?}`", last).unwrap();
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
) {
    let diag = Diagnostic::error()
        .with_message("blocks require the same depth on exit as on entry")
        .with_labels(vec![
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
                    a,
                    b
                ));
            }

            diags.push(diag);
        }
        _ => {}
    }
}

macro_rules! stack_check {
    ($errors:ident, $stack:ident, $interners:ident, $op:ident, $($expected:pat)|+) => {
        match $stack.popn() {
            Some( $(a @ $expected)|+) => Some(a),
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

pub fn type_check(ops: &[Op], interner: &Interners) -> Result<(), Vec<Diagnostic<FileId>>> {
    let mut stack: Vec<PorthType> = Vec::new();
    let mut block_stack_states: Vec<(SourceLocation, Vec<PorthType>, bool)> = Vec::new();
    let mut diags = Vec::new();

    for op in ops {
        match op.code {
            OpCode::Add => {
                let res = stack_check!(
                    diags,
                    stack,
                    interner,
                    op,
                    [PorthType::Int, PorthType::Int]
                        | [PorthType::Int, PorthType::Ptr]
                        | [PorthType::Ptr, PorthType::Int]
                );

                match res {
                    Some([PorthType::Int, PorthType::Int]) => stack.push(PorthType::Int),
                    Some([PorthType::Ptr, PorthType::Int]) => stack.push(PorthType::Ptr),
                    Some([PorthType::Int, PorthType::Ptr]) => stack.push(PorthType::Ptr),
                    Some(_) => unreachable!(),
                    None => stack.push(PorthType::Unknown),
                }
            }
            OpCode::Subtract
            | OpCode::Multiply
            | OpCode::BitOr
            | OpCode::BitAnd
            | OpCode::ShiftLeft
            | OpCode::ShiftRight => {
                stack_check!(diags, stack, interner, op, [PorthType::Int, PorthType::Int]);
                stack.push(PorthType::Int);
            }

            OpCode::DivMod => {
                stack_check!(diags, stack, interner, op, [PorthType::Int, PorthType::Int]);

                stack.extend_from_slice(&[PorthType::Int, PorthType::Int]);
            }

            OpCode::PushInt(_) => stack.push(PorthType::Int),
            OpCode::PushStr(_) => stack.extend_from_slice(&[PorthType::Int, PorthType::Ptr]),
            OpCode::Drop => {
                stack_check!(diags, stack, interner, op, [_]);
            }

            OpCode::While { .. } => {
                block_stack_states.push((op.token.location, stack.clone(), false));
            }
            OpCode::Do { .. } => {
                stack_check!(diags, stack, interner, op, [PorthType::Bool]);
                let (open_loc, expected_stack, _) = block_stack_states
                    .last()
                    .expect("ICE: EndWhile/EndIf requires a stack depth");

                compare_expected_stacks(
                    expected_stack,
                    &stack,
                    &mut diags,
                    *open_loc,
                    op,
                    "while-do condition must leave the stack in the same state it entered with",
                );

                // Restore the stack so that we know it's the expected state before the body executes.
                stack.clear();
                stack.extend_from_slice(expected_stack);
            }
            OpCode::EndWhile { .. } => {
                let (open_loc, expected_stack, _) = block_stack_states
                    .pop()
                    .expect("ICE: EndWhile/EndIf requires a stack depth");

                compare_expected_stacks(
                    &expected_stack,
                    &stack,
                    &mut diags,
                    open_loc,
                    op,
                    "while-do blocks must leave the stack in the same state it entered with",
                );

                // Now that we've checked, we need to restore the stack to the state it was in
                // prior to the branch, so that the remainder of the code can operate as if
                // we never went down it.
                stack = expected_stack;
            }

            OpCode::If { .. } => {
                stack_check!(diags, stack, interner, op, [PorthType::Bool]);
                block_stack_states.push((op.token.location, stack.clone(), false));
            }
            OpCode::Else { .. } => {
                // If the if-expr has an else-branch, then both branches are allowed to alter the state of the
                // stack *as long as* both alter it in the same way.
                // We need to restore the stack to how it was when we entered the if-expr, but need to store
                // the exit state of the true branch to enforce that both branches leave the stack in the same
                // state.

                let (_, entry_stack, had_else) = block_stack_states
                    .last_mut()
                    .expect("ICE: Else requires a stack depth");

                // We need the state of the stack from the true-branch, so we can restore that on the end-tag.
                let exit_branch = stack.clone();
                *had_else = true;

                // Now we need to restore the stack to the state it was in prior to entering the if-expr, so
                // that the else branch can operate on the same state.
                stack.clear();
                stack.extend_from_slice(entry_stack);
                *entry_stack = exit_branch;
            }
            OpCode::EndIf { .. } => {
                let (open_loc, expected_stack, had_else) = block_stack_states
                    .pop()
                    .expect("ICE: EndWhile/EndIf requires a stack depth");

                let msg = if had_else {
                    "if-else blocks must leave the stack in the same state"
                } else {
                    "if-end blocks must leave the stack in the same state it entered with"
                };

                compare_expected_stacks(&expected_stack, &stack, &mut diags, open_loc, op, msg);

                // Now that we've checked, we need to restore the stack to the state it was in
                // prior to the branch, so that the remainder of the code can operate as if
                // we never went down it.
                stack = expected_stack;
            }

            OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Equal
            | OpCode::NotEq => {
                stack_check!(diags, stack, interner, op, [PorthType::Int, PorthType::Int]);
                stack.push(PorthType::Bool);
            }

            OpCode::Print => {
                stack_check!(diags, stack, interner, op, [PorthType::Int]);
            }
            OpCode::Dup { depth } => {
                if stack.len() < (depth + 1) {
                    generate_stack_exhaustion(&mut diags, op, stack.len(), depth + 1);
                    // We don't know what was expected, but we need something there.
                    stack.push(PorthType::Unknown);
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
                    stack.extend_from_slice(&[PorthType::Unknown, a]);
                }
                [] => {
                    generate_stack_exhaustion(&mut diags, op, 0, op.code.pop_count());
                    stack.extend_from_slice(&[PorthType::Unknown, PorthType::Unknown]);
                }
            },

            OpCode::Swap => match &*stack {
                [.., a, b] => {
                    let a = *a;
                    let b = *b;
                    stack.extend_from_slice(&[b, a]);
                }
                [a] => {
                    let a = *a;
                    generate_stack_exhaustion(&mut diags, op, stack.len(), op.code.pop_count());
                    stack.extend_from_slice(&[a, PorthType::Unknown]);
                }
                [] => {
                    generate_stack_exhaustion(&mut diags, op, 0, op.code.pop_count());
                    stack.extend_from_slice(&[PorthType::Unknown, PorthType::Unknown]);
                }
            },

            OpCode::Mem { .. } => stack.push(PorthType::Ptr),
            OpCode::Load | OpCode::Load64 => {
                stack_check!(diags, stack, interner, op, [PorthType::Ptr]);
                stack.push(PorthType::Int);
            }
            OpCode::Store | OpCode::Store64 => {
                stack_check!(diags, stack, interner, op, [_, PorthType::Ptr]);
            }

            OpCode::ArgC => stack.push(PorthType::Int),
            OpCode::ArgV => stack.push(PorthType::Ptr),

            OpCode::SysCall(num_args @ 0..=6) => {
                let required = num_args + 1; //
                if stack.len() < required {
                    generate_stack_exhaustion(&mut diags, op, stack.len(), required);
                } else {
                    stack.truncate(stack.len() - required);
                }

                stack.push(PorthType::Int);
            }

            OpCode::SysCall(_) | OpCode::Ident(_) | OpCode::Include(_) | OpCode::End { .. } => {
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
