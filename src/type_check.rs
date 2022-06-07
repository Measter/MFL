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
    // TODO: Replace this with source token.
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

    diagnostics::emit_error(op.token.location, message, labels, None, source_store);
}

fn generate_stack_exhaustion(
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

    diagnostics::emit_error(op.token.location, message, labels, None, source_store);
}

fn generate_block_depth_mismatch(
    source_store: &SourceStorage,
    open_loc: SourceLocation,
    close_loc: SourceLocation,
    expected: usize,
    actual: usize,
    msg: &str,
) {
    diagnostics::emit_error(
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
    sample_loc: SourceLocation,
    error_loc: SourceLocation,
    msg: &str,
    source_store: &SourceStorage,
) {
    let mut note = "\n\t\tDepth | Expected |   Actual\n\
        \t\t______|__________|_________"
        .to_owned();

    if expected_stack[0] == actual_stack[0] {
        note.push_str("\n\t\t...");
    }

    let mut pairs = expected_stack
        .iter()
        .zip(actual_stack)
        .enumerate()
        .rev()
        .peekable();
    while matches!(pairs.peek(), Some((_, (a, b))) if a == b) {
        pairs.next();
    }

    for (idx, (a, b)) in pairs {
        write!(
            &mut note,
            "\n\t\t{:<5} | {:<8} | {:>8}",
            actual_stack.len() - idx - 1,
            a.kind,
            b.kind
        )
        .unwrap();
    }

    diagnostics::emit_error(
        sample_loc,
        msg,
        [
            Label::new(error_loc)
                .with_color(Color::Red)
                .with_message("actual sampled here"),
            Label::new(sample_loc)
                .with_color(Color::Cyan)
                .with_message("expected sampled here"),
        ],
        note,
        source_store,
    );
}

#[must_use]
fn compare_expected_stacks(
    expected_stack: &[PorthType],
    actual_stack: &[PorthType],
    sample_loc: SourceLocation,
    error_loc: SourceLocation,
    msg: &str,
    source_store: &SourceStorage,
) -> bool {
    match expected_stack.len().cmp(&actual_stack.len()) {
        Ordering::Less | Ordering::Greater => {
            generate_block_depth_mismatch(
                source_store,
                sample_loc,
                error_loc,
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
                sample_loc,
                error_loc,
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
                *$had_error = true;
                None
            }
            #[allow(unreachable_patterns)]
            Some(ts) => {
                let lexeme = $interners.resolve_lexeme($op.token.lexeme);
                generate_type_mismatch($source_store, lexeme, $op, &ts);
                *$had_error = true;
                None
            }
            None => {
                generate_stack_exhaustion(
                    $source_store,
                    $op,
                    $stack.len(),
                    $op.code.pop_count(),
                );
                *$had_error = true;
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
    op: Option<&Op>,
    stack: &[PorthType],
    source_store: &SourceStorage,
) -> bool {
    let op = op.unwrap_or_else(|| procedure.body().last().unwrap());

    let make_labels = || {
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

        labels
    };

    if stack.len() != procedure.exit_stack().len() {
        diagnostics::emit_error(
            op.token.location,
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
            procedure.exit_stack_location(),
            op.token.location,
            "procedure return stack mismatch",
            source_store,
        );

        return true;
    }

    false
}

pub fn type_check_block(
    program: &Program,
    proc: &Procedure,
    body: &[Op],
    stack: &mut Vec<PorthType>,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    for op in body {
        match &op.code {
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

            OpCode::While {  body: while_body } => {
                let entry_stack = stack.clone();

                type_check_block(program, proc, &while_body.condition, stack, had_error, interner, source_store);

                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Bool])
                );

                *had_error |= compare_expected_stacks(
                    &entry_stack,
                    stack,
                    op.token.location,
                    while_body.do_token.location,
                    "while-do condition must leave the stack in the same state it entered with",
                    source_store
                );

                // Restore the stack to the state it was in before the condition.
                // We do this because the stack check may have failed.
                stack.clear();
                stack.extend_from_slice(&entry_stack);

                type_check_block(program, proc, &while_body.block, stack, had_error, interner, source_store);

                *had_error |= compare_expected_stacks(
                    &entry_stack,
                    stack,
                    op.token.location,
                    while_body.close_token.location,
                    "while-do bodies must leave the stack in the same state it entered with",
                    source_store
                );

                // Now restore the stack again do where it was prior to the loop.
                *stack = entry_stack;

            }

            OpCode::If { main, elif_blocks, else_block, open_token, end_token } => {
                let entry_stack = stack.clone();
                let mut expected_stack = stack.clone();
                let mut stack_sample_location = open_token.location;

                type_check_block(program, proc, &main.condition, stack, had_error, interner, source_store);
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Bool])
                );

                *had_error |= compare_expected_stacks(
                    &entry_stack, 
                    stack,
                    stack_sample_location,
                    main.do_token.location,
                    "if condition must leave the stack in the same state it entered with",
                    source_store
                );

                // Restore the stack to the state it was in before the condition.
                // We do this because the stack check may have failed.
                stack.clear();
                stack.extend_from_slice(&entry_stack);

                type_check_block(program, proc, &main.block,  stack, had_error, interner, source_store);

                // If we have an else-block, we should be allowed to change the state of the stack.
                // We just have to make sure all the branches leave the stack in the same state,
                // which we can do by overwriting our entry stack, since that's what we compare it to.
                if else_block.is_some() {
                    expected_stack = stack.clone();
                    stack_sample_location = main.close_token.location;
                } else {
                    *had_error |= compare_expected_stacks(
                        &expected_stack,
                        stack,
                        stack_sample_location,
                        main.close_token.location,
                        "if-block cannot change the types on the stack",
                        source_store
                    );

                }

                stack.clear();
                stack.extend_from_slice(&entry_stack);

                for elif_block in elif_blocks {
                    type_check_block(program, proc, &elif_block.condition, stack, had_error, interner, source_store);
                    stack_check!(
                        source_store,
                        had_error,
                        stack,
                        interner,
                        op,
                        kind_pat!([PorthTypeKind::Bool])
                    );

                    *had_error |= compare_expected_stacks(
                        &entry_stack, 
                        stack,
                        stack_sample_location,
                        elif_block.do_token.location,
                        "if condition must leave the stack in the same state it entered with",
                        source_store
                    );

                    // Restore the stack to the state it was in before the condition.
                    // We do this because the stack check may have failed.
                    stack.clear();
                    stack.extend_from_slice(&entry_stack);

                    type_check_block(program, proc, &elif_block.block,  stack, had_error, interner, source_store);

                    *had_error |= compare_expected_stacks(
                        &expected_stack,
                        stack,
                        stack_sample_location,
                        elif_block.close_token.location,
                        "all if-elif-else blocks cannot change the types on the stack",
                        source_store
                    );

                    stack.clear();
                    stack.extend_from_slice(&entry_stack);
                }

                if let Some(else_block) = else_block.as_ref() {
                    type_check_block(program, proc, else_block, stack, had_error, interner, source_store);

                    *had_error |= compare_expected_stacks(
                        &expected_stack, 
                        stack,
                        stack_sample_location,
                        end_token.location,
                        "else-block cannot change the types on the stack",
                        source_store
                    );

                    stack.clear();
                    stack.extend_from_slice(&entry_stack);
                }

                *stack = expected_stack;
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
                    *had_error = true;
                    // We don't know what was expected, but we need something there.
                    stack.push(PorthType::new(PorthTypeKind::Unknown, op.token.location));
                } else {
                    let ty = stack[stack.len() - 1 - depth];
                    stack.push(ty);
                }
            }
            OpCode::DupPair => match stack.as_slice() {
                [.., a, b] => {
                    let a = *a;
                    let b = *b;
                    stack.extend_from_slice(&[a, b]);
                }
                [a] => {
                    let a = *a;
                    generate_stack_exhaustion(source_store, op, stack.len(), op.code.pop_count());
                    *had_error = true;
                    stack.extend_from_slice(&[
                        PorthType::new(PorthTypeKind::Unknown, op.token.location),
                        a,
                    ]);
                }
                [] => {
                    generate_stack_exhaustion(source_store, op, 0, op.code.pop_count());
                    *had_error = true;
                    stack.extend_from_slice(&[
                        PorthType::new(PorthTypeKind::Unknown, op.token.location),
                        PorthType::new(PorthTypeKind::Unknown, op.token.location),
                    ]);
                }
            },
            OpCode::Rot => {
                match stack.as_slice() {
                    [.., _, _, _] => {}
                    _ => {
                        generate_stack_exhaustion(
                            source_store,
                            op,
                            stack.len(),
                            op.code.pop_count(),
                        );
                        *had_error = true;
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
                    *had_error = true;
                    stack.resize(2, PorthType::new(PorthTypeKind::Unknown, op.token.location));
                }
            },

            OpCode::Load{ kind, .. } => {
                stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([PorthTypeKind::Ptr])
                );
                stack.push(PorthType::new(*kind, op.token.location));
            }
            OpCode::Store{ kind, .. } => {
                let res = stack_check!(
                    source_store,
                    had_error,
                    stack,
                    interner,
                    op,
                    kind_pat!([_, PorthTypeKind::Ptr])
                );

                match res {
                    Some([store_kind, _]) if store_kind.kind != *kind && store_kind.kind != PorthTypeKind::Unknown => {
                        *had_error = true;
                        let lexeme = interner.resolve_lexeme(op.token.lexeme);
                        generate_type_mismatch(source_store, lexeme, op, &[store_kind]);
                    }
                    _ => {}
                }
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
                let referenced_proc = program.get_proc(*proc_id);

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
                            *had_error = true;
                            stack.clear();
                        } else {
                            let last_n = stack.lastn(referenced_proc.entry_stack().len()).unwrap();
                            if last_n != referenced_proc.entry_stack() {
                                failed_compare_stack_types(
                                    referenced_proc.entry_stack(),
                                    last_n,
                                    referenced_proc.name().location,
                                    op.token.location,
                                    "incorrect types on stack",
                                    source_store,
                                );
                                *had_error = true;
                            }
                            stack.truncate(stack.len() - referenced_proc.entry_stack().len());
                        }

                        stack.extend_from_slice(referenced_proc.exit_stack());
                    }
                }
            }

            OpCode::Epilogue | OpCode::Prologue => {}
            OpCode::Return => {
                *had_error |= final_stack_check(proc, Some(op), stack, source_store);
            }

            OpCode::SysCall(num_args @ 0..=6) => {
                let required = num_args + 1; //
                if stack.len() < required {
                    generate_stack_exhaustion(source_store, op, stack.len(), required);
                    *had_error = true;
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
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }
}

pub fn type_check(
    program: &Program,
    proc: &Procedure,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut stack: Vec<PorthType> = proc.entry_stack().to_owned();
    let mut had_error = false;

    type_check_block(
        program,
        proc,
        proc.body(),
        &mut stack,
        &mut had_error,
        interner,
        source_store,
    );

    had_error |= final_stack_check(proc, None, &stack, source_store);

    had_error.not().then(|| ()).ok_or(())
}
