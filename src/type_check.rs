use std::fmt::Write;

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
    let mut stack_depths: Vec<(usize, SourceLocation)> = Vec::new();
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

            OpCode::While { .. } => {}
            OpCode::Do { .. } | OpCode::If { .. } => {
                stack_check!(diags, stack, interner, op, [PorthType::Bool]);
                stack_depths.push((stack.len(), op.token.location));
            }
            OpCode::EndIf { .. } | OpCode::EndWhile { .. } => {
                let (open_depth, open_loc) = stack_depths
                    .pop()
                    .expect("ICE: EndWhile/EndIf requires a stack depth");

                match open_depth.cmp(&stack.len()) {
                    std::cmp::Ordering::Less => {
                        generate_block_depth_mismatch(
                            &mut diags,
                            open_loc,
                            op.token.location,
                            open_depth,
                            stack.len(),
                        );

                        stack.truncate(open_depth);
                    }
                    std::cmp::Ordering::Greater => {
                        generate_block_depth_mismatch(
                            &mut diags,
                            open_loc,
                            op.token.location,
                            open_depth,
                            stack.len(),
                        );

                        stack.resize(open_depth, PorthType::Unknown);
                    }
                    std::cmp::Ordering::Equal => {}
                }
            }
            OpCode::Else { .. } => {
                let (open_depth, open_loc) = stack_depths
                    .last()
                    .copied()
                    .expect("ICE: Else requires a stack depth");

                match open_depth.cmp(&stack.len()) {
                    std::cmp::Ordering::Less => {
                        generate_block_depth_mismatch(
                            &mut diags,
                            open_loc,
                            op.token.location,
                            open_depth,
                            stack.len(),
                        );

                        stack.truncate(open_depth);
                    }
                    std::cmp::Ordering::Greater => {
                        generate_block_depth_mismatch(
                            &mut diags,
                            open_loc,
                            op.token.location,
                            open_depth,
                            stack.len(),
                        );

                        stack.resize(open_depth, PorthType::Unknown);
                    }
                    std::cmp::Ordering::Equal => {}
                }
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
