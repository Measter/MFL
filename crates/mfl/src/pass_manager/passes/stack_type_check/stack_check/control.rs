use std::cmp::Ordering;

use ariadne::{Color, Label};

use crate::{
    context::{Context, ItemId},
    diagnostics::{self, build_creator_label_chain},
    ir::{Op, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::{Analyzer, ValueId},
    Stores,
};

pub(crate) fn epilogue_return(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    item_id: ItemId,
) {
    let item_header = ctx.get_item_header(item_id);
    let item_sig = ctx.urir().get_item_signature(item_id);

    let exit_sig = &item_sig.exit.inner;
    if stack.len() == exit_sig.len() {
        let inputs = stack.lastn(exit_sig.len()).unwrap();

        for &value_id in inputs {
            analyzer.consume_value(value_id, op.id);
        }
        analyzer.set_op_io(op, inputs, &[]);
        let len = inputs.len();
        stack.truncate(stack.len() - len);

        return;
    }

    *had_error = true;

    let mut labels = vec![
        Label::new(op.token.location)
            .with_color(Color::Red)
            .with_message("returning here"),
        Label::new(item_sig.exit.location)
            .with_color(Color::Cyan)
            .with_message("return type defined here"),
    ];

    match stack.len().cmp(&exit_sig.len()) {
        Ordering::Less => {
            let num_missing = usize::saturating_sub(exit_sig.len(), stack.len());
            for _ in 0..num_missing {
                let pad_value = analyzer.new_value(op.token.location, None);
                stack.push(pad_value);
            }
        }
        Ordering::Greater => {
            let unused_values = stack[..stack.len() - exit_sig.len()]
                .iter()
                .zip(0..)
                .map(|(&id, idx)| (id, idx, "unused value"));
            let unused_value_labels =
                build_creator_label_chain(analyzer, unused_values, Color::Green, Color::Cyan);
            labels.extend(unused_value_labels);
        }
        Ordering::Equal => unreachable!(),
    }

    diagnostics::emit_error(
        stores,
        op.token.location,
        format!(
            "function '{}' return {}, found {}",
            stores.strings.resolve(item_header.name.inner),
            exit_sig.len(),
            stack.len()
        ),
        labels,
        None,
    );
}
