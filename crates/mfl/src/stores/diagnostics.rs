use std::collections::BTreeMap;

use ariadne::{Color, Label, Report, ReportBuilder, ReportKind, Span};
use hashbrown::HashSet;
use intcast::IntCast;
use lasso::Spur;
use lexer::TokenKind;
use once_cell::sync::Lazy;
use prettytable::format::{LinePosition, LineSeparator, TableFormat};
use stores::{
    items::ItemId,
    source::{SourceLocation, SourceStore, Spanned},
};

use crate::ir::StructDef;

use super::{
    item::{ItemHeader, LangItem},
    ops::OpId,
    types::{TypeId, TypeInfo},
    values::{ValueId, ValueStore},
    Stores,
};

pub static TABLE_FORMAT: Lazy<TableFormat> = Lazy::new(|| {
    let mut format = TableFormat::new();
    format.padding(1, 1);
    format.column_separator('│');
    format.separators(
        &[LinePosition::Title],
        LineSeparator::new('─', '┼', '├', '┤'),
    );
    format
});

pub struct DiagnosticStore {
    detatched: Vec<Diagnostic>,
    attached: BTreeMap<ItemId, Vec<Diagnostic>>,
}

impl DiagnosticStore {
    pub fn new() -> Self {
        Self {
            detatched: Vec::new(),
            attached: BTreeMap::new(),
        }
    }

    fn add_detached(&mut self, diag: Diagnostic) {
        self.detatched.push(diag);
    }

    fn add_attached(&mut self, item_id: ItemId, diag: Diagnostic) {
        let list = self.attached.entry(item_id).or_default();
        list.push(diag);
    }
}

#[derive(Clone, Copy)]
enum DiagKind {
    Error,
    Warning,
    Advise,
}

const RED: Color = Color::Rgb(0xbd, 0x4e, 0x4a);
const YELLOW: Color = Color::Rgb(0xd3, 0xc4, 0x8a);
const GREEN: Color = Color::Rgb(0xaa, 0xcd, 0x7b);
const CYAN: Color = Color::Rgb(0x7b, 0xcb, 0xcd);

impl DiagKind {
    fn primary_label_color(self) -> Color {
        match self {
            DiagKind::Error => RED,
            DiagKind::Warning => YELLOW,
            DiagKind::Advise => CYAN,
        }
    }

    fn help_label_color(&self) -> Color {
        GREEN
    }

    fn secondary_label_color(&self) -> Color {
        YELLOW
    }

    fn chain_label_root_color(&self) -> [Color; 3] {
        [
            Color::Rgb(0xd3, 0x75, 0xb1),
            Color::Rgb(0x9d, 0x75, 0xd3),
            Color::Rgb(0x75, 0xa5, 0xd3),
        ]
    }

    fn chain_label_link_color(&self) -> [Color; 3] {
        [
            Color::Rgb(0xbc, 0x8c, 0xad),
            Color::Rgb(0x9e, 0x8c, 0xbc),
            Color::Rgb(0x8c, 0xa7, 0xbc),
        ]
    }
}

impl From<DiagKind> for ReportKind<'_> {
    fn from(val: DiagKind) -> Self {
        match val {
            DiagKind::Error => ReportKind::Error,
            DiagKind::Warning => ReportKind::Warning,
            DiagKind::Advise => ReportKind::Advice,
        }
    }
}

#[derive(Clone, Copy)]
enum LabelKind {
    Help,
    Secondary,
}

struct SimpleLabel {
    kind: LabelKind,
    location: SourceLocation,
    message: Option<String>,
}

struct ChainLabel {
    value_id: ValueId,
    idx: u64,
    description: String,
}

#[must_use]
pub struct Diagnostic {
    kind: DiagKind,
    location: SourceLocation,
    primary_message: String,
    primary_label_message: Option<String>,
    simple_labels: Vec<SimpleLabel>,
    chain_labels: Vec<ChainLabel>,
    note: Option<String>,
}

impl Diagnostic {
    pub(crate) fn error(loc: SourceLocation, message: impl Into<String>) -> Diagnostic {
        Self {
            kind: DiagKind::Error,
            location: loc,
            primary_message: message.into(),
            primary_label_message: None,
            simple_labels: Vec::new(),
            chain_labels: Vec::new(),
            note: None,
        }
    }

    pub(crate) fn warning(loc: SourceLocation, message: impl Into<String>) -> Diagnostic {
        Self {
            kind: DiagKind::Warning,
            location: loc,
            primary_message: message.into(),
            primary_label_message: None,
            simple_labels: Vec::new(),
            chain_labels: Vec::new(),
            note: None,
        }
    }

    pub(crate) fn advice(loc: SourceLocation, message: impl Into<String>) -> Diagnostic {
        Self {
            kind: DiagKind::Advise,
            location: loc,
            primary_message: message.into(),
            primary_label_message: None,
            simple_labels: Vec::new(),
            chain_labels: Vec::new(),
            note: None,
        }
    }

    pub(crate) fn primary_label_message(mut self, message: impl Into<String>) -> Self {
        self.primary_label_message = Some(message.into());
        self
    }

    pub(crate) fn add_primary_label_message(&mut self, message: impl Into<String>) -> &mut Self {
        self.primary_label_message = Some(message.into());
        self
    }

    pub(crate) fn with_help_label<M, O>(mut self, location: SourceLocation, message: O) -> Self
    where
        O: Into<Option<M>>,
        M: Into<String>,
    {
        self.add_help_label(location, message);
        self
    }

    pub(crate) fn with_secondary_label<M, O>(mut self, location: SourceLocation, message: O) -> Self
    where
        O: Into<Option<M>>,
        M: Into<String>,
    {
        self.add_secondary_label(location, message);
        self
    }

    pub(crate) fn add_help_label<M, O>(&mut self, location: SourceLocation, message: O) -> &mut Self
    where
        O: Into<Option<M>>,
        M: Into<String>,
    {
        self.simple_labels.push(SimpleLabel {
            location,
            kind: LabelKind::Help,
            message: message.into().map(Into::into),
        });
        self
    }

    pub(crate) fn add_secondary_label<M, O>(
        &mut self,
        location: SourceLocation,
        message: O,
    ) -> &mut Self
    where
        O: Into<Option<M>>,
        M: Into<String>,
    {
        self.simple_labels.push(SimpleLabel {
            location,
            kind: LabelKind::Secondary,
            message: message.into().map(Into::into),
        });
        self
    }

    pub(crate) fn with_label_chain(
        mut self,
        value_id: ValueId,
        idx: u64,
        description: impl Into<String>,
    ) -> Self {
        self.add_label_chain(value_id, idx, description);
        self
    }

    pub(crate) fn add_label_chain(
        &mut self,
        value_id: ValueId,
        idx: u64,
        description: impl Into<String>,
    ) -> &mut Self {
        self.chain_labels.push(ChainLabel {
            value_id,
            idx,
            description: description.into(),
        });

        self
    }

    pub(crate) fn with_note(mut self, message: impl Into<String>) -> Self {
        self.note = Some(message.into());
        self
    }

    pub(crate) fn set_note(&mut self, message: impl Into<String>) -> &mut Self {
        self.note = Some(message.into());
        self
    }

    pub(crate) fn attached(self, diags: &mut DiagnosticStore, item_id: ItemId) {
        diags.add_attached(item_id, self);
    }

    pub(crate) fn detached(self, diags: &mut DiagnosticStore) {
        diags.add_detached(self);
    }

    #[allow(unused)] // This function exists mostly for debugging the compiler.
    pub(crate) fn immediate(self, stores: &mut Stores) {
        display_single_diag(stores.values, stores.source, self);
    }
}

impl Diagnostic {
    pub fn bad_extern(diags: &mut DiagnosticStore, item_header: ItemHeader) {
        Diagnostic::error(
            item_header.name.location,
            format!("{} cannot be extern", item_header.kind.kind_str()),
        )
        .attached(diags, item_header.id);
    }

    pub fn bad_lang_item(
        diags: &mut DiagnosticStore,
        item_header: ItemHeader,
        lang_item: LangItem,
    ) {
        Diagnostic::error(
            item_header.name.location,
            format!(
                "{} is invalid for lang item {}",
                item_header.kind.kind_str(),
                lang_item.kind_str()
            ),
        )
        .attached(diags, item_header.id);
    }

    pub fn bad_top_level_op(
        diags: &mut DiagnosticStore,
        module_id: ItemId,
        location: SourceLocation,
        kind: TokenKind,
    ) {
        Diagnostic::error(location,
            format!("top-level can only declared `assert` `const` `import` `var` `module` `proc` or `struct`, found `{}`", kind.kind_str()),
        ).attached(diags, module_id);
    }

    pub fn field_not_found(
        stores: &mut Stores,
        item_id: ItemId,
        field_name: Spanned<Spur>,
        struct_def: &StructDef<TypeId>,
        input_struct_type_info: TypeInfo,
        input_struct_value_id: ValueId,
    ) {
        let unknown_field_name = stores.strings.resolve(field_name.inner);
        let struct_name = stores.strings.resolve(struct_def.name.inner);

        let value_type_name = stores.strings.resolve(input_struct_type_info.friendly_name);

        let diag = Diagnostic::error(
            field_name.location,
            format!("unknown field `{unknown_field_name}` in struct `{struct_name}`"),
        )
        .with_label_chain(input_struct_value_id, 1, value_type_name)
        .with_help_label(struct_def.name.location, "struct defined here");
        stores.diags.add_attached(item_id, diag);
    }

    pub fn not_a_struct(
        stores: &mut Stores,
        item_id: ItemId,
        input_struct_type_info: TypeInfo,
        input_struct_value_id: ValueId,
        op_id: OpId,
        error_str: &str,
    ) {
        let value_type_name = stores.strings.resolve(input_struct_type_info.friendly_name);
        let op_loc = stores.ops.get_token(op_id).location;

        let diag = Diagnostic::error(
            op_loc,
            format!("cannot {error_str} field of type `{value_type_name}`"),
        )
        .with_label_chain(input_struct_value_id, 1, value_type_name)
        .with_note(format!("`{value_type_name}` is not a struct"));

        stores.diags.add_attached(item_id, diag)
    }

    pub fn type_error(stores: &mut Stores, token: Spanned<Spur>) {
        Diagnostic::error(
            token.location,
            format!("unknown type `{}`", stores.strings.resolve(token.inner)),
        )
        .detached(stores.diags);
    }

    pub fn unsupported_sim_op(stores: &mut Stores, item_id: ItemId, op_id: OpId) {
        let op_location = stores.ops.get_token(op_id).location;

        Diagnostic::error(
            op_location,
            "operation not supported during const evalutation",
        )
        .attached(stores.diags, item_id);
    }
}

impl Stores<'_, '_, '_, '_, '_, '_, '_, '_, '_, '_> {
    pub fn display_diags(&mut self) {
        for diag in self.diags.detatched.drain(..) {
            display_single_diag(self.values, self.source, diag);
        }

        while let Some((_, diags)) = self.diags.attached.pop_first() {
            for diag in diags {
                display_single_diag(self.values, self.source, diag);
            }
        }
    }
}

fn display_single_diag(value_store: &ValueStore, source_store: &SourceStore, diag: Diagnostic) {
    let mut report: ReportBuilder<SourceLocation> = Report::build(
        diag.kind.into(),
        diag.location.file_id,
        diag.location.start().to_usize(),
    )
    .with_message(diag.primary_message);

    if let Some(note) = diag.note {
        report = report.with_note(note);
    }

    let mut labels = Vec::new();
    {
        let mut ariadne_label =
            Label::new(diag.location).with_color(diag.kind.primary_label_color());
        if let Some(msg) = diag.primary_label_message {
            ariadne_label = ariadne_label.with_message(msg);
        } else {
            ariadne_label = ariadne_label.with_message("here");
        }
        labels.push((ariadne_label, diag.location));
    }

    for label in diag.simple_labels {
        let color = match label.kind {
            LabelKind::Help => diag.kind.help_label_color(),
            LabelKind::Secondary => diag.kind.secondary_label_color(),
        };

        let mut ariadne_label = Label::new(label.location).with_color(color);
        if let Some(msg) = label.message {
            ariadne_label = ariadne_label.with_message(msg);
        }
        labels.push((ariadne_label, label.location));
    }

    for chain in diag.chain_labels {
        build_label_chains(value_store, &mut labels, diag.kind, &chain);
    }

    labels.sort_by_key(|(_, l)| *l);
    let num_labels = labels.len().to_i32().unwrap();
    let labels: Vec<_> = labels
        .into_iter()
        .zip((0..num_labels).rev())
        .map(|((l, _), idx)| l.with_order(idx))
        .collect();
    report.add_labels(labels);

    report.finish().eprint(source_store).unwrap();
}

fn build_label_chains(
    value_store: &ValueStore,
    labels: &mut Vec<(Label<SourceLocation>, SourceLocation)>,
    diag_kind: DiagKind,
    chain: &ChainLabel,
) {
    let creators = value_store.get_creator_tokens(chain.value_id);
    let msg = format!("{}: {}", chain.idx, chain.description);
    let mut seen = HashSet::<(bool, SourceLocation)>::new();

    for pair @ (is_root, creator) in creators {
        if seen.contains(&pair) {
            continue;
        }

        let colors = if is_root {
            diag_kind.chain_label_root_color()
        } else {
            diag_kind.chain_label_link_color()
        };
        let color = colors[chain.idx.to_usize() % colors.len()];
        labels.push((
            Label::new(creator).with_color(color).with_message(&msg),
            creator,
        ));
        seen.insert(pair);
    }
}
