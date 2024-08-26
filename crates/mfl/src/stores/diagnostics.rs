use ariadne::{Color, Label, Report, ReportBuilder, ReportKind, Span};
use hashbrown::HashMap;
use intcast::IntCast;
use stores::{
    items::ItemId,
    source::{SourceLocation, SourceStore},
};

use super::{
    values::{ValueId, ValueStore},
    Stores,
};

pub struct DiagnosticStore {
    detatched: Vec<Diagnostic>,
    attached: HashMap<ItemId, Vec<Diagnostic>>,
}

impl DiagnosticStore {
    pub fn new() -> Self {
        Self {
            detatched: Vec::new(),
            attached: HashMap::new(),
        }
    }

    pub fn add_detached(&mut self, diag: Diagnostic) {
        self.detatched.push(diag);
    }
}

#[derive(Clone, Copy)]
enum DiagKind {
    Error,
    Warning,
    Advise,
}

impl DiagKind {
    fn primary_label_color(self) -> Color {
        match self {
            DiagKind::Error => Color::Red,
            DiagKind::Warning => Color::Yellow,
            DiagKind::Advise => Color::Green,
        }
    }

    fn secondary_label_color(&self) -> Color {
        match self {
            DiagKind::Error => Color::Yellow,
            DiagKind::Warning | DiagKind::Advise => Color::Cyan,
        }
    }

    fn help_label_color(&self) -> Color {
        Color::Cyan
    }

    fn chain_label_root_color(&self) -> Color {
        match self {
            DiagKind::Error => Color::Yellow,
            DiagKind::Warning | DiagKind::Advise => Color::Cyan,
        }
    }

    fn chain_label_chained_color(&self) -> Color {
        match self {
            DiagKind::Error => Color::Cyan,
            DiagKind::Warning | DiagKind::Advise => Color::Green,
        }
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
    Secondary,
    Help,
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
    pub(crate) fn new_error(op_loc: SourceLocation, message: impl Into<String>) -> Diagnostic {
        Self {
            kind: DiagKind::Error,
            location: op_loc,
            primary_message: message.into(),
            primary_label_message: None,
            simple_labels: Vec::new(),
            chain_labels: Vec::new(),
            note: None,
        }
    }

    pub(crate) fn primary_label_message(&mut self, message: impl Into<String>) -> &mut Self {
        self.primary_label_message = Some(message.into());
        self
    }

    pub(crate) fn with_label<M, O>(&mut self, location: SourceLocation, message: O) -> &mut Self
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

    pub(crate) fn with_help_label<M, O>(
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
            kind: LabelKind::Help,
            message: message.into().map(Into::into),
        });
        self
    }

    pub(crate) fn with_label_chain(
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

    pub(crate) fn with_note(&mut self, message: impl Into<String>) -> &mut Self {
        self.note = Some(message.into());
        self
    }
}

impl Stores<'_, '_, '_, '_, '_, '_, '_, '_, '_> {
    pub fn display_diags(&mut self) {
        for diag in self.diags.detatched.drain(..) {
            display_single_diag(self.values, self.source, diag);
        }

        for (_, diags) in self.diags.attached.drain() {
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
        }
        labels.push((ariadne_label, diag.location));
    }

    for label in diag.simple_labels {
        let color = match label.kind {
            LabelKind::Secondary => diag.kind.secondary_label_color(),
            LabelKind::Help => diag.kind.help_label_color(),
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
    let mut creators = value_store.get_creator_token(chain.value_id);
    let msg = format!("{}: {}", chain.idx, chain.description);

    let root = creators.pop().unwrap();
    labels.push((
        Label::new(root)
            .with_color(diag_kind.chain_label_root_color())
            .with_message(&msg),
        root,
    ));
    for creator in creators {
        labels.push((
            Label::new(creator)
                .with_color(diag_kind.chain_label_chained_color())
                .with_message(&msg),
            creator,
        ));
    }
}
