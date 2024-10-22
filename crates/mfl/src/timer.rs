use std::{
    cell::RefCell,
    collections::BTreeMap,
    time::{Duration, Instant},
};

use prettytable::{row, Table};

use crate::pass_manager::PassState;

#[derive(Debug)]
struct TimerInner {
    enabled: bool,
    lexing: Duration,
    parsing: Duration,
    passes: BTreeMap<PassState, Duration>,
    compiling: Duration,
    linking: Duration,

    timer_stack: Vec<TimedFunction>,
}

pub struct TimerHandle<'a> {
    timer: &'a RefCell<TimerInner>,
}

impl<'a> TimerHandle<'a> {
    fn new(timer: &'a RefCell<TimerInner>) -> Self {
        Self { timer }
    }
}

impl Drop for TimerHandle<'_> {
    fn drop(&mut self) {
        let mut inner = self.timer.borrow_mut();

        if inner.enabled {
            let last = inner.timer_stack.pop().expect("ICE: Mismatched timer");
            let (timer_kind, final_time) = last.finish();

            for timer in &mut inner.timer_stack {
                timer.add_child_time(final_time);
            }

            match timer_kind {
                TimerKind::Lexing => inner.lexing += final_time,
                TimerKind::Parsing => inner.parsing += final_time,
                TimerKind::Pass(pass_state) => {
                    *inner.passes.entry(pass_state).or_default() += final_time;
                }
                TimerKind::Compiling => inner.compiling += final_time,
                TimerKind::Linking => inner.linking += final_time,
            }
        }
    }
}

#[derive(Debug)]
pub struct Timer {
    inner: RefCell<TimerInner>,
}

impl Timer {
    pub fn new(enabled: bool) -> Self {
        let inner = TimerInner {
            enabled,
            lexing: Duration::ZERO,
            parsing: Duration::ZERO,
            passes: BTreeMap::new(),
            compiling: Duration::ZERO,
            linking: Duration::ZERO,

            timer_stack: Vec::new(),
        };

        Self {
            inner: RefCell::new(inner),
        }
    }

    pub fn print(&self) {
        let inner = self.inner.borrow();

        let mut total = Duration::ZERO;
        let mut table = Table::new();
        table.set_format(*prettytable::format::consts::FORMAT_CLEAN);

        let mut add = |name: &str, time: Duration| {
            total += time;
            table.add_row(row![name, format!("{time:?}")]);
        };

        add("lexing", inner.lexing);
        add("parsing", inner.parsing);

        for (pass, duration) in &inner.passes {
            let name = match pass {
                PassState::BuildNames => "build names",
                PassState::CheckAsserts => "check asserts",
                PassState::ConstPropBody => "const prop",
                PassState::DeclareEnums => "declare enums",
                PassState::DeclareStructs => "declared structs",
                PassState::DefineStructs => "define structs",
                PassState::EvaluatedConstsAsserts => "evaluate consts",
                PassState::IdentResolvedBody => "ident resolve bodies",
                PassState::IdentResolvedScope => "ident resolve scopes",
                PassState::IdentResolvedSignature => "ident result signatures",
                PassState::PartiallyTypeResolved => "partially type resolve",
                PassState::StackAndTypeCheckedBody => "stack/type check",
                PassState::TerminalBlockCheckBody => "terminal block chec",
                PassState::TypeResolvedBody => "type resolve bodies",
                PassState::TypeResolvedSignature => "type resolve signatures",
                PassState::ValidityCheck => "validity check",
            };

            add(name, *duration);
        }

        add("compiling", inner.compiling);
        add("linking", inner.linking);

        table.add_empty_row();
        table.add_row(row!["total", format!("{total:?}")]);
        eprintln!("{table}");
    }

    pub fn start_compile(&self) -> TimerHandle<'_> {
        self.start(TimerKind::Compiling)
    }

    pub fn start_lex(&self) -> TimerHandle<'_> {
        self.start(TimerKind::Lexing)
    }

    pub fn start_link(&self) -> TimerHandle<'_> {
        self.start(TimerKind::Linking)
    }

    pub fn start_parse(&self) -> TimerHandle<'_> {
        self.start(TimerKind::Parsing)
    }

    pub fn start_pass(&self, pass: PassState) -> TimerHandle<'_> {
        self.start(TimerKind::Pass(pass))
    }

    fn start(&self, kind: TimerKind) -> TimerHandle {
        {
            let mut inner = self.inner.borrow_mut();
            if inner.enabled {
                inner.timer_stack.push(TimedFunction::new(kind));
            }
        }

        TimerHandle::new(&self.inner)
    }
}

#[derive(Debug)]
struct TimedFunction {
    kind: TimerKind,
    start: Instant,
    // This will be how much time child-passes took.
    to_subtract: Duration,
}

impl TimedFunction {
    fn new(kind: TimerKind) -> Self {
        Self {
            kind,
            start: Instant::now(),
            to_subtract: Duration::ZERO,
        }
    }

    fn add_child_time(&mut self, time: Duration) {
        self.to_subtract += time;
    }

    fn finish(self) -> (TimerKind, Duration) {
        (self.kind, self.start.elapsed() - self.to_subtract)
    }
}

#[derive(Debug, Clone, Copy)]
enum TimerKind {
    Lexing,
    Parsing,
    Pass(PassState),
    Compiling,
    Linking,
}
