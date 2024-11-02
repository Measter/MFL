use std::{
    collections::{BinaryHeap, HashMap},
    ffi::OsStr,
    io::{Error as IoError, ErrorKind, StdoutLock, Write},
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Output},
    sync::mpsc::{Receiver, Sender},
};

use clap::Parser;
use color_eyre::{
    eyre::{bail, Context},
    owo_colors::OwoColorize,
    Result,
};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use regex::Regex;
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

#[derive(Debug, Parser)]
struct Args {
    /// Path to the MFL compiler to execute
    #[arg(default_value = "./target/release/mfl")]
    mfl: PathBuf,

    /// Path to the directory containing the tests.
    #[arg(default_value = "./tests")]
    tests_root: PathBuf,

    /// Path to where the stdout and stderr outputs are stored.
    #[arg(default_value = "./test_results")]
    output_root: PathBuf,

    /// Generate the outputs rather than read.
    #[clap(short)]
    generate: bool,

    /// Filter the run tests with the given regexs.
    #[clap(short)]
    filter: Vec<String>,

    /// Set the output style. 0 = check list, 1 = short, 2 = long, 3 = print streams
    #[clap(short = 's', action = clap::ArgAction::Count)]
    output_style: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
enum RunStatus {
    Ok,
    Error,
}

impl From<ExitStatus> for RunStatus {
    fn from(value: ExitStatus) -> Self {
        if value.success() {
            RunStatus::Ok
        } else {
            RunStatus::Error
        }
    }
}

#[derive(Debug)]
enum PostFnResult {
    Ok,
    NotEqual {
        stdout: Vec<diff::Result<String>>,
        stderr: Vec<diff::Result<String>>,
    },
    Missing,
    Other(IoError),
}

#[derive(Debug, Serialize, Deserialize)]
struct RunTestConfig {
    #[serde(rename = "expected")]
    expected_result: RunStatus,
    #[serde(rename = "args", default)]
    command_args: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct TestConfig {
    #[serde(rename = "compile")]
    compile_test: RunTestConfig,
    #[serde(rename = "run", default)]
    run_tests: HashMap<String, RunTestConfig>,
}

#[derive(Debug)]
struct Test {
    cfg: RunTestConfig,
    name: String,
}

#[derive(Debug)]
struct TestGroup {
    id: usize,
    path: PathBuf,
    name: String,
    compile: Test,
    run_tests: Vec<Test>,
    skip: bool,
}

#[derive(Debug, Default)]
struct ResultCounts {
    total: usize,
    passed: usize,
    skipped: usize,
    failed: usize,
}

impl ResultCounts {
    fn add_result(
        &mut self,
        actual_result: RunStatus,
        expected_result: RunStatus,
        post_fn_result: &PostFnResult,
    ) {
        self.total += 1;

        if actual_result == expected_result && matches!(post_fn_result, PostFnResult::Ok) {
            self.passed += 1;
        } else {
            self.failed += 1;
        }
    }

    fn skip(&mut self) {
        self.total += 1;
        self.skipped += 1;
    }

    fn merge(self, rhs: Self) -> Self {
        Self {
            total: self.total + rhs.total,
            passed: self.passed + rhs.passed,
            skipped: self.skipped + rhs.skipped,
            failed: self.failed + rhs.failed,
        }
    }
}

enum TestRunResult<'a> {
    Run {
        command: Output,
        command_result: RunStatus,
        test: &'a Test,
        post_fn_result: PostFnResult,
    },
    Skipped {
        test: &'a Test,
    },
}

struct TestGroupResult<'a> {
    id: usize,
    group_name: &'a str,
    results: Vec<TestRunResult<'a>>,
}

impl Ord for TestGroupResult<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.id.cmp(&self.id)
    }
}

impl PartialOrd for TestGroupResult<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for TestGroupResult<'_> {}

impl PartialEq for TestGroupResult<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

fn read_test(args: &Args, path: &Path) -> Result<Option<TestGroup>> {
    let test_source = std::fs::read_to_string(path)?;

    let mut cfg_toml = String::new();
    let mut is_in_cfg = false;
    for raw_line in test_source.lines() {
        let line = raw_line.trim().trim_start_matches("//").trim_start();
        if line == "CFG" {
            is_in_cfg = true;
        } else if line == "END" {
            break;
        } else if is_in_cfg {
            cfg_toml.push_str(line);
            cfg_toml.push('\n');
        }
    }

    if cfg_toml.is_empty() {
        return Ok(None);
    }

    let config: TestConfig = toml::from_str(&cfg_toml)?;

    let test_name = path
        .strip_prefix(&args.tests_root)
        .unwrap()
        .with_extension("");

    let compile_test = Test {
        cfg: config.compile_test,
        name: "compile".to_owned(),
    };

    let mut run_tests = Vec::new();

    for (name, cfg) in config.run_tests {
        run_tests.push(Test { cfg, name });
    }

    Ok(Some(TestGroup {
        id: 0,
        compile: compile_test,
        name: test_name.display().to_string(),
        path: test_name,
        run_tests,
        skip: false,
    }))
}

fn get_tests(args: &Args) -> Result<Vec<TestGroup>> {
    let mut tests = Vec::new();

    for entry in WalkDir::new(&args.tests_root) {
        let entry = entry?;
        if !entry.metadata()?.is_file() {
            continue;
        }

        if entry.path().extension() == Some(OsStr::new("mfl")) {
            let Some(mut test_case) = read_test(args, entry.path())
                .with_context(|| format!("error reading test `{}`", entry.path().display()))?
            else {
                continue;
            };

            test_case.id = tests.len();
            tests.push(test_case);
        }
    }

    Ok(tests)
}

fn store_streams(args: &Args, group_name: &Path, test_name: &str, output: &Output) -> PostFnResult {
    let root_name = args.output_root.join(group_name);
    if let Err(e) = std::fs::create_dir_all(root_name.parent().unwrap()) {
        return PostFnResult::Other(e);
    };

    if let Err(e) = std::fs::write(
        root_name.with_extension(format!("{test_name}.stdout")),
        &output.stdout,
    ) {
        return PostFnResult::Other(e);
    }

    if let Err(e) = std::fs::write(
        root_name.with_extension(format!("{test_name}.stderr")),
        &output.stderr,
    ) {
        return PostFnResult::Other(e);
    }

    PostFnResult::Ok
}

fn compare_streams(
    args: &Args,
    group_name: &Path,
    test_name: &str,
    output: &Output,
) -> PostFnResult {
    let root_name = args.output_root.join(group_name);

    let prev_stdout = match std::fs::read(root_name.with_extension(format!("{test_name}.stdout"))) {
        Ok(v) => v,
        Err(e) if e.kind() == ErrorKind::NotFound => {
            return PostFnResult::Missing;
        }
        Err(e) => return PostFnResult::Other(e),
    };

    let prev_stderr = match std::fs::read(root_name.with_extension(format!("{test_name}.stderr"))) {
        Ok(v) => v,
        Err(e) if e.kind() == ErrorKind::NotFound => {
            return PostFnResult::Missing;
        }
        Err(e) => return PostFnResult::Other(e),
    };

    if prev_stdout != output.stdout || prev_stderr != output.stderr {
        let stdout_diff = build_diff(&prev_stdout, &output.stdout);
        let stderr_diff = build_diff(&prev_stderr, &output.stderr);
        PostFnResult::NotEqual {
            stdout: stdout_diff,
            stderr: stderr_diff,
        }
    } else {
        PostFnResult::Ok
    }
}

fn run_command(command: impl AsRef<OsStr>, pre_args: &[&OsStr], test: &Test) -> Result<Output> {
    let test_command = Command::new(command)
        .args(pre_args)
        .args(&test.cfg.command_args)
        .output()?;

    Ok(test_command)
}

fn build_diff(prev_stream: &[u8], new_stream: &[u8]) -> Vec<diff::Result<String>> {
    let left = std::str::from_utf8(prev_stream).unwrap();
    let right = std::str::from_utf8(new_stream).unwrap();

    diff::lines(left, right)
        .into_iter()
        .map(|res| {
            use diff::Result::*;
            match res {
                Left(l) => Left(l.into()),
                Both(l, r) => Both(l.into(), r.into()),
                Right(r) => Right(r.into()),
            }
        })
        .collect()
}

fn print_result_group(
    stdout: &mut StdoutLock,
    result_group: &TestGroupResult,
    output_style: u8,
) -> Result<()> {
    let print_group_name = output_style > 0;
    let post_group_new_line = output_style > 0;
    let print_subtest_name = output_style > 1;
    let post_subtest_new_line = output_style > 1;
    let verbose_result_mark = output_style > 1;
    let print_diff_streams = output_style > 1;
    let print_streams = output_style > 2;

    if print_group_name {
        let newline = if print_subtest_name { "\n" } else { "" };
        write!(stdout, "{} {}", result_group.group_name, newline)?;
    }

    for sub_test in &result_group.results {
        match sub_test {
            TestRunResult::Skipped { test } => {
                if print_subtest_name {
                    write!(stdout, "  {} ", test.name)?;
                }
                let mark = if verbose_result_mark { "SKIPPED" } else { "o" };
                write!(stdout, "{}", mark.yellow())?;
                if post_subtest_new_line {
                    writeln!(stdout)?;
                }
            }
            TestRunResult::Run {
                command,
                command_result,
                test,
                post_fn_result,
            } => {
                if print_subtest_name {
                    write!(stdout, "  {} ", test.name)?;
                }

                let mut diffs = Vec::new();

                let mark = if *command_result != test.cfg.expected_result {
                    if verbose_result_mark {
                        format!(
                            "{}: Expected {:?} got {:?}",
                            "FAIL".red(),
                            test.cfg.expected_result,
                            command_result
                        )
                    } else {
                        "x".red().to_string()
                    }
                } else {
                    match post_fn_result {
                        PostFnResult::Ok => {
                            if verbose_result_mark {
                                "PASS".green().to_string()
                            } else {
                                "✓".green().to_string()
                            }
                        }
                        PostFnResult::NotEqual { stdout, stderr } => {
                            for (name, stream) in [("STDOUT", stdout), ("STDERR", stderr)] {
                                if !stream.is_empty() {
                                    diffs.push(format!("    -- {name} --"));
                                    for d in stream {
                                        match d {
                                            diff::Result::Left(l) => {
                                                diffs.push(format!(
                                                    "    {} {}",
                                                    "-".bright_black(),
                                                    l
                                                ));
                                            }
                                            diff::Result::Right(l) => {
                                                diffs.push(format!(
                                                    "    {} {}",
                                                    "+".bright_white(),
                                                    l
                                                ));
                                            }
                                            diff::Result::Both(_, _) => {}
                                        }
                                    }
                                }
                                diffs.push(String::new());
                            }
                            if verbose_result_mark {
                                format!("{}: Test output changed", "FAIL".red())
                            } else {
                                "x".red().to_string()
                            }
                        }

                        PostFnResult::Missing => {
                            if verbose_result_mark {
                                format!("{}: Previous output not found", "Missing".magenta())
                            } else {
                                "m".magenta().to_string()
                            }
                        }
                        PostFnResult::Other(e) => {
                            if verbose_result_mark {
                                format!("{}: Output error - {}", "Error".red(), e)
                            } else {
                                "x".red().to_string()
                            }
                        }
                    }
                };

                write!(stdout, "{mark}",)?;

                if print_diff_streams {
                    if !diffs.is_empty() {
                        writeln!(stdout)?;
                    }
                    for line in diffs {
                        writeln!(stdout, "{line}")?;
                    }
                }

                if print_streams {
                    for (name, stream) in [("STDOUT", &command.stdout), ("STDERR", &command.stderr)]
                    {
                        if !stream.is_empty() {
                            writeln!(stdout)?;
                            writeln!(stdout, "    -- {name} --")?;
                            std::str::from_utf8(stream).unwrap().lines().try_for_each(
                                |line| -> Result<()> {
                                    writeln!(stdout, "    {line}")?;
                                    Ok(())
                                },
                            )?;
                        }
                    }
                }

                if post_subtest_new_line {
                    writeln!(stdout)?;
                }
            }
        }
    }

    if post_group_new_line {
        writeln!(stdout)?;
    }
    stdout.flush()?;

    Ok(())
}

fn run_single_test<'a>(
    sender: Sender<TestGroupResult<'a>>,
    test_group: &'a TestGroup,
    build_path: &Path,
    args: &Args,
    post_test_fn: fn(&Args, &Path, &str, &Output) -> PostFnResult,
) -> ResultCounts {
    fn run_impl<'a>(
        sender: Sender<TestGroupResult<'a>>,
        test_group: &'a TestGroup,
        build_path: &Path,
        args: &Args,
        post_test_fn: fn(&Args, &Path, &str, &Output) -> PostFnResult,
        counts: &mut ResultCounts,
    ) -> Result<(), color_eyre::Report> {
        if test_group.skip {
            counts.skip();
            for _ in &test_group.run_tests {
                counts.skip();
            }

            return Ok(());
        }

        let mut test_results = Vec::new();

        let test_dir = build_path.join(&test_group.path);
        let objdir = test_dir.join("obj");
        let output_binary = test_dir.join("program");
        let mut mfl_file = args.tests_root.join(&test_group.path);

        mfl_file.set_extension("mfl");
        let objdir = objdir.as_os_str();
        let output_binary = output_binary.as_os_str();
        let mfl_file = mfl_file.as_os_str();

        let compiler_args = [
            OsStr::new("--obj"),
            objdir,
            OsStr::new("-o"),
            output_binary,
            mfl_file,
        ];

        let test_command = run_command(&args.mfl, &compiler_args, &test_group.compile)?;
        let post_fn_result = post_test_fn(args, &test_group.path, "compile", &test_command);
        let command_result: RunStatus = test_command.status.into();

        counts.add_result(
            command_result,
            test_group.compile.cfg.expected_result,
            &post_fn_result,
        );

        let skip_run = command_result == RunStatus::Error
            || test_group.compile.cfg.expected_result == RunStatus::Error
            || !matches!(post_fn_result, PostFnResult::Ok | PostFnResult::Missing);

        test_results.push(TestRunResult::Run {
            command: test_command,
            command_result,
            test: &test_group.compile,
            post_fn_result,
        });

        for run in &test_group.run_tests {
            if skip_run {
                counts.skip();
                test_results.push(TestRunResult::Skipped { test: run });
                continue;
            }

            let test_command = run_command(output_binary, &[], run)?;
            let command_result: RunStatus = test_command.status.into();
            let post_fn_result = post_test_fn(args, &test_group.path, &run.name, &test_command);

            counts.add_result(command_result, run.cfg.expected_result, &post_fn_result);

            test_results.push(TestRunResult::Run {
                command: test_command,
                command_result,
                test: run,
                post_fn_result,
            });
        }

        sender
            .send(TestGroupResult {
                id: test_group.id,
                group_name: &test_group.name,
                results: test_results,
            })
            .unwrap();

        Ok(())
    }

    let mut counts = ResultCounts::default();

    if let Err(e) = run_impl(
        sender,
        test_group,
        build_path,
        args,
        post_test_fn,
        &mut counts,
    ) {
        eprintln!();
        eprintln!("{e}");
    }

    counts
}

fn result_printer_thread(
    receiver: Receiver<TestGroupResult>,
    expected_ids: Vec<usize>,
    output_style: u8,
) {
    let mut stdout = std::io::stdout().lock();
    let mut queue = BinaryHeap::new();
    let mut expected_ids = expected_ids.into_iter().peekable();

    for result_group in receiver.iter() {
        queue.push(result_group);

        while queue.peek().is_some() && queue.peek().map(|rg| rg.id) == expected_ids.peek().copied()
        {
            expected_ids.next();
            let result_group = queue.pop().unwrap();
            print_result_group(&mut stdout, &result_group, output_style).unwrap();
        }
    }
}

fn run_all_tests(
    args: &Args,
    expected_ids: Vec<usize>,
    tests: &[TestGroup],
    post_test_fn: fn(&Args, &Path, &str, &Output) -> PostFnResult,
) -> Result<ResultCounts> {
    let temp_dir = tempfile::tempdir()?;

    let counts = std::thread::scope(|scope| {
        let (sender, receiver) = std::sync::mpsc::channel::<TestGroupResult>();
        scope.spawn(|| result_printer_thread(receiver, expected_ids, args.output_style));

        tests
            .par_iter()
            .map(|test| run_single_test(sender.clone(), test, temp_dir.path(), args, post_test_fn))
            .reduce(ResultCounts::default, |a, b| a.merge(b))
    });

    Ok(counts)
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let args = Args::parse();

    if !args.mfl.exists() {
        bail!("MFL compiler not found at `{}`", args.mfl.display());
    }

    if !args.tests_root.exists() {
        bail!("Tests not found at `{}`", args.tests_root.display());
    }

    let mut tests = get_tests(&args)?;
    if tests.is_empty() {
        return Ok(());
    }

    let filters: Vec<_> = args
        .filter
        .iter()
        .map(|f| Regex::new(f))
        .collect::<Result<_, _>>()?;

    let mut expected_ids = Vec::new();
    if !filters.is_empty() {
        tests.iter_mut().for_each(|test_group| {
            let is_skip = filters
                .iter()
                .all(|filter| !filter.is_match(&test_group.name));

            test_group.skip |= is_skip;
            if !is_skip {
                expected_ids.push(test_group.id);
            }
        });
    }

    if tests.is_empty() {
        println!("No tests to run");
    }

    let counts = if args.generate {
        println!("Generating test output");
        println!();
        run_all_tests(&args, expected_ids, &tests, store_streams)?
    } else {
        println!("Running tests");
        println!();
        run_all_tests(&args, expected_ids, &tests, compare_streams)?
    };

    if !args.generate {
        println!();
        println!("------");
        println!(
            "Summary: {} tests, {} {}, {} {}, {} {}",
            counts.total.bright_white(),
            counts.passed.bright_white(),
            "passed".green(),
            counts.skipped.bright_white(),
            "skipped".yellow(),
            counts.failed.bright_white(),
            "failed".red()
        );
    }

    Ok(())
}
