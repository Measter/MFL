use std::{
    collections::HashMap,
    ffi::OsStr,
    io::{Error as IoError, ErrorKind},
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Output},
};

use clap::Parser;
use color_eyre::{
    eyre::{bail, Context},
    owo_colors::OwoColorize,
    Result,
};
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

    /// Force long-style output.
    #[clap(long)]
    long: bool,

    /// Always print full STDOUT and STDERR streams
    #[clap(long)]
    print_streams: bool,
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
struct Tests {
    path: PathBuf,
    name: String,
    compile: Test,
    run: Vec<Test>,
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

fn read_test(args: &Args, path: &Path) -> Result<Option<Tests>> {
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

    Ok(Some(Tests {
        compile: compile_test,
        name: test_name.display().to_string(),
        path: test_name,
        run: run_tests,
    }))
}

fn get_tests(args: &Args) -> Result<Vec<Tests>> {
    let mut tests = Vec::new();

    for entry in WalkDir::new(&args.tests_root) {
        let entry = entry?;
        if !entry.metadata()?.is_file() {
            continue;
        }

        if entry.path().extension() == Some(OsStr::new("mfl")) {
            let Some(test_case) = read_test(args, entry.path())
                .with_context(|| format!("error reading test `{}`", entry.path().display()))? else
            {
                continue;
            };

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

fn print_result(
    output: &Output,
    actual_result: RunStatus,
    expected_result: RunStatus,
    post_fn_result: PostFnResult,
    force_print_full_streams: bool,
) {
    let print_streams = || {
        for (name, stream) in [("STDOUT", &output.stdout), ("STDERR", &output.stderr)] {
            if !stream.is_empty() {
                println!("    -- {name} --");
                std::str::from_utf8(stream)
                    .unwrap()
                    .lines()
                    .for_each(|line| println!("    {line}",));
            }
            println!();
        }
    };

    if actual_result != expected_result {
        println!(
            "{}: Expected {expected_result:?} got {actual_result:?}",
            "FAIL".red()
        );

        print_streams();

        return;
    }

    match post_fn_result {
        PostFnResult::Ok => println!("{}", "PASS".green()),
        PostFnResult::NotEqual { stdout, stderr } => {
            println!("{}: Test output changed", "FAIL".red());
            for (name, stream) in [("STDOUT", stdout), ("STDERR", stderr)] {
                if !stream.is_empty() {
                    println!("    -- {name} --");
                    for d in stream {
                        match d {
                            diff::Result::Left(l) => println!("    {} {}", "-".bright_black(), l),
                            diff::Result::Right(l) => println!("    {} {}", "+".bright_white(), l),
                            diff::Result::Both(_, _) => {}
                        }
                    }
                }
                println!();
            }
        }
        PostFnResult::Missing => println!("{}: Previous output not found", "Error".red()),
        PostFnResult::Other(e) => println!("{}: Output error - {}", "Error".red(), e),
    }

    if force_print_full_streams {
        print_streams();
    }
}

fn run_single_test(
    test: &Tests,
    temp_dir: &tempfile::TempDir,
    args: &Args,
    post_test_fn: fn(&Args, &Path, &str, &Output) -> PostFnResult,
    counts: &mut ResultCounts,
) -> Result<(), color_eyre::Report> {
    print!("{}", test.name);

    let mut test_results = Vec::new();
    let mut short_output = !args.long;

    let test_dir = temp_dir.path().join(&test.path);
    let objdir = test_dir.join("obj");
    let output_binary = test_dir.join("program");
    let mut mfl_file = args.tests_root.join(&test.path);

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

    let test_command = run_command(&args.mfl, &compiler_args, &test.compile)?;
    let post_fn_result = post_test_fn(args, &test.path, "compile", &test_command);
    let command_result: RunStatus = test_command.status.into();
    short_output &= command_result == test.compile.cfg.expected_result
        && matches!(post_fn_result, PostFnResult::Ok);

    counts.add_result(
        command_result,
        test.compile.cfg.expected_result,
        &post_fn_result,
    );

    let skip_run = command_result == RunStatus::Error
        || test.compile.cfg.expected_result == RunStatus::Error
        || !matches!(post_fn_result, PostFnResult::Ok);

    test_results.push(TestRunResult::Run {
        command: test_command,
        command_result,
        test: &test.compile,
        post_fn_result,
    });

    for run in &test.run {
        if !skip_run {
            let test_command = run_command(output_binary, &[], run)?;
            let command_result: RunStatus = test_command.status.into();
            let post_fn_result = post_test_fn(args, &test.path, &run.name, &test_command);

            short_output &= command_result == run.cfg.expected_result
                && matches!(post_fn_result, PostFnResult::Ok);

            counts.add_result(command_result, run.cfg.expected_result, &post_fn_result);

            test_results.push(TestRunResult::Run {
                command: test_command,
                command_result,
                test: run,
                post_fn_result,
            });
        } else {
            counts.skip();
            test_results.push(TestRunResult::Skipped { test: run });
        }
    }

    if short_output {
        let checks: String = "✓".repeat(1 + test.run.len());
        println!(" {}", checks.green());
    } else {
        println!();
        for result in test_results {
            match result {
                TestRunResult::Run {
                    command,
                    command_result,
                    test,
                    post_fn_result,
                } => {
                    print!("  {} ", test.name);
                    print_result(
                        &command,
                        command_result,
                        test.cfg.expected_result,
                        post_fn_result,
                        args.print_streams,
                    );
                }
                TestRunResult::Skipped { test } => {
                    println!("  {} {}", test.name, "Skipped".yellow());
                }
            }
        }
    }

    Ok(())
}

fn run_all_tests(
    args: &Args,
    tests: &[Tests],
    post_test_fn: fn(&Args, &Path, &str, &Output) -> PostFnResult,
) -> Result<ResultCounts> {
    let mut counts = ResultCounts::default();
    let temp_dir = tempfile::tempdir()?;

    for test in tests {
        run_single_test(test, &temp_dir, args, post_test_fn, &mut counts)?;
    }

    Ok(counts)
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let mut args = Args::parse();

    if !args.mfl.exists() {
        bail!("MFL compiler not found at `{}`", args.mfl.display());
    }

    if !args.tests_root.exists() {
        bail!("Tests not found at `{}`", args.tests_root.display());
    }

    // Print streams should imply long-style
    args.long |= args.print_streams;

    let mut tests = get_tests(&args)?;
    if tests.is_empty() {
        return Ok(());
    }

    let filters: Vec<_> = args
        .filter
        .iter()
        .map(|f| Regex::new(f))
        .collect::<Result<_, _>>()?;

    if !filters.is_empty() {
        tests.retain(|test| filters.iter().any(|filter| filter.is_match(&test.name)));
    }

    if tests.is_empty() {
        println!("No tests to run");
    }

    let counts = if args.generate {
        println!("Generating test output");
        println!();
        run_all_tests(&args, &tests, store_streams)?
    } else {
        let count: usize = tests.iter().map(|t| 1 + t.run.len()).sum();
        println!("Running {count} tests");
        println!();
        run_all_tests(&args, &tests, compare_streams)?
    };

    if !args.generate {
        println!();
        println!("------");
        println!(
            "Summary: {} tests run, {} {}, {} {}, {} {}",
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
