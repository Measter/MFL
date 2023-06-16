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
    name: PathBuf,
    compile: Test,
    run: Vec<Test>,
}

fn read_test(args: &Args, path: &Path) -> Result<Option<Tests>> {
    let config_toml = std::fs::read_to_string(path)?;
    let config: TestConfig = toml::from_str(&config_toml)?;

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
        name: test_name,
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

        if entry.path().extension() == Some(OsStr::new("toml")) {
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

fn run_test(command: impl AsRef<OsStr>, pre_args: &[&OsStr], test: &Test) -> Result<Output> {
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
    actual_result: RunStatus,
    expected_result: RunStatus,
    post_fn_result: PostFnResult,
) {
    let print_diffs = |stdout: Vec<diff::Result<String>>, stderr| {
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
    };

    if actual_result != expected_result {
        println!(
            "{}: Expected {expected_result:?} got {actual_result:?}",
            "Error".red()
        );

        if let PostFnResult::NotEqual { stdout, stderr } = post_fn_result {
            print_diffs(stdout, stderr);
        }

        return;
    }

    match post_fn_result {
        PostFnResult::Ok => println!("{}", "Ok".green()),
        PostFnResult::NotEqual { stdout, stderr } => {
            println!("{}: Test output changed", "Error".red());
            print_diffs(stdout, stderr);
        }
        PostFnResult::Missing => println!("{}: Previous output not found", "Error".red()),
        PostFnResult::Other(e) => println!("{}: Output error - {}", "Error".red(), e),
    }
}

fn run_all_tests(
    args: &Args,
    tests: &[Tests],
    post_test_fn: fn(&Args, &Path, &str, &Output) -> PostFnResult,
) -> Result<()> {
    let temp_dir = tempfile::tempdir()?;

    for test in tests {
        println!("{}", test.name.display());

        let test_dir = temp_dir.path().join(&test.name);
        let objdir = test_dir.join("obj");
        let output_binary = test_dir.join("program");

        let mut mfl_file = args.tests_root.join(&test.name);
        mfl_file.set_extension("mfl");

        // We need all the compile paths to be OsStr..
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

        print!("  compile ");
        let test_command = run_test(&args.mfl, &compiler_args, &test.compile)?;
        let post_fn_result = post_test_fn(args, &test.name, "compile", &test_command);
        let command_result: RunStatus = test_command.status.into();

        let skip_run = command_result == RunStatus::Error
            || test.compile.cfg.expected_result == RunStatus::Error
            || !matches!(post_fn_result, PostFnResult::Ok);

        print_result(
            command_result,
            test.compile.cfg.expected_result,
            post_fn_result,
        );

        for run in &test.run {
            print!("  {} ", run.name);
            if !skip_run {
                let test_command = run_test(output_binary, &[], run)?;
                let post_fn_result = post_test_fn(args, &test.name, &run.name, &test_command);

                print_result(
                    test_command.status.into(),
                    run.cfg.expected_result,
                    post_fn_result,
                );
            } else {
                println!("{}", "Skipped".yellow());
            }
        }
    }

    Ok(())
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

    let tests = get_tests(&args)?;
    if tests.is_empty() {
        return Ok(());
    }

    let post_fn = if args.generate {
        println!("Generating test output");
        println!();
        store_streams
    } else {
        println!("Running tests");
        println!();
        compare_streams
    };

    run_all_tests(&args, &tests, post_fn)?;

    Ok(())
}
