use std::{
    collections::HashMap,
    ffi::OsStr,
    io::{StdoutLock, Write},
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

fn store_streams(
    args: &Args,
    group_name: &Path,
    test_name: &str,
    output: &Output,
) -> Result<RunStatus> {
    let root_name = args.output_root.join(group_name);
    std::fs::create_dir_all(root_name.parent().unwrap())?;

    std::fs::write(
        root_name.with_extension(format!("{test_name}.stdout")),
        &output.stdout,
    )?;

    std::fs::write(
        root_name.with_extension(format!("{test_name}.stderr")),
        &output.stderr,
    )?;

    Ok(RunStatus::Ok)
}

fn run_test(command: impl AsRef<OsStr>, pre_args: &[&OsStr], test: &Test) -> Result<Output> {
    let test_command = Command::new(command)
        .args(pre_args)
        .args(&test.cfg.command_args)
        .output()?;

    Ok(test_command)
}

fn print_result(
    stdout: &mut StdoutLock<'_>,
    actual_result: RunStatus,
    expected_result: RunStatus,
    post_fn_result: RunStatus,
) -> Result<()> {
    if actual_result != expected_result {
        writeln!(
            stdout,
            "{}: Expected {expected_result:?} got {actual_result:?}",
            "Error".red()
        )?;
    } else if post_fn_result == RunStatus::Error {
        writeln!(stdout, "{}: Output streams differ", "Error".red())?;
    } else {
        writeln!(stdout, "{}", "Ok".green())?;
    }

    Ok(())
}

fn run_all_tests(
    args: &Args,
    tests: &[Tests],
    post_test_fn: fn(&Args, &Path, &str, &Output) -> Result<RunStatus>,
) -> Result<()> {
    let temp_dir = tempfile::tempdir()?;
    let mut stdout = std::io::stdout().lock();
    let stdout = &mut stdout;

    for test in tests {
        writeln!(stdout, "{}", test.name.display())?;

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

        write!(stdout, "  compile ")?;
        let test_command = run_test(&args.mfl, &compiler_args, &test.compile)?;
        let post_fn_result = post_test_fn(args, &test.name, "compile", &test_command)?;

        print_result(
            stdout,
            test_command.status.into(),
            test.compile.cfg.expected_result,
            post_fn_result,
        )?;

        let skip_run = RunStatus::Error == test_command.status.into()
            || test.compile.cfg.expected_result == RunStatus::Error;

        for run in &test.run {
            write!(stdout, "  {} ", run.name)?;
            if !skip_run {
                let test_command = run_test(output_binary, &[], run)?;
                let post_fn_result = post_test_fn(args, &test.name, &run.name, &test_command)?;

                print_result(
                    stdout,
                    test_command.status.into(),
                    run.cfg.expected_result,
                    post_fn_result,
                )?;
            } else {
                writeln!(stdout, "Skipped")?;
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

    if args.generate {
        println!("Generating test output");
        println!();
        run_all_tests(&args, &tests, store_streams)?;
    }

    Ok(())
}
