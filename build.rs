use std::{path::Path, process::Command};

fn main() {
    let out_dir = std::env::var_os("OUT_DIR").unwrap();

    for file in ["bootstrap.s", "syscalls.s"] {
        println!("cargo:rerun-if-changed=./src/asm/{file}");
        let mut dest_dir = Path::new(&out_dir).join(file);
        dest_dir.set_extension("o");

        assert!(Command::new("nasm")
            .arg("-felf64")
            .arg(format!("./src/asm/{file}"))
            .arg("-o")
            .arg(&dest_dir)
            .status()
            .unwrap()
            .success());
    }
    println!("cargo:rerun-if-changed=build.rs");
}
