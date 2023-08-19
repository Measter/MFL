use std::{
    fmt,
    io::{BufWriter, Write},
    path::Path,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Signedness {
    Signed,
    Unsigned,
}

impl fmt::Display for Signedness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            match self {
                Signedness::Signed => f.write_str("I"),
                Signedness::Unsigned => f.write_str("U"),
            }
        } else {
            match self {
                Signedness::Signed => f.write_str("i"),
                Signedness::Unsigned => f.write_str("u"),
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Width {
    I8,
    I16,
    I32,
    I64,
    Size,
    I128,
}

impl Width {
    fn bit_width(self) -> u8 {
        match self {
            Width::I8 => 8,
            Width::I16 => 16,
            Width::I32 => 32,
            Width::I64 | Width::Size => 64,
            Width::I128 => 128,
        }
    }
}

impl fmt::Display for Width {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Width::I8 => f.write_str("8"),
            Width::I16 => f.write_str("16"),
            Width::I32 => f.write_str("32"),
            Width::I64 => f.write_str("64"),
            Width::I128 => f.write_str("128"),
            Width::Size => f.write_str("size"),
        }
    }
}

fn main() {
    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("impl.rs");

    let mut kind_width = Vec::new();
    for signedness in [Signedness::Unsigned, Signedness::Signed] {
        for width in [
            Width::I8,
            Width::I16,
            Width::I32,
            Width::I64,
            Width::Size,
            Width::I128,
        ] {
            kind_width.push((signedness, width));
        }
    }

    let impl_file = std::fs::File::create(dest_path).unwrap();
    let mut impl_file = BufWriter::new(impl_file);

    generate_impls(&mut impl_file, &kind_width).unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}

fn generate_impls(
    impl_file: &mut impl Write,
    types: &[(Signedness, Width)],
) -> Result<(), Box<dyn std::error::Error>> {
    for &(from_sign, from_width) in types {
        writeln!(impl_file, "impl IntCast for {from_sign}{from_width} {{")?;

        for &(to_sign, to_width) in types {
            if is_infallible(from_sign, from_width, to_sign, to_width) {
                // This will always succeed.
                writeln!(
                    impl_file,
                    "    type {to_sign:#}{to_width} = {to_sign}{to_width};"
                )?;
            } else {
                // This may fail.
                writeln!(
                    impl_file,
                    "    type {to_sign:#}{to_width} = Option<{to_sign}{to_width}>;"
                )?;
            }

            writeln!(impl_file, "#[inline(always)]")?;

            writeln!(
                impl_file,
                "    fn to_{to_sign}{to_width}(self) -> Self::{to_sign:#}{to_width} {{"
            )?;

            if from_sign == to_sign {
                if to_width.bit_width() >= from_width.bit_width() {
                    writeln!(impl_file, "        self as _")?;
                } else {
                    writeln!(
                        impl_file,
                        "        (self >= {to_sign}{to_width}::MIN as _ && self <= {to_sign}{to_width}::MAX as _).then_some(self as _)"
                    )?;
                }
            } else if from_sign == Signedness::Unsigned {
                if to_width.bit_width() > from_width.bit_width() {
                    writeln!(impl_file, "        self as _")?;
                } else {
                    writeln!(
                        impl_file,
                        "        (self <= {to_sign}{to_width}::MAX as _).then_some(self as _)"
                    )?;
                }
            } else {
                #[allow(clippy::collapsible_else_if)]
                if to_width.bit_width() >= from_width.bit_width() {
                    writeln!(impl_file, "        (self >= 0).then_some(self as _)")?;
                } else {
                    writeln!(impl_file, "        (self >= 0 && self <= {to_sign}{to_width}::MAX as _).then_some(self as _)")?;
                }
            }

            writeln!(impl_file, "    }}")?;
        }

        writeln!(impl_file, "}}")?;
    }
    Ok(())
}

fn is_infallible(
    from_sign: Signedness,
    from_width: Width,
    to_sign: Signedness,
    to_width: Width,
) -> bool {
    (from_sign == to_sign && to_width.bit_width() >= from_width.bit_width())
        || (from_sign != to_sign
            && from_sign == Signedness::Unsigned
            && to_width.bit_width() > from_width.bit_width())
}
