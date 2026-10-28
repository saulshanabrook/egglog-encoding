use egglog_experimental::DisequalityEncoding;
use egglog_experimental::slotted::ProofMode;
use std::ffi::OsString;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    let (encoding, args) = extension_args(std::env::args_os()).unwrap_or_else(|error| {
        eprintln!("error: {error}");
        std::process::exit(2);
    });
    let SlottedArgs {
        slotted,
        encoded,
        no_aliasing,
        proof_mode: slotted_proofs,
        args,
    } = extract_slotted_args(args).unwrap_or_else(|error| {
        eprintln!("error: {error}");
        std::process::exit(2);
    });
    let options: Vec<_> = args.iter().skip(1).take_while(|arg| *arg != "--").collect();
    if options.iter().any(|arg| *arg == "--help" || *arg == "-h") {
        println!(
            "Experimental options:\n  --slotted              Transform slotted source before evaluation\n  --slotted-encoded      Evaluate already lowered slotted code\n  --slotted-no-aliasing  Restrict matching to the nested reference\n  --proofs               With --slotted: translate and check proofs of equality claims\n  --slotted-proof-checks Run the proof-compatible encoding with ordinary checks\n  --disequality-encoding <nee|ee>  Disequality encoding [default: nee]\n"
        );
    }
    let proof_mode = options.iter().any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--proof-extraction" | "--term-encoding")
        )
    });
    if (slotted || encoded) && proof_mode {
        eprintln!("error: --slotted cannot be combined with term/proof encoding");
        std::process::exit(2);
    }
    let mut egraph = egglog_experimental::new_experimental_egraph_with_options(
        !proof_mode && !slotted && !encoded,
        encoding,
    );
    if slotted || encoded {
        egglog_experimental::slotted::register(&mut egraph);
        if slotted_proofs == ProofMode::Prove {
            egraph = egglog_experimental::slotted::with_proofs(egraph);
        }
    }
    if slotted {
        let mut compiler =
            egglog_experimental::slotted::Compiler::new(egglog_experimental::slotted::Options {
                no_aliasing,
                proof_mode: slotted_proofs,
            });
        egglog::cli_with_preprocessor(egraph, args, move |filename, source| {
            compiler.compile(filename, source).map_err(Into::into)
        });
    } else {
        egglog::cli_from(egraph, args);
    }
}

struct SlottedArgs {
    slotted: bool,
    encoded: bool,
    no_aliasing: bool,
    proof_mode: ProofMode,
    args: Vec<OsString>,
}

fn extract_slotted_args(args: impl IntoIterator<Item = OsString>) -> Result<SlottedArgs, String> {
    let (mut slotted, mut encoded, mut no_aliasing) = (false, false, false);
    let mut filtered = Vec::new();
    let mut positional = false;
    let (mut proofs, mut checks) = (false, false);
    for arg in args {
        match arg.to_str() {
            Some("--") => {
                positional = true;
                filtered.push(arg);
            }
            Some("--slotted") if !positional => slotted = true,
            Some("--slotted-proofs") if !positional => proofs = true,
            Some("--slotted-proof-checks") if !positional => checks = true,
            Some("--slotted-encoded") if !positional => encoded = true,
            Some("--slotted-no-aliasing") if !positional => no_aliasing = true,
            _ => filtered.push(arg),
        }
    }
    if no_aliasing && !slotted {
        return Err("--slotted-no-aliasing requires --slotted".into());
    }
    if slotted && encoded {
        return Err("--slotted and --slotted-encoded are mutually exclusive".into());
    }
    if (proofs || checks) && !slotted && !encoded {
        return Err("slotted proof options require --slotted or --slotted-encoded".into());
    }
    if slotted || encoded {
        let mut positional = false;
        filtered.retain(|a| {
            if a == "--" {
                positional = true;
            }
            if !positional && a == "--proofs" {
                proofs = true;
                false
            } else {
                true
            }
        });
    }
    if proofs && checks {
        return Err("--proofs and --slotted-proof-checks are mutually exclusive".into());
    }
    let proof_mode = if proofs {
        ProofMode::Prove
    } else if checks {
        ProofMode::Check
    } else {
        ProofMode::Disabled
    };
    Ok(SlottedArgs {
        slotted,
        encoded,
        no_aliasing,
        proof_mode,
        args: filtered,
    })
}

fn extension_args(
    args: impl IntoIterator<Item = OsString>,
) -> Result<(DisequalityEncoding, Vec<OsString>), String> {
    let mut args = args.into_iter();
    let mut filtered = vec![args.next().ok_or("missing program name")?];
    let mut encoding = None;
    while let Some(arg) = args.next() {
        if arg == "--" {
            filtered.push(arg);
            filtered.extend(args);
            break;
        }
        let value = if arg == "--disequality-encoding" {
            Some(
                args.next()
                    .ok_or("--disequality-encoding requires a value")?,
            )
        } else {
            arg.to_str()
                .and_then(|s| s.strip_prefix("--disequality-encoding="))
                .map(OsString::from)
        };
        if let Some(value) = value {
            if encoding.is_some() {
                return Err("--disequality-encoding may only be specified once".into());
            }
            encoding = Some(value.to_str().ok_or("encoding must be UTF-8")?.parse()?);
        } else {
            filtered.push(arg);
        }
    }
    Ok((encoding.unwrap_or_default(), filtered))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extension_options() {
        for (args, expected) in [
            (
                vec!["bin", "--proofs", "--disequality-encoding=ee", "input.egg"],
                DisequalityEncoding::Ee,
            ),
            (
                vec![
                    "bin",
                    "--proofs",
                    "--disequality-encoding",
                    "nee",
                    "input.egg",
                ],
                DisequalityEncoding::Nee,
            ),
            (
                vec!["bin", "--proofs", "input.egg"],
                DisequalityEncoding::Nee,
            ),
        ] {
            let (encoding, rest) = extension_args(args.into_iter().map(OsString::from)).unwrap();
            assert_eq!(encoding, expected);
            assert_eq!(rest, ["bin", "--proofs", "input.egg"].map(OsString::from));
        }
        let args = ["bin", "--", "--disequality-encoding=ee"].map(OsString::from);
        assert_eq!(
            extension_args(args.clone()).unwrap(),
            (DisequalityEncoding::Nee, args.to_vec())
        );
        for args in [
            vec!["bin", "--disequality-encoding"],
            vec!["bin", "--disequality-encoding=de"],
            vec![
                "bin",
                "--disequality-encoding=ee",
                "--disequality-encoding=nee",
            ],
        ] {
            assert!(extension_args(args.into_iter().map(OsString::from)).is_err());
        }
    }
}
