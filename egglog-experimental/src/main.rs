use egglog_experimental::slotted::ProofMode;
use std::ffi::OsString;

#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;

fn main() {
    let args = benchmark_memory::configure(std::env::args_os());
    let SlottedArgs {
        slotted,
        encoded,
        no_aliasing,
        source,
        proof_mode: slotted_proofs,
        args,
    } = extract_slotted_args(args).unwrap_or_else(|error| {
        eprintln!("error: {error}");
        std::process::exit(2);
    });
    let options: Vec<_> = args.iter().skip(1).take_while(|arg| *arg != "--").collect();
    if options.iter().any(|arg| *arg == "--help" || *arg == "-h") {
        println!(
            "Experimental options:\n  --slotted              Transform slotted source before evaluation\n  --slotted-encoded      Evaluate already lowered slotted code\n  --slotted-source PATH  Original source for replaying encoded proofs\n  --slotted-no-aliasing  Restrict matching to the nested reference\n  --proofs               With --slotted: translate and check proofs of equality claims\n  --slotted-proof-checks Run the proof-compatible encoding with ordinary checks\n  --memory-limit-bytes <N>       Bound native address space\n"
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
    );
    if slotted || encoded {
        egglog_experimental::slotted::register(&mut egraph);
        if slotted_proofs == ProofMode::Prove {
            egraph = egglog_experimental::slotted::with_proofs(egraph);
        }
    }
    if slotted {
        let mut compiler = egglog_experimental::slotted::Compiler::for_egraph(
            egglog_experimental::slotted::Options {
                no_aliasing,
                proof_mode: slotted_proofs,
            },
            &egraph,
        );
        egglog::cli_with_preprocessor(egraph, args, move |filename, source| {
            compiler
                .compile_program(filename, source)
                .map_err(Into::into)
        });
    } else if let Some(path) = source {
        let program = (|| -> Result<_, Box<dyn std::error::Error>> {
            let source = std::fs::read_to_string(&path)?;
            let mut compiler = egglog_experimental::slotted::Compiler::new(
                egglog_experimental::slotted::Options {
                    no_aliasing,
                    proof_mode: ProofMode::Prove,
                },
            );
            Ok(compiler.compile_program(Some(path.to_string_lossy().into_owned()), &source)?)
        })()
        .unwrap_or_else(|error| {
            eprintln!("error: {error}");
            std::process::exit(2);
        });
        egglog::cli_with_preprocessor(egraph, args, move |filename, encoded| {
            program.with_encoded(filename, encoded)
        });
    } else {
        egglog::cli_from(egraph, args);
    }
}

struct SlottedArgs {
    slotted: bool,
    encoded: bool,
    no_aliasing: bool,
    source: Option<std::path::PathBuf>,
    proof_mode: ProofMode,
    args: Vec<OsString>,
}

fn extract_slotted_args(args: impl IntoIterator<Item = OsString>) -> Result<SlottedArgs, String> {
    let (mut slotted, mut encoded, mut no_aliasing) = (false, false, false);
    let mut filtered = Vec::new();
    let mut positional = false;
    let (mut proofs, mut checks) = (false, false);
    let mut args = args.into_iter();
    let mut source = None;
    while let Some(arg) = args.next() {
        match arg.to_str() {
            Some("--") => {
                positional = true;
                filtered.push(arg);
            }
            Some("--slotted-source") if !positional => {
                if source.is_some() {
                    return Err("--slotted-source may only be specified once".into());
                }
                source = Some(std::path::PathBuf::from(
                    args.next().ok_or("--slotted-source requires a path")?,
                ));
            }
            Some("--slotted") if !positional => slotted = true,
            Some("--slotted-proofs") if !positional => proofs = true,
            Some("--slotted-proof-checks") if !positional => checks = true,
            Some("--slotted-encoded") if !positional => encoded = true,
            Some("--slotted-no-aliasing") if !positional => no_aliasing = true,
            _ => filtered.push(arg),
        }
    }
    if no_aliasing && !slotted && source.is_none() {
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
    if source.is_some() && (!encoded || !proofs) {
        return Err("--slotted-source requires --slotted-encoded --proofs".into());
    }
    if encoded && proofs && source.is_none() {
        return Err("encoded proofs require --slotted-source <original.egg>".into());
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
        source,
        proof_mode,
        args: filtered,
    })
}
