use std::ffi::OsString;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Backend {
    Main,
    #[cfg(feature = "dd-backend")]
    Dd,
}

fn main() {
    let (backend, args) = extract_backend_arg(std::env::args_os()).unwrap_or_else(|err| {
        eprintln!("error: {err}");
        std::process::exit(2);
    });
    let proof_mode = option_args(&args).any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--proof-extraction" | "--term-encoding")
        )
    });
    let slice_requested = slice_request_for_backend(backend, &args).unwrap_or_else(|err| {
        eprintln!("error: {err}");
        std::process::exit(2);
    });
    #[cfg(feature = "dd-backend")]
    let args = if matches!(backend, Backend::Dd) {
        strip_term_encoding_arg(args)
    } else {
        args
    };
    let proof_mode = proof_mode && !slice_requested;
    let egraph = match backend {
        Backend::Main if proof_mode => egglog_experimental::new_experimental_egraph_for_proofs(),
        Backend::Main => egglog_experimental::new_experimental_egraph(),
        #[cfg(feature = "dd-backend")]
        Backend::Dd => egglog_experimental::new_experimental_egraph_with_backend_for_proofs(
            Box::new(egglog_experimental_dd::EGraph::new()),
        ),
    };
    egglog::cli(
        egraph,
        args,
        egglog_experimental::new_experimental_egraph_for_proofs,
    )
}

fn requests_slice(args: &[OsString]) -> bool {
    option_args(args).any(|arg| {
        let Some(arg) = arg.to_str() else {
            return false;
        };
        matches!(arg, "--slice" | "--slice-output") || arg.starts_with("--slice-output=")
    })
}

fn option_args(args: &[OsString]) -> impl Iterator<Item = &OsString> {
    args.iter().take_while(|arg| arg.to_str() != Some("--"))
}

fn slice_request_for_backend(backend: Backend, args: &[OsString]) -> Result<bool, &'static str> {
    let requested = requests_slice(args);
    if requested && !matches!(backend, Backend::Main) {
        Err("slicing is supported only with --backend main")
    } else {
        Ok(requested)
    }
}

fn extract_backend_arg<I>(args: I) -> Result<(Backend, Vec<OsString>), String>
where
    I: IntoIterator<Item = OsString>,
{
    let mut backend = Backend::Main;
    let mut saw_backend = false;
    let mut filtered = Vec::new();
    let mut iter = args.into_iter();
    while let Some(arg) = iter.next() {
        if arg.to_str() == Some("--") {
            filtered.push(arg);
            filtered.extend(iter);
            break;
        }
        match arg.to_str() {
            Some("--backend") => {
                if saw_backend {
                    return Err("--backend may only be passed once".to_string());
                }
                let Some(value) = iter.next() else {
                    return Err("--backend requires one of: main, dd".to_string());
                };
                backend = parse_backend(value.to_str())?;
                saw_backend = true;
            }
            Some(value) if value.starts_with("--backend=") => {
                if saw_backend {
                    return Err("--backend may only be passed once".to_string());
                }
                backend = parse_backend(value.strip_prefix("--backend="))?;
                saw_backend = true;
            }
            _ => filtered.push(arg),
        }
    }
    Ok((backend, filtered))
}

/// The DD backend always runs under the term encoding, so `--term-encoding` is
/// redundant there; drop it before handing the arguments to the CLI.
#[cfg(feature = "dd-backend")]
fn strip_term_encoding_arg(args: Vec<OsString>) -> Vec<OsString> {
    let mut after_options = false;
    args.into_iter()
        .filter(|arg| {
            if after_options {
                return true;
            }
            if arg.to_str() == Some("--") {
                after_options = true;
                return true;
            }
            arg.to_str() != Some("--term-encoding")
        })
        .collect()
}

fn parse_backend(value: Option<&str>) -> Result<Backend, String> {
    match value {
        Some("main") => Ok(Backend::Main),
        #[cfg(feature = "dd-backend")]
        Some("dd") => Ok(Backend::Dd),
        #[cfg(not(feature = "dd-backend"))]
        Some("dd") => Err(
            "backend \"dd\" requires building egglog-experimental with --features dd-backend"
                .to_string(),
        ),
        Some(other) => Err(format!(
            "unknown backend {other:?}; expected one of: main, dd"
        )),
        None => Err("backend value must be valid UTF-8".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_main_backend() {
        assert_eq!(parse_backend(Some("main")), Ok(Backend::Main));
    }

    #[cfg(not(feature = "dd-backend"))]
    #[test]
    fn explains_how_to_enable_dd_backend() {
        assert_eq!(
            parse_backend(Some("dd")),
            Err(
                "backend \"dd\" requires building egglog-experimental with --features dd-backend"
                    .to_string()
            )
        );
    }

    #[cfg(feature = "dd-backend")]
    #[test]
    fn parses_enabled_dd_backend() {
        assert_eq!(parse_backend(Some("dd")), Ok(Backend::Dd));
    }

    #[cfg(feature = "dd-backend")]
    #[test]
    fn dd_backend_arg_filtering_drops_term_encoding() {
        let args = ["egglog", "--backend", "dd", "--term-encoding", "prog.egg"]
            .into_iter()
            .map(OsString::from);
        let (backend, rest) = extract_backend_arg(args).unwrap();
        assert_eq!(backend, Backend::Dd);
        assert_eq!(
            strip_term_encoding_arg(rest),
            vec![OsString::from("egglog"), OsString::from("prog.egg")]
        );
        assert_eq!(
            strip_term_encoding_arg(
                ["egglog", "--term-encoding", "--", "--term-encoding"]
                    .into_iter()
                    .map(OsString::from)
                    .collect()
            ),
            ["egglog", "--", "--term-encoding"]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn wrapper_options_stop_at_the_argument_terminator() {
        let args = ["egglog", "--", "--backend=dd", "--slice", "--proofs"]
            .into_iter()
            .map(OsString::from);
        let (backend, rest) = extract_backend_arg(args).unwrap();
        assert_eq!(backend, Backend::Main);
        assert!(!requests_slice(&rest));
        assert!(!option_args(&rest).any(|arg| arg.to_str() == Some("--proofs")));
        assert_eq!(
            rest,
            ["egglog", "--", "--backend=dd", "--slice", "--proofs"]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
    }
}

#[cfg(test)]
#[path = "causal_slice_tests.rs"]
mod causal_slice_tests;
