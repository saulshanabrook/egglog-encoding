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
    let proof_mode = args.iter().any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--proof-extraction" | "--term-encoding")
        )
    });
    #[cfg(feature = "dd-backend")]
    let args = if matches!(backend, Backend::Dd) {
        strip_term_encoding_arg(args)
    } else {
        args
    };
    let egraph = match backend {
        Backend::Main if proof_mode => egglog_experimental::new_experimental_egraph_for_proofs(),
        Backend::Main => egglog_experimental::new_experimental_egraph(),
        #[cfg(feature = "dd-backend")]
        Backend::Dd => egglog_experimental::new_experimental_egraph_with_backend_for_proofs(
            Box::new(egglog_experimental_dd::EGraph::new()),
        ),
    };
    egglog::cli_with_args(egraph, args)
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
    args.into_iter()
        .filter(|arg| arg.to_str() != Some("--term-encoding"))
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
    }
}
