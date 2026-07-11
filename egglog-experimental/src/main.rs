use std::ffi::OsString;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Backend {
    Main,
    Dd,
}

fn main() {
    let (backend, mut args) = extract_backend_arg(std::env::args_os()).unwrap_or_else(|err| {
        eprintln!("error: {err}");
        std::process::exit(2);
    });
    let proof_mode = args.iter().any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--term-encoding")
        )
    });
    if backend == Backend::Dd {
        args.retain(|arg| arg.to_str() != Some("--term-encoding"));
    }
    let egraph = match backend {
        Backend::Main if proof_mode => egglog_experimental::new_experimental_egraph_for_proofs(),
        Backend::Main => egglog_experimental::new_experimental_egraph(),
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

fn parse_backend(value: Option<&str>) -> Result<Backend, String> {
    match value {
        Some("main") => Ok(Backend::Main),
        Some("dd") => Ok(Backend::Dd),
        Some(other) => Err(format!(
            "unknown backend {other:?}; expected one of: main, dd"
        )),
        None => Err("backend value must be valid UTF-8".to_string()),
    }
}
