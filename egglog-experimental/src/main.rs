use egglog_experimental::DisequalityEncoding;
use std::ffi::OsString;

fn main() {
    let (encoding, args) = extension_args(std::env::args_os()).unwrap_or_else(|error| {
        eprintln!("error: {error}");
        std::process::exit(2);
    });
    let options: Vec<_> = args.iter().skip(1).take_while(|arg| *arg != "--").collect();
    if options.iter().any(|arg| *arg == "--help" || *arg == "-h") {
        println!(
            "Experimental options:\n  --disequality-encoding <nee|ee>  Disequality encoding [default: nee]\n"
        );
    }
    let proof_mode = options.iter().any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--proof-extraction" | "--term-encoding")
        )
    });
    let egraph = egglog_experimental::new_experimental_egraph_with_options(!proof_mode, encoding);
    egglog::cli_from(egraph, args)
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
