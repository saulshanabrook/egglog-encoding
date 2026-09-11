use egglog_experimental::DisequalityEncoding;
use std::{ffi::OsString, str::FromStr};

fn main() {
    let (disequality_encoding, args) = parse_disequality_encoding(std::env::args_os())
        .unwrap_or_else(|error| {
            eprintln!("error: {error}");
            std::process::exit(2);
        });
    if cli_options(&args).any(|arg| arg == "--help" || arg == "-h") {
        println!(
            "Experimental options:\n  --disequality-encoding <ENCODING>  Disequality encoding [default: ee] [possible values: {}]\n",
            DisequalityEncoding::POSSIBLE_VALUES
        );
    }

    let proof_mode =
        validate_disequality_mode(disequality_encoding, &args).unwrap_or_else(|error| {
            eprintln!("error: {error}");
            std::process::exit(2);
        });
    let egraph = if proof_mode {
        egglog_experimental::new_experimental_egraph_for_proofs_with_disequality_encoding(
            disequality_encoding,
        )
    } else {
        egglog_experimental::new_experimental_egraph_with_disequality_encoding(disequality_encoding)
    };
    egglog::cli_from(egraph, args)
}

fn validate_disequality_mode(
    encoding: DisequalityEncoding,
    args: &[OsString],
) -> Result<bool, String> {
    let proof_mode = cli_options(args).any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--proof-extraction" | "--term-encoding")
        )
    });
    if proof_mode && encoding == DisequalityEncoding::DisequalityEdges {
        return Err("--disequality-encoding de is currently supported only in normal mode; it cannot be combined with --term-encoding, --proofs, --proof-testing, or --proof-extraction".to_owned());
    }
    Ok(proof_mode)
}

fn cli_options(args: &[OsString]) -> impl Iterator<Item = &OsString> {
    args.iter().skip(1).take_while(|arg| *arg != "--")
}

fn parse_disequality_encoding(
    args: impl IntoIterator<Item = OsString>,
) -> Result<(DisequalityEncoding, Vec<OsString>), String> {
    let mut args = args.into_iter();
    let Some(program) = args.next() else {
        return Err("missing program name".to_owned());
    };
    let mut filtered = vec![program];
    let mut encoding = None;
    let mut parse_options = true;

    while let Some(arg) = args.next() {
        if parse_options && arg == "--" {
            parse_options = false;
            filtered.push(arg);
            continue;
        }

        let inline_value = parse_options
            .then(|| arg.to_str())
            .flatten()
            .and_then(|arg| arg.strip_prefix("--disequality-encoding="));
        if parse_options && arg == "--disequality-encoding" {
            if encoding.is_some() {
                return Err("--disequality-encoding may only be specified once".to_owned());
            }
            let value = args
                .next()
                .ok_or_else(|| "--disequality-encoding requires a value".to_owned())?;
            let value = value
                .to_str()
                .ok_or_else(|| "--disequality-encoding must be valid UTF-8".to_owned())?;
            encoding = Some(DisequalityEncoding::from_str(value)?);
        } else if let Some(value) = inline_value {
            if encoding.is_some() {
                return Err("--disequality-encoding may only be specified once".to_owned());
            }
            encoding = Some(DisequalityEncoding::from_str(value)?);
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
    fn parses_and_filters_disequality_encoding() {
        let (encoding, args) = parse_disequality_encoding(
            [
                "egglog-experimental",
                "--disequality-encoding=nee",
                "input.egg",
            ]
            .map(OsString::from),
        )
        .unwrap();
        assert_eq!(encoding, DisequalityEncoding::NegatedEqualityEmbedding);
        assert_eq!(
            args,
            ["egglog-experimental", "input.egg"].map(OsString::from)
        );

        let (encoding, args) = parse_disequality_encoding(
            ["egglog-experimental", "--disequality-encoding", "de", "-"].map(OsString::from),
        )
        .unwrap();
        assert_eq!(encoding, DisequalityEncoding::DisequalityEdges);
        assert_eq!(args, ["egglog-experimental", "-"].map(OsString::from));
    }

    #[test]
    fn defaults_to_ee_and_respects_end_of_options() {
        let (encoding, args) = parse_disequality_encoding(
            ["egglog-experimental", "--", "--disequality-encoding=de"].map(OsString::from),
        )
        .unwrap();
        assert_eq!(encoding, DisequalityEncoding::EqualityEmbedding);
        assert_eq!(
            args,
            ["egglog-experimental", "--", "--disequality-encoding=de"].map(OsString::from)
        );
    }

    #[test]
    fn rejects_invalid_or_duplicate_encodings() {
        let invalid = parse_disequality_encoding(
            ["egglog-experimental", "--disequality-encoding", "bogus"].map(OsString::from),
        )
        .unwrap_err();
        assert!(invalid.contains("expected one of: ee, oee, nee, de"));

        let duplicate = parse_disequality_encoding(
            [
                "egglog-experimental",
                "--disequality-encoding=ee",
                "--disequality-encoding=de",
            ]
            .map(OsString::from),
        )
        .unwrap_err();
        assert!(duplicate.contains("only be specified once"));
    }

    #[test]
    fn recognizes_every_term_and_proof_mode_as_incompatible_with_de() {
        for flag in [
            "--term-encoding",
            "--proofs",
            "--proof-testing",
            "--proof-extraction",
        ] {
            let args = [OsString::from("egglog-experimental"), OsString::from(flag)];
            assert!(
                validate_disequality_mode(DisequalityEncoding::DisequalityEdges, &args)
                    .unwrap_err()
                    .contains("supported only in normal mode")
            );
        }
        assert!(
            !validate_disequality_mode(
                DisequalityEncoding::DisequalityEdges,
                &[OsString::from("egglog-experimental")]
            )
            .unwrap()
        );
    }

    #[test]
    fn mode_flags_after_end_of_options_are_input_paths() {
        for flag in [
            "--term-encoding",
            "--proofs",
            "--proof-testing",
            "--proof-extraction",
        ] {
            let args = [
                OsString::from("egglog-experimental"),
                OsString::from("--"),
                OsString::from(flag),
            ];
            assert!(
                !validate_disequality_mode(DisequalityEncoding::DisequalityEdges, &args).unwrap()
            );
        }
    }
}
