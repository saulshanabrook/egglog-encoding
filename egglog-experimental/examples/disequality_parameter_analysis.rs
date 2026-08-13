use egglog_experimental::{DisequalityEncoding, new_experimental_egraph_with_disequality_encoding};
use std::{error::Error, fmt::Write, path::PathBuf, str::FromStr, time::Instant};

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args_os();
    let program = args
        .next()
        .and_then(|value| value.into_string().ok())
        .unwrap_or_else(|| "disequality_parameter_analysis".to_owned());
    let input = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("usage: {program} <artifact-exprs.in> <ratio> [ee|oee|nee|de]"))?;
    let ratio = args
        .next()
        .ok_or_else(|| format!("usage: {program} <artifact-exprs.in> <ratio> [ee|oee|nee|de]"))?
        .into_string()
        .map_err(|_| "ratio must be valid UTF-8")?
        .parse::<f32>()?;
    if !(0.0..=1.0).contains(&ratio) {
        return Err("ratio must be between 0 and 1".into());
    }
    let encoding = args
        .next()
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "encoding must be valid UTF-8".to_owned())
                .and_then(|value| DisequalityEncoding::from_str(&value))
        })
        .transpose()?
        .unwrap_or_default();
    if args.next().is_some() {
        return Err(format!("usage: {program} <artifact-exprs.in> <ratio> [ee|oee|nee|de]").into());
    }

    let input = std::fs::read_to_string(&input)?;
    let artifact_line_slots = input.split('\n').count();
    let expressions = input
        .lines()
        .map(translate_artifact_expr)
        .collect::<Result<Vec<_>, _>>()?;
    if expressions.len() % 2 != 0 {
        return Err("artifact input must contain an even number of expressions".into());
    }
    // The artifact computes its threshold over `content.split("\n")`, which
    // includes one trailing empty slot for the supplied newline-terminated
    // input. Preserve that detail, then cap at the number of parsed expressions.
    let disequality_expressions =
        (((ratio * artifact_line_slots as f32 / 2.0) as usize) * 2).min(expressions.len());

    let mut setup = String::from(
        r#"(datatype Expr
  (N1)
  (N2)
  (N3)
  (N4)
  (N5)
  (f Expr)
  (g Expr Expr)
  (h Expr Expr Expr))
"#,
    );
    let mut base_disequalities = 0;
    // Match the artifact's `for y in x+1..5` loop exactly. Although its
    // comment says all five numerals, the exclusive upper bound yields six
    // pairwise constraints among 1 through 4.
    for left in 1..5 {
        for right in left + 1..5 {
            writeln!(setup, "(disequal (N{left}) (N{right}))")?;
            base_disequalities += 1;
        }
    }

    let mut workload = String::new();
    for (index, pair) in expressions.chunks_exact(2).enumerate() {
        if index * 2 < disequality_expressions {
            writeln!(workload, "(disequal {} {})", pair[0], pair[1])?;
        } else {
            writeln!(workload, "(union {} {})", pair[0], pair[1])?;
        }
    }
    workload.push_str("(run-schedule (saturate (run)))\n");

    let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
    egraph.set_num_threads(1);
    egraph.parse_and_run_program(None, &setup)?;
    let parse_start = Instant::now();
    let parsed = egraph.parse_program(None, &workload)?;
    let parse_elapsed = parse_start.elapsed();
    let execute_start = Instant::now();
    let result = egraph.run_program(parsed);
    let execute_elapsed = execute_start.elapsed();
    let contradiction = match result {
        Ok(_) => false,
        Err(error)
            if error
                .to_string()
                .contains("disequality constraint contradicted") =>
        {
            true
        }
        Err(error) => return Err(error.into()),
    };
    let encoding_prefix = match encoding {
        DisequalityEncoding::EqualityEmbedding
        | DisequalityEncoding::OptimizedEqualityEmbedding => "@disequality-eq-",
        DisequalityEncoding::NegatedEqualityEmbedding => "@disequality-ne-",
        DisequalityEncoding::DisequalityEdges => "@disequality-edge-",
    };
    let encoding_rows = egraph
        .get_function_names()
        .into_iter()
        .filter(|name| name.starts_with(encoding_prefix))
        .map(|name| egraph.get_size(&name))
        .sum::<usize>();

    println!(
        "engine,encoding,ratio,expressions,base_disequalities,disequalities,equalities,contradiction,parse_ms,execute_ms,total_ms,encoding_rows,tuples"
    );
    println!(
        "egglog,{encoding},{ratio},{},{base_disequalities},{},{},{contradiction},{:.3},{:.3},{:.3},{encoding_rows},{}",
        expressions.len(),
        disequality_expressions / 2 + base_disequalities,
        (expressions.len() - disequality_expressions) / 2,
        parse_elapsed.as_secs_f64() * 1_000.0,
        execute_elapsed.as_secs_f64() * 1_000.0,
        (parse_elapsed + execute_elapsed).as_secs_f64() * 1_000.0,
        egraph.num_tuples(),
    );
    Ok(())
}

fn translate_artifact_expr(input: &str) -> Result<String, String> {
    fn skip_whitespace(input: &[u8], cursor: &mut usize) {
        while input.get(*cursor).is_some_and(u8::is_ascii_whitespace) {
            *cursor += 1;
        }
    }

    fn parse(input: &[u8], cursor: &mut usize) -> Result<String, String> {
        skip_whitespace(input, cursor);
        match input.get(*cursor).copied() {
            Some(b'1'..=b'5') => {
                let numeral = input[*cursor] as char;
                *cursor += 1;
                Ok(format!("(N{numeral})"))
            }
            Some(b'(') => {
                *cursor += 1;
                skip_whitespace(input, cursor);
                let function = match input.get(*cursor).copied() {
                    Some(function @ (b'f' | b'g' | b'h')) => function as char,
                    _ => return Err(format!("expected f, g, or h at byte {cursor}")),
                };
                *cursor += 1;
                let arity = match function {
                    'f' => 1,
                    'g' => 2,
                    'h' => 3,
                    _ => unreachable!(),
                };
                let mut translated = format!("({function}");
                for _ in 0..arity {
                    translated.push(' ');
                    translated.push_str(&parse(input, cursor)?);
                }
                skip_whitespace(input, cursor);
                if input.get(*cursor) != Some(&b')') {
                    return Err(format!("expected ')' at byte {cursor}"));
                }
                *cursor += 1;
                translated.push(')');
                Ok(translated)
            }
            _ => Err(format!("expected an expression at byte {cursor}")),
        }
    }

    let mut cursor = 0;
    let translated = parse(input.as_bytes(), &mut cursor)?;
    skip_whitespace(input.as_bytes(), &mut cursor);
    if cursor != input.len() {
        return Err(format!("unexpected input at byte {cursor}"));
    }
    Ok(translated)
}

#[cfg(test)]
mod tests {
    use super::translate_artifact_expr;

    #[test]
    fn translates_and_validates_artifact_expressions() {
        assert_eq!(translate_artifact_expr("1").unwrap(), "(N1)");
        assert_eq!(
            translate_artifact_expr("(f (g 2 (h 3 4 5)))").unwrap(),
            "(f (g (N2) (h (N3) (N4) (N5))))"
        );
        assert!(translate_artifact_expr("(g 1)").is_err());
        assert!(translate_artifact_expr("(x 1)").is_err());
        assert!(translate_artifact_expr("6").is_err());
    }
}
