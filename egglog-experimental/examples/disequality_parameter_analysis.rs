use egglog::{Error as EgglogError, FullState, RawValues, Value, Write as EgglogWrite};
use egglog_experimental::{
    CompiledDisequalityWriter, DisequalityEncoding,
    new_experimental_egraph_with_disequality_encoding,
};
use std::{
    error::Error,
    fmt::{self, Write as FmtWrite},
    path::PathBuf,
    str::FromStr,
    time::{Duration, Instant},
};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum LoadMode {
    #[default]
    Source,
    BatchedApi,
}

impl fmt::Display for LoadMode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source => formatter.write_str("source"),
            Self::BatchedApi => formatter.write_str("batched-api"),
        }
    }
}

impl FromStr for LoadMode {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "source" => Ok(Self::Source),
            "batched-api" => Ok(Self::BatchedApi),
            _ => Err(format!(
                "unknown load mode {value:?}; expected source or batched-api"
            )),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ArtifactExpr {
    Numeral(u8),
    Apply(char, Vec<Self>),
}

impl ArtifactExpr {
    fn add_to(&self, state: &mut FullState<'_, '_>) -> Result<Value, EgglogError> {
        match self {
            Self::Numeral(numeral) => state.add(&format!("N{numeral}"), RawValues(Vec::new())),
            Self::Apply(function, children) => {
                let children = children
                    .iter()
                    .map(|child| child.add_to(state))
                    .collect::<Result<Vec<_>, _>>()?;
                state.add(&function.to_string(), RawValues(children))
            }
        }
    }
}

impl fmt::Display for ArtifactExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Numeral(numeral) => write!(formatter, "(N{numeral})"),
            Self::Apply(function, children) => {
                write!(formatter, "({function}")?;
                for child in children {
                    write!(formatter, " {child}")?;
                }
                formatter.write_char(')')
            }
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args_os();
    let program = args
        .next()
        .and_then(|value| value.into_string().ok())
        .unwrap_or_else(|| "disequality_parameter_analysis".to_owned());
    let input = args.next().map(PathBuf::from).ok_or_else(|| {
        format!("usage: {program} <artifact-exprs.in> <ratio> [ee|oee|nee|de] [source|batched-api] [source-batch-size]")
    })?;
    let ratio = args
        .next()
        .ok_or_else(|| {
            format!(
                "usage: {program} <artifact-exprs.in> <ratio> [ee|oee|nee|de] [source|batched-api] [source-batch-size]"
            )
        })?
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
    let load_mode = args
        .next()
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "load mode must be valid UTF-8".to_owned())
                .and_then(|value| LoadMode::from_str(&value))
        })
        .transpose()?
        .unwrap_or_default();
    let source_batch_size = args
        .next()
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "source batch size must be valid UTF-8".to_owned())?
                .parse::<usize>()
                .map_err(|error| format!("invalid source batch size: {error}"))
        })
        .transpose()?;
    if args.next().is_some() {
        return Err(format!(
            "usage: {program} <artifact-exprs.in> <ratio> [ee|oee|nee|de] [source|batched-api] [source-batch-size]"
        )
        .into());
    }
    if source_batch_size == Some(0) {
        return Err("source batch size must be positive".into());
    }
    if load_mode == LoadMode::BatchedApi && source_batch_size.is_some() {
        return Err("source batch size applies only to source mode".into());
    }
    let input = std::fs::read_to_string(&input)?;
    let artifact_parse_start = Instant::now();
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
    let artifact_parse_elapsed = artifact_parse_start.elapsed();

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

    let source_render_start = Instant::now();
    let workload = if load_mode == LoadMode::Source {
        let mut workload = String::new();
        let pair_count = expressions.len() / 2;
        for (index, pair) in expressions.chunks_exact(2).enumerate() {
            if source_batch_size.is_some_and(|batch_size| index % batch_size == 0) {
                workload.push_str("(begin\n");
            }
            if index * 2 < disequality_expressions {
                writeln!(workload, "(disequal {} {})", pair[0], pair[1])?;
            } else {
                writeln!(workload, "(union {} {})", pair[0], pair[1])?;
            }
            if source_batch_size
                .is_some_and(|batch_size| (index + 1) % batch_size == 0 || index + 1 == pair_count)
            {
                workload.push_str(")\n");
            }
        }
        workload
    } else {
        String::new()
    };
    let source_render_elapsed = source_render_start.elapsed();

    let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
    egraph.set_num_threads(1);
    egraph.parse_and_run_program(None, &setup)?;
    let schedule = egraph.parse_program(None, "(run-schedule (saturate (run)))")?;
    let mut contradiction = false;
    let (parse_elapsed, load_elapsed) = match load_mode {
        LoadMode::Source => {
            let parse_start = Instant::now();
            let parsed = egraph.parse_program(None, &workload)?;
            let parse_elapsed = parse_start.elapsed();
            let load_start = Instant::now();
            let result = egraph.run_program(parsed);
            let load_elapsed = load_start.elapsed();
            match result {
                Ok(_) => {}
                Err(error)
                    if error
                        .to_string()
                        .contains("disequality constraint contradicted") =>
                {
                    contradiction = true;
                }
                Err(error) => return Err(error.into()),
            }
            (parse_elapsed, load_elapsed)
        }
        LoadMode::BatchedApi => {
            let load_start = Instant::now();
            egraph.update(|mut state| {
                let writer = CompiledDisequalityWriter::from_installed_support(
                    &mut state, encoding, "Expr",
                )?;
                for (index, pair) in expressions.chunks_exact(2).enumerate() {
                    let left = pair[0].add_to(&mut state)?;
                    let right = pair[1].add_to(&mut state)?;
                    if index * 2 < disequality_expressions {
                        writer.add(&mut state, left, right)?;
                    } else {
                        state.union(left, right)?;
                    }
                }
                Ok(())
            })?;
            (Duration::ZERO, load_start.elapsed())
        }
    };
    let schedule_elapsed = if contradiction {
        Duration::ZERO
    } else {
        let schedule_start = Instant::now();
        let result = egraph.run_program(schedule);
        let elapsed = schedule_start.elapsed();
        match result {
            Ok(_) => {}
            Err(error)
                if error
                    .to_string()
                    .contains("disequality constraint contradicted") =>
            {
                contradiction = true;
            }
            Err(error) => return Err(error.into()),
        }
        elapsed
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
        "engine,encoding,load_mode,source_batch_size,ratio,expressions,base_disequalities,disequalities,equalities,contradiction,artifact_parse_ms,source_render_ms,source_parse_ms,load_ms,schedule_ms,total_ms,encoding_rows,tuples"
    );
    println!(
        "egglog,{encoding},{load_mode},{},{ratio},{},{base_disequalities},{},{},{contradiction},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{encoding_rows},{}",
        match load_mode {
            LoadMode::Source => source_batch_size.unwrap_or(1),
            LoadMode::BatchedApi => 0,
        },
        expressions.len(),
        disequality_expressions / 2 + base_disequalities,
        (expressions.len() - disequality_expressions) / 2,
        artifact_parse_elapsed.as_secs_f64() * 1_000.0,
        source_render_elapsed.as_secs_f64() * 1_000.0,
        parse_elapsed.as_secs_f64() * 1_000.0,
        load_elapsed.as_secs_f64() * 1_000.0,
        schedule_elapsed.as_secs_f64() * 1_000.0,
        (artifact_parse_elapsed
            + source_render_elapsed
            + parse_elapsed
            + load_elapsed
            + schedule_elapsed)
            .as_secs_f64()
            * 1_000.0,
        egraph.num_tuples(),
    );
    Ok(())
}

fn translate_artifact_expr(input: &str) -> Result<ArtifactExpr, String> {
    fn skip_whitespace(input: &[u8], cursor: &mut usize) {
        while input.get(*cursor).is_some_and(u8::is_ascii_whitespace) {
            *cursor += 1;
        }
    }

    fn parse(input: &[u8], cursor: &mut usize) -> Result<ArtifactExpr, String> {
        skip_whitespace(input, cursor);
        match input.get(*cursor).copied() {
            Some(b'1'..=b'5') => {
                let numeral = input[*cursor] as char;
                *cursor += 1;
                Ok(ArtifactExpr::Numeral(numeral as u8 - b'0'))
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
                let mut children = Vec::with_capacity(arity);
                for _ in 0..arity {
                    children.push(parse(input, cursor)?);
                }
                skip_whitespace(input, cursor);
                if input.get(*cursor) != Some(&b')') {
                    return Err(format!("expected ')' at byte {cursor}"));
                }
                *cursor += 1;
                Ok(ArtifactExpr::Apply(function, children))
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
        assert_eq!(translate_artifact_expr("1").unwrap().to_string(), "(N1)");
        assert_eq!(
            translate_artifact_expr("(f (g 2 (h 3 4 5)))")
                .unwrap()
                .to_string(),
            "(f (g (N2) (h (N3) (N4) (N5))))"
        );
        assert!(translate_artifact_expr("(g 1)").is_err());
        assert!(translate_artifact_expr("(x 1)").is_err());
        assert!(translate_artifact_expr("6").is_err());
    }
}
