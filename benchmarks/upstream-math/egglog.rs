fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let n: usize = args.next().ok_or("usage: egglog-math N (1–13)")?.parse()?;
    if !(1..=13).contains(&n) || args.next().is_some() {
        return Err("usage: egglog-math N (1–13)".into());
    }
    let mut egraph = egglog::EGraph::new(1);
    egraph.parse_and_run_program(Some("math.egg".into()), include_str!("math.egg"))?;
    let run = egraph.parse_program(None, &format!("(run {n})"))?;
    egraph.run_program(run)?;
    let completed = egraph.get_overall_run_report().iterations.len();
    if completed != n {
        return Err(format!("Egglog stopped after {completed} of {n} required iterations").into());
    }
    Ok(())
}
