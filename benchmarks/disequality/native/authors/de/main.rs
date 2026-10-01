use std::env;
use std::fs;
use std::time::Instant;

use disegg::{*};

macro_rules! parse {($e:expr) => { $e.parse().unwrap() }}

fn equate(egraph: &mut EGraph<SymbolLang, ()>, lhs: &str, rhs: &str) {
  let id1 = egraph.add_expr(&parse!(lhs));
  let id2 = egraph.add_expr(&parse!(rhs));
  egraph.union(id1, id2);
}

fn disequate(egraph: &mut EGraph<SymbolLang, ()>, lhs: &str, rhs: &str) {
  let id1 = egraph.add_expr(&parse!(lhs));
  let id2 = egraph.add_expr(&parse!(rhs));
  egraph.disunion(id1, id2);
}

fn main() -> () {
  let args: Vec<String> = env::args().collect();

  assert!(args.len() == 4, "{} [file.in] [base number] [diseq number]", args[0]);

  let content = fs::read_to_string(&args[1]).expect(&format!("Could not read {}", &args[1]));
  let exprs = content.split("\n").collect::<Vec<_>>();

  let base_number: usize = args[2].parse().unwrap();
  let diseq_number: usize = args[3].parse().unwrap();

  assert!(2*(base_number + diseq_number) <= exprs.len(),
          "Not enough expressions to fill the e-graph");



  let mut g: EGraph<SymbolLang, ()> = Default::default();

  // making all the numbers unequal
  for x in 1..=5 { for y in x+1..5 {
    disequate(&mut g, &format!("{x}"), &format!("{y}"));
  }}



  let start = Instant::now();

  {
    let mut i : usize = 0;

    // adding the equalities
    while i+1 < 2*base_number {
      equate(&mut g, &exprs[i], &exprs[i+1]);
      i += 2;
    }

    // adding the disequalities
    while i+1 < 2*(base_number + diseq_number) {
      disequate(&mut g, &exprs[i], &exprs[i+1]);
      i += 2;
    }

    g.rebuild();

    let contra_time = Instant::now();
    {
      let c = if !g.is_consistent() { "Y" } else { "N" };

      println!("method,base,diseq_num,contradiction,time_to_find_contradiction,full_time,number_nodes,number_classes,ratio_nodes_classes");
      println!("de,{base_number},{diseq_number:0>8},{c},{:.2?},{:.2?},{},{},{}", contra_time.elapsed(), start.elapsed(), g.total_size(), g.number_of_classes(), g.total_size() as f32 / g.number_of_classes() as f32);
    }
  }

}
