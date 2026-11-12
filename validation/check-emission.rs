use egglog_experimental::slotted::new_egraph_with_proofs;
use std::{env, fs};

fn main() {
    let args = env::args().skip(1).collect::<Vec<_>>();
    assert_eq!(args.len(), 2);
    let before = fs::read_to_string(&args[0]).unwrap();
    let after = fs::read_to_string(&args[1]).unwrap();
    assert_eq!(before, after, "emitted bytes differ");
    let mut left_graph = new_egraph_with_proofs();
    let mut right_graph = new_egraph_with_proofs();
    let left = left_graph.parse_program(None, &before).unwrap();
    let right = right_graph.parse_program(None, &after).unwrap();
    // Commands do not implement Eq. Compare each parsed command's canonical
    // rendering as well as the original bytes above.
    let left = left.iter().map(ToString::to_string).collect::<Vec<_>>();
    let right = right.iter().map(ToString::to_string).collect::<Vec<_>>();
    assert_eq!(left, right, "parsed command sequences differ");
    println!("{}", left.len());
}
