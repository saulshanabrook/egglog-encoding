fn main() {
    egglog::cli(
        egglog_experimental::new_experimental_egraph(),
        std::env::args_os(),
        egglog_experimental::new_experimental_egraph_for_proofs,
    );
}
