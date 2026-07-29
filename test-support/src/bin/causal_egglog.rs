fn main() {
    egglog::cli(
        egglog::EGraph::default(),
        std::env::args_os(),
        egglog::EGraph::default,
    );
}
