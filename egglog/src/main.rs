use egglog::EGraph;

#[cfg(feature = "bin")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    egglog::cli_with_args_and_factory(EGraph::default(), std::env::args_os(), EGraph::default);
}
