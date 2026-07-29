use egglog::EGraph;

#[cfg(feature = "bin")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    egglog::cli(EGraph::default(), std::env::args_os(), EGraph::default);
}
