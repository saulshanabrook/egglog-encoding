//! FlatTable microbenchmarks against the proof-shaped SortedWritesTable it
//! replaces. The fixed-total-work thread cases measure write scalability, not
//! independent benchmark copies.

use std::sync::OnceLock;

use divan::{Bencher, counter::ItemsCount};
use egglog_concurrency::{ThreadPool, without_current_pool};
use egglog_core_relations::{ColumnId, Database, FlatTable, SortedWritesTable, Table, Value};
use egglog_numeric_id::NumericId;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const COLS: usize = 4;
const KEY_COLS: usize = 2;
const ROW_COUNT: usize = 1 << 20;
const BATCH_ROWS: usize = 8 * 1024;
type BenchRow = [Value; COLS];

static WORKLOAD: OnceLock<Box<[BenchRow]>> = OnceLock::new();

fn main() {
    divan::main();
}

fn workload() -> &'static [BenchRow] {
    WORKLOAD.get_or_init(|| {
        (0..ROW_COUNT)
            .map(|i| {
                let id = u32::try_from(i).unwrap();
                // Payload, freshly minted final id, Unit, merge-epoch timestamp.
                [
                    Value::new(id.wrapping_mul(0x9e37_79b9)),
                    Value::new(id),
                    Value::new(0),
                    Value::new(0),
                ]
            })
            .collect::<Vec<_>>()
            .into_boxed_slice()
    })
}

#[derive(Clone, Copy)]
enum Kind {
    Flat,
    SortedProofShape,
}

enum Store {
    Flat(Box<FlatTable>),
    Sorted(Box<SortedWritesTable>),
}

impl Store {
    fn new(kind: Kind) -> Self {
        match kind {
            Kind::Flat => Self::Flat(Box::new(FlatTable::new(COLS))),
            Kind::SortedProofShape => Self::Sorted(Box::new(SortedWritesTable::new(
                KEY_COLS,
                COLS,
                Some(ColumnId::from_usize(COLS - 1)),
                vec![ColumnId::new(1)],
                Box::new(|_, _, _, _| {
                    panic!("the proof-shaped workload must have unique minted ids")
                }),
            ))),
        }
    }

    fn stage(&self, rows: &[BenchRow], threads: usize) {
        match self {
            Self::Flat(table) => stage_table(table.as_ref(), rows, threads),
            Self::Sorted(table) => stage_table(table.as_ref(), rows, threads),
        }
    }

    fn merge(&mut self, db: &Database) -> usize {
        db.with_execution_state(|exec_state| match self {
            Self::Flat(table) => {
                table.merge(exec_state);
            }
            Self::Sorted(table) => {
                table.merge(exec_state);
            }
        });
        self.len()
    }

    fn len(&self) -> usize {
        match self {
            Self::Flat(table) => table.len(),
            Self::Sorted(table) => table.len(),
        }
    }

    fn checksum(&self) -> u64 {
        match self {
            Self::Flat(table) => scan_checksum(table.as_ref()),
            Self::Sorted(table) => scan_checksum(table.as_ref()),
        }
    }
}

struct Input {
    db: Database,
    store: Store,
}

impl Input {
    fn new(kind: Kind) -> Self {
        Self {
            db: Database::default(),
            store: Store::new(kind),
        }
    }

    fn merge(&mut self) -> usize {
        self.store.merge(&self.db)
    }
}

fn with_pool<R>(pool: &Option<ThreadPool>, f: impl FnOnce() -> R) -> R {
    match pool {
        Some(pool) => pool.install(f),
        None => without_current_pool(f),
    }
}

fn make_pool(threads: usize) -> Option<ThreadPool> {
    (threads > 1).then(|| ThreadPool::new(threads))
}

fn stage_range<T: Table>(table: &T, rows: &[BenchRow]) {
    for batch in rows.chunks(BATCH_ROWS) {
        let mut buffer = table.new_buffer();
        for row in batch {
            buffer.stage_insert(row);
        }
    }
}

fn stage_table<T: Table>(table: &T, rows: &[BenchRow], threads: usize) {
    if threads == 1 {
        stage_range(table, rows);
        return;
    }

    let rows_per_worker = rows.len().div_ceil(threads);
    egglog_concurrency::scope(|scope| {
        for worker_rows in rows.chunks(rows_per_worker) {
            scope.spawn(move |_| stage_range(table, worker_rows));
        }
    });
}

fn scan_checksum<T: Table>(table: &T) -> u64 {
    let all = table.all();
    let mut checksum = 0u64;
    table.scan_generic(all.as_ref(), |_, row| {
        for value in row {
            checksum = checksum.rotate_left(5) ^ u64::from(value.rep());
        }
    });
    checksum
}

fn bench_append<const THREADS: usize>(bench: Bencher, kind: Kind) {
    let pool = make_pool(THREADS);
    let rows = workload();

    bench
        .counter(ItemsCount::new(ROW_COUNT))
        .with_inputs(|| with_pool(&pool, || Input::new(kind)))
        .bench_local_refs(|input| {
            with_pool(&pool, || input.store.stage(rows, THREADS));
        });
}

fn bench_merge<const THREADS: usize>(bench: Bencher, kind: Kind) {
    let pool = make_pool(THREADS);
    let rows = workload();

    bench
        .counter(ItemsCount::new(ROW_COUNT))
        .with_inputs(|| {
            with_pool(&pool, || {
                let input = Input::new(kind);
                input.store.stage(rows, THREADS);
                input
            })
        })
        .bench_local_refs(|input| {
            with_pool(&pool, || {
                let len = input.merge();
                assert_eq!(len, ROW_COUNT);
                len
            })
        });
}

fn bench_write<const THREADS: usize>(bench: Bencher, kind: Kind) {
    let pool = make_pool(THREADS);
    let rows = workload();

    bench
        .counter(ItemsCount::new(ROW_COUNT))
        .with_inputs(|| with_pool(&pool, || Input::new(kind)))
        .bench_local_refs(|input| {
            with_pool(&pool, || {
                input.store.stage(rows, THREADS);
                let len = input.merge();
                assert_eq!(len, ROW_COUNT);
                len
            })
        });
}

fn bench_scan(bench: Bencher, kind: Kind) {
    let rows = workload();

    bench
        .counter(ItemsCount::new(ROW_COUNT))
        .with_inputs(|| {
            without_current_pool(|| {
                let mut input = Input::new(kind);
                input.store.stage(rows, 1);
                assert_eq!(input.merge(), ROW_COUNT);
                input
            })
        })
        .bench_local_refs(|input| without_current_pool(|| input.store.checksum()));
}

#[divan::bench(consts = [1, 2, 4, 8, 16], sample_count = 10, sample_size = 1)]
fn append_flat<const THREADS: usize>(bench: Bencher) {
    bench_append::<THREADS>(bench, Kind::Flat);
}

#[divan::bench(consts = [1, 2, 4, 8, 16], sample_count = 10, sample_size = 1)]
fn append_sorted<const THREADS: usize>(bench: Bencher) {
    bench_append::<THREADS>(bench, Kind::SortedProofShape);
}

#[divan::bench(consts = [1, 2, 4, 8, 16], sample_count = 10, sample_size = 1)]
fn merge_flat<const THREADS: usize>(bench: Bencher) {
    bench_merge::<THREADS>(bench, Kind::Flat);
}

#[divan::bench(consts = [1, 2, 4, 8, 16], sample_count = 10, sample_size = 1)]
fn merge_sorted<const THREADS: usize>(bench: Bencher) {
    bench_merge::<THREADS>(bench, Kind::SortedProofShape);
}

#[divan::bench(consts = [1, 2, 4, 8, 16], sample_count = 10, sample_size = 1)]
fn write_flat<const THREADS: usize>(bench: Bencher) {
    bench_write::<THREADS>(bench, Kind::Flat);
}

#[divan::bench(consts = [1, 2, 4, 8, 16], sample_count = 10, sample_size = 1)]
fn write_sorted<const THREADS: usize>(bench: Bencher) {
    bench_write::<THREADS>(bench, Kind::SortedProofShape);
}

#[divan::bench(sample_count = 25, sample_size = 1)]
fn scan_flat(bench: Bencher) {
    bench_scan(bench, Kind::Flat);
}

#[divan::bench(sample_count = 25, sample_size = 1)]
fn scan_sorted(bench: Bencher) {
    bench_scan(bench, Kind::SortedProofShape);
}
