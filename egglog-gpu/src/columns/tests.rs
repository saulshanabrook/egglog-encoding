use super::*;
use crate::AdapterMode;

#[test]
#[ignore = "requires software Vulkan"]
fn tiled_operators_cache_and_submission_boundaries() {
    let gpu = Arc::new(GpuOps::new(
        Arc::new(DeviceJoin::new(AdapterMode::Software).unwrap()),
        1_000_000,
    ));
    scans(&gpu);
    sorts(&gpu);
    lookups(&gpu);
    batches(&gpu);
    paired_readbacks(&gpu);
    split_rows(&gpu);
    concurrent_readbacks(gpu);
}

fn split_rows(gpu: &GpuOps) {
    let rows: Vec<_> = (0..129)
        .map(|i| vec![Value::new(i), Value::new(1000 - i)])
        .collect();
    let matrix = gpu.upload(&rows, 2).unwrap();
    // Request a hypothetical wide action row so small inputs exercise the
    // same byte-budget boundary used by real large match batches.
    let width = gpu.dev.device.limits().max_storage_buffer_binding_size as usize / (17 * 4) + 1;
    let batches = gpu.split_for_width(matrix, width).unwrap();
    assert!(batches.len() > 1 && batches.iter().all(|batch| batch.rows <= 17));
    let actual: Vec<_> = batches
        .iter()
        .flat_map(|batch| gpu.download(batch).unwrap())
        .collect();
    assert_eq!(actual, rows);
    let nullary = gpu.upload(&vec![Vec::new(); 129], 0).unwrap();
    let batches = gpu.split_for_width(nullary, width).unwrap();
    assert_eq!(
        batches
            .iter()
            .map(|batch| gpu.download(batch).unwrap().len())
            .sum::<usize>(),
        129
    );
}

fn scans(gpu: &GpuOps) {
    for n in [
        0, 1, 2, 63, 64, 65, 127, 128, 129, 4095, 4096, 4097, 262_145,
    ] {
        let values: Vec<u32> = (0..n).map(|i| (i % 3) as u32).collect();
        let expected: Vec<_> = values
            .iter()
            .scan(0u32, |sum, &v| {
                *sum = sum.saturating_add(v);
                Some(*sum)
            })
            .collect();
        let (prefix, total) = gpu.prefix(gpu.words(&values).unwrap(), n).unwrap();
        assert_eq!(
            total,
            expected.last().copied().unwrap_or(0) as usize,
            "n={n}"
        );
        assert_eq!(gpu.read(&prefix, 0, n).unwrap(), expected, "n={n}");
    }
    let mut values = vec![2u32; 129];
    values[0] = u32::MAX - 3;
    let prefix = gpu.scan(gpu.words(&values).unwrap(), values.len()).unwrap();
    let mut expected = vec![u32::MAX; 129];
    expected[0] = u32::MAX - 3;
    expected[1] = u32::MAX - 1;
    assert_eq!(gpu.read(&prefix, 0, 129).unwrap(), expected);
    assert!(gpu.prefix(gpu.words(&[1_000_000, 1]).unwrap(), 2).is_err());
}

fn sorts(gpu: &GpuOps) {
    for n in [
        0, 1, 2, 63, 64, 65, 127, 128, 129, 1023, 1024, 1025, 4097, 16_385,
    ] {
        let rows: Vec<_> = (0..n)
            .map(|i| {
                vec![
                    Value::new(((n - i) % 37) as u32),
                    Value::new((i % 5) as u32),
                    Value::new(u32::MAX - 1 - (i % 11) as u32),
                ]
            })
            .collect();
        let matrix = gpu.upload(&rows, 3).unwrap();
        for keys in [vec![], vec![0], vec![1, 0], vec![2]] {
            let mut expected: Vec<usize> = (0..n).collect();
            expected.sort_by_key(|&i| keys.iter().map(|&k| rows[i][k]).collect::<Vec<_>>());
            let order = gpu.sort(&matrix, &keys).unwrap();
            assert_eq!(
                gpu.read(&order, 0, n).unwrap(),
                expected.into_iter().map(|i| i as u32).collect::<Vec<_>>(),
                "n={n}, keys={keys:?}"
            );
            let dispatches = gpu.dispatches.load(Ordering::Relaxed);
            let hits = gpu.sort_cache_hits.load(Ordering::Relaxed);
            let cached = gpu.sort(&matrix.clone(), &keys).unwrap();
            assert_eq!(gpu.dispatches.load(Ordering::Relaxed), dispatches);
            assert_eq!(gpu.sort_cache_hits.load(Ordering::Relaxed), hits + 1);
            assert_eq!(
                gpu.read(&cached, 0, n).unwrap(),
                gpu.read(&order, 0, n).unwrap()
            );
        }
    }
}

fn lookups(gpu: &GpuOps) {
    for n in [0, 1, 63, 64, 65, 129, 4097] {
        let rows: Vec<_> = (0..n)
            .map(|i| {
                vec![
                    Value::new((i % 37) as u32),
                    Value::new(((i / 37) % 3) as u32),
                    Value::new(i as u32),
                ]
            })
            .collect();
        let matrix = gpu.upload(&rows, 3).unwrap();
        for probes in [0, 1, 8, 9, 17] {
            let keys: Vec<_> = (0..probes)
                .map(|i| {
                    vec![
                        Value::new(((i * 7) % 40) as u32),
                        Value::new((i % 4) as u32),
                    ]
                })
                .collect();
            let expected: Vec<_> = keys
                .iter()
                .map(|key| {
                    rows.iter()
                        .find(|row| &row[..2] == key)
                        .map_or(vec![Value::new(0), Value::new(0)], |row| {
                            vec![Value::new(1), row[2]]
                        })
                })
                .collect();
            let keys = gpu.upload(&keys, 2).unwrap();
            let found = gpu.lookup(&keys, &matrix, 2).unwrap();
            assert_eq!(
                gpu.download(&found).unwrap(),
                expected,
                "rows={n}, probes={probes}"
            );
            // A new snapshot must never reuse the old snapshot's permutation.
            let reversed = gpu
                .upload(&rows.iter().rev().cloned().collect::<Vec<_>>(), 3)
                .unwrap();
            let found = gpu.lookup(&keys, &reversed, 2).unwrap();
            let expected: Vec<_> = gpu
                .download(&keys)
                .unwrap()
                .iter()
                .map(|key| {
                    rows.iter()
                        .rev()
                        .find(|row| &row[..2] == key)
                        .map_or(vec![Value::new(0), Value::new(0)], |row| {
                            vec![Value::new(1), row[2]]
                        })
                })
                .collect();
            assert_eq!(gpu.download(&found).unwrap(), expected);
        }
    }
    let rows = vec![vec![Value::new(17)], vec![Value::new(23)]];
    let table = gpu.upload(&rows, 1).unwrap();
    for n in [1, 9] {
        let keys = gpu.upload(&vec![vec![]; n], 0).unwrap();
        let found = gpu.lookup(&keys, &table, 0).unwrap();
        assert_eq!(
            gpu.download(&found).unwrap(),
            vec![vec![Value::new(1), Value::new(17)]; n]
        );
    }
    let unique = gpu.unique_by(table, &[]).unwrap();
    assert_eq!(gpu.download(&unique).unwrap(), vec![rows[0].clone()]);
}

fn batches(gpu: &GpuOps) {
    gpu.flush();
    let rows: Vec<_> = (0..128)
        .map(|i| vec![Value::new(i), Value::new(128 - i)])
        .collect();
    let mut current = gpu.upload(&rows, 2).unwrap();
    let submissions = gpu.submissions.load(Ordering::Relaxed);
    for _ in 0..300 {
        current = gpu.project(&current, &[(1, 1), (1, 0)]).unwrap();
    }
    let before_read = gpu.submissions.load(Ordering::Relaxed) - submissions;
    assert!(
        before_read < 30,
        "dependent projections should share submissions"
    );
    assert_eq!(gpu.download(&current).unwrap(), rows);
    assert_eq!(
        gpu.submissions.load(Ordering::Relaxed) - submissions,
        before_read + 1
    );
}

fn paired_readbacks(gpu: &GpuOps) {
    for (left, left_cols, right, right_cols) in [
        (vec![vec![Value::new(17)]], 1, vec![vec![]; 3], 0),
        (vec![], 1, vec![vec![Value::new(23), Value::new(29)]], 2),
        (vec![vec![]; 2], 0, vec![vec![]; 4], 0),
    ] {
        let a = gpu.upload(&left, left_cols).unwrap();
        let b = gpu.upload(&right, right_cols).unwrap();
        let before = gpu.readbacks.load(Ordering::Relaxed);
        assert_eq!(gpu.download_pair(&a, &b).unwrap(), (left, right));
        assert!(gpu.readbacks.load(Ordering::Relaxed) - before <= 1);
    }
}

fn concurrent_readbacks(gpu: Arc<GpuOps>) {
    let workers: Vec<_> = (0..4)
        .map(|worker| {
            let gpu = gpu.clone();
            std::thread::spawn(move || {
                for round in 0..8 {
                    let value = worker * 8 + round;
                    let counts = gpu.words(&vec![value; 65]).unwrap();
                    let (_, total) = gpu.prefix(counts, 65).unwrap();
                    assert_eq!(total, value as usize * 65);
                }
            })
        })
        .collect();
    for worker in workers {
        worker.join().unwrap();
    }
}
