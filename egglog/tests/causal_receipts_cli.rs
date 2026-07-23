use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_PROGRAM: AtomicU64 = AtomicU64::new(0);

fn temporary_program() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "egglog-causal-receipts-cli-{}-{}.egg",
        std::process::id(),
        NEXT_PROGRAM.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, "(relation R (i64)) (R 1) (check (R 1))").unwrap();
    path
}

#[test]
fn causal_receipts_reject_parallel_activation() {
    let program = temporary_program();
    let output = Command::new(env!("CARGO_BIN_EXE_egglog"))
        .args(["--threads", "2", "--causal-receipts"])
        .arg(&program)
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "causal receipts require --threads 1; parallel causal capture is unsupported"
        )
    );
    std::fs::remove_file(program).unwrap();
}
