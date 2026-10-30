"""Run the fixed Math12 cross-engine graph test under the shared native cap."""

import argparse
import os
import subprocess
from pathlib import Path

from native_memory import NATIVE_LIMIT_BYTES, native_memory_command


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test-binary", type=Path, required=True)
    args = parser.parse_args()
    command, environment = native_memory_command(
        [str(args.test_binary.resolve()), "--exact", "tests::math12_graph_parity", "--ignored", "--nocapture"],
        os.environ | {"MATH12_MEMORY_LIMIT_BYTES": str(NATIVE_LIMIT_BYTES), "RUST_TEST_THREADS": "1"},
        limit_bytes=None,  # libtest owns argv; the test installs the cap.
    )
    subprocess.run(command, env=environment, check=True, timeout=300)


if __name__ == "__main__":
    main()
