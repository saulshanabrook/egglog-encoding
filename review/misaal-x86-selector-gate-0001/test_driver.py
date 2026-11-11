"""Data-only fixture identity checks; never launch the driver or native tools."""

import hashlib
import tempfile
import unittest
from pathlib import Path

from run import source_inventory


class SourcePinTests(unittest.TestCase):
    def test_added_cpp_and_changed_bytes_change_prebuild_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Legalizer.cpp"
            source.write_text("original")
            pinned = source_inventory(root)
            self.assertEqual(pinned, {"Legalizer.cpp": hashlib.sha256(b"original").hexdigest()})
            source.write_text("modified")
            self.assertNotEqual(source_inventory(root), pinned)
            source.write_text("original")
            (root / "extra.cpp").write_text("native extra glob member")
            self.assertNotEqual(source_inventory(root), pinned)

    def test_symlinks_refused_even_when_target_bytes_match(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Legalizer.cpp").write_text("original")
            (root / "alias.cpp").symlink_to(root / "Legalizer.cpp")
            with self.assertRaisesRegex(ValueError, "linked native source"):
                source_inventory(root)


if __name__ == "__main__":
    unittest.main()
