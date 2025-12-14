#!/usr/bin/env python3
"""
Copy non-.diff output files from test-diffs/BACKEND/ to examples/BACKEND/

This script copies generated backend outputs (e.g., .efg, .sol, .vy files) from the
test-diffs directory structure to corresponding subdirectories under examples/.

Directory structure:
  test-diffs/gambit/Simple.efg      -> examples/gambit/Simple.efg
  test-diffs/solidity/Simple.sol    -> examples/solidity/Simple.sol
  etc.

.diff files are excluded from copying.
"""

import shutil
from pathlib import Path

# Backend directories to process
BACKENDS = ["clarity", "gambit", "graphviz", "lightning", "smt", "solidity", "vyper"]

def copy_test_outputs():
    """Copy non-.diff files from test-diffs/BACKEND/ to examples/BACKEND/"""

    for backend in BACKENDS:
        src_dir = Path("test-diffs") / backend
        dst_dir = Path("examples") / backend

        if not src_dir.exists():
            print(f"Warning: Source directory {src_dir} does not exist, skipping")
            continue

        # Create destination directory
        dst_dir.mkdir(parents=True, exist_ok=True)

        # Copy all non-.diff files
        count = 0
        for src_file in src_dir.iterdir():
            # Skip directories and .diff files
            if src_file.is_dir() or src_file.suffix == ".diff":
                continue

            # Copy the file
            dst_file = dst_dir / src_file.name
            shutil.copy2(src_file, dst_file)
            count += 1

        print(f"Copied {count} files from {src_dir} to {dst_dir}")

    print("Done!")

if __name__ == "__main__":
    copy_test_outputs()
