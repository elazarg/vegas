#!/usr/bin/env python3
"""
Install external tools required by Ethereum integration tests: solc and anvil.

Usage:
    python setup-eth-tools.py

Steps:
  1. Create a Python venv in .venv/ (if absent)
  2. Install solc-select from requirements-test.txt
  3. Install and activate solc 0.8.31
  4. Install Foundry (provides anvil) via foundryup
  5. Verify both tools respond on PATH
"""

import os
import platform
import shutil
import subprocess
import sys
from pathlib import Path

SOLC_VERSION = "0.8.31"
REPO_ROOT = Path(__file__).resolve().parent
VENV_DIR = REPO_ROOT / ".venv"
REQUIREMENTS = REPO_ROOT / "requirements-test.txt"

IS_WINDOWS = platform.system() == "Windows"


def venv_bin(name: str) -> Path:
    """Return path to a binary inside the venv."""
    if IS_WINDOWS:
        return VENV_DIR / "Scripts" / (name + ".exe")
    return VENV_DIR / "bin" / name


def run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    print(f"  $ {' '.join(cmd)}")
    return subprocess.run(cmd, check=True, **kwargs)


def ensure_venv():
    if VENV_DIR.exists():
        print(f"venv already exists at {VENV_DIR}")
        return
    print(f"Creating venv at {VENV_DIR} ...")
    run([sys.executable, "-m", "venv", str(VENV_DIR)])


def install_solc():
    pip = str(venv_bin("pip"))
    solc_select = str(venv_bin("solc-select"))

    print("Installing solc-select ...")
    run([pip, "install", "-r", str(REQUIREMENTS)])

    print(f"Installing solc {SOLC_VERSION} ...")
    run([solc_select, "install", SOLC_VERSION])
    run([solc_select, "use", SOLC_VERSION])


def install_foundry():
    if shutil.which("anvil"):
        print("anvil already on PATH — skipping Foundry install")
        return

    if IS_WINDOWS:
        print("Foundry install on Windows: use 'foundryup' from WSL or Git Bash,")
        print("or install via 'cargo install --git https://github.com/foundry-rs/foundry anvil'.")
        print("See https://book.getfoundry.sh/getting-started/installation")
        return

    # Unix: use foundryup
    foundryup = shutil.which("foundryup")
    if foundryup:
        print("Running foundryup ...")
        run([foundryup])
    else:
        print("Installing Foundry via foundryup installer ...")
        result = subprocess.run(
            ["curl", "-L", "https://foundry.paradigm.xyz"],
            capture_output=True, text=True, check=True,
        )
        subprocess.run(["bash"], input=result.stdout, check=True)
        # foundryup is now at ~/.foundry/bin/foundryup
        home_foundryup = Path.home() / ".foundry" / "bin" / "foundryup"
        if home_foundryup.exists():
            run([str(home_foundryup)])
        else:
            print("WARNING: foundryup not found after install — run 'foundryup' manually")


def verify():
    ok = True

    # solc — may be on PATH via solc-select's shim or in the venv
    solc = shutil.which("solc") or str(venv_bin("solc"))
    try:
        r = subprocess.run([solc, "--version"], capture_output=True, text=True, timeout=10)
        if r.returncode == 0:
            version_line = [l for l in r.stdout.splitlines() if "Version:" in l]
            print(f"  solc: {version_line[0].strip() if version_line else r.stdout.strip()}")
        else:
            print(f"  solc: exit code {r.returncode}")
            ok = False
    except FileNotFoundError:
        print("  solc: NOT FOUND")
        print(f"    Hint: add {VENV_DIR / ('Scripts' if IS_WINDOWS else 'bin')} to your PATH")
        ok = False

    # anvil
    anvil = shutil.which("anvil")
    if anvil:
        try:
            r = subprocess.run([anvil, "--version"], capture_output=True, text=True, timeout=10)
            print(f"  anvil: {r.stdout.strip()}")
        except Exception as e:
            print(f"  anvil: error — {e}")
            ok = False
    else:
        print("  anvil: NOT FOUND")
        foundry_bin = Path.home() / ".foundry" / "bin"
        if foundry_bin.exists():
            print(f"    Hint: add {foundry_bin} to your PATH")
        ok = False

    return ok


def main():
    print("=== Vegas Ethereum Test Tool Setup ===\n")

    ensure_venv()
    install_solc()
    install_foundry()

    print("\nVerifying tools ...")
    if verify():
        print("\nAll tools ready.")
    else:
        print("\nSome tools are missing — see hints above.")
        print("Ethereum tests will be skipped until both solc and anvil are on PATH.")
        sys.exit(1)


if __name__ == "__main__":
    main()
