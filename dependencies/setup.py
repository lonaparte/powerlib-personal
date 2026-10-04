#!/usr/bin/env python3
"""Install user-local Agda/Cubical dependencies, then check both proof systems."""
import hashlib
import platform
import shutil
import sys
import tarfile
import urllib.request

from common import ROOT, DEPENDENCIES, CACHE, CUBICAL_COMMIT, demand

AGDA_URL = "https://github.com/agda/agda/releases/download/v2.8.0/Agda-v2.8.0-linux.tar.xz"
AGDA_SHA256 = "824081b8dcbe431289a50ac6bd83e451f390c51c3884ac7a8c4a5c0df2632faf"


def setup():
    if not shutil.which("lake") or not shutil.which("git"):
        raise RuntimeError("Install Lean/Elan and Git first")
    if sys.version_info < (3, 12):
        raise RuntimeError("Use Python 3.12 or newer")
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise RuntimeError("This minimal setup supports Linux x86_64")
    CACHE.mkdir(parents=True, exist_ok=True)
    agda = CACHE / "agda"
    if not agda.exists():
        print("Downloading Agda 2.8.0 (no root privileges needed)", flush=True)
        archive = CACHE / "agda.tar.xz"
        urllib.request.urlretrieve(AGDA_URL, archive)
        if hashlib.sha256(archive.read_bytes()).hexdigest() != AGDA_SHA256:
            raise RuntimeError("Agda archive checksum mismatch")
        with tarfile.open(archive) as bundle:
            bundle.extractall(CACHE, filter="data")
        agda.chmod(0o755)
    if demand([agda, "--numeric-version"]).strip() != "2.8.0":
        raise RuntimeError("Expected Agda 2.8.0")
    cubical = CACHE / "cubical"
    if not cubical.exists():
        print("Downloading pinned Cubical library", flush=True)
        demand(["git", "clone", "--depth", "1", "--branch", "v0.9",
                "https://github.com/agda/cubical.git", cubical])
    if demand(["git", "-C", cubical, "rev-parse", "HEAD"]).strip() != CUBICAL_COMMIT:
        raise RuntimeError("Existing Cubical checkout has the wrong commit")
    print("Fetching Mathlib cache", flush=True)
    print(demand(["lake", "exe", "cache", "get", "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
                  "Mathlib.Tactic"], timeout=1800), end="", flush=True)
    print("Checking Agda and its Lean conversion", flush=True)
    print(demand([sys.executable, DEPENDENCIES / "bridge.py"], timeout=1800), end="", flush=True)
    print("Building the Lean library", flush=True)
    print(demand(["lake", "build"], timeout=1800), end="", flush=True)
    print(demand(["lake", "env", "lean", DEPENDENCIES / "tests/Audit.lean"]), end="", flush=True)
    print("Setup complete. Run the ATP and ATD examples from the README.")


if __name__ == "__main__":
    try:
        setup()
    except (RuntimeError, OSError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
