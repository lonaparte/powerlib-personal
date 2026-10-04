#!/usr/bin/env python3
"""Check the Agda field operation and its independent finite-matrix Lean endpoint."""
import argparse
import json
from pathlib import Path
import shutil
import sys
import tempfile

from bridge import extract
from common import ROOT, CACHE, RESULTS, CUBICAL_COMMIT, audit, check_lean, demand, digest

TARGET = ROOT / "theorems/generated/LTIFoundation.lean"
SNAPSHOT = ROOT / "dependencies/lti_wire.json"


def render(words, source_hash):
    if (len(words) > 64 or words[:2] != [20261004, 3]
            or any(type(word) is not int or word < 0 for word in words)):
        raise ValueError("Unsupported LTI field interface")
    position = 2

    def index(environment):
        nonlocal position
        if position >= len(words) or words[position] >= len(environment):
            raise ValueError("Unbound or truncated LTI coordinate")
        result = environment[words[position]]
        position += 1
        return result

    def expression(environment):
        nonlocal position
        if position >= len(words):
            raise ValueError("Truncated LTI expression")
        tag = words[position]
        position += 1
        if tag == 0:
            return f"A {index(environment)} {index(environment)}"
        if tag == 1:
            return f"x {index(environment)}"
        if tag == 2:
            return f"({expression(environment)} * {expression(environment)})"
        if tag == 3:
            binder = f"j{len(environment) - 1}"
            return f"(∑ {binder}, {expression((binder,) + environment)})"
        raise ValueError("Invalid LTI expression or binder scope")

    body = expression(("i",))
    if position != len(words):
        raise ValueError("Trailing LTI interface data")
    return f'''-- Generated from the scoped syntax executed by Agda's field operation.
-- Agda source SHA-256: {source_hash}
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import theorems.Attributes

namespace powerlib.generated
open scoped BigOperators

def linearField {{n : ℕ}} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) : ℝ := {body}

@[simp, powerlib_foundation] theorem linearField_spec {{n : ℕ}}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    linearField A x = A.mulVec x := rfl

end powerlib.generated
'''


def rebuild(write=False):
    demand(["lake", "build", "theorems.Attributes"])
    agda, cubical = CACHE / "agda", CACHE / "cubical"
    if demand([agda, "--numeric-version"]).strip() != "2.8.0":
        raise RuntimeError("Expected pinned Agda 2.8.0; run dependencies/setup.py")
    if demand(["git", "-C", cubical, "rev-parse", "HEAD"]).strip() != CUBICAL_COMMIT:
        raise RuntimeError("Cubical commit mismatch")
    if demand(["git", "-C", cubical, "status", "--porcelain", "--untracked-files=all"]).strip():
        raise RuntimeError("Cubical checkout must be clean")
    RESULTS.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="lti-bridge-", dir=RESULTS) as directory:
        stage = Path(directory)
        (stage / "theorems").mkdir()
        for name in ["LTIFoundation.agda"]:
            shutil.copy(ROOT / "theorems" / name, stage / "theorems" / name)
        shutil.copy(ROOT / "powerlib.agda-lib", stage)
        libraries = stage / "libraries"
        libraries.write_text(str(cubical / "cubical.agda-lib") + "\n")
        entry = stage / "theorems/LTIFoundation.agda"
        flags = [agda, f"--library-file={libraries}", "--no-default-libraries"]
        log = demand(flags + [entry], cwd=stage)
        path = json.dumps(str(entry))
        commands = (f'IOTCM {path} None Direct (Cmd_load {path} [])\n'
                    f'IOTCM {path} None Direct (Cmd_compute_toplevel DefaultCompute "wire")\n')
        normalized = demand(flags + ["--interaction-json", "--interaction-exit-on-error"],
                            input=commands, cwd=stage)
        words = extract(normalized)
        source_hash = digest(entry)
        content = render(words, source_hash)
        proof = stage / "LTIFoundation.lean"
        proof.write_text("import Lean\n" + content +
                         audit(["powerlib.generated.linearField_spec"], include_core=False))
        check_lean(proof)
        snapshot = json.dumps(words) + "\n"
        if write:
            TARGET.write_text(content)
            SNAPSHOT.write_text(snapshot)
        elif TARGET.read_text() != content or SNAPSHOT.read_text() != snapshot:
            raise RuntimeError("Generated LTI field is stale; run dependencies/lti_bridge.py --write")
        report = {"agda": "2.8.0", "cubical_commit": CUBICAL_COMMIT,
                  "agda_source_sha256": source_hash,
                  "wire": words, "generated_sha256": digest(TARGET),
                  "status": "AGDA_AND_LEAN_CHECKED"}
        (RESULTS / "lti-bridge.log").write_text(log + normalized)
        (RESULTS / "lti-bridge.json").write_text(json.dumps(report, indent=2) + "\n")
        return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    try:
        print(json.dumps(rebuild(parser.parse_args().write), indent=2))
    except (ValueError, OSError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
