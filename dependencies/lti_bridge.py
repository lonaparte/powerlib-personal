#!/usr/bin/env python3
"""Check the Agda field operation and its independent finite-matrix Lean endpoint."""
import argparse
import json
import sys

from bridge import rebuild_checked
from common import ROOT, RESULTS

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
    return rebuild_checked(
        sources={"agda_source_sha256": "LTIFoundation.agda"}, render=render,
        theorem="powerlib.generated.linearField_spec", target=TARGET, snapshot=SNAPSHOT,
        report_name="lti-bridge", write=write, root=ROOT, results=RESULTS)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    try:
        print(json.dumps(rebuild(parser.parse_args().write), indent=2))
    except (ValueError, OSError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
