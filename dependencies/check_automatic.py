#!/usr/bin/env python3
"""Run witness-free stability synthesis, with separate library reuse checks."""
import json
from pathlib import Path
import tempfile

from common import DEPENDENCIES, RESULTS, demand
from nonlinear import SEMANTIC_THEOREMS, atp


def term(coefficient, a, b):
    return {"coefficient": str(coefficient), "powers": [a, b]}


def withheld_models():
    # Model data only. Neither case has a named stability theorem in the library.
    # The second quartic requires a nonzero rational Gram parameter.
    return [
        {"schema": "powerlib.polynomial2.v1", "field": [
            [term(-3, 1, 0), term(1, 0, 1), term(-2, 3, 0), term(-3, 1, 2)],
            [term(-2, 0, 1), term(-4, 2, 1), term(-2, 0, 3)]]},
        {"schema": "powerlib.polynomial2.v1", "field": [
            [term(-1, 1, 0), term(1, 0, 1), term(-1, 3, 0), term(-3, 2, 1),
             term(-3, 1, 2), term(-1, 0, 3)],
            [term(-2, 0, 1), term(-2, 3, 0), term(-6, 2, 1),
             term(-6, 1, 2), term(-2, 0, 3)]]},
    ]


def check_automatic():
    for filename, marker in [("API.lean", "POWERLIB_API_OK"),
                             ("RuleReuse.lean", "POWERLIB_RULE_REUSE_OK"),
                             ("Upstream.lean", "POWERLIB_UPSTREAM_REUSE_OK")]:
        output = demand(["lake", "env", "lean", DEPENDENCIES / "tests" / filename])
        if output.count(marker) != 1:
            raise RuntimeError(f"Missing API or library-reuse evidence: {marker}")
    RESULTS.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="withheld-models-", dir=RESULTS) as directory:
        path = Path(directory) / "model.json"
        for index, model in enumerate(withheld_models()):
            path.write_text(json.dumps(model))
            report = atp(path)
            if (report["status"] != "ACCEPTED" or report["kernel_verified"] is not True
                    or report["maturity"] != "S-level"
                    or report["semantic_theorems"] != SEMANTIC_THEOREMS
                    or report["certificate"]["P"][0][1] == "0"):
                raise RuntimeError(f"Withheld nonlinear model {index} was not automatically proved")
        # A stable linearization alone cannot admit the full nonlinear system.
        bad = {"schema": "powerlib.polynomial2.v1", "field": [
            [term(-1, 1, 0), term(1, 3, 0)], [term(-1, 0, 1)]]}
        path.write_text(json.dumps(bad))
        report = atp(path)
        if (report["status"] != "UNPROVED" or report["kernel_verified"] is not False
                or "proof" in report or "semantic_theorems" in report):
            raise RuntimeError("Uncertified nonlinear field was admitted or falsely refuted")
    count = len(withheld_models())
    print(f"POWERLIB_WITNESS_FREE_NONLINEAR_OK: {count} fields", flush=True)
    return count


if __name__ == "__main__":
    check_automatic()
