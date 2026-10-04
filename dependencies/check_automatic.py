#!/usr/bin/env python3
"""Compile independent consumers for every theorem type exported by Lean."""
import re
from common import DEPENDENCIES, RESULTS, audit, check_lean, demand


def check_automatic():
    demand(["lake", "env", "lean", DEPENDENCIES / "tests/Automatic.lean"])
    exported = demand(["lake", "env", "lean", DEPENDENCIES / "tests/ExportTheorems.lean"])
    begin, end = "POWERLIB_EXPORT_BEGIN\n", "POWERLIB_EXPORT_END"
    if exported.count(begin) != 1 or exported.count(end) != 1:
        raise RuntimeError("Expected exactly one Lean theorem inventory")
    source = exported.split(begin, 1)[1].split(end, 1)[0]
    counts = re.findall(r"^-- POWERLIB_THEOREM_COUNT (\d+)$", source, re.MULTILINE)
    if len(counts) != 1 or int(counts[0]) == 0:
        raise RuntimeError("Empty or malformed theorem inventory")
    count = int(counts[0])
    roots = [f"AutomationCheck.reuse_{index}" for index in range(count)]
    RESULTS.mkdir(exist_ok=True)
    proof = RESULTS / "AutomaticConsumers.lean"
    proof.write_text(source + audit(roots))
    check_lean(proof)
    print(f"POWERLIB_AUTOMATIC_THEOREMS_OK: {count}")
    return count


if __name__ == "__main__":
    check_automatic()
