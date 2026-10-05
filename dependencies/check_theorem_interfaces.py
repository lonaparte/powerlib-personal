#!/usr/bin/env python3
"""Check public theorem metadata and representative native theorem consumers."""
from common import DEPENDENCIES, RESULTS, demand, run


def check_theorem_interfaces():
    demand(["lake", "build", "TheoremInspection"])
    checks = [
        ("PublicTheoremRegistry", "POWERLIB_PUBLIC_THEOREM_REGISTRY_OK"),
        ("NativeTheoremUse", "POWERLIB_NATIVE_THEOREM_USE_OK"),
        ("StateSpacePassivityCases", "POWERLIB_STATE_SPACE_PASSIVITY_CASES_OK"),
        ("Upstream", "POWERLIB_UPSTREAM_REUSE_OK"),
    ]
    RESULTS.mkdir(parents=True, exist_ok=True)
    for name, marker in checks:
        print(f"Checking {name} in an independent Lean process", flush=True)
        source = (DEPENDENCIES / "tests" / (name + ".lean")).read_bytes()
        retained = RESULTS / (name + ".lean")
        retained.write_bytes(source)
        code, log = run(["lake", "env", "lean", retained])
        retained.with_suffix(".log").write_text(log)
        if code:
            raise RuntimeError(f"Lean rejected {name}; see {retained.with_suffix('.log')}\n{log}")
        if log.count(marker) != 1:
            raise RuntimeError(f"Missing {name} kernel-check evidence")
        print(marker, flush=True)
    print("POWERLIB_THEOREM_INTERFACES_OK", flush=True)
    return len(checks)


if __name__ == "__main__":
    check_theorem_interfaces()
