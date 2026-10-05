#!/usr/bin/env python3
"""Check retained artifact identities after all ATP/ATD commands have run."""
import json
from pathlib import Path
from common import RESULTS, digest


def check(proof, provenance):
    if digest(proof) != provenance["proof_sha256"]:
        raise RuntimeError(f"Proof identity changed: {proof}")
    if digest(proof.with_suffix(".log")) != provenance["kernel_log_sha256"]:
        raise RuntimeError(f"Kernel log identity changed: {proof}")
    evidence = proof.parent / provenance["evidence_directory"]
    for name, expected in provenance["evidence_files_sha256"].items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts or digest(evidence / relative) != expected:
            raise RuntimeError(f"Retained evidence identity changed: {name}")
    if "kernel_checked_source" in provenance:
        source = Path(provenance["kernel_checked_source"])
        if (source.is_absolute() or ".." in source.parts or
                digest(evidence / source) != provenance["kernel_checked_source_sha256"]):
            raise RuntimeError("Independently audited kernel source identity changed")
    for family, prefix in [("rl", "bridge"), ("lcl", "lcl-bridge")]:
        conversion = provenance["conversions"][family]
        for suffix, key in [(".json", "report_sha256"), (".log", "agda_log_sha256"),
                            ("-endpoint.lean", "endpoint_sha256"),
                            ("-endpoint.log", "endpoint_log_sha256")]:
            if digest(evidence / (prefix + suffix)) != conversion[key]:
                raise RuntimeError(f"Conversion evidence identity changed: {family}/{key}")


def main():
    accepted = candidates = passive_admissions = 0
    for path in RESULTS.rglob("*.json"):
        if path.name not in {"report.json", "certificate.json"}:
            continue
        data = json.loads(path.read_text())
        if data.get("status") == "ACCEPTED":
            check(path.parent / Path(data["proof"]).name, data["provenance"])
            if digest(path.parent / "submitted.json") != data["submitted_model_sha256"]:
                raise RuntimeError("Submitted input identity changed")
            accepted += 1
            if data.get("goal") == "passive-stability" and data.get("maturity") == "S-level":
                passive_admissions += 1
        for result in data.get("results", []):
            if result["status"] in {"PROVED", "REFUTED"}:
                check(path.parent / Path(result["proof"]).name, result["provenance"])
                candidates += 1
    if accepted < 3 or candidates < 6 or passive_admissions < 1:
        raise RuntimeError("RL, strict LCL, passive LCL ATP and both fixed-candidate artifacts are required")
    print(f"POWERLIB_RETAINED_EVIDENCE_OK: {accepted} admissions, "
          f"{passive_admissions} passive admissions, {candidates} candidates")


if __name__ == "__main__":
    main()
