#!/usr/bin/env python3
"""Check retained artifact identities after all ATP/ATD commands have run."""
import json
from pathlib import Path
from common import RESULTS, digest

EXPECTED_CANDIDATES = {
    "rl": {"positive": "PROVED", "nonnegative": "REFUTED", "negative": "REFUTED"},
    "lcl": {"not_both_zero": "PROVED", "both_positive": "REFUTED", "nonnegative_sum": "REFUTED"},
}


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
    for family, prefix in [("rl", "bridge"), ("lcl", "lcl-bridge")]:
        conversion = provenance["conversions"][family]
        for suffix, key in [(".json", "report_sha256"), (".log", "agda_log_sha256"),
                            ("-endpoint.lean", "endpoint_sha256"),
                            ("-endpoint.log", "endpoint_log_sha256")]:
            if digest(evidence / (prefix + suffix)) != conversion[key]:
                raise RuntimeError(f"Conversion evidence identity changed: {family}/{key}")


def check_all(directory=RESULTS):
    syntheses = set()
    candidates = {family: set() for family in EXPECTED_CANDIDATES}
    for path in directory.rglob("*.json"):
        if path.name not in {"report.json", "certificate.json"}:
            continue
        data = json.loads(path.read_text())
        family, kind = data.get("family"), data.get("artifact_type")
        if data.get("status") == "ACCEPTED":
            if family not in EXPECTED_CANDIDATES or kind not in {"synthesis", "certificate_verification"}:
                raise RuntimeError(f"Missing or invalid admission classification: {path}")
            check(path.parent / Path(data["proof"]).name, data["provenance"])
            if digest(path.parent / "submitted.json") != data["submitted_model_sha256"]:
                raise RuntimeError("Submitted input identity changed")
            expected_maturity = "S-level" if kind == "synthesis" else "Certificate verification"
            if data.get("maturity") != expected_maturity:
                raise RuntimeError(f"Admission maturity does not match its kind: {path}")
            if kind == "synthesis":
                syntheses.add(family)
        if "results" in data or kind == "fixed_candidates":
            if family not in EXPECTED_CANDIDATES or kind != "fixed_candidates":
                raise RuntimeError(f"Missing or invalid fixed-candidate classification: {path}")
            for result in data["results"]:
                candidate = result.get("candidate_id")
                expected = EXPECTED_CANDIDATES[family].get(candidate)
                if expected is None or result.get("status") != expected:
                    raise RuntimeError(f"Unexpected fixed-candidate result: {family}/{candidate}")
                check(path.parent / Path(result["proof"]).name, result["provenance"])
                candidates[family].add(candidate)
    for family, expected in EXPECTED_CANDIDATES.items():
        if family not in syntheses:
            raise RuntimeError(f"Missing accepted synthesis: {family}")
        missing = expected.keys() - candidates[family]
        if missing:
            raise RuntimeError(f"Missing fixed candidates for {family}: {', '.join(sorted(missing))}")


def main():
    check_all()
    print("POWERLIB_RETAINED_EVIDENCE_OK: rl/lcl synthesis, 6 distinct fixed candidates")


if __name__ == "__main__":
    main()
