"""Admission structure and provenance controls; mathematical checks remain in Lean/Agda."""
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common
from check_evidence import EXPECTED_CANDIDATES, check_all


class RuleTests(unittest.TestCase):
    def test_formalization_has_no_markdown(self):
        notes = [str(p.relative_to(common.ROOT)) for p in (common.ROOT / "theorems").rglob("*")
                 if p.is_file() and p.suffix.lower() in {".md", ".markdown"}]
        self.assertEqual(notes, [])

    def test_stale_conversion_evidence_is_rejected(self):
        # Exercise the actual checked reports retained by the two bridges.
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            for prefix in ["bridge", "lcl-bridge"]:
                for suffix in [".json", ".log", "-endpoint.lean", "-endpoint.log"]:
                    shutil.copy(common.RESULTS / (prefix + suffix), stage)
            with patch.object(common, "RESULTS", stage):
                self.assertEqual(set(common.conversion_provenance()), {"rl", "lcl"})
                for prefix in ["bridge", "lcl-bridge"]:
                    report = stage / (prefix + ".json")
                    original = report.read_text()
                    for key, value in [("agda_source_sha256", "0" * 64),
                                       ("wire", [0]), ("endpoint_log_sha256", "0" * 64)]:
                        data = json.loads(original)
                        data[key] = value
                        report.write_text(json.dumps(data))
                        with self.assertRaises(RuntimeError):
                            common.conversion_provenance()
                    report.write_text(original)


@unittest.skipUnless(os.environ.get("POWERLIB_RETAINED_TESTS") == "1",
                     "Run after both ATP and fixed-candidate commands")
class RetainedEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Reuse actual kernel-checked artifacts, never fabricated proof/log fixtures.
        cls.records = {}
        for path in common.RESULTS.rglob("*.json"):
            if path.name not in {"report.json", "certificate.json"}:
                continue
            data = json.loads(path.read_text())
            if data.get("artifact_type") == "fixed_candidates" or data.get("status") == "ACCEPTED":
                cls.records.setdefault((data["family"], data["artifact_type"]), path)
        for family in EXPECTED_CANDIDATES:
            for kind in ["synthesis", "fixed_candidates"]:
                if (family, kind) not in cls.records:
                    raise RuntimeError(f"Missing kernel-checked fixture: {family}/{kind}")
        cls.temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temporary.cleanup)
        source = Path(cls.temporary.name) / "model.json"
        model = json.loads((common.DEPENDENCIES / "examples/lcl.json").read_text())
        cls.synthesis_input = ("\n" + json.dumps(model, indent=3) + "\n\n").encode()
        source.write_bytes(cls.synthesis_input)
        cls.synthesis = json.loads(common.demand(
            [sys.executable, common.DEPENDENCIES / "lcl.py", "synthesize", source, "--verify"]))
        certificate = Path(cls.synthesis["proof"]).with_name("certificate.json")
        # Same physical model, different original bytes: verification must retain
        # this submission, not the earlier synthesizer's input or normalized model.
        cls.verification_input = (json.dumps(model, sort_keys=True) + "\n").encode()
        source.write_bytes(cls.verification_input)
        cls.verification = json.loads(common.demand(
            [sys.executable, common.DEPENDENCIES / "lcl.py", "verify", source, certificate, "--verify"]))

    def copy_record(self, path, stage, name):
        target = stage / name
        shutil.copytree(path.parent, target)
        return target / path.name

    def copy_complete(self, stage):
        return {key: self.copy_record(self.records[key], stage, "-".join(key))
                for key in [(family, kind) for family in EXPECTED_CANDIDATES
                            for kind in ["synthesis", "fixed_candidates"]]}

    def test_complete_and_direct_lcl_records(self):
        for report, raw, kind, maturity in [
            (self.synthesis, self.synthesis_input, "synthesis", "S-level"),
            (self.verification, self.verification_input, "certificate_verification", "Certificate verification"),
        ]:
            with self.subTest(kind=kind):
                directory = Path(report["proof"]).parent
                self.assertEqual(report["status"], "ACCEPTED")
                self.assertEqual(report["family"], "lcl")
                self.assertEqual(report["artifact_type"], kind)
                self.assertEqual(report["maturity"], maturity)
                self.assertEqual((directory / "submitted.json").read_bytes(), raw)
                self.assertEqual(report["submitted_model_sha256"], common.digest(directory / "submitted.json"))
                self.assertEqual(json.loads((directory / "certificate.json").read_text()), report)
        check_all(common.RESULTS)
        # Verification records are checked for integrity even though they cannot
        # contribute synthesis coverage.
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            self.copy_complete(stage)
            copied = self.copy_record(Path(self.verification["proof"]).with_name("certificate.json"),
                                      stage, "verification")
            copied.with_name("submitted.json").write_text("{}")
            with self.assertRaisesRegex(RuntimeError, "Submitted input identity changed"):
                check_all(stage)

    def test_missing_family_cannot_be_hidden_by_duplicates(self):
        for missing in EXPECTED_CANDIDATES:
            with self.subTest(family=missing), tempfile.TemporaryDirectory() as directory:
                stage = Path(directory)
                other = "lcl" if missing == "rl" else "rl"
                for kind in ["synthesis", "fixed_candidates"]:
                    for duplicate in range(2):
                        self.copy_record(self.records[other, kind], stage, f"{kind}-{duplicate}")
                with self.assertRaisesRegex(RuntimeError, f"Missing accepted synthesis: {missing}"):
                    check_all(stage)
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            for key in [("rl", "synthesis"), ("rl", "fixed_candidates"), ("lcl", "fixed_candidates")]:
                self.copy_record(self.records[key], stage, "-".join(key))
            self.copy_record(Path(self.verification["proof"]).with_name("certificate.json"), stage, "verification")
            with self.assertRaisesRegex(RuntimeError, "Missing accepted synthesis: lcl"):
                check_all(stage)

    def test_missing_or_wrong_candidate_is_rejected(self):
        for family, expected in EXPECTED_CANDIDATES.items():
            for candidate in expected:
                with self.subTest(family=family, candidate=candidate), tempfile.TemporaryDirectory() as directory:
                    stage = Path(directory)
                    paths = self.copy_complete(stage)
                    path = paths[family, "fixed_candidates"]
                    report = json.loads(path.read_text())
                    remaining = [r for r in report["results"] if r["candidate_id"] != candidate]
                    report["results"] = remaining + [remaining[0]]  # Still six total results.
                    path.write_text(json.dumps(report))
                    with self.assertRaisesRegex(RuntimeError, f"Missing fixed candidates for {family}: {candidate}"):
                        check_all(stage)
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            path = self.copy_complete(stage)["rl", "fixed_candidates"]
            report = json.loads(path.read_text())
            report["results"][0]["status"] = "REFUTED"
            path.write_text(json.dumps(report))
            with self.assertRaisesRegex(RuntimeError, "Unexpected fixed-candidate result: rl/positive"):
                check_all(stage)


if __name__ == "__main__":
    unittest.main()
