"""Retained proof evidence must agree with the actual kernel-check snapshot."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_evidence import check
from common import digest


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.proof = self.root / "Certificate.lean"
        self.proof.write_text("theorem valid : True := True.intro\n")
        self.proof.with_suffix(".log").write_text("POWERLIB_KERNEL_OK\n")
        self.evidence = self.root / "Certificate-evidence"
        self.evidence.mkdir()
        source = self.evidence / "powerlib.lean"
        source.write_text("theorem public : True := True.intro\n")
        self.snapshot = {
            "schema": "powerlib.kernel-check.v1", "build": True,
            "source_snapshot": {"proof_sha256": digest(self.proof),
                                "source_files_sha256": {"powerlib.lean": digest(source)}},
            "compiled_artifacts_sha256": {"powerlib.olean": "compiled-identity"},
            "kernel_log_sha256": digest(self.proof.with_suffix(".log")),
        }
        self.provenance = {
            "proof_sha256": digest(self.proof),
            "kernel_log_sha256": self.snapshot["kernel_log_sha256"],
            "compiled_artifacts_sha256": self.snapshot["compiled_artifacts_sha256"],
            "evidence_directory": self.evidence.name, "conversions": {},
        }
        for family, prefix in [("rl", "bridge"), ("lcl", "lcl-bridge")]:
            conversion = {}
            for suffix, key in [(".json", "report_sha256"), (".log", "agda_log_sha256"),
                                ("-endpoint.lean", "endpoint_sha256"),
                                ("-endpoint.log", "endpoint_log_sha256")]:
                path = self.evidence / (prefix + suffix)
                path.write_text(prefix + suffix)
                conversion[key] = digest(path)
            self.provenance["conversions"][family] = conversion
        self.save_snapshot()

    def save_snapshot(self):
        path = self.proof.with_suffix(".checked.json")
        path.write_text(json.dumps(self.snapshot))
        shutil.copyfile(path, self.evidence / path.name)
        self.provenance["kernel_check_sha256"] = digest(path)
        self.provenance["evidence_files_sha256"] = {
            path.name: digest(path) for path in self.evidence.iterdir()}

    def test_matching_evidence_passes(self):
        check(self.proof, self.provenance)

    def test_current_check_snapshot_cannot_be_swapped(self):
        self.proof.with_suffix(".checked.json").write_text("{}")
        with self.assertRaisesRegex(RuntimeError, "Kernel-check identity changed"):
            check(self.proof, self.provenance)

    def test_report_hashes_do_not_replace_checked_source_identity(self):
        source = self.evidence / "powerlib.lean"
        source.write_text("theorem different : True := True.intro\n")
        self.provenance["evidence_files_sha256"][source.name] = digest(source)
        with self.assertRaisesRegex(RuntimeError, "Checked source identity changed"):
            check(self.proof, self.provenance)

    def test_snapshot_must_refer_to_the_admitted_proof(self):
        self.snapshot["source_snapshot"]["proof_sha256"] = "another-proof"
        self.save_snapshot()
        with self.assertRaisesRegex(RuntimeError, "Kernel-check evidence mismatch"):
            check(self.proof, self.provenance)


if __name__ == "__main__":
    unittest.main()
