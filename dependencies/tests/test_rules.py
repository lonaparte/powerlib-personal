"""Admission structure and provenance controls; mathematical checks remain in Lean/Agda."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common


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


if __name__ == "__main__":
    unittest.main()
