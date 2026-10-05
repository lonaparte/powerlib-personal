"""Admission must refer to the exact sources and build actually checked."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common


class CheckSnapshotTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.dependencies = self.root / "dependencies"
        self.dependencies.mkdir()
        self.public = self.root / "powerlib.lean"
        self.public.write_text("theorem original : True := True.intro\n")
        self.proof = self.root / "Certificate.lean"
        self.proof.write_text("import powerlib\n")
        self.compiled = self.root / ".lake/build/lib/lean/powerlib.olean"
        self.compiled.parent.mkdir(parents=True)
        self.compiled.write_bytes(b"compiled-original")
        for name in ["ROOT", "DEPENDENCIES"]:
            replacement = self.root if name == "ROOT" else self.dependencies
            guard = patch.object(common, name, replacement)
            guard.start()
            self.addCleanup(guard.stop)

    def checked(self):
        with patch.object(common, "run", side_effect=[(0, "built"),
                                                     (0, "POWERLIB_KERNEL_OK\n")]):
            common.check_lean(self.proof)
        return self.proof.with_suffix(".checked.json")

    def test_default_build_precedes_kernel_and_records_identity(self):
        with patch.object(common, "run", side_effect=[(0, "built"),
                                                     (0, "POWERLIB_KERNEL_OK\n")]) as run:
            common.check_lean(self.proof)
        self.assertEqual(run.call_args_list[0].args[0], ["lake", "build"])
        self.assertEqual(run.call_args_list[1].args[0], ["lake", "env", "lean", self.proof])
        checked = common._checked_snapshot(self.proof)
        self.assertTrue(checked["build"])
        self.assertEqual(checked["source_snapshot"]["proof_sha256"], common.digest(self.proof))
        self.assertEqual(checked["compiled_artifacts_sha256"][".lake/build/lib/lean/powerlib.olean"],
                         common.digest(self.compiled))

    def test_failed_build_removes_previous_success(self):
        checked = self.checked()
        with patch.object(common, "run", return_value=(1, "invalid public source")) as run:
            with self.assertRaisesRegex(RuntimeError, "library build failed"):
                common.check_lean(self.proof)
        run.assert_called_once_with(["lake", "build"], timeout=1800)
        self.assertFalse(checked.exists())
        with self.assertRaisesRegex(RuntimeError, "Missing or invalid"):
            common.proof_provenance(self.proof)

    def test_source_edit_during_build_prevents_kernel_check(self):
        def build(*args, **kwargs):
            self.public.write_text("theorem edited : True := True.intro\n")
            return 0, "built"
        with patch.object(common, "run", side_effect=build) as run:
            with self.assertRaisesRegex(RuntimeError, "changed during the library build"):
                common.check_lean(self.proof)
        self.assertEqual(run.call_count, 1)
        self.assertFalse(self.proof.with_suffix(".checked.json").exists())

    def test_proof_edit_during_kernel_check_is_rejected(self):
        def check(args, **kwargs):
            if args == ["lake", "build"]:
                return 0, "built"
            self.proof.write_text("theorem different : False := by sorry\n")
            return 0, "POWERLIB_KERNEL_OK\n"
        with patch.object(common, "run", side_effect=check):
            with self.assertRaisesRegex(RuntimeError, "changed during kernel checking"):
                common.check_lean(self.proof)
        self.assertFalse(self.proof.with_suffix(".checked.json").exists())

    def test_failed_kernel_check_removes_previous_success(self):
        checked = self.checked()
        with patch.object(common, "run", side_effect=[(0, "built"), (1, "invalid proof")]):
            with self.assertRaisesRegex(RuntimeError, "Lean rejected"):
                common.check_lean(self.proof)
        self.assertFalse(checked.exists())

    def test_provenance_rejects_sources_changed_after_checking(self):
        self.checked()
        self.public.write_text("theorem current : True := True.intro\n")
        with self.assertRaisesRegex(RuntimeError, "Public source or proof changed"):
            common.proof_provenance(self.proof)

    def test_provenance_rejects_compiled_artifacts_changed_after_checking(self):
        self.checked()
        self.compiled.write_bytes(b"compiled-different")
        with self.assertRaisesRegex(RuntimeError, "Compiled library changed"):
            common.proof_provenance(self.proof)

    def test_provenance_rejects_kernel_log_changed_after_checking(self):
        self.checked()
        self.proof.with_suffix(".log").write_text("different log\n")
        with self.assertRaisesRegex(RuntimeError, "Kernel log changed"):
            common.proof_provenance(self.proof)

    def test_endpoint_opt_out_does_not_claim_a_public_build(self):
        with patch.object(common, "run", return_value=(0, "POWERLIB_KERNEL_OK\n")) as run:
            common.check_lean(self.proof, build=False)
        run.assert_called_once_with(["lake", "env", "lean", self.proof])
        checked = json.loads(self.proof.with_suffix(".checked.json").read_text())
        self.assertFalse(checked["build"])
        with self.assertRaisesRegex(RuntimeError, "completed public-library build"):
            common.proof_provenance(self.proof)


if __name__ == "__main__":
    unittest.main()
