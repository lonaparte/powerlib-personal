"""Check physical storage synthesis, model binding, and passive semantic admission."""
from fractions import Fraction as F
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, RESULTS, audit
from lcl import Model, lyapunov_product, state_matrix
from passivity import (ADMITTED_THEOREMS, SCHEMA, certificate_report, physical_weights,
                       proof_source, synthesize, synthesize_witness, verify_kernel,
                       verify_saved, verify_witness)
import powerlib


def model(r1=1, r2=0, l1=1, l2=1, c=1):
    return Model(F(l1), F(l2), F(c), F(r1), F(r2))


class StorageSynthesisTests(unittest.TestCase):
    def test_storage_from_original_components_including_lossless(self):
        for m in [model(), model(0, 0), model(0, 3),
                  model(F(1, 7), F(2, 5), F(2, 3), F(3, 2), F(5, 7))]:
            p = synthesize_witness(m)
            self.assertEqual(p, ((m.l1, F(0), F(0)),
                                 (F(0), m.c, F(0)), (F(0), F(0), m.l2)))
            verify_witness(m, p)
            # The actual derived dynamics cancel all conservative cross terms.
            product = lyapunov_product(state_matrix(m), p)
            self.assertEqual(product, ((-2*m.r1, F(0), F(0)),
                                       (F(0), F(0), F(0)), (F(0), F(0), -2*m.r2)))

    def test_negative_resistance_rejected_even_with_positive_total(self):
        for m in [model(-1, 2), model(2, -1), model(-1, -1)]:
            with self.subTest(model=m), self.assertRaises(ValueError):
                synthesize_witness(m)

    def test_forged_physical_weights_rejected(self):
        m = model(0, 0, l1=2, l2=3, c=5)
        good = physical_weights(m)
        for replacement in [physical_weights(model(0, 0)),
                            tuple(tuple(2*x for x in row) for row in good),
                            ((F(2), F(1), F(0)), (F(1), F(5), F(0)),
                             (F(0), F(0), F(3))),
                            ((F(2), F(0), F(0)), (F(0), F(5), F(0)),
                             (F(0), F(0), F(0)))]:
            with self.subTest(p=replacement), self.assertRaises(ValueError):
                verify_witness(m, replacement)

    def test_saved_status_paths_and_metadata_cannot_claim_acceptance(self):
        m = model(0, 0)
        data = certificate_report(m, synthesize_witness(m))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "certificate.json"
            path.write_text(json.dumps(data | {"status": "ACCEPTED", "maturity": "S-level",
                                               "kernel_verified": True, "proof": "/nonexistent",
                                               "proof_sha256": "forged",
                                               "theorems": ["forged.stable"]}))
            checked = verify_saved(m, path)
            self.assertEqual(checked["status"], "UNVERIFIED")
            self.assertFalse(checked["kernel_verified"])
            self.assertNotIn("proof", checked)
            self.assertNotIn("theorems", checked)
            self.assertEqual(checked["P"], data["P"])
            for bad in [{"schema": "powerlib.lcl.lyapunov.v1"},
                        {"goal": "asymptotic"}, {"model": model(2).serialized()},
                        {"state_order": list(reversed(data["state_order"]))},
                        {"P": [["1"]]}, {"P": [["0"]*3 for _ in range(3)]},
                        {"P": [[True]*3 for _ in range(3)]},
                        {"P": [["by sorry"]*3 for _ in range(3)]}]:
                path.write_text(json.dumps(data | bad))
                with self.subTest(bad=bad), self.assertRaises(ValueError):
                    verify_saved(m, path)

    def test_duplicate_certificate_fields_rejected(self):
        m = model(0, 0)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "certificate.json"
            path.write_text('{"schema": "'+SCHEMA+'", "schema": "'+SCHEMA+'"}')
            with self.assertRaises(ValueError):
                verify_saved(m, path)

    def test_unverified_synthesis_retains_exact_original_submission(self):
        m = model(0, 0)
        raw = (json.dumps(m.serialized(), separators=(",", ":")) + "\n\n").encode()
        with tempfile.TemporaryDirectory() as directory:
            report = synthesize(m, directory=directory, submitted_bytes=raw)
            self.assertEqual((Path(directory) / "submitted.json").read_bytes(), raw)
            self.assertEqual(report["status"], "UNVERIFIED")
            self.assertFalse(report["kernel_verified"])
            self.assertNotIn("Admission.globally_asymptotically_stable", ADMITTED_THEOREMS)


class PublicGoalRoutingTests(unittest.TestCase):
    def test_lossless_passive_goal_routes_to_storage_admission(self):
        path = str(ROOT / "dependencies/examples/lcl-lossless.json")
        output = io.StringIO()
        with patch.object(sys, "argv", ["powerlib.py", "atp", path, "--family", "lcl",
                                        "--goal", "passive-stability"]), \
                patch("passivity.atp", return_value={"status": "ACCEPTED"}) as passive, \
                patch("lcl.atp") as strict, redirect_stdout(output):
            self.assertEqual(powerlib.main(), 0)
        passive.assert_called_once_with(path)
        strict.assert_not_called()
        self.assertEqual(json.loads(output.getvalue())["status"], "ACCEPTED")

    def test_default_lcl_goal_retains_strict_semantics(self):
        output = io.StringIO()
        with patch.object(sys, "argv", ["powerlib.py", "atp", "model.json", "--family", "lcl"]), \
                patch("lcl.atp", return_value={"status": "ACCEPTED"}) as strict, \
                patch("passivity.atp") as passive, redirect_stdout(output):
            self.assertEqual(powerlib.main(), 0)
        strict.assert_called_once_with("model.json")
        passive.assert_not_called()

    def test_passive_goal_rejects_unsupported_family(self):
        output = io.StringIO()
        with patch.object(sys, "argv", ["powerlib.py", "atp", "model.json", "--family", "rl",
                                        "--goal", "passive-stability"]), \
                patch("passivity.atp") as passive, redirect_stdout(output):
            self.assertEqual(powerlib.main(), 1)
        passive.assert_not_called()
        self.assertEqual(json.loads(output.getvalue())["status"], "NOT_ACCEPTED")


@unittest.skipUnless(os.environ.get("POWERLIB_LCL_KERNEL_TESTS") == "1",
                     "Set POWERLIB_LCL_KERNEL_TESTS=1 after building the passive storage module")
class KernelTests(unittest.TestCase):
    def setUp(self):
        RESULTS.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="passivity-tests-", dir=RESULTS)
        self.root = Path(self.directory.name)

    def tearDown(self):
        self.directory.cleanup()

    def write_proof(self, m, p=None, **kwargs):
        path = self.root / "Certificate.lean"
        path.write_text(proof_source(m, physical_weights(m) if p is None else p, **kwargs))
        return path

    def assert_real_rejection(self, proof):
        with self.assertRaises(RuntimeError):
            verify_kernel(proof)
        log = proof.with_suffix(".log").read_text()
        self.assertNotIn("unknown module", log)
        self.assertNotIn("object file", log)
        return log

    def test_physical_storage_semantics_including_lossless(self):
        for m in [model(0, 0), model(), model(0, 1),
                  model(F(1, 7), 0, F(2, 3), F(3, 2), F(5, 7))]:
            with self.subTest(model=m):
                verify_kernel(self.write_proof(m))

    def test_lossless_stability_does_not_imply_asymptotic_stability(self):
        proof = self.write_proof(model(0, 0))
        proof.write_text(proof.read_text() + '''
@[powerlib_domain] theorem lossless_not_asymptotic :
    ¬ powerlib.LCL.AsymptoticallyStable Admission.submittedModel 0 0 0 := by
  apply powerlib.LCL.lossless_not_asymptoticallyStable (by norm_num [Admission.submittedModel])
    (by norm_num [Admission.submittedModel]) (powerlib.LCL.zero_equilibrium _)
''' + audit(["lossless_not_asymptotic"]))
        verify_kernel(proof)
        # A request for strict convergence must actually fail on this accepted passive model.
        proof.write_text(proof.read_text() + '''
theorem false_asymptotic_claim :
    powerlib.LCL.AsymptoticallyStable Admission.submittedModel 0 0 0 := by
  exact Admission.zero_input_stable
''')
        self.assertIn("type mismatch", self.assert_real_rejection(proof))

    def test_wrong_matrix_and_negative_resistance_fail_in_kernel(self):
        m = model(0, 0, l1=2)
        self.assertIn("unsolved goals", self.assert_real_rejection(
            self.write_proof(m, physical_weights(model(0, 0)))))
        for m in [model(-1, 2), model(2, -1)]:
            with self.subTest(model=m):
                self.assertIn("unsolved goals", self.assert_real_rejection(self.write_proof(m)))

    def test_valid_certificate_for_other_model_is_a_type_mismatch(self):
        # The same physical P is valid for both resistance choices, but the old proof
        # still cannot replace a fresh proof about the original submitted model.
        self.assertIn("type mismatch", self.assert_real_rejection(
            self.write_proof(model(0, 0), candidate_model=model(2, 0))))

    def test_sorry_and_custom_axiom_are_rejected(self):
        proof = self.write_proof(model(0, 0))
        proof.write_text(proof.read_text().replace("by norm_num", "by sorry"))
        self.assertIn("sorryAx", self.assert_real_rejection(proof))
        proof = self.write_proof(model(0, 0))
        source = proof.read_text().replace("namespace Candidate", "axiom forbidden : False\nnamespace Candidate")
        proof.write_text(source.replace("by norm_num", "by exact False.elim forbidden"))
        self.assertIn("Unexpected axiom forbidden", self.assert_real_rejection(proof))

    def test_forged_marker_without_required_roots_is_rejected(self):
        proof = self.root / "Certificate.lean"
        proof.write_text('''import powerlib
theorem forged : False := by sorry
run_cmd Lean.logInfo "POWERLIB_KERNEL_OK"
''')
        self.assertIn("Missing required admission declaration Admission.accepted",
                      self.assert_real_rejection(proof))

    def test_checker_audits_sorry_and_custom_axiom_despite_forged_marker(self):
        proof = self.write_proof(model(0, 0))
        # Omit the source's audit entirely: only the independent checker audit
        # can reject these proofs, even though their source logs a fake success.
        source = proof.read_text().split("\nopen Lean Elab Command\n", 1)[0]
        marker = '\nrun_cmd Lean.logInfo "POWERLIB_KERNEL_OK"\n'
        proof.write_text(source.replace("by norm_num", "by sorry") + marker)
        self.assertIn("sorryAx", self.assert_real_rejection(proof))
        source = source.replace("namespace Candidate", "axiom forgedAxiom : False\nnamespace Candidate")
        proof.write_text(source.replace("by norm_num", "by exact False.elim forgedAxiom") + marker)
        self.assertIn("Unexpected axiom forgedAxiom", self.assert_real_rejection(proof))

    def test_checker_requires_each_semantic_root_and_preserves_source(self):
        proof = self.write_proof(model(0, 0))
        original = proof.read_bytes()
        verify_kernel(proof)
        self.assertEqual(proof.read_bytes(), original)
        verify_kernel(proof)
        self.assertEqual(proof.read_bytes(), original)
        source = proof.read_text().split("\nopen Lean Elab Command\n", 1)[0]
        source = source.replace('''@[powerlib_domain] theorem zero_input_stable :
    powerlib.LCL.LyapunovStable submittedModel 0 0 0 := accepted.zeroInput_stable
''', "")
        proof.write_text(source + '\nrun_cmd Lean.logInfo "POWERLIB_KERNEL_OK"\n')
        self.assertIn("Missing required admission declaration Admission.zero_input_stable",
                      self.assert_real_rejection(proof))

    def test_saved_forged_success_path_gets_fresh_kernel_verification(self):
        m = model(0, 0)
        certificate = self.root / "input-certificate.json"
        data = certificate_report(m, synthesize_witness(m))
        certificate.write_text(json.dumps(data | {"status": "ACCEPTED", "proof": "/nonexistent",
                                                  "proof_sha256": "forged", "kernel_verified": True}))
        report = verify_saved(m, certificate, kernel=True)
        self.assertEqual(report["status"], "ACCEPTED")
        self.assertEqual(report["maturity"], "Certificate verification")
        self.assertNotEqual(report["proof"], "/nonexistent")
        self.assertTrue(Path(report["proof"]).is_file())
        evidence = Path(report["proof"]).parent / report["provenance"]["evidence_directory"]
        self.assertEqual((evidence / "submitted.json").read_bytes(),
                         Path(report["proof"]).with_name("submitted.json").read_bytes())
        self.assertEqual(report["submitted_model_sha256"],
                         report["provenance"]["evidence_files_sha256"]["submitted.json"])


if __name__ == "__main__":
    unittest.main()
