"""Check the LCL derivation, exact synthesis, and rejection of false witnesses."""
from fractions import Fraction as F
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, CACHE, RESULTS, audit, check_lean, run
from lcl_bridge import render
from lcl import (Model, certificate_fraction, certificate_report, coefficients,
                 determinant, derive, hurwitz_checks, model_from_data, model_source, proof_source,
                 state_matrix, synthesize_witness, verify_kernel, verify_saved,
                 verify_witness)


def model(r1=1, r2=0, l1=1, l2=1, c=1):
    return Model(F(l1), F(l2), F(c), F(r1), F(r2))


class DerivationTests(unittest.TestCase):
    def test_characteristic_polynomial_against_determinant(self):
        for m in [model(), model(r1=0, r2=0), model(r1=-1, r2=2),
                  model(F(1, 4), F(1, 7), F(2, 3), F(3, 2), F(5, 7))]:
            a = state_matrix(m)
            a3, a2, a1, a0 = coefficients(m)
            # Four distinct points determine a cubic; use one additional point.
            for s in map(F, [-2, -1, 0, 1, 3]):
                si_minus_a = tuple(tuple(s*int(i == j)-a[i][j] for j in range(3))
                                   for i in range(3))
                self.assertEqual(a3*determinant(si_minus_a), a3*s**3+a2*s**2+a1*s+a0)

    def test_passive_simplification_and_lossless_boundary(self):
        for l1, l2, c in [(1, 1, 1), (F(2, 3), F(3, 2), F(7, 5))]:
            for r1 in [0, F(1, 3), 2]:
                for r2 in [0, F(1, 3), 2]:
                    result = derive(model(r1, r2, l1, l2, c))
                    self.assertEqual(result["hurwitz_by_derived_criterion"], r1 != 0 or r2 != 0)
                    self.assertEqual(result["passive_resistances_not_both_zero"], r1 != 0 or r2 != 0)
        self.assertEqual(coefficients(model(0, 0)), (F(1), F(0), F(2), F(0)))
        with self.assertRaises(ValueError):
            synthesize_witness(model(0, 0))

    def test_positive_total_is_insufficient_for_signed_resistances(self):
        m = model(-1, 2)
        self.assertGreater(m.r1+m.r2, 0)
        self.assertFalse(all(hurwitz_checks(m).values()))
        self.assertIsNone(derive(m)["passive_resistances_not_both_zero"])
        with self.assertRaises(ValueError):
            synthesize_witness(m)

    def test_bad_model_inputs(self):
        valid = model().serialized()
        for key in ["inductance1", "inductance2", "capacitance"]:
            for value in ["0", "-1", True, 1.5, "by sorry"]:
                with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                    model_from_data(valid | {key: value})
        for data in [[], valid | {"extra": "1"}, {"inductance1": "1"}]:
            with self.assertRaises(ValueError):
                model_from_data(data)
        with self.assertRaises(ValueError):
            Model(1, F(1), F(1), F(1), F(0))

    def test_wire_decoder_rejects_malformed_or_ill_typed_data(self):
        valid = json.loads((ROOT / "dependencies/lcl_wire.json").read_text())
        render(valid, "test", "test")
        for bad in [valid[:-1], valid+[0], [20261004, 2], [20261004, 1, 99],
                    [20261004, 1, 0, 5], [20261004, 1, 0, 2],
                    [20261004, 1, True], [20261004, 1, -1]]:
            with self.subTest(wire=bad), self.assertRaises(ValueError):
                render(bad, "test", "test")


class SynthesisTests(unittest.TestCase):
    def test_one_sided_and_mixed_sign_certificates(self):
        for m in [model(), model(0, 1), model(1, 2), model(F(-1, 2), 1),
                  model(F(1, 4), 0, F(2, 3), F(3, 2), F(5, 7))]:
            verify_witness(m, synthesize_witness(m))

    def test_expected_cross_terms(self):
        self.assertEqual(synthesize_witness(model()),
                         ((F(3, 2), F(1), F(-1, 2)),
                          (F(1), F(3), F(1, 2)),
                          (F(-1, 2), F(1, 2), F(5, 2))))
        with self.assertRaises(ValueError):
            verify_witness(model(), ((F(1, 2), F(0), F(0)),
                                     (F(0), F(1, 2), F(0)), (F(0), F(0), F(1, 2))))

    def test_wrong_witness_and_different_model(self):
        m = model()
        p = synthesize_witness(m)
        with self.assertRaises(ValueError):
            verify_witness(model(2, 0), p)
        for factor in [-1, 2]:
            with self.assertRaises(ValueError):
                verify_witness(m, tuple(tuple(factor*x for x in row) for row in p))
        bad = [list(row) for row in p]
        bad[1][0] += 1
        with self.assertRaises(ValueError):
            verify_witness(m, bad)

    def test_saved_certificate_is_rechecked(self):
        m = model()
        data = certificate_report(m, synthesize_witness(m))
        with tempfile.TemporaryDirectory() as directory, patch("lcl.RESULTS", Path(directory)):
            path = Path(directory) / "certificate.json"
            submission = Path(directory) / "model.json"
            submission.write_text(json.dumps(m.serialized()))
            forged = data | {"status": "ACCEPTED", "kernel_verified": True,
                             "proof": "untrusted-path", "leading_minors": ["1", "1", "1"]}
            path.write_text(json.dumps(forged))
            checked = verify_saved(submission, path)
            self.assertEqual(checked["status"], "UNVERIFIED")
            self.assertFalse(checked["kernel_verified"])
            self.assertEqual(checked["leading_minors"], ["3/2", "7/2", "57/8"])
            for replacement in [{"model": model(2, 0).serialized()},
                                {"state_order": ["grid_current", "capacitor_voltage", "converter_current"]},
                                {"Q": [["0"]*3 for _ in range(3)]},
                                {"P": [["1"]]},
                                {"P": [["0"]*3 for _ in range(3)]}]:
                path.write_text(json.dumps(data | replacement))
                with self.assertRaises(ValueError):
                    verify_saved(submission, path)

    def test_witness_entries_can_exceed_model_input_length(self):
        value = F(10**120+1, 10**121+3)
        self.assertEqual(certificate_fraction(str(value)), value)
        for value in [True, 0.5, "1/0", "by sorry"]:
            with self.assertRaises(ValueError):
                certificate_fraction(value)


@unittest.skipUnless(os.environ.get("POWERLIB_LCL_KERNEL_TESTS") == "1",
                     "Set POWERLIB_LCL_KERNEL_TESTS=1 after building the LCL certificate module")
class KernelTests(unittest.TestCase):
    def setUp(self):
        RESULTS.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="lcl-tests-", dir=RESULTS)
        self.root = Path(self.directory.name)

    def tearDown(self):
        self.directory.cleanup()

    def write_proof(self, m, p):
        path = self.root / "Certificate.lean"
        path.write_text(proof_source(m, p))
        return path

    def test_generated_proofs(self):
        for m in [model(), model(0, 1), model(F(-1, 2), 1),
                  model(F(1, 4), 0, F(2, 3), F(3, 2), F(5, 7))]:
            verify_kernel(self.write_proof(m, synthesize_witness(m)))

    def test_false_matrix_and_model_fail_in_kernel(self):
        p = synthesize_witness(model())
        for m, proposed in [(model(2, 0), p), (model(), tuple(tuple(2*x for x in row) for row in p))]:
            with self.assertRaises(RuntimeError):
                verify_kernel(self.write_proof(m, proposed))
            log = (self.root / "Certificate.log").read_text()
            self.assertNotIn("unknown module", log)
            self.assertNotIn("object file", log)

    def test_sorry_cannot_pass_audit(self):
        proof = self.write_proof(model(), synthesize_witness(model()))
        proof.write_text(proof.read_text().replace("by norm_num", "by sorry"))
        with self.assertRaises(RuntimeError):
            verify_kernel(proof)
        self.assertIn("sorryAx", proof.with_suffix(".log").read_text())

    def test_custom_axiom_cannot_pass_audit(self):
        proof = self.write_proof(model(), synthesize_witness(model()))
        source = proof.read_text().replace("namespace Candidate", "axiom forbidden : False\nnamespace Candidate")
        proof.write_text(source.replace("by norm_num", "by exact False.elim forbidden"))
        with self.assertRaises(RuntimeError):
            verify_kernel(proof)
        self.assertIn("Unexpected axiom forbidden", proof.with_suffix(".log").read_text())

    def test_different_candidate_model_is_a_type_mismatch(self):
        other = model(2, 0)
        proof = self.write_proof(other, synthesize_witness(other))
        proof.write_text(proof.read_text().replace(model_source("submittedModel", other),
                                                  model_source("submittedModel", model())))
        with self.assertRaises(RuntimeError):
            verify_kernel(proof)
        self.assertIn("type mismatch", proof.with_suffix(".log").read_text())

    def test_wrong_wire_fails_lean_endpoint(self):
        # A typed projection swap must still fail the independent endpoint contract.
        words = json.loads((ROOT / "dependencies/lcl_wire.json").read_text())
        words[4] = 1
        proof = self.root / "WrongConversion.lean"
        proof.write_text("import Lean\n"+render(words, "test", "test")+
                         audit(["powerlib.generated.convertLCL_spec"], include_core=False))
        with self.assertRaises(RuntimeError):
            check_lean(proof)
        self.assertIn("rfl", proof.with_suffix(".log").read_text())

    def test_wrong_agda_conversion_fails_roundtrip(self):
        stage = self.root / "negative-agda"
        (stage / "theorems").mkdir(parents=True)
        for name in ["Conversion.agda", "LCLConversion.agda"]:
            source = (ROOT / "theorems" / name).read_text()
            if name == "LCLConversion.agda":
                source = source.replace("RL.run scale reciprocal (fst (fst x))", "fst (fst x)")
            (stage / "theorems" / name).write_text(source)
        (stage / "powerlib.agda-lib").write_text((ROOT / "powerlib.agda-lib").read_text())
        libraries = stage / "libraries"
        libraries.write_text(str(CACHE / "cubical/cubical.agda-lib")+"\n")
        code, log = run([CACHE / "agda", f"--library-file={libraries}",
                         "--no-default-libraries", stage / "theorems/LCLConversion.agda"], cwd=stage)
        self.assertNotEqual(code, 0, log)
        self.assertIn("recover", log)
        self.assertNotIn("Failed to find source", log)


if __name__ == "__main__":
    unittest.main()
