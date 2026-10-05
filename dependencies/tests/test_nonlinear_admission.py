"""Failure paths must never turn a proposal into an accepted proof report."""
from contextlib import redirect_stdout
from dataclasses import replace
from fractions import Fraction
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import nonlinear
import powerlib
from nonlinear_synthesis import Term, WeightedSquare, model_from_data, synthesize


def term(coefficient, a, b):
    return {"coefficient": str(coefficient), "powers": [a, b]}


def model_data(*, unstable=False):
    return {"schema": "powerlib.polynomial2.v1", "field": [
        [term(-1, 1, 0), term(1 if unstable else -1, 3, 0)],
        [term(-1, 0, 1), term(-1, 0, 3)],
    ]}


class AdmissionFailureTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.results = self.root / "results"
        self.model = self.root / "model.json"
        guard = patch.object(nonlinear, "RESULTS", self.results)
        guard.start()
        self.addCleanup(guard.stop)

    def write_model(self, *, unstable=False):
        self.model.write_text(json.dumps(model_data(unstable=unstable)))
        return self.model

    def assert_no_acceptance_report(self):
        self.assertEqual(list(self.results.rglob("report.json")), [])

    def candidate_fixture(self):
        model = model_from_data(model_data())
        result = synthesize(model)
        self.assertIsNotNone(result.witness)
        return model, result.witness

    def test_unproved_search_never_calls_admission(self):
        with patch.object(nonlinear, "check_conversions") as conversions, \
                patch.object(nonlinear, "check_lean") as kernel, \
                patch.object(nonlinear, "proof_provenance") as provenance:
            report = nonlinear.atp(self.write_model(unstable=True))
        for operation in (conversions, kernel, provenance):
            operation.assert_not_called()
        self.assertEqual(report["status"], "UNPROVED")
        self.assertIs(report["kernel_verified"], False)
        for claimed_result in ("proof", "theorems", "semantic_theorems", "provenance"):
            self.assertNotIn(claimed_result, report)
        self.assertEqual(list(self.results.rglob("Certificate.lean")), [])

    def test_kernel_rejection_cannot_write_accepted_report(self):
        # Use the actual synthesizer; only the external admission call is forced to fail.
        with patch.object(nonlinear, "check_conversions"), \
                patch.object(nonlinear, "check_lean", side_effect=RuntimeError("kernel rejected")) \
                as kernel, patch.object(nonlinear, "proof_provenance") as provenance:
            with self.assertRaisesRegex(RuntimeError, "kernel rejected"):
                nonlinear.atp(self.write_model())
        kernel.assert_called_once()
        provenance.assert_not_called()
        self.assert_no_acceptance_report()

    def test_submission_change_during_check_is_rejected(self):
        def alter_submission(proof):
            Path(proof).with_name("submitted.json").write_text(
                json.dumps(model_data(unstable=True)))

        # These mocks exercise the rejection guard only; they establish no kernel success.
        with patch.object(nonlinear, "check_conversions"), \
                patch.object(nonlinear, "check_lean", side_effect=alter_submission) as kernel, \
                patch.object(nonlinear, "proof_provenance", return_value={}):
            with self.assertRaisesRegex(RuntimeError, "Original polynomial submission changed"):
                nonlinear.atp(self.write_model())
        kernel.assert_called_once()
        self.assert_no_acceptance_report()

    def test_real_unproved_cli_result_has_nonzero_exit_status(self):
        output = io.StringIO()
        argv = ["powerlib.py", "atp", str(self.write_model(unstable=True)),
                "--family", "nonlinear"]
        with patch.object(sys, "argv", argv), redirect_stdout(output), \
                patch.object(nonlinear, "check_conversions") as conversions, \
                patch.object(nonlinear, "check_lean") as kernel, \
                patch.object(nonlinear, "proof_provenance") as provenance:
            exit_status = powerlib.main()
        self.assertEqual(exit_status, 1)
        report = json.loads(output.getvalue())
        self.assertEqual(report["status"], "UNPROVED")
        self.assertIs(report["kernel_verified"], False)
        self.assertNotIn("proof", report)
        for operation in (conversions, kernel, provenance):
            operation.assert_not_called()

    def test_scalar_object_cannot_inject_lean_commands(self):
        class SourcePayload:
            numerator = "0 : ℚ)\n#exit\n--"
            denominator = 1

        model, witness = self.candidate_fixture()
        for value in (SourcePayload(), "1", True, 0.5):
            with self.subTest(value_type=type(value).__name__):
                with self.assertRaises(ValueError):
                    nonlinear.candidate_source(model, replace(witness, p00=value))

    def test_corrupted_monomial_powers_are_rejected_before_serialization(self):
        model, witness = self.candidate_fixture()
        for powers in (("0\n#exit", 1), (True, 0), (-1, 0), (1024, 0)):
            with self.subTest(powers=powers):
                factor = Term(Fraction(1), (1, 0))
                object.__setattr__(factor, "powers", powers)
                square = WeightedSquare(Fraction(1), (factor,))
                proposed = replace(witness, decay_sos=(square,))
                with self.assertRaises(ValueError):
                    nonlinear.candidate_source(model, proposed)

    def test_sos_weight_requires_an_exact_numeric_value(self):
        model, witness = self.candidate_fixture()
        for weight in (object(), "1", True, 0.5):
            with self.subTest(weight_type=type(weight).__name__):
                square = WeightedSquare(weight, (Term(Fraction(1), (1, 0)),))
                with self.assertRaises(ValueError):
                    nonlinear.candidate_source(model, replace(witness, decay_sos=(square,)))

    def test_original_json_validation_does_not_trust_the_model_object(self):
        model, _ = self.candidate_fixture()
        malformed_powers = model_data()
        malformed_powers["field"][0][0]["powers"] = ["0\n#exit", 0]
        floating_coefficient = model_data()
        floating_coefficient["field"][0][0]["coefficient"] = 0.5
        for label, data in (("powers", malformed_powers), ("coefficient", floating_coefficient)):
            with self.subTest(label=label):
                self.model.write_text(json.dumps(data))
                with self.assertRaises(ValueError):
                    nonlinear.admission_source(model, original_path=self.model)

    def test_original_json_duplicate_key_is_rejected(self):
        model, _ = self.candidate_fixture()
        data = json.dumps(model_data()).replace(
            '"schema":', '"schema": "powerlib.polynomial2.v1", "schema":', 1)
        self.model.write_text(data)
        with self.assertRaisesRegex(ValueError, "Duplicate submitted JSON key"):
            nonlinear.admission_source(model, original_path=self.model)

    def test_corrupted_fraction_slots_cannot_escape_the_numeric_boundary(self):
        model, witness = self.candidate_fixture()
        for slot, value in (("_numerator", "0 : ℚ)\n#exit\n--"),
                            ("_denominator", "1\n#exit"), ("_denominator", 0)):
            with self.subTest(slot=slot, value=value):
                number = Fraction(1)
                object.__setattr__(number, slot, value)
                with self.assertRaises(ValueError):
                    nonlinear.candidate_source(model, replace(witness, p00=number))


if __name__ == "__main__":
    unittest.main()
