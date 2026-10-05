"""Check synthesized nonlinear witnesses and reject altered proposals in Lean."""
from dataclasses import replace
from fractions import Fraction as F
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import RESULTS, check_lean
from nonlinear import admission_source, candidate_source, proof_source
from nonlinear_synthesis import model_from_data, synthesize


def term(coefficient, a, b):
    return {"coefficient": str(coefficient), "powers": [a, b]}


def held_out_model():
    # This field is distinct from the synthesizer's two coupled examples. All
    # energy, coercivity, rate, and SOS data must come from automatic synthesis.
    return model_from_data({
        "schema": "powerlib.polynomial2.v1",
        "field": [
            [term(-3, 1, 0), term(1, 0, 1), term(-1, 3, 0), term(-1, 1, 2)],
            [term(-2, 0, 1), term(-1, 2, 1), term(-1, 0, 3)],
        ],
    })


@unittest.skipUnless(os.environ.get("POWERLIB_NONLINEAR_KERNEL_TESTS") == "1",
                     "Set POWERLIB_NONLINEAR_KERNEL_TESTS=1 after building Polynomial2")
class KernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model = held_out_model()
        result = synthesize(cls.model)
        if result.witness is None:
            raise AssertionError(f"Held-out field was not synthesized: {result.reason}")
        cls.witness = result.witness
        RESULTS.mkdir(parents=True, exist_ok=True)
        cls.directory = tempfile.TemporaryDirectory(prefix="nonlinear-tests-", dir=RESULTS)
        cls.root = Path(cls.directory.name)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def write_source(self, name, source):
        path = self.root / (name + ".lean")
        path.write_text(source)
        return path

    def reject(self, name, source, expected=None):
        proof = self.write_source(name, source)
        with self.assertRaises(RuntimeError):
            check_lean(proof)
        log = proof.with_suffix(".log").read_text()
        for missing_dependency in ["unknown module", "object file", "module prefix",
                                   "No such file or directory"]:
            self.assertNotIn(missing_dependency, log)
        self.assertNotIn("POWERLIB_KERNEL_OK", log)
        self.assertFalse(proof.with_suffix(".checked.json").exists())
        if expected is not None:
            self.assertIn(expected, log)

    def changed_decay_square(self, change):
        squares = self.witness.decay_sos
        index = next(i for i, square in enumerate(squares)
                     if square.weight > 0 and any(t.coefficient != 0 for t in square.poly))
        changed = list(squares)
        changed[index] = change(squares[index])
        return replace(self.witness, decay_sos=tuple(changed))

    def test_held_out_coupled_field_is_kernel_checked(self):
        self.assertNotEqual(self.witness.p01, 0)
        self.assertTrue(any(any(sum(t.powers) == 2 for t in square.poly)
                            for square in self.witness.decay_sos))
        proof = self.write_source("held_out", proof_source(self.model, self.witness))
        log = check_lean(proof)
        self.assertIn("POWERLIB_KERNEL_OK", log)
        self.assertTrue(proof.with_suffix(".checked.json").exists())

    def test_empty_sos_identities_are_kernel_checked(self):
        model = model_from_data({
            "schema": "powerlib.polynomial2.v1",
            "field": [[term("-1/2", 1, 0)], [term("-1/2", 0, 1)]],
        })
        result = synthesize(model)
        self.assertIsNotNone(result.witness, result.reason)
        witness = result.witness
        self.assertEqual((witness.lower_sos, witness.upper_sos, witness.decay_sos),
                         ((), (), ()))
        proof = self.write_source("empty_sos", proof_source(model, witness))
        self.assertIn("POWERLIB_KERNEL_OK", check_lean(proof))

    def test_changed_matrix_cannot_reuse_old_sos(self):
        bad = replace(self.witness, p00=self.witness.p00 + 1)
        self.reject("changed_matrix", proof_source(self.model, bad), "unsolved goals")

    def test_excessive_rate_cannot_reuse_old_sos(self):
        bad = replace(self.witness, rate=self.witness.rate + 100)
        self.reject("excessive_rate", proof_source(self.model, bad), "unsolved goals")

    def test_negative_sos_weight_is_rejected(self):
        bad = self.changed_decay_square(lambda square: replace(square, weight=F(-1)))
        self.reject("negative_weight", proof_source(self.model, bad), "unsolved goals")

    def test_changed_sos_polynomial_is_rejected(self):
        def change(square):
            terms = list(square.poly)
            index = next(i for i, t in enumerate(terms) if t.coefficient != 0)
            terms[index] = replace(terms[index], coefficient=2 * terms[index].coefficient)
            return replace(square, poly=tuple(terms))

        bad = self.changed_decay_square(change)
        self.reject("changed_square", proof_source(self.model, bad), "unsolved goals")

    def test_nonpositive_coercivity_is_rejected(self):
        bad = replace(self.witness, lower=F(0))
        self.reject("zero_lower", proof_source(self.model, bad), "unsolved goals")

    def test_certificate_for_another_field_is_not_admitted(self):
        submitted = model_from_data({
            "schema": "powerlib.polynomial2.v1",
            "field": [[term(-1, 1, 0), term(1, 3, 0)], [term(-1, 0, 1)]],
        })
        source = candidate_source(self.model, self.witness) + admission_source(submitted)
        self.reject("other_field", source, "type mismatch")

    def test_original_json_overrules_the_proposed_model(self):
        submitted = self.root / "original.json"
        submitted.write_text(json.dumps({
            "schema": "powerlib.polynomial2.v1",
            "field": [[term(-1, 1, 0), term(1, 3, 0)], [term(-1, 0, 1)]],
        }))
        # Even if the proposal's model object claims its own field was submitted,
        # admission must compile the original JSON into the independent target.
        source = candidate_source(self.model, self.witness) + admission_source(
            self.model, original_path=submitted)
        self.reject("original_field", source, "type mismatch")

    def test_sorry_is_rejected_by_transitive_audit(self):
        source = proof_source(self.model, self.witness).replace("by norm_num", "by sorry")
        self.reject("sorry", source, "sorryAx")

    def test_custom_axiom_is_rejected_by_transitive_audit(self):
        source = proof_source(self.model, self.witness).replace(
            "namespace Candidate", "axiom forbidden : False\nnamespace Candidate", 1)
        source = source.replace("by norm_num", "by exact False.elim forbidden")
        self.reject("custom_axiom", source, "Unexpected axiom forbidden")


if __name__ == "__main__":
    unittest.main()
