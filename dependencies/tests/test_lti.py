"""General LTI synthesis, independent admission, and proof-kernel negative controls."""
import copy
from fractions import Fraction as F
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lti
import lti_bridge
from common import RESULTS, ROOT, audit, check_lean


class ExactSynthesis(unittest.TestCase):
    def test_arbitrary_dimensions_and_nonnormality(self):
        for n in (1, 2, 3, 5, 8):
            a = tuple(tuple(F(-i-1 if i == j else 3 if j == i+1 else 0)
                            for j in range(n)) for i in range(n))
            c = lti.synthesize(a)
            p = lti.matrix_from_data(c["P"])
            self.assertEqual(lti.lyapunov_product(a, p),
                             tuple(tuple(F(-int(i == j)) for j in range(n)) for i in range(n)))

    def test_unstable_and_boundary_are_unproved(self):
        for raw in ([[1]], [[0]], [[0, -1], [1, 0]], [[-1, 0], [0, 1]]):
            with self.assertRaises(lti.Unproved):
                lti.synthesize(lti.model_from_data({"A": raw}))

    def test_input_does_not_accept_witness_or_float(self):
        for raw in ({"A": [[-1]], "P": [["1/2"]]}, {"A": [[-1.0]]},
                    {"A": [[True]]}, {"A": []}, {"A": [[-1, 0]]},
                    {"A": [["by sorry"]]}):
            with self.assertRaises(ValueError):
                lti.model_from_data(raw)
        with self.assertRaises(ValueError):
            json.loads('{"A":[[-1]],"A":[[1]]}', object_pairs_hook=lti.unique_object)

    def test_bridge_rejects_malformed_and_scoped_data(self):
        for words in ([20261004, 2, 3, 2, 0, 1],  # legacy lossy interface
                      [20261004, 3, 0], [20261004, 3, 1, 1],
                      [20261004, 3, 3, 1, 2], [20261004, 3, 3, 2, 0, 1, 0],
                      [20261004, 3, 3, 2, 0, 1, 0, 1, 0, 0],
                      [20261004, 3, 3, 2, 0, True, 0, 1, 0],
                      [20261004, 3, 3, 1, -1]):
            with self.assertRaises(ValueError):
                lti_bridge.render(words, "test")

    def test_bridge_retains_each_index_and_nested_binding(self):
        good = lti_bridge.render([20261004, 3, 3, 2, 0, 1, 0, 1, 0], "test")
        wrong_state = lti_bridge.render([20261004, 3, 3, 2, 0, 1, 0, 1, 1], "test")
        transposed = lti_bridge.render([20261004, 3, 3, 2, 0, 0, 1, 1, 0], "test")
        nested = lti_bridge.render([20261004, 3, 3, 3, 2, 0, 2, 1, 1, 0], "test")
        self.assertIn("A i j0 * x j0", good)
        self.assertIn("A i j0 * x i", wrong_state)
        self.assertIn("A j0 i * x j0", transposed)
        self.assertIn("A i j0 * x j1", nested)
        self.assertNotEqual(good, wrong_state)
        self.assertNotEqual(good, transposed)


@unittest.skipUnless(os.environ.get("POWERLIB_LTI_KERNEL_TESTS") == "1", "enable LTI kernel controls")
class KernelAdmission(unittest.TestCase):
    def setUp(self):
        RESULTS.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="lti-test-", dir=RESULTS)
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def check_source(self, source):
        path = self.root / "Proof.lean"
        path.write_text(source)
        return check_lean(path)

    def test_synthesized_proofs_across_dimensions(self):
        # Repeated eigenvalue/Jordan block, coupled oscillator, and higher dimension.
        for raw in ([[-1]], [[-1, 10], [0, -1]], [[0, 1], [-2, -3]],
                    [[-1, 1, 0, 0], [0, -2, 1, 0], [0, 0, -3, 1], [0, 0, 0, -4]]):
            a = lti.model_from_data({"A": raw})
            c = lti.synthesize(a)
            self.check_source(lti.candidate_source(c) + lti.admission_source(a))

    def test_wrong_model_rejected(self):
        a = lti.model_from_data({"A": [[-1, 0], [0, -2]]})
        b = lti.model_from_data({"A": [[-2, 0], [0, -1]]})
        with self.assertRaises(RuntimeError):
            self.check_source(lti.candidate_source(lti.synthesize(a)) + lti.admission_source(b))

    def test_wrong_scoped_wire_rejected_by_lean(self):
        for words in ([20261004, 3, 3, 2, 0, 1, 0, 1, 1],
                      [20261004, 3, 3, 2, 0, 0, 1, 1, 0]):
            source = "import Lean\n" + lti_bridge.render(words, "test")
            with self.subTest(wire=words), self.assertRaises(RuntimeError):
                self.check_source(source + audit(["powerlib.generated.linearField_spec"],
                                                include_core=False))

    def test_changed_agda_operation_rejected_before_publication(self):
        source = (ROOT / "theorems/LTIFoundation.agda").read_text()
        mutations = [
            ("(stateEntry fzero))", "(stateEntry (fsuc fzero)))"),
            ("(matrixEntry (fsuc fzero) fzero)", "(matrixEntry fzero (fsuc fzero))"),
            ("run sum mul A x i = eval sum mul A x (λ _ → i) body",
             "run sum mul A x i = sum (λ j → mul (A i j) (x i))"),
            ("eval sum mul A x env (matrixEntry i j) = A (env i) (env j)",
             "eval sum mul A x env (matrixEntry i j) = A (env j) (env i)"),
        ]
        for old, new in mutations:
            with self.subTest(mutation=old), tempfile.TemporaryDirectory(dir=self.root) as directory:
                stage = Path(directory)
                (stage / "theorems").mkdir()
                self.assertEqual(source.count(old), 1)
                (stage / "theorems/LTIFoundation.agda").write_text(source.replace(old, new))
                shutil.copy(ROOT / "powerlib.agda-lib", stage)
                target, snapshot = stage / "Exported.lean", stage / "wire.json"
                with patch.multiple(lti_bridge, ROOT=stage, TARGET=target, SNAPSHOT=snapshot,
                                    RESULTS=stage / "results"):
                    with self.assertRaisesRegex(RuntimeError, r"!=|≠"):
                        lti_bridge.rebuild(write=True)
                self.assertFalse(target.exists())
                self.assertFalse(snapshot.exists())

    def test_tampered_identity_bounds_and_witness_rejected(self):
        a = lti.model_from_data({"A": [[-1, 10], [0, -1]]})
        original = lti.synthesize(a)
        for kind in ("P", "lower", "upper", "lower_D", "unstable_model"):
            c = copy.deepcopy(original)
            if kind == "P":
                c["P"][0][0] = "-1"
            elif kind == "lower":
                c["lower"] = "1000"
            elif kind == "upper":
                c["upper"] = "1/1000"
            elif kind == "lower_D":
                c["lower_D"][0] = "-1"
            else:
                c["model"]["A"][0][0] = "1"
            with self.subTest(kind=kind), self.assertRaises(RuntimeError):
                self.check_source(lti.candidate_source(c) + lti.admission_source(a))

    def test_transitive_custom_axiom_and_sorry_rejected(self):
        a = lti.model_from_data({"A": [[-1]]})
        prefix = "import powerlib\nnamespace Candidate\n" + lti.model_source("model", a)
        for declaration in (
            "axiom counterfeit : powerlib.LTI.Accepted model\ndef certificate := counterfeit\n",
            "def certificate : powerlib.LTI.Accepted model := by sorry\n"):
            with self.assertRaisesRegex(RuntimeError, "Unexpected axiom"):
                self.check_source(prefix + declaration + "end Candidate\n" + lti.admission_source(a))

    def test_end_to_end_and_supplied_witness_maturity(self):
        path = self.root / "model.json"
        path.write_text('{"A":[[-1,10],[0,-1]]}')
        report = lti.atp(path)
        self.assertEqual(report["status"], "ACCEPTED")
        self.assertEqual(report["maturity"], "S-level")
        self.assertEqual(report["agda_bridge"]["status"], "AGDA_AND_LEAN_CHECKED")
        supplied = lti.admit(path, lti.synthesize(lti.read_model(path)))
        self.assertEqual(supplied["maturity"], "Lean theorem")
        path.write_text('{"A":[[0]]}')
        self.assertEqual(lti.atp(path)["status"], "UNPROVED")


if __name__ == "__main__":
    unittest.main()
