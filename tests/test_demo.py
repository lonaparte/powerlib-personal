"""Exercise successful certificates and intentional failures at both kernels."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from fractions import Fraction

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from bridge import extract, render
from common import ROOT, audit, check_lean, run
from powerlib import admission_source, candidate_source, read_model


class InputTests(unittest.TestCase):
    def check_input(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "model.json"
            path.write_text(text)
            return read_model(path)

    def test_exact_rationals(self):
        self.assertEqual(self.check_input('{"resistance":"3/2","inductance":"2/3"}'),
                         (Fraction(3, 2), Fraction(2, 3)))

    def test_bad_inputs(self):
        for data in [
            {"resistance": 2.0, "inductance": 1},
            {"resistance": True, "inductance": 1},
            {"resistance": 2, "inductance": 0},
            {"resistance": 2, "inductance": -1},
            {"resistance": 2, "inductance": "1/0"},
            {"resistance": 2},
            {"resistance": 2, "inductance": 1, "certificate": {}},
            {"resistance": "by sorry", "inductance": 1},
            [],
        ]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                self.check_input(json.dumps(data))
        for text in ['{', '{"resistance":2,"resistance":3,"inductance":1}']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.check_input(text)

    def test_wire_decoder(self):
        valid = [20261003, 1, 2, 0, 3, 1, 3, 1]
        for bad in [valid + [0], valid[:-1], [20261003, 2, 0, 1],
                    [20261003, 1, 99, 1], [20261003, 1, 1, 0]]:
            with self.subTest(wire=bad), self.assertRaises(ValueError):
                render(bad, "test")
        for expression in ["20261003 ∷ [] extra", "(1 ∷ []", "1 2 ∷ []"]:
            log = json.dumps({"info": {"kind": "NormalForm", "expr": expression}})
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                extract(log)


class KernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        (ROOT / "results").mkdir(exist_ok=True)
        cls.directory = tempfile.TemporaryDirectory(prefix="tests-", dir=ROOT / "results")
        cls.root = Path(cls.directory.name)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def check_source(self, name, source, accepted):
        path = self.root / (name + ".lean")
        path.write_text(source)
        if accepted:
            check_lean(path)
        else:
            code, log = run(["lake", "env", "lean", path])
            self.assertNotEqual(code, 0, log)
            self.assertNotIn("unknown module", log)
            self.assertNotIn("object file", log)
            return log

    def test_valid_certificates(self):
        for resistance, inductance in [(Fraction(2), Fraction(1)), (Fraction(3, 2), Fraction(2, 3))]:
            p, rate = inductance / (2 * resistance), 2 * resistance / inductance
            self.check_source("valid", candidate_source(resistance, inductance, p, rate) +
                              admission_source(resistance, inductance, p, rate), True)

    def test_wrong_witnesses_and_model(self):
        r, l, p, rate = Fraction(2), Fraction(1), Fraction(1, 4), Fraction(4)
        admission = admission_source(r, l, p, rate)
        self.check_source("bad_p", candidate_source(r, l, Fraction(1), rate) + admission, False)
        self.check_source("bad_rate", candidate_source(r, l, p, Fraction(3)) + admission, False)
        # A valid witness for a different model must not satisfy this submission.
        log = self.check_source("bad_model", candidate_source(2*r, 2*l, p, rate) + admission, False)
        self.assertIn("type mismatch", log)

    def test_no_sorry(self):
        r, l, p, rate = Fraction(2), Fraction(1), Fraction(1, 4), Fraction(4)
        source = candidate_source(r, l, p, rate).replace(
            "norm_num [model, powerlib.toStateSpace, powerlib.generated.convert, powerlib.reciprocal]",
            "sorry") + admission_source(r, l, p, rate)
        log = self.check_source("bad_sorry", source, False)
        self.assertIn("Unexpected axiom sorryAx", log)

    def test_exported_formula(self):
        # Well-typed but wrong data must fail the independent Lean endpoint.
        source = "import Lean\n" + render([20261003, 1, 0, 1], "test") + audit(
            ["powerlib.generated.convert_spec"], include_core=False)
        self.check_source("bad_export", source, False)

    def test_agda_roundtrip(self):
        stage = self.root / "negative-agda"
        entry = stage / "agda/powerlib/Conversion.agda"
        entry.parent.mkdir(parents=True)
        source = (ROOT / "agda/powerlib/Conversion.agda").read_text()
        source = source.replace(
            "run scale reciprocal x = scale (fst x) (reciprocal (snd x)) , reciprocal (snd x)",
            "run scale reciprocal x = fst x , reciprocal (snd x)")
        entry.write_text(source)
        (stage / "powerlib.agda-lib").write_text((ROOT / "powerlib.agda-lib").read_text())
        libraries = stage / "libraries"
        libraries.write_text(str(ROOT / ".deps/cubical/cubical.agda-lib") + "\n")
        code, log = run([ROOT / ".tools/agda", f"--library-file={libraries}",
                         "--no-default-libraries", entry], cwd=stage)
        self.assertNotEqual(code, 0, log)
        self.assertIn("recover", log)
        self.assertNotIn("Failed to find source", log)

    def test_cli_rejects_unstable_models(self):
        for r in [0, -1]:
            path = self.root / "unstable.json"
            path.write_text(json.dumps({"resistance": r, "inductance": 1}))
            code, log = run([sys.executable, ROOT / "scripts/powerlib.py", "atp", path])
            self.assertNotEqual(code, 0, log)
            self.assertEqual(json.loads(log)["status"], "NOT_ACCEPTED")


if __name__ == "__main__":
    unittest.main()
