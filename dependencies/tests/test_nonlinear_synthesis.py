"""Check exact nonlinear synthesis, coefficient identities, and rejected witnesses."""
from copy import deepcopy
from dataclasses import replace
from fractions import Fraction as F
import json
from pathlib import Path
import sys
from tempfile import NamedTemporaryFile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from nonlinear_synthesis import _ldl_sos, model_from_data, read_model, synthesize, verify_witness


SCHEMA = "powerlib.polynomial2.v1"


def term(coefficient, a, b):
    return {"coefficient": str(coefficient), "powers": [a, b]}


def coupled_data():
    # The linear coupling and cubic dissipation require a non-diagonal P.
    return {
        "schema": SCHEMA,
        "field": [
            [term(-1, 1, 0), term(1, 0, 1), term(-1, 3, 0), term(-2, 1, 2)],
            [term(-2, 0, 1), term(-1, 0, 3), term(-3, 2, 1)],
        ],
    }


def second_coupled_data():
    return {
        "schema": SCHEMA,
        "field": [
            [term(-2, 1, 0), term(2, 0, 1), term(-3, 3, 0), term(-4, 1, 2)],
            [term(-3, 0, 1), term(-2, 0, 3), term(-5, 2, 1)],
        ],
    }


# Independent coefficient arithmetic: these checks do not call production
# polynomial helpers or the production witness verifier.
def coefficients(poly):
    result = {}
    for item in poly:
        result[item.powers] = result.get(item.powers, F(0)) + item.coefficient
    return {powers: value for powers, value in result.items() if value}


def add(*polys):
    result = {}
    for poly in polys:
        for powers, value in poly.items():
            result[powers] = result.get(powers, F(0)) + value
    return {powers: value for powers, value in result.items() if value}


def scale(value, poly):
    return {powers: value * coefficient for powers, coefficient in poly.items()
            if value * coefficient}


def multiply(left, right):
    result = {}
    for (a, b), c in left.items():
        for (d, e), f in right.items():
            powers = (a + d, b + e)
            result[powers] = result.get(powers, F(0)) + c * f
    return {powers: value for powers, value in result.items() if value}


def differentiate(poly, axis):
    result = {}
    for powers, value in poly.items():
        if powers[axis]:
            derived = list(powers)
            derived[axis] -= 1
            result[tuple(derived)] = value * powers[axis]
    return result


def sos_polynomial(squares):
    return add(*(scale(square.weight, multiply(coefficients(square.poly),
                                               coefficients(square.poly)))
                 for square in squares))


class InputTests(unittest.TestCase):
    def test_exact_integer_and_rational_input(self):
        data = coupled_data()
        data["field"][0][0]["coefficient"] = -1
        data["field"][0][1]["coefficient"] = "2/3"
        model = model_from_data(data)
        self.assertEqual(coefficients(model.field0)[(1, 0)], F(-1))
        self.assertEqual(coefficients(model.field0)[(0, 1)], F(2, 3))
        for poly in (model.field0, model.field1):
            self.assertTrue(all(type(item.coefficient) is F for item in poly))

    def test_coefficients_reject_float_bool_and_invalid_rationals(self):
        for value in [1.0, 0.5, True, False, None, {}, [], "1/0", "nan",
                      "inf", "", "by sorry"]:
            data = coupled_data()
            data["field"][0][0]["coefficient"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                model_from_data(data)

    def test_schema_rejects_certificate_fields_and_extra_keys(self):
        valid = coupled_data()
        for data in [[], {}, valid | {"schema": "powerlib.polynomial2.v2"},
                     {"field": valid["field"]}, {"schema": SCHEMA},
                     valid | {"P": [[1, 0], [0, 1]]}, valid | {"rate": "1"},
                     valid | {"extra": "1"}]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                model_from_data(data)
        for extra in [{"extra": "1"}, {"P": "1"}, {"rate": "1"}]:
            data = deepcopy(valid)
            data["field"][0][0].update(extra)
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                model_from_data(data)

    def test_invalid_dimension_powers_and_equilibrium(self):
        valid = coupled_data()
        for field in [None, {}, [], valid["field"][:1], valid["field"] + [[]],
                      [None, valid["field"][1]], [{}, valid["field"][1]]]:
            with self.subTest(field=field), self.assertRaises(ValueError):
                model_from_data(valid | {"field": field})
        for powers in [[], [1], [1, 0, 0], [-1, 0], [True, 0], [1.0, 0],
                       ["1", 0], [4, 0], [2, 2], None]:
            data = deepcopy(valid)
            data["field"][0][0]["powers"] = powers
            with self.subTest(powers=powers), self.assertRaises(ValueError):
                model_from_data(data)
        data = deepcopy(valid)
        data["field"][0].append(term(1, 0, 0))
        with self.assertRaises(ValueError):
            model_from_data(data)
        for malformed in [{"coefficient": "1"}, {"powers": [1, 0]}, "-x"]:
            data = deepcopy(valid)
            data["field"][0][0] = malformed
            with self.subTest(term=malformed), self.assertRaises(ValueError):
                model_from_data(data)


    def test_read_model_rejects_duplicate_json_keys_at_every_level(self):
        empty_field = json.dumps([[], []])
        texts = [
            '{"schema":' + json.dumps(SCHEMA) + ',"schema":' + json.dumps(SCHEMA)
            + ',"field":' + empty_field + '}',
            '{"schema":' + json.dumps(SCHEMA) + ',"field":' + empty_field
            + ',"field":' + empty_field + '}',
        ]
        for duplicate_term in [
                '{"coefficient":"-1","coefficient":"-2","powers":[1,0]}',
                '{"coefficient":"-1","powers":[1,0],"powers":[0,1]}']:
            texts.append('{"schema":' + json.dumps(SCHEMA)
                         + ',"field":[[' + duplicate_term + '],[]]}')
        for text in texts:
            with self.subTest(text=text), NamedTemporaryFile(mode="w+", suffix=".json") as file:
                file.write(text)
                file.flush()
                with self.assertRaises(ValueError):
                    read_model(file.name)


class SynthesisTests(unittest.TestCase):
    def assert_search_unproved(self, result):
        self.assertEqual(result.status, "UNPROVED")
        self.assertIsNone(result.witness)
        self.assertTrue(result.reason)
        for claim in ["refuted", "unstable", "disproved"]:
            self.assertNotIn(claim, result.reason.lower())

    def lie_coefficients(self, model, value):
        return add(multiply(differentiate(value, 0), coefficients(model.field0)),
                   multiply(differentiate(value, 1), coefficients(model.field1)))

    def assert_exact_certificate(self, model, witness):
        for value in [witness.p00, witness.p01, witness.p11,
                      witness.lower, witness.upper, witness.rate]:
            self.assertIs(type(value), F)
        self.assertGreater(witness.lower, 0)
        self.assertGreater(witness.upper, 0)
        self.assertGreater(witness.rate, 0)
        for squares in [witness.lower_sos, witness.upper_sos, witness.decay_sos]:
            for square in squares:
                self.assertIs(type(square.weight), F)
                self.assertGreaterEqual(square.weight, 0)
                self.assertTrue(all(type(item.coefficient) is F for item in square.poly))
        energy = {(2, 0): witness.p00, (1, 1): 2 * witness.p01,
                  (0, 2): witness.p11}
        norm_squared = {(2, 0): F(1), (0, 2): F(1)}
        lie = add(multiply(differentiate(energy, 0), coefficients(model.field0)),
                  multiply(differentiate(energy, 1), coefficients(model.field1)))
        self.assertEqual(sos_polynomial(witness.lower_sos),
                         add(energy, scale(-witness.lower, norm_squared)))
        self.assertEqual(sos_polynomial(witness.upper_sos),
                         add(scale(witness.upper, norm_squared), scale(-1, energy)))
        self.assertEqual(sos_polynomial(witness.decay_sos),
                         add(scale(-1, lie), scale(-witness.rate, energy)))
        verify_witness(model, witness)

    def assert_mixed_quartic_square(self, witness):
        mixed_squares = [square for square in witness.decay_sos
                         if square.weight > 0 and
                         len([powers for powers in coefficients(square.poly)
                              if sum(powers) == 2]) > 1]
        self.assertTrue(mixed_squares,
                        "Quartic dissipation must use a square with mixed quadratic terms")
        decay = sos_polynomial(witness.decay_sos)
        self.assertTrue(decay.get((3, 1), 0) or decay.get((1, 3), 0))

    def test_coupled_cubic_synthesizes_expected_non_diagonal_energy(self):
        model = model_from_data(coupled_data())
        result = synthesize(model)
        self.assertEqual(result.status, "CANDIDATE", result.reason)
        self.assertIsNotNone(result.witness)
        witness = result.witness
        self.assertEqual((witness.p00, witness.p01, witness.p11),
                         (F(1, 2), F(1, 6), F(1, 3)))
        self.assert_exact_certificate(model, witness)
        self.assert_mixed_quartic_square(witness)

    def test_different_coupled_cubic_is_actually_synthesized(self):
        model = model_from_data(second_coupled_data())
        result = synthesize(model)
        self.assertEqual(result.status, "CANDIDATE", result.reason)
        self.assertIsNotNone(result.witness)
        self.assertNotEqual(result.witness.p01, 0)
        self.assert_exact_certificate(model, result.witness)
        self.assert_mixed_quartic_square(result.witness)

    def test_locally_stable_escape_field_remains_unproved(self):
        data = {"schema": SCHEMA,
                "field": [[term(-1, 1, 0), term(1, 3, 0)], [term(-1, 0, 1)]]}
        result = synthesize(model_from_data(data))
        self.assertEqual(result.status, "UNPROVED")
        self.assertIsNone(result.witness)
        self.assertTrue(result.reason)
        self.assertNotIn("refuted", result.reason.lower())

    def test_quadratic_field_is_not_claimed_proved_or_refuted(self):
        data = {"schema": SCHEMA,
                "field": [[term(-1, 1, 0), term(-1, 2, 0)], [term(-1, 0, 1)]]}
        result = synthesize(model_from_data(data))
        self.assertEqual(result.status, "UNPROVED")
        self.assertIsNone(result.witness)
        self.assertTrue(result.reason)
        self.assertNotIn("refuted", result.reason.lower())

    def test_globally_asymptotic_cubic_without_exponential_rate_is_unproved(self):
        model = model_from_data({"schema": SCHEMA,
                                 "field": [[term(-1, 3, 0)], [term(-1, 0, 3)]]})
        # This radially unbounded V has a strictly negative derivative off the
        # origin, proving GAS. No uniform positive quadratic decay rate exists:
        # at (epsilon, 0), -dot(V)/V = 2*epsilon**2 tends to zero.
        value = {(2, 0): F(1), (0, 2): F(1)}
        self.assertEqual(self.lie_coefficients(model, value),
                         {(4, 0): F(-2), (0, 4): F(-2)})
        self.assert_search_unproved(synthesize(model))

    def test_true_exponential_stability_can_defeat_fixed_q_candidate(self):
        model = model_from_data({
            "schema": SCHEMA,
            "field": [[term(-1, 1, 0), term(-2, 2, 1), term(-4, 0, 3)],
                      [term(-1, 0, 1), term(1, 3, 0), term(2, 1, 2)]],
        })
        # W=x**2+2*y**2 proves GES with dot(W)=-2*W, whereas the fixed
        # Q=I linear equation chooses V=(x**2+y**2)/2, whose derivative is
        # positive at (1,-1). Search failure therefore cannot refute stability.
        value = {(2, 0): F(1), (0, 2): F(2)}
        self.assertEqual(self.lie_coefficients(model, value), scale(F(-2), value))
        fixed_q_value = {(2, 0): F(1, 2), (0, 2): F(1, 2)}
        fixed_q_lie = self.lie_coefficients(model, fixed_q_value)
        self.assertEqual(sum(c * (-1) ** b for (a, b), c in fixed_q_lie.items()), F(1))
        self.assert_search_unproved(synthesize(model))

    def test_true_exponential_quadratic_field_is_not_truncated(self):
        model = model_from_data({
            "schema": SCHEMA,
            "field": [[term(-1, 1, 0), term(-2, 1, 1)],
                      [term(-1, 0, 1), term(1, 2, 0)]],
        })
        # The quadratic terms cancel for this energy, proving GES; the current
        # cubic search must report its unsupported terms instead of dropping them.
        value = {(2, 0): F(1), (0, 2): F(2)}
        self.assertEqual(self.lie_coefficients(model, value), scale(F(-2), value))
        result = synthesize(model)
        self.assert_search_unproved(result)
        self.assertIn("quadratic", result.reason.lower())

    def test_rank_one_quartic_requires_nondyadic_rational_gram_parameter(self):
        # f=(-x+y-(x+y)**3, -2*y-2*(x+y)**3). The quartic dissipation
        # equals (5/3)*(x+y)**4, whose PSD Gram matrix requires free=5/3.
        model = model_from_data({
            "schema": SCHEMA,
            "field": [[term(-1, 1, 0), term(1, 0, 1), term(-1, 3, 0),
                       term(-3, 2, 1), term(-3, 1, 2), term(-1, 0, 3)],
                      [term(-2, 0, 1), term(-2, 3, 0), term(-6, 2, 1),
                       term(-6, 1, 2), term(-2, 0, 3)]],
        })
        self.assert_search_unproved(synthesize(model, denominator_bound=2))
        result = synthesize(model)
        self.assertEqual(result.status, "CANDIDATE", result.reason)
        self.assertIsNotNone(result.witness)
        self.assert_exact_certificate(model, result.witness)
        quartic = {powers: value for powers, value in sos_polynomial(result.witness.decay_sos).items()
                   if sum(powers) == 4}
        self.assertEqual(quartic, {(4, 0): F(5, 3), (3, 1): F(20, 3),
                                  (2, 2): F(10), (1, 3): F(20, 3), (0, 4): F(5, 3)})
        quartic_squares = [square for square in result.witness.decay_sos
                          if any(sum(item.powers) == 2 for item in square.poly)]
        self.assertEqual(len(quartic_squares), 1)
        self.assertEqual(quartic_squares[0].weight, F(5, 3))
        self.assertEqual(coefficients(quartic_squares[0].poly),
                         {(2, 0): F(1), (1, 1): F(2), (0, 2): F(1)})

    def test_increasing_quartic_search_budget_proves_the_same_stable_model(self):
        model = model_from_data({
            "schema": SCHEMA,
            "field": [[term(-1, 1, 0), term(-1, 3, 0), term("35/2", 1, 2)],
                      [term(-1, 0, 1), term("35/2", 2, 1), term(-324, 0, 3)]],
        })
        # With V=(x**2+y**2)/2, -dot(V)=x**2+y**2+q, where
        # q=(x**2-18*y**2)**2+(x*y)**2. Thus the system is GES.
        # Its quartic Gram parameter must lie in [-18,-35/2]; the default
        # numerator bound 16 misses that interval, while bound 18 finds it.
        value = {(2, 0): F(1, 2), (0, 2): F(1, 2)}
        expected_quartic = {(4, 0): F(1), (2, 2): F(-35), (0, 4): F(324)}
        negative_lie = scale(F(-1), self.lie_coefficients(model, value))
        self.assertEqual(negative_lie,
                         add({(2, 0): F(1), (0, 2): F(1)}, expected_quartic))
        square = {(2, 0): F(1), (0, 2): F(-18)}
        self.assertEqual(add(multiply(square, square), {(2, 2): F(1)}),
                         expected_quartic)
        self.assert_search_unproved(synthesize(model))
        result = synthesize(model, numerator_bound=18)
        self.assertEqual(result.status, "CANDIDATE", result.reason)
        self.assertIsNotNone(result.witness)
        self.assertEqual((result.witness.p00, result.witness.p01, result.witness.p11),
                         (F(1, 2), F(0), F(1, 2)))
        self.assert_exact_certificate(model, result.witness)
        actual_quartic = {powers: coefficient
                          for powers, coefficient in sos_polynomial(result.witness.decay_sos).items()
                          if sum(powers) == 4}
        self.assertEqual(actual_quartic, expected_quartic)

    def test_tampered_witnesses_and_wrong_model_are_rejected(self):
        model = model_from_data(coupled_data())
        witness = synthesize(model).witness
        self.assertIsNotNone(witness)
        tampered = [replace(witness, p00=witness.p00 + 1),
                    replace(witness, p01=witness.p01 + 1),
                    replace(witness, p11=witness.p11 + 1),
                    replace(witness, lower=F(0)),
                    replace(witness, upper=-witness.upper),
                    replace(witness, rate=F(0)),
                    replace(witness, rate=witness.rate + 1),
                    replace(witness, lower_sos=()),
                    replace(witness, upper_sos=()),
                    replace(witness, decay_sos=())]
        first = witness.decay_sos[0]
        tampered.extend([
            replace(witness, decay_sos=(replace(first, weight=first.weight + 1),)
                    + witness.decay_sos[1:]),
            replace(witness, decay_sos=(replace(first, weight=F(-1)),)
                    + witness.decay_sos[1:]),
        ])
        for bad in tampered:
            with self.subTest(witness=bad), self.assertRaises(ValueError):
                verify_witness(model, bad)
        with self.assertRaises(ValueError):
            verify_witness(model_from_data(second_coupled_data()), witness)


class GramBoundaryTests(unittest.TestCase):
    def test_zero_pivot_with_nonzero_offdiagonal_is_rejected(self):
        monomials = ((2, 0), (1, 1), (0, 2))
        # Check both the initial and a later zero pivot, after elimination.
        for raw in [((0, 1, 0), (1, 1, 0), (0, 0, 1)),
                    ((1, 0, 0), (0, 0, 1), (0, 1, 1))]:
            matrix = tuple(tuple(F(value) for value in row) for row in raw)
            with self.subTest(matrix=matrix):
                self.assertIsNone(_ldl_sos(matrix, monomials))

    def test_degenerate_positive_semidefinite_gram_is_accepted(self):
        matrix = ((F(1), F(0), F(0)),
                  (F(0), F(0), F(0)),
                  (F(0), F(0), F(0)))
        squares = _ldl_sos(matrix, ((2, 0), (1, 1), (0, 2)))
        self.assertIsNotNone(squares)
        self.assertEqual(len(squares), 1)
        self.assertEqual(sos_polynomial(squares), {(4, 0): F(1)})


if __name__ == "__main__":
    unittest.main()
