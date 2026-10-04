"""Shared rational solver and the existing family-specific failure contracts."""
from fractions import Fraction as F
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import exact
import lcl
import lti


class ExactLinearTests(unittest.TestCase):
    def test_rational_solution_with_pivot_and_unchanged_inputs(self):
        matrix = [[F(0), F(2, 3)], [F(3, 5), F(1, 7)]]
        expected = (F(5, 11), F(-2, 13))
        rhs = [sum(a*x for a, x in zip(row, expected)) for row in matrix]
        original = [row[:] for row in matrix], rhs[:]
        for solver in (exact.solve_linear, lcl.solve_linear, lti.solve_linear):
            with self.subTest(solver=solver.__module__):
                self.assertEqual(solver(matrix, rhs), expected)
                self.assertEqual((matrix, rhs), original)

    def test_singular_failure_contracts_are_preserved(self):
        for rhs in ([F(0)], [F(1)]):
            matrix = [[F(0)]]
            with self.assertRaises(exact.SingularSystem):
                exact.solve_linear(matrix, rhs)
            with self.assertRaisesRegex(ValueError, "The Lyapunov equation is singular") as caught:
                lcl.solve_linear(matrix, rhs)
            self.assertIs(type(caught.exception), ValueError)
            with self.assertRaisesRegex(lti.Unproved, "Singular Lyapunov operator"):
                lti.solve_linear(matrix, rhs)


if __name__ == "__main__":
    unittest.main()
