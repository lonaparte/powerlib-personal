"""Exact, witness-free quadratic/SOS search for two-state cubic polynomial ODEs.

The algorithm is untrusted. A CANDIDATE contains only rational data for independent
Lean checking; search exhaustion is UNPROVED and never a stability refutation.
"""
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import re


SCHEMA = "powerlib.polynomial2.v1"
Powers = tuple[int, int]


@dataclass(frozen=True)
class Term:
    coefficient: Fraction
    powers: Powers

    def __post_init__(self):
        if type(self.coefficient) is not Fraction:
            raise ValueError("Polynomial coefficients must be exact Fraction values")
        if (not isinstance(self.powers, tuple) or len(self.powers) != 2
                or any(type(power) is not int or power < 0 for power in self.powers)):
            raise ValueError("Monomial powers must be a pair of nonnegative integers")


Polynomial = tuple[Term, ...]


def polynomial(coefficients: dict[Powers, Fraction]) -> Polynomial:
    return tuple(Term(coefficient, powers)
                 for powers, coefficient in sorted(coefficients.items(),
                                                   key=lambda item: (sum(item[0]), item[0]))
                 if coefficient)


def coefficients(poly: Polynomial) -> dict[Powers, Fraction]:
    result = {}
    for term in poly:
        result[term.powers] = result.get(term.powers, Fraction(0)) + term.coefficient
    return {powers: coefficient for powers, coefficient in result.items() if coefficient}


def add(left: Polynomial, right: Polynomial) -> Polynomial:
    values = coefficients(left)
    for powers, coefficient in coefficients(right).items():
        values[powers] = values.get(powers, Fraction(0)) + coefficient
    return polynomial(values)


def scale(value: Fraction, poly: Polynomial) -> Polynomial:
    return polynomial({powers: value * coefficient
                       for powers, coefficient in coefficients(poly).items()})


def multiply(left: Polynomial, right: Polynomial) -> Polynomial:
    values = {}
    for a in left:
        for b in right:
            powers = (a.powers[0] + b.powers[0], a.powers[1] + b.powers[1])
            values[powers] = values.get(powers, Fraction(0)) + a.coefficient * b.coefficient
    return polynomial(values)


def derivative(poly: Polynomial, coordinate: int) -> Polynomial:
    values = {}
    for term in poly:
        power = term.powers[coordinate]
        if power:
            powers = list(term.powers)
            powers[coordinate] -= 1
            values[tuple(powers)] = term.coefficient * power
    return polynomial(values)


NORM_SQUARED = polynomial({(2, 0): Fraction(1), (0, 2): Fraction(1)})


@dataclass(frozen=True)
class Model:
    field0: Polynomial
    field1: Polynomial

    def __post_init__(self):
        for poly in self.field:
            if not isinstance(poly, tuple) or any(not isinstance(term, Term) for term in poly):
                raise ValueError("The field must contain exact polynomial term tuples")
            if any(sum(term.powers) > 3 for term in poly):
                raise ValueError("The supported input degree is at most three")
            if coefficients(poly).get((0, 0), Fraction(0)):
                raise ValueError("The input field must have the origin as an equilibrium")

    @property
    def field(self) -> tuple[Polynomial, Polynomial]:
        return self.field0, self.field1

    def serialized(self):
        return {"schema": SCHEMA,
                "field": [[{"coefficient": str(term.coefficient),
                            "powers": list(term.powers)} for term in poly]
                          for poly in self.field]}


def _rational(value):
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError("Use integers or exact rational strings for coefficients")
    text = str(value)
    if len(text) > 100 or not re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", text):
        raise ValueError("Expected a rational with a positive denominator")
    return Fraction(text)


def model_from_data(data) -> Model:
    if (not isinstance(data, dict) or set(data) != {"schema", "field"}
            or data["schema"] != SCHEMA):
        raise ValueError("Expected the polynomial2 schema and exactly its field key")
    field = data["field"]
    if not isinstance(field, list) or len(field) != 2:
        raise ValueError("The field must have exactly two coordinates")
    parsed = []
    for coordinate in field:
        if not isinstance(coordinate, list) or len(coordinate) > 128:
            raise ValueError("Each coordinate must be a list of at most 128 monomials")
        values = {}
        for term in coordinate:
            if not isinstance(term, dict) or set(term) != {"coefficient", "powers"}:
                raise ValueError("Each monomial needs exactly coefficient and powers")
            powers = term["powers"]
            if (not isinstance(powers, list) or len(powers) != 2
                    or any(type(power) is not int or power < 0 for power in powers)
                    or sum(powers) > 3):
                raise ValueError("Powers must be two nonnegative integers of total degree at most three")
            powers = tuple(powers)
            if powers in values:
                raise ValueError("Duplicate monomials are not allowed")
            values[powers] = _rational(term["coefficient"])
        parsed.append(polynomial(values))
    return Model(*parsed)


def read_model(path) -> Model:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate JSON key: {key}")
            result[key] = value
        return result
    return model_from_data(json.loads(Path(path).read_text(), object_pairs_hook=unique))


@dataclass(frozen=True)
class WeightedSquare:
    weight: Fraction
    poly: Polynomial


@dataclass(frozen=True)
class Witness:
    p00: Fraction
    p01: Fraction
    p11: Fraction
    lower: Fraction
    upper: Fraction
    rate: Fraction
    lower_sos: tuple[WeightedSquare, ...]
    upper_sos: tuple[WeightedSquare, ...]
    decay_sos: tuple[WeightedSquare, ...]

    @property
    def matrix(self):
        return ((self.p00, self.p01), (self.p01, self.p11))

    def serialized(self):
        def squares(values):
            return [{"weight": str(value.weight),
                     "poly": [{"coefficient": str(term.coefficient),
                               "powers": list(term.powers)} for term in value.poly]}
                    for value in values]
        return {"P": [[str(value) for value in row] for row in self.matrix],
                "lower": str(self.lower), "upper": str(self.upper), "rate": str(self.rate),
                "lower_sos": squares(self.lower_sos), "upper_sos": squares(self.upper_sos),
                "decay_sos": squares(self.decay_sos)}


@dataclass(frozen=True)
class SynthesisResult:
    status: str
    witness: Witness | None
    reason: str


def energy(p00: Fraction, p01: Fraction, p11: Fraction) -> Polynomial:
    return polynomial({(2, 0): p00, (1, 1): 2 * p01, (0, 2): p11})


def lie_derivative(model: Model, value: Polynomial) -> Polynomial:
    return add(multiply(derivative(value, 0), model.field0),
               multiply(derivative(value, 1), model.field1))


def sum_squares(squares: tuple[WeightedSquare, ...]) -> Polynomial:
    result = ()
    for square in squares:
        result = add(result, scale(square.weight, multiply(square.poly, square.poly)))
    return result


def verify_witness(model: Model, witness: Witness):
    """Independent exact coefficient checks; this does not replace Lean admission."""
    numbers = (witness.p00, witness.p01, witness.p11,
               witness.lower, witness.upper, witness.rate)
    if any(type(number) is not Fraction for number in numbers):
        raise ValueError("All certificate scalars must be exact Fraction values")
    if min(witness.lower, witness.upper, witness.rate) <= 0:
        raise ValueError("Norm bounds and decay rate must be strictly positive")
    for group in (witness.lower_sos, witness.upper_sos, witness.decay_sos):
        if not isinstance(group, tuple) or len(group) > 32:
            raise ValueError("SOS groups must be bounded exact tuples")
        for square in group:
            if not isinstance(square, WeightedSquare) or type(square.weight) is not Fraction:
                raise ValueError("SOS weights must be exact Fraction values")
            if square.weight < 0:
                raise ValueError("SOS weights must be nonnegative")
            if (not isinstance(square.poly, tuple)
                    or any(not isinstance(term, Term) or sum(term.powers) > 2
                           for term in square.poly)):
                raise ValueError("SOS factors must be exact polynomials of degree at most two")
    value = energy(witness.p00, witness.p01, witness.p11)
    targets = (add(value, scale(-witness.lower, NORM_SQUARED)),
               add(scale(witness.upper, NORM_SQUARED), scale(Fraction(-1), value)),
               add(scale(Fraction(-1), lie_derivative(model, value)), scale(-witness.rate, value)))
    for label, target, squares in zip(("lower", "upper", "decay"), targets,
                                      (witness.lower_sos, witness.upper_sos, witness.decay_sos)):
        if coefficients(target) != coefficients(sum_squares(squares)):
            raise ValueError(f"The {label} SOS identity does not match the submitted field")
    return True


def _solve(matrix, rhs):
    rows = [list(row) + [value] for row, value in zip(matrix, rhs)]
    size = len(rhs)
    for column in range(size):
        pivot = next((index for index in range(column, size) if rows[index][column]), None)
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        divisor = rows[column][column]
        rows[column] = [value / divisor for value in rows[column]]
        for index in range(size):
            if index != column:
                divisor = rows[index][column]
                rows[index] = [a - divisor * b for a, b in zip(rows[index], rows[column])]
    return tuple(row[-1] for row in rows)


def _quadratic_matrix(poly):
    values = coefficients(poly)
    return [[values.get((2, 0), Fraction(0)), values.get((1, 1), Fraction(0)) / 2],
            [values.get((1, 1), Fraction(0)) / 2, values.get((0, 2), Fraction(0))]]


def _lyapunov_candidate(model):
    linear = Model(*(polynomial({powers: coefficient for powers, coefficient in coefficients(poly).items()
                                if sum(powers) == 1}) for poly in model.field))
    basis = (energy(Fraction(1), Fraction(0), Fraction(0)),
             energy(Fraction(0), Fraction(1), Fraction(0)),
             energy(Fraction(0), Fraction(0), Fraction(1)))
    images = [coefficients(lie_derivative(linear, value)) for value in basis]
    matrix = [[image.get(powers, Fraction(0)) for image in images]
              for powers in ((2, 0), (1, 1), (0, 2))]
    return _solve(matrix, (Fraction(-1), Fraction(0), Fraction(-1)))


def _ldl_sos(matrix, monomials):
    """Exact PSD elimination, including singular Gram matrices and zero pivots."""
    work = [list(row) for row in matrix]
    size = len(work)
    if any(work[i][j] != work[j][i] for i in range(size) for j in range(size)):
        return None
    squares = []
    for pivot in range(size):
        weight = work[pivot][pivot]
        if weight < 0:
            return None
        if not weight:
            if any(work[pivot][j] for j in range(pivot + 1, size)):
                return None
            continue
        factor = {monomials[pivot]: Fraction(1)}
        for j in range(pivot + 1, size):
            factor[monomials[j]] = work[pivot][j] / weight
        squares.append(WeightedSquare(weight, polynomial(factor)))
        for i in range(pivot + 1, size):
            for j in range(pivot + 1, size):
                work[i][j] -= work[pivot][i] * work[pivot][j] / weight
    return tuple(squares)


def _rational_grid(numerator_bound, denominator_bound):
    yield Fraction(0)
    seen = {Fraction(0)}
    for denominator in range(1, denominator_bound + 1):
        for numerator in range(1, numerator_bound + 1):
            for value in (Fraction(numerator, denominator), Fraction(-numerator, denominator)):
                if value not in seen:
                    seen.add(value)
                    yield value


def _quartic_sos(poly, numerator_bound, denominator_bound):
    values = coefficients(poly)
    a, b, c, d, e = [values.get(powers, Fraction(0))
                     for powers in ((4, 0), (3, 1), (2, 2), (1, 3), (0, 4))]
    for free in _rational_grid(numerator_bound, denominator_bound):
        gram = ((a, b / 2, free), (b / 2, c - 2 * free, d / 2), (free, d / 2, e))
        squares = _ldl_sos(gram, ((2, 0), (1, 1), (0, 2)))
        if squares is not None:
            return squares
    return None


def synthesize(model: Model, *, numerator_bound=16, denominator_bound=12,
               bound_steps=32, rate_steps=32) -> SynthesisResult:
    """Find P and three exact SOS identities without accepting any witness input.

    This first search supports linear and cubic terms. It tries the rational
    Lyapunov-equation candidate and a bounded binary-quartic Gram parameter grid.
    A failure describes this search and does not claim the system is unstable.
    """
    for limit in (numerator_bound, denominator_bound, bound_steps, rate_steps):
        if type(limit) is not int or limit <= 0 or limit > 1024:
            raise ValueError("Search limits must be positive integers at most 1024")
    def unproved(reason):
        return SynthesisResult("UNPROVED", None, reason)
    if any(sum(term.powers) == 2 for poly in model.field for term in poly):
        return unproved("This search supports linear and cubic terms; quadratic terms need a full Gram search")
    candidate = _lyapunov_candidate(model)
    if candidate is None:
        return unproved("The fixed-Q linear Lyapunov equation is singular")
    p00, p01, p11 = candidate
    if p00 <= 0 or p00 * p11 - p01 * p01 <= 0:
        return unproved("The fixed-Q linear Lyapunov candidate is not positive definite")
    value = energy(p00, p01, p11)
    negative_lie = scale(Fraction(-1), lie_derivative(model, value))
    quartic = polynomial({powers: coefficient for powers, coefficient in coefficients(negative_lie).items()
                          if sum(powers) == 4})
    nonlinear_sos = _quartic_sos(quartic, numerator_bound, denominator_bound)
    if nonlinear_sos is None:
        return unproved("The bounded rational quartic Gram search found no PSD certificate")
    linear_monomials = ((1, 0), (0, 1))
    lower = Fraction(1)
    for _ in range(bound_steps):
        lower_sos = _ldl_sos(_quadratic_matrix(add(value, scale(-lower, NORM_SQUARED))),
                             linear_monomials)
        if lower_sos is not None:
            break
        lower /= 2
    else:
        return unproved("The bounded norm-lower-bound search was exhausted")
    upper = Fraction(1)
    for _ in range(bound_steps):
        upper_sos = _ldl_sos(_quadratic_matrix(add(scale(upper, NORM_SQUARED),
                                                  scale(Fraction(-1), value))), linear_monomials)
        if upper_sos is not None:
            break
        upper *= 2
    else:
        return unproved("The bounded norm-upper-bound search was exhausted")
    rate = Fraction(1)
    for _ in range(rate_steps):
        decay = add(negative_lie, scale(-rate, value))
        quadratic_sos = _ldl_sos(_quadratic_matrix(decay), linear_monomials)
        if quadratic_sos is not None:
            witness = Witness(p00, p01, p11, lower, upper, rate, lower_sos, upper_sos,
                              quadratic_sos + nonlinear_sos)
            verify_witness(model, witness)
            return SynthesisResult("CANDIDATE", witness,
                                   "Exact rational quadratic energy and three SOS identities; pending Lean admission")
        rate /= 2
    return unproved("The bounded positive decay-rate search was exhausted")
