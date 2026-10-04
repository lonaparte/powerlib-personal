"""Exact Lyapunov synthesis for arbitrary finite rational autonomous LTI models.

Input contains only A, in the coordinate order x[0], ..., x[n-1]. This is the
complete submitted continuous-time vector field, with zero external input.
The solver is untrusted. Only independently reconstructed Lean admission can
produce ACCEPTED. There is no numerical eigenvalue test or floating arithmetic.
"""
from fractions import Fraction as F
import json
import re
from pathlib import Path
import tempfile

from common import RESULTS, audit, check_lean, demand, digest, proof_provenance
from powerlib import literal


def rational(value):
    if type(value) not in (str, int) or not re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", str(value)):
        raise ValueError("Use exact integers or rational strings, not floats or proof text")
    return F(value)


class Unproved(ValueError):
    """Synthesis found no certificate; this is not a formal refutation."""


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate key: {key}")
        result[key] = value
    return result


def matrix_from_data(data, n=None):
    if not isinstance(data, list) or not data:
        raise ValueError("Expected a nonempty square matrix")
    if n is None:
        n = len(data)
    if len(data) != n or any(not isinstance(row, list) or len(row) != n for row in data):
        raise ValueError("Expected a square matrix of the submitted dimension")
    return tuple(tuple(rational(value) for value in row) for row in data)


def model_from_data(data):
    if not isinstance(data, dict) or set(data) != {"A"}:
        raise ValueError("An LTI model contains exactly A; no supplied witness")
    return matrix_from_data(data["A"])


def read_model(path):
    return model_from_data(json.loads(Path(path).read_text(), object_pairs_hook=unique_object))


def matrix_data(a):
    return [[str(value) for value in row] for row in a]


def solve_linear(a, b):
    n = len(b)
    rows = [list(row) + [value] for row, value in zip(a, b)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j]), None)
        if pivot is None:
            raise Unproved("Singular Lyapunov operator; no strict certificate synthesized")
        rows[j], rows[pivot] = rows[pivot], rows[j]
        scale = rows[j][j]
        rows[j] = [x / scale for x in rows[j]]
        for i in range(n):
            if i != j:
                scale = rows[i][j]
                rows[i] = [x - scale*y for x, y in zip(rows[i], rows[j])]
    return tuple(row[-1] for row in rows)


def lyapunov_product(a, p):
    n = len(a)
    return tuple(tuple(sum((a[k][i]*p[k][j] + p[i][k]*a[k][j] for k in range(n)), F(0))
                       for j in range(n)) for i in range(n))


def ldl(p):
    """Exact unit-lower L and strictly positive D, or an unproved result."""
    n = len(p)
    if any(p[i][j] != p[j][i] for i in range(n) for j in range(n)):
        raise Unproved("Nonsymmetric matrix")
    l = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    d = []
    for j in range(n):
        pivot = p[j][j] - sum((l[j][k]**2*d[k] for k in range(j)), F(0))
        if pivot <= 0:
            raise Unproved("No positive definite Lyapunov witness")
        d.append(pivot)
        for i in range(j+1, n):
            l[i][j] = (p[i][j] - sum((l[i][k]*l[j][k]*d[k] for k in range(j)), F(0))) / pivot
    return tuple(map(tuple, l)), tuple(d)


def shift(p, diagonal, sign=1):
    return tuple(tuple(sign*p[i][j] + (diagonal if i == j else 0)
                       for j in range(len(p))) for i in range(len(p)))


def synthesize(a):
    n = len(a)
    positions = [(i, j) for i in range(n) for j in range(i, n)]
    basis = []
    for i, j in positions:
        e = [[F(0) for _ in range(n)] for _ in range(n)]
        e[i][j] = e[j][i] = F(1)
        basis.append(lyapunov_product(a, e))
    equations = [[image[i][j] for image in basis] for i, j in positions]
    values = solve_linear(equations, [F(-int(i == j)) for i, j in positions])
    p = [[F(0) for _ in range(n)] for _ in range(n)]
    for (i, j), v in zip(positions, values):
        p[i][j] = p[j][i] = v
    p = tuple(map(tuple, p))
    ldl(p)
    lower = F(1)
    while True:
        try:
            lower_l, lower_d = ldl(shift(p, -lower))
            break
        except Unproved:
            lower /= 2
    upper = F(1) + sum((abs(v) for row in p for v in row), F(0))
    upper_l, upper_d = ldl(shift(p, upper, -1))
    return {"schema": "powerlib.lti.lyapunov.v1", "model": {"A": matrix_data(a)},
            "P": matrix_data(p), "lower": str(lower), "upper": str(upper),
            "lower_L": matrix_data(lower_l), "lower_D": list(map(str, lower_d)),
            "upper_L": matrix_data(upper_l), "upper_D": list(map(str, upper_d))}


def matrix_literal(a):
    return "![" + ", ".join("![" + ", ".join(map(literal, row)) + "]" for row in a) + "]"


def model_source(name, a):
    return f"def {name} : powerlib.LTI.Model {len(a)} := ⟨{matrix_literal(a)}⟩\n"


def sos(l, d):
    n = len(d)
    return " + ".join(
        f"{literal(d[k])} * (" + " + ".join(f"{literal(l[i][k])} * x {i}"
         for i in range(n) if l[i][k]) + ") ^ 2" for k in range(n))


def candidate_source(certificate):
    expected = {"schema", "model", "P", "lower", "upper", "lower_L", "lower_D", "upper_L", "upper_D"}
    if not isinstance(certificate, dict) or set(certificate) != expected:
        raise ValueError("Unexpected certificate fields")
    if certificate["schema"] != "powerlib.lti.lyapunov.v1":
        raise ValueError("Unsupported certificate schema")
    a = model_from_data(certificate["model"])
    n = len(a)
    p = matrix_from_data(certificate["P"], n)
    lower, upper = rational(certificate["lower"]), rational(certificate["upper"])
    factors = []
    for prefix in ("lower", "upper"):
        l = matrix_from_data(certificate[prefix + "_L"], n)
        data = certificate[prefix + "_D"]
        if not isinstance(data, list) or len(data) != n:
            raise ValueError("Wrong diagonal dimension")
        d = tuple(map(rational, data))
        factors.append(sos(l, d))
    simplify = "powerlib.LTI.energy, powerlib.LTI.sqNorm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ"
    return ("import powerlib\nset_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\n"
            "noncomputable section\nnamespace Candidate\n" + model_source("model", a) + f'''
def certificate : powerlib.LTI.Accepted model where
  P := {matrix_literal(p)}
  lower := {literal(lower)}
  upper := {literal(upper)}
  lower_pos := by norm_num
  upper_pos := by norm_num
  symmetric := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply]
  lower_bound := by
    intro x
    have hs : 0 ≤ {factors[0]} := by positivity
    calc
      _ ≤ _ + ({factors[0]}) := le_add_of_nonneg_right hs
      _ = _ := by norm_num [{simplify}]; ring1!
  upper_bound := by
    intro x
    have hs : 0 ≤ {factors[1]} := by positivity
    calc
      _ ≤ _ + ({factors[1]}) := le_add_of_nonneg_right hs
      _ = _ := by norm_num [{simplify}]; ring1!
  lyapunov := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [model, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
end Candidate
''')


def admission_source(a):
    # Never reconstruct this target from certificate data.
    return ("namespace Admission\n" + model_source("submittedModel", a) + '''
def accepted : powerlib.LTI.Accepted submittedModel := Candidate.certificate
@[powerlib_domain] theorem exponentially_stable :
    powerlib.LTI.ExponentiallyStable submittedModel := accepted.exponentially_stable
@[powerlib_domain] theorem decay (x : ℝ → powerlib.LTI.State _) 
    (hx : powerlib.LTI.IsTrajectory submittedModel x) (t : ℝ) (ht : 0 ≤ t) :
    powerlib.LTI.sqNorm (x t) ≤ (accepted.upper / accepted.lower) *
      Real.exp (-(t / accepted.upper)) * powerlib.LTI.sqNorm (x 0) :=
  accepted.decay_bound hx t ht
@[powerlib_domain] theorem exists_solution (initial : powerlib.LTI.State _) :
    ∃ x, powerlib.LTI.IsTrajectory submittedModel x ∧ x 0 = initial :=
  powerlib.LTI.trajectory_exists submittedModel initial
@[powerlib_domain] theorem norm_decay (x : ℝ → powerlib.LTI.State _)
    (hx : powerlib.LTI.IsTrajectory submittedModel x) (t : ℝ) (ht : 0 ≤ t) :
    ‖powerlib.LTI.euclidean (x t)‖ ≤ Real.sqrt (accepted.upper / accepted.lower) *
      Real.exp (-(t / accepted.upper) / 2) * ‖powerlib.LTI.euclidean (x 0)‖ :=
  accepted.norm_bound hx t ht
@[powerlib_domain] theorem unique_solution (x : ℝ → powerlib.LTI.State _)
    (hx : powerlib.LTI.IsTrajectory submittedModel x) (t : ℝ) (ht : 0 ≤ t) :
    x t = powerlib.LTI.response submittedModel (x 0) t := accepted.response_unique hx t ht
@[powerlib_domain] theorem converges (x : ℝ → powerlib.LTI.State _)
    (hx : powerlib.LTI.IsTrajectory submittedModel x) :
    Filter.Tendsto (fun t => powerlib.LTI.sqNorm (x t)) Filter.atTop (nhds 0) :=
  accepted.sqNorm_tendsto_zero hx
end Admission
''' + audit(["Admission.accepted", "Admission.exponentially_stable", "Admission.decay",
             "Admission.exists_solution", "Admission.norm_decay", "Admission.unique_solution",
             "Admission.converges"]))


def admit(submission_path, certificate):
    import lti_bridge
    bridge = lti_bridge.rebuild()
    demand(["lake", "build"], timeout=1800)
    a = read_model(submission_path)
    RESULTS.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="lti-", dir=RESULTS))
    proof = directory / "Certificate.lean"
    proof.write_text(candidate_source(certificate) + admission_source(a))
    (directory / "certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
    # Both semantic theorem and transitive axiom audit are mandatory.
    check_lean(proof)
    report = {"status": "ACCEPTED", "kernel_verified": True,
              "maturity": "Lean theorem",
              "witness_origin": "Supplied certificate",
              "scope": "Finite-dimensional continuous-time autonomous LTI; submitted coordinates x[0..n-1]",
              "dimension": len(a), "model": {"A": matrix_data(a)},
              "squared_norm_rate": str(1 / rational(certificate["upper"])),
              "squared_norm_gain": str(rational(certificate["upper"]) / rational(certificate["lower"])),
              "norm_rate": str(1 / (2 * rational(certificate["upper"]))),
              "theorems": ["Admission.exponentially_stable", "Admission.decay", "Admission.exists_solution",
                           "Admission.norm_decay", "Admission.unique_solution", "Admission.converges"],
              "proof": str(proof), "submitted_model_sha256": digest(submission_path),
              "certificate_sha256": digest(directory / "certificate.json"),
              "agda_bridge": bridge, "provenance": proof_provenance(proof)}
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def atp(path):
    try:
        certificate = synthesize(read_model(path))
    except Unproved as error:
        return {"status": "UNPROVED", "kernel_verified": False, "reason": str(error)}
    report = admit(path, certificate)
    report.update(maturity="S-level", witness_origin="Automatic exact synthesis from witness-free input")
    (Path(report["proof"]).parent / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report
