#!/usr/bin/env python3
"""Derive LCL stability and synthesize exact rational Lyapunov witnesses."""
import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import re
import sys
import tempfile

from common import ROOT, RESULTS, audit, check_lean, check_conversions, demand, digest, proof_provenance, run
from powerlib import rational

KEYS = ("inductance1", "inductance2", "capacitance", "resistance1", "resistance2")
POSITIONS = ((0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2))
IDENTITY = tuple(tuple(Fraction(int(i == j)) for j in range(3)) for i in range(3))
SEMANTIC_THEOREMS = ["Admission.autonomous_globally_exponentially_stable",
                     "Admission.autonomous_globally_asymptotically_stable"]
ADMITTED_THEOREMS = ["Admission." + name for name in (
    "stable", "positive", "dissipation", "small_signal", "lyapunov_stable",
    "globally_asymptotically_stable", "globally_exponentially_stable",
    "equilibrium_exists", "trajectory_exists", "trajectory_unique",
    "trajectory_tendsto", "energy_derivative")] + SEMANTIC_THEOREMS


@dataclass(frozen=True)
class Model:
    l1: Fraction
    l2: Fraction
    c: Fraction
    r1: Fraction
    r2: Fraction

    def __post_init__(self):
        if any(type(value) is not Fraction for value in self.values()):
            raise ValueError("Model parameters must be exact Fraction values")
        if min(self.l1, self.l2, self.c) <= 0:
            raise ValueError("Both inductances and the capacitance must be positive")

    def values(self):
        return (self.l1, self.l2, self.c, self.r1, self.r2)

    def serialized(self):
        return dict(zip(KEYS, map(str, self.values())))


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate key: {key}")
        result[key] = value
    return result


def model_from_data(data):
    if not isinstance(data, dict) or set(data) != set(KEYS):
        raise ValueError("Expected exactly " + ", ".join(KEYS))
    return Model(*(rational(data[key]) for key in KEYS))


def read_model(path):
    return model_from_data(json.loads(Path(path).read_text(), object_pairs_hook=unique_object))


def state_matrix(model):
    l1, l2, c, r1, r2 = model.values()
    z = Fraction(0)
    return ((-r1/l1, -1/l1, z), (1/c, z, -1/c), (z, 1/l2, -r2/l2))


def coefficients(model):
    l1, l2, c, r1, r2 = model.values()
    return (l1*l2*c, c*(r1*l2+r2*l1), l1+l2+c*r1*r2, r1+r2)


def hurwitz_checks(model):
    a3, a2, a1, a0 = coefficients(model)
    return {"a2_positive": a2 > 0, "a1_positive": a1 > 0,
            "a0_positive": a0 > 0, "hurwitz_gap_positive": a2*a1-a3*a0 > 0}


def determinant(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def leading_minors(p):
    return (p[0][0], p[0][0]*p[1][1]-p[0][1]*p[1][0], determinant(p))


def lyapunov_product(a, p):
    return tuple(tuple(sum(a[k][i]*p[k][j]+p[i][k]*a[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


def symmetric(entries):
    p = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for (i, j), value in zip(POSITIONS, entries):
        p[i][j] = p[j][i] = value
    return tuple(map(tuple, p))


def solve_linear(matrix, rhs):
    n = len(rhs)
    rows = [list(row) + [value] for row, value in zip(matrix, rhs)]
    for column in range(n):
        pivot = next((i for i in range(column, n) if rows[i][column]), None)
        if pivot is None:
            raise ValueError("The Lyapunov equation is singular")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [value/scale for value in rows[column]]
        for i in range(n):
            if i != column:
                scale = rows[i][column]
                rows[i] = [x-scale*y for x, y in zip(rows[i], rows[column])]
    return tuple(row[-1] for row in rows)


def verify_witness(model, p):
    if (len(p) != 3 or any(len(row) != 3 for row in p)
            or any(type(value) is not Fraction for row in p for value in row)):
        raise ValueError("P must be a 3-by-3 exact rational matrix")
    if any(p[i][j] != p[j][i] for i in range(3) for j in range(3)):
        raise ValueError("P must be symmetric")
    if any(minor <= 0 for minor in leading_minors(p)):
        raise ValueError("P fails the strict Sylvester positivity checks")
    product = lyapunov_product(state_matrix(model), p)
    if any(product[i][j] != (-1 if i == j else 0) for i in range(3) for j in range(3)):
        raise ValueError("P fails the Lyapunov identity for the submitted model")
    return product


def synthesize_witness(model):
    if not all(hurwitz_checks(model).values()):
        raise ValueError("The derived strict Hurwitz criterion is not satisfied")
    a = state_matrix(model)
    basis = [symmetric(tuple(Fraction(int(i == j)) for i in range(6))) for j in range(6)]
    images = [lyapunov_product(a, p) for p in basis]
    system = [tuple(image[i][j] for image in images) for i, j in POSITIONS]
    rhs = tuple(Fraction(-1 if i == j else 0) for i, j in POSITIONS)
    p = symmetric(solve_linear(system, rhs))
    verify_witness(model, p)
    return p


def matrix_data(matrix):
    return [[str(value) for value in row] for row in matrix]


def derive(model):
    a3, a2, a1, a0 = coefficients(model)
    passive = model.r1 >= 0 and model.r2 >= 0
    return {"maturity": "Note", "kernel_verified": False,
            "scope": "Continuous-time LCL plant without a controller",
            "state_order": ["converter_current", "capacitor_voltage", "grid_current"],
            "model": model.serialized(), "A": matrix_data(state_matrix(model)),
            "coefficients": dict(zip(("a3", "a2", "a1", "a0"), map(str, (a3, a2, a1, a0)))),
            "hurwitz_gap": str(a2*a1-a3*a0), "conditions": hurwitz_checks(model),
            "hurwitz_by_derived_criterion": all(hurwitz_checks(model).values()),
            "passive": passive,
            "passive_resistances_not_both_zero": (model.r1 != 0 or model.r2 != 0) if passive else None}


def literal(value):
    return f"({value.numerator} / {value.denominator} : ℝ)"


def model_source(name, model):
    l1, l2, c, r1, r2 = map(literal, model.values())
    return (f"def {name} : powerlib.LCL.Circuit :=\n"
            f"  ⟨⟨{r1}, ⟨{l1}, by norm_num⟩⟩, ⟨{r2}, ⟨{l2}, by norm_num⟩⟩, ⟨{c}, by norm_num⟩⟩\n")


def proof_source(model, p):
    # Rebuild the target from the submission, independently of synthesis.
    entries = ", ".join(literal(p[i][j]) for i, j in POSITIONS)
    unfold = ("model, powerlib.LCL.toStateSpace, powerlib.generated.convertLCL, "
              "powerlib.reciprocal, powerlib.LCL.Circuit.a3, powerlib.LCL.Circuit.a2, "
              "powerlib.LCL.Circuit.a1, powerlib.LCL.Circuit.a0, "
              "powerlib.LCL.SymmetricMatrix.minor2, powerlib.LCL.SymmetricMatrix.det")
    fields = ("p11_pos", "minor2_pos", "det_pos", "a2_pos", "a1_pos", "a0_pos", "gap_pos",
              "eq11", "eq12", "eq13", "eq22", "eq23", "eq33")
    checks = "".join(f"  {field} := by norm_num [{unfold}]\n" for field in fields)
    return ("import powerlib\nnoncomputable section\nnamespace Candidate\n" +
            model_source("model", model) +
            f"def certificate : powerlib.LCL.Accepted model where\n  p := ⟨{entries}⟩\n" +
            checks + "end Candidate\nnamespace Admission\n" +
            model_source("submittedModel", model) + '''
def accepted : powerlib.LCL.Accepted submittedModel := Candidate.certificate
@[powerlib_domain] theorem stable : (powerlib.LCL.toStateSpace submittedModel).Stable := accepted.stable
@[powerlib_domain] theorem autonomous_globally_exponentially_stable :
    powerlib.Dynamics.GloballyExponentiallyStable submittedModel.autonomousField 0 :=
  accepted.autonomousGloballyExponentiallyStable
@[powerlib_domain] theorem autonomous_globally_asymptotically_stable :
    powerlib.Dynamics.GloballyAsymptoticallyStable submittedModel.autonomousField 0 :=
  accepted.autonomousGloballyAsymptoticallyStable
@[powerlib_domain] theorem positive (x y z : ℝ) (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < powerlib.LCL.energy accepted.p x y z := accepted.positive x y z hn
@[powerlib_domain] theorem dissipation (x y z : ℝ) :
    let f := (powerlib.LCL.toStateSpace submittedModel).field x y z 0 0
    powerlib.LCL.energyDerivative accepted.p x y z f.1 f.2.1 f.2.2 = -(x^2+y^2+z^2) :=
  accepted.dissipation x y z
@[powerlib_domain] theorem small_signal :
    powerlib.LCL.AsymptoticallyStable submittedModel 0 0 0 :=
  accepted.asymptoticallyStable (powerlib.LCL.zero_equilibrium submittedModel)
@[powerlib_domain] theorem lyapunov_stable (u vg : ℝ) (e : powerlib.LCL.State)
    (he : powerlib.LCL.IsEquilibrium submittedModel u vg e) :
    powerlib.LCL.LyapunovStable submittedModel u vg e := accepted.lyapunovStable he
@[powerlib_domain] theorem globally_asymptotically_stable (u vg : ℝ) (e : powerlib.LCL.State)
    (he : powerlib.LCL.IsEquilibrium submittedModel u vg e) :
    powerlib.LCL.GloballyAsymptoticallyStable submittedModel u vg e :=
  accepted.globallyAsymptoticallyStable he
@[powerlib_domain] theorem globally_exponentially_stable (u vg : ℝ) (e : powerlib.LCL.State)
    (he : powerlib.LCL.IsEquilibrium submittedModel u vg e) :
    powerlib.LCL.GloballyExponentiallyStable submittedModel u vg e :=
  accepted.globallyExponentiallyStable he
@[powerlib_domain] theorem equilibrium_exists (u vg : ℝ) :
    powerlib.LCL.IsEquilibrium submittedModel u vg (powerlib.LCL.equilibrium submittedModel u vg) :=
  accepted.equilibrium_exists u vg
@[powerlib_domain] theorem trajectory_exists (u vg : ℝ) (initial : powerlib.LCL.State) :
    ∃ x, powerlib.LCL.IsTrajectory submittedModel u vg x ∧ x 0 = initial :=
  accepted.trajectory_exists u vg initial
@[powerlib_domain] theorem trajectory_unique (u vg : ℝ) (e : powerlib.LCL.State)
    (x y : ℝ → powerlib.LCL.State) (he : powerlib.LCL.IsEquilibrium submittedModel u vg e)
    (hx : powerlib.LCL.IsTrajectory submittedModel u vg x)
    (hy : powerlib.LCL.IsTrajectory submittedModel u vg y) (h0 : x 0 = y 0) :
    Set.EqOn x y (Set.Ici 0) := powerlib.LCL.trajectory_unique he hx hy h0
@[powerlib_domain] theorem trajectory_tendsto (u vg : ℝ) (e : powerlib.LCL.State)
    (x : ℝ → powerlib.LCL.State) (he : powerlib.LCL.IsEquilibrium submittedModel u vg e)
    (hx : powerlib.LCL.IsTrajectory submittedModel u vg x) :
    Filter.Tendsto x Filter.atTop (nhds e) := accepted.trajectory_tendsto he hx
@[powerlib_domain] theorem energy_derivative (u vg : ℝ) (e : powerlib.LCL.State)
    (x : ℝ → powerlib.LCL.State) (he : powerlib.LCL.IsEquilibrium submittedModel u vg e)
    (hx : powerlib.LCL.IsTrajectory submittedModel u vg x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => powerlib.LCL.quadraticEnergy accepted.p (x s - e))
      (-powerlib.LCL.squaredSize (x t - e)) (Set.Ici 0) t := accepted.energy_derivative he hx ht
end Admission
''' + audit(["Admission.accepted", *ADMITTED_THEOREMS], theorem_roots=ADMITTED_THEOREMS))


def verify_kernel(proof):
    check_lean(proof)
    version = demand(["lake", "env", "lean", "--version"]).strip()
    if "version 4.19.0" not in version:
        raise RuntimeError("Expected pinned Lean 4.19.0")
    return version


def certificate_report(model, p):
    verify_witness(model, p)
    return {"schema": "powerlib.lcl.lyapunov.v1", "model": model.serialized(),
            "state_order": ["converter_current", "capacitor_voltage", "grid_current"],
            "P": matrix_data(p), "Q": matrix_data(IDENTITY),
            "leading_minors": list(map(str, leading_minors(p))),
            "status": "UNVERIFIED", "kernel_verified": False,
            "maturity": "Unverified proof artifact"}


def synthesize(model, kernel=False, directory=None):
    p = synthesize_witness(model)
    report = certificate_report(model, p)
    RESULTS.mkdir(parents=True, exist_ok=True)
    directory = directory or Path(tempfile.mkdtemp(prefix="lcl-", dir=RESULTS))
    proof = directory / "Certificate.lean"
    proof.write_text(proof_source(model, p))
    report["proof"] = str(proof)
    report["proof_sha256"] = digest(proof)
    if kernel:
        check_conversions()
        report["lean"] = verify_kernel(proof)
        report["provenance"] = proof_provenance(proof)
        report["kernel_verified"] = True
        report["status"] = "ACCEPTED"
        report["maturity"] = "S-level"
        report["witness_origin"] = "Automatic exact Lyapunov synthesis from witness-free model"
        report["theorems"] = list(ADMITTED_THEOREMS)
        report["semantic_theorems"] = list(SEMANTIC_THEOREMS)
    (directory / "certificate.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def certificate_fraction(value):
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError("Certificate entries must be integers or exact rational strings")
    text = str(value)
    if len(text) > 10000 or not re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", text):
        raise ValueError("Invalid rational certificate entry")
    return Fraction(text)


def certificate_matrix(rows):
    if (not isinstance(rows, list) or len(rows) != 3
            or any(not isinstance(row, list) or len(row) != 3 for row in rows)):
        raise ValueError("Certificate matrices must be 3-by-3")
    return tuple(tuple(certificate_fraction(value) for value in row) for row in rows)


def verify_saved(model, path, kernel=False):
    data = json.loads(Path(path).read_text(), object_pairs_hook=unique_object)
    if not isinstance(data, dict) or data.get("schema") != "powerlib.lcl.lyapunov.v1":
        raise ValueError("Unsupported certificate schema")
    if model_from_data(data.get("model")) != model:
        raise ValueError("Certificate describes a different submitted model")
    if data.get("state_order") != ["converter_current", "capacitor_voltage", "grid_current"]:
        raise ValueError("Certificate uses the wrong state order")
    if certificate_matrix(data.get("Q")) != IDENTITY:
        raise ValueError("This certificate schema requires Q = I")
    p = certificate_matrix(data.get("P"))
    report = certificate_report(model, p)
    # Recompute all checks and regenerate proof; trust no claimed status or proof path.
    if kernel:
        check_conversions()
        RESULTS.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="lcl-verify-", dir=RESULTS))
        proof = directory / "Certificate.lean"
        proof.write_text(proof_source(model, p))
        report["lean"] = verify_kernel(proof)
        report["proof"] = str(proof)
        report["provenance"] = proof_provenance(proof)
        report["kernel_verified"] = True
        report["status"] = "ACCEPTED"
        report["maturity"] = "Certificate verification"
        report["witness_origin"] = "Submitted certificate"
        report["theorems"] = list(ADMITTED_THEOREMS)
        report["semantic_theorems"] = list(SEMANTIC_THEOREMS)
        (directory / "certificate.json").write_text(json.dumps(report, indent=2)+"\n")
    return report


def atp(path):
    RESULTS.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="lcl-", dir=RESULTS))
    submitted = directory / "submitted.json"
    submitted.write_bytes(Path(path).read_bytes())
    report = synthesize(read_model(submitted), kernel=True, directory=directory)
    report["submitted_model_sha256"] = digest(submitted)
    report["conversion"] = report["provenance"]["conversions"]["lcl"]
    Path(report["proof"]).with_name("certificate.json").write_text(json.dumps(report, indent=2)+"\n")
    return report


def atd():
    bridge = check_conversions()["lcl"]
    RESULTS.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="lcl-atd-", dir=RESULTS))
    results = []
    for name, condition, counterexample in [
        ("not_both_zero", "m.Damped", None),
        ("both_positive", "0 < m.first.resistance ∧ 0 < m.second.resistance", (1, 0)),
        ("nonnegative_sum", "0 ≤ m.first.resistance + m.second.resistance", (0, 0)),
    ]:
        proposition = ("∀ m : powerlib.LCL.Circuit, m.Passive → "
                       f"(powerlib.LCL.AsymptoticallyStable m 0 0 0 ↔ {condition})")
        proof = directory / (name+".lean")
        proof.write_text(f'''import powerlib
@[powerlib_domain] theorem discovered : {proposition} := by
  intro m hp
  rw [powerlib.LCL.passive_asymptoticallyStable_iff m hp (powerlib.LCL.zero_equilibrium m)] <;>
    first | rfl | tauto
''' + audit(["discovered"]))
        try:
            check_lean(proof)
            status = "PROVED"
        except RuntimeError:
            status = "UNPROVED"
        if status == "UNPROVED" and counterexample is not None:
            example = Model(Fraction(1), Fraction(1), Fraction(1), *map(Fraction, counterexample))
            proof = directory / (name+"_refuted.lean")
            proof.write_text("import powerlib\nnoncomputable section\n" + model_source("model", example) + f'''
@[powerlib_domain] theorem refuted : ¬ ({proposition}) := by
  intro h
  have hp : model.Passive := by norm_num [model, powerlib.LCL.Circuit.Passive]
  have hh := h model hp
  rw [powerlib.LCL.passive_asymptoticallyStable_iff model hp (powerlib.LCL.zero_equilibrium model)] at hh
  norm_num [model, powerlib.LCL.Circuit.Damped] at hh
''' + audit(["refuted"]))
            check_lean(proof)
            status = "REFUTED"
        results.append({"conjecture": proposition, "status": status,
                        "proof": str(proof), "proof_sha256": digest(proof),
                        "theorem": "discovered" if status == "PROVED" else "refuted" if status == "REFUTED" else None,
                        "provenance": proof_provenance(proof) if status != "UNPROVED" else None})
    report = {"scope": "Finite search of three conditions in the passive canonical LCL family",
              "maturity": "Fixed-candidate verification prototype",
              "conjecture_generation": "Three manually enumerated conditions",
              "conversion": bridge, "results": results}
    (directory / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    if [item["status"] for item in results] != ["PROVED", "REFUTED", "REFUTED"]:
        details = "; ".join(f"{item['status']}: {item['proof']}" for item in results)
        raise RuntimeError("The LCL fixed-candidate experiment did not complete: " + details)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("derive").add_argument("model")
    synthesis = commands.add_parser("synthesize")
    synthesis.add_argument("model")
    synthesis.add_argument("--verify", action="store_true", help="Kernel-check the certificate and semantic theorems")
    verification = commands.add_parser("verify")
    verification.add_argument("model")
    verification.add_argument("certificate")
    verification.add_argument("--verify", action="store_true", help="Regenerate and kernel-check the proof")
    args = parser.parse_args()
    try:
        model = read_model(args.model)
        if args.command == "derive":
            report = derive(model)
        elif args.command == "synthesize":
            report = synthesize(model, args.verify)
        else:
            report = verify_saved(model, args.certificate, args.verify)
        print(json.dumps(report, indent=2))
        return 0
    except (ValueError, OSError, RuntimeError) as error:
        print(json.dumps({"status": "NOT_ACCEPTED", "reason": str(error)}, indent=2))
        return 1


if __name__ == "__main__":
    sys.exit(main())
