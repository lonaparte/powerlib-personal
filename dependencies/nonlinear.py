#!/usr/bin/env python3
"""Witness-free polynomial stability synthesis followed by Lean kernel checking."""
import json
from fractions import Fraction
from pathlib import Path
import re
import tempfile

from common import (RESULTS, audit, check_conversions, check_lean, digest,
                    proof_provenance)
from nonlinear_synthesis import (Model, Term, WeightedSquare, Witness,
                                 read_model, synthesize)

NAMESPACE = "powerlib.Dynamics.Polynomial2"
SEMANTIC_THEOREMS = ["Admission." + name for name in (
    "forward_complete", "globally_exponentially_stable",
    "globally_asymptotically_stable", "all_trajectory_decay")]


def literal(value):
    if (type(value) is not Fraction or type(value.numerator) is not int
            or type(value.denominator) is not int or value.denominator <= 0):
        raise ValueError("Generated certificate values must be exact Fraction data")
    return f"({value.numerator} / {value.denominator} : ℚ)"


def polynomial_source(poly, *, max_degree=3):
    if type(poly) is not tuple or len(poly) > 128:
        raise ValueError("Generated polynomials must be bounded term tuples")
    for term in poly:
        if (type(term) is not Term or type(term.powers) is not tuple or len(term.powers) != 2
                or any(type(power) is not int or power < 0 for power in term.powers)
                or sum(term.powers) > max_degree):
            raise ValueError("Generated monomials require two bounded integer powers")
    return "[" + ", ".join(
        f"⟨{literal(term.coefficient)}, ({term.powers[0]}, {term.powers[1]})⟩"
        for term in poly) + "]"


def squares_source(squares):
    if (type(squares) is not tuple or len(squares) > 32
            or any(type(square) is not WeightedSquare for square in squares)):
        raise ValueError("Generated SOS data must be bounded WeightedSquare tuples")
    return "[" + ", ".join(
        f"⟨{literal(square.weight)}, {polynomial_source(square.poly, max_degree=2)}⟩"
        for square in squares) + "]"


def model_source(name, model):
    if type(model) is not Model:
        raise ValueError("The proposed field must be a polynomial Model")
    return (f"def {name} : {NAMESPACE}.Model :=\n"
            f"  ⟨{polynomial_source(model.field0)}, {polynomial_source(model.field1)}⟩\n")


def submitted_model_source(name, path):
    # Compile and validate original JSON independently of the searcher's
    # polynomial representation and normalizer. The sorting is only the wire
    # convention for the model-indexed type, not a solver-supplied field.
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("Duplicate submitted JSON key")
            result[key] = value
        return result
    data = json.loads(Path(path).read_text(), object_pairs_hook=unique)
    if (type(data) is not dict or set(data) != {"schema", "field"}
            or data["schema"] != "powerlib.polynomial2.v1"
            or type(data["field"]) is not list or len(data["field"]) != 2):
        raise ValueError("The original submission must describe exactly two polynomial coordinates")
    coordinates = []
    for terms in data["field"]:
        if type(terms) is not list or len(terms) > 128:
            raise ValueError("Submitted coordinates must be bounded monomial lists")
        seen = set()
        for term in terms:
            if type(term) is not dict or set(term) != {"coefficient", "powers"}:
                raise ValueError("Invalid submitted monomial")
            powers = term["powers"]
            if (type(powers) is not list or len(powers) != 2
                    or any(type(power) is not int or power < 0 for power in powers)
                    or sum(powers) > 3 or tuple(powers) in seen):
                raise ValueError("Invalid or duplicated submitted monomial powers")
            seen.add(tuple(powers))
            coefficient = term["coefficient"]
            if (type(coefficient) not in (str, int) or len(str(coefficient)) > 100
                    or not re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", str(coefficient))):
                raise ValueError("Submitted coefficients must be exact rational data")
        terms = sorted(terms, key=lambda t: (sum(t["powers"]), tuple(t["powers"])))
        values = []
        for term in terms:
            coefficient = Fraction(term["coefficient"])
            if coefficient:
                a, b = term["powers"]
                values.append(f"⟨{literal(coefficient)}, ({a}, {b})⟩")
        coordinates.append("[" + ", ".join(values) + "]")
    return (f"def {name} : {NAMESPACE}.Model :=\n"
            f"  ⟨{coordinates[0]}, {coordinates[1]}⟩\n")


def candidate_source(model, witness):
    # Treat the synthesizer as untrusted: all signs and polynomial identities
    # are obligations in the generated Lean term, including incorrect proposals.
    if type(witness) is not Witness:
        raise ValueError("The proposed certificate must contain Witness data")
    scalar_fields = ("p00", "p01", "p11", "lower", "upper", "rate")
    sos_fields = ("lower_sos", "upper_sos", "decay_sos")
    fields = "".join(f"  {name} := {literal(getattr(witness, name))}\n"
                     for name in scalar_fields)
    fields += "".join(f"  {name} := {squares_source(getattr(witness, name))}\n"
                      for name in sos_fields)
    fields += "".join(f"  {name}_pos := by norm_num\n"
                      for name in ("lower", "upper", "rate"))
    fields += "".join(f"  {name}_nonneg := by norm_num [List.Forall]\n"
                      for name in ("lower", "upper", "decay"))
    fields += ("  field_zero := by\n"
               "    ext j\n"
               "    fin_cases j <;> norm_num [model, Model.field, eval]\n")
    fields += "".join(
        f"  {name}_identity := by\n"
        "    intro x y\n"
        "    norm_num [model, quadratic, lie, eval, sosEval]\n"
        "    <;> ring\n"
        for name in ("lower", "upper", "decay"))
    return ("import powerlib\nnoncomputable section\n"
            f"open {NAMESPACE}\nnamespace Candidate\n" +
            model_source("model", model) +
            f"def certificate : {NAMESPACE}.Accepted model where\n" +
            fields + "end Candidate\n")


def admission_source(submitted_model, *, original_path=None):
    # This target is rebuilt from the original field, separately from the
    # proposal. A certificate for a different polynomial field fails to typecheck.
    target_source = (submitted_model_source("submittedModel", original_path)
                     if original_path is not None else model_source("submittedModel", submitted_model))
    return ("namespace Admission\n" + target_source +
            f"def accepted : {NAMESPACE}.Accepted submittedModel := Candidate.certificate\n" + '''
@[powerlib_domain] theorem forward_complete :
    powerlib.Dynamics.ForwardComplete submittedModel.field :=
  accepted.quadraticDecayCertificate.forwardComplete submittedModel.field_smooth
@[powerlib_domain] theorem globally_exponentially_stable :
    powerlib.Dynamics.GloballyExponentiallyStable submittedModel.field 0 :=
  accepted.globallyExponentiallyStable
@[powerlib_domain] theorem globally_asymptotically_stable :
    powerlib.Dynamics.GloballyAsymptoticallyStable submittedModel.field 0 :=
  accepted.quadraticDecayCertificate.globallyAsymptoticallyStable
    (by norm_num) submittedModel.field_smooth
@[powerlib_domain] theorem all_trajectory_decay
    {φ : ℝ → powerlib.Dynamics.State 2} {a b t : ℝ}
    (hφ : powerlib.Dynamics.IsTrajectoryOn φ submittedModel.field a b)
    (ht : t ∈ Set.Icc a b) :
    ‖φ t‖ ≤ Real.sqrt ((accepted.upper : ℝ) / (accepted.lower : ℝ)) *
      Real.exp (-((accepted.rate : ℝ) / 2 * (t - a))) * ‖φ a‖ := by
  simpa only [sub_zero] using accepted.quadraticDecayCertificate.norm_bound hφ ht
end Admission
''' + audit(["Candidate.certificate", "Admission.accepted", *SEMANTIC_THEOREMS],
            theorem_roots=SEMANTIC_THEOREMS))


def proof_source(model, witness):
    return candidate_source(model, witness) + admission_source(model)


def atp(path):
    RESULTS.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="nonlinear-", dir=RESULTS))
    submitted = directory / "submitted.json"
    submitted.write_bytes(Path(path).read_bytes())
    submitted_hash = digest(submitted)
    proposal_model = read_model(submitted)
    result = synthesize(proposal_model)
    report = {"status": "UNPROVED", "kernel_verified": False,
              "submitted_model_sha256": submitted_hash,
              "model": proposal_model.serialized(),
              "state_order": ["x0", "x1"], "time_domain": "continuous",
              "equilibrium": ["0", "0"], "inputs": "autonomous",
              "method": "Exact rational fixed-Q=I linear Lyapunov equation and bounded SOS Gram search",
              "search_scope": "Two coordinates, linear and cubic terms, quadratic energy",
              "search_limits": {"gram_numerator_bound": 16, "gram_denominator_bound": 12,
                                "norm_bound_steps": 32, "rate_steps": 32},
              "synthesizer_sha256": digest(Path(__file__).with_name("nonlinear_synthesis.py"))}
    if result.witness is None:
        report["reason"] = result.reason
    else:
        check_conversions()
        proof = directory / "Certificate.lean"
        proof.write_text(candidate_source(proposal_model, result.witness) +
                         admission_source(read_model(submitted), original_path=submitted))
        check_lean(proof)
        w = result.witness
        report.update({"status": "ACCEPTED", "kernel_verified": True,
                       "maturity": "S-level",
                       "witness_origin": "Automatic exact synthesis from witness-free vector field",
                       "certificate": w.serialized(),
                       "proof": str(proof), "proof_sha256": digest(proof),
                       "theorems": list(SEMANTIC_THEOREMS),
                       "semantic_theorems": list(SEMANTIC_THEOREMS),
                       "semantics": "Global forward existence; all trajectories and all initial amplitudes",
                       "provenance": proof_provenance(proof)})
    if digest(submitted) != submitted_hash:
        raise RuntimeError("Original polynomial submission changed during admission")
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report
