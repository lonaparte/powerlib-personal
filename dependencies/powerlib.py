#!/usr/bin/env python3
"""Small ATP certificate synthesizer and finite ATD experiment for an RL circuit."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import re
import sys
import tempfile

from common import ROOT, RESULTS, audit, check_lean, demand, digest, run


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError("Use integer values or exact rational strings such as '3/2'")
    text = str(value)
    if len(text) > 100 or not re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", text):
        raise ValueError("Expected an integer or a rational with a positive denominator")
    return Fraction(text)


def read_model(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate model key: {key}")
            result[key] = value
        return result
    data = json.loads(Path(path).read_text(), object_pairs_hook=unique)
    if not isinstance(data, dict) or set(data) != {"resistance", "inductance"}:
        raise ValueError("Expected exactly resistance and inductance")
    resistance, inductance = map(rational, (data["resistance"], data["inductance"]))
    if inductance <= 0:
        raise ValueError("Inductance must be positive")
    return resistance, inductance


def literal(x):
    return f"({x.numerator} / {x.denominator} : ℝ)"


def model_source(name, resistance, inductance):
    return f"def {name} : powerlib.Impedance := ⟨{literal(resistance)}, ⟨{literal(inductance)}, by norm_num⟩⟩\n"


def candidate_source(resistance, inductance, p, rate):
    return "import powerlib\nnoncomputable section\nnamespace Candidate\n" + model_source(
        "model", resistance, inductance) + f'''
def certificate : powerlib.Accepted model where
  p := {literal(p)}
  rate := {literal(rate)}
  p_pos := by norm_num
  rate_pos := by norm_num
  lyapunov_identity := by
    norm_num [model, powerlib.toStateSpace, powerlib.generated.convert, powerlib.reciprocal]
  rate_exact := by
    norm_num [model, powerlib.toStateSpace, powerlib.generated.convert, powerlib.reciprocal]
end Candidate
'''


def admission_source(resistance, inductance, p, rate):
    # Reconstruct the target from the submitted model, independently of the candidate.
    return "namespace Admission\n" + model_source("submittedModel", resistance, inductance) + f'''
def accepted : powerlib.Accepted submittedModel := Candidate.certificate
example : accepted.p = {literal(p)} := by norm_num [accepted, Candidate.certificate]
example : accepted.rate = {literal(rate)} := by norm_num [accepted, Candidate.certificate]
theorem stable : submittedModel.Stable := accepted.stable
theorem dissipation (current : ℝ) :
    2 * accepted.p * current * (powerlib.toStateSpace submittedModel).field current 0 =
      -current ^ 2 := accepted.dissipation current
theorem decay (initial t : ℝ) :
    (powerlib.response submittedModel initial t) ^ 2 =
      initial ^ 2 * Real.exp (-accepted.rate * t) := accepted.decay_bound initial t
end Admission
''' + audit(["Admission.accepted", "Admission.stable", "Admission.dissipation", "Admission.decay"])


def output_dir(kind):
    RESULTS.mkdir(exist_ok=True)
    return Path(tempfile.mkdtemp(prefix=kind + "-", dir=RESULTS))


def atp(path):
    resistance, inductance = read_model(path)
    if resistance <= 0:
        raise ValueError("No strict stability certificate: resistance must be positive")
    p, rate = inductance / (2 * resistance), 2 * resistance / inductance
    directory = output_dir("atp")
    proof = directory / "Certificate.lean"
    proof.write_text(candidate_source(resistance, inductance, p, rate) +
                     admission_source(resistance, inductance, p, rate))
    check_lean(proof)
    report = {
        "status": "ACCEPTED", "model": {"resistance": str(resistance), "inductance": str(inductance)},
        "state_space": {"decay": str(resistance / inductance), "input_gain": str(1 / inductance)},
        "certificate": {"p": str(p), "squared_current_decay_rate": str(rate)},
        "theorem": "Admission.stable", "proof": str(proof.relative_to(ROOT)),
        "proof_sha256": digest(proof), "lean": demand(["lake", "env", "lean", "--version"]).strip(),
    }
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def atd():
    directory = output_dir("atd")
    results = []
    for name, condition, counterexample in [
        ("positive", "0 < m.resistance", None),
        ("nonnegative", "0 ≤ m.resistance", 0),
        ("negative", "m.resistance < 0", 1),
    ]:
        proposition = f"∀ m : powerlib.Impedance, m.Stable ↔ {condition}"
        path = directory / (name + ".lean")
        path.write_text(f'''import powerlib
theorem discovered : {proposition} := by
  intro m
  rw [powerlib.impedance_stable_iff] <;> (constructor <;> intro h <;> linarith)
''' + audit(["discovered"]))
        code, log = run(["lake", "env", "lean", path])
        path.with_suffix(".log").write_text(log)
        status = "PROVED" if code == 0 and "POWERLIB_KERNEL_OK" in log else "UNPROVED"
        if status == "UNPROVED" and counterexample is not None:
            refutation = directory / (name + "_refuted.lean")
            refutation.write_text(f'''import powerlib
theorem refuted : ¬ ({proposition}) := by
  intro h
  have hh := h ⟨{counterexample}, ⟨1, by norm_num⟩⟩
  rw [powerlib.impedance_stable_iff] at hh
  norm_num at hh
''' + audit(["refuted"]))
            check_lean(refutation)
            status = "REFUTED"
        artifact = path if status == "PROVED" else refutation if status == "REFUTED" else path
        results.append({"conjecture": proposition, "status": status,
                        "proof": str(artifact.relative_to(ROOT)), "proof_sha256": digest(artifact)})
    report = {"scope": "Finite search of three resistance sign conditions in the canonical RL family",
              "results": results}
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if [item["status"] for item in results] != ["PROVED", "REFUTED", "REFUTED"]:
        raise RuntimeError("The ATD experiment did not complete; see its report and logs")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("atp", help="Synthesize and verify an RL stability certificate").add_argument("model")
    commands.add_parser("atd", help="Search three sign conditions and verify proofs or counterexamples")
    args = parser.parse_args()
    try:
        report = atp(args.model) if args.command == "atp" else atd()
    except (ValueError, OSError, RuntimeError) as error:
        print(json.dumps({"status": "NOT_ACCEPTED", "reason": str(error)}, indent=2))
        return 1
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
