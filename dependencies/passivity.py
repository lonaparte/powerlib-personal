#!/usr/bin/env python3
"""Synthesize and independently admit physical LCL storage certificates."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
import tempfile

from common import (DEPENDENCIES, RESULTS, audit, check_conversions, check_lean, demand, digest,
                    proof_provenance)
from lcl import (Model, POSITIONS, certificate_matrix, literal, matrix_data,
                 model_from_data, model_source, read_model, unique_object)

SCHEMA = "powerlib.lcl.passive-storage.v1"
STATE_ORDER = ["converter_current", "capacitor_voltage", "grid_current"]
ADMITTED_THEOREMS = ["Admission." + name for name in (
    "lyapunov_stable", "zero_input_stable", "trajectory_exists",
    "zero_input_trajectory_exists", "trajectory_unique", "integral_passivity",
    "zero_input_energy_nonincreasing", "passive_with_storage")]


def physical_weights(model):
    """Find the exact storage witness directly from the original components."""
    z = Fraction(0)
    return ((model.l1, z, z), (z, model.c, z), (z, z, model.l2))


def verify_witness(model, p):
    if model.r1 < 0 or model.r2 < 0:
        raise ValueError("Passive storage requires both resistances to be nonnegative")
    if (len(p) != 3 or any(len(row) != 3 for row in p)
            or any(type(value) is not Fraction for row in p for value in row)):
        raise ValueError("P must be a 3-by-3 exact rational matrix")
    if p != physical_weights(model):
        raise ValueError("P is not the physical storage matrix for the submitted model")
    return p


def synthesize_witness(model):
    return verify_witness(model, physical_weights(model))


def proof_source(model, p, *, candidate_model=None):
    """Reconstruct the admission target independently of the untrusted proposal."""
    proposed_model = model if candidate_model is None else candidate_model
    entries = ", ".join(literal(p[i][j]) for i, j in POSITIONS)
    return ("import powerlib\nnoncomputable section\nopen MeasureTheory\nnamespace Candidate\n" +
            model_source("model", proposed_model) +
            f"def certificate : powerlib.LCL.StorageAccepted model where\n"
            f"  p := ⟨{entries}⟩\n" +
            "  weights_exact := by norm_num [model, powerlib.LCL.physicalWeights]\n"
            "  passive := by norm_num [model, powerlib.LCL.Circuit.Passive]\n"
            "end Candidate\nnamespace Admission\n" +
            model_source("submittedModel", model) + '''
def accepted : powerlib.LCL.StorageAccepted submittedModel := Candidate.certificate
def portStorage : powerlib.Passivity.QuadraticStorage (powerlib.LCL.portSystem submittedModel) :=
  accepted.portStorage
@[powerlib_domain] theorem passive_with_storage :
    powerlib.Passivity.PassiveWithStorage (powerlib.LCL.portSystem submittedModel)
      (powerlib.LCL.portEnergy submittedModel) := accepted.passiveWithStorage
@[powerlib_domain] theorem lyapunov_stable (u vg : ℝ) (e : powerlib.LCL.State)
    (he : powerlib.LCL.IsEquilibrium submittedModel u vg e) :
    powerlib.LCL.LyapunovStable submittedModel u vg e := accepted.lyapunovStable he
@[powerlib_domain] theorem zero_input_stable :
    powerlib.LCL.LyapunovStable submittedModel 0 0 0 := accepted.zeroInput_stable
@[powerlib_domain] theorem trajectory_exists (u vg : ℝ) (e initial : powerlib.LCL.State)
    (he : powerlib.LCL.IsEquilibrium submittedModel u vg e) :
    ∃ x, powerlib.LCL.IsTrajectory submittedModel u vg x ∧ x 0 = initial :=
  accepted.trajectory_exists he initial
@[powerlib_domain] theorem zero_input_trajectory_exists (initial : powerlib.LCL.State) :
    ∃ x, powerlib.LCL.IsTrajectory submittedModel 0 0 x ∧ x 0 = initial :=
  accepted.trajectory_exists (powerlib.LCL.zero_equilibrium submittedModel) initial
@[powerlib_domain] theorem trajectory_unique (u vg : ℝ) (e : powerlib.LCL.State)
    (x y : ℝ → powerlib.LCL.State) (he : powerlib.LCL.IsEquilibrium submittedModel u vg e)
    (hx : powerlib.LCL.IsTrajectory submittedModel u vg x)
    (hy : powerlib.LCL.IsTrajectory submittedModel u vg y) (h0 : x 0 = y 0) :
    Set.EqOn x y (Set.Ici 0) := accepted.trajectory_unique he hx hy h0
@[powerlib_domain] theorem integral_passivity (u : ℝ → powerlib.LCL.PortInput)
    (x : ℝ → powerlib.LCL.State) (hx : powerlib.LCL.IsPortTrajectory submittedModel u x)
    (t : ℝ) (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun s => u s 0 * x s 0 - u s 1 * x s 2) volume 0 t) :
    powerlib.LCL.portEnergy submittedModel (x t) - powerlib.LCL.portEnergy submittedModel (x 0) ≤
      ∫ s in (0 : ℝ)..t, u s 0 * x s 0 - u s 1 * x s 2 :=
  accepted.integral_passivity hx ht hsupply
@[powerlib_domain] theorem zero_input_energy_nonincreasing (x : ℝ → powerlib.LCL.State)
    (hx : powerlib.LCL.IsTrajectory submittedModel 0 0 x) :
    AntitoneOn (fun t => powerlib.LCL.portEnergy submittedModel (x t)) (Set.Ici 0) :=
  accepted.zeroInput_energy_nonincreasing hx
end Admission
''' + audit(["Admission.accepted", "Admission.portStorage", *ADMITTED_THEOREMS]))


def verify_kernel(proof):
    proof = Path(proof)
    roots = ["Admission.accepted", "Admission.portStorage", *ADMITTED_THEOREMS]
    names = ", ".join("`" + name for name in roots)
    required = f'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for root in ([{names}] : List Name) do
    unless (env.find? root).isSome do
      throwError "Missing required admission declaration {{root}}"
'''
    # The checker supplies its own fixed-root audit. A success marker in the
    # proposed source cannot replace this audit, and checking never changes the
    # original proof artifact or grows it on repeated verification.
    with tempfile.TemporaryDirectory(prefix="passivity-audit-", dir=proof.parent) as directory:
        checked = Path(directory) / proof.name
        checked.write_text(proof.read_text() + required + audit(roots))
        proof.with_name(proof.stem + "-kernel.lean").write_bytes(checked.read_bytes())
        try:
            check_lean(checked)
        finally:
            log = checked.with_suffix(".log")
            if log.exists():
                proof.with_suffix(".log").write_bytes(log.read_bytes())
    version = demand(["lake", "env", "lean", "--version"]).strip()
    if "version 4.19.0" not in version:
        raise RuntimeError("Expected pinned Lean 4.19.0")
    return version


def certificate_report(model, p):
    verify_witness(model, p)
    return {"schema": SCHEMA, "goal": "passive-stability",
            "model": model.serialized(), "state_order": list(STATE_ORDER),
            "P": matrix_data(p), "status": "UNVERIFIED", "kernel_verified": False,
            "maturity": "Unverified proof artifact",
            "scope": "Ideal three-state continuous-time single-axis LCL plant",
            "model_boundary": {
                "coordinate_frame": "Scalar stationary electrical axis",
                "parameters": "L1, L2, C > 0; R1, R2 >= 0",
                "inputs": ["converter_voltage", "grid_voltage"],
                "output": ["converter_current", "negative_grid_current"],
                "supply": "converter_voltage * converter_current - grid_voltage * grid_current",
                "controller": "None; voltages are external ports",
                "dynamics": "Continuous-time ideal lumped LCL circuit",
                "excluded": ["delay", "PWM", "PLL", "switching", "nonlinear grid dynamics"],
                "equilibria": "Zero-input origin; arbitrary existing equilibria under constant ports"},
            "storage": "(L1 * i1^2 + C * vc^2 + L2 * i2^2) / 2",
            "semantics": ("Integral input-output passivity along actual varying-port trajectories; "
                          "epsilon-delta stability of constant-port equilibria, including lossless circuits")}


def output_directory(prefix, directory=None):
    RESULTS.mkdir(parents=True, exist_ok=True)
    path = Path(directory) if directory is not None else Path(tempfile.mkdtemp(prefix=prefix, dir=RESULTS))
    path.mkdir(parents=True, exist_ok=True)
    return path


def retain_model(model, directory, *, submitted_bytes=None):
    submitted = directory / "submitted.json"
    submitted.write_bytes(submitted_bytes if submitted_bytes is not None else
                          (json.dumps(model.serialized(), indent=2) + "\n").encode())
    # The retained original is what admission must reconstruct, not a candidate claim.
    if read_model(submitted) != model:
        raise ValueError("Retained submission disagrees with the admission model")
    return submitted


def admit(model, p, directory, *, submitted_bytes=None, maturity, witness_origin):
    submitted = retain_model(model, directory, submitted_bytes=submitted_bytes)
    submitted_model = read_model(submitted)
    report = certificate_report(submitted_model, p)
    proof = directory / "Certificate.lean"
    proof.write_text(proof_source(submitted_model, p))
    check_conversions()
    report["lean"] = verify_kernel(proof)
    provenance = proof_provenance(proof)
    # Copy input bytes into the immutable per-proof bundle as well as the result root.
    evidence = directory / provenance["evidence_directory"]
    retained = evidence / "submitted.json"
    retained.write_bytes(submitted.read_bytes())
    provenance["evidence_files_sha256"]["submitted.json"] = digest(retained)
    kernel_source = proof.with_name(proof.stem + "-kernel.lean")
    retained_kernel_source = evidence / kernel_source.name
    retained_kernel_source.write_bytes(kernel_source.read_bytes())
    provenance["evidence_files_sha256"][kernel_source.name] = digest(retained_kernel_source)
    provenance["kernel_checked_source"] = kernel_source.name
    provenance["kernel_checked_source_sha256"] = digest(kernel_source)
    for name in ["passivity.py", "lcl.py", "common.py", "powerlib.py", "bridge.py", "lcl_bridge.py"]:
        target = evidence / "dependencies" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((DEPENDENCIES / name).read_bytes())
        provenance["evidence_files_sha256"][str(target.relative_to(evidence))] = digest(target)
    report.update({"proof": str(proof), "proof_sha256": digest(proof),
                   "provenance": provenance, "kernel_verified": True,
                   "status": "ACCEPTED", "maturity": maturity,
                   "witness_origin": witness_origin, "theorems": list(ADMITTED_THEOREMS),
                   "submitted_model_sha256": digest(submitted),
                   "conversion": provenance["conversions"]["lcl"]})
    (directory / "certificate.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def synthesize(model, kernel=False, directory=None, *, submitted_bytes=None):
    p = synthesize_witness(model)
    directory = output_directory("lcl-passivity-", directory)
    if kernel:
        return admit(model, p, directory, submitted_bytes=submitted_bytes,
                     maturity="S-level",
                     witness_origin="Automatic exact physical storage synthesis from witness-free model")
    submitted = retain_model(model, directory, submitted_bytes=submitted_bytes)
    report = certificate_report(model, p)
    proof = directory / "Certificate.lean"
    proof.write_text(proof_source(read_model(submitted), p))
    report.update({"proof": str(proof), "proof_sha256": digest(proof),
                   "submitted_model_sha256": digest(submitted)})
    (directory / "certificate.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def verify_saved(model, path, kernel=False, *, submitted_bytes=None):
    supplied = Path(path).read_bytes()
    data = json.loads(supplied, object_pairs_hook=unique_object)
    if not isinstance(data, dict) or data.get("schema") != SCHEMA:
        raise ValueError("Unsupported passive storage certificate schema")
    if data.get("goal") != "passive-stability":
        raise ValueError("Certificate uses the wrong admission goal")
    if model_from_data(data.get("model")) != model:
        raise ValueError("Certificate describes a different submitted model")
    if data.get("state_order") != STATE_ORDER:
        raise ValueError("Certificate uses the wrong state order")
    p = certificate_matrix(data.get("P"))
    report = certificate_report(model, p)
    # Claimed success, theorem names, proof paths and hashes have no admission authority.
    if kernel:
        report = admit(model, p, output_directory("lcl-passivity-verify-"),
                       submitted_bytes=submitted_bytes,
                       maturity="Certificate verification", witness_origin="Submitted certificate")
        directory = Path(report["proof"]).parent
        evidence = directory / report["provenance"]["evidence_directory"]
        retained = evidence / "supplied_certificate.json"
        retained.write_bytes(supplied)
        report["submitted_certificate_sha256"] = digest(retained)
        report["provenance"]["evidence_files_sha256"]["supplied_certificate.json"] = digest(retained)
        (directory / "certificate.json").write_text(json.dumps(report, indent=2) + "\n")
        return report
    return report


def atp(path):
    original = Path(path).read_bytes()
    directory = output_directory("lcl-passivity-")
    submitted = directory / "submitted.json"
    submitted.write_bytes(original)
    return synthesize(read_model(submitted), kernel=True, directory=directory,
                      submitted_bytes=original)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    synthesis = commands.add_parser("synthesize")
    synthesis.add_argument("model")
    synthesis.add_argument("--verify", action="store_true", help="Check bridge, model-bound proof, and axiom audit")
    verification = commands.add_parser("verify")
    verification.add_argument("model")
    verification.add_argument("certificate")
    verification.add_argument("--verify", action="store_true", help="Reconstruct and kernel-check a fresh proof")
    args = parser.parse_args()
    try:
        model = read_model(args.model)
        report = (synthesize(model, args.verify, submitted_bytes=Path(args.model).read_bytes())
                  if args.command == "synthesize" else
                  verify_saved(model, args.certificate, args.verify,
                               submitted_bytes=Path(args.model).read_bytes()))
        print(json.dumps(report, indent=2))
        return 0
    except (ValueError, OSError, RuntimeError) as error:
        print(json.dumps({"status": "NOT_ACCEPTED", "reason": str(error)}, indent=2))
        return 1


if __name__ == "__main__":
    sys.exit(main())
