"""Shared process and kernel-audit utilities for the minimal demonstration."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = ROOT / "dependencies"
CACHE = Path(os.environ.get("POWERLIB_CACHE_DIR", ROOT.parent / ".powerlib-local/cache")).resolve()
RESULTS = Path(os.environ.get("POWERLIB_RESULTS_DIR", ROOT.parent / ".powerlib-local/results")).resolve()
CUBICAL_COMMIT = "b150186d2544e7efeddd31e5d14a8b9ecbb100f7"


def run(args, *, input=None, cwd=ROOT, timeout=600):
    result = subprocess.run(list(map(str, args)), cwd=cwd, input=input,
                            text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout)
    return result.returncode, result.stdout


def demand(args, **kwargs):
    code, log = run(args, **kwargs)
    if code:
        raise RuntimeError(f"Command failed ({code}): {' '.join(map(str, args))}\n{log}")
    return log


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def proof_provenance(proof):
    version = demand(["lake", "env", "lean", "--version"]).strip()
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0" or "version 4.19.0" not in version:
        raise RuntimeError("Expected pinned Lean 4.19.0")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    revisions = {}
    for package in manifest["packages"]:
        checkout = ROOT / manifest["packagesDir"] / package["name"]
        actual = demand(["git", "-C", checkout, "rev-parse", "HEAD"]).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        if demand(["git", "-C", checkout, "status", "--porcelain", "--untracked-files=no"]).strip():
            raise RuntimeError(f"Dependency source has been modified: {package['name']}")
        revisions[package["name"]] = actual
    return {"lean": version, "dependencies": revisions,
            "manifest_sha256": digest(ROOT / "lake-manifest.json"),
            "public_source_sha256": {
                str(path.relative_to(ROOT)): digest(path)
                for path in sorted((ROOT / "theorems").rglob("*.lean"))},
            "proof_sha256": digest(proof),
            "kernel_log_sha256": digest(Path(proof).with_suffix(".log")),
            "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"]}


CORE = [
    "reciprocal_involutive", "scale_cancel", "state_roundtrip", "impedance_roundtrip",
    "modelEquiv", "same_dynamics", "same_port_relation", "frequency_zero_iff",
    "impedance_stable_iff", "stability_agrees", "Accepted.stable",
    "Accepted.dissipation", "response_initial", "response_solves", "Accepted.decay_bound",
    "generated.convert_spec",
    "LCL.circuit_roundtrip", "LCL.state_roundtrip", "LCL.modelEquiv",
    "LCL.same_dynamics", "LCL.StateSpace.matrix_mulVec", "LCL.StateSpace.perturbation",
    "LCL.characteristic_identity", "LCL.same_characteristic", "lcl_stable_iff",
    "LCL.stability_agrees", "LCL.hurwitz_gap", "LCL.cubic_hurwitz",
    "LCL.stable_of_hurwitz", "LCL.passive_hurwitz", "LCL.passive_stable_iff",
    "LCL.energy_positive", "LCL.Accepted.stable", "LCL.Accepted.positive",
    "LCL.Accepted.dissipation", "generated.convertLCL_spec",
]


def audit(extra=(), *, include_core=True):
    roots = (["powerlib." + name for name in CORE] if include_core else []) + list(extra)
    names = ", ".join("`" + name for name in roots)
    return f'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {{}}
  for root in [{names}] do
    let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
    state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom {{ax}}"
  logInfo "POWERLIB_KERNEL_OK"
'''


def check_lean(path):
    code, log = run(["lake", "env", "lean", path])
    Path(path).with_suffix(".log").write_text(log)
    if code or "POWERLIB_KERNEL_OK" not in log:
        raise RuntimeError(f"Lean rejected {path}; see {Path(path).with_suffix('.log')}\n{log}")
    return log
