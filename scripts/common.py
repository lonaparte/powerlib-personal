"""Shared process and kernel-audit utilities for the minimal demonstration."""
from pathlib import Path
import hashlib
import subprocess

ROOT = Path(__file__).resolve().parents[1]
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


CORE = [
    "reciprocal_involutive", "scale_cancel", "state_roundtrip", "impedance_roundtrip",
    "modelEquiv", "same_dynamics", "same_port_relation", "frequency_zero_iff",
    "impedance_stable_iff", "stability_agrees", "Accepted.stable",
    "Accepted.dissipation", "response_initial", "response_solves", "Accepted.decay_bound",
    "generated.convert_spec",
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
