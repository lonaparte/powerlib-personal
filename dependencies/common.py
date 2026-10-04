"""Shared process and kernel-audit utilities for the minimal demonstration."""
from pathlib import Path
import hashlib
import json
import os
import shutil
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


def check_conversions():
    from bridge import rebuild
    from lcl_bridge import rebuild as rebuild_lcl
    conversions = {"rl": rebuild(), "lcl": rebuild_lcl()}
    demand(["lake", "build"], timeout=1800)
    return conversions


def conversion_provenance():
    evidence = {}
    for family, prefix, source, target, wire in [
        ("rl", "bridge", "Conversion.agda", "Conversion.lean", "wire.json"),
        ("lcl", "lcl-bridge", "LCLConversion.agda", "LCLConversion.lean", "lcl_wire.json"),
    ]:
        report_path = RESULTS / (prefix + ".json")
        report = json.loads(report_path.read_text())
        expected = {"status": "AGDA_AND_LEAN_CHECKED", "agda": "2.8.0",
                    "cubical_commit": CUBICAL_COMMIT,
                    "agda_source_sha256": digest(ROOT / "theorems" / source),
                    "generated_sha256": digest(ROOT / "theorems/generated" / target),
                    "wire": json.loads((DEPENDENCIES / wire).read_text())}
        if family == "lcl":
            expected["rl_source_sha256"] = digest(ROOT / "theorems/Conversion.agda")
        if any(report.get(key) != value for key, value in expected.items()):
            raise RuntimeError(f"Stale or mismatched {family} conversion provenance")
        endpoint = RESULTS / (prefix + "-endpoint.lean")
        if report.get("endpoint_sha256") != digest(endpoint) or report.get("endpoint_log_sha256") != digest(endpoint.with_suffix(".log")):
            raise RuntimeError(f"Mismatched {family} endpoint evidence")
        evidence[family] = {**report, "report_sha256": digest(report_path),
                            "agda_log_sha256": digest(RESULTS / (prefix + ".log")),
                            "wire_sha256": digest(DEPENDENCIES / wire)}
    return evidence


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
    conversions = conversion_provenance()
    # Keep immutable per-proof copies: a later bridge run must not overwrite
    # the logs identified by an earlier certificate's hashes.
    evidence = Path(proof).with_name(Path(proof).stem + "-evidence")
    evidence.mkdir(parents=True, exist_ok=True)
    for prefix in ["bridge", "lcl-bridge"]:
        for suffix in [".json", ".log", "-endpoint.lean", "-endpoint.log"]:
            shutil.copyfile(RESULTS / (prefix + suffix), evidence / (prefix + suffix))
    for path in [ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "Rules.md",
                 ROOT / "powerlib.lean", DEPENDENCIES / "wire.json", DEPENDENCIES / "lcl_wire.json",
                 *sorted((ROOT / "theorems").rglob("*.lean")),
                 *sorted((ROOT / "theorems").rglob("*.agda"))]:
        target = evidence / path.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    return {"lean": version, "dependencies": revisions,
            "source_commit": demand(["git", "rev-parse", "HEAD"]).strip(),
            "conversions": conversions,
            "evidence_directory": evidence.name,
            "evidence_files_sha256": {str(p.relative_to(evidence)): digest(p)
                                      for p in sorted(evidence.rglob("*")) if p.is_file()},
            "manifest_sha256": digest(ROOT / "lake-manifest.json"),
            "public_source_sha256": {"powerlib.lean": digest(ROOT / "powerlib.lean"), **{
                str(path.relative_to(ROOT)): digest(path)
                for path in sorted((ROOT / "theorems").rglob("*.lean"))}},
            "proof_sha256": digest(proof),
            "kernel_log_sha256": digest(Path(proof).with_suffix(".log")),
            "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"]}


def audit(extra=(), *, include_core=True):
    names = ", ".join("`" + name for name in extra)
    discovered = " ++ (powerlib.Registry.theoremNames env).toList" if include_core else ""
    core = '''
  for (root, info) in env.constants do
    if root.getRoot == `powerlib && !info.isUnsafe then
      let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
      state := next
''' if include_core else ""
    return f'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {{}}{core}
  let roots := ([{names}] : List Name){discovered}
  for root in roots do
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
