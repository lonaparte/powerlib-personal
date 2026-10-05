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


def _source_snapshot(proof):
    paths = [ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
             ROOT / "Rules.md", ROOT / "powerlib.lean", DEPENDENCIES / "wire.json",
             DEPENDENCIES / "lcl_wire.json",
             *sorted((ROOT / "theorems").rglob("*.lean")),
             *sorted((ROOT / "theorems").rglob("*.agda")),
             *sorted((DEPENDENCIES / "licenses").rglob("*"))]
    return {"source_files_sha256": {str(path.relative_to(ROOT)): digest(path)
                                    for path in paths if path.is_file()},
            "proof_sha256": digest(proof)}


def _compiled_snapshot():
    artifacts = ROOT / ".lake/build/lib/lean"
    return {str(path.relative_to(ROOT)): digest(path)
            for path in sorted(artifacts.rglob("*.olean"))}


def _checked_path(proof):
    return Path(proof).with_suffix(".checked.json")


def _checked_snapshot(proof):
    try:
        checked = json.loads(_checked_path(proof).read_text())
    except (OSError, ValueError) as error:
        raise RuntimeError("Missing or invalid kernel-check snapshot; check the proof again") from error
    if (not isinstance(checked, dict) or checked.get("schema") != "powerlib.kernel-check.v1"
            or checked.get("build") is not True):
        raise RuntimeError("Proof provenance requires a completed public-library build")
    if checked.get("source_snapshot") != _source_snapshot(proof):
        raise RuntimeError("Public source or proof changed after kernel checking")
    if checked.get("compiled_artifacts_sha256") != _compiled_snapshot():
        raise RuntimeError("Compiled library changed after kernel checking")
    if checked.get("kernel_log_sha256") != digest(Path(proof).with_suffix(".log")):
        raise RuntimeError("Kernel log changed after kernel checking")
    return checked


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
    checked = _checked_snapshot(proof)
    checked_hash = digest(_checked_path(proof))
    checked_sources = checked["source_snapshot"]["source_files_sha256"]
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
    shutil.copyfile(_checked_path(proof), evidence / _checked_path(proof).name)
    for prefix in ["bridge", "lcl-bridge"]:
        for suffix in [".json", ".log", "-endpoint.lean", "-endpoint.log"]:
            shutil.copyfile(RESULTS / (prefix + suffix), evidence / (prefix + suffix))
    for name, expected_hash in checked_sources.items():
        path = ROOT / name
        target = evidence / path.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        if digest(target) != expected_hash:
            raise RuntimeError(f"Source changed while retaining evidence: {name}")
    for family, prefix in [("rl", "bridge"), ("lcl", "lcl-bridge")]:
        for suffix, key in [(".json", "report_sha256"), (".log", "agda_log_sha256"),
                            ("-endpoint.lean", "endpoint_sha256"),
                            ("-endpoint.log", "endpoint_log_sha256")]:
            if digest(evidence / (prefix + suffix)) != conversions[family][key]:
                raise RuntimeError(f"Conversion evidence changed while retaining it: {family}")
    # Reject edits or another build while assembling the retained evidence.
    if (_checked_snapshot(proof) != checked or digest(_checked_path(proof)) != checked_hash):
        raise RuntimeError("Kernel-check snapshot changed while retaining evidence")
    return {"lean": version, "dependencies": revisions,
            "source_commit": demand(["git", "rev-parse", "HEAD"]).strip(),
            "conversions": conversions,
            "evidence_directory": evidence.name,
            "evidence_files_sha256": {str(p.relative_to(evidence)): digest(p)
                                      for p in sorted(evidence.rglob("*")) if p.is_file()},
            "manifest_sha256": checked_sources["lake-manifest.json"],
            "public_source_sha256": {name: expected_hash for name, expected_hash in checked_sources.items()
                                     if name == "powerlib.lean" or
                                     (name.startswith("theorems/") and name.endswith(".lean"))},
            "proof_sha256": checked["source_snapshot"]["proof_sha256"],
            "kernel_log_sha256": checked["kernel_log_sha256"],
            "kernel_check_sha256": checked_hash,
            "compiled_artifacts_sha256": checked["compiled_artifacts_sha256"],
            "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"]}


def audit(extra=(), *, include_core=True, theorem_roots=()):
    theorem_roots = list(theorem_roots)
    roots = list(dict.fromkeys(list(extra) + theorem_roots))
    names = ", ".join("`" + name for name in roots)
    theorem_names = ", ".join("`" + name for name in theorem_roots)

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
    unless (env.checked.get.find? root).isSome do
      throwError "Unknown audit root: {{root}}"
  for root in ([{theorem_names}] : List Name) do
    match env.checked.get.find? root with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected a theorem audit root: {{root}}"
  for root in roots do
    let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
    state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom {{ax}}"
  logInfo "POWERLIB_KERNEL_OK"
'''


def check_lean(path, *, build=True):
    path = Path(path)
    checked_path = _checked_path(path)
    # An unsuccessful recheck must not leave an earlier success usable.
    checked_path.unlink(missing_ok=True)
    sources = _source_snapshot(path)
    if build:
        code, build_log = run(["lake", "build"], timeout=1800)
        if code:
            path.with_suffix(".log").write_text(build_log)
            raise RuntimeError(f"Lean library build failed before checking {path}\n{build_log}")
    if _source_snapshot(path) != sources:
        raise RuntimeError("Public source or proof changed during the library build")
    compiled = _compiled_snapshot()
    code, log = run(["lake", "env", "lean", path])
    path.with_suffix(".log").write_text(log)
    if code or "POWERLIB_KERNEL_OK" not in log:
        raise RuntimeError(f"Lean rejected {path}; see {path.with_suffix('.log')}\n{log}")
    if _source_snapshot(path) != sources:
        raise RuntimeError("Public source or proof changed during kernel checking")
    if _compiled_snapshot() != compiled:
        raise RuntimeError("Compiled library changed during kernel checking")
    checked_path.write_text(json.dumps({
        "schema": "powerlib.kernel-check.v1", "build": build,
        "source_snapshot": sources, "compiled_artifacts_sha256": compiled,
        "kernel_log_sha256": digest(path.with_suffix(".log")),
    }, indent=2) + "\n")
    return log
