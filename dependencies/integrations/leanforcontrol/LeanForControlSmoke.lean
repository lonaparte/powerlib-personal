import theorem.LibrarySearch
import theorem.Flow.Certificate
import theorem.Linear.Realization
import LeanForControl.axioms

open scoped Matrix.Norms.Frobenius

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`LinearSystems.IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov,
      `hurwitz_linearization_locally_exponentially_stable,
      `unstable_affineLinear_of_eigenvalue_re_pos, `lyapunov_asymptotic_stable,
      `exists_isIntegralCurveOn_Ici,
      `LinearSystems.isControllable_iff_controllabilityMatrix_rank_eq,
      `LinearSystems.IsHurwitz.exists_norm_exp_nat_smul_lt_one] do
    let some entry := powerlib.Search.describe env name |
      throwError "LeanForControl declaration absent from discovery: {name}"
    unless entry.moduleName.getRoot == `LeanForControl && entry.kind.isNone do
      throwError "Upstream declaration lost its module or was classified locally: {name}"
    unless powerlib.Search.eligible env name do
      throwError "Axiom-admissible LeanForControl declaration was excluded: {name}"
  let consumers : Array (Name × powerlib.Registry.TheoremKind) := #[
    (`powerlib.Linear.locallyExponentiallyStable_of_isHurwitz, .foundation),
    (`powerlib.Linear.nonempty_certificate_iff, .foundation),
    (`powerlib.Linear.unstable_of_eigenvalue, .foundation),
    (`powerlib.Flow.globallyAsymptoticallyStable_of_strictLyapunov, .foundation),
    (`powerlib.Flow.forwardComplete_of_lipschitzWith, .foundation),
    (`powerlib.Linear.isObservable_iff_isControllable_transpose, .foundation),
    (`powerlib.Linear.contractive_block, .foundation)]
  for (name, kind) in consumers do
    let info ← getConstInfo name
    let some proof := info.value? (allowOpaque := true) |
      throwError "Missing upstream consumer proof: {name}"
    unless proof.getUsedConstants.any (fun dependency =>
        match env.getModuleIdxFor? dependency with
        | some index => env.header.moduleNames[index]!.getRoot == `LeanForControl
        | none => false) do
      throwError "Consumer did not directly apply an imported LeanForControl theorem: {name}"
    for ax in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unapproved upstream consumer axiom: {name}: {ax}"
    unless powerlib.Registry.kindOf? env name == some kind do
      throwError "Upstream consumer has the wrong classification: {name}"
  -- This is an actual proved upstream lemma with a transitive custom-axiom dependency.
  let badName := `exists_strictMono_upper_bound
  let some bad := powerlib.Search.describe env badName |
    throwError "Missing upstream negative control"
  unless bad.moduleName == `LeanForControl.axioms &&
      bad.axioms.contains `exists_strictMono_upper_bound_global do
    throwError "Negative control did not inherit the real upstream custom axiom"
  if powerlib.Search.eligible env badName then
    throwError "Upstream custom-axiom consequence entered the admissible index"
  liftTermElabM do
    let info ← getConstInfo badName
    forallTelescope info.type fun _ goal => do
      let raw ← LibrarySearch.libSearchFindDecls goal
      unless raw.any (fun entry => entry.1 == badName) do
        throwError "Negative control did not exercise the standard search index"
      let admitted ← powerlib.Search.candidates goal
      if admitted.any (fun entry => entry.1 == badName) then
        throwError "Search failed to filter the upstream custom-axiom dependency"
    let badProof ← mkConstWithFreshMVarLevels badName
    unless (← observing? (powerlib.Search.checkProof badProof)).isNone do
      throwError "Completed-proof audit admitted an upstream custom axiom"
    withLetDecl `borrowed info.type badProof fun borrowed => do
      unless (← observing? (powerlib.Search.checkProof borrowed)).isNone do
        throwError "A local let hid an upstream custom axiom from the proof audit"
  logInfo "POWERLIB_LEANFORCONTROL_REUSE_OK: 7 direct consumers; custom-axiom rejection"
