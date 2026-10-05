import powerlib

open powerlib

-- These are library-rule reuse checks with supplied premises, not certificate synthesis.
namespace RuleReuseChecks

inductive DerivedClaim (value : ℕ) : Prop where
  | intro : 0 < value → DerivedClaim value

-- A type-directed rule whose numerical premise must be discharged at the application.
@[powerlib_foundation] theorem from_model_relation (value witness : ℕ) (h : value = 2 * witness + 1) :
    DerivedClaim value := .intro (by omega)

@[powerlib_foundation] theorem concrete_relation : DerivedClaim 23 := by
  have hmodel : (23 : ℕ) = 2 * 11 + 1 := by decide
  powerlib_search

@[powerlib_domain] theorem existence_and_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → E} {V : E → ℝ} {equilibrium : E}
    (certificate : Dynamics.QuadraticDecayCertificate f V equilibrium)
    (hf : ContDiff ℝ 1 f) :
    Dynamics.ForwardComplete f ∧ Dynamics.GloballyExponentiallyStable f equilibrium := by
  constructor <;> powerlib_search

@[powerlib_domain] theorem strict_energy_existence {n : ℕ}
    {f : Dynamics.State n → Dynamics.State n} {V : Dynamics.State n → ℝ}
    {equilibrium : Dynamics.State n} (hn : 0 < n) (hf : ContDiff ℝ 1 f)
    (hV : Dynamics.IsStrictLyapunovFunction f V equilibrium) :
    Dynamics.ForwardComplete f := by
  have hstable : Dynamics.GloballyAsymptoticallyStable f equilibrium := by powerlib_search
  exact hstable.2.1

end RuleReuseChecks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let info ← getConstInfo `RuleReuseChecks.concrete_relation
  let some proof := info.value? (allowOpaque := true) | throwError "Missing rule-reuse proof"
  unless proof.getUsedConstants.contains `RuleReuseChecks.from_model_relation do
    throwError "The numerical target did not apply the type-directed rule"
  for name in #[`RuleReuseChecks.concrete_relation, `RuleReuseChecks.existence_and_decay,
      `RuleReuseChecks.strict_energy_existence] do
    for axiomName in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom axiomName do
        throwError "Rule reuse used an unapproved axiom: {axiomName}"
  logInfo "POWERLIB_RULE_REUSE_OK"
