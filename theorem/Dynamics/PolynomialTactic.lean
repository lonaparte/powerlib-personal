import theorem.Dynamics.PolynomialSynthesis
import theorem.LibrarySearch
import Lean.Meta.Eval
import Lean.Meta.Transform
import Lean.Elab.Tactic

/-! Witness-free polynomial stability synthesis inside Lean.
Native evaluation proposes rational data only. The elaborator reconstructs every
`Accepted` obligation with ordinary kernel-checked arithmetic and polynomial
proofs, then checks the transitive axiom dependencies of the final result.
-/

namespace powerlib.Dynamics.Polynomial2
open Lean Meta Elab Tactic

private unsafe def synthesizeAccepted (originalModel : Expr) : TacticM Expr := do
  let closedModel ← zetaReduce (← instantiateMVars originalModel)
  if closedModel.hasFVar || closedModel.hasMVar then
    throwError "UNPROVED: polynomial_stability requires a closed, computable Model"
  let model : Model ← evalExpr Model (mkConst ``Model) closedModel
  let some witness := synthesize model |
    throwError "UNPROVED: bounded rational Lyapunov/SOS synthesis found no certificate"
  let originalModelSyntax ← Term.exprToSyntax originalModel
  let modelSyntax ← Term.exprToSyntax (toExpr model)
  let witnessSyntax ← Term.exprToSyntax (toExpr witness)
  let candidate ← `(term|
    (show Accepted $originalModelSyntax from by
     have model_eq : $originalModelSyntax = $modelSyntax := by decide +kernel
     exact model_eq.symm ▸ (show Accepted $modelSyntax from
     { toWitness := $witnessSyntax
       lower_pos := by norm_num [ratLiteral]
       upper_pos := by norm_num [ratLiteral]
       rate_pos := by norm_num [ratLiteral]
       lower_nonneg := by norm_num [List.Forall, ratLiteral]
       upper_nonneg := by norm_num [List.Forall, ratLiteral]
       decay_nonneg := by norm_num [List.Forall, ratLiteral]
       field_zero := by
         ext j
         fin_cases j <;> norm_num [Model.field, eval, ratLiteral]
       lower_identity := by
         intro x y
         norm_num [quadratic, sosEval, eval, ratLiteral] <;> ring
       upper_identity := by
         intro x y
         norm_num [quadratic, sosEval, eval, ratLiteral] <;> ring
       decay_identity := by
         intro x y
         norm_num [lie, quadratic, sosEval, eval, ratLiteral] <;> ring
     })))
  -- The expected type retains the original submitted model expression. A
  -- wrong evaluation or quotation cannot substitute a different model here:
  -- the ordinary `decide` proof also checks the model equality in the kernel.
  let certificate ← Term.elabTermEnsuringType candidate
    (some (mkApp (mkConst ``Accepted) originalModel))
  Term.synthesizeSyntheticMVarsNoPostponing
  let certificate ← instantiateMVars certificate
  if certificate.hasMVar then throwError "Polynomial certificate contains unresolved obligations"
  return certificate

private unsafe def solvePolynomial (modelSyntax : Syntax) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let model ← Term.elabTermEnsuringType modelSyntax (some (mkConst ``Model))
  Term.synthesizeSyntheticMVarsNoPostponing
  let model ← instantiateMVars model
  let certificate ← synthesizeAccepted model
  let target ← goal.getType
  let mut answer : Option Expr := none
  if ← isDefEq (← inferType certificate) target then
    answer := some certificate
  else
    for theoremName in #[``Accepted.globallyExponentiallyStable,
        ``Accepted.globallyAsymptoticallyStable, ``Accepted.forwardComplete] do
      let proof ← mkAppM theoremName #[certificate]
      if ← isDefEq (← inferType proof) target then
        answer := some proof
        break
  let some proof := answer |
    throwError "polynomial_stability expected Accepted, global stability, or forward completeness of the submitted model"
  powerlib.Search.checkProof proof
  goal.assign proof
  replaceMainGoal []

syntax (name := polynomialStability) "polynomial_stability " term : tactic

@[tactic polynomialStability] unsafe def evalPolynomialStability : Tactic := fun stx => do
  match stx with
  | `(tactic| polynomial_stability $model) => solvePolynomial model
  | _ => throwUnsupportedSyntax

end powerlib.Dynamics.Polynomial2
