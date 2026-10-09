-- Automatically synthesized from the original matrix without a supplied witness.
import powerlib
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace Candidate
def model : powerlib.LTI.AutonomousModel 2 := ⟨![![(-1 / 1 : ℝ), (10 / 1 : ℝ)], ![(0 / 1 : ℝ), (-1 / 1 : ℝ)]]⟩

def certificate : powerlib.LTI.Accepted model where
  P := ![![(1 / 2 : ℝ), (5 / 2 : ℝ)], ![(5 / 2 : ℝ), (51 / 2 : ℝ)]]
  lower := (1 / 4 : ℝ)
  upper := (32 / 1 : ℝ)
  lower_pos := by norm_num
  upper_pos := by norm_num
  symmetric := by
    ext i j
    erw [Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> norm_num
  lower_bound := by
    intro x
    have hs : 0 ≤ (1 / 4 : ℝ) * ((1 / 1 : ℝ) * x 0 + (10 / 1 : ℝ) * x 1) ^ 2 + (1 / 4 : ℝ) * ((1 / 1 : ℝ) * x 1) ^ 2 := by positivity
    calc
      _ ≤ _ + ((1 / 4 : ℝ) * ((1 / 1 : ℝ) * x 0 + (10 / 1 : ℝ) * x 1) ^ 2 + (1 / 4 : ℝ) * ((1 / 1 : ℝ) * x 1) ^ 2) := le_add_of_nonneg_right hs
      _ = _ := by norm_num [powerlib.LTI.energy, powerlib.LTI.sqNorm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ]; ring1!
  upper_bound := by
    intro x
    have hs : 0 ≤ (63 / 2 : ℝ) * ((1 / 1 : ℝ) * x 0 + (-5 / 63 : ℝ) * x 1) ^ 2 + (397 / 63 : ℝ) * ((1 / 1 : ℝ) * x 1) ^ 2 := by positivity
    calc
      _ ≤ _ + ((63 / 2 : ℝ) * ((1 / 1 : ℝ) * x 0 + (-5 / 63 : ℝ) * x 1) ^ 2 + (397 / 63 : ℝ) * ((1 / 1 : ℝ) * x 1) ^ 2) := le_add_of_nonneg_right hs
      _ = _ := by norm_num [powerlib.LTI.energy, powerlib.LTI.sqNorm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ]; ring1!
  lyapunov := by
    ext i j
    erw [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [model, Fin.sum_univ_succ]
end Candidate
namespace Admission
def submittedModel : powerlib.LTI.AutonomousModel 2 := ⟨![![(-1 / 1 : ℝ), (10 / 1 : ℝ)], ![(0 / 1 : ℝ), (-1 / 1 : ℝ)]]⟩

def accepted : powerlib.LTI.Accepted submittedModel := Candidate.certificate
@[powerlib_domain] theorem exponentially_stable :
    powerlib.LTI.ExponentiallyStable submittedModel := accepted.exponentially_stable
@[powerlib_domain] theorem decay (x : ℝ → powerlib.LTI.State _)
    (hx : powerlib.LTI.IsTrajectory submittedModel x) (t : ℝ) (ht : 0 ≤ t) :
    powerlib.LTI.sqNorm (x t) ≤ (accepted.upper / accepted.lower) *
      Real.exp (-(t / accepted.upper)) * powerlib.LTI.sqNorm (x 0) :=
  accepted.decay_bound hx t ht
@[powerlib_domain] theorem exists_solution (initial : powerlib.LTI.State _) :
    ∃ x, powerlib.LTI.IsTrajectory submittedModel x ∧ x 0 = initial :=
  powerlib.LTI.trajectory_exists submittedModel initial
@[powerlib_domain] theorem norm_decay (x : ℝ → powerlib.LTI.State _)
    (hx : powerlib.LTI.IsTrajectory submittedModel x) (t : ℝ) (ht : 0 ≤ t) :
    ‖powerlib.LTI.euclidean (x t)‖ ≤ Real.sqrt (accepted.upper / accepted.lower) *
      Real.exp (-(t / accepted.upper) / 2) * ‖powerlib.LTI.euclidean (x 0)‖ :=
  accepted.norm_bound hx t ht
@[powerlib_domain] theorem unique_solution (x : ℝ → powerlib.LTI.State _)
    (hx : powerlib.LTI.IsTrajectory submittedModel x) (t : ℝ) (ht : 0 ≤ t) :
    x t = powerlib.LTI.response submittedModel (x 0) t := accepted.response_unique hx t ht
@[powerlib_domain] theorem converges (x : ℝ → powerlib.LTI.State _)
    (hx : powerlib.LTI.IsTrajectory submittedModel x) :
    Filter.Tendsto (fun t => powerlib.LTI.sqNorm (x t)) Filter.atTop (nhds 0) :=
  accepted.sqNorm_tendsto_zero hx
structure SemanticContract : Prop where
  exponentially_stable : powerlib.LTI.ExponentiallyStable submittedModel
  decay : ∀ (x : ℝ → powerlib.LTI.State _),
    powerlib.LTI.IsTrajectory submittedModel x → ∀ t : ℝ, 0 ≤ t →
      powerlib.LTI.sqNorm (x t) ≤ (accepted.upper / accepted.lower) *
        Real.exp (-(t / accepted.upper)) * powerlib.LTI.sqNorm (x 0)
  exists_solution : ∀ initial : powerlib.LTI.State _,
    ∃ x, powerlib.LTI.IsTrajectory submittedModel x ∧ x 0 = initial
  norm_decay : ∀ (x : ℝ → powerlib.LTI.State _),
    powerlib.LTI.IsTrajectory submittedModel x → ∀ t : ℝ, 0 ≤ t →
      ‖powerlib.LTI.euclidean (x t)‖ ≤ Real.sqrt (accepted.upper / accepted.lower) *
        Real.exp (-(t / accepted.upper) / 2) * ‖powerlib.LTI.euclidean (x 0)‖
  unique_solution : ∀ (x : ℝ → powerlib.LTI.State _),
    powerlib.LTI.IsTrajectory submittedModel x → ∀ t : ℝ, 0 ≤ t →
      x t = powerlib.LTI.response submittedModel (x 0) t
  converges : ∀ (x : ℝ → powerlib.LTI.State _),
    powerlib.LTI.IsTrajectory submittedModel x →
      Filter.Tendsto (fun t => powerlib.LTI.sqNorm (x t)) Filter.atTop (nhds 0)

@[powerlib_domain] theorem semanticContract : SemanticContract := {
  exponentially_stable := Admission.exponentially_stable
  decay := Admission.decay
  exists_solution := Admission.exists_solution
  norm_decay := Admission.norm_decay
  unique_solution := Admission.unique_solution
  converges := Admission.converges
}

end Admission

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let registered := powerlib.Registry.theoremNames env
  for root in registered do
    if root.getRoot == `Admission then
      logInfo m!"POWERLIB_ADMITTED_THEOREM {root}"
  let mut roots : Array Name := #[`Admission.semanticContract] ++ registered
  for (root, info) in env.constants do
    if root.getRoot == `powerlib && !info.isUnsafe then
      roots := roots.push root
  roots := roots.qsort Name.lt
  let mut previous : Option Name := none
  for root in roots do
    if previous == some root then continue
    previous := some root
    unless (env.find? root).isSome do throwError "Missing audit root {root}"
    for ax in powerlib.Search.declarationAxioms env root do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected axiom {ax}"
  logInfo "POWERLIB_KERNEL_OK"
namespace LTISynthesisBinding
open powerlib

def differentModel : LTI.AutonomousModel 2 := ⟨![![-2, 10], ![0, -1]]⟩

@[powerlib_foundation] theorem a_certificate_for_another_model_is_rejected : True := by
  fail_if_success
    have wrong : LTI.Accepted differentModel := Candidate.certificate
  trivial

end LTISynthesisBinding
