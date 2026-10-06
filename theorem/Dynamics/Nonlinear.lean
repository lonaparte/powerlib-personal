import dependencies.Mathlib
import Mathlib.Analysis.InnerProductSpace.Calculus
import theorem.Dynamics.Stability

/-! A nonlinear certificate instance in every finite dimension.
The full autonomous field is x' = -(1 + ‖x‖²) x. Its cubic growth is not bounded
by a global Lipschitz constant. The energy V(x) = ‖x‖² nevertheless proves
global existence and exponential decay for arbitrary initial states.
-/

noncomputable section
namespace powerlib.Dynamics.Nonlinear

def field {n : ℕ} (x : State n) : State n := (-(1 + ‖x‖ ^ 2)) • x

def energy {n : ℕ} (x : State n) : ℝ := ‖x‖ ^ 2

@[powerlib_foundation] theorem field_smooth (n : ℕ) :
    ContDiff ℝ 1 (@field n) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).neg.smul contDiff_id

@[powerlib_foundation] theorem energy_lie_derivative {n : ℕ} (x : State n) :
    fderiv ℝ (@energy n) x (field x) = -2 * (1 + ‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  change fderiv ℝ (fun y : State n => ‖y‖ ^ 2) x (field x) = _
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp only [smul_apply, innerSL_apply_apply]
  rw [field, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

def certificate (n : ℕ) : QuadraticDecayCertificate (@field n) (@energy n) 0 where
  lower := 1
  upper := 1
  rate := 2
  lower_pos := by norm_num
  upper_pos := by norm_num
  rate_pos := by norm_num
  smooth := contDiff_norm_sq ℝ
  equilibrium_field := by simp [field]
  equilibrium_value := by simp [energy]
  lower_bound := by intro x; simp [energy]
  upper_bound := by intro x; simp [energy]
  dissipation := by
    intro x
    rw [energy_lie_derivative]
    dsimp [energy]
    nlinarith [sq_nonneg (‖x‖ ^ 2)]

/-- Global existence and exponential stability of the full cubic field. -/
@[powerlib_domain, aesop safe apply] theorem globallyExponentiallyStable (n : ℕ) :
    GloballyExponentiallyStable (@field n) 0 :=
  (certificate n).globallyExponentiallyStable (field_smooth n)

@[powerlib_domain, aesop safe apply] theorem globallyAsymptoticallyStable {n : ℕ} (hn : 0 < n) :
    GloballyAsymptoticallyStable (@field n) 0 :=
  (certificate n).globallyAsymptoticallyStable hn (field_smooth n)

/-- Every solution, with arbitrary initial amplitude, decays at least as e⁻ᵗ. -/
@[powerlib_domain, aesop norm -1 forward (immediate := [hφ, ht])] theorem norm_bound {n : ℕ} {φ : ℝ → State n} {a b t : ℝ}
    (hφ : IsTrajectoryOn φ (@field n) a b) (ht : t ∈ Set.Icc a b) :
    ‖φ t‖ ≤ Real.exp (-(t - a)) * ‖φ a‖ := by
  simpa [certificate] using (certificate n).norm_bound hφ ht

end powerlib.Dynamics.Nonlinear
