import theorem.Flow.Certificate
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Cubic damping

Model boundary: the autonomous field `x' = -(1 + ‖x‖²) x` on `ℝⁿ`, in continuous time, without
input, delay or switching. Its cubic growth admits no global Lipschitz constant, so existence for
all time is not available from Picard–Lindelöf alone. The energy `‖x‖²` is a quadratic-decay
certificate; it proves forward completeness and global exponential stability at every initial
amplitude. -/

noncomputable section

namespace powerlib.Nonlinear.Cubic

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The cubic damping field. -/
def field (x : ℝⁿ) : ℝⁿ := (-(1 + ‖x‖ ^ 2)) • x

/-- The energy `‖x‖²`. -/
def energy (x : ℝⁿ) : ℝ := ‖x‖ ^ 2

@[powerlib_foundation] theorem field_smooth (n : ℕ) : ContDiff ℝ 1 (field (n := n)) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).neg.smul contDiff_id

/-- The field admits no global Lipschitz constant. -/
@[powerlib_domain] theorem not_lipschitzWith (hn : 0 < n) (K : NNReal) :
    ¬ LipschitzWith K (field (n := n)) := by
  intro h
  have hr : (0 : ℝ) < K + 1 := by positivity
  let x : ℝⁿ := EuclideanSpace.single ⟨0, hn⟩ ((K : ℝ) + 1)
  have hx : ‖x‖ = K + 1 := by simp [x, abs_of_pos hr]
  have h1 := h.norm_sub_le x 0
  simp only [field, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, smul_zero, sub_zero, norm_smul, norm_neg, hx] at h1
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  nlinarith [NNReal.coe_nonneg K]

/-- The Lie derivative of the energy. -/
@[powerlib_foundation] theorem energy_lie (x : ℝⁿ) :
    fderiv ℝ energy x (field x) = -2 * (1 + ‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  change fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ 2) x (field x) = _
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp only [smul_apply, innerSL_apply_apply]
  rw [field, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- The energy is a quadratic-decay certificate with rate `2`. -/
def certificate (n : ℕ) : Flow.QuadraticDecay (field (n := n)) energy 0 where
  lower := 1
  upper := 1
  rate := 2
  lower_pos := one_pos
  upper_pos := one_pos
  rate_pos := two_pos
  smooth := contDiff_norm_sq ℝ
  equilibrium := by simp [field]
  lower_bound x := by simp [energy]
  upper_bound x := by simp [energy]
  dissipation x := by
    rw [energy_lie]
    dsimp [energy]
    nlinarith [sq_nonneg (‖x‖ ^ 2)]

/-- Global exponential stability of the cubic field, with a solution through every state. -/
@[powerlib_domain] theorem globallyExponentiallyStable (n : ℕ) :
    Flow.GloballyExponentiallyStable (field (n := n)) 0 :=
  (certificate n).globallyExponentiallyStable (field_smooth n)

/-- Every attractive sentence holds for the cubic field. -/
@[powerlib_domain] theorem holds (n : ℕ) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (field (n := n)) 0 :=
  (certificate n).holds (field_smooth n) hP

/-- Every solution, at every initial amplitude, decays at least as `e^{-t}`. -/
@[powerlib_domain] theorem norm_bound {φ : ℝ → ℝⁿ} {a b t : ℝ} (hφ : IsTrajectoryOn φ field a b)
    (ht : t ∈ Set.Icc a b) : ‖φ t‖ ≤ Real.exp (-(t - a)) * ‖φ a‖ := by
  have h := (certificate n).norm_bound hφ ht
  simp only [certificate, div_one, Real.sqrt_one, one_mul, sub_zero] at h
  convert h using 3
  ring

end powerlib.Nonlinear.Cubic
