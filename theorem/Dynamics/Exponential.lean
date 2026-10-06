import dependencies.Mathlib
import theorem.Dynamics.Defs

/-! A global Lyapunov certificate for the full nonlinear vector field.
The finite-segment theorems apply to every solution and every initial amplitude.
Existence for all forward times is a separate obligation, expressed by
`ForwardComplete`; no assertion of global existence is hidden in the certificate.
-/

noncomputable section
namespace powerlib.Dynamics

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quadratic bounds on an arbitrary smooth energy and uniform strict decay.
The energy itself need not be a quadratic form, and the field need not be linear. -/
structure QuadraticDecayCertificate (f : E → E) (V : E → ℝ) (equilibrium : E) where
  lower : ℝ
  upper : ℝ
  rate : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  rate_pos : 0 < rate
  smooth : ContDiff ℝ 1 V
  equilibrium_field : f equilibrium = 0
  equilibrium_value : V equilibrium = 0
  lower_bound : ∀ x, lower * ‖x - equilibrium‖ ^ 2 ≤ V x
  upper_bound : ∀ x, V x ≤ upper * ‖x - equilibrium‖ ^ 2
  dissipation : ∀ x, (fderiv ℝ V x) (f x) ≤ -rate * V x

namespace QuadraticDecayCertificate

variable {f : E → E} {V : E → ℝ} {equilibrium : E}

/-- The chain rule connects the certificate's Lie derivative to every solution. -/
@[powerlib_foundation] theorem energy_hasDerivWithinAt
    (c : QuadraticDecayCertificate f V equilibrium)
    {φ : ℝ → E} {a b t : ℝ} (hφ : IsTrajectoryOn φ f a b) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => V (φ s))
      ((fderiv ℝ V (φ t)) (f (φ t))) (Icc a b) t := by
  exact ((c.smooth.differentiable (by norm_num)) (φ t)).hasFDerivAt.comp_hasDerivWithinAt
    t (hφ t ht)

/-- Integrating the nonlinear Lyapunov inequality yields exponential energy decay. -/
@[powerlib_domain] theorem energy_bound
    (c : QuadraticDecayCertificate f V equilibrium)
    {φ : ℝ → E} {a b t : ℝ} (hφ : IsTrajectoryOn φ f a b) (ht : t ∈ Icc a b) :
    V (φ t) ≤ Real.exp (-(c.rate * (t - a))) * V (φ a) := by
  let W : ℝ → ℝ := fun s => Real.exp (c.rate * (s - a)) * V (φ s)
  let W' : ℝ → ℝ := fun s =>
    Real.exp (c.rate * (s - a)) *
      (c.rate * V (φ s) + (fderiv ℝ V (φ s)) (f (φ s)))
  have hW : ∀ s ∈ Icc a b, HasDerivWithinAt W (W' s) (Icc a b) s := by
    intro s hs
    have hexp : HasDerivAt (fun u => Real.exp (c.rate * (u - a)))
        (Real.exp (c.rate * (s - a)) * c.rate) s := by
      simpa only [id_eq, mul_one, mul_comm] using
        (((hasDerivAt_id s).sub_const a).const_mul c.rate).exp
    convert! hexp.hasDerivWithinAt.mul (c.energy_hasDerivWithinAt hφ hs) using 1
    dsimp [W, W']
    ring
  have hmono : AntitoneOn W (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun s hs => (hW s hs).continuousWithinAt)
    · intro s hs
      exact (hW s (interior_subset hs)).mono interior_subset
    · intro s hs
      dsimp [W']
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      have hdecay := c.dissipation (φ s)
      linarith
  have hab : a ≤ b := ht.1.trans ht.2
  have hbound := hmono (left_mem_Icc.mpr hab) ht ht.1
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-(c.rate * (t - a))))
  have hcancel : Real.exp (-(c.rate * (t - a))) * Real.exp (c.rate * (t - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa [W, mul_assoc, ← mul_assoc, hcancel] using hmul

/-- The energy certificate gives a uniform bound on the full nonlinear state. -/
@[powerlib_domain] theorem norm_bound
    (c : QuadraticDecayCertificate f V equilibrium)
    {φ : ℝ → E} {a b t : ℝ} (hφ : IsTrajectoryOn φ f a b) (ht : t ∈ Icc a b) :
    ‖φ t - equilibrium‖ ≤
      Real.sqrt (c.upper / c.lower) * Real.exp (-(c.rate / 2 * (t - a))) *
        ‖φ a - equilibrium‖ := by
  have henergy := (c.lower_bound (φ t)).trans
    ((c.energy_bound hφ ht).trans
      (mul_le_mul_of_nonneg_left (c.upper_bound (φ a)) (Real.exp_nonneg _)))
  have hsquared : ‖φ t - equilibrium‖ ^ 2 ≤
      (c.upper / c.lower) * Real.exp (-(c.rate * (t - a))) *
        ‖φ a - equilibrium‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ c.lower_pos).mp
    convert! henergy using 1
    field_simp [ne_of_gt c.lower_pos]
  have hratio : 0 ≤ c.upper / c.lower := le_of_lt (div_pos c.upper_pos c.lower_pos)
  have hexp : Real.exp (-(c.rate / 2 * (t - a))) ^ 2 =
      Real.exp (-(c.rate * (t - a))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hratio, hexp] using hsquared

end QuadraticDecayCertificate
end powerlib.Dynamics
