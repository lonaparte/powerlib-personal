import theorem.NormalForm.Scalar

/-! # Power-synchronization control (PSC): quasi-static one-dimensional model and algebra

Model boundary (domain part).
* Quasi-static PSC: the converter is a voltage source `V ∠ θ` behind the line reactance
  `X = ω₁ L` to an infinite bus `V_g ∠ θ_g`, `θ_g = ω₁ t + θ_{g0}`; the line current is
  quasi-static (no inductor dynamics), so `P = P_max sin(θ − θ_g)`, `P_max = V V_g / (ω₁ L)`.
* Synchronization law `θ̇ = ω₁ + K_p (P* − P)` with constant `P*`; in the grid-angle frame
  `δ = θ − θ_g` this is the one-dimensional autonomous field `δ̇ = K_p (P* − P_max sin δ)`
  (state `δ : Dynamics.State 1`, continuous time).
* Excluded: active-resistance damping loop and inductor dynamics (the three-pole closed loop of
  T-power-synchronization-control §1.4), DC-link loop, current limiting / PLL backup, delay, PWM.
* Power is export-positive (GFM family exception).

Results: equilibria `⇔ |P*| ≤ P_max`; equilibria with `cos δ₀ > 0` are locally exponentially
stable and with `cos δ₀ < 0` unstable (`K_p, P_max > 0`), via the scalar linearization
wrappers of `theorem/NormalForm/Scalar.lean`.

Algebra (foundation): the steady-state active power, the converter-side reactive power and the
grid-side received reactive power from `S̄ = V̄ Ī*`; the active-resistance high-pass
`R_a (H(s) − 1) = −R_a s/(s + ω_b)`; PSC as pure droop with `D = 1/K_p`.

Corrections.
* T-power-synchronization-control §1.1 calls `Q₀ = (V V_g cos θ₀ − V_g²)/(ω₁ L)` the reactive
  power exported by the converter; that expression is the reactive power *received at the grid
  bus*.  The converter-side output reactive power is `(V² − V V_g cos θ₀)/(ω₁ L)`
  (`converterSide_power`, `gridSide_power`).
* The same section declares the current IN-positive (into the converter) while the line equation
  `L dĪ/dt = V̄_conv − V̄_g − jω₁ L Ī` makes `Ī` flow from the converter to the grid; here `Ī` is
  the converter-to-grid (export) current.

Source: work-sync theory/T-power-synchronization-control.md §1.1–§1.3, §1.10;
theory/T-vsg-control.md §1.7; theory/T-gfm-control.md §1.4.
-/

noncomputable section
namespace powerlib.GFM
open Set
open powerlib.Dynamics (State)
open powerlib.NormalForm (lift embed)

/-- Parameters of quasi-static PSC: gain `K_p`, set-point `P*`, maximum power `P_max`. -/
structure PSC where
  Kp : ℝ
  Pstar : ℝ
  Pmax : ℝ

namespace PSC

variable (c : PSC)

/-- Scalar right-hand side `K_p (P* − P_max sin δ)`. -/
def rhs (δ : ℝ) : ℝ := c.Kp * (c.Pstar - c.Pmax * Real.sin δ)

/-- The one-dimensional PSC field on `State 1`. -/
def field : State 1 → State 1 := lift c.rhs

@[powerlib_foundation] theorem rhs_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k c.rhs := by
  unfold rhs; fun_prop

@[powerlib_foundation] theorem hasDerivAt_rhs (δ : ℝ) :
    HasDerivAt c.rhs (-(c.Kp * c.Pmax * Real.cos δ)) δ := by
  unfold rhs
  have h := ((Real.hasDerivAt_sin δ).const_mul c.Pmax).const_sub c.Pstar |>.const_mul c.Kp
  convert h using 1
  ring

/-- Equilibria: `δ₀` is an equilibrium iff `P_max sin δ₀ = P*` (`K_p ≠ 0`). -/
@[powerlib_domain] theorem field_eq_zero_iff (hK : c.Kp ≠ 0) (δ : ℝ) :
    c.field (embed δ) = 0 ↔ c.Pmax * Real.sin δ = c.Pstar := by
  rw [field, NormalForm.lift_eq_zero_iff, rhs, mul_eq_zero, or_iff_right hK, sub_eq_zero, eq_comm]

/-- Equilibria exist iff `|P*| ≤ P_max` (`K_p ≠ 0`, `P_max > 0`). -/
@[powerlib_domain] theorem exists_equilibrium_iff (hK : c.Kp ≠ 0) (hP : 0 < c.Pmax) :
    (∃ x, c.field x = 0) ↔ |c.Pstar| ≤ c.Pmax := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← NormalForm.embed_coord x, c.field_eq_zero_iff hK] at hx
    rw [← hx, abs_mul, abs_of_pos hP]
    exact mul_le_of_le_one_right hP.le (Real.abs_sin_le_one _)
  · intro h
    have ha : |c.Pstar / c.Pmax| ≤ 1 := by rw [abs_div, abs_of_pos hP, div_le_one hP]; exact h
    refine ⟨embed (Real.arcsin (c.Pstar / c.Pmax)), (c.field_eq_zero_iff hK _).mpr ?_⟩
    rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]
    field_simp

/-- An equilibrium with `cos δ₀ > 0` is locally exponentially stable (`K_p, P_max > 0`). -/
@[powerlib_domain] theorem locallyExponentiallyStable (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    {δ₀ : ℝ} (heq : c.Pmax * Real.sin δ₀ = c.Pstar) (hcos : 0 < Real.cos δ₀) :
    Dynamics.LocallyExponentiallyStable c.field (embed δ₀) := by
  apply NormalForm.lift_locallyExponentiallyStable c.rhs_contDiff
  · simp [rhs, heq]
  · rw [(c.hasDerivAt_rhs δ₀).deriv]
    have : 0 < c.Kp * c.Pmax * Real.cos δ₀ := by positivity
    linarith

/-- An equilibrium with `cos δ₀ < 0` is unstable (`K_p, P_max > 0`). -/
@[powerlib_domain] theorem unstable (hK : 0 < c.Kp) (hP : 0 < c.Pmax) {δ₀ : ℝ}
    (heq : c.Pmax * Real.sin δ₀ = c.Pstar) (hcos : Real.cos δ₀ < 0) :
    Dynamics.Unstable c.field (embed δ₀) := by
  apply NormalForm.lift_unstable c.rhs_contDiff
  · simp [rhs, heq]
  · rw [(c.hasDerivAt_rhs δ₀).deriv]
    have : c.Kp * c.Pmax * Real.cos δ₀ < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hK hP) hcos
    linarith

/-- The loading angle `arcsin(P*/P_max)` is locally exponentially stable when
`|P*| < P_max`. -/
@[powerlib_domain] theorem locallyExponentiallyStable_arcsin (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    (h : |c.Pstar| < c.Pmax) :
    Dynamics.LocallyExponentiallyStable c.field (embed (Real.arcsin (c.Pstar / c.Pmax))) := by
  have ha : |c.Pstar / c.Pmax| < 1 := by rw [abs_div, abs_of_pos hP, div_lt_one hP]; exact h
  apply c.locallyExponentiallyStable hK hP
  · rw [Real.sin_arcsin (abs_lt.mp ha).1.le (abs_lt.mp ha).2.le]; field_simp
  · rw [Real.cos_arcsin]; apply Real.sqrt_pos.mpr
    have : (c.Pstar / c.Pmax) ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (c.Pstar / c.Pmax)]
    linarith

/-- The second equilibrium `π − arcsin(P*/P_max)` is unstable when `|P*| < P_max`. -/
@[powerlib_domain] theorem unstable_pi_sub_arcsin (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    (h : |c.Pstar| < c.Pmax) :
    Dynamics.Unstable c.field (embed (Real.pi - Real.arcsin (c.Pstar / c.Pmax))) := by
  have ha : |c.Pstar / c.Pmax| < 1 := by rw [abs_div, abs_of_pos hP, div_lt_one hP]; exact h
  apply c.unstable hK hP
  · rw [Real.sin_pi_sub, Real.sin_arcsin (abs_lt.mp ha).1.le (abs_lt.mp ha).2.le]; field_simp
  · rw [Real.cos_pi_sub, Real.cos_arcsin, neg_lt_zero]; apply Real.sqrt_pos.mpr
    have : (c.Pstar / c.Pmax) ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (c.Pstar / c.Pmax)]
    linarith

end PSC

/-! ## Algebra (foundation) -/

/-- Converter-side complex power `S̄ = V̄_conv Ī*`, `Ī = (V e^{jθ} − V_g)/(jX)` (export current):
`P = V V_g sin θ / X`, `Q_conv = (V² − V V_g cos θ)/X`. -/
@[powerlib_foundation] theorem converterSide_power (V Vg θ X : ℝ) (hX : X ≠ 0) :
    (V : ℂ) * Complex.exp (θ * Complex.I) *
        (starRingEnd ℂ) (((V : ℂ) * Complex.exp (θ * Complex.I) - (Vg : ℂ)) /
          ((X : ℂ) * Complex.I)) =
      ((V * Vg * Real.sin θ / X : ℝ) : ℂ) +
        ((V ^ 2 - V * Vg * Real.cos θ) / X : ℝ) * Complex.I := by
  rw [show V ^ 2 - V * Vg * Real.cos θ =
      V ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) - V * Vg * Real.cos θ by
    rw [Real.sin_sq_add_cos_sq]; ring]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;>
    field_simp <;> ring

/-- Grid-side received complex power `S̄_g = V̄_g Ī*`: `P = V V_g sin θ / X`,
`Q_g = (V V_g cos θ − V_g²)/X` (the note's `Q₀`). -/
@[powerlib_foundation] theorem gridSide_power (V Vg θ X : ℝ) (hX : X ≠ 0) :
    (Vg : ℂ) * (starRingEnd ℂ) (((V : ℂ) * Complex.exp (θ * Complex.I) - (Vg : ℂ)) /
          ((X : ℂ) * Complex.I)) =
      ((V * Vg * Real.sin θ / X : ℝ) : ℂ) +
        ((V * Vg * Real.cos θ - Vg ^ 2) / X : ℝ) * Complex.I := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;>
    field_simp <;> ring

/-- Active resistance: with `H(s) = ω_b/(s + ω_b)`, `R_a (H(s) − 1) = −R_a s/(s + ω_b)`. -/
@[powerlib_foundation] theorem activeResistance_highPass (Ra ωb : ℝ) (s : ℂ)
    (hs : s + (ωb : ℂ) ≠ 0) :
    (Ra : ℂ) * ((ωb : ℂ) / (s + (ωb : ℂ)) - 1) = -(Ra : ℂ) * s / (s + (ωb : ℂ)) := by
  field_simp
  ring

/-- PSC frequency law `Δω = K_p (P* − P)` is the pure droop / zero-inertia swing law
`0 = (P* − P) − D Δω` with `D = 1/K_p`. -/
@[powerlib_foundation] theorem psc_eq_droop {Kp Δω Pstar P : ℝ} (hK : Kp ≠ 0) :
    Δω = Kp * (Pstar - P) ↔ 0 = (Pstar - P) - (1 / Kp) * Δω := by
  constructor
  · intro h; rw [h]; field_simp; ring
  · intro h; field_simp at h; linarith

end powerlib.GFM
