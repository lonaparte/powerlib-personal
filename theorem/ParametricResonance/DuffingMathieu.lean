import theorem.ParametricResonance.SaturatedAmplitude
import theorem.Averaging.KBM

/-! # The Duffing–Mathieu oscillator: first-order averaging to the cubic amplitude equation

The damped Duffing–Mathieu oscillator `ẍ + 2ζω₀ ẋ + ω₀²(1 + ε cos Ωt) x + γ x³ = 0` is the
simplest model of a parametric oscillation that saturates. Writing it in van der Pol coordinates
in the frame rotating at half the pump frequency `ν = Ω/2` is an exact change of variables; the
average of the resulting standard-form field over one period `T = 2π/ν` is computed exactly and is
the cubic 2:1 amplitude equation of `theorem/ParametricResonance/SaturatedAmplitude.lean`, with a
pure frequency-shift nonlinearity (`η = 0`). Its phase-locked states give the saturated amplitude
of the parametric oscillation, hardening (`γ > 0`) or softening (`γ < 0`).

Scope.
* The oscillator in coefficient form `ẍ + b ẋ + (k₀ + k₁ cos 2νt) x + γ x³ = u(t)` (`accel`, real
  coefficients, `ν ≠ 0`, an input `u` only in `hasDerivAt_vdp`); the physical form is
  `b = 2ζω₀`, `k₀ = ω₀²`, `k₁ = εω₀²` (`averaged_physical`, `saturated_states`,
  `saturated_stable_iff`). Continuous time, scalar position `x`, velocity `ẋ`.
* Van der Pol amplitude `z = e^{−jνt}(x − j ẋ/ν)`, i.e. `x = Re(z e^{jνt})`,
  `ẋ = −ν Im(z e^{jνt})` (`vdp`, `pos`, `vel`): `x = a cos(νt + φ)` for `z = a e^{jφ}`. The
  standard form is `ż = vdpField b k₀ k₁ γ ν z t` (`ż = −(j/ν)(ẍ + ν²x) e^{−jνt}`).
* First-order averaging is KBM's period average `Averaging.fieldAverage` over `T = 2π/ν`
  (`theorem/Averaging/KBM.lean`). It is of first order when damping, detuning `ν² − k₀`, pump and
  `γ x²` are all of order `ε`, i.e. for an amplitude of order `√ε` (`vdpField_scaled`: then
  `ẇ = ε vdpField … w t` with `z = √ε w`, the standard form `ẋ = ε f(x, t)` of
  `Averaging.kbm_first_order`).
* The averaged equation and its phase-locked states are exact statements. The closeness of the
  oscillator to the averaged equation is proved on bounded sets: KBM (`Averaging.kbm_first_order`)
  needs a global Lipschitz bound, so the field is read through the clamp `clampC` onto a square
  containing the averaged solution with margin one (`cutField`, `cutField_hyp`); global solutions
  of the clamped fields (`exists_global_solution`) and uniqueness (Mathlib's
  `ODE_solution_unique_of_mem_Icc_right`) transfer the estimate to every solution of the
  unclamped field on `[0, L/ε]` (`averaging_valid`, `oscillator_averaging`). Only averaged
  solutions that stay in a disc `|z̄| ≤ R` up to `L/ε` are covered (e.g. a phase-locked state),
  and the estimate is the KBM `O(ε)` on the time scale `1/ε`, not uniform in time.
* Generic mathematics, no model family.

Source: first-order averaging of the parametrically excited Duffing oscillator (Nayfeh–Mook,
*Nonlinear Oscillations*, Ch. 5, parametrically excited systems: the Mathieu–Duffing equation,
the method of averaging, the frequency–response equation and its stability; Landau–Lifshitz,
*Mechanics* §27, §29); the KBM theorem `Averaging.kbm_first_order` and its average
`Averaging.fieldAverage` (work-sync theory/T-averaging-method.md §1.1–1.3); the cubic amplitude
equation `Saturation.ampField`.

Sharpenings.
* `theorem/Averaging/KBM.lean` lists the domain-restricted KBM theorem (averaged solution in a
  compact set with margin) as not formalized; for the van der Pol field it is obtained here from
  the global theorem by the clamp (`averaging_valid`).
* The exact averaged coefficients carry `ν` where the usual first-order formulas carry `ω₀`:
  `Δ = (ν² − ω₀²)/(2ν)` (`≈ Ω/2 − ω₀`), `c = j εω₀²/(4ν)` (`≈ j εω₀/4`), `β = 3γ/(8ν)`
  (`≈ 3γ/(8ω₀)`), `σ = ζω₀`; the pump coefficient has the phase `j`.
* Existence of a saturated state needs `|ε| ω₀ ≥ 4ζν` (`|ε| ≥ 4ζ` at `Ω = 2ω₀`), with
  `3γa² = 4(ν² − ω₀²) ± 2ω₀ √(ε²ω₀² − 16ζ²ν²)`; the stable state is the larger amplitude,
  `γ(3γa² − 4(ν² − ω₀²)) > 0` (`saturated_stable_iff`). By `Saturation.shift_bistable` the
  response is bistable below the linear threshold exactly on the side `γ(ν² − ω₀²) > 0`
  (hardening: pump above `2ω₀`; softening: below).

Results.
* `pos`, `vel`, `vdp`, `accel`, `vdpField`, `vdp_mul_exp`, `pos_vdp`, `vel_vdp` — the van der Pol
  coordinates and the standard-form field.
* `hasDerivAt_vdp` — the exact transformation: a solution of the (forced) oscillator gives a
  solution of `ż = vdpField z t − (j/ν) u(t) e^{−jνt}`.
* `vdpField_eq` — the harmonic decomposition: the non-rotating part of `vdpField` is exactly
  `ampField (b/2) ((ν² − k₀)/(2ν)) (j k₁/(4ν)) 0 (3γ/(8ν))`, the rest rotates at `2ν`, `4ν`.
* `fieldAverage_vdpField`, `averaged_physical` — the exact period average is that cubic
  amplitude field; for the physical form `σ = ζω₀`, `Δ = (ν² − ω₀²)/(2ν)`, `c = jεω₀²/(4ν)`,
  `η = 0`, `β = 3γ/(8ν)`.
* `vdpField_smul`, `vdpField_ofReal_mul`, `vdpField_scaled` — coefficients of order `ε` and an
  amplitude of order `√ε` give the first-order standard form.
* `saturated_states`, `saturated_stable_iff` — the saturated amplitudes and which one is stable.
* `abs_sin_sub_cubic_le` — `|sin x − (x − x³/6)| ≤ |x|⁵/120`: a sine restoring force is a softening
  Duffing force `γ = −k/6` up to a fifth-order remainder.
* `clampC`, `clampC_of_norm_le`, `norm_clampC_le`, `norm_clampC_sub_le`, `continuous_clampC` — the
  coordinate clamp (identity on the disc of radius `ρ`, `1`-Lipschitz, bounded by `2ρ`).
* `norm_vdpField_sub_le`, `vdpField_zero`, `continuous_vdpField`, `vdpField_periodic` — the field
  is `lipConst`-Lipschitz on discs, vanishes at `0`, is continuous and `2π/ν`-periodic.
* `cutField`, `cutField_hyp`, `lipConst`, `kbmConst` — the clamped field satisfies the hypotheses
  of `Averaging.kbm_first_order`; its error constant.
* `exists_global_solution` — a continuous field, Lipschitz in the state uniformly in time, has a
  solution on all of `ℝ` from every initial state.
* `averaging_valid` — **rigorous first-order averaging on a bounded set**: every solution of the
  standard form `ż = ε vdpField … z t` stays within `kbmConst · ε` of the averaged solution on
  `[0, L/ε]` while the latter stays in `|z̄| ≤ R` (`kbmConst · ε ≤ 1`).
* `oscillator_averaging` — for `ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + γx³ = 0`:
  `|x(t) − √ε Re(w̄(t) e^{jνt})| ≤ √ε · kbmConst · ε` on `[0, L/ε]`, `w̄` the averaged amplitude.
-/

noncomputable section
namespace powerlib.ParametricResonance.DuffingMathieu

open Complex Set Filter Topology
open Saturation (ampField ampSystem)

/-! ## The oscillator and its van der Pol coordinates -/

/-- The position `x = Re(z e^{jνt})` carried by the van der Pol amplitude `z` at time `t`. -/
def pos (ν : ℝ) (z : ℂ) (t : ℝ) : ℝ := (z * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re

/-- The velocity `ẋ = −ν Im(z e^{jνt})` carried by the van der Pol amplitude `z` at time `t`. -/
def vel (ν : ℝ) (z : ℂ) (t : ℝ) : ℝ := -ν * (z * Complex.exp (((ν * t : ℝ) : ℂ) * I)).im

/-- The van der Pol amplitude `z = e^{−jνt} (x − j ẋ/ν)` of the state `(x, ẋ)` at time `t`. -/
def vdp (ν t x x' : ℝ) : ℂ :=
  Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) * ((x : ℂ) - ((x' / ν : ℝ) : ℂ) * I)

/-- The acceleration of the oscillator `ẍ + b ẋ + (k₀ + k₁ cos 2νt) x + γ x³ = 0`. -/
def accel (b k₀ k₁ γ ν t x x' : ℝ) : ℝ :=
  -(b * x' + (k₀ + k₁ * Real.cos (2 * ν * t)) * x + γ * x ^ 3)

/-- The oscillator in van der Pol coordinates (standard form): `ż = −(j/ν)(ẍ + ν² x) e^{−jνt}`,
with `x, ẋ, ẍ` read off `z` (`pos`, `vel`, `accel`). -/
def vdpField (b k₀ k₁ γ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  -(I / ν) * ((accel b k₀ k₁ γ ν t (pos ν z t) (vel ν z t) + ν ^ 2 * pos ν z t : ℝ) : ℂ) *
    Complex.exp (-(((ν * t : ℝ) : ℂ) * I))

variable {b k₀ k₁ γ ν : ℝ}

@[tmio M, powerlib_foundation] theorem vdp_mul_exp (ν t x x' : ℝ) :
    vdp ν t x x' * Complex.exp (((ν * t : ℝ) : ℂ) * I) = (x : ℂ) - ((x' / ν : ℝ) : ℂ) * I := by
  rw [vdp, mul_comm, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- The van der Pol amplitude carries the position: `Re(z e^{jνt}) = x`. -/
@[tmio M, powerlib_foundation] theorem pos_vdp (ν t x x' : ℝ) : pos ν (vdp ν t x x') t = x := by
  rw [pos, vdp_mul_exp]; simp

/-- The van der Pol amplitude carries the velocity: `−ν Im(z e^{jνt}) = ẋ`. -/
@[tmio M, powerlib_foundation] theorem vel_vdp (hν : ν ≠ 0) (t x x' : ℝ) :
    vel ν (vdp ν t x x') t = x' := by
  rw [vel, vdp_mul_exp]; simp; field_simp

/-- **The exact van der Pol transformation.** If `x` solves the forced oscillator
`ẍ + b ẋ + (k₀ + k₁ cos 2νt) x + γ x³ = u(t)` (with `ẋ = x'`), its van der Pol amplitude
`z(t) = e^{−jνt}(x − j ẋ/ν)` solves `ż = vdpField b k₀ k₁ γ ν z t − (j/ν) u(t) e^{−jνt}`; for
`u = 0` this is the standard form `ż = vdpField b k₀ k₁ γ ν z t`. No approximation is made. -/
@[tmio M, powerlib_foundation] theorem hasDerivAt_vdp (hν : ν ≠ 0) {x x' u : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x' (accel b k₀ k₁ γ ν t (x t) (x' t) + u t) t) (t : ℝ) :
    HasDerivAt (fun t => vdp ν t (x t) (x' t))
      (vdpField b k₀ k₁ γ ν (vdp ν t (x t) (x' t)) t -
        I / ν * (u t : ℂ) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have h1 : HasDerivAt (fun t : ℝ => ((ν * t : ℝ) : ℂ)) (ν : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul ν).ofReal_comp; simpa using this
  have h2 := ((h1.mul_const I).neg).cexp
  have h3 : HasDerivAt (fun t => (x t : ℂ) - ((x' t / ν : ℝ) : ℂ) * I)
      ((x' t : ℂ) - (((accel b k₀ k₁ γ ν t (x t) (x' t) + u t) / ν : ℝ) : ℂ) * I) t :=
    ((hx t).ofReal_comp).sub ((((hx' t).div_const ν).ofReal_comp).mul_const I)
  convert h2.mul h3 using 1
  · funext s; simp [vdp]
  rw [vdpField, pos_vdp, vel_vdp hν, Pi.neg_apply]
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- **A sine restoring force is a softening Duffing force.** `sin x = x − x³/6 + R(x)` with
`|R(x)| ≤ |x|⁵/120` for every real `x`: a restoring torque `k sin x` is the Duffing force
`k x − (k/6) x³` up to `|k| |x|⁵/120`. -/
@[tmio T, powerlib_foundation] theorem abs_sin_sub_cubic_le (x : ℝ) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 120 := by
  -- `1 − t²/2 + t⁴/24 − cos t ≥ 0` and `t − t³/6 + t⁵/120 − sin t ≥ 0` for `t ≥ 0`
  have hcos : ∀ t : ℝ, 0 ≤ t → Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
    let m (t : ℝ) : ℝ := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
    have hderiv (t : ℝ) : deriv m t = Real.sin t - (t - t ^ 3 / 6) := by
      simp (disch := fun_prop) [m]; ring
    have hmono : MonotoneOn m (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
      intro t ht
      rw [interior_Ici] at ht
      rw [hderiv]
      linarith [Real.sin_ge_sub_cube (le_of_lt ht)]
    intro t ht
    have := hmono Set.self_mem_Ici ht ht
    simp only [m] at this
    simp at this
    linarith
  have hsin : ∀ t : ℝ, 0 ≤ t → Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
    let k (t : ℝ) : ℝ := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
    have hderiv (t : ℝ) : deriv k t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
      simp (disch := fun_prop) [k]; ring
    have hmono : MonotoneOn k (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
      intro t ht
      rw [interior_Ici] at ht
      rw [hderiv]
      linarith [hcos t (le_of_lt ht)]
    intro t ht
    have := hmono Set.self_mem_Ici ht ht
    simp only [k] at this
    simp at this
    linarith
  have hpos : ∀ t : ℝ, 0 ≤ t → |Real.sin t - (t - t ^ 3 / 6)| ≤ t ^ 5 / 120 := by
    intro t ht
    rw [abs_le]
    exact ⟨by linarith [Real.sin_ge_sub_cube ht, pow_nonneg ht 5], by linarith [hsin t ht]⟩
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact hpos x hx
  · have := hpos (-x) (by linarith)
    rw [Real.sin_neg, abs_of_nonpos hx] at *
    rw [show Real.sin x - (x - x ^ 3 / 6) = -(-Real.sin x - (-x - (-x) ^ 3 / 6)) by ring,
      abs_neg]
    exact this

/-! ## The exact average over one period `T = 2π/ν` -/

@[tmio T, powerlib_foundation] private theorem exp_nat_mul_phase (ν t : ℝ) (n : ℕ) :
    Complex.exp ((((n : ℝ) * (ν * t) : ℝ) : ℂ) * I) = Complex.exp (((ν * t : ℝ) : ℂ) * I) ^ n := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- **The harmonic decomposition of the van der Pol field.** With `w = e^{jνt}`:
`vdpField z t = ampField (b/2) ((ν² − k₀)/(2ν)) (j k₁/(4ν)) 0 (3γ/(8ν)) z
  + a₂ w² + a₋₂ w⁻² + a₋₄ w⁻⁴`, with the explicit coefficients below: the resonant
(non-rotating) part is exactly the cubic amplitude field, all other terms rotate at `2ν` or
`4ν`. -/
@[tmio M, powerlib_foundation] theorem vdpField_eq (hν : ν ≠ 0) (z : ℂ) (t : ℝ) :
    vdpField b k₀ k₁ γ ν z t =
      ampField (b / 2) ((ν ^ 2 - k₀) / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
          (3 * γ / (8 * ν)) z +
        I / ν * (k₁ * z / 4 + γ * z ^ 3 / 8) * Complex.exp (((2 * ν * t : ℝ) : ℂ) * I) +
        (-(I / ν) * ((ν ^ 2 - k₀) * (starRingEnd ℂ) z / 2 - k₁ * z / 4 -
            3 * γ * z * (starRingEnd ℂ) z ^ 2 / 8) + b / 2 * (starRingEnd ℂ) z) *
          Complex.exp (-(((2 * ν * t : ℝ) : ℂ) * I)) +
        I / ν * (k₁ * (starRingEnd ℂ) z / 4 + γ * (starRingEnd ℂ) z ^ 3 / 8) *
          Complex.exp (-(((4 * ν * t : ℝ) : ℂ) * I)) := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  set w := Complex.exp (((ν * t : ℝ) : ℂ) * I) with hw
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hconj : (starRingEnd ℂ) w = w⁻¹ := by
    rw [hw, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_neg]
    ring_nf
  have hX : ((pos ν z t : ℝ) : ℂ) = (z * w + (starRingEnd ℂ) z * w⁻¹) / 2 := by
    rw [pos, Complex.re_eq_add_conj, map_mul, hconj]
  have hX' : ((vel ν z t : ℝ) : ℂ) = ν * I * (z * w - (starRingEnd ℂ) z * w⁻¹) / 2 := by
    rw [vel, Complex.ofReal_mul, Complex.ofReal_neg, Complex.im_eq_sub_conj, map_mul, hconj]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  have hC : ((Real.cos (2 * ν * t) : ℝ) : ℂ) = (w ^ 2 + (w ^ 2)⁻¹) / 2 := by
    rw [Complex.ofReal_cos, ← exp_nat_mul_phase, ← Complex.exp_neg]
    rw [eq_div_iff (two_ne_zero), mul_comm, Complex.two_cos]
    push_cast
    ring_nf
  have h2 : Complex.exp (((2 * ν * t : ℝ) : ℂ) * I) = w ^ 2 := by
    rw [← exp_nat_mul_phase]; push_cast; ring_nf
  have h2' : Complex.exp (-(((2 * ν * t : ℝ) : ℂ) * I)) = (w ^ 2)⁻¹ := by
    rw [Complex.exp_neg, h2]
  have h4' : Complex.exp (-(((4 * ν * t : ℝ) : ℂ) * I)) = (w ^ 4)⁻¹ := by
    rw [Complex.exp_neg, ← exp_nat_mul_phase]; push_cast; ring_nf
  have h1' : Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) = w⁻¹ := by rw [Complex.exp_neg]
  have hn : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.mul_conj]
  rw [h2, h2', h4']
  simp only [vdpField, accel, ampField, slowFlowField]
  push_cast at hC h1' ⊢
  rw [hX, hX', hC, h1', hn]
  field_simp
  ring_nf
  simp only [I_sq]
  ring


@[tmio T, powerlib_foundation] private theorem integral_exp_harmonic (hν : 0 < ν) (k : ℤ)
    (hk : k ≠ 0) (r : ℝ) (hr : r = k * ν) :
    ∫ s in (0 : ℝ)..(2 * Real.pi / ν), Complex.exp (((r * s : ℝ) : ℂ) * I) = 0 := by
  have hc : (r : ℂ) * I ≠ 0 :=
    mul_ne_zero (by rw [hr]; exact_mod_cast mul_ne_zero (Int.cast_ne_zero.mpr hk) hν.ne') I_ne_zero
  have e : (fun s : ℝ => Complex.exp (((r * s : ℝ) : ℂ) * I)) =
      fun s : ℝ => Complex.exp (((r : ℂ) * I) * s) := by
    funext s; congr 1; push_cast; ring
  rw [e, integral_exp_mul_complex hc]
  have h1 : Complex.exp (((r : ℂ) * I) * ((2 * Real.pi / ν : ℝ) : ℂ)) = 1 := by
    have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    rw [show ((r : ℂ) * I) * ((2 * Real.pi / ν : ℝ) : ℂ) = k * (2 * Real.pi * I) by
      rw [hr]; push_cast; field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h1]; simp

/-- **The exact first-order average of the Duffing–Mathieu oscillator.** Over one period
`T = 2π/ν` of the van der Pol field (KBM's `Averaging.fieldAverage`), the average is exactly the
cubic amplitude field with `σ = b/2`, `Δ = (ν² − k₀)/(2ν)`, `c = j k₁/(4ν)`, `η = 0`,
`β = 3γ/(8ν)`. -/
@[tmio M, powerlib_foundation] theorem fieldAverage_vdpField (hν : 0 < ν) (z : ℂ) :
    Averaging.fieldAverage (vdpField b k₀ k₁ γ ν) (2 * Real.pi / ν) z =
      ampField (b / 2) ((ν ^ 2 - k₀) / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * γ / (8 * ν)) z := by
  set T := 2 * Real.pi / ν with hTdef
  have hT : 0 < T := by positivity
  set A := ampField (b / 2) ((ν ^ 2 - k₀) / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
    (3 * γ / (8 * ν)) z
  set c₂ := I / ν * (k₁ * z / 4 + γ * z ^ 3 / 8)
  set cm₂ := -(I / ν) * ((ν ^ 2 - k₀) * (starRingEnd ℂ) z / 2 - k₁ * z / 4 -
    3 * γ * z * (starRingEnd ℂ) z ^ 2 / 8) + b / 2 * (starRingEnd ℂ) z
  set cm₄ := I / ν * (k₁ * (starRingEnd ℂ) z / 4 + γ * (starRingEnd ℂ) z ^ 3 / 8)
  have e : (fun s => vdpField b k₀ k₁ γ ν z s) = fun s =>
      A + c₂ * Complex.exp ((((2 * ν) * s : ℝ) : ℂ) * I) +
        cm₂ * Complex.exp ((((-2 * ν) * s : ℝ) : ℂ) * I) +
        cm₄ * Complex.exp ((((-4 * ν) * s : ℝ) : ℂ) * I) := by
    funext s
    rw [vdpField_eq hν.ne' z s]
    congr 3 <;> push_cast <;> ring_nf
  have hc : ∀ r : ℝ, Continuous fun s : ℝ => Complex.exp (((r * s : ℝ) : ℂ) * I) :=
    fun r => by fun_prop
  have i2 := integral_exp_harmonic hν 2 (by norm_num) (2 * ν) (by push_cast; ring)
  have i2' := integral_exp_harmonic hν (-2) (by norm_num) (-2 * ν) (by push_cast; ring)
  have i4' := integral_exp_harmonic hν (-4) (by norm_num) (-4 * ν) (by push_cast; ring)
  rw [Averaging.fieldAverage, e, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, i2, i2', i4']
  · simp only [mul_zero, add_zero, sub_zero]
    rw [smul_smul, inv_mul_cancel₀ hT.ne', one_smul]
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- **The averaged amplitude equation of `ẍ + 2ζω₀ ẋ + ω₀²(1 + ε cos 2νt) x + γ x³ = 0`**: the
cubic amplitude field with `σ = ζω₀`, `Δ = (ν² − ω₀²)/(2ν)` (`≈ ν − ω₀`), `c = j ε ω₀²/(4ν)`
(`≈ j εω₀/4`), `η = 0`, `β = 3γ/(8ν)` (`≈ 3γ/(8ω₀)`). -/
@[tmio M, powerlib_foundation] theorem averaged_physical (hν : 0 < ν) (ζ ω₀ ε : ℝ) (z : ℂ) :
    Averaging.fieldAverage (vdpField (2 * ζ * ω₀) (ω₀ ^ 2) (ε * ω₀ ^ 2) γ ν) (2 * Real.pi / ν) z =
      ampField (ζ * ω₀) ((ν ^ 2 - ω₀ ^ 2) / (2 * ν)) (I * ((ε * ω₀ ^ 2 / (4 * ν) : ℝ) : ℂ)) 0
        (3 * γ / (8 * ν)) z := by
  rw [fieldAverage_vdpField hν]; congr 1; ring

/-! ## The scalings that make the field of first order -/

/-- Coefficients of order `ε` give a field of order `ε`: with damping `εb`, stiffness
`ν² − εd`, pump `εk₁` and cubic coefficient `εγ`, `vdpField = ε · vdpField b (ν² − d) k₁ γ ν`. -/
@[tmio M, powerlib_foundation] theorem vdpField_smul (ε b d k₁ γ ν : ℝ) (z : ℂ) (t : ℝ) :
    vdpField (ε * b) (ν ^ 2 - ε * d) (ε * k₁) (ε * γ) ν z t =
      (ε : ℂ) * vdpField b (ν ^ 2 - d) k₁ γ ν z t := by
  simp only [vdpField, accel]; push_cast; ring

/-- Amplitude scaling: `vdpField (r w) = r · vdpField` with the cubic coefficient `r²γ`. -/
@[tmio M, powerlib_foundation] theorem vdpField_ofReal_mul (b k₀ k₁ γ ν r : ℝ) (w : ℂ) (t : ℝ) :
    vdpField b k₀ k₁ γ ν ((r : ℂ) * w) t = (r : ℂ) * vdpField b k₀ k₁ (r ^ 2 * γ) ν w t := by
  simp only [vdpField, accel, pos, vel, mul_assoc, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  push_cast; ring

/-- **The weakly nonlinear scaling.** Damping, detuning and pump of order `ε` and an amplitude of
order `√ε` (`z = √ε w`, so `x = √ε Re(w e^{jνt})`) with a fixed cubic coefficient `γ`: the
scaled amplitude obeys `ẇ = ε vdpField b (ν² − d) k₁ γ ν w t`, the standard form of first-order
averaging (`Averaging.kbm_first_order`). -/
@[tmio M, powerlib_foundation] theorem vdpField_scaled {ε : ℝ} (hε : 0 ≤ ε) (b d k₁ γ ν : ℝ)
    (w : ℂ) (t : ℝ) :
    vdpField (ε * b) (ν ^ 2 - ε * d) (ε * k₁) γ ν ((√ε : ℂ) * w) t =
      (√ε : ℂ) * ((ε : ℂ) * vdpField b (ν ^ 2 - d) k₁ γ ν w t) := by
  rw [vdpField_ofReal_mul, Real.sq_sqrt hε, vdpField_smul]

/-! ## The saturated amplitude of the parametric oscillation -/

/-- **Saturated amplitudes of the Duffing–Mathieu oscillator** (first-order averaged level):
a phase-locked state of the averaged equation with `a² = A > 0` exists iff
`16ζ²ν² ≤ ε²ω₀²` and `3γA = 4(ν² − ω₀²) ± 2ω₀ √(ε²ω₀² − 16ζ²ν²)`; at `Ω = 2ν = 2ω₀` the
existence threshold is `|ε| ≥ 4ζ`. -/
@[tmio M, powerlib_foundation] theorem saturated_states (hν : 0 < ν) {ω₀ : ℝ} (hω : 0 < ω₀)
    (hγ : γ ≠ 0) (ζ ε : ℝ) {A : ℝ} (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ Averaging.fieldAverage (vdpField (2 * ζ * ω₀) (ω₀ ^ 2) (ε * ω₀ ^ 2) γ ν)
        (2 * Real.pi / ν) z = 0) ↔
      16 * ζ ^ 2 * ν ^ 2 ≤ ε ^ 2 * ω₀ ^ 2 ∧
        (3 * γ * A = 4 * (ν ^ 2 - ω₀ ^ 2) + 2 * ω₀ * √(ε ^ 2 * ω₀ ^ 2 - 16 * ζ ^ 2 * ν ^ 2) ∨
          3 * γ * A = 4 * (ν ^ 2 - ω₀ ^ 2) - 2 * ω₀ * √(ε ^ 2 * ω₀ ^ 2 - 16 * ζ ^ 2 * ν ^ 2)) := by
  simp_rw [averaged_physical hν]
  have hβ : 3 * γ / (8 * ν) ≠ 0 := div_ne_zero (mul_ne_zero three_ne_zero hγ) (by positivity)
  rw [Saturation.shift_states hβ hA]
  have hc : ‖I * ((ε * ω₀ ^ 2 / (4 * ν) : ℝ) : ℂ)‖ ^ 2 = (ε * ω₀ ^ 2 / (4 * ν)) ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hc]
  set X := ε ^ 2 * ω₀ ^ 2 - 16 * ζ ^ 2 * ν ^ 2 with hX
  have hXe : (ε * ω₀ ^ 2 / (4 * ν)) ^ 2 - (ζ * ω₀) ^ 2 = (ω₀ / (4 * ν)) ^ 2 * X := by
    rw [hX]; field_simp; ring
  have hs : √((ε * ω₀ ^ 2 / (4 * ν)) ^ 2 - (ζ * ω₀) ^ 2) = ω₀ / (4 * ν) * √X := by
    rw [hXe, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hs]
  have hle : (ζ * ω₀) ^ 2 ≤ (ε * ω₀ ^ 2 / (4 * ν)) ^ 2 ↔ 16 * ζ ^ 2 * ν ^ 2 ≤ ε ^ 2 * ω₀ ^ 2 := by
    rw [← sub_nonneg, hXe, hX]
    constructor
    · intro h
      have hp : 0 < (ω₀ / (4 * ν)) ^ 2 := by positivity
      nlinarith
    · intro h; exact mul_nonneg (sq_nonneg _) (by linarith)
  rw [hle]
  refine and_congr_right fun _ => ?_
  have e : ∀ e : ℝ,
      (A = ((ν ^ 2 - ω₀ ^ 2) / (2 * ν) + e * (ω₀ / (4 * ν) * √X)) / (3 * γ / (8 * ν)) ↔
      3 * γ * A = 4 * (ν ^ 2 - ω₀ ^ 2) + e * (2 * ω₀ * √X)) := by
    intro e
    rw [eq_div_iff hβ]
    constructor <;> intro h
    · field_simp at h; linarith
    · field_simp; linarith
  have e1 := e 1
  have e2 := e (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e1 e2
  rw [e1, e2]

/-- **Which saturated state is stable** (`ζ > 0`): a nontrivial steady state of the averaged
Duffing–Mathieu equation is locally exponentially stable iff `γ(3γa² − 4(ν² − ω₀²)) > 0`, and a
saddle iff `γ(3γa² − 4(ν² − ω₀²)) < 0`: for a hardening spring (`γ > 0`) the upper root
`3γa² = 4(ν² − ω₀²) + 2ω₀√(ε²ω₀² − 16ζ²ν²)`, for a softening spring (`γ < 0`) the root
`3γa² = 4(ν² − ω₀²) − 2ω₀√(…)` (the larger amplitude in both cases). -/
@[tmio TM, powerlib_foundation] theorem saturated_stable_iff (hν : 0 < ν) {ζ ω₀ ε : ℝ}
    (hζ : 0 < ζ) (hω : 0 < ω₀) {z : ℂ}
    (hz : ampField (ζ * ω₀) ((ν ^ 2 - ω₀ ^ 2) / (2 * ν)) (I * ((ε * ω₀ ^ 2 / (4 * ν) : ℝ) : ℂ)) 0
      (3 * γ / (8 * ν)) z = 0) (hz0 : z ≠ 0) :
    (LocallyExponentiallyStable (ampSystem (ζ * ω₀) ((ν ^ 2 - ω₀ ^ 2) / (2 * ν))
        (I * ((ε * ω₀ ^ 2 / (4 * ν) : ℝ) : ℂ)) 0 (3 * γ / (8 * ν))) (toReal z) ↔
        0 < γ * (3 * γ * ‖z‖ ^ 2 - 4 * (ν ^ 2 - ω₀ ^ 2))) ∧
      (γ * (3 * γ * ‖z‖ ^ 2 - 4 * (ν ^ 2 - ω₀ ^ 2)) < 0 →
        Unstable (ampSystem (ζ * ω₀) ((ν ^ 2 - ω₀ ^ 2) / (2 * ν))
          (I * ((ε * ω₀ ^ 2 / (4 * ν) : ℝ) : ℂ)) 0 (3 * γ / (8 * ν))) (toReal z)) := by
  obtain ⟨h1, h2⟩ := Saturation.shift_stable_iff (mul_pos hζ hω) hz hz0
  have e : 3 * γ / (8 * ν) * (3 * γ / (8 * ν) * ‖z‖ ^ 2 - (ν ^ 2 - ω₀ ^ 2) / (2 * ν)) =
      3 / (64 * ν ^ 2) * (γ * (3 * γ * ‖z‖ ^ 2 - 4 * (ν ^ 2 - ω₀ ^ 2))) := by
    field_simp; ring
  have hp : 0 < 3 / (64 * ν ^ 2) := by positivity
  rw [e] at h1 h2
  refine ⟨h1.trans (mul_pos_iff_of_pos_left hp), fun h => h2 ?_⟩
  exact mul_neg_of_pos_of_neg hp h


/-! ## Validity of the averaged equation on a bounded set (KBM with a cut-off) -/

section Validity

/-- The coordinate clamp of `ℂ` onto the square `|Re z|, |Im z| ≤ ρ`. -/
def clampC (ρ : ℝ) (z : ℂ) : ℂ := ⟨max (-ρ) (min ρ z.re), max (-ρ) (min ρ z.im)⟩

@[tmio T, powerlib_foundation] theorem clampC_of_norm_le {ρ : ℝ} {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    clampC ρ z = z := by
  have h1 := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have h2 := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  apply Complex.ext <;> simp [clampC, h1.1, h1.2, h2.1, h2.2]

@[tmio T, powerlib_foundation] theorem norm_clampC_le {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℂ) :
    ‖clampC ρ z‖ ≤ 2 * ρ := by
  have hc : ∀ x : ℝ, |max (-ρ) (min ρ x)| ≤ ρ := fun x =>
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  calc ‖clampC ρ z‖ ≤ |(clampC ρ z).re| + |(clampC ρ z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ρ + ρ := add_le_add (hc z.re) (hc z.im)
    _ = 2 * ρ := by ring

@[tmio T, powerlib_foundation] private theorem abs_clip_sub_le (ρ x y : ℝ) :
    |max (-ρ) (min ρ x) - max (-ρ) (min ρ y)| ≤ |x - y| := by
  have h1 : |max (min ρ x) (-ρ) - max (min ρ y) (-ρ)| ≤ |min ρ x - min ρ y| :=
    abs_max_sub_max_le_abs _ _ _
  have h2 : |min ρ x - min ρ y| ≤ max |ρ - ρ| |x - y| := abs_min_sub_min_le_max _ _ _ _
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h2
  rw [max_comm (-ρ) (min ρ x), max_comm (-ρ) (min ρ y)]
  exact h1.trans h2

@[tmio T, powerlib_foundation] theorem norm_clampC_sub_le (ρ : ℝ) (z w : ℂ) :
    ‖clampC ρ z - clampC ρ w‖ ≤ ‖z - w‖ := by
  have hre := abs_clip_sub_le ρ z.re w.re
  have him := abs_clip_sub_le ρ z.im w.im
  have h : ‖clampC ρ z - clampC ρ w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, clampC]
    have e1 := sq_le_sq.mpr hre
    have e2 := sq_le_sq.mpr him
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

@[tmio T, powerlib_foundation] theorem continuous_clampC (ρ : ℝ) : Continuous (clampC ρ) := by
  have h : clampC ρ = fun z : ℂ => Complex.equivRealProdCLM.symm
      (max (-ρ) (min ρ z.re), max (-ρ) (min ρ z.im)) := by
    funext z; apply Complex.ext <;> simp [clampC]
  rw [h]
  exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)

/-! ### Bounds on the van der Pol field -/

/-- The restoring residual `ẍ + ν² x` of the oscillator, read off `z`. -/
@[tmio M, powerlib_foundation] private theorem residual_eq (z : ℂ) (t : ℝ) :
    accel b k₀ k₁ γ ν t (pos ν z t) (vel ν z t) + ν ^ 2 * pos ν z t =
      (ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) * pos ν z t - b * vel ν z t -
        γ * pos ν z t ^ 3 := by
  simp only [accel]; ring

@[tmio T, powerlib_foundation] private theorem abs_pos_sub_le (ν : ℝ) (z w : ℂ) (t : ℝ) :
    |pos ν z t - pos ν w t| ≤ ‖z - w‖ := by
  have : pos ν z t - pos ν w t = ((z - w) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re := by
    simp only [pos, sub_mul, Complex.sub_re]
  rw [this]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem abs_pos_le (ν : ℝ) (z : ℂ) (t : ℝ) :
    |pos ν z t| ≤ ‖z‖ := by
  have := abs_pos_sub_le ν z 0 t
  simpa [pos] using this

@[tmio T, powerlib_foundation] private theorem abs_vel_sub_le {ν : ℝ} (hν : 0 ≤ ν) (z w : ℂ)
    (t : ℝ) : |vel ν z t - vel ν w t| ≤ ν * ‖z - w‖ := by
  have : vel ν z t - vel ν w t = -ν * ((z - w) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).im := by
    simp only [vel, sub_mul, Complex.sub_im]; ring
  rw [this, abs_mul, abs_neg, abs_of_nonneg hν]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans ?_) hν
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem norm_vdpField_sub (hν : 0 < ν) (z w : ℂ) (t : ℝ) :
    ‖vdpField b k₀ k₁ γ ν z t - vdpField b k₀ k₁ γ ν w t‖ =
      |(accel b k₀ k₁ γ ν t (pos ν z t) (vel ν z t) + ν ^ 2 * pos ν z t) -
        (accel b k₀ k₁ γ ν t (pos ν w t) (vel ν w t) + ν ^ 2 * pos ν w t)| / ν := by
  simp only [vdpField]
  rw [← sub_mul, ← mul_sub, ← Complex.ofReal_sub,
    show -(((ν * t : ℝ) : ℂ) * I) = ((-(ν * t) : ℝ) : ℂ) * I by push_cast; ring]
  simp only [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hν, Complex.norm_exp_ofReal_mul_I]
  ring

/-- **Lipschitz bound of the van der Pol field on a disc**: for `|z|, |w| ≤ r`,
`|F(z, t) − F(w, t)| ≤ ((|ν² − k₀| + |k₁| + ν|b| + 3|γ| r²)/ν) |z − w|`. -/
@[tmio M, powerlib_foundation] theorem norm_vdpField_sub_le (hν : 0 < ν) {r : ℝ} {z w : ℂ}
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (t : ℝ) :
    ‖vdpField b k₀ k₁ γ ν z t - vdpField b k₀ k₁ γ ν w t‖ ≤
      (|ν ^ 2 - k₀| + |k₁| + ν * |b| + 3 * |γ| * r ^ 2) / ν * ‖z - w‖ := by
  rw [norm_vdpField_sub hν, residual_eq, residual_eq, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hν]
  set X := pos ν z t
  set Y := pos ν w t
  have hX : |X| ≤ r := (abs_pos_le ν z t).trans hz
  have hY : |Y| ≤ r := (abs_pos_le ν w t).trans hw
  have hXY := abs_pos_sub_le ν z w t
  have hV := abs_vel_sub_le hν.le z w t
  have hc := Real.abs_cos_le_one (2 * ν * t)
  have e : (ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) * X - b * vel ν z t - γ * X ^ 3 -
      ((ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) * Y - b * vel ν w t - γ * Y ^ 3) =
      ((ν ^ 2 - k₀) - k₁ * Real.cos (2 * ν * t)) * (X - Y) - b * (vel ν z t - vel ν w t) -
        γ * (X - Y) * (X ^ 2 + X * Y + Y ^ 2) := by ring
  rw [e]
  have hq : |X ^ 2 + X * Y + Y ^ 2| ≤ 3 * r ^ 2 := by
    have h1 : |X ^ 2 + X * Y + Y ^ 2| ≤ |X| ^ 2 + |X| * |Y| + |Y| ^ 2 := by
      calc |X ^ 2 + X * Y + Y ^ 2| ≤ |X ^ 2 + X * Y| + |Y ^ 2| := abs_add_le _ _
        _ ≤ |X ^ 2| + |X * Y| + |Y ^ 2| := by gcongr; exact abs_add_le _ _
        _ = _ := by rw [abs_pow, abs_mul, abs_pow]
    have h0 : 0 ≤ |X| := abs_nonneg _
    have h0' : 0 ≤ |Y| := abs_nonneg _
    nlinarith [mul_le_mul hX hY h0' (h0.trans hX)]
  have hk : |(ν ^ 2 - k₀) - k₁ * Real.cos (2 * ν * t)| ≤ |ν ^ 2 - k₀| + |k₁| := by
    calc |(ν ^ 2 - k₀) - k₁ * Real.cos (2 * ν * t)| ≤ |ν ^ 2 - k₀| + |k₁ * Real.cos (2 * ν * t)| :=
          abs_sub _ _
      _ ≤ |ν ^ 2 - k₀| + |k₁| := by
          rw [abs_mul]; gcongr; nlinarith [abs_nonneg k₁]
  calc |((ν ^ 2 - k₀) - k₁ * Real.cos (2 * ν * t)) * (X - Y) - b * (vel ν z t - vel ν w t) -
        γ * (X - Y) * (X ^ 2 + X * Y + Y ^ 2)|
      ≤ |((ν ^ 2 - k₀) - k₁ * Real.cos (2 * ν * t)) * (X - Y)| +
          |b * (vel ν z t - vel ν w t)| + |γ * (X - Y) * (X ^ 2 + X * Y + Y ^ 2)| := by
        calc _ ≤ |((ν ^ 2 - k₀) - k₁ * Real.cos (2 * ν * t)) * (X - Y) -
              b * (vel ν z t - vel ν w t)| + |γ * (X - Y) * (X ^ 2 + X * Y + Y ^ 2)| := abs_sub _ _
          _ ≤ _ := by gcongr; exact abs_sub _ _
    _ ≤ (|ν ^ 2 - k₀| + |k₁|) * ‖z - w‖ + |b| * (ν * ‖z - w‖) + |γ| * ‖z - w‖ * (3 * r ^ 2) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
        gcongr
    _ = (|ν ^ 2 - k₀| + |k₁| + ν * |b| + 3 * |γ| * r ^ 2) * ‖z - w‖ := by ring


/-! ### Global solutions of a globally Lipschitz field -/

/-- **Global solutions.** A continuous field `f(t, x)` that is `K`-Lipschitz in `x` uniformly in
`t` has, from every initial state, a solution defined for all `t ∈ ℝ` (LeanForControl's
`exists_isIntegralCurveOn_Ici` forward, and for the reversed field backward). -/
@[tmio T, powerlib_foundation] theorem exists_global_solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {K : NNReal}
    (hc : Continuous (Function.uncurry f)) (hl : ∀ t, LipschitzWith K (f t)) (x₀ : E) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (f t (x t)) t := by
  obtain ⟨α, hα0, hα, -⟩ := exists_isIntegralCurveOn_Ici hc hl 0 x₀
  have hgc : Continuous (Function.uncurry fun s x => -f (-s) x) :=
    (hc.comp (continuous_fst.neg.prodMk continuous_snd)).neg
  have hgl : ∀ s, LipschitzWith K (fun x => -f (-s) x) := fun s => (hl (-s)).neg
  obtain ⟨β, hβ0, hβ, -⟩ := exists_isIntegralCurveOn_Ici hgc hgl 0 x₀
  set x : ℝ → E := fun t => if 0 ≤ t then α t else β (-t) with hx
  have hxα : EqOn x α (Ici 0) := fun s hs => by simp [hx, mem_Ici.mp hs]
  have hxβ : EqOn x (fun s => β (-s)) (Iic 0) := by
    intro s hs
    rcases (mem_Iic.mp hs).lt_or_eq with h | h
    · simp [hx, not_le.mpr h]
    · subst h; simp [hx, hα0, hβ0]
  -- the backward solution read forward in time
  have hback : ∀ s ∈ Iic (0 : ℝ),
      HasDerivWithinAt (fun s => β (-s)) (f s (β (-s))) (Iic 0) s := by
    intro s hs
    have h1 := hβ (-s) (by simpa using hs)
    have h2 := h1.scomp s (hasDerivAt_neg s).hasDerivWithinAt
      (fun u hu => by simpa using (mem_Iic.mp hu))
    simpa [Function.comp_def] using h2
  refine ⟨x, by simp [hx, hα0], fun t => ?_⟩
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := (hback t ht.le).hasDerivAt (Iic_mem_nhds ht)
    have heq : x =ᶠ[𝓝 t] fun s => β (-s) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) fun s hs => by
        simp [hx, not_le.mpr (mem_Iio.mp hs)]
    rw [show x t = β (-t) by simp [hx, not_le.mpr ht]]
    exact h.congr_of_eventuallyEq heq
  · have hr : HasDerivWithinAt x (f 0 (x 0)) (Ici 0) 0 := by
      have := (hα 0 self_mem_Ici).congr hxα (hxα self_mem_Ici)
      rwa [show α 0 = x 0 from (hxα self_mem_Ici).symm] at this
    have hl' : HasDerivWithinAt x (f 0 (x 0)) (Iic 0) 0 := by
      have := (hback 0 self_mem_Iic).congr hxβ (hxβ self_mem_Iic)
      rwa [show β (-0) = x 0 from (hxβ self_mem_Iic).symm] at this
    have := hl'.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have h := (hα t ht.le).hasDerivAt (Ici_mem_nhds ht)
    have heq : x =ᶠ[𝓝 t] α :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
        simp [hx, le_of_lt (mem_Ioi.mp hs)]
    rw [show x t = α t by simp [hx, ht.le]]
    exact h.congr_of_eventuallyEq heq

/-! ### The cut-off field and the KBM hypotheses -/

/-- The Lipschitz constant `(|ν² − k₀| + |k₁| + ν|b| + 3|γ|r²)/ν` of the van der Pol field on the
disc of radius `r` (`norm_vdpField_sub_le`). -/
def lipConst (b k₀ k₁ γ ν r : ℝ) : ℝ := (|ν ^ 2 - k₀| + |k₁| + ν * |b| + 3 * |γ| * r ^ 2) / ν

/-- The KBM error constant `(2ℓMLT + 2MT) e^{ℓL}` for averaged solutions in the disc of radius
`R`: cut-off radius `ρ = R + 1`, field disc `2ρ`, `ℓ = lipConst … (2ρ)`, `M = 2ρℓ`, `T = 2π/ν`. -/
def kbmConst (b k₀ k₁ γ ν R L : ℝ) : ℝ :=
  (2 * lipConst b k₀ k₁ γ ν (2 * (R + 1)) * (lipConst b k₀ k₁ γ ν (2 * (R + 1)) * (2 * (R + 1))) *
      L * (2 * Real.pi / ν) +
    2 * (lipConst b k₀ k₁ γ ν (2 * (R + 1)) * (2 * (R + 1))) * (2 * Real.pi / ν)) *
    Real.exp (lipConst b k₀ k₁ γ ν (2 * (R + 1)) * L)

/-- The van der Pol field read through the clamp onto the square of half-side `ρ`. -/
def cutField (b k₀ k₁ γ ν ρ : ℝ) (w : ℂ) (t : ℝ) : ℂ := vdpField b k₀ k₁ γ ν (clampC ρ w) t

@[tmio M, powerlib_foundation] theorem vdpField_zero (ν t : ℝ) : vdpField b k₀ k₁ γ ν 0 t = 0 := by
  simp [vdpField, accel, pos, vel]

@[tmio M, powerlib_foundation] theorem continuous_vdpField :
    Continuous fun q : ℂ × ℝ => vdpField b k₀ k₁ γ ν q.1 q.2 := by
  simp only [vdpField, accel, pos, vel]
  fun_prop

@[tmio M, powerlib_foundation] theorem vdpField_periodic (hν : 0 < ν) (z : ℂ) (t : ℝ) :
    vdpField b k₀ k₁ γ ν z (t + 2 * Real.pi / ν) = vdpField b k₀ k₁ γ ν z t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have he : Complex.exp (((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I) =
      Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    rw [show ((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I = ((ν * t : ℝ) : ℂ) * I + 2 * Real.pi * I by
      push_cast; field_simp, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have he' : Complex.exp (-(((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I)) =
      Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, he, ← Complex.exp_neg]
  have hc : Real.cos (2 * ν * (t + 2 * Real.pi / ν)) = Real.cos (2 * ν * t) := by
    rw [show 2 * ν * (t + 2 * Real.pi / ν) = 2 * ν * t + (2 : ℕ) * (2 * Real.pi) by
      field_simp; push_cast; ring]
    exact Real.cos_periodic.nat_mul 2 _
  simp only [vdpField, accel, pos, vel, he, he', hc]

/-- **The cut-off field satisfies the hypotheses of KBM** (`Averaging.kbm_first_order`): period
`T = 2π/ν`, Lipschitz constant `ℓ = lipConst … (2ρ)`, bound `M = 2ρℓ`. -/
@[tmio M, powerlib_foundation] theorem cutField_hyp (hν : 0 < ν) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 < 2 * Real.pi / ν ∧ 0 ≤ lipConst b k₀ k₁ γ ν (2 * ρ) ∧
      Continuous (Function.uncurry (cutField b k₀ k₁ γ ν ρ)) ∧
      (∀ x t, cutField b k₀ k₁ γ ν ρ x (t + 2 * Real.pi / ν) = cutField b k₀ k₁ γ ν ρ x t) ∧
      (∀ x y t, ‖cutField b k₀ k₁ γ ν ρ x t - cutField b k₀ k₁ γ ν ρ y t‖ ≤
        lipConst b k₀ k₁ γ ν (2 * ρ) * ‖x - y‖) ∧
      ∀ x t, ‖cutField b k₀ k₁ γ ν ρ x t‖ ≤ lipConst b k₀ k₁ γ ν (2 * ρ) * (2 * ρ) := by
  have hlip : ∀ x y t, ‖cutField b k₀ k₁ γ ν ρ x t - cutField b k₀ k₁ γ ν ρ y t‖ ≤
      lipConst b k₀ k₁ γ ν (2 * ρ) * ‖clampC ρ x - clampC ρ y‖ := by
    intro x y t
    simp only [cutField, lipConst]
    exact norm_vdpField_sub_le hν (norm_clampC_le hρ x) (norm_clampC_le hρ y) t
  have hℓ : 0 ≤ lipConst b k₀ k₁ γ ν (2 * ρ) := by
    unfold lipConst; have := hν.le; positivity
  have hcont : Continuous (Function.uncurry (cutField b k₀ k₁ γ ν ρ)) := by
    have e : Function.uncurry (cutField b k₀ k₁ γ ν ρ) =
        (fun q : ℂ × ℝ => vdpField b k₀ k₁ γ ν q.1 q.2) ∘ fun q : ℂ × ℝ => (clampC ρ q.1, q.2) := by
      funext q; simp only [Function.uncurry, cutField, Function.comp_apply]
    rw [e]
    exact continuous_vdpField.comp
      (((continuous_clampC ρ).comp continuous_fst).prodMk continuous_snd)
  have hper : ∀ x t, cutField b k₀ k₁ γ ν ρ x (t + 2 * Real.pi / ν) = cutField b k₀ k₁ γ ν ρ x t := by
    intro x t
    simp only [cutField]
    exact vdpField_periodic hν _ t
  have hbd : ∀ x t, ‖cutField b k₀ k₁ γ ν ρ x t‖ ≤ lipConst b k₀ k₁ γ ν (2 * ρ) * (2 * ρ) := by
    intro x t
    have h := norm_vdpField_sub_le (b := b) (k₀ := k₀) (k₁ := k₁) (γ := γ) hν
      (norm_clampC_le hρ x) (by rw [norm_zero]; positivity) t
    rw [vdpField_zero, sub_zero, sub_zero] at h
    simp only [cutField]
    exact h.trans (mul_le_mul_of_nonneg_left (norm_clampC_le hρ x) hℓ)
  exact ⟨by positivity, hℓ, hcont, hper,
    fun x y t => (hlip x y t).trans (mul_le_mul_of_nonneg_left (norm_clampC_sub_le ρ x y) hℓ), hbd⟩

@[tmio T, powerlib_foundation] private theorem lipschitzWith_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → E} {ε ℓ : ℝ} (hε : 0 ≤ ε) (hℓ : 0 ≤ ℓ)
    (hg : ∀ x y, ‖g x - g y‖ ≤ ℓ * ‖x - y‖) :
    LipschitzWith (Real.toNNReal (ε * ℓ)) fun x => ε • g x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hε,
    Real.coe_toNNReal _ (mul_nonneg hε hℓ), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x y) hε

@[tmio T, powerlib_foundation] private theorem hasDerivWithinAt_Ici_of_Icc {z : ℝ → ℂ} {v : ℝ → ℂ}
    {a b : ℝ} (h : ∀ t ∈ Icc a b, HasDerivWithinAt z (v t) (Icc a b) t) :
    ∀ t ∈ Ico a b, HasDerivWithinAt z (v t) (Ici t) t := fun t ht =>
  (h t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- **Rigorous first-order averaging of the Duffing–Mathieu oscillator on a bounded set.** In the
standard form `ż = ε vdpField b k₀ k₁ γ ν z t` (`vdpField_scaled`), let `z̄` solve the averaged
cubic amplitude equation `z̄̇ = ε ampField (b/2) ((ν² − k₀)/(2ν)) (jk₁/(4ν)) 0 (3γ/(8ν)) z̄` on
`[0, L/ε]` and stay in the disc `|z̄| ≤ R`. Then every solution `z` of the standard form on
`[0, L/ε]` with `z(0) = z̄(0)` stays within `C ε` of `z̄` there, `C = kbmConst b k₀ k₁ γ ν R L`,
as soon as `C ε ≤ 1`. (KBM's `Averaging.kbm_first_order` applied to the field clamped to the
square of half-side `R + 1`, `cutField`, with global solutions from `exists_global_solution` and
uniqueness from Mathlib's `ODE_solution_unique_of_mem_Icc_right`.) -/
@[tmio T, powerlib_foundation] theorem averaging_valid (hν : 0 < ν) {R L ε : ℝ} (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hε : 0 < ε) {z zbar : ℝ → ℂ}
    (hz : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt z (ε • vdpField b k₀ k₁ γ ν (z t) t) (Icc 0 (L / ε)) t)
    (hzbar : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt zbar
      (ε • ampField (b / 2) ((ν ^ 2 - k₀) / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * γ / (8 * ν)) (zbar t)) (Icc 0 (L / ε)) t)
    (hbound : ∀ t ∈ Icc 0 (L / ε), ‖zbar t‖ ≤ R) (h0 : z 0 = zbar 0)
    (hsmall : kbmConst b k₀ k₁ γ ν R L * ε ≤ 1) :
    ∀ t ∈ Icc 0 (L / ε), ‖z t - zbar t‖ ≤ kbmConst b k₀ k₁ γ ν R L * ε := by
  have hρ : 0 ≤ R + 1 := by linarith
  have hf := cutField_hyp (b := b) (k₀ := k₀) (k₁ := k₁) (γ := γ) hν hρ
  have hℓ : 0 ≤ lipConst b k₀ k₁ γ ν (2 * (R + 1)) := hf.2.1
  have hfbar : ∀ x, Averaging.fieldAverage (cutField b k₀ k₁ γ ν (R + 1)) (2 * Real.pi / ν) x =
      ampField (b / 2) ((ν ^ 2 - k₀) / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * γ / (8 * ν)) (clampC (R + 1) x) := by
    intro x
    rw [← fieldAverage_vdpField hν (clampC (R + 1) x)]
    simp only [Averaging.fieldAverage, cutField]
  -- global solutions of the cut-off and of the averaged cut-off system
  have hlipf : ∀ t : ℝ, LipschitzWith (Real.toNNReal (ε * lipConst b k₀ k₁ γ ν (2 * (R + 1))))
      fun x => ε • cutField b k₀ k₁ γ ν (R + 1) x t := fun t =>
    lipschitzWith_smul hε.le hℓ fun x y => hf.2.2.2.2.1 x y t
  have hcontf : Continuous (Function.uncurry fun (t : ℝ) (x : ℂ) =>
      ε • cutField b k₀ k₁ γ ν (R + 1) x t) :=
    (hf.2.2.1.comp (continuous_snd.prodMk continuous_fst)).const_smul ε
  obtain ⟨w, hw0, hw⟩ := exists_global_solution hcontf hlipf (z 0)
  have hlipa : ∀ t : ℝ, LipschitzWith (Real.toNNReal (ε * lipConst b k₀ k₁ γ ν (2 * (R + 1))))
      fun x => ε • Averaging.fieldAverage (cutField b k₀ k₁ γ ν (R + 1)) (2 * Real.pi / ν) x :=
    fun _ => lipschitzWith_smul hε.le hℓ fun x y => Averaging.fieldAverage_lipschitz hf x y
  have hconta : Continuous (Function.uncurry fun (_ : ℝ) (x : ℂ) =>
      ε • Averaging.fieldAverage (cutField b k₀ k₁ γ ν (R + 1)) (2 * Real.pi / ν) x) :=
    ((Averaging.fieldAverage_continuous hf).comp continuous_snd).const_smul ε
  obtain ⟨wbar, hwbar0, hwbar⟩ := exists_global_solution hconta hlipa (zbar 0)
  -- KBM for the cut-off system
  have hk := Averaging.kbm_first_order hf hε hL hw hwbar (by rw [hw0, hwbar0, h0])
  -- the averaged solution is the cut-off averaged solution on the window
  have hzbarc : ContinuousOn zbar (Icc 0 (L / ε)) := fun t ht => (hzbar t ht).continuousWithinAt
  have hE1 : EqOn zbar wbar (Icc 0 (L / ε)) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ x => ε • Averaging.fieldAverage (cutField b k₀ k₁ γ ν (R + 1)) (2 * Real.pi / ν) x)
      (s := fun _ => univ) (fun t _ => (hlipa t).lipschitzOnWith) hzbarc ?_ (fun _ _ => mem_univ _)
      (fun t _ => (hwbar t).continuousAt.continuousWithinAt) (fun t _ => (hwbar t).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hwbar0.symm
    intro t ht
    have h := hasDerivWithinAt_Ici_of_Icc hzbar t ht
    have hc : clampC (R + 1) (zbar t) = zbar t :=
      clampC_of_norm_le (by linarith [hbound t (Ico_subset_Icc_self ht)])
    rw [hfbar, hc]
    exact h
  -- the cut-off solution stays in the disc of radius `R + 1`, where the clamp is inactive
  have hwin : ∀ t ∈ Icc 0 (L / ε), ‖w t‖ ≤ R + 1 := by
    intro t ht
    have h1 := hk t ht
    rw [← hE1 ht] at h1
    have h2 := norm_le_norm_add_norm_sub' (w t) (zbar t)
    have h3 := hbound t ht
    have h4 : (2 * lipConst b k₀ k₁ γ ν (2 * (R + 1)) *
        (lipConst b k₀ k₁ γ ν (2 * (R + 1)) * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
        2 * (lipConst b k₀ k₁ γ ν (2 * (R + 1)) * (2 * (R + 1))) * (2 * Real.pi / ν)) *
        Real.exp (lipConst b k₀ k₁ γ ν (2 * (R + 1)) * L) * ε ≤ 1 := hsmall
    linarith
  -- uniqueness for the true field: both solve the field clamped at a larger radius
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun t ht => (hz t ht).continuousWithinAt : ContinuousOn z (Icc 0 (L / ε)))
  have hρ'0 : 0 ≤ max B (R + 1) := le_trans hρ (le_max_right _ _)
  have hf' := cutField_hyp (b := b) (k₀ := k₀) (k₁ := k₁) (γ := γ) hν hρ'0
  have hlip' : ∀ t : ℝ, LipschitzWith
      (Real.toNNReal (ε * lipConst b k₀ k₁ γ ν (2 * max B (R + 1))))
      fun x => ε • cutField b k₀ k₁ γ ν (max B (R + 1)) x t := fun t =>
    lipschitzWith_smul hε.le hf'.2.1 fun x y => hf'.2.2.2.2.1 x y t
  have hE2 : EqOn z w (Icc 0 (L / ε)) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun t x => ε • cutField b k₀ k₁ γ ν (max B (R + 1)) x t)
      (s := fun _ => univ) (fun t _ => (hlip' t).lipschitzOnWith)
      (fun t ht => (hz t ht).continuousWithinAt) ?_ (fun _ _ => mem_univ _)
      (fun t _ => (hw t).continuousAt.continuousWithinAt) ?_ (fun _ _ => mem_univ _)
      (by rw [hw0])
    · intro t ht
      have h := hasDerivWithinAt_Ici_of_Icc hz t ht
      have hc : clampC (max B (R + 1)) (z t) = z t :=
        clampC_of_norm_le ((hB t (Ico_subset_Icc_self ht)).trans (le_max_left _ _))
      show HasDerivWithinAt z (ε • vdpField b k₀ k₁ γ ν (clampC (max B (R + 1)) (z t)) t) (Ici t) t
      rw [hc]
      exact h
    · intro t ht
      have h := (hw t).hasDerivWithinAt (s := Ici t)
      have hwt := hwin t (Ico_subset_Icc_self ht)
      have hc1 : clampC (R + 1) (w t) = w t := clampC_of_norm_le hwt
      have hc2 : clampC (max B (R + 1)) (w t) = w t :=
        clampC_of_norm_le (hwt.trans (le_max_right _ _))
      show HasDerivWithinAt w (ε • vdpField b k₀ k₁ γ ν (clampC (max B (R + 1)) (w t)) t) (Ici t) t
      rw [hc2]
      have e : ε • cutField b k₀ k₁ γ ν (R + 1) (w t) t = ε • vdpField b k₀ k₁ γ ν (w t) t := by
        simp only [cutField, hc1]
      rw [e] at h
      exact h
  intro t ht
  rw [hE2 ht, hE1 ht]
  exact hk t ht

/-- **The oscillator follows its averaged amplitude on the time scale `1/ε`.** For the weakly
nonlinear Duffing–Mathieu oscillator `ẍ + εb ẋ + (ν² − εd + εk₁ cos 2νt) x + γ x³ = 0`, let `w̄`
solve the averaged amplitude equation
`w̄̇ = ε ampField (b/2) (d/(2ν)) (jk₁/(4ν)) 0 (3γ/(8ν)) w̄` on `[0, L/ε]` in the disc `|w̄| ≤ R`,
started at the scaled van der Pol amplitude of the oscillator, `z(0) = √ε w̄(0)`. Then on
`[0, L/ε]` the oscillation is `x(t) = √ε Re(w̄(t) e^{jνt}) + O(ε^{3/2})`:
`|x(t) − √ε Re(w̄(t) e^{jνt})| ≤ √ε · C ε`, `C = kbmConst b (ν² − d) k₁ γ ν R L`, whenever
`C ε ≤ 1` (`hasDerivAt_vdp`, `vdpField_scaled`, `averaging_valid`). -/
@[tmio T, powerlib_foundation] theorem oscillator_averaging (hν : 0 < ν) {b d k₁ γ R L ε : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) {x x' : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) γ ν t (x t) (x' t)) t)
    {wbar : ℝ → ℂ}
    (hwbar : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 (3 * γ / (8 * ν))
        (wbar t)) (Icc 0 (L / ε)) t)
    (hbound : ∀ t ∈ Icc 0 (L / ε), ‖wbar t‖ ≤ R)
    (h0 : vdp ν 0 (x 0) (x' 0) = (√ε : ℂ) * wbar 0)
    (hsmall : kbmConst b (ν ^ 2 - d) k₁ γ ν R L * ε ≤ 1) :
    ∀ t ∈ Icc 0 (L / ε), |x t - √ε * (wbar t * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤
      √ε * (kbmConst b (ν ^ 2 - d) k₁ γ ν R L * ε) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  set z : ℝ → ℂ := fun t => vdp ν t (x t) (x' t) with hzdef
  have hz : ∀ t, HasDerivAt z (vdpField (ε * b) (ν ^ 2 - ε * d) (ε * k₁) γ ν (z t) t) t := by
    intro t
    have h := hasDerivAt_vdp (u := fun _ => 0) hν.ne' hx (fun t => by simpa using hx' t) t
    simpa using h
  set w : ℝ → ℂ := fun t => ((√ε : ℝ) : ℂ)⁻¹ * z t with hwdef
  have hzw : ∀ t, z t = ((√ε : ℝ) : ℂ) * w t := fun t => by
    simp only [hwdef]; field_simp
  have hw : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt w (ε • vdpField b (ν ^ 2 - d) k₁ γ ν (w t) t) (Icc 0 (L / ε)) t := by
    intro t _
    have h := ((hz t).const_mul ((√ε : ℝ) : ℂ)⁻¹).hasDerivWithinAt (s := Icc 0 (L / ε))
    rw [hzw t, vdpField_scaled hε.le] at h
    convert h using 1
    rw [Complex.real_smul]
    field_simp
  have hΔ : (ν ^ 2 - (ν ^ 2 - d)) / (2 * ν) = d / (2 * ν) := by ring
  have hwbar' : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt wbar
      (ε • ampField (b / 2) ((ν ^ 2 - (ν ^ 2 - d)) / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * γ / (8 * ν)) (wbar t)) (Icc 0 (L / ε)) t := by
    intro t ht; rw [hΔ]; exact hwbar t ht
  have hw0 : w 0 = wbar 0 := by
    simp only [hwdef, hzdef, h0]; field_simp
  have hav := averaging_valid hν hR hL hε hw hwbar' hbound hw0 hsmall
  intro t ht
  have hx_eq : x t = (z t * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re := (pos_vdp ν t (x t) (x' t)).symm
  rw [hx_eq, show √ε * (wbar t * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re =
      ((((√ε : ℝ) : ℂ) * wbar t) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re by
    rw [mul_assoc, Complex.re_ofReal_mul], ← Complex.sub_re, ← sub_mul]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hzw t, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hs0.le]
  exact mul_le_mul_of_nonneg_left (hav t ht) hs0.le

end Validity

end powerlib.ParametricResonance.DuffingMathieu
