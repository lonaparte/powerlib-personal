import theorem.ParametricResonance.BoundaryUndecided

/-! # The second Picard term of a trigonometric-polynomial modulation in closed form

On the first-order boundary of the 2:1 criterion the verdict is carried by
`mixedDet(M, N₂) = tr M tr N₂ − tr(M N₂)`, with `M` the slow-flow matrix and
`N₂ = ∫₀ᵀ F(r) ∫₀ʳ F` the second Picard term of the rotating-frame matrix `F`
(`Boundary.full_boundary_decided`, `Boundary.critical_jury`). For a trigonometric-polynomial
matrix `F(t) = M₀ + ∑_{k ∈ H} (cos(kωt) C_k + sin(kωt) S_k)` (`k ≠ 0`, `T = 2π/ω`) the double
integral is elementary:

`N₂ = (T²/2) M₀² + ∑_{k ∈ H} (T/(kω)) ([M₀, S_k] + ½ [S_k, C_k])`, `[X, Y] = XY − YX`

(`secondTerm_trigPoly`; equivalently `N₂ = ½ (T M₀)² + ½ ∫₀ᵀ [F, ∫F]`). Only the sine
coefficients couple to the mean and different harmonics do not interact. For `2 × 2` matrices
`mixedDet(M₀, M₀²) = tr M₀ det M₀` and commutators with `M₀` drop out (`mixedDet_sq_comm`), so

`mixedDet(M₀, N₂) = (T²/2) tr M₀ det M₀ + ∑_{k ∈ H} (T/(2kω)) mixedDet(M₀, [S_k, C_k])`

(`mixedDet_secondTerm_trigPoly`). For the complete two-state 2:1 system `TwoToOne.full`
(`TwoToOne.stdForm`: harmonics `ω` and `2ω`) the fundamental coefficients commute (both lie in
the span of `I` and the quarter turn `J`), and the second-harmonic pair is fixed by the
anti-resonant pump `g' = ū A₁ r` (`antiPump`), the coefficient of the term rotating at `−2ω`
relative to the resonant one: `N₂ = (T²/2)M² + (T/ω)[M, M₂] + (T/(2ω))[M, M₄] − (T|g'|²/(8ω)) J`
(`secondTerm_stdForm`) and

`mixedDet(M, N₂) = −sT²(s² + d² − |g/2|²) + T d |g'|²/(4ω)` (`mixedDet_secondTerm_stdForm`).

On the first-order boundary `s² + d² = |g/2|²`, `s > 0`, this is `T d |g'|²/(4ω)`: the damped
two-state system is Schur stable for all small `ε` when `d |g'|² > 0` and Floquet unstable when
`d |g'|² < 0` (`full_boundary_closed_form`); the verdict is left open at this order exactly for
`d = 0` or `g' = 0` (the latter includes the exact resonant normal form, marginal on the boundary,
`Boundary.nf_boundary_marginal`); these cases are taken to third order in
`theorem/ParametricResonance/ThirdOrderBoundary.lean` (`full_boundary_third_order`,
`antiFree_stable`, `antiFree_marginal`, `antiFree_undecided`). The decisive second-order
quantity is thus a function of the detuning and of one further pump coefficient of the
modulation matrix `A₁`; the undamped case `s = 0` is treated in
`theorem/ParametricResonance/ZeroDampingBranch.lean`.

Scope.
* Generic: matrices on a finite index type `X` with the operator `L∞` norm; `trigPoly M₀ C S H ω`
  with a finite set `H ⊆ ℕ ∖ {0}` of harmonics, period `T = 2π/ω`, `ω > 0`; `secondTerm` and
  `mixedDet` of `theorem/ParametricResonance/BoundaryUndecided.lean`. The `2 × 2` statements are
  on `Fin 2`.
* Two-state system: `TwoToOne.full s d ω A ε` (critical pair `−εs ± j(ω/2 − εd)` in real modal
  form, modulation `ε Re{A e^{jωt}}`, arbitrary complex `A`), its rotating-frame matrix
  `TwoToOne.stdForm`, pump `g = Element.pump A left right`, anti-resonant pump
  `g' = Element.pump A (star left) (star right)`; statements for all sufficiently small `ε > 0`.
* Generic mathematics; no model family.

Source: the second-order (Picard / Magnus) term of the monodromy of `ẏ = εF(t)y` and the
transition curves of parametrically excited systems beyond first order (Nayfeh–Mook, *Nonlinear
Oscillations*, Ch. 5; Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic
Coefficients*, the small-parameter method); the open second-order quantity of
`Boundary.full_boundary_decided` (`theorem/ParametricResonance/BoundaryUndecided.lean`) and the
trigonometric decomposition `TwoToOne.stdForm_eq` (`theorem/ParametricResonance/TwoToOneAveraging.lean`).

Results.
* Period integrals: `integral_cos_int_mul`, `integral_sin_int_mul` (integer frequencies),
  `integral_cos_mul_cos_period`, `integral_sin_mul_sin_period`, `integral_cos_mul_sin_period`
  (orthogonality), `integral_mul_cos_period`, `integral_mul_sin_period` (`∫₀ᵀ t cos(kωt) = 0`,
  `∫₀ᵀ t sin(kωt) = −T/(kω)`).
* `trigPoly`, `trigPrim`, `continuous_trigPoly`, `integral_trigPoly` (`∫₀ʳ F = trigPrim`);
  `secondTerm_trigPoly` — `N₂` in closed form for every trigonometric polynomial.
* `mixedDet_sq_comm`, `mixedDet_secondTerm_trigPoly` — the `2 × 2` decisive quantity in terms of
  the Fourier coefficients.
* `stdCos`, `stdSin`, `stdForm_eq_trigPoly` (the rotating-frame matrix of the two-state system as
  a trigonometric polynomial), `antiPump`, `antiPump_eq` (`g' = (a₀₀ − a₁₁ − j(a₀₁ + a₁₀))/2`),
  `secondTerm_stdForm`, `mixedDet_secondTerm_stdForm`.
* `full_boundary_closed_form` — the boundary `s² + d² = |g/2|²`, `s > 0`, decided by the sign of
  `d |g'|²`.

Corrections.
None: an extension (the closed form of the second-order quantity left symbolic in
`Boundary.full_boundary_decided`).

Family and connection conclusions.
None: static evidence on periodic linear systems.
-/

noncomputable section
namespace powerlib.ParametricResonance.SecondOrder

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator Interval
open Boundary (secondTerm mixedDet)

/-! ## Trigonometric integrals over one pump period -/

section Trig

variable {ω : ℝ}

/-- `∫₀ᵀ cos(mωt) dt` is `T` for `m = 0` and `0` for every other integer `m` (`T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_cos_int_mul (hω : 0 < ω) (m : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (m * (ω * t)) =
      if m = 0 then 2 * Real.pi / ω else 0 := by
  split_ifs with hm
  · simp [hm]
  · have hmω : (m : ℝ) * ω ≠ 0 := mul_ne_zero (by exact_mod_cast hm) hω.ne'
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) (2 * Real.pi / ω),
        HasDerivAt (fun t => Real.sin (m * (ω * t)) / (m * ω)) (Real.cos (m * (ω * x))) x := by
      intro x _
      have h1 : HasDerivAt (fun t => (m : ℝ) * (ω * t)) (m * ω) x := by
        simpa using ((hasDerivAt_id x).const_mul ω).const_mul (m : ℝ)
      have h2 := h1.sin.div_const ((m : ℝ) * ω)
      convert h2 using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have : (m : ℝ) * (ω * (2 * Real.pi / ω)) = ((2 * m : ℤ) : ℝ) * Real.pi := by
      push_cast; field_simp
    rw [this, Real.sin_int_mul_pi]
    simp

/-- `∫₀ᵀ sin(mωt) dt = 0` for every integer `m` (`T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_sin_int_mul (hω : 0 < ω) (m : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (m * (ω * t)) = 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hmω : (m : ℝ) * ω ≠ 0 := mul_ne_zero (by exact_mod_cast hm) hω.ne'
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) (2 * Real.pi / ω),
        HasDerivAt (fun t => -Real.cos (m * (ω * t)) / (m * ω)) (Real.sin (m * (ω * x))) x := by
      intro x _
      have h1 : HasDerivAt (fun t => (m : ℝ) * (ω * t)) (m * ω) x := by
        simpa using ((hasDerivAt_id x).const_mul ω).const_mul (m : ℝ)
      have h2 := h1.cos.neg.div_const ((m : ℝ) * ω)
      convert h2 using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have : (m : ℝ) * (ω * (2 * Real.pi / ω)) = (m : ℝ) * (2 * Real.pi) := by
      field_simp
    rw [this, Real.cos_int_mul_two_pi]
    simp

/-- `∫₀ᵀ cos(jωt) cos(kωt) dt` is `T/2` for `j = k` and `0` otherwise (`j ≠ 0`, `T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_cos_mul_cos_period (hω : 0 < ω) {j : ℕ}
    (hj : j ≠ 0) (k : ℕ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (j * (ω * t)) * Real.cos (k * (ω * t)) =
      if j = k then 2 * Real.pi / ω / 2 else 0 := by
  have e : ∀ t : ℝ, Real.cos (j * (ω * t)) * Real.cos (k * (ω * t)) =
      (Real.cos (((j - k : ℤ) : ℝ) * (ω * t)) + Real.cos (((j + k : ℤ) : ℝ) * (ω * t))) / 2 := by
    intro t
    have h1 : ((j - k : ℤ) : ℝ) * (ω * t) = j * (ω * t) - k * (ω * t) := by push_cast; ring
    have h2 : ((j + k : ℤ) : ℝ) * (ω * t) = j * (ω * t) + k * (ω * t) := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul hω, integral_cos_int_mul hω]
  have hjk : (j + k : ℤ) ≠ 0 := by omega
  simp only [hjk, ↓reduceIte]
  by_cases h : j = k
  · subst h; simp
  · have : (j - k : ℤ) ≠ 0 := by omega
    simp [this, h]

/-- `∫₀ᵀ sin(jωt) sin(kωt) dt` is `T/2` for `j = k` and `0` otherwise (`j ≠ 0`, `T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_sin_mul_sin_period (hω : 0 < ω) {j : ℕ}
    (hj : j ≠ 0) (k : ℕ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (j * (ω * t)) * Real.sin (k * (ω * t)) =
      if j = k then 2 * Real.pi / ω / 2 else 0 := by
  have e : ∀ t : ℝ, Real.sin (j * (ω * t)) * Real.sin (k * (ω * t)) =
      (Real.cos (((j - k : ℤ) : ℝ) * (ω * t)) - Real.cos (((j + k : ℤ) : ℝ) * (ω * t))) / 2 := by
    intro t
    have h1 : ((j - k : ℤ) : ℝ) * (ω * t) = j * (ω * t) - k * (ω * t) := by push_cast; ring
    have h2 : ((j + k : ℤ) : ℝ) * (ω * t) = j * (ω * t) + k * (ω * t) := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul hω, integral_cos_int_mul hω]
  have hjk : (j + k : ℤ) ≠ 0 := by omega
  simp only [hjk, ↓reduceIte]
  by_cases h : j = k
  · subst h; simp
  · have : (j - k : ℤ) ≠ 0 := by omega
    simp [this, h]

/-- `∫₀ᵀ cos(jωt) sin(kωt) dt = 0` (`T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_cos_mul_sin_period (hω : 0 < ω) (j k : ℕ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (j * (ω * t)) * Real.sin (k * (ω * t)) = 0 := by
  have e : ∀ t : ℝ, Real.cos (j * (ω * t)) * Real.sin (k * (ω * t)) =
      (Real.sin (((k + j : ℤ) : ℝ) * (ω * t)) + Real.sin (((k - j : ℤ) : ℝ) * (ω * t))) / 2 := by
    intro t
    have h1 : ((k - j : ℤ) : ℝ) * (ω * t) = k * (ω * t) - j * (ω * t) := by push_cast; ring
    have h2 : ((k + j : ℤ) : ℝ) * (ω * t) = k * (ω * t) + j * (ω * t) := by push_cast; ring
    rw [h1, h2, Real.sin_sub, Real.sin_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_sin_int_mul hω, integral_sin_int_mul hω]
  simp

/-- `∫₀ᵀ t cos(kωt) dt = 0` (`k ≠ 0`, `T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_mul_cos_period (hω : 0 < ω) {k : ℕ}
    (hk : k ≠ 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), t * Real.cos (k * (ω * t)) = 0 := by
  have hkω : (k : ℝ) * ω ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hω.ne'
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (2 * Real.pi / ω),
      HasDerivAt (fun t => t * Real.sin (k * (ω * t)) / (k * ω) +
        Real.cos (k * (ω * t)) / ((k : ℝ) * ω) ^ 2) (x * Real.cos (k * (ω * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun t => (k : ℝ) * (ω * t)) (k * ω) x := by
      simpa using ((hasDerivAt_id x).const_mul ω).const_mul (k : ℝ)
    have h2 := (((hasDerivAt_id' x).mul h1.sin).div_const ((k : ℝ) * ω)).add
      (h1.cos.div_const (((k : ℝ) * ω) ^ 2))
    refine h2.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : (k : ℝ) * (ω * (2 * Real.pi / ω)) = ((2 * k : ℕ) : ℝ) * Real.pi := by
    push_cast; field_simp
  have h2 : (k : ℝ) * (ω * (2 * Real.pi / ω)) = (k : ℕ) * (2 * Real.pi) := by
    field_simp
  rw [h1, Real.sin_nat_mul_pi, ← h1, h2, Real.cos_nat_mul_two_pi]
  simp

/-- `∫₀ᵀ t sin(kωt) dt = −T/(kω)` (`k ≠ 0`, `T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_mul_sin_period (hω : 0 < ω) {k : ℕ}
    (hk : k ≠ 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), t * Real.sin (k * (ω * t)) =
      -(2 * Real.pi / ω / (k * ω)) := by
  have hkω : (k : ℝ) * ω ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hω.ne'
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (2 * Real.pi / ω),
      HasDerivAt (fun t => -(t * Real.cos (k * (ω * t))) / (k * ω) +
        Real.sin (k * (ω * t)) / ((k : ℝ) * ω) ^ 2) (x * Real.sin (k * (ω * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun t => (k : ℝ) * (ω * t)) (k * ω) x := by
      simpa using ((hasDerivAt_id x).const_mul ω).const_mul (k : ℝ)
    have h2 := (((hasDerivAt_id' x).mul h1.cos).neg.div_const ((k : ℝ) * ω)).add
      (h1.sin.div_const (((k : ℝ) * ω) ^ 2))
    refine h2.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : (k : ℝ) * (ω * (2 * Real.pi / ω)) = ((2 * k : ℕ) : ℝ) * Real.pi := by
    push_cast; field_simp
  have h2 : (k : ℝ) * (ω * (2 * Real.pi / ω)) = (k : ℕ) * (2 * Real.pi) := by
    field_simp
  rw [h1, Real.sin_nat_mul_pi, ← h1, h2, Real.cos_nat_mul_two_pi]
  simp
  ring

end Trig

/-! ## The second Picard term of a trigonometric polynomial -/

section General

variable {X : Type*} [Fintype X] [DecidableEq X] {ω : ℝ}

/-- A trigonometric-polynomial matrix `F(t) = M₀ + ∑_{k ∈ H} (cos(kωt) C_k + sin(kωt) S_k)`:
mean `M₀`, cosine and sine Fourier coefficients `C_k`, `S_k` at the harmonics `k ∈ H`. -/
def trigPoly (M₀ : Matrix X X ℝ) (C S : ℕ → Matrix X X ℝ) (H : Finset ℕ) (ω t : ℝ) :
    Matrix X X ℝ :=
  M₀ + ∑ k ∈ H, (Real.cos (k * (ω * t)) • C k + Real.sin (k * (ω * t)) • S k)

/-- Its primitive `∫₀ʳ F = r M₀ + ∑ (sin(kωr) C_k + (1 − cos(kωr)) S_k)/(kω)`. -/
def trigPrim (M₀ : Matrix X X ℝ) (C S : ℕ → Matrix X X ℝ) (H : Finset ℕ) (ω r : ℝ) :
    Matrix X X ℝ :=
  r • M₀ + ∑ k ∈ H, ((Real.sin (k * (ω * r)) / (k * ω)) • C k +
    ((1 - Real.cos (k * (ω * r))) / (k * ω)) • S k)

variable {M₀ : Matrix X X ℝ} {C S : ℕ → Matrix X X ℝ} {H : Finset ℕ}

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem continuous_trigPoly (M₀ : Matrix X X ℝ)
    (C S : ℕ → Matrix X X ℝ) (H : Finset ℕ) (ω : ℝ) : Continuous (trigPoly M₀ C S H ω) := by
  unfold trigPoly
  fun_prop

/-- `∫₀ʳ cos(kωu) du = sin(kωr)/(kω)` and `∫₀ʳ sin(kωu) du = (1 − cos(kωr))/(kω)`. -/
@[tmio T, powerlib_foundation] private theorem integral_cos_sin_upto (hω : 0 < ω) {k : ℕ}
    (hk : k ≠ 0) (r : ℝ) :
    (∫ u in (0 : ℝ)..r, Real.cos (k * (ω * u))) = Real.sin (k * (ω * r)) / (k * ω) ∧
      (∫ u in (0 : ℝ)..r, Real.sin (k * (ω * u))) = (1 - Real.cos (k * (ω * r))) / (k * ω) := by
  have hkω : (k : ℝ) * ω ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hω.ne'
  have h1 : ∀ x, HasDerivAt (fun t => (k : ℝ) * (ω * t)) (k * ω) x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul ω).const_mul (k : ℝ)
  constructor
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.sin (k * (ω * t)) /
      (k * ω)) (fun x _ => ((h1 x).sin.div_const ((k : ℝ) * ω)).congr_deriv (by field_simp))
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -Real.cos (k * (ω * t)) /
      (k * ω)) (fun x _ => ((h1 x).cos.neg.div_const ((k : ℝ) * ω)).congr_deriv (by field_simp))
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [mul_zero, Real.cos_zero]
    ring

/-- `∫₀ʳ F = trigPrim` for harmonics `k ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem integral_trigPoly (hω : 0 < ω) (hH : 0 ∉ H) (r : ℝ) :
    ∫ u in (0 : ℝ)..r, trigPoly M₀ C S H ω u = trigPrim M₀ C S H ω r := by
  unfold trigPoly trigPrim
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const, sub_zero,
    intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := fun h => hH (h ▸ hk)
  obtain ⟨hc, hs⟩ := integral_cos_sin_upto hω hk0 r
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const, hc, hs]

omit [DecidableEq X] in
/-- The integrand of the second Picard term as a double sum over the harmonics. -/
@[tmio T, powerlib_foundation] private theorem trigPoly_mul_trigPrim (M₀ : Matrix X X ℝ)
    (C S : ℕ → Matrix X X ℝ) (H : Finset ℕ) (ω r : ℝ) :
    trigPoly M₀ C S H ω r * trigPrim M₀ C S H ω r =
      r • (M₀ * M₀) +
      ∑ k ∈ H, ((Real.sin (k * (ω * r)) / (k * ω)) • (M₀ * C k) +
        ((1 - Real.cos (k * (ω * r))) / (k * ω)) • (M₀ * S k)) +
      ∑ j ∈ H, ((Real.cos (j * (ω * r)) * r) • (C j * M₀) +
        (Real.sin (j * (ω * r)) * r) • (S j * M₀)) +
      ∑ j ∈ H, ∑ k ∈ H,
        ((Real.cos (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (C j * C k) +
          (Real.cos (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (C j * S k) +
          (Real.sin (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (S j * C k) +
          (Real.sin (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (S j * S k)) := by
  rw [trigPoly, trigPrim, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_mul, Matrix.mul_smul]
  have e1 : ∀ k ∈ H, M₀ * ((Real.sin (k * (ω * r)) / (k * ω)) • C k +
      ((1 - Real.cos (k * (ω * r))) / (k * ω)) • S k) =
      (Real.sin (k * (ω * r)) / (k * ω)) • (M₀ * C k) +
        ((1 - Real.cos (k * (ω * r))) / (k * ω)) • (M₀ * S k) := fun k _ => by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  have e2 : ∀ j ∈ H, (Real.cos (j * (ω * r)) • C j + Real.sin (j * (ω * r)) • S j) * (r • M₀) =
      (Real.cos (j * (ω * r)) * r) • (C j * M₀) + (Real.sin (j * (ω * r)) * r) • (S j * M₀) :=
    fun j _ => by
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
        smul_smul, smul_smul]
  have e3 : ∀ j ∈ H, (Real.cos (j * (ω * r)) • C j + Real.sin (j * (ω * r)) • S j) *
      ∑ k ∈ H, ((Real.sin (k * (ω * r)) / (k * ω)) • C k +
        ((1 - Real.cos (k * (ω * r))) / (k * ω)) • S k) =
      ∑ k ∈ H, ((Real.cos (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (C j * C k) +
          (Real.cos (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (C j * S k) +
          (Real.sin (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (S j * C k) +
          (Real.sin (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (S j * S k)) :=
    fun j _ => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
      module
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3]
  abel

/-- The integrals of the scalar coefficients of the expansion over one period. -/
@[tmio T, powerlib_foundation] private theorem coeff_integrals (hω : 0 < ω) {j k : ℕ}
    (hj : j ≠ 0) (hk : k ≠ 0) :
    (∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (k * (ω * r)) / (k * ω)) = 0 ∧
      (∫ r in (0 : ℝ)..(2 * Real.pi / ω), (1 - Real.cos (k * (ω * r))) / (k * ω)) =
        2 * Real.pi / ω / (k * ω) ∧
      (∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (j * (ω * r)) * r) = 0 ∧
      (∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (j * (ω * r)) * r) =
        -(2 * Real.pi / ω / (j * ω)) ∧
      (∫ r in (0 : ℝ)..(2 * Real.pi / ω),
        Real.cos (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) = 0 ∧
      (∫ r in (0 : ℝ)..(2 * Real.pi / ω),
        Real.cos (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) =
        -(if j = k then 2 * Real.pi / ω / 2 else 0) / (k * ω) ∧
      (∫ r in (0 : ℝ)..(2 * Real.pi / ω),
        Real.sin (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) =
        (if j = k then 2 * Real.pi / ω / 2 else 0) / (k * ω) ∧
      (∫ r in (0 : ℝ)..(2 * Real.pi / ω),
        Real.sin (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) = 0 := by
  have hc1 : ∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (k * (ω * r)) = 0 := by
    have := integral_cos_int_mul hω (k : ℤ)
    simp only [Nat.cast_eq_zero, hk, ↓reduceIte] at this
    exact_mod_cast this
  have hcj : ∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (j * (ω * r)) = 0 := by
    have := integral_cos_int_mul hω (j : ℤ)
    simp only [Nat.cast_eq_zero, hj, ↓reduceIte] at this
    exact_mod_cast this
  have hs1 : ∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (k * (ω * r)) = 0 := by
    exact_mod_cast integral_sin_int_mul hω (k : ℤ)
  have hsj : ∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (j * (ω * r)) = 0 := by
    exact_mod_cast integral_sin_int_mul hω (j : ℤ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [intervalIntegral.integral_div, hs1, zero_div]
  · rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const
      (by apply Continuous.intervalIntegrable; fun_prop), hc1]
    simp
  · simp_rw [mul_comm (Real.cos _)]
    exact integral_mul_cos_period hω hj
  · simp_rw [mul_comm (Real.sin _)]
    exact integral_mul_sin_period hω hj
  · simp_rw [mul_div_assoc']
    rw [intervalIntegral.integral_div, integral_cos_mul_sin_period hω, zero_div]
  · simp_rw [mul_div_assoc', mul_sub, mul_one]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), hcj,
      integral_cos_mul_cos_period hω hj, zero_sub]
  · simp_rw [mul_div_assoc']
    rw [intervalIntegral.integral_div, integral_sin_mul_sin_period hω hj]
  · simp_rw [mul_div_assoc', mul_sub, mul_one]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), hsj]
    simp_rw [mul_comm (Real.sin _)]
    rw [integral_cos_mul_sin_period hω]
    simp

/-- **The second Picard term of a trigonometric polynomial in closed form.** For
`F(t) = M₀ + ∑_{k ∈ H} (cos(kωt) C_k + sin(kωt) S_k)` with harmonics `k ≠ 0` and `T = 2π/ω`:
`N₂ = ∫₀ᵀ F(r) ∫₀ʳ F = (T²/2) M₀² + ∑_{k ∈ H} (T/(kω)) ([M₀, S_k] + ½ [S_k, C_k])`, with
`[X, Y] = XY − YX`. Only the sine coefficients couple to the mean, and each harmonic contributes
the commutator of its own two coefficients; different harmonics do not interact. -/
@[tmio T, powerlib_foundation] theorem secondTerm_trigPoly (hω : 0 < ω) (hH : 0 ∉ H) :
    secondTerm (trigPoly M₀ C S H ω) (2 * Real.pi / ω) =
      ((2 * Real.pi / ω) ^ 2 / 2) • (M₀ * M₀) +
        ∑ k ∈ H, (2 * Real.pi / ω / (k * ω)) •
          (M₀ * S k - S k * M₀ + (1 / 2 : ℝ) • (S k * C k - C k * S k)) := by
  set T := 2 * Real.pi / ω with hT
  have hint : ∀ r, ∫ u in (0 : ℝ)..r, trigPoly M₀ C S H ω u = trigPrim M₀ C S H ω r :=
    integral_trigPoly hω hH
  unfold secondTerm
  simp_rw [hint, trigPoly_mul_trigPrim]
  have hne : ∀ k ∈ H, k ≠ 0 := fun k hk h => hH (h ▸ hk)
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_smul_const, integral_id,
    intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
  have e1 : ∀ k ∈ H, (∫ r in (0 : ℝ)..T, ((Real.sin (k * (ω * r)) / (k * ω)) • (M₀ * C k) +
      ((1 - Real.cos (k * (ω * r))) / (k * ω)) • (M₀ * S k))) = (T / (k * ω)) • (M₀ * S k) :=
    fun k hk => by
      obtain ⟨h1, h2, -⟩ := coeff_integrals hω (hne k hk) (hne k hk)
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const, h1, h2,
        zero_smul, zero_add]
  have e2 : ∀ j ∈ H, (∫ r in (0 : ℝ)..T, ((Real.cos (j * (ω * r)) * r) • (C j * M₀) +
      (Real.sin (j * (ω * r)) * r) • (S j * M₀))) = (-(T / (j * ω))) • (S j * M₀) :=
    fun j hj => by
      obtain ⟨-, -, h3, h4, -⟩ := coeff_integrals hω (hne j hj) (hne j hj)
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const, h3, h4,
        zero_smul, zero_add]
  have e3 : ∀ j ∈ H, (∫ r in (0 : ℝ)..T, ∑ k ∈ H,
      ((Real.cos (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (C j * C k) +
        (Real.cos (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (C j * S k) +
        (Real.sin (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (S j * C k) +
        (Real.sin (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (S j * S k))) =
      (T / 2 / (j * ω)) • (S j * C j - C j * S j) := fun j hj => by
    rw [intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    have hk : ∀ k ∈ H, (∫ r in (0 : ℝ)..T,
        ((Real.cos (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (C j * C k) +
          (Real.cos (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (C j * S k) +
          (Real.sin (j * (ω * r)) * (Real.sin (k * (ω * r)) / (k * ω))) • (S j * C k) +
          (Real.sin (j * (ω * r)) * ((1 - Real.cos (k * (ω * r))) / (k * ω))) • (S j * S k))) =
        if j = k then (T / 2 / (j * ω)) • (S j * C j - C j * S j) else 0 := fun k hk => by
      obtain ⟨-, -, -, -, h5, h6, h7, h8⟩ := coeff_integrals hω (hne j hj) (hne k hk)
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
        intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
        h5, h6, h7, h8]
      by_cases hjk : j = k
      · subst hjk
        simp only [↓reduceIte]
        module
      · simp [hjk]
    rw [Finset.sum_congr rfl hk, Finset.sum_ite_eq]
    simp only [hj, ↓reduceIte]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, add_assoc,
    add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · simp only [hT]
    ring_nf
  · refine Finset.sum_congr rfl fun k hk => ?_
    module

end General

/-! ## The two-state case: the decisive quantity `mixedDet(M₀, N₂)` -/

section TwoState

variable {ω : ℝ} {M₀ : Matrix (Fin 2) (Fin 2) ℝ} {C S : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
  {H : Finset ℕ}

@[tmio T, powerlib_foundation] private theorem mixedDet_add_right' (M N N' : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet M (N + N') = mixedDet M N + mixedDet M N' := by
  simp [mixedDet, Matrix.mul_add, Matrix.trace_add]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_smul_right' (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) : mixedDet M (c • N) = c * mixedDet M N := by
  simp [mixedDet, Matrix.trace_smul]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_sum_right (M : Matrix (Fin 2) (Fin 2) ℝ)
    (f : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (H : Finset ℕ) :
    mixedDet M (∑ k ∈ H, f k) = ∑ k ∈ H, mixedDet M (f k) := by
  simp only [mixedDet, Matrix.trace_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- `mixedDet(M, M²) = tr M · det M` and `mixedDet(M, MX − XM) = 0`: the mean's own square enters
only through `det M`, and commutators with the mean drop out. -/
@[tmio T, powerlib_foundation] theorem mixedDet_sq_comm (M X : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet M (M * M) = M.trace * M.det ∧ mixedDet M (M * X - X * M) = 0 := by
  constructor
  · simp [mixedDet, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply]
    ring

/-- **The decisive second-order quantity of a two-state trigonometric polynomial.** For
`F = M₀ + ∑_{k ∈ H} (cos(kωt) C_k + sin(kωt) S_k)` on `ℝ²` (`k ≠ 0`, `T = 2π/ω`):
`mixedDet(M₀, N₂) = (T²/2) tr M₀ det M₀ + ∑_{k ∈ H} (T/(2kω)) mixedDet(M₀, [S_k, C_k])`. -/
@[tmio T, powerlib_foundation] theorem mixedDet_secondTerm_trigPoly (hω : 0 < ω) (hH : 0 ∉ H) :
    mixedDet M₀ (secondTerm (trigPoly M₀ C S H ω) (2 * Real.pi / ω)) =
      (2 * Real.pi / ω) ^ 2 / 2 * (M₀.trace * M₀.det) +
        ∑ k ∈ H, 2 * Real.pi / ω / (k * ω) / 2 * mixedDet M₀ (S k * C k - C k * S k) := by
  rw [secondTerm_trigPoly hω hH, mixedDet_add_right', mixedDet_smul_right',
    (mixedDet_sq_comm M₀ M₀).1, mixedDet_sum_right]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mixedDet_smul_right', mixedDet_add_right', (mixedDet_sq_comm M₀ (S k)).2,
    mixedDet_smul_right']
  ring

end TwoState

/-! ## The complete two-state 2:1 system -/

section Full

open TwoToOne (stdForm full left right refl1 refl2)
open _root_.powerlib.ParametricResonance.NormalForm (quarter)

/-- The cosine coefficients of the rotating-frame matrix `TwoToOne.stdForm` at the harmonics
`ω` (`k = 1`) and `2ω` (`k = 2`, every other `k`), read off `TwoToOne.stdForm_eq`. -/
def stdCos (A : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = 1 then (((A 0 0).re + (A 1 1).re) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (((A 1 0).re - (A 0 1).re) / 2) • quarter
  else (((A 0 0).re - (A 1 1).re + (A 0 1).im + (A 1 0).im) / 4) • refl1 +
      (((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4) • refl2

/-- The sine coefficients of `TwoToOne.stdForm` at `ω` (`k = 1`) and `2ω` (every other `k`). -/
def stdSin (A : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = 1 then (-(((A 0 0).im + (A 1 1).im) / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      (((A 1 0).im - (A 0 1).im) / 2) • quarter
  else (((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4) • refl1 -
      (((A 0 1).im + (A 1 0).im + (A 0 0).re - (A 1 1).re) / 4) • refl2

/-- The anti-resonant pump coefficient `g' = ū A₁ r` (`Element.pump A₁ ū r̄`; the pump
coefficient is `g = u A₁ r̄`). In `ẋ = (A₀ + ε Re{A₁ e^{jωt}}) x` with `x = z r + z̄ r̄` it is the
conjugate of the coefficient `u Ā₁ r̄` of the term `½ e^{−jωt} z̄` in `ż`, which rotates at `−2ω`
relative to the resonant term `½ g e^{jωt} z̄`. -/
def antiPump (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := Element.pump A (star left) (star right)

/-- `g' = (a₀₀ − a₁₁ − j(a₀₁ + a₁₀))/2` (compare `TwoToOne.pump_base`). -/
@[tmio T, powerlib_foundation] theorem antiPump_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    antiPump A = (A 0 0 - A 1 1 - I * (A 0 1 + A 1 0)) / 2 := by
  simp [antiPump, Element.pump, left, right, mulVec, dotProduct, Fin.sum_univ_two, map_ofNat]
  ring_nf; simp [I_sq]; ring

/-- **The rotating-frame matrix as a trigonometric polynomial**: `TwoToOne.stdForm s d ω A` is
`trigPoly` with mean `slowFlowMatrix s d (g/2)`, harmonics `{1, 2}` and the coefficients
`stdCos A`, `stdSin A`. -/
@[tmio T, powerlib_foundation] theorem stdForm_eq_trigPoly (s d ω : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    stdForm s d ω A = trigPoly (slowFlowMatrix s d (Element.pump A left right / 2)) (stdCos A)
      (stdSin A) {1, 2} ω := by
  funext t
  rw [TwoToOne.stdForm_eq, trigPoly, Finset.sum_pair (by norm_num)]
  simp only [stdCos, stdSin, ↓reduceIte, Nat.cast_one, one_mul, Nat.cast_ofNat,
    OfNat.ofNat_ne_one]
  abel

@[tmio T, powerlib_foundation] private theorem comm_one (A : Matrix (Fin 2) (Fin 2) ℂ) :
    stdSin A 1 * stdCos A 1 - stdCos A 1 * stdSin A 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stdCos, stdSin, quarter, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[tmio T, powerlib_foundation] private theorem comm_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    stdSin A 2 * stdCos A 2 - stdCos A 2 * stdSin A 2 = (-(‖antiPump A‖ ^ 2 / 2)) • quarter := by
  rw [Complex.sq_norm, Complex.normSq_apply, antiPump_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stdCos, stdSin, refl1, refl2, quarter] <;> ring

/-- **The second Picard term of the two-state 2:1 system in closed form.** With
`M₀ = slowFlowMatrix s d (g/2)`, the sine coefficients `M₂ = stdSin A 1` (at `ω`) and
`M₄ = stdSin A 2` (at `2ω`), `T = 2π/ω` and `J` the quarter turn:
`N₂ = (T²/2) M₀² + (T/ω)[M₀, M₂] + (T/(2ω))[M₀, M₄] − (T|g'|²/(8ω)) J`. The fundamental
coefficients commute with each other (both are combinations of `I` and `J`); the second-harmonic
pair contributes `½[M₄, M₃] = −(|g'|²/4) J`. -/
@[tmio T, powerlib_foundation] theorem secondTerm_stdForm (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    secondTerm (stdForm s d ω A) (2 * Real.pi / ω) =
      ((2 * Real.pi / ω) ^ 2 / 2) • (slowFlowMatrix s d (Element.pump A left right / 2) *
          slowFlowMatrix s d (Element.pump A left right / 2)) +
        (2 * Real.pi / ω / ω) • (slowFlowMatrix s d (Element.pump A left right / 2) * stdSin A 1 -
          stdSin A 1 * slowFlowMatrix s d (Element.pump A left right / 2)) +
        (2 * Real.pi / ω / (2 * ω)) • (slowFlowMatrix s d (Element.pump A left right / 2) *
          stdSin A 2 - stdSin A 2 * slowFlowMatrix s d (Element.pump A left right / 2)) -
        (2 * Real.pi / ω * ‖antiPump A‖ ^ 2 / (8 * ω)) • quarter := by
  rw [stdForm_eq_trigPoly, secondTerm_trigPoly hω (by simp), Finset.sum_pair (by norm_num),
    comm_one, comm_two]
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat, smul_zero, add_zero]
  have hω0 : ω ≠ 0 := hω.ne'
  have e : (2 * Real.pi / ω / (2 * ω)) • ((1 / 2 : ℝ) • (-(‖antiPump A‖ ^ 2 / 2)) • quarter) =
      -((2 * Real.pi / ω * ‖antiPump A‖ ^ 2 / (8 * ω)) • quarter) := by
    rw [smul_smul, smul_smul, ← neg_smul]
    congr 1
    field_simp
    ring
  rw [smul_add (2 * Real.pi / ω / (2 * ω)), e]
  abel

/-- **`mixedDet(M, N₂)` of the two-state 2:1 system in closed form.** With the slow-flow matrix
`M = slowFlowMatrix s d (g/2)`, `N₂ = secondTerm (stdForm s d ω A) T`, `T = 2π/ω`:
`mixedDet(M, N₂) = −sT²(s² + d² − |g/2|²) + T d |g'|²/(4ω)`, `g' = antiPump A`. Only the slow-flow
data `s, d, g` and the anti-resonant pump `g'` enter; the fundamental (`ω`) components of the
rotating-frame matrix do not. -/
@[tmio T, powerlib_foundation] theorem mixedDet_secondTerm_stdForm (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
        (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)) =
      -(s * (2 * Real.pi / ω) ^ 2 * (s ^ 2 + d ^ 2 - ‖Element.pump A left right / 2‖ ^ 2)) +
        2 * Real.pi / ω * d * ‖antiPump A‖ ^ 2 / (4 * ω) := by
  rw [stdForm_eq_trigPoly, mixedDet_secondTerm_trigPoly hω (by simp),
    Finset.sum_pair (by norm_num), comm_one, comm_two, mixedDet_smul_right',
    trace_slowFlowMatrix, det_slowFlowMatrix]
  have hJ : mixedDet (slowFlowMatrix s d (Element.pump A left right / 2)) quarter = -(2 * d) := by
    simp [mixedDet, slowFlowMatrix, quarter, Matrix.trace_fin_two]
    ring
  have h0 : mixedDet (slowFlowMatrix s d (Element.pump A left right / 2)) 0 = 0 := by
    simp [mixedDet]
  rw [hJ, h0]
  simp only [Nat.cast_one, Nat.cast_ofNat]
  have hω0 : ω ≠ 0 := hω.ne'
  field_simp
  ring

/-- **The first-order boundary of the damped two-state system decided in closed form.** On the
boundary `s² + d² = |g/2|²`, `s > 0`, the complete two-state system `TwoToOne.full s d ω A ε` is
Schur stable for all small `ε > 0` if `d |g'|² > 0` and Floquet unstable if `d |g'|² < 0`
(`g' = antiPump A`): `Boundary.full_boundary_decided` with
`mixedDet(M, N₂) = T d |g'|²/(4ω)` there. The verdict is undecided at this order exactly when
`d = 0` or `g' = 0` (the latter is the exact resonant normal form, which is marginal,
`Boundary.nf_boundary_marginal`); third order: `ThirdOrder.full_boundary_third_order`. -/
@[tmio T, powerlib_foundation] theorem full_boundary_closed_form {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    (0 < d * ‖antiPump A‖ ^ 2 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LTI.SchurStable (Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0)) ∧
      (d * ‖antiPump A‖ ^ 2 < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω)) := by
  obtain ⟨h1, h2⟩ := Boundary.full_boundary_decided hω A hs hb
  have hm := mixedDet_secondTerm_stdForm s d hω A
  rw [← hb, sub_self, mul_zero, neg_zero, zero_add] at hm
  have hc : 0 < 2 * Real.pi / ω / (4 * ω) := by positivity
  have e : 2 * Real.pi / ω * d * ‖antiPump A‖ ^ 2 / (4 * ω) =
      2 * Real.pi / ω / (4 * ω) * (d * ‖antiPump A‖ ^ 2) := by ring
  rw [e] at hm
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [hm]; exact mul_pos hc h
  · rw [hm]; exact mul_neg_of_pos_of_neg hc h

end Full

end powerlib.ParametricResonance.SecondOrder
