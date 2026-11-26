import theorem.ParametricResonance.SlowFlowBranches
import theorem.ParametricResonance.UniversalThreshold
import Mathlib.MeasureTheory.Function.Floor

/-! # The square-wave oscillator at the averaged level (L2) against its exact boundary (L1)

For `ẍ + 2cẋ + ω₀²(1 + p(t))x = 0` with a `T`-periodic modulation `p` and pump frequency
`ω = 2π/T`, the frame rotating at `ω/2`, `(x, ẋ) = P(t) w`, `P(t) = D R(ωt/2)`,
`D = diag(1, −ω/2)`, is an exact change of variables: `ẇ = G(t) w` with
`G(t) = R(−ωt/2) N(t) R(ωt/2)`, `N(t) = [[0, 0], [(4k(t) − ω²)/(2ω), −2c]]`. The first-order
averaged (L2) model is `ẇ = Ḡ w`, `Ḡ = (1/T) ∫₀ᵀ G` (the integral exists for every integrable,
in particular for the piecewise-constant, modulation). For every waveform `Ḡ` is the 2:1 slow
flow `slowFlowMatrix c Δ g` of `theorem/ParametricResonance/SlowFlow.lean`: damping `c`, detuning
`Δ = (ω²/4 − ω₀²(1 + p̄))/ω` from `ω/2` and pump `g = ω₀² (b₁ + j a₁)/(2ω)`, so only the mean
`p̄` and the fundamental (`|g| = ω₀² m₁/(2ω)`) of the modulation enter. For the square wave of
depth `ε` the wave-1 coefficients (`a₁ = 0`, `b₁ = 4ε/π`) give `g = 2ω₀²ε/(πω)`, the
sinusoidal-pump value `ω₀²h/(2ω)` at the fundamental amplitude `h = 4ε/π`, and the L2 threshold
`π ω √(c² + Δ²) = 2|ε| ω₀²`, i.e. `|ε| = π (ω/(2ω₀)) √(ξ² + d²)`, `ξ = c/ω₀`, `d = Δ/ω₀`: to the
order of the averaging (`ω/(2ω₀) = 1 + O(d)`) `ε_c^{L2} = π √(ξ² + d²)`, and exactly `πξ` at
`ω = 2ω₀`.

Against the exact Meissner boundary (L1, `theorem/ParametricResonance/Meissner.lean`):
* first-order agreement at the exact tongue centre `Ω = ν₁ + ν₂`: for every `η > 0` and all
  small `ξ`, `ε`, `ε > (π + η)ξ` gives Floquet instability and `ε < (π − η)ξ` Schur stability
  (the limit `ε_c/ξ → π` in cone form; no threshold function is defined); at the same pump
  frequency the L2 verdicts are the same, so the two levels can disagree only in the cone
  `|ε − πξ| ≤ ηξ`;
* the finite-`ξ` gap: the exact centre is Schur stable when `ε < πξ √(1 − ε − ξ²)` and Floquet
  unstable when `πξ √(1 − ξ²) cosh(πξ/√(2(1 − ξ²))) < ε cos(πε/(2(1 − ξ²)))`, from explicit
  bounds on the three correction factors `√(ν₁ν₂)/ω₀`, `sinh x/x`, `|sin θ₁|` of
  `Meissner.centre_threshold_iff`; both bounds are `πξ(1 + O(ξ + ε))`;
* validity of L2 for the square wave: in the distinguished scaling `c = μs`,
  `ω²/4 − ω₀² = μωd`, `ω₀²ε = μπωe/2` the L2 verdict (Hurwitz, or an exponent with positive real
  part, of `μ · slowFlowMatrix s d e`) holds for the Meissner monodromy for all small `μ > 0`,
  although the coefficient jumps. The time change `τ(t) = t − (T/(4π)) sin(4πt/T)`, `τ' = 0` at
  the switching instants, turns the switched period map into the monodromy of a continuous field
  with the same average, to which `Averaging.averaging_schurStable` and
  `Averaging.averaging_floquetUnstable` apply;
* the universal region `|ε|/√(1 − |ε|) < 2ξ` of `theorem/ParametricResonance/UniversalThreshold.lean`
  (proved there for continuous stiffness, compared here algebraically) lies inside the L2 stable
  region at every detuning for `ω ≥ (4/π) ω₀ √(1 − |ε|)`; at `ω = 2ω₀` the L2 threshold `πξ` is
  `π/(2√(1 − |ε|)) ≥ π/2` times the universal one.

Scope.
* The scalar oscillator in the state `(x, ẋ)`, `ẏ = oscMatrix c (k t) y`, constant damping `c`,
  stiffness `k = ω₀²(1 + p)`: `p` interval integrable for the averaged matrix, `p` the square
  wave `squareWave ε T` (`Meissner.stiffness`) for the Meissner statements; pump frequency
  `ω > 0`, period `T = 2π/ω`; continuous time; solutions with right derivatives as in
  `theorem/ParametricResonance/Meissner.lean`.
* L1: `Meissner.meissnerMonodromy`, a multiplier of modulus `> 1` (Floquet instability) or
  `LTI.SchurStable`. L2: `averagedMatrix`, its characteristic roots (`Linear.characteristicMatrix`)
  and `LinearSystems.IsHurwitz`. The rotating frame is exact; averaging replaces `G` by `Ḡ`. The
  passage L2 → L1 is proved for small modulation in the distinguished scaling and, at the exact
  tongue centre, in the small-`(ξ, ε)` cone; at finite depth the levels are compared through the
  explicit bounds only.
* The generic two-piece averaging theorems concern continuous bounded `G₁`, `G₂` on
  `[0, T/2]` and `[T/2, T]` (`Periodic.transition`), stated for `ε → 0⁺`.
* Generic mathematics; no model family.

Source: first-order averaging of the damped Hill equation in the frame rotating at half the pump
frequency (Nayfeh–Mook, *Nonlinear Oscillations*, parametrically excited systems; Richards,
*Analysis of Periodically Time-Varying Systems*, 1983); the 2:1 slow flow and its branches
(`theorem/ParametricResonance/SlowFlow.lean`, `Branches.slowFlow_unstable_iff`); the square-wave
coefficients `SpecialFunctions.PeriodicWaves.coeff_squareWave`; the exact Meissner boundary
(`Meissner.centre_threshold_iff`, `Meissner.schurStable_iff`, `Meissner.meissnerMonodromy_eq_exp`);
the averaging theorems of `theorem/ParametricResonance/PeriodicAveraging.lean`;
`UniversalThreshold.schurStable_of_threshold`. Closes the gap recorded in
`theorem/Periodic/AnalysisLevels.lean` (no closed-form first-order model of the square wave).

Sharpenings.
* "`ε_c ≈ πζ` for small `ε`, `ζ`" (Meissner) is made a two-sided limit statement
  (`centre_threshold_ratio`) with an explicit finite-`ξ` band (`centre_band`), and the averaged
  and exact verdicts coincide outside a cone of half-width `ηξ` (`centre_levels_agree`).
* `PeriodicAveraging` assumes a continuous modulation; for the square wave the first-order
  verdicts are recovered by the time change (`twoPiece_averaging_schurStable`,
  `twoPiece_averaging_floquetUnstable`).

Results.
* `scale_mul_scaleInv`, `scaleInv_mul_scale`, `scaleInv_mul_osc`, `frameInv_mul_frame`,
  `frame_mul_frameInv` — the frame `P(t) = D R(ωt/2)`; `D⁻¹ A = ((ω/2)J + N) D⁻¹`.
* `hasDerivWithinAt_frameInv_mul`, `hasDerivWithinAt_frameInv_mulVec` — the rotating frame is
  exact: `Ẏ = A Y` (or `ẏ = A y`) within any set gives `Ẇ = G W` for `W = P⁻¹ Y`.
* `frameField_eq` — `G = −c I + (n/2) J + (c cos ωt + (n/2) sin ωt) E₁ + ((n/2) cos ωt − c sin ωt) E₂`.
* `averagedMatrix_eq` — every integrable waveform: `Ḡ = slowFlowMatrix c Δ g`,
  `Δ = (ω²/4 − ω₀²(1 + p̄))/ω`, `g = ω₀²(b₁ + j a₁)/(2ω)`; `norm_pump_eq_amp` — `|g| = ω₀² m₁/(2ω)`.
* `intervalIntegrable_squareWave`, `integral_squareWave`, `fourier_squareWave` — the square wave is
  integrable with zero mean, `a₁ = 0`, `b₁ = 4ε/π`; `averagedMatrix_squareWave` — its L2 matrix
  `slowFlowMatrix c ((ω²/4 − ω₀²)/ω) (2ω₀²ε/(πω))`.
* `averaged_threshold` — L2 unstable iff `πω √(c² + Δ²) < 2|ε|ω₀²` (`c ≥ 0`), Hurwitz iff
  `2|ε|ω₀² < πω √(c² + Δ²)` (`c > 0`); `averaged_threshold_normalized` — the same as
  `|ε| ≷ π (ω/(2ω₀)) √(ξ² + d²)`; `averaged_centre_threshold` — at `ω = 2ω₀`: `|ε| ≷ πξ`.
* `averaged_hurwitz_of_universal` — the universal region lies inside the L2 stable region for
  `4ω₀√(1 − |ε|) ≤ πω`.
* `centre_schurStable_iff` — exact centre, stable side:
  `ε ω₀² |sin θ₁| < √(ν₁ν₂)(ν₁ + ν₂) sinh(πc/(ν₁ + ν₂))`.
* `centre_factors`, `centre_band` — explicit bounds on the three correction factors and the
  explicit finite-`ξ` band of the exact centre threshold.
* `centre_threshold_ratio` — `ε > (π + η)ξ` unstable, `ε < (π − η)ξ` stable for small `ξ`, `ε`;
  `centre_levels_agree` — the same cone for L1 and L2 at `Ω = ν₁ + ν₂`.
* `reparam`, `reparamDeriv`, `twoPiece`, `hasDerivAt_reparam`, `continuous_reparam`,
  `continuous_reparamDeriv`, `reparam_zero`, `reparam_half`, `reparam_period`,
  `reparamDeriv_half`, `abs_reparamDeriv_le`, `continuous_twoPiece`, `norm_twoPiece_le`,
  `integral_twoPiece`, `transition_twoPiece` — the time change: a continuous field with the same
  average whose transition over `[0, T]` is `Φ_{G₂}(T, T/2) Φ_{G₁}(T/2, 0)`.
* `twoPiece_averaging_schurStable`, `twoPiece_averaging_floquetUnstable` — first-order averaging
  across a switching instant.
* `continuous_frameField_const`, `norm_frameField_const_le`, `exp_mul_frame`,
  `meissnerMonodromy_mul_scale` — `e^{(t − a)B} P(a) = P(t) Φ_G(t, a)`, hence
  `M D = −D Φ₋(T, T/2) Φ₊(T/2, 0)`; `schurStable_iff_of_mul_eq_neg` — `M D = −D P`: same
  stability, eigenvalues `ρ ↦ −ρ`.
* `integral_frameField_const`, `integral_halves`, `averagedMatrix_eq_halves` — the half-period
  average of two frozen levels is the L2 matrix of the square wave.
* `averagedMatrix_scaled`, `meissner_averaging_stable`, `meissner_averaging_unstable` — in the
  distinguished scaling the L2 matrix is `μ · slowFlowMatrix s d e` and its verdicts hold for the
  exact Meissner monodromy for all small `μ > 0`.
-/

noncomputable section
namespace powerlib.ParametricResonance.SquareWave

open Matrix Complex Set Filter Topology MeasureTheory
open powerlib.Periodic (oscMatrix)
open powerlib.ParametricResonance.NormalForm (rot quarter)
open powerlib.ParametricResonance.TwoToOne (refl1 refl2)
open powerlib.SpecialFunctions.PeriodicWaves (squareWave cosCoeff sinCoeff coeff amp)
open scoped Matrix.Norms.Operator

/-! ## The rotating frame -/

/-- The velocity scaling `(x, ẋ) = D z`, `z = (x, −2ẋ/ω)`. -/
def scale (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -(ω / 2)]

/-- The inverse scaling `D⁻¹ = diag(1, −2/ω)`. -/
def scaleInv (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -(2 / ω)]

/-- The frame `P(t) = D R(ωt/2)`: `(x, ẋ) = P(t) w`. -/
def frame (ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := scale ω * rot (ω * t / 2)

/-- The inverse frame `P(t)⁻¹ = R(−ωt/2) D⁻¹`. -/
def frameInv (ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := rot (-(ω * t / 2)) * scaleInv ω

/-- The residual of a frozen stiffness `k` in the scaled coordinates, after removing the rotation
at `ω/2`: `[[0, 0], [(4k − ω²)/(2ω), −2c]]`. -/
def residual (c k ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; (4 * k - ω ^ 2) / (2 * ω), -(2 * c)]

/-- The rotating-frame field of `ẍ + 2cẋ + k(t)x = 0` at half the pump frequency `ω`:
`G(t) = R(−ωt/2) N(t) R(ωt/2)`, `N(t) = residual c (k t) ω`. -/
def frameField (c ω : ℝ) (k : ℝ → ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rot (-(ω * t / 2)) * residual c (k t) ω * rot (ω * t / 2)

@[tmio T, powerlib_foundation] theorem scale_mul_scaleInv {ω : ℝ} (hω : ω ≠ 0) :
    scale ω * scaleInv ω = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [scale, scaleInv]; field_simp

@[tmio T, powerlib_foundation] theorem scaleInv_mul_scale {ω : ℝ} (hω : ω ≠ 0) :
    scaleInv ω * scale ω = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [scale, scaleInv, hω]

/-- In the scaled coordinates the oscillator is the rotation at `ω/2` plus the residual:
`D⁻¹ A = ((ω/2) J + N) D⁻¹`, `A = oscMatrix c k`. -/
@[tmio T, powerlib_foundation] theorem scaleInv_mul_osc {ω : ℝ} (hω : ω ≠ 0) (c k : ℝ) :
    scaleInv ω * oscMatrix c k = ((ω / 2) • quarter + residual c k ω) * scaleInv ω := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [scaleInv, oscMatrix, quarter, residual, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try field_simp)
  all_goals ring

/-- An entry of a matrix as a continuous linear map. -/
private def entry (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[tmio T, powerlib_foundation] private theorem hasDerivAt_rot_neg (ω t : ℝ) :
    HasDerivAt (fun t => rot (-(ω * t / 2))) ((-(ω / 2)) • (rot (-(ω * t / 2)) * quarter)) t := by
  have h := NormalForm.hasDerivAt_rot (-ω) t
  have e : (fun t => rot (-ω * t / 2)) = fun t => rot (-(ω * t / 2)) := by
    funext s; congr 1; ring
  rw [e, show -ω * t / 2 = -(ω * t / 2) by ring, show -ω / 2 = -(ω / 2) by ring] at h
  exact h

@[tmio T, powerlib_foundation] private theorem hasDerivAt_frameInv (ω t : ℝ) :
    HasDerivAt (fun t => frameInv ω t)
      ((-(ω / 2)) • (rot (-(ω * t / 2)) * quarter) * scaleInv ω) t :=
  (hasDerivAt_rot_neg ω t).mul_const (scaleInv ω)

/-- **The rotating frame is exact (matrix solutions).** If `Ẏ = A(t) Y` (within any set `s`,
`A(t) = oscMatrix c (k t)`), then `W(t) = P(t)⁻¹ Y(t)` satisfies `Ẇ = G(t) W`, `G` the
rotating-frame field. -/
@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_frameInv_mul {c ω : ℝ} (hω : ω ≠ 0)
    {k : ℝ → ℝ} {Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {s : Set ℝ} {t : ℝ}
    (hY : HasDerivWithinAt Y (oscMatrix c (k t) * Y t) s t) :
    HasDerivWithinAt (fun t => frameInv ω t * Y t)
      (frameField c ω k t * (frameInv ω t * Y t)) s t := by
  have h := (hasDerivAt_frameInv ω t).hasDerivWithinAt (s := s) |>.mul hY
  refine h.congr_deriv ?_
  have hr := TwoToOne.rot_mul_rot_neg (ω * t / 2)
  have e1 : frameInv ω t * (oscMatrix c (k t) * Y t) =
      rot (-(ω * t / 2)) * (((ω / 2) • quarter + residual c (k t) ω) * scaleInv ω) * Y t := by
    rw [frameInv, ← scaleInv_mul_osc hω]; simp only [Matrix.mul_assoc]
  rw [e1, frameField, frameInv]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (rot (ω * t / 2)) (rot (-(ω * t / 2))), hr, Matrix.one_mul]
  module

/-- **The rotating frame is exact (vector solutions).** If `ẏ = A(t) y` within `s`, then
`w(t) = P(t)⁻¹ y(t)` satisfies `ẇ = G(t) w` within `s`. -/
@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_frameInv_mulVec {c ω : ℝ} (hω : ω ≠ 0)
    {k : ℝ → ℝ} {y : ℝ → Fin 2 → ℝ} {s : Set ℝ} {t : ℝ}
    (hy : HasDerivWithinAt y (oscMatrix c (k t) *ᵥ y t) s t) :
    HasDerivWithinAt (fun t => frameInv ω t *ᵥ y t)
      (frameField c ω k t *ᵥ (frameInv ω t *ᵥ y t)) s t := by
  have hM := (hasDerivAt_frameInv ω t).hasDerivWithinAt (s := s)
  have h : HasDerivWithinAt (fun t => frameInv ω t *ᵥ y t)
      (((-(ω / 2)) • (rot (-(ω * t / 2)) * quarter) * scaleInv ω) *ᵥ y t +
        frameInv ω t *ᵥ (oscMatrix c (k t) *ᵥ y t)) s t := by
    rw [hasDerivWithinAt_pi]
    intro i
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin 2)), HasDerivWithinAt
        (fun t => frameInv ω t i j * y t j)
        (((-(ω / 2)) • (rot (-(ω * t / 2)) * quarter) * scaleInv ω) i j * y t j +
          frameInv ω t i j * (oscMatrix c (k t) *ᵥ y t) j) s t := fun j _ =>
      ((entry i j).hasFDerivAt.comp_hasDerivWithinAt t hM).mul
        (hasDerivWithinAt_pi.1 hy j)
    have hs := HasDerivWithinAt.fun_sum hj
    convert hs using 1
    · funext r; simp [Matrix.mulVec, dotProduct]
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply]
      ring
  refine h.congr_deriv ?_
  have hr := TwoToOne.rot_mul_rot_neg (ω * t / 2)
  have e1 : frameInv ω t *ᵥ (oscMatrix c (k t) *ᵥ y t) =
      (rot (-(ω * t / 2)) * (((ω / 2) • quarter + residual c (k t) ω) * scaleInv ω)) *ᵥ y t := by
    rw [Matrix.mulVec_mulVec, frameInv, Matrix.mul_assoc, scaleInv_mul_osc hω]
  rw [e1, frameField, frameInv, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (rot (ω * t / 2)) (rot (-(ω * t / 2))), hr, Matrix.one_mul]
  module

/-! ## The averaged (L2) model of an arbitrary periodic modulation -/

/-- The rotating-frame field in the basis `I, J, E₁, E₂`: with `n = (4k − ω²)/(2ω)`,
`G = −c I + (n/2) J + (c cos ωt + (n/2) sin ωt) E₁ + ((n/2) cos ωt − c sin ωt) E₂`. -/
@[tmio T, powerlib_foundation] theorem frameField_eq (c ω : ℝ) (k : ℝ → ℝ) (t : ℝ) :
    frameField c ω k t = (-c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      ((4 * k t - ω ^ 2) / (2 * ω) / 2) • quarter +
      (c * Real.cos (ω * t) + (4 * k t - ω ^ 2) / (2 * ω) / 2 * Real.sin (ω * t)) • refl1 +
      ((4 * k t - ω ^ 2) / (2 * ω) / 2 * Real.cos (ω * t) - c * Real.sin (ω * t)) • refl2 := by
  rw [frameField, TwoToOne.rot_conj]
  simp only [residual, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  congr 2 <;> [congr 2; congr 1; congr 1] <;> ring

/-- The first-order averaged (L2) state matrix of `ẍ + 2cẋ + ω₀²(1 + p(t))x = 0` at the pump
frequency `ω`: the mean `(1/T) ∫₀ᵀ G` of the rotating-frame field over the pump period `T`. -/
def averagedMatrix (c ω₀ ω T : ℝ) (p : ℝ → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  T⁻¹ • ∫ t in (0 : ℝ)..T, frameField c ω (fun t => ω₀ ^ 2 * (1 + p t)) t

@[tmio T, powerlib_foundation] private theorem integral_cos_period {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) : ∫ t in (0 : ℝ)..T, Real.cos (ω * t) = 0 := by
  have h := TwoToOne.integral_cos_mul_period hω 1 one_ne_zero
  simp only [Nat.cast_one, one_mul] at h
  rw [hT]; exact h

@[tmio T, powerlib_foundation] private theorem integral_sin_period {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) : ∫ t in (0 : ℝ)..T, Real.sin (ω * t) = 0 := by
  have h := TwoToOne.integral_sin_mul_period hω 1 one_ne_zero
  simp only [Nat.cast_one, one_mul] at h
  rw [hT]; exact h

@[tmio T, powerlib_foundation] private theorem arg_eq {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) (t : ℝ) : 2 * Real.pi * ((1 : ℕ) : ℝ) * t / T = ω * t := by
  rw [hT]; field_simp; ring

@[tmio T, powerlib_foundation] private theorem integral_mul_sin {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) (p : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..T, p t * Real.sin (ω * t) = T / 2 * sinCoeff T p 1 := by
  have hT0 : T ≠ 0 := by rw [hT]; positivity
  simp only [sinCoeff, arg_eq hω hT]
  field_simp

@[tmio T, powerlib_foundation] private theorem integral_mul_cos {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) (p : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..T, p t * Real.cos (ω * t) = T / 2 * cosCoeff T p 1 := by
  have hT0 : T ≠ 0 := by rw [hT]; positivity
  simp only [cosCoeff, arg_eq hω hT]
  field_simp

/-- **The L2 model of an arbitrary waveform is the 2:1 slow flow.** For an interval-integrable
modulation `p`, pump frequency `ω > 0` and period `T = 2π/ω`, the averaged matrix is
`slowFlowMatrix c Δ g` with damping `c`, detuning `Δ = (ω²/4 − ω₀²(1 + p̄))/ω` from `ω/2`
(`p̄ = (1/T) ∫₀ᵀ p`) and pump coefficient `g = ω₀² (b₁ + j a₁)/(2ω)`, `a₁`, `b₁` the cosine and
sine coefficients of the fundamental of `p`. -/
@[tmio T, powerlib_foundation] theorem averagedMatrix_eq (c ω₀ : ℝ) {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) {p : ℝ → ℝ} (hp : IntervalIntegrable p volume 0 T) :
    averagedMatrix c ω₀ ω T p = slowFlowMatrix c
      ((ω ^ 2 / 4 - ω₀ ^ 2 * (1 + T⁻¹ * ∫ t in (0 : ℝ)..T, p t)) / ω)
      ⟨ω₀ ^ 2 * sinCoeff T p 1 / (2 * ω), ω₀ ^ 2 * cosCoeff T p 1 / (2 * ω)⟩ := by
  have hT0 : 0 < T := by rw [hT]; positivity
  have hs := integral_sin_period hω hT
  have hc := integral_cos_period hω hT
  have hps := integral_mul_sin hω hT p
  have hpc := integral_mul_cos hω hT p
  set n : ℝ → ℝ := fun t => (4 * (ω₀ ^ 2 * (1 + p t)) - ω ^ 2) / (2 * ω) / 2 with hn
  have hn' : ∀ t, n t = (4 * ω₀ ^ 2 - ω ^ 2) / (4 * ω) + ω₀ ^ 2 / ω * p t := fun t => by
    simp only [hn]; field_simp; ring
  have ip : IntervalIntegrable n volume 0 T := by
    have : n = fun t => (4 * ω₀ ^ 2 - ω ^ 2) / (4 * ω) + ω₀ ^ 2 / ω * p t := funext hn'
    rw [this]; exact intervalIntegrable_const.add (hp.const_mul _)
  have ics : ∀ a : ℝ, IntervalIntegrable (fun t => Real.cos (a * t)) volume 0 T := fun a =>
    (by fun_prop : Continuous fun t => Real.cos (a * t)).intervalIntegrable _ _
  have isn : ∀ a : ℝ, IntervalIntegrable (fun t => Real.sin (a * t)) volume 0 T := fun a =>
    (by fun_prop : Continuous fun t => Real.sin (a * t)).intervalIntegrable _ _
  have inS : IntervalIntegrable (fun t => n t * Real.sin (ω * t)) volume 0 T :=
    ip.mul_continuousOn (by fun_prop : Continuous fun t => Real.sin (ω * t)).continuousOn
  have inC : IntervalIntegrable (fun t => n t * Real.cos (ω * t)) volume 0 T :=
    ip.mul_continuousOn (by fun_prop : Continuous fun t => Real.cos (ω * t)).continuousOn
  have hpS : IntervalIntegrable (fun t => p t * Real.sin (ω * t)) volume 0 T :=
    hp.mul_continuousOn (by fun_prop : Continuous fun t => Real.sin (ω * t)).continuousOn
  have hpC : IntervalIntegrable (fun t => p t * Real.cos (ω * t)) volume 0 T :=
    hp.mul_continuousOn (by fun_prop : Continuous fun t => Real.cos (ω * t)).continuousOn
  -- the three scalar integrals
  have eN : ∫ t in (0 : ℝ)..T, n t =
      T * ((4 * ω₀ ^ 2 - ω ^ 2) / (4 * ω)) + ω₀ ^ 2 / ω * ∫ t in (0 : ℝ)..T, p t := by
    rw [intervalIntegral.integral_congr (fun t _ => hn' t),
      intervalIntegral.integral_add intervalIntegrable_const (hp.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero]
  have eS : ∫ t in (0 : ℝ)..T, n t * Real.sin (ω * t) = ω₀ ^ 2 / ω * (T / 2 * sinCoeff T p 1) := by
    have : (fun t => n t * Real.sin (ω * t)) = fun t =>
        (4 * ω₀ ^ 2 - ω ^ 2) / (4 * ω) * Real.sin (ω * t) + ω₀ ^ 2 / ω * (p t * Real.sin (ω * t)) :=
      funext fun t => by rw [hn']; ring
    rw [this, intervalIntegral.integral_add ((isn ω).const_mul _) (hpS.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hs, hps]
    ring
  have eC : ∫ t in (0 : ℝ)..T, n t * Real.cos (ω * t) = ω₀ ^ 2 / ω * (T / 2 * cosCoeff T p 1) := by
    have : (fun t => n t * Real.cos (ω * t)) = fun t =>
        (4 * ω₀ ^ 2 - ω ^ 2) / (4 * ω) * Real.cos (ω * t) + ω₀ ^ 2 / ω * (p t * Real.cos (ω * t)) :=
      funext fun t => by rw [hn']; ring
    rw [this, intervalIntegral.integral_add ((ics ω).const_mul _) (hpC.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hc, hpc]
    ring
  -- the matrix integral
  have hfun : (fun t => frameField c ω (fun t => ω₀ ^ 2 * (1 + p t)) t) = fun t =>
      (-c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + n t • quarter +
      (c * Real.cos (ω * t) + n t * Real.sin (ω * t)) • refl1 +
      (n t * Real.cos (ω * t) - c * Real.sin (ω * t)) • refl2 := funext fun t => frameField_eq _ _ _ t
  have i1 : IntervalIntegrable (fun t => c * Real.cos (ω * t) + n t * Real.sin (ω * t)) volume 0 T :=
    ((ics ω).const_mul c).add inS
  have i2 : IntervalIntegrable (fun t => n t * Real.cos (ω * t) - c * Real.sin (ω * t)) volume 0 T :=
    inC.sub ((isn ω).const_mul c)
  have hI : ∫ t in (0 : ℝ)..T, frameField c ω (fun t => ω₀ ^ 2 * (1 + p t)) t =
      (T • ((-c) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) + (∫ t in (0 : ℝ)..T, n t) • quarter +
      (∫ t in (0 : ℝ)..T, (c * Real.cos (ω * t) + n t * Real.sin (ω * t))) • refl1 +
      (∫ t in (0 : ℝ)..T, (n t * Real.cos (ω * t) - c * Real.sin (ω * t))) • refl2 := by
    rw [hfun, intervalIntegral.integral_add ?h1 ?h2, intervalIntegral.integral_add ?h3 ?h4,
      intervalIntegral.integral_add ?h5 ?h6, intervalIntegral.integral_const,
      intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
      intervalIntegral.integral_smul_const, sub_zero]
    case h5 => exact intervalIntegrable_const
    case h6 => exact ⟨ip.1.smul_const _, ip.2.smul_const _⟩
    case h4 => exact ⟨i1.1.smul_const _, i1.2.smul_const _⟩
    case h2 => exact ⟨i2.1.smul_const _, i2.2.smul_const _⟩
    case h3 => exact intervalIntegrable_const.add ⟨ip.1.smul_const _, ip.2.smul_const _⟩
    case h1 => exact (intervalIntegrable_const.add ⟨ip.1.smul_const _, ip.2.smul_const _⟩).add
                 ⟨i1.1.smul_const _, i1.2.smul_const _⟩
  rw [averagedMatrix, hI, intervalIntegral.integral_add ((ics ω).const_mul c) inS,
    intervalIntegral.integral_sub inC ((isn ω).const_mul c), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hc, hs, eN, eS, eC]
  have hT1 : T ≠ 0 := hT0.ne'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [slowFlowMatrix, quarter, refl1, refl2] <;> field_simp <;> ring

/-- **Only the fundamental enters.** The pump coefficient of the averaged model has modulus
`ω₀² m₁/(2ω)`, `m₁ = √(a₁² + b₁²)` the harmonic amplitude of the fundamental of `p`
(`SpecialFunctions.PeriodicWaves.amp`); every other harmonic of the modulation drops out at first
order. -/
@[tmio T, powerlib_foundation] theorem norm_pump_eq_amp (ω₀ : ℝ) {ω T : ℝ} (hω : 0 < ω)
    (hT : 0 < T) {p : ℝ → ℝ} (hp : IntervalIntegrable p volume 0 T) :
    ‖(⟨ω₀ ^ 2 * sinCoeff T p 1 / (2 * ω), ω₀ ^ 2 * cosCoeff T p 1 / (2 * ω)⟩ : ℂ)‖ =
      ω₀ ^ 2 * amp hT p 1 / (2 * ω) := by
  rw [SpecialFunctions.PeriodicWaves.amp_eq_sqrt hT hp, Complex.norm_def, Complex.normSq_mk]
  have h1 : (ω₀ ^ 2 * sinCoeff T p 1 / (2 * ω)) * (ω₀ ^ 2 * sinCoeff T p 1 / (2 * ω)) +
      (ω₀ ^ 2 * cosCoeff T p 1 / (2 * ω)) * (ω₀ ^ 2 * cosCoeff T p 1 / (2 * ω)) =
      (ω₀ ^ 2 / (2 * ω)) ^ 2 * (cosCoeff T p 1 ^ 2 + sinCoeff T p 1 ^ 2) := by ring
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-! ## The square wave -/

@[tmio T, powerlib_foundation] theorem intervalIntegrable_squareWave (ε T a b : ℝ) :
    IntervalIntegrable (squareWave ε T) volume a b := by
  have hm : Measurable (squareWave ε T) := by
    unfold squareWave
    exact Measurable.ite (measurableSet_lt ((measurable_fract).comp
      (measurable_id.div_const T)) measurable_const) measurable_const measurable_const
  have hb : ∀ t, ‖squareWave ε T t‖ ≤ |ε| := fun t => by
    unfold squareWave; split_ifs <;> simp
  refine ⟨IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable |ε|
    (Filter.Eventually.of_forall hb), IntegrableOn.of_bound measure_Ioc_lt_top
    hm.aestronglyMeasurable |ε| (Filter.Eventually.of_forall hb)⟩

@[tmio T, powerlib_foundation] private theorem fract_div_of_mem {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ico 0 T) : Int.fract (t / T) = t / T := by
  rw [Int.fract_eq_self]
  exact ⟨div_nonneg ht.1 hT.le, (div_lt_one hT).mpr ht.2⟩

/-- The square wave has zero mean over its period. -/
@[tmio T, powerlib_foundation] theorem integral_squareWave {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    ∫ t in (0 : ℝ)..T, squareWave ε T t = 0 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := T / 2)
    (intervalIntegrable_squareWave ε T _ _) (intervalIntegrable_squareWave ε T _ _),
    intervalIntegral.integral_congr_Ioo_of_le (a := 0) (b := T / 2) (g := fun _ => ε) (by positivity) (fun t ht => by
      have h2 : t < T / 2 := ht.2
      have hc : t / T < 1 / 2 := by rw [div_lt_iff₀ hT]; linarith
      have hf := fract_div_of_mem (t := t) hT ⟨ht.1.le, by linarith⟩
      simp only [squareWave, hf, hc, ↓reduceIte]),
    intervalIntegral.integral_congr_Ioo_of_le (a := T / 2) (b := T) (g := fun _ => -ε) (by linarith) (fun t ht => by
      have h1 : T / 2 < t := ht.1
      have hc : ¬ t / T < 1 / 2 := by rw [not_lt, le_div_iff₀ hT]; linarith
      have hf := fract_div_of_mem (t := t) hT ⟨by linarith, ht.2⟩
      simp only [squareWave, hf, hc, ↓reduceIte])]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **The fundamental of the square wave** (wave-1 coefficients
`SpecialFunctions.PeriodicWaves.coeff_squareWave`): `a₁ = 0`, `b₁ = 4ε/π`. -/
@[tmio T, powerlib_foundation] theorem fourier_squareWave {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    cosCoeff T (squareWave ε T) 1 = 0 ∧ sinCoeff T (squareWave ε T) 1 = 4 * ε / Real.pi := by
  have h := SpecialFunctions.PeriodicWaves.coeff_squareWave hT ε (n := 1) one_ne_zero
  rw [SpecialFunctions.PeriodicWaves.coeff_eq_cos_sin hT (intervalIntegrable_squareWave ε T 0 T)
    1] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp [Complex.div_re, Complex.div_im] at hre him
  constructor
  · linarith
  · field_simp at him ⊢
    linarith

/-- **The L2 model of the square-wave-modulated oscillator.** For
`ẍ + 2cẋ + ω₀²(1 + sq(t))x = 0`, `sq = squareWave ε T` (`+ε` on the first, `−ε` on the second half
period), `T = 2π/ω`: the averaged matrix is the 2:1 slow flow with damping `c`, detuning
`Δ = (ω²/4 − ω₀²)/ω` and real pump coefficient `g = 2ω₀²ε/(πω) = (4/π) · ω₀²ε/(2ω)`, the
sinusoidal-pump value `ω₀²h/(2ω)` at the fundamental amplitude `h = 4ε/π`. -/
@[tmio T, powerlib_foundation] theorem averagedMatrix_squareWave (c ω₀ ε : ℝ) {ω T : ℝ}
    (hω : 0 < ω) (hT : T = 2 * Real.pi / ω) :
    averagedMatrix c ω₀ ω T (squareWave ε T) =
      slowFlowMatrix c ((ω ^ 2 / 4 - ω₀ ^ 2) / ω) ⟨2 * ω₀ ^ 2 * ε / (Real.pi * ω), 0⟩ := by
  have hT0 : 0 < T := by rw [hT]; positivity
  rw [averagedMatrix_eq c ω₀ hω hT (intervalIntegrable_squareWave ε T 0 T),
    integral_squareWave hT0, (fourier_squareWave hT0 ε).1, (fourier_squareWave hT0 ε).2]
  congr 2
  · ring
  · field_simp; ring
  · simp

/-- **The L2 threshold of the square wave.** With damping `c ≥ 0`, the averaged model has an
exponent with positive real part iff `π ω √(c² + Δ²) < 2 |ε| ω₀²`, `Δ = (ω²/4 − ω₀²)/ω`; with
`c > 0` it is Hurwitz iff `2 |ε| ω₀² < π ω √(c² + Δ²)`. -/
@[tmio T, powerlib_foundation] theorem averaged_threshold {c ω₀ ε ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) :
    (0 ≤ c → ((∃ μ : ℂ, (Linear.characteristicMatrix
        (averagedMatrix c ω₀ ω T (squareWave ε T)) μ).det = 0 ∧ 0 < μ.re) ↔
      Real.pi * ω * √(c ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2) / ω) ^ 2) < 2 * |ε| * ω₀ ^ 2)) ∧
    (0 < c → (LinearSystems.IsHurwitz (averagedMatrix c ω₀ ω T (squareWave ε T)) ↔
      2 * |ε| * ω₀ ^ 2 < Real.pi * ω * √(c ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2) / ω) ^ 2))) := by
  set Δ := (ω ^ 2 / 4 - ω₀ ^ 2) / ω
  have hg : ‖(⟨2 * ω₀ ^ 2 * ε / (Real.pi * ω), 0⟩ : ℂ)‖ = 2 * |ε| * ω₀ ^ 2 / (Real.pi * ω) := by
    rw [Complex.norm_def, Complex.normSq_mk, mul_zero, add_zero, Real.sqrt_mul_self_eq_abs,
      abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi * ω),
      abs_of_nonneg (sq_nonneg ω₀), abs_two]
    ring
  have hpω : 0 < Real.pi * ω := by positivity
  have key : ∀ r : ℝ, 0 ≤ r → (r ^ 2 < ‖(⟨2 * ω₀ ^ 2 * ε / (Real.pi * ω), 0⟩ : ℂ)‖ ^ 2 ↔
      Real.pi * ω * r < 2 * |ε| * ω₀ ^ 2) := by
    intro r hr
    rw [hg, pow_lt_pow_iff_left₀ hr (by positivity) two_ne_zero, lt_div_iff₀ hpω, mul_comm]
  have key' : ∀ r : ℝ, 0 ≤ r → (‖(⟨2 * ω₀ ^ 2 * ε / (Real.pi * ω), 0⟩ : ℂ)‖ ^ 2 < r ^ 2 ↔
      2 * |ε| * ω₀ ^ 2 < Real.pi * ω * r) := by
    intro r hr
    rw [hg, pow_lt_pow_iff_left₀ (by positivity) hr two_ne_zero, div_lt_iff₀ hpω, mul_comm r]
  have hsq : √(c ^ 2 + Δ ^ 2) ^ 2 = c ^ 2 + Δ ^ 2 := Real.sq_sqrt (by positivity)
  rw [averagedMatrix_squareWave c ω₀ ε hω hT]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [Branches.slowFlow_unstable_iff, ← key _ (Real.sqrt_nonneg _), hsq]
    constructor
    · rintro (⟨h, -⟩ | ⟨⟨-, h⟩, -⟩)
      · exact absurd hc (not_le.mpr h)
      · exact h
    · intro h; exact Or.inr ⟨⟨hc, h⟩, not_lt.mpr hc⟩
  · rw [Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix, det_slowFlowMatrix,
      ← key' _ (Real.sqrt_nonneg _), hsq]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩

/-- **The L2 threshold in normalized form.** With `c = ξω₀`, `ω₀ > 0` and the normalized
detuning `d = (ω²/4 − ω₀²)/(ωω₀)` (`= Δ/ω₀`): the averaged model is unstable iff
`π (ω/(2ω₀)) √(ξ² + d²) < |ε|` (`ξ ≥ 0`) and Hurwitz iff `|ε| < π (ω/(2ω₀)) √(ξ² + d²)`
(`ξ > 0`). The factor `ω/(2ω₀)` is `1 + O(d)`, so to the order of the averaging
`ε_c^{L2} = π √(ξ² + d²)`. -/
@[tmio T, powerlib_foundation] theorem averaged_threshold_normalized {ω₀ ξ ε ω T : ℝ}
    (hω₀ : 0 < ω₀) (hω : 0 < ω) (hT : T = 2 * Real.pi / ω) :
    (0 ≤ ξ → ((∃ μ : ℂ, (Linear.characteristicMatrix
        (averagedMatrix (ξ * ω₀) ω₀ ω T (squareWave ε T)) μ).det = 0 ∧ 0 < μ.re) ↔
      Real.pi * (ω / (2 * ω₀)) * √(ξ ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2) / (ω * ω₀)) ^ 2) < |ε|)) ∧
    (0 < ξ → (LinearSystems.IsHurwitz (averagedMatrix (ξ * ω₀) ω₀ ω T (squareWave ε T)) ↔
      |ε| < Real.pi * (ω / (2 * ω₀)) * √(ξ ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2) / (ω * ω₀)) ^ 2))) := by
  obtain ⟨hU, hS⟩ := averaged_threshold (c := ξ * ω₀) (ω₀ := ω₀) (ε := ε) hω hT
  set d := (ω ^ 2 / 4 - ω₀ ^ 2) / (ω * ω₀)
  have hΔ : (ω ^ 2 / 4 - ω₀ ^ 2) / ω = d * ω₀ := by simp only [d]; field_simp
  have hsq : √((ξ * ω₀) ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2) / ω) ^ 2) = ω₀ * √(ξ ^ 2 + d ^ 2) := by
    rw [hΔ, show (ξ * ω₀) ^ 2 + (d * ω₀) ^ 2 = ω₀ ^ 2 * (ξ ^ 2 + d ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω₀.le]
  have e : Real.pi * ω * (ω₀ * √(ξ ^ 2 + d ^ 2)) =
      (Real.pi * (ω / (2 * ω₀)) * √(ξ ^ 2 + d ^ 2)) * (2 * ω₀ ^ 2) := by
    field_simp
  have e' : 2 * |ε| * ω₀ ^ 2 = |ε| * (2 * ω₀ ^ 2) := by ring
  have h2 : (0 : ℝ) < 2 * ω₀ ^ 2 := by positivity
  refine ⟨fun hξ => ?_, fun hξ => ?_⟩
  · rw [hU (by positivity), hsq, e, e', mul_lt_mul_iff_left₀ h2]
  · rw [hS (by positivity), hsq, e, e', mul_lt_mul_iff_left₀ h2]

/-- **`ε_c^{L2} = πξ` at the 2:1 resonance.** At the pump frequency `ω = 2ω₀` (`d = 0`) the
averaged square-wave model is unstable iff `πξ < |ε|` and Hurwitz iff `|ε| < πξ`. -/
@[tmio T, powerlib_foundation] theorem averaged_centre_threshold {ω₀ ξ ε : ℝ} (hω₀ : 0 < ω₀) :
    (0 ≤ ξ → ((∃ μ : ℂ, (Linear.characteristicMatrix (averagedMatrix (ξ * ω₀) ω₀ (2 * ω₀)
        (2 * Real.pi / (2 * ω₀)) (squareWave ε (2 * Real.pi / (2 * ω₀)))) μ).det = 0 ∧
          0 < μ.re) ↔ Real.pi * ξ < |ε|)) ∧
    (0 < ξ → (LinearSystems.IsHurwitz (averagedMatrix (ξ * ω₀) ω₀ (2 * ω₀)
        (2 * Real.pi / (2 * ω₀)) (squareWave ε (2 * Real.pi / (2 * ω₀)))) ↔
      |ε| < Real.pi * ξ)) := by
  obtain ⟨hU, hS⟩ := averaged_threshold_normalized (ξ := ξ) (ε := ε) hω₀
    (by positivity : (0 : ℝ) < 2 * ω₀) rfl
  have hd : ((2 * ω₀) ^ 2 / 4 - ω₀ ^ 2) / (2 * ω₀ * ω₀) = 0 := by ring_nf
  have h1 : 2 * ω₀ / (2 * ω₀) = 1 := div_self (by positivity)
  rw [hd, h1] at hU hS
  refine ⟨fun hξ => ?_, fun hξ => ?_⟩
  · rw [hU hξ]; simp [Real.sqrt_sq hξ]
  · rw [hS hξ]; simp [Real.sqrt_sq hξ.le]

/-- **The universal region lies inside the L2 stable region.** If the square-wave depth satisfies
the frequency- and waveform-free bound `|ε|/√(1 − |ε|) < 2ξ`, `ξ = c/ω₀`
(`UniversalThreshold.schurStable_of_threshold` with `m = 1`, `D = 2c`, `K̄ = ω₀²`; proved there
for continuous stiffness, so it does not itself cover the square wave), then the averaged model is
Hurwitz at every detuning for every pump frequency `ω ≥ (4/π) ω₀ √(1 − |ε|)`, in particular near
`2ω₀`: `2|ε|ω₀² < 4cω₀√(1 − |ε|) ≤ πωc ≤ πω√(c² + Δ²)`. At `ω = 2ω₀` the L2 threshold `πξ`
exceeds the universal one `2ξ√(1 − |ε|)` by the factor `π/(2√(1 − |ε|)) ≥ π/2`. -/
@[tmio T, powerlib_foundation] theorem averaged_hurwitz_of_universal {c ω₀ ε ω T : ℝ}
    (hω : 0 < ω) (hT : T = 2 * Real.pi / ω) (hω₀ : 0 < ω₀) (hc : 0 < c) (hε : |ε| < 1)
    (hu : |ε| / √(1 - |ε|) < 2 * c / ω₀) (hΩ : 4 * ω₀ * √(1 - |ε|) ≤ Real.pi * ω) :
    LinearSystems.IsHurwitz (averagedMatrix c ω₀ ω T (squareWave ε T)) := by
  rw [(averaged_threshold hω hT).2 hc]
  have hr : 0 < √(1 - |ε|) := Real.sqrt_pos.mpr (by linarith)
  have h1 : |ε| * ω₀ < 2 * c * √(1 - |ε|) := by
    rw [div_lt_div_iff₀ hr hω₀] at hu; linarith
  have h2 : c ≤ √(c ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2) / ω) ^ 2) :=
    calc c = √(c ^ 2) := (Real.sqrt_sq hc.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((ω ^ 2 / 4 - ω₀ ^ 2) / ω)])
  calc 2 * |ε| * ω₀ ^ 2 = 2 * ω₀ * (|ε| * ω₀) := by ring
    _ < 2 * ω₀ * (2 * c * √(1 - |ε|)) := mul_lt_mul_of_pos_left h1 (by positivity)
    _ = (4 * ω₀ * √(1 - |ε|)) * c := by ring
    _ ≤ (Real.pi * ω) * c := mul_le_mul_of_nonneg_right hΩ hc.le
    _ ≤ Real.pi * ω * √(c ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2) / ω) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ## The exact tongue centre against the averaged threshold -/

section Centre

open Meissner (meissnerMonodromy reducedTrace)

variable {c ω₀ ε T ν₁ ν₂ : ℝ}

/-- **Stable side of the exact tongue centre.** At `Ω = ν₁ + ν₂` with `c > 0`, the Meissner
monodromy is Schur stable iff `ε ω₀² |sin θ₁| < √(ν₁ν₂) (ν₁ + ν₂) sinh(πc/(ν₁ + ν₂))`, the
mirror of `Meissner.centre_threshold_iff`. -/
@[tmio T, powerlib_foundation] theorem centre_schurStable_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) (hc : 0 < c) (hε : 0 ≤ ε) (hT : T = 2 * Real.pi / (ν₁ + ν₂)) :
    LTI.SchurStable (meissnerMonodromy c ω₀ ε T) ↔
      ε * ω₀ ^ 2 * |Real.sin (ν₁ * T / 2)| <
        √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂)) := by
  have hT0 : 0 < T := by rw [hT]; positivity
  rw [Meissner.schurStable_iff hν₁ hν₂ h₁.ne' h₂.ne' hc hT0, Meissner.reducedTrace_centre h₁ h₂ hT]
  have hs : 0 < ν₁ + ν₂ := by linarith
  have hp : 0 < ν₁ * ν₂ := mul_pos h₁ h₂
  rw [show -2 - (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2 =
      -(2 + (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2) by ring, abs_neg,
    abs_of_nonneg (by positivity)]
  have hcosh : Real.cosh (c * T) = 1 + 2 * Real.sinh (c * T / 2) ^ 2 := by
    rw [show c * T = 2 * (c * T / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
    ring_nf
  have hdiff : ν₁ - ν₂ = 2 * ε * ω₀ ^ 2 / (ν₁ + ν₂) := by
    field_simp
    nlinarith
  have hcT : c * T / 2 = Real.pi * c / (ν₁ + ν₂) := by rw [hT]; field_simp
  rw [hcosh, hcT, hdiff]
  have hsh : 0 ≤ Real.sinh (Real.pi * c / (ν₁ + ν₂)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq : √(ν₁ * ν₂) ^ 2 = ν₁ * ν₂ := Real.sq_sqrt hp.le
  set L := √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂))
  set R := ε * ω₀ ^ 2 * |Real.sin (ν₁ * T / 2)|
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by positivity
  have e1 : 4 * (ν₁ * ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂)) ^ 2 =
      4 * L ^ 2 / (ν₁ + ν₂) ^ 2 := by
    simp only [L]; rw [mul_pow, mul_pow, hsq]; field_simp
  have e2 : (2 * ε * ω₀ ^ 2 / (ν₁ + ν₂)) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 =
      4 * R ^ 2 / (ν₁ + ν₂) ^ 2 := by
    simp only [R]; rw [mul_pow, mul_pow, sq_abs]; field_simp; ring
  have key : 2 + (2 * ε * ω₀ ^ 2 / (ν₁ + ν₂)) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2 <
      2 * (1 + 2 * Real.sinh (Real.pi * c / (ν₁ + ν₂)) ^ 2) ↔
      (2 * ε * ω₀ ^ 2 / (ν₁ + ν₂)) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 <
        4 * (ν₁ * ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂)) ^ 2 := by
    rw [div_mul_eq_mul_div, ← sub_pos]
    conv_rhs => rw [← sub_pos]
    have e : 2 * (1 + 2 * Real.sinh (Real.pi * c / (ν₁ + ν₂)) ^ 2) -
        (2 + (2 * ε * ω₀ ^ 2 / (ν₁ + ν₂)) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 / (ν₁ * ν₂)) =
        (4 * (ν₁ * ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂)) ^ 2 -
          (2 * ε * ω₀ ^ 2 / (ν₁ + ν₂)) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2) / (ν₁ * ν₂) := by
      field_simp; ring
    rw [e]
    exact div_pos_iff_of_pos_right hp
  rw [key, e1, e2, div_lt_div_iff_of_pos_right (by positivity), mul_lt_mul_iff_right₀ four_pos]
  exact pow_lt_pow_iff_left₀ hR hL two_ne_zero

@[tmio T, powerlib_foundation] private theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have h1 : ∫ t in (0 : ℝ)..x, Real.cosh t = Real.sinh x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.sinh)
      (fun t _ => Real.hasDerivAt_sinh t) (Real.continuous_cosh.intervalIntegrable _ _),
      Real.sinh_zero, sub_zero]
  have h2 : ∫ t in (0 : ℝ)..x, Real.cosh t ≤ ∫ _ in (0 : ℝ)..x, Real.cosh x :=
    intervalIntegral.integral_mono_on hx (Real.continuous_cosh.intervalIntegrable _ _)
      intervalIntegrable_const (fun t ht => Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg ht.1, abs_of_nonneg hx]; exact ht.2))
  rw [h1, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h2
  exact h2

variable {ξ : ℝ}

/-- **The three correction factors at the exact centre, bounded explicitly.** With `c = ξω₀`,
`ω₀ > 0`, `ξ ≥ 0`, both half periods oscillatory, `Ω = ν₁ + ν₂`: the exact criterion reads
`ε |sin θ₁| ≷ πξ · (√(ν₁ν₂)/ω₀) · (sinh x/x)`, `x = πξω₀/(ν₁ + ν₂)`, and
* `ω₀ √(1 − ε − ξ²) ≤ √(ν₁ν₂) ≤ ω₀ √(1 − ξ²)`;
* `πξω₀ ≤ (ν₁ + ν₂) sinh x ≤ πξω₀ cosh(πξ/√(2(1 − ξ²)))`;
* `cos(πε/(2(1 − ξ²))) ≤ |sin θ₁| ≤ 1`, `θ₁ = ν₁T/2`. -/
@[tmio T, powerlib_foundation] theorem centre_factors (hω : 0 < ω₀) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε)
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2)
    (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hT : T = 2 * Real.pi / (ν₁ + ν₂)) :
    (ω₀ * √(1 - ε - ξ ^ 2) ≤ √(ν₁ * ν₂) ∧ √(ν₁ * ν₂) ≤ ω₀ * √(1 - ξ ^ 2)) ∧
    (Real.pi * ξ * ω₀ ≤ (ν₁ + ν₂) * Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂)) ∧
      (ν₁ + ν₂) * Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂)) ≤
        Real.pi * ξ * ω₀ * Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2)))) ∧
    (Real.cos (Real.pi * ε / (2 * (1 - ξ ^ 2))) ≤ |Real.sin (ν₁ * T / 2)| ∧
      |Real.sin (ν₁ * T / 2)| ≤ 1) := by
  have hs : 0 < ν₁ + ν₂ := by linarith
  have hp : 0 < ν₁ * ν₂ := mul_pos h₁ h₂
  have h12 : ν₂ ≤ ν₁ := by nlinarith
  have hpos : 0 < 1 - ε - ξ ^ 2 := by
    have : 0 < ω₀ ^ 2 * (1 - ε - ξ ^ 2) := by nlinarith
    exact pos_of_mul_pos_right this (by positivity)
  have hξ1 : 0 < 1 - ξ ^ 2 := by linarith
  have hsq₂ : ν₂ ^ 2 = (ω₀ * √(1 - ε - ξ ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpos.le, hν₂]; ring
  have hν₂eq : ν₂ = ω₀ * √(1 - ε - ξ ^ 2) :=
    (pow_left_inj₀ h₂.le (by positivity) two_ne_zero).mp hsq₂
  have hsum2 : 2 * ω₀ ^ 2 * (1 - ξ ^ 2) ≤ (ν₁ + ν₂) ^ 2 := by nlinarith
  have hsumge : ω₀ * √(2 * (1 - ξ ^ 2)) ≤ ν₁ + ν₂ := by
    rw [← Real.sqrt_sq hω.le, ← Real.sqrt_mul (sq_nonneg _), ← Real.sqrt_sq hs.le]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, Real.abs_sin_le_one _⟩⟩
  · calc ω₀ * √(1 - ε - ξ ^ 2) = √(ν₂ ^ 2) := by rw [Real.sqrt_sq h₂.le, hν₂eq]
      _ ≤ √(ν₁ * ν₂) := Real.sqrt_le_sqrt (by nlinarith)
  · have hprod : (ν₁ * ν₂) ^ 2 ≤ (ω₀ ^ 2 * (1 - ξ ^ 2)) ^ 2 := by
      have : (ν₁ * ν₂) ^ 2 = (ω₀ ^ 2 * (1 - ξ ^ 2)) ^ 2 - (ε * ω₀ ^ 2) ^ 2 := by
        rw [mul_pow, hν₁, hν₂]; ring
      rw [this]; nlinarith [sq_nonneg (ε * ω₀ ^ 2)]
    have hle : ν₁ * ν₂ ≤ ω₀ ^ 2 * (1 - ξ ^ 2) :=
      (pow_le_pow_iff_left₀ hp.le (by positivity) two_ne_zero).mp hprod
    rw [show ω₀ * √(1 - ξ ^ 2) = √(ω₀ ^ 2 * (1 - ξ ^ 2)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω.le]]
    exact Real.sqrt_le_sqrt hle
  · have hx : Real.pi * (ξ * ω₀) / (ν₁ + ν₂) ≤ Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂)) :=
      Real.self_le_sinh_iff.mpr (by positivity)
    calc Real.pi * ξ * ω₀ = (ν₁ + ν₂) * (Real.pi * (ξ * ω₀) / (ν₁ + ν₂)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hs.le
  · set x := Real.pi * (ξ * ω₀) / (ν₁ + ν₂)
    have hx0 : 0 ≤ x := by positivity
    have hxm : x ≤ Real.pi * ξ / √(2 * (1 - ξ ^ 2)) := by
      have hr : 0 < √(2 * (1 - ξ ^ 2)) := Real.sqrt_pos.mpr (by linarith)
      simp only [x]
      rw [div_le_div_iff₀ hs hr]
      calc Real.pi * (ξ * ω₀) * √(2 * (1 - ξ ^ 2)) = Real.pi * ξ * (ω₀ * √(2 * (1 - ξ ^ 2))) := by
            ring
        _ ≤ Real.pi * ξ * (ν₁ + ν₂) := mul_le_mul_of_nonneg_left hsumge (by positivity)
    have hc : Real.cosh x ≤ Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2))) :=
      Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hx0, abs_of_nonneg (hx0.trans hxm)]; exact hxm)
    calc (ν₁ + ν₂) * Real.sinh x ≤ (ν₁ + ν₂) * (x * Real.cosh x) :=
          mul_le_mul_of_nonneg_left (sinh_le_mul_cosh hx0) hs.le
      _ = Real.pi * ξ * ω₀ * Real.cosh x := by simp only [x]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
  · set u := Real.pi * ε * ω₀ ^ 2 / (ν₁ + ν₂) ^ 2
    have hθ : ν₁ * T / 2 = Real.pi / 2 + u := by
      rw [hT]
      simp only [u]
      field_simp
      linear_combination hν₁ - hν₂
    have hu0 : 0 ≤ u := by positivity
    have hum : u ≤ Real.pi * ε / (2 * (1 - ξ ^ 2)) := by
      simp only [u]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hsum2 (by positivity : (0 : ℝ) ≤ Real.pi * ε)
      nlinarith
    have humπ : Real.pi * ε / (2 * (1 - ξ ^ 2)) ≤ Real.pi / 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.pi_pos]
    have hcu : 0 ≤ Real.cos u :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hum.trans humπ⟩
    rw [hθ, add_comm, Real.sin_add_pi_div_two, abs_of_nonneg hcu]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hu0 (humπ.trans (by linarith [Real.pi_pos])) hum

/-- **The exact centre threshold in an explicit band (finite `ξ`).** With `c = ξω₀ > 0` at the
centre `Ω = ν₁ + ν₂` of the principal Meissner tongue:
* `ε < πξ √(1 − ε − ξ²)` gives Schur stability;
* `πξ √(1 − ξ²) cosh(πξ/√(2(1 − ξ²))) < ε cos(πε/(2(1 − ξ²)))` gives Floquet instability.
Both bounds tend to the first-order value `πξ` as `ε, ξ → 0`; they quantify the gap from it
through the three factors of `centre_factors`. -/
@[tmio T, powerlib_foundation] theorem centre_band (hω : 0 < ω₀) (hξ : 0 < ξ) (hε : 0 ≤ ε)
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2)
    (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hT : T = 2 * Real.pi / (ν₁ + ν₂)) :
    (ε < Real.pi * ξ * √(1 - ε - ξ ^ 2) →
      LTI.SchurStable (meissnerMonodromy (ξ * ω₀) ω₀ ε T)) ∧
    (Real.pi * ξ * √(1 - ξ ^ 2) * Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2))) <
        ε * Real.cos (Real.pi * ε / (2 * (1 - ξ ^ 2))) →
      ∃ μ ∈ spectrum ℂ ((meissnerMonodromy (ξ * ω₀) ω₀ ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) := by
  obtain ⟨⟨f1l, f1u⟩, ⟨f2l, f2u⟩, ⟨f3l, f3u⟩⟩ :=
    centre_factors hω hξ.le hε hν₁ hν₂ h₁ h₂ hT
  have hs : 0 < ν₁ + ν₂ := by linarith
  have hsh : 0 ≤ Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq : 0 ≤ √(ν₁ * ν₂) := Real.sqrt_nonneg _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [centre_schurStable_iff hν₁ hν₂ h₁ h₂ (by positivity) hε hT]
    calc ε * ω₀ ^ 2 * |Real.sin (ν₁ * T / 2)| ≤ ε * ω₀ ^ 2 := by
          have : 0 ≤ ε * ω₀ ^ 2 := by positivity
          nlinarith
      _ < Real.pi * ξ * √(1 - ε - ξ ^ 2) * ω₀ ^ 2 := by
          exact mul_lt_mul_of_pos_right h (by positivity)
      _ = (ω₀ * √(1 - ε - ξ ^ 2)) * (Real.pi * ξ * ω₀) := by ring
      _ ≤ √(ν₁ * ν₂) * ((ν₁ + ν₂) * Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂))) :=
          mul_le_mul f1l f2l (by positivity) hsq
      _ = _ := by ring
  · rw [Meissner.centre_threshold_iff hν₁ hν₂ h₁ h₂ (by positivity) hε hT]
    calc √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂))
        = √(ν₁ * ν₂) * ((ν₁ + ν₂) * Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂))) := by ring
      _ ≤ (ω₀ * √(1 - ξ ^ 2)) *
            (Real.pi * ξ * ω₀ * Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2)))) :=
          mul_le_mul f1u f2u (by positivity) (by positivity)
      _ = Real.pi * ξ * √(1 - ξ ^ 2) * Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2))) *
            ω₀ ^ 2 := by ring
      _ < ε * Real.cos (Real.pi * ε / (2 * (1 - ξ ^ 2))) * ω₀ ^ 2 :=
          mul_lt_mul_of_pos_right h (by positivity)
      _ ≤ ε * ω₀ ^ 2 * |Real.sin (ν₁ * T / 2)| := by
          have : 0 ≤ ε * ω₀ ^ 2 := by positivity
          nlinarith

/-- **First-order agreement at the exact centre: `ε_c/ξ → π`.** For every `η > 0` there is
`δ > 0` such that for `0 < ξ < δ` and `0 ≤ ε < δ`, at the centre `Ω = ν₁ + ν₂` of the principal
Meissner tongue with damping `c = ξω₀`: `ε > (π + η)ξ` gives Floquet instability and
`ε < (π − η)ξ` gives Schur stability: the exact centre threshold is `πξ (1 + o(1))` in cone
form, the first-order (L2) value at the 2:1 resonance (`averaged_centre_threshold`). -/
@[tmio T, powerlib_foundation] theorem centre_threshold_ratio {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ω₀ ξ ε ν₁ ν₂ T : ℝ, 0 < ω₀ → 0 < ξ → ξ < δ → 0 ≤ ε → ε < δ →
      ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2 →
      0 < ν₁ → 0 < ν₂ → T = 2 * Real.pi / (ν₁ + ν₂) →
      ((Real.pi + η) * ξ < ε →
        ∃ μ ∈ spectrum ℂ ((meissnerMonodromy (ξ * ω₀) ω₀ ε T).map (algebraMap ℝ ℂ)),
          1 < ‖μ‖) ∧
      (ε < (Real.pi - η) * ξ → LTI.SchurStable (meissnerMonodromy (ξ * ω₀) ω₀ ε T)) := by
  have hπ := Real.pi_pos
  -- the limit inequality `π cosh(πd) < (π + η) cos(πd)` near `d = 0`
  have hev : ∀ᶠ d in 𝓝 (0 : ℝ),
      Real.pi * Real.cosh (Real.pi * d) < (Real.pi + η) * Real.cos (Real.pi * d) := by
    have h1 : Tendsto (fun d => Real.pi * Real.cosh (Real.pi * d)) (𝓝 0) (𝓝 Real.pi) := by
      have : Continuous fun d => Real.pi * Real.cosh (Real.pi * d) := by fun_prop
      simpa using this.tendsto 0
    have h2 : Tendsto (fun d => (Real.pi + η) * Real.cos (Real.pi * d)) (𝓝 0)
        (𝓝 (Real.pi + η)) := by
      have : Continuous fun d => (Real.pi + η) * Real.cos (Real.pi * d) := by fun_prop
      simpa using this.tendsto 0
    exact h1.eventually_lt h2 (by linarith)
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff.mp hev
  set δ := min (min (r / 2) (1 / 4)) (η / (2 * Real.pi)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hδh : δ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδη : δ ≤ η / (2 * Real.pi) := min_le_right _ _
  have hPδ := hP (y := δ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]; exact hδr)
  refine ⟨δ, hδ0, fun ω₀ ξ ε ν₁ ν₂ T hω hξ hξδ hε hεδ hν₁ hν₂ h₁ h₂ hT => ?_⟩
  obtain ⟨hS, hU⟩ := centre_band hω hξ hε hν₁ hν₂ h₁ h₂ hT
  have hpos : 0 < 1 - ε - ξ ^ 2 := by
    have : 0 < ω₀ ^ 2 * (1 - ε - ξ ^ 2) := by nlinarith
    exact pos_of_mul_pos_right this (by positivity)
  have hξ2 : ξ ^ 2 < δ := by nlinarith
  refine ⟨fun h => hU ?_, fun h => hS ?_⟩
  · -- instability side
    have hξ1 : 1 / 2 ≤ 1 - ξ ^ 2 := by nlinarith
    have hsq1 : √(1 - ξ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
    have hr2 : 1 ≤ √(2 * (1 - ξ ^ 2)) := Real.one_le_sqrt.mpr (by linarith)
    have hxm : Real.pi * ξ / √(2 * (1 - ξ ^ 2)) ≤ Real.pi * δ := by
      rw [div_le_iff₀ (by linarith)]
      have h1 := mul_le_mul_of_nonneg_left hr2 (by positivity : (0 : ℝ) ≤ Real.pi * δ)
      have h2 : Real.pi * ξ ≤ Real.pi * δ := mul_le_mul_of_nonneg_left hξδ.le hπ.le
      linarith
    have hcosh : Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2))) ≤ Real.cosh (Real.pi * δ) :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; exact hxm)
    have hum : Real.pi * ε / (2 * (1 - ξ ^ 2)) ≤ Real.pi * δ := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : Real.pi * δ * 1 ≤ Real.pi * δ * (2 * (1 - ξ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 : Real.pi * ε ≤ Real.pi * δ := mul_le_mul_of_nonneg_left hεδ.le hπ.le
      linarith
    have hcos : Real.cos (Real.pi * δ) ≤ Real.cos (Real.pi * ε / (2 * (1 - ξ ^ 2))) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) hum
    have hcpos : 0 < Real.cos (Real.pi * δ) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
    have hcoshpos : 0 ≤ Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2))) := (Real.cosh_pos _).le
    calc Real.pi * ξ * √(1 - ξ ^ 2) * Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2)))
        ≤ Real.pi * ξ * 1 * Real.cosh (Real.pi * δ) := by
          gcongr
      _ = ξ * (Real.pi * Real.cosh (Real.pi * δ)) := by ring
      _ < ξ * ((Real.pi + η) * Real.cos (Real.pi * δ)) := mul_lt_mul_of_pos_left hPδ hξ
      _ = ((Real.pi + η) * ξ) * Real.cos (Real.pi * δ) := by ring
      _ ≤ ε * Real.cos (Real.pi * δ) := mul_le_mul_of_nonneg_right h.le hcpos.le
      _ ≤ ε * Real.cos (Real.pi * ε / (2 * (1 - ξ ^ 2))) := mul_le_mul_of_nonneg_left hcos hε
  · -- stability side
    have hroot : 1 - ε - ξ ^ 2 ≤ √(1 - ε - ξ ^ 2) := by
      rw [Real.le_sqrt hpos.le hpos.le]
      nlinarith
    have h2 : Real.pi * (2 * δ) ≤ η := by
      rw [le_div_iff₀ (by positivity)] at hδη; linarith
    calc ε < (Real.pi - η) * ξ := h
      _ ≤ Real.pi * ξ * (1 - 2 * δ) := by nlinarith
      _ ≤ Real.pi * ξ * (1 - ε - ξ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ ≤ Real.pi * ξ * √(1 - ε - ξ ^ 2) := mul_le_mul_of_nonneg_left hroot (by positivity)

@[tmio T, powerlib_foundation] private theorem prod_lower {ω₀ ξ ε ν₁ ν₂ : ℝ}
    (hp : 0 < ν₁ * ν₂) (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2)
    (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2) (h34 : 4 * ε ^ 2 + 4 * ξ ^ 2 ≤ 3) :
    ω₀ ^ 2 * (1 - ξ ^ 2) - 2 * ε ^ 2 * ω₀ ^ 2 ≤ ν₁ * ν₂ := by
  by_contra hlt
  push Not at hlt
  have hsq := pow_lt_pow_left₀ hlt hp.le two_ne_zero
  have e : (ω₀ ^ 2 * (1 - ξ ^ 2) - 2 * ε ^ 2 * ω₀ ^ 2) ^ 2 - (ν₁ * ν₂) ^ 2 =
      -((ω₀ ^ 2 * ε) ^ 2 * (3 - 4 * ε ^ 2 - 4 * ξ ^ 2)) := by
    rw [mul_pow, hν₁, hν₂]; ring
  have : 0 ≤ (ω₀ ^ 2 * ε) ^ 2 * (3 - 4 * ε ^ 2 - 4 * ξ ^ 2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  linarith

@[tmio T, powerlib_foundation] private theorem l2_key {η δ ξ ε : ℝ} (hξ : 0 < ξ)
    (hξ2 : ξ ^ 2 ≤ δ * ξ) (hε2 : ε ^ 2 ≤ δ * ε) (h : (Real.pi + η) * ξ < ε)
    (hk : Real.pi * δ * (Real.pi + η + 1) ≤ 2 * η) (hπδ : Real.pi * δ < 2) :
    2 * Real.pi * ξ + Real.pi * (ξ ^ 2 + ε ^ 2) < 2 * ε := by
  have h1 := mul_lt_mul_of_pos_right h (by linarith : (0 : ℝ) < 2 - Real.pi * δ)
  have h2 := mul_le_mul_of_nonneg_left hk hξ.le
  have h3 := mul_le_mul_of_nonneg_left hξ2 Real.pi_pos.le
  have h4 := mul_le_mul_of_nonneg_left hε2 Real.pi_pos.le
  nlinarith

/-- **L1 and L2 agree at the exact centre outside a thin cone.** For every `η > 0` there is
`δ > 0` such that for `0 < ξ < δ`, `0 ≤ ε < δ` and the pump at the exact centre
`Ω = ν₁ + ν₂` of the principal Meissner tongue (damping `c = ξω₀`):
* `ε > (π + η)ξ`: the Meissner system (L1) is Floquet unstable and the averaged model (L2) at the
  same pump frequency has an exponent with positive real part;
* `ε < (π − η)ξ`: L1 is Schur stable and L2 is Hurwitz.
The verdicts can differ only in the cone `|ε − πξ| ≤ ηξ` around the common first-order threshold
`πξ`; inside it the finite-`ξ` corrections of `centre_band` (L1) and the detuning
`ω₀² − Ω²/4 ≤ ω₀²(ξ² + ε²)` of the exact centre from `2ω₀` (L2) decide. -/
@[tmio T, powerlib_foundation] theorem centre_levels_agree {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ω₀ ξ ε ν₁ ν₂ : ℝ, 0 < ω₀ → 0 < ξ → ξ < δ → 0 ≤ ε → ε < δ →
      ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2 →
      0 < ν₁ → 0 < ν₂ →
      ((Real.pi + η) * ξ < ε →
        (∃ μ ∈ spectrum ℂ ((meissnerMonodromy (ξ * ω₀) ω₀ ε
          (2 * Real.pi / (ν₁ + ν₂))).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ∧
        ∃ μ : ℂ, (Linear.characteristicMatrix (averagedMatrix (ξ * ω₀) ω₀ (ν₁ + ν₂)
          (2 * Real.pi / (ν₁ + ν₂)) (squareWave ε (2 * Real.pi / (ν₁ + ν₂)))) μ).det = 0 ∧
          0 < μ.re) ∧
      (ε < (Real.pi - η) * ξ →
        LTI.SchurStable (meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))) ∧
        LinearSystems.IsHurwitz (averagedMatrix (ξ * ω₀) ω₀ (ν₁ + ν₂)
          (2 * Real.pi / (ν₁ + ν₂)) (squareWave ε (2 * Real.pi / (ν₁ + ν₂))))) := by
  have hπ := Real.pi_pos
  obtain ⟨δ₁, hδ₁, hL1⟩ := centre_threshold_ratio hη
  set δ := min δ₁ (min (1 / 4) (min (η / (2 * Real.pi))
    (2 * η / (Real.pi * (Real.pi + η + 1))))) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hδ1 : δ ≤ δ₁ := min_le_left _ _
  have hδh : δ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδη : δ ≤ η / (2 * Real.pi) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδη' : δ ≤ 2 * η / (Real.pi * (Real.pi + η + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hk : Real.pi * δ * (Real.pi + η + 1) ≤ 2 * η := by
    rw [le_div_iff₀ (by positivity)] at hδη'; linarith
  have h2δ : Real.pi * (2 * δ) ≤ η := by
    rw [le_div_iff₀ (by positivity)] at hδη; linarith
  have hπδ : Real.pi * δ < 2 := by
    have := mul_le_mul_of_nonneg_left hδh hπ.le
    linarith [Real.pi_lt_four]
  refine ⟨δ, hδ0, fun ω₀ ξ ε ν₁ ν₂ hω hξ hξδ hε hεδ hν₁ hν₂ h₁ h₂ => ?_⟩
  have hs : 0 < ν₁ + ν₂ := by linarith
  obtain ⟨hU1, hS1⟩ := hL1 ω₀ ξ ε ν₁ ν₂ _ hω hξ (hξδ.trans_le hδ1) hε (hεδ.trans_le hδ1) hν₁ hν₂
    h₁ h₂ rfl
  obtain ⟨hU2, hS2⟩ := averaged_threshold (c := ξ * ω₀) (ω₀ := ω₀) (ε := ε) hs rfl
  rw [abs_of_nonneg hε] at hU2 hS2
  have hdiff : ν₁ ^ 2 - ν₂ ^ 2 = 2 * ε * ω₀ ^ 2 := by rw [hν₁, hν₂]; ring
  have h12 : ν₂ ≤ ν₁ := by
    have : ν₂ ^ 2 ≤ ν₁ ^ 2 := by nlinarith [sq_nonneg ω₀]
    exact (pow_le_pow_iff_left₀ h₂.le h₁.le two_ne_zero).mp this
  have hpos : 0 < 1 - ε - ξ ^ 2 := by
    have : 0 < ω₀ ^ 2 * (1 - ε - ξ ^ 2) := by
      have h := pow_pos h₂ 2
      rw [hν₂] at h
      linarith [show ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2 = ω₀ ^ 2 * (1 - ε - ξ ^ 2) by ring]
    exact pos_of_mul_pos_right this (by positivity)
  have hξ2 : ξ ^ 2 ≤ δ * ξ := by rw [sq]; exact mul_le_mul_of_nonneg_right hξδ.le hξ.le
  have hε2 : ε ^ 2 ≤ δ * ε := by rw [sq]; exact mul_le_mul_of_nonneg_right hεδ.le hε
  have hξ4 : ξ ^ 2 ≤ 1 / 16 := by nlinarith
  have hε4 : ε ^ 2 ≤ 1 / 16 := by nlinarith
  set ω := ν₁ + ν₂
  set Δ := (ω ^ 2 / 4 - ω₀ ^ 2) / ω
  refine ⟨fun h => ⟨hU1 h, (hU2 (by positivity)).mpr ?_⟩,
    fun h => ⟨hS1 h, (hS2 (by positivity)).mpr ?_⟩⟩
  · -- the averaged model is unstable
    have hsum : ν₁ ^ 2 + ν₂ ^ 2 = 2 * ω₀ ^ 2 * (1 - ξ ^ 2) := by rw [hν₁, hν₂]; ring
    have hω2 : ω ^ 2 ≤ 4 * ω₀ ^ 2 := by
      have e : ω ^ 2 = 2 * (ν₁ ^ 2 + ν₂ ^ 2) - (ν₁ - ν₂) ^ 2 := by simp only [ω]; ring
      rw [e, hsum]; nlinarith [sq_nonneg (ν₁ - ν₂), sq_nonneg ξ, sq_nonneg ω₀]
    have hprod := prod_lower (mul_pos h₁ h₂) hν₁ hν₂ (by linarith)
    have hdet : ω₀ ^ 2 - ω ^ 2 / 4 ≤ ω₀ ^ 2 * (ξ ^ 2 + ε ^ 2) := by
      have e : ω ^ 2 = ν₁ ^ 2 + ν₂ ^ 2 + 2 * (ν₁ * ν₂) := by simp only [ω]; ring
      rw [e, hsum]; linarith
    have hΔ : ω * |Δ| = ω₀ ^ 2 - ω ^ 2 / 4 := by
      simp only [Δ]
      rw [abs_div, abs_of_pos hs, abs_of_nonpos (by linarith)]
      field_simp; ring
    have hsqrt : √((ξ * ω₀) ^ 2 + Δ ^ 2) ≤ ξ * ω₀ + |Δ| := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ ξ * ω₀ + |Δ|)]
      refine Real.sqrt_le_sqrt ?_
      have : 0 ≤ ξ * ω₀ * |Δ| := by positivity
      rw [add_sq, sq_abs]; linarith
    have hωle : ω ≤ 2 * ω₀ :=
      (pow_le_pow_iff_left₀ hs.le (by positivity) two_ne_zero).mp (by linarith)
    have key := l2_key hξ hξ2 hε2 h hk hπδ
    calc Real.pi * ω * √((ξ * ω₀) ^ 2 + Δ ^ 2) ≤ Real.pi * ω * (ξ * ω₀ + |Δ|) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = Real.pi * ξ * ω₀ * ω + Real.pi * (ω * |Δ|) := by ring
      _ ≤ Real.pi * ξ * ω₀ * (2 * ω₀) + Real.pi * (ω₀ ^ 2 * (ξ ^ 2 + ε ^ 2)) := by
          rw [hΔ]; gcongr
      _ = (2 * Real.pi * ξ + Real.pi * (ξ ^ 2 + ε ^ 2)) * ω₀ ^ 2 := by ring
      _ < 2 * ε * ω₀ ^ 2 := mul_lt_mul_of_pos_right key (by positivity)
  · -- the averaged model is Hurwitz
    have hν₂lo : ω₀ * (1 - ε - ξ ^ 2) ≤ ν₂ := by
      have hsq : (ω₀ * (1 - ε - ξ ^ 2)) ^ 2 ≤ ν₂ ^ 2 := by
        have e : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε - ξ ^ 2) := by rw [hν₂]; ring
        rw [e, mul_pow]
        have : (1 - ε - ξ ^ 2) ^ 2 ≤ 1 - ε - ξ ^ 2 := by
          rw [sq]; exact mul_le_of_le_one_left hpos.le (by nlinarith)
        exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
      exact (pow_le_pow_iff_left₀ (by positivity) h₂.le two_ne_zero).mp hsq
    have hsqrt : ξ * ω₀ ≤ √((ξ * ω₀) ^ 2 + Δ ^ 2) :=
      calc ξ * ω₀ = √((ξ * ω₀) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith [sq_nonneg Δ])
    have hlin : (Real.pi - η) * ξ ≤ Real.pi * ξ * (1 - ε - ξ ^ 2) := by
      have h3 : Real.pi * ξ * (ε + ξ ^ 2) ≤ Real.pi * ξ * (2 * δ) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have h4 := mul_le_mul_of_nonneg_right h2δ hξ.le
      nlinarith
    calc 2 * ε * ω₀ ^ 2 < 2 * ((Real.pi - η) * ξ) * ω₀ ^ 2 := by
          have := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < 2 * ω₀ ^ 2); linarith
      _ ≤ 2 * (Real.pi * ξ * (1 - ε - ξ ^ 2)) * ω₀ ^ 2 := by gcongr
      _ = Real.pi * (2 * (ω₀ * (1 - ε - ξ ^ 2))) * (ξ * ω₀) := by ring
      _ ≤ Real.pi * ω * (ξ * ω₀) := by
          gcongr; simp only [ω]; linarith
      _ ≤ Real.pi * ω * √((ξ * ω₀) ^ 2 + Δ ^ 2) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)

end Centre

/-! ## Averaging across a switching instant -/

section TwoPiece

variable {T : ℝ}

/-- The time change `τ(t) = t − (T/(4π)) sin(4πt/T)`, whose derivative `1 − cos(4πt/T)` vanishes
at `t = 0, T/2, T`. -/
def reparam (T t : ℝ) : ℝ := t - T / (4 * Real.pi) * Real.sin (4 * Real.pi * t / T)

/-- `τ'(t) = 1 − cos(4πt/T)`. -/
def reparamDeriv (T t : ℝ) : ℝ := 1 - Real.cos (4 * Real.pi * t / T)

/-- The two-piece field run with the time change: `τ'(t) G₁(τ(t))` up to `T/2`, `τ'(t) G₂(τ(t))`
after; continuous although `G₁(T/2) ≠ G₂(T/2)`, because `τ'(T/2) = 0`. -/
def twoPiece (G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (T t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if t ≤ T / 2 then reparamDeriv T t • G₁ (reparam T t) else reparamDeriv T t • G₂ (reparam T t)

@[tmio T, powerlib_foundation] theorem hasDerivAt_reparam (hT : 0 < T) (t : ℝ) :
    HasDerivAt (reparam T) (reparamDeriv T t) t := by
  have hπ := Real.pi_pos
  have h1 : HasDerivAt (fun t => 4 * Real.pi * t / T) (4 * Real.pi / T) t := by
    simpa using ((hasDerivAt_id t).const_mul (4 * Real.pi)).div_const T
  have h2 := ((Real.hasDerivAt_sin _).comp t h1).const_mul (T / (4 * Real.pi))
  have h3 := (hasDerivAt_id t).sub h2
  convert h3 using 1
  · funext s; simp [reparam]
  · simp only [reparamDeriv]; field_simp

@[tmio T, powerlib_foundation] theorem continuous_reparam : Continuous (reparam T) := by
  unfold reparam; fun_prop

@[tmio T, powerlib_foundation] theorem continuous_reparamDeriv :
    Continuous (reparamDeriv T) := by
  unfold reparamDeriv; fun_prop

@[tmio T, powerlib_foundation] theorem reparam_zero : reparam T 0 = 0 := by simp [reparam]

@[tmio T, powerlib_foundation] theorem reparam_half (hT : 0 < T) : reparam T (T / 2) = T / 2 := by
  have : 4 * Real.pi * (T / 2) / T = 2 * Real.pi := by field_simp; ring
  simp [reparam, this]

@[tmio T, powerlib_foundation] theorem reparam_period (hT : 0 < T) : reparam T T = T := by
  have : 4 * Real.pi * T / T = ((4 : ℕ) : ℝ) * Real.pi := by field_simp; push_cast; ring
  rw [reparam, this, Real.sin_nat_mul_pi]
  ring

@[tmio T, powerlib_foundation] theorem reparamDeriv_half (hT : 0 < T) :
    reparamDeriv T (T / 2) = 0 := by
  have : 4 * Real.pi * (T / 2) / T = 2 * Real.pi := by field_simp; ring
  simp [reparamDeriv, this]

@[tmio T, powerlib_foundation] theorem abs_reparamDeriv_le (t : ℝ) : |reparamDeriv T t| ≤ 2 := by
  have := Real.neg_one_le_cos (4 * Real.pi * t / T)
  have := Real.cos_le_one (4 * Real.pi * t / T)
  unfold reparamDeriv
  rw [abs_le]; constructor <;> linarith

@[tmio T, powerlib_foundation] theorem continuous_twoPiece (hT : 0 < T)
    {G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (h₁ : Continuous G₁) (h₂ : Continuous G₂) :
    Continuous (twoPiece G₁ G₂ T) := by
  refine Continuous.if_le (continuous_reparamDeriv.smul (h₁.comp continuous_reparam))
    (continuous_reparamDeriv.smul (h₂.comp continuous_reparam)) continuous_id continuous_const ?_
  intro t ht
  rw [show t = T / 2 from ht, reparamDeriv_half hT, zero_smul, zero_smul]

@[tmio T, powerlib_foundation] theorem norm_twoPiece_le {G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {M : ℝ} (h₁ : ∀ t, ‖G₁ t‖ ≤ M) (h₂ : ∀ t, ‖G₂ t‖ ≤ M) (t : ℝ) :
    ‖twoPiece G₁ G₂ T t‖ ≤ 2 * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h₁ 0)
  unfold twoPiece
  split_ifs
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_reparamDeriv_le t) (h₁ _) (norm_nonneg _) (by norm_num)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_reparamDeriv_le t) (h₂ _) (norm_nonneg _) (by norm_num)

/-- `∫₀ᵀ F = ∫₀^{T/2} G₁ + ∫_{T/2}^T G₂`: the time change keeps the averages of both pieces. -/
@[tmio T, powerlib_foundation] theorem integral_twoPiece (hT : 0 < T)
    {G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (h₁ : Continuous G₁) (h₂ : Continuous G₂) :
    ∫ t in (0 : ℝ)..T, twoPiece G₁ G₂ T t =
      (∫ t in (0 : ℝ)..T / 2, G₁ t) + ∫ t in T / 2..T, G₂ t := by
  have hc := continuous_twoPiece hT h₁ h₂
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := T / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in (0 : ℝ)..T / 2, twoPiece G₁ G₂ T t =
      ∫ t in (0 : ℝ)..T / 2, reparamDeriv T t • (G₁ ∘ reparam T) t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by positivity)] at ht
    simp only [twoPiece, ht.2, ↓reduceIte, Function.comp]
  have e2 : ∫ t in T / 2..T, twoPiece G₁ G₂ T t =
      ∫ t in T / 2..T, reparamDeriv T t • (G₂ ∘ reparam T) t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith)] at ht
    rcases ht.1.eq_or_lt with h | h
    · subst h
      simp only [twoPiece, le_refl, ↓reduceIte, reparamDeriv_half hT, zero_smul]
    · simp only [twoPiece, not_le.mpr h, ↓reduceIte, Function.comp]
  rw [e1, e2, intervalIntegral.integral_deriv_smul_comp (fun t _ => hasDerivAt_reparam hT t)
      continuous_reparamDeriv.continuousOn h₁,
    intervalIntegral.integral_deriv_smul_comp (fun t _ => hasDerivAt_reparam hT t)
      continuous_reparamDeriv.continuousOn h₂, reparam_zero, reparam_half hT, reparam_period hT]

/-- **The time change realizes the switched transition.** For continuous bounded `G₁`, `G₂`,
the transition matrix of the continuous field `F = twoPiece G₁ G₂ T` over `[0, T]` is the
product `Φ_{G₂}(T, T/2) Φ_{G₁}(T/2, 0)`: running `ẏ = G₁ y` on `[0, T/2]` and `ẏ = G₂ y` on
`[T/2, T]`. -/
@[tmio T, powerlib_foundation] theorem transition_twoPiece (hT : 0 < T)
    {G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M : ℝ} (h₁ : Continuous G₁) (h₂ : Continuous G₂)
    (hM₁ : ∀ t, ‖G₁ t‖ ≤ M) (hM₂ : ∀ t, ‖G₂ t‖ ≤ M) :
    Periodic.transition (twoPiece G₁ G₂ T) T 0 =
      Periodic.transition G₂ T (T / 2) * Periodic.transition G₁ (T / 2) 0 := by
  set a := T / 2 with ha
  set C := Periodic.transition G₁ a 0
  set Y₁ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => Periodic.transition G₁ (reparam T t) 0
  set Y₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t =>
    Periodic.transition G₂ (reparam T t) a * C
  set Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => if t ≤ a then Y₁ t else Y₂ t
  have d₁ : ∀ t, HasDerivAt Y₁ (reparamDeriv T t • (G₁ (reparam T t) * Y₁ t)) t := fun t =>
    (Dynamics.stm_hasDerivAt h₁ (reparam T t) 0).scomp t (hasDerivAt_reparam hT t)
  have d₂ : ∀ t, HasDerivAt Y₂ (reparamDeriv T t • (G₂ (reparam T t) * Y₂ t)) t := fun t => by
    have h := ((Dynamics.stm_hasDerivAt h₂ (reparam T t) a).scomp t
      (hasDerivAt_reparam hT t)).mul_const C
    have e : (reparamDeriv T t • (G₂ (reparam T t) *
        LinearSystems.stateTransitionMatrix G₂ (reparam T t) a)) * C =
        reparamDeriv T t • (G₂ (reparam T t) * Y₂ t) := by
      simp only [Y₂, smul_mul_assoc, Matrix.mul_assoc]
    exact h.congr_deriv e
  have hjoin : Y₁ a = Y₂ a := by
    simp only [Y₁, Y₂, C, ha, reparam_half hT, LinearSystems.stateTransitionMatrix_self,
      Matrix.one_mul]
  have hd : ∀ t, HasDerivAt Y (twoPiece G₁ G₂ T t * Y t) t := by
    intro t
    rcases lt_trichotomy t a with h | h | h
    · have hev : Y =ᶠ[𝓝 t] Y₁ := by
        filter_upwards [Iio_mem_nhds h] with u hu
        simp only [Y, (mem_Iio.mp hu).le, ↓reduceIte]
      have e : twoPiece G₁ G₂ T t * Y t = reparamDeriv T t • (G₁ (reparam T t) * Y₁ t) := by
        simp only [twoPiece, Y, ← ha, h.le, ↓reduceIte, smul_mul_assoc]
      rw [e]
      exact (d₁ t).congr_of_eventuallyEq hev
    · subst h
      have hz : twoPiece G₁ G₂ T a * Y a = 0 := by
        simp only [twoPiece, ha, le_refl, ↓reduceIte, reparamDeriv_half hT, zero_smul,
          Matrix.zero_mul]
      rw [hz]
      have hl : HasDerivWithinAt Y 0 (Iic a) a := by
        have h := (d₁ a).hasDerivWithinAt (s := Iic a)
        rw [ha, reparamDeriv_half hT, zero_smul, ← ha] at h
        exact h.congr (fun u hu => by simp only [Y, mem_Iic.mp hu, ↓reduceIte])
          (by simp only [Y, le_refl, ↓reduceIte])
      have hr : HasDerivWithinAt Y 0 (Ici a) a := by
        have h := (d₂ a).hasDerivWithinAt (s := Ici a)
        rw [ha, reparamDeriv_half hT, zero_smul, ← ha] at h
        refine h.congr (fun u hu => ?_) (by simp only [Y, le_refl, ↓reduceIte, hjoin])
        rcases (mem_Ici.mp hu).eq_or_lt with h' | h'
        · subst h'; simp only [Y, le_refl, ↓reduceIte, hjoin]
        · simp only [Y, not_le.mpr h', ↓reduceIte]
      have := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · have hev : Y =ᶠ[𝓝 t] Y₂ := by
        filter_upwards [Ioi_mem_nhds h] with u hu
        simp only [Y, not_le.mpr (mem_Ioi.mp hu), ↓reduceIte]
      have e : twoPiece G₁ G₂ T t * Y t = reparamDeriv T t • (G₂ (reparam T t) * Y₂ t) := by
        simp only [twoPiece, Y, ← ha, not_le.mpr h, ↓reduceIte, smul_mul_assoc]
      rw [e]
      exact (d₂ t).congr_of_eventuallyEq hev
  have hF := continuous_twoPiece hT h₁ h₂
  have hY : IsIntegralCurveOn Y (Periodic.matField (twoPiece G₁ G₂ T)) (Ici 0) :=
    fun t _ => (hd t).hasDerivWithinAt
  have h := Periodic.transition_unique hF (norm_twoPiece_le hM₁ hM₂) hY T hT.le
  have hY0 : Y 0 = 1 := by
    simp only [Y, Y₁, ha, (by positivity : (0 : ℝ) ≤ T / 2), ↓reduceIte, reparam_zero,
      LinearSystems.stateTransitionMatrix_self]
  have hYT : Y T = Periodic.transition G₂ T a * C := by
    simp only [Y, Y₂, ha, not_le.mpr (by linarith : T / 2 < T), ↓reduceIte, reparam_period hT]
  rw [hY0, Matrix.mul_one, hYT] at h
  exact h.symm

@[tmio T, powerlib_foundation] private theorem twoPiece_smul (μ : ℝ)
    (G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) :
    (fun t => μ • twoPiece G₁ G₂ T t) = twoPiece (fun t => μ • G₁ t) (fun t => μ • G₂ t) T := by
  funext t
  simp only [twoPiece]
  split_ifs <;> rw [smul_comm]

/-- **First-order averaging across a switching instant, stability.** Let `G₁`, `G₂` be
continuous and bounded, `T > 0`, and `Ḡ = (1/T)(∫₀^{T/2} G₁ + ∫_{T/2}^T G₂)` with
`tr Ḡ < 0 < det Ḡ` (Hurwitz). Then the period map `Φ_{εG₂}(T, T/2) Φ_{εG₁}(T/2, 0)` of the
switched system `ẏ = εG₁ y` on `[0, T/2]`, `ẏ = εG₂ y` on `[T/2, T]` is Schur stable for all
small `ε > 0`. The piecewise-continuous counterpart of `Averaging.averaging_schurStable`, which
it applies to the continuous time-changed field `twoPiece`. -/
@[tmio T, powerlib_foundation] theorem twoPiece_averaging_schurStable
    {G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M : ℝ} (h₁ : Continuous G₁) (h₂ : Continuous G₂)
    (hM₁ : ∀ t, ‖G₁ t‖ ≤ M) (hM₂ : ∀ t, ‖G₂ t‖ ≤ M) (hT : 0 < T)
    {Gbar : Matrix (Fin 2) (Fin 2) ℝ}
    (havg : (∫ t in (0 : ℝ)..T / 2, G₁ t) + ∫ t in T / 2..T, G₂ t = T • Gbar)
    (htr : Gbar.trace < 0) (hdet : 0 < Gbar.det) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable
      (Periodic.transition (fun t => ε • G₂ t) T (T / 2) *
        Periodic.transition (fun t => ε • G₁ t) (T / 2) 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM₁ 0)
  have h := Averaging.averaging_schurStable (continuous_twoPiece hT h₁ h₂)
    (norm_twoPiece_le hM₁ hM₂) (by positivity) hT
    ((integral_twoPiece hT h₁ h₂).trans havg) htr hdet
  filter_upwards [h] with ε hε
  have hε' : ∀ t, ‖ε • G₁ t‖ ≤ |ε| * M := fun t => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM₁ t) (abs_nonneg ε)
  have hε'' : ∀ t, ‖ε • G₂ t‖ ≤ |ε| * M := fun t => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM₂ t) (abs_nonneg ε)
  rw [Periodic.monodromy, zero_add, twoPiece_smul] at hε
  have e := transition_twoPiece hT (h₁.const_smul ε) (h₂.const_smul ε) hε' hε''
  exact e ▸ hε

/-- **First-order averaging across a switching instant, instability.** With `G₁`, `G₂`, `Ḡ` as
in `twoPiece_averaging_schurStable` and `tr Ḡ > 0` or `det Ḡ < 0`, the switched period map has a
multiplier outside the unit circle for all small `ε > 0` (from
`Averaging.averaging_floquetUnstable`). -/
@[tmio T, powerlib_foundation] theorem twoPiece_averaging_floquetUnstable
    {G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M : ℝ} (h₁ : Continuous G₁) (h₂ : Continuous G₂)
    (hM₁ : ∀ t, ‖G₁ t‖ ≤ M) (hM₂ : ∀ t, ‖G₂ t‖ ≤ M) (hT : 0 < T)
    {Gbar : Matrix (Fin 2) (Fin 2) ℝ}
    (havg : (∫ t in (0 : ℝ)..T / 2, G₁ t) + ∫ t in T / 2..T, G₂ t = T • Gbar)
    (h : 0 < Gbar.trace ∨ Gbar.det < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ρ ∈ spectrum ℂ ((Periodic.transition (fun t => ε • G₂ t) T (T / 2) *
        Periodic.transition (fun t => ε • G₁ t) (T / 2) 0).map (algebraMap ℝ ℂ)), 1 < ‖ρ‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM₁ 0)
  have h' := Averaging.averaging_floquetUnstable (continuous_twoPiece hT h₁ h₂)
    (norm_twoPiece_le hM₁ hM₂) (by positivity) hT
    ((integral_twoPiece hT h₁ h₂).trans havg) h
  filter_upwards [h'] with ε hε
  have hε' : ∀ t, ‖ε • G₁ t‖ ≤ |ε| * M := fun t => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM₁ t) (abs_nonneg ε)
  have hε'' : ∀ t, ‖ε • G₂ t‖ ≤ |ε| * M := fun t => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM₂ t) (abs_nonneg ε)
  unfold Periodic.FloquetUnstable at hε
  rw [Periodic.monodromy, zero_add, twoPiece_smul] at hε
  have e := transition_twoPiece hT (h₁.const_smul ε) (h₂.const_smul ε) hε' hε''
  exact e ▸ hε

end TwoPiece

/-! ## The square wave: the L2 verdict predicts L1 for small modulation -/

section Meissner

open Meissner (meissnerMonodromy)

@[tmio T, powerlib_foundation] theorem frameInv_mul_frame {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    frameInv ω t * frame ω t = 1 := by
  rw [frameInv, frame, Matrix.mul_assoc, ← Matrix.mul_assoc (scaleInv ω), scaleInv_mul_scale hω,
    Matrix.one_mul]
  have := TwoToOne.rot_mul_rot_neg (-(ω * t / 2))
  rwa [neg_neg] at this

@[tmio T, powerlib_foundation] theorem frame_mul_frameInv {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    frame ω t * frameInv ω t = 1 := by
  rw [frameInv, frame, Matrix.mul_assoc, ← Matrix.mul_assoc (rot (ω * t / 2)),
    TwoToOne.rot_mul_rot_neg, Matrix.one_mul, scale_mul_scaleInv hω]

@[tmio T, powerlib_foundation] private theorem continuous_rot_mul (a : ℝ) :
    Continuous fun t => rot (a * t / 2) := by
  unfold rot; fun_prop

@[tmio T, powerlib_foundation] theorem continuous_frameField_const (c ω k : ℝ) :
    Continuous (frameField c ω (fun _ => k)) := by
  have h1 : Continuous fun t => rot (-(ω * t / 2)) := by unfold rot; fun_prop
  exact (h1.mul continuous_const).mul (continuous_rot_mul ω)

@[tmio T, powerlib_foundation] private theorem norm_rot_le (θ : ℝ) :
    ‖rot θ‖ ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + ‖quarter‖ := by
  unfold rot
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one θ)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one θ)

@[tmio T, powerlib_foundation] theorem norm_frameField_const_le (c ω k t : ℝ) :
    ‖frameField c ω (fun _ => k) t‖ ≤
      (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + ‖quarter‖) * ‖residual c k ω‖ *
        (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + ‖quarter‖) := by
  unfold frameField
  refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_rot_le _) (norm_nonneg _))) (norm_rot_le _)
    (norm_nonneg _) (by positivity))

/-- **The half-period exponentials in the rotating frame.** For a frozen stiffness `k` and
`a ≤ t`: `e^{(t − a)B} P(a) = P(t) Φ_G(t, a)`, `B = oscMatrix c k`, `G` the rotating-frame field
of `k` (continuous, so `Φ_G` is the transition matrix of `theorem/Periodic/Transition.lean`). -/
@[tmio T, powerlib_foundation] theorem exp_mul_frame {c ω : ℝ} (hω : ω ≠ 0) (k : ℝ) {a t : ℝ}
    (hat : a ≤ t) :
    NormedSpace.exp ((t - a) • oscMatrix c k) * frame ω a =
      frame ω t * Periodic.transition (frameField c ω (fun _ => k)) t a := by
  set B := oscMatrix c k
  set W : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t =>
    frameInv ω t * (NormedSpace.exp ((t - a) • B) * frame ω a)
  have hE : ∀ r, HasDerivAt (fun t => NormedSpace.exp ((t - a) • B) * frame ω a)
      (B * (NormedSpace.exp ((r - a) • B) * frame ω a)) r := fun r => by
    have h := (hasDerivAt_exp_smul_const' B (r - a)).scomp r ((hasDerivAt_id r).sub_const a)
    simp only [Function.comp_def, id, one_smul] at h
    have h2 := h.mul_const (frame ω a)
    rw [Matrix.mul_assoc] at h2
    exact h2
  have hW : IsIntegralCurveOn W (Periodic.matField (frameField c ω (fun _ => k))) (Ici a) :=
    fun r _ => hasDerivWithinAt_frameInv_mul (k := fun _ => k) hω ((hE r).hasDerivWithinAt)
  have hu := Periodic.transition_unique (continuous_frameField_const c ω k)
    (norm_frameField_const_le c ω k) hW t hat
  have hWa : W a = 1 := by
    simp only [W, sub_self, zero_smul, NormedSpace.exp_zero, Matrix.one_mul,
      frameInv_mul_frame hω]
  rw [hWa, Matrix.mul_one] at hu
  have := congrArg (frame ω t * ·) hu
  simp only [W, ← Matrix.mul_assoc, frame_mul_frameInv hω, Matrix.one_mul] at this
  exact this

/-- **The Meissner monodromy in the rotating frame.** For `ω > 0`, `T = 2π/ω`:
`M D = −D Φ₋(T, T/2) Φ₊(T/2, 0)`, `D = scale ω`, `Φ±` the transition matrices of the
rotating-frame fields of the two stiffness levels `ω₀²(1 ± ε)`. -/
@[tmio T, powerlib_foundation] theorem meissnerMonodromy_mul_scale (c ω₀ ε : ℝ) {ω T : ℝ}
    (hω : 0 < ω) (hT : T = 2 * Real.pi / ω) :
    meissnerMonodromy c ω₀ ε T * scale ω =
      -(scale ω * (Periodic.transition (frameField c ω (fun _ => ω₀ ^ 2 * (1 - ε))) T (T / 2) *
        Periodic.transition (frameField c ω (fun _ => ω₀ ^ 2 * (1 + ε))) (T / 2) 0)) := by
  have hT0 : 0 < T := by rw [hT]; positivity
  have hf0 : frame ω 0 = scale ω := by simp [frame, rot]
  have hfT : frame ω T = -scale ω := by
    have : ω * T / 2 = Real.pi := by rw [hT]; field_simp
    simp [frame, rot, this]
  have e1 := exp_mul_frame (c := c) hω.ne' (ω₀ ^ 2 * (1 + ε)) (a := 0) (t := T / 2)
    (by positivity)
  have e2 := exp_mul_frame (c := c) hω.ne' (ω₀ ^ 2 * (1 - ε)) (a := T / 2) (t := T)
    (by linarith)
  rw [sub_zero] at e1
  rw [show T - T / 2 = T / 2 by ring] at e2
  rw [Meissner.meissnerMonodromy_eq_exp]
  conv_lhs => rw [← hf0, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, e2, hfT]
  rw [Matrix.mul_assoc, Matrix.neg_mul]

@[tmio T, powerlib_foundation] private theorem eig_transfer {M P D Dinv : Matrix (Fin 2) (Fin 2) ℝ}
    (hDD : Dinv * D = 1) (h : M * D = -(D * P)) {μ : ℂ} :
    μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) → -μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
  have hmap : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      (A * B).map (algebraMap ℝ ℂ) = A.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ) :=
    fun A B => Matrix.map_mul
  rw [LTI.mem_spectrum_iff_exists_eigvec, LTI.mem_spectrum_iff_exists_eigvec]
  rintro ⟨v, hv, hPv⟩
  refine ⟨D.map (algebraMap ℝ ℂ) *ᵥ v, fun h0 => hv ?_, ?_⟩
  · have h1 : (Dinv * D).map (algebraMap ℝ ℂ) *ᵥ v = 0 := by
      rw [hmap, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    rwa [hDD, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h1
  · have hMD := congrArg (fun A => A.map (algebraMap ℝ ℂ)) h
    simp only [hmap, Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a)] at hMD
    rw [Matrix.mulVec_mulVec, hMD, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hPv,
      Matrix.mulVec_smul, neg_smul]

/-- `M D = −D P` with `D` invertible: `M` is Schur stable iff `P` is, and an eigenvalue `ρ` of `P`
gives the eigenvalue `−ρ` of `M`. -/
@[tmio T, powerlib_foundation] theorem schurStable_iff_of_mul_eq_neg
    {M P D Dinv : Matrix (Fin 2) (Fin 2) ℝ} (hDD : Dinv * D = 1) (hDD' : D * Dinv = 1)
    (h : M * D = -(D * P)) :
    (LTI.SchurStable M ↔ LTI.SchurStable P) ∧
      ((∃ ρ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)), 1 < ‖ρ‖) →
        ∃ ρ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), 1 < ‖ρ‖) := by
  have h' : P * Dinv = -(Dinv * M) := by
    have := congrArg (fun A => Dinv * A * Dinv) h
    simp only [Matrix.mul_assoc, hDD', Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at this
    rw [← Matrix.mul_assoc Dinv D, hDD, Matrix.one_mul] at this
    rw [this, neg_neg]
  have key : ∀ {A B : Matrix (Fin 2) (Fin 2) ℝ} {E Einv : Matrix (Fin 2) (Fin 2) ℝ},
      Einv * E = 1 → E * Einv = 1 → A * E = -(E * B) → LTI.SchurStable A → LTI.SchurStable B := by
    intro A B E Einv h1 _ hAB hA μ v hv hBv
    have hm : μ ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) :=
      LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, hBv⟩
    obtain ⟨u, hu, hAu⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp (eig_transfer h1 hAB hm)
    have := hA (-μ) u hu hAu
    rwa [norm_neg] at this
  refine ⟨⟨key hDD hDD' h, key hDD' hDD h'⟩, ?_⟩
  rintro ⟨ρ, hρ, hρ1⟩
  exact ⟨-ρ, eig_transfer hDD h hρ, by rwa [norm_neg]⟩

/-- The integral of the rotating-frame field of a frozen stiffness `k` over `[a, b]`, with
`n = (4k − ω²)/(4ω)`: `(b − a)(−c I + n J) + (∫ cos ωt)(c E₁ + n E₂) + (∫ sin ωt)(n E₁ − c E₂)`. -/
@[tmio T, powerlib_foundation] theorem integral_frameField_const (c ω k a b : ℝ) :
    ∫ t in a..b, frameField c ω (fun _ => k) t =
      (b - a) • ((-c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ((4 * k - ω ^ 2) / (2 * ω) / 2) • quarter) +
      (∫ t in a..b, Real.cos (ω * t)) • (c • refl1 + ((4 * k - ω ^ 2) / (2 * ω) / 2) • refl2) +
      (∫ t in a..b, Real.sin (ω * t)) • (((4 * k - ω ^ 2) / (2 * ω) / 2) • refl1 - c • refl2) := by
  set n := (4 * k - ω ^ 2) / (2 * ω) / 2
  have hfun : (fun t => frameField c ω (fun _ => k) t) = fun t =>
      (-c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + n • quarter +
      (c * Real.cos (ω * t) + n * Real.sin (ω * t)) • refl1 +
      (n * Real.cos (ω * t) - c * Real.sin (ω * t)) • refl2 :=
    funext fun t => frameField_eq _ _ _ t
  have ic : IntervalIntegrable (fun t => Real.cos (ω * t)) volume a b :=
    (by fun_prop : Continuous fun t => Real.cos (ω * t)).intervalIntegrable _ _
  have is : IntervalIntegrable (fun t => Real.sin (ω * t)) volume a b :=
    (by fun_prop : Continuous fun t => Real.sin (ω * t)).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun t => c * Real.cos (ω * t) + n * Real.sin (ω * t)) volume a b :=
    (ic.const_mul c).add (is.const_mul n)
  have i2 : IntervalIntegrable (fun t => n * Real.cos (ω * t) - c * Real.sin (ω * t)) volume a b :=
    (ic.const_mul n).sub (is.const_mul c)
  rw [hfun, intervalIntegral.integral_add ?h1 ?h2, intervalIntegral.integral_add ?h3 ?h4,
    intervalIntegral.integral_add ?h5 ?h6, intervalIntegral.integral_const,
    intervalIntegral.integral_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_add (ic.const_mul c)
      (is.const_mul n), intervalIntegral.integral_sub (ic.const_mul n) (is.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  case h5 => exact intervalIntegrable_const
  case h6 => exact intervalIntegrable_const
  case h4 => exact ⟨i1.1.smul_const _, i1.2.smul_const _⟩
  case h2 => exact ⟨i2.1.smul_const _, i2.2.smul_const _⟩
  case h3 => exact intervalIntegrable_const.add intervalIntegrable_const
  case h1 => exact (intervalIntegrable_const.add intervalIntegrable_const).add
               ⟨i1.1.smul_const _, i1.2.smul_const _⟩
  module

@[tmio T, powerlib_foundation] private theorem integral_trig_halves {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) :
    (∫ t in (0 : ℝ)..T / 2, Real.cos (ω * t)) = 0 ∧
    (∫ t in (0 : ℝ)..T / 2, Real.sin (ω * t)) = 2 / ω ∧
    (∫ t in T / 2..T, Real.cos (ω * t)) = 0 ∧
    (∫ t in T / 2..T, Real.sin (ω * t)) = -(2 / ω) := by
  have e1 : ω * (T / 2) = Real.pi := by rw [hT]; field_simp
  have e2 : ω * T = 2 * Real.pi := by rw [hT]; field_simp
  have hc := fun a b => intervalIntegral.integral_comp_mul_left (a := a) (b := b)
    (fun x => Real.cos x) hω.ne'
  have hs := fun a b => intervalIntegral.integral_comp_mul_left (a := a) (b := b)
    (fun x => Real.sin x) hω.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc, integral_cos, mul_zero, e1]; simp
  · rw [hs, integral_sin, mul_zero, e1]; simp; field_simp; norm_num
  · rw [hc, integral_cos, e1, e2]; simp
  · rw [hs, integral_sin, e1, e2]; simp; field_simp; norm_num

/-- **The half-period average of two frozen stiffness levels.** For `T = 2π/ω`:
`∫₀^{T/2} G_{k₁} + ∫_{T/2}^T G_{k₂} = T · slowFlowMatrix c ((ω²/4 − (k₁ + k₂)/2)/ω) g`,
`g = (k₁ − k₂)/(πω)` real. -/
@[tmio T, powerlib_foundation] theorem integral_halves (c k₁ k₂ : ℝ) {ω T : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) :
    (∫ t in (0 : ℝ)..T / 2, frameField c ω (fun _ => k₁) t) +
        ∫ t in T / 2..T, frameField c ω (fun _ => k₂) t =
      T • slowFlowMatrix c ((ω ^ 2 / 4 - (k₁ + k₂) / 2) / ω)
        ⟨(k₁ - k₂) / (Real.pi * ω), 0⟩ := by
  obtain ⟨c1, s1, c2, s2⟩ := integral_trig_halves hω hT
  rw [integral_frameField_const, integral_frameField_const, c1, s1, c2, s2]
  have hT' : T * ω = 2 * Real.pi := by rw [hT]; field_simp
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [slowFlowMatrix, quarter, refl1, refl2] <;> field_simp <;> rw [hT] <;> field_simp <;>
    ring

/-- The L2 matrix of the square wave is the half-period average of the two frozen rotating-frame
fields: `T · averagedMatrix = ∫₀^{T/2} G₊ + ∫_{T/2}^T G₋`, `G±` the fields of `ω₀²(1 ± ε)`. -/
@[tmio T, powerlib_foundation] theorem averagedMatrix_eq_halves (c ω₀ ε : ℝ) {ω T : ℝ}
    (hω : 0 < ω) (hT : T = 2 * Real.pi / ω) :
    T • averagedMatrix c ω₀ ω T (squareWave ε T) =
      (∫ t in (0 : ℝ)..T / 2, frameField c ω (fun _ => ω₀ ^ 2 * (1 + ε)) t) +
        ∫ t in T / 2..T, frameField c ω (fun _ => ω₀ ^ 2 * (1 - ε)) t := by
  rw [integral_halves c _ _ hω hT, averagedMatrix_squareWave c ω₀ ε hω hT]
  congr 2
  · ring
  · congr 1; field_simp; ring

/-- The distinguished scaling of the square-wave oscillator: damping `c = μs`, detuning
`ω²/4 − ω₀² = μωd` and depth `ω₀²ε = μπωe/2`. Its L2 matrix is `μ · slowFlowMatrix s d e`. -/
@[tmio T, powerlib_foundation] theorem averagedMatrix_scaled {ω T s d e μ ω₀ ε : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) (h₁ : ω₀ ^ 2 = ω ^ 2 / 4 - μ * ω * d)
    (h₂ : ω₀ ^ 2 * ε = μ * Real.pi * ω * e / 2) :
    averagedMatrix (μ * s) ω₀ ω T (squareWave ε T) = μ • slowFlowMatrix s d ⟨e, 0⟩ := by
  rw [averagedMatrix_squareWave _ ω₀ ε hω hT]
  have hd : (ω ^ 2 / 4 - ω₀ ^ 2) / ω = μ * d := by rw [h₁]; field_simp; ring
  have he : 2 * ω₀ ^ 2 * ε / (Real.pi * ω) = μ * e := by
    rw [mul_assoc, h₂]; field_simp
  rw [hd, he]
  ext i j; fin_cases i <;> fin_cases j <;> simp [slowFlowMatrix] <;> ring

@[tmio T, powerlib_foundation] private theorem frameField_scaled {ω s d e μ ω₀ ε : ℝ}
    (hω : 0 < ω) (h₁ : ω₀ ^ 2 = ω ^ 2 / 4 - μ * ω * d)
    (h₂ : ω₀ ^ 2 * ε = μ * Real.pi * ω * e / 2) (σ : ℝ) :
    frameField (μ * s) ω (fun _ => ω₀ ^ 2 * (1 + σ * ε)) = fun t =>
      μ • frameField s ω (fun _ => ω ^ 2 / 4 - ω * d + σ * (Real.pi * ω * e / 2)) t := by
  have hres : residual (μ * s) (ω₀ ^ 2 * (1 + σ * ε)) ω =
      μ • residual s (ω ^ 2 / 4 - ω * d + σ * (Real.pi * ω * e / 2)) ω := by
    have e1 : ω₀ ^ 2 * (1 + σ * ε) = ω ^ 2 / 4 - μ * ω * d + σ * (μ * Real.pi * ω * e / 2) := by
      rw [← h₂, ← h₁]; ring
    rw [e1]
    ext i j; fin_cases i <;> fin_cases j <;> simp [residual]
    all_goals (try field_simp)
    all_goals ring
  funext t
  rw [frameField, frameField, hres, Matrix.mul_smul, Matrix.smul_mul]

@[tmio T, powerlib_foundation] private theorem scaled_pieces {ω s d e : ℝ} (hω : 0 < ω) :
    (∫ t in (0 : ℝ)..2 * Real.pi / ω / 2,
        frameField s ω (fun _ => ω ^ 2 / 4 - ω * d + 1 * (Real.pi * ω * e / 2)) t) +
      ∫ t in 2 * Real.pi / ω / 2..2 * Real.pi / ω,
        frameField s ω (fun _ => ω ^ 2 / 4 - ω * d + -1 * (Real.pi * ω * e / 2)) t =
      (2 * Real.pi / ω) • slowFlowMatrix s d ⟨e, 0⟩ := by
  rw [integral_halves s _ _ hω rfl]
  congr 2
  · field_simp; ring
  · congr 1; field_simp; ring

@[tmio T, powerlib_foundation] private theorem scaled_bound (ω s k₁ k₂ : ℝ) :
    ∃ M, (∀ t, ‖frameField s ω (fun _ => k₁) t‖ ≤ M) ∧
      ∀ t, ‖frameField s ω (fun _ => k₂) t‖ ≤ M := by
  set R := ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + ‖quarter‖
  refine ⟨R * max ‖residual s k₁ ω‖ ‖residual s k₂ ω‖ * R, fun t => ?_, fun t => ?_⟩
  · refine (norm_frameField_const_le s ω k₁ t).trans ?_
    gcongr; exact le_max_left _ _
  · refine (norm_frameField_const_le s ω k₂ t).trans ?_
    gcongr; exact le_max_right _ _

/-- **The L2 verdict predicts L1 for the square wave: stability.** Pump frequency `ω > 0`,
period `T = 2π/ω`, the distinguished scaling `c = μs`, `ω²/4 − ω₀² = μωd`, `ω₀²ε = μπωe/2`. If
the averaged model is Hurwitz (`s > 0`, `e² < s² + d²`, `averagedMatrix_scaled`), then for all
small `μ > 0` the exact Meissner monodromy is Schur stable. -/
@[tmio T, powerlib_foundation] theorem meissner_averaging_stable {ω s d e : ℝ} (hω : 0 < ω)
    (hs : 0 < s) (he : e ^ 2 < s ^ 2 + d ^ 2) :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ ω₀ ε : ℝ, ω₀ ^ 2 = ω ^ 2 / 4 - μ * ω * d →
      ω₀ ^ 2 * ε = μ * Real.pi * ω * e / 2 →
      LTI.SchurStable (meissnerMonodromy (μ * s) ω₀ ε (2 * Real.pi / ω)) := by
  obtain ⟨M, hM₁, hM₂⟩ := scaled_bound ω s (ω ^ 2 / 4 - ω * d + 1 * (Real.pi * ω * e / 2))
    (ω ^ 2 / 4 - ω * d + -1 * (Real.pi * ω * e / 2))
  have hnorm : ‖(⟨e, 0⟩ : ℂ)‖ ^ 2 = e ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]; ring
  have hb := twoPiece_averaging_schurStable (continuous_frameField_const _ _ _)
    (continuous_frameField_const _ _ _) hM₁ hM₂ (by positivity : (0 : ℝ) < 2 * Real.pi / ω)
    (scaled_pieces hω) (by rw [trace_slowFlowMatrix]; linarith)
    (by rw [det_slowFlowMatrix, hnorm]; linarith)
  filter_upwards [hb] with μ hμ
  intro ω₀ ε h₁ h₂
  have hM := meissnerMonodromy_mul_scale (μ * s) ω₀ ε hω rfl
  have hp := frameField_scaled (s := s) hω h₁ h₂ 1
  have hm := frameField_scaled (s := s) hω h₁ h₂ (-1)
  rw [one_mul] at hp
  rw [neg_one_mul, ← sub_eq_add_neg] at hm
  rw [hp, hm] at hM
  exact ((schurStable_iff_of_mul_eq_neg (scaleInv_mul_scale hω.ne') (scale_mul_scaleInv hω.ne')
    hM).1).mpr hμ

/-- **The L2 verdict predicts L1 for the square wave: instability.** In the scaling of
`meissner_averaging_stable`, if the averaged model has an exponent with positive real part
(`s < 0`, or `s² + d² < e²`), then for all small `μ > 0` the Meissner system has a Floquet
multiplier outside the unit circle. -/
@[tmio T, powerlib_foundation] theorem meissner_averaging_unstable {ω s d e : ℝ} (hω : 0 < ω)
    (h : s < 0 ∨ s ^ 2 + d ^ 2 < e ^ 2) :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ ω₀ ε : ℝ, ω₀ ^ 2 = ω ^ 2 / 4 - μ * ω * d →
      ω₀ ^ 2 * ε = μ * Real.pi * ω * e / 2 →
      ∃ ρ ∈ spectrum ℂ ((meissnerMonodromy (μ * s) ω₀ ε (2 * Real.pi / ω)).map
        (algebraMap ℝ ℂ)), 1 < ‖ρ‖ := by
  obtain ⟨M, hM₁, hM₂⟩ := scaled_bound ω s (ω ^ 2 / 4 - ω * d + 1 * (Real.pi * ω * e / 2))
    (ω ^ 2 / 4 - ω * d + -1 * (Real.pi * ω * e / 2))
  have hnorm : ‖(⟨e, 0⟩ : ℂ)‖ ^ 2 = e ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]; ring
  have hb := twoPiece_averaging_floquetUnstable (continuous_frameField_const _ _ _)
    (continuous_frameField_const _ _ _) hM₁ hM₂ (by positivity : (0 : ℝ) < 2 * Real.pi / ω)
    (scaled_pieces hω) (by
      rw [trace_slowFlowMatrix, det_slowFlowMatrix, hnorm]
      rcases h with h | h
      · left; linarith
      · right; linarith)
  filter_upwards [hb] with μ hμ
  intro ω₀ ε h₁ h₂
  have hM := meissnerMonodromy_mul_scale (μ * s) ω₀ ε hω rfl
  have hp := frameField_scaled (s := s) hω h₁ h₂ 1
  have hm := frameField_scaled (s := s) hω h₁ h₂ (-1)
  rw [one_mul] at hp
  rw [neg_one_mul, ← sub_eq_add_neg] at hm
  rw [hp, hm] at hM
  exact (schurStable_iff_of_mul_eq_neg (scaleInv_mul_scale hω.ne') (scale_mul_scaleInv hω.ne')
    hM).2 hμ

end Meissner

end powerlib.ParametricResonance.SquareWave
