import theorem.Periodic.TwoStateBoundary
import theorem.ParametricResonance.Signature

/-! # The mean trace separates small-signal instability from parametric instability

Liouville's formula fixes the product of the Floquet multipliers of `ẋ = A(t) x` to
`det M = exp(∫₀ᵀ tr A)`, whatever the periodic variation of `A`. This separates the two kinds of
instability exactly:

* any dimension: a positive mean trace `(1/T) ∫₀ᵀ tr A > 0` puts some multiplier outside the unit
  circle for every periodic `A(t)` (the largest Floquet exponent is at least the mean trace divided
  by the dimension): such an instability cannot be removed by any modulation. A negative mean
  trace leaves at least one decaying mode, but does not exclude growing ones;
* two states: a non-real multiplier has `|μ| = exp(½ ∫₀ᵀ tr A)` exactly, so its growth rate is
  half the mean trace and does not depend on the modulation; with a negative mean trace every
  multiplier on or outside the unit circle is real, `μ = r`, its real Floquet mode satisfies
  `x(t + T) = r x(t)` on the whole line, and after removing the envelope `e^{(ln |r|/T) t}` it is
  `T`-periodic (`r > 0`) or `T`-antiperiodic (`r < 0`): its Fourier content is locked to `kΩ` or
  to `(k + ½)Ω`, `Ω = 2π/T`. An instability with negative mean trace is parametric;
* second order, `m δ̈ + D(t) δ̇ + K(t) δ = 0`: `det M = exp(−(1/m) ∫₀ᵀ D)`, so the separating
  parameter is the mean damping, not the frozen damping `D(t)`. Negative mean damping is an
  instability at the averaged small-signal level and at the Floquet level, for every stiffness
  modulation (the levels agree); with positive mean damping the only possible instability is the
  frequency-locked real-multiplier one, which the small-signal analysis of the frozen or averaged
  matrix can miss (`ParametricResonance.Signature.frozen_damping_paradox`).

Scope.
* `ẋ = A(t) x` on `ℝ^X` (finite `X`) with a continuous real `T`-periodic state matrix; transition
  and monodromy matrices of `theorem/Periodic/Transition.lean`, `M = monodromy A T 0`. The Floquet
  multipliers are the complex spectrum of the complexified `M`; products over multipliers are
  taken over the roots of its characteristic polynomial, with algebraic multiplicity.
* Two-state statements: `X = Fin 2`. Fourier coefficients over the windows `[s, s + 2T]`, `s ≥ 0`,
  are `SpecialFunctions.PeriodicWaves.coeff` (index `m` at the frequency `mΩ/2`), as in
  `theorem/ParametricResonance/Signature.lean`.
* Second-order systems: `m δ̈ + D(t) δ̇ + K(t) δ = 0` in the state `(δ, δ̇)`, state matrix
  `oscMatrix (D(t)/(2m)) (K(t)/m)` of `theorem/Periodic/TwoStateBoundary.lean`, continuous
  `T`-periodic `D` and `K`, constant `m > 0`; no sign condition on `D(t)` or `K(t)`. The averaged
  small-signal matrix is `oscMatrix (D̄/(2m)) k̄` with the mean damping `D̄ = (1/T) ∫₀ᵀ D`.
* Generic mathematics; no model family.

Source: Liouville's formula `Periodic.det_monodromy` (`theorem/Periodic/Liouville.lean`) and the
two-state boundary of `theorem/Periodic/TwoStateBoundary.lean`; Floquet theory of periodic linear
systems (Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic Coefficients*;
Nayfeh–Mook, *Nonlinear Oscillations*, parametrically excited systems); the frequency signatures
of `theorem/ParametricResonance/Signature.lean` (`coeff_eq_zero_of_periodic`,
`coeff_eq_zero_of_antiperiodic`), here applied after removing the growth envelope.

Results.
* `mem_spectrum_of_mem_roots`, `card_roots_charpoly` — a complex `n × n` matrix has `n`
  eigenvalues counted with algebraic multiplicity (the roots of its characteristic polynomial).
* `prod_norm_multipliers` — `∏ |μᵢ| = exp(∫₀ᵀ tr A)` for every continuous periodic `A`.
* `exists_multiplier_norm_ge_le` — some multiplier has `|μ| ≥ exp((1/n) ∫₀ᵀ tr A)` and some has
  `|μ| ≤ exp((1/n) ∫₀ᵀ tr A)`.
* `floquetUnstable_of_integral_trace_pos` — `∫₀ᵀ tr A > 0` gives a multiplier outside the unit
  circle; `exists_norm_lt_one_of_integral_trace_neg` — `∫₀ᵀ tr A < 0` gives one inside.
* `norm_multiplier_of_im_ne_zero` — two states: a non-real multiplier has
  `|μ| = exp(½ ∫₀ᵀ tr A)`; `one_le_norm_iff_of_im_ne_zero` — it is on or outside the unit circle
  iff `∫₀ᵀ tr A ≥ 0`, strictly outside iff `> 0`; `im_eq_zero_of_integral_trace_neg` — for
  `∫₀ᵀ tr A < 0` every multiplier with `|μ| ≥ 1` is real.
* `exists_real_eigvec` — a real eigenvalue of the complexification has a real eigenvector.
* `hasDerivAt_transition_mulVec`, `real_mode_add_period` — `Φ(t, 0) w` solves `ẋ = A(t) x` on
  `ℝ`, and `M w = r w` gives `Φ(t + T, 0) w = r Φ(t, 0) w` for every real `t`
  (Mathlib `ODE_solution_unique_univ`).
* `real_mode_envelope`, `real_mode_coeff` — `p(t) = e^{−(ln |r|/T) t} Φ(t, 0) w` satisfies
  `p(t + T) = (r/|r|) p(t)`; over every window `[s, s + 2T]` it has no content at `(k + ½)Ω` for
  `r > 0` and none at `kΩ` for `r < 0`.
* `real_multiplier_of_floquetUnstable` — two states, `∫₀ᵀ tr A < 0`, Floquet unstable: the
  instability is carried by a real multiplier `|r| > 1` with a real eigenvector.
* `det_monodromy_secondOrder` — `det M = exp(−(1/m) ∫₀ᵀ D)`;
  `secondOrder_floquetUnstable_of_mean_damping_neg` — `∫₀ᵀ D < 0`: Floquet unstable for every
  `K`; `secondOrder_parametric_of_mean_damping_pos` — `∫₀ᵀ D > 0`: non-real multipliers have
  `|μ| = exp(−(1/(2m)) ∫₀ᵀ D) < 1` and every instability is a real multiplier `|r| > 1`;
  `secondOrder_levels_agree_of_mean_damping_neg` — `∫₀ᵀ D < 0`: the averaged small-signal matrix
  is not Hurwitz for any stiffness and the periodic system is Floquet unstable.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function Polynomial
open scoped Matrix.Norms.Operator
open powerlib.SpecialFunctions.PeriodicWaves (coeff)
open powerlib.ParametricResonance

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {T : ℝ}

/-! ## Any dimension: the product of the multipliers -/

/-- The complex roots (with multiplicity) of the characteristic polynomial of a complex matrix
are its eigenvalues. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_of_mem_roots {N : Matrix X X ℂ}
    {μ : ℂ} (h : μ ∈ N.charpoly.roots) : μ ∈ spectrum ℂ N :=
  Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (Polynomial.isRoot_of_mem_roots h)

/-- A complex `n × n` matrix has `n` eigenvalues counted with algebraic multiplicity. -/
@[tmio T, powerlib_foundation] theorem card_roots_charpoly (N : Matrix X X ℂ) :
    Multiset.card N.charpoly.roots = Fintype.card X := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]

/-- `|det N| = ∏ |μᵢ|` over the eigenvalues of a complex matrix, with algebraic multiplicity. -/
@[tmio T, powerlib_foundation] private theorem norm_det_eq_prod (N : Matrix X X ℂ) :
    ‖N.det‖ = (N.charpoly.roots.map (fun μ => ‖μ‖)).prod := by
  rw [Matrix.det_eq_prod_roots_charpoly]
  exact map_multiset_prod (normHom (α := ℂ)) _

/-- **Product of the Floquet multipliers.** For every continuous `T`-periodic state matrix the
moduli of the multipliers (with algebraic multiplicity) multiply to `exp(∫₀ᵀ tr A)`. -/
@[tmio T, powerlib_foundation] theorem prod_norm_multipliers (hA : Continuous A)
    (hP : Periodic A T) :
    (((monodromy A T 0).map (algebraMap ℝ ℂ)).charpoly.roots.map (fun μ => ‖μ‖)).prod =
      Real.exp (∫ r in (0 : ℝ)..T, (A r).trace) := by
  rw [← norm_det_eq_prod, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_monodromy hA hP 0]
  simp

/-- Extreme multipliers: some multiplier has modulus at least, and some at most,
`exp((1/n) ∫₀ᵀ tr A)`, the geometric mean of the moduli (`n` states). -/
@[tmio T, powerlib_foundation] theorem exists_multiplier_norm_ge_le [Nonempty X]
    (hA : Continuous A) (hP : Periodic A T) :
    (∃ μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)),
        Real.exp ((∫ r in (0 : ℝ)..T, (A r).trace) / Fintype.card X) ≤ ‖μ‖) ∧
      ∃ μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)),
        ‖μ‖ ≤ Real.exp ((∫ r in (0 : ℝ)..T, (A r).trace) / Fintype.card X) := by
  set N := (monodromy A T 0).map (algebraMap ℝ ℂ) with hN
  set I := ∫ r in (0 : ℝ)..T, (A r).trace with hI
  have hn : 0 < Fintype.card X := Fintype.card_pos
  have hprod := prod_norm_multipliers hA hP
  rw [← hN, ← hI] at hprod
  have hcard := card_roots_charpoly N
  have hne : N.charpoly.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  have hexp : Real.exp (I / Fintype.card X) ^ Fintype.card X = Real.exp I := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hn0 : Fintype.card X ≠ 0 := hn.ne'
  constructor
  · obtain ⟨μ, hμ, hmax⟩ := Multiset.exists_max_image (fun μ : ℂ => ‖μ‖) hne
    refine ⟨μ, mem_spectrum_of_mem_roots hμ, ?_⟩
    have hle := Multiset.prod_map_le_prod_map₀ (s := N.charpoly.roots) (fun μ : ℂ => ‖μ‖)
      (fun _ => ‖μ‖) (fun i _ => norm_nonneg i) hmax
    rw [Multiset.map_const', Multiset.prod_replicate, hcard, hprod, ← hexp] at hle
    exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) hn0).mp hle
  · obtain ⟨μ, hμ, hmin⟩ := Multiset.exists_min_image (fun μ : ℂ => ‖μ‖) hne
    refine ⟨μ, mem_spectrum_of_mem_roots hμ, ?_⟩
    have hle := Multiset.prod_map_le_prod_map₀ (s := N.charpoly.roots) (fun _ => ‖μ‖)
      (fun μ : ℂ => ‖μ‖) (fun _ _ => norm_nonneg μ) hmin
    rw [Multiset.map_const', Multiset.prod_replicate, hcard, hprod, ← hexp] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le hn0).mp hle

/-- **Positive mean trace: unstable under every modulation.** If `∫₀ᵀ tr A > 0`, some Floquet
multiplier lies outside the unit circle, whatever the periodic variation of `A`: the largest
Floquet exponent is at least `(1/(nT)) ∫₀ᵀ tr A > 0`. -/
@[tmio T, powerlib_foundation] theorem floquetUnstable_of_integral_trace_pos (hA : Continuous A)
    (hP : Periodic A T) (h : 0 < ∫ r in (0 : ℝ)..T, (A r).trace) : FloquetUnstable A T := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [Matrix.trace] at h
  · obtain ⟨μ, hμ, hle⟩ := (exists_multiplier_norm_ge_le hA hP).1
    exact ⟨μ, hμ, lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (div_pos h (by positivity))) hle⟩

/-- **Negative mean trace: some mode always decays.** If `∫₀ᵀ tr A < 0`, some Floquet multiplier
lies strictly inside the unit circle; a modulation can amplify some modes but never all. -/
@[tmio T, powerlib_foundation] theorem exists_norm_lt_one_of_integral_trace_neg [Nonempty X]
    (hA : Continuous A) (hP : Periodic A T) (h : ∫ r in (0 : ℝ)..T, (A r).trace < 0) :
    ∃ μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)), ‖μ‖ < 1 := by
  obtain ⟨μ, hμ, hle⟩ := (exists_multiplier_norm_ge_le hA hP).2
  exact ⟨μ, hμ, lt_of_le_of_lt hle (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos h
    (Nat.cast_pos.mpr Fintype.card_pos)))⟩

/-! ## Two states: non-real multipliers grow at half the mean trace -/

section TwoStates

variable {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ}

/-- **A non-real multiplier is fixed by the mean trace.** For two states a multiplier with
`Im μ ≠ 0` has `|μ| = exp(½ ∫₀ᵀ tr A)` exactly: its Floquet exponent `(1/T) ln |μ|` is half the
mean trace, whatever the modulation. -/
@[tmio T, powerlib_foundation] theorem norm_multiplier_of_im_ne_zero (hA : Continuous A)
    (hP : Periodic A T) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ))) (him : μ.im ≠ 0) :
    ‖μ‖ = Real.exp ((∫ r in (0 : ℝ)..T, (A r).trace) / 2) := by
  have h := (sq_norm_eq_det_of_im_ne_zero hμ him).trans (det_monodromy hA hP 0)
  have e : Real.exp (∫ r in (0 : ℝ)..T, (A r).trace) =
      Real.exp ((∫ r in (0 : ℝ)..T, (A r).trace) / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e] at h
  exact (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp h

/-- A non-real multiplier is on or outside the unit circle iff `∫₀ᵀ tr A ≥ 0`, strictly outside
iff `∫₀ᵀ tr A > 0`. -/
@[tmio T, powerlib_foundation] theorem one_le_norm_iff_of_im_ne_zero (hA : Continuous A)
    (hP : Periodic A T) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ))) (him : μ.im ≠ 0) :
    (1 ≤ ‖μ‖ ↔ 0 ≤ ∫ r in (0 : ℝ)..T, (A r).trace) ∧
      (1 < ‖μ‖ ↔ 0 < ∫ r in (0 : ℝ)..T, (A r).trace) := by
  rw [norm_multiplier_of_im_ne_zero hA hP hμ him, Real.one_le_exp_iff, Real.one_lt_exp_iff]
  constructor <;> constructor <;> intro h <;> linarith

/-- **Negative mean trace: only real multipliers reach the unit circle.** For two states with
`∫₀ᵀ tr A < 0`, every multiplier with `|μ| ≥ 1` is real (`det M = exp(∫₀ᵀ tr A) < 1`,
`TwoStateBoundary.im_eq_zero_of_one_le_norm`). -/
@[tmio T, powerlib_foundation] theorem im_eq_zero_of_integral_trace_neg (hA : Continuous A)
    (hP : Periodic A T) (h : ∫ r in (0 : ℝ)..T, (A r).trace < 0) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ))) (h1 : 1 ≤ ‖μ‖) :
    μ.im = 0 :=
  im_eq_zero_of_one_le_norm (by rw [det_monodromy hA hP 0]; exact Real.exp_lt_one_iff.mpr h) hμ h1

end TwoStates

/-! ## Real multipliers: frequency locking to the pump -/

/-- A real eigenvalue of the complexification has a real eigenvector. -/
@[tmio T, powerlib_foundation] theorem exists_real_eigvec {P : Matrix X X ℝ} {r : ℝ}
    (h : (r : ℂ) ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) :
    ∃ w : X → ℝ, w ≠ 0 ∧ P *ᵥ w = r • w := by
  obtain ⟨v, hv, hPv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp h
  have hre : P *ᵥ (fun k => (v k).re) = r • (fun k => (v k).re) := by
    funext i
    have h1 := congrArg Complex.re (congrFun hPv i)
    simp [Matrix.mulVec, dotProduct, Complex.re_sum] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  have him : P *ᵥ (fun k => (v k).im) = r • (fun k => (v k).im) := by
    funext i
    have h1 := congrArg Complex.im (congrFun hPv i)
    simp [Matrix.mulVec, dotProduct, Complex.im_sum] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  by_cases h0 : (fun k => (v k).re) = 0
  · refine ⟨fun k => (v k).im, fun h1 => hv ?_, him⟩
    funext k
    exact Complex.ext (congrFun h0 k) (congrFun h1 k)
  · exact ⟨_, h0, hre⟩

/-- `t ↦ Φ(t, 0) w` solves `ẋ = A(t) x` on the whole line. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transition_mulVec (hA : Continuous A)
    (w : X → ℝ) (t : ℝ) :
    HasDerivAt (fun t => transition A t 0 *ᵥ w) (A t *ᵥ (transition A t 0 *ᵥ w)) t := by
  let L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun N => N *ᵥ w
        map_add' := fun N N' => Matrix.add_mulVec N N' w
        map_smul' := fun c N => Matrix.smul_mulVec c N w }
  refine (L.hasFDerivAt.comp_hasDerivAt t (Dynamics.stm_hasDerivAt hA t 0)).congr_deriv ?_
  show (A t * transition A t 0) *ᵥ w = A t *ᵥ (transition A t 0 *ᵥ w)
  rw [Matrix.mulVec_mulVec]

/-- A real Floquet mode on the whole line: for `M w = r w`, `Φ(t + T, 0) w = r Φ(t, 0) w` for
every real `t` (both sides solve `ẋ = A(t) x` and agree at `t = 0`; Mathlib
`ODE_solution_unique_univ`). -/
@[tmio T, powerlib_foundation] theorem real_mode_add_period (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) {r : ℝ} {w : X → ℝ} (hw : monodromy A T 0 *ᵥ w = r • w)
    (t : ℝ) : transition A (t + T) 0 *ᵥ w = r • (transition A t 0 *ᵥ w) := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  have hsol : ∀ t, HasDerivAt (fun t => transition A t 0 *ᵥ w)
      (vecField A t (transition A t 0 *ᵥ w)) t := hasDerivAt_transition_mulVec hA w
  have hf : ∀ t, HasDerivAt (fun t => transition A (t + T) 0 *ᵥ w)
      (vecField A t (transition A (t + T) 0 *ᵥ w)) t ∧
        transition A (t + T) 0 *ᵥ w ∈ (univ : Set (X → ℝ)) := fun t => by
    refine ⟨?_, trivial⟩
    have h := (hsol (t + T)).comp_add_const t T
    simpa only [vecField, hP t] using h
  have hg : ∀ t, HasDerivAt (fun t => r • (transition A t 0 *ᵥ w))
      (vecField A t (r • (transition A t 0 *ᵥ w))) t ∧
        r • (transition A t 0 *ᵥ w) ∈ (univ : Set (X → ℝ)) := fun t => by
    refine ⟨?_, trivial⟩
    have h := (hsol t).const_smul r
    rw [vecField, Matrix.mulVec_smul]
    exact h
  have h0 : transition A (0 + T) 0 *ᵥ w = r • (transition A 0 0 *ᵥ w) := by
    have e : transition A (0 + T) 0 = monodromy A T 0 := rfl
    rw [e, hw]
    simp [LinearSystems.stateTransitionMatrix_self]
  have := ODE_solution_unique_univ (v := vecField A) (s := fun _ => univ)
    (fun t => (vecField_lipschitz hM t).lipschitzOnWith) hf hg h0
  exact congrFun this t

/-- **The envelope of a real Floquet mode.** For a real multiplier `r ≠ 0` with real eigenvector
`M w = r w`, the mode `x(t) = Φ(t, 0) w` with its growth envelope removed,
`p(t) = e^{−λt} x(t)`, `λ = ln |r| / T`, satisfies `p(t + T) = (r/|r|) p(t)` for `t ≥ 0`:
`T`-periodic for `r > 0`, `T`-antiperiodic for `r < 0`. -/
@[tmio T, powerlib_foundation] theorem real_mode_envelope (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) {r : ℝ} (hr : r ≠ 0) {w : X → ℝ} (hw : monodromy A T 0 *ᵥ w = r • w) {t : ℝ}
    (ht : 0 ≤ t) (i : X) :
    Real.exp (-(Real.log |r| / T * (t + T))) * (transition A (t + T) 0 *ᵥ w) i =
      r / |r| * (Real.exp (-(Real.log |r| / T * t)) * (transition A t 0 *ᵥ w) i) := by
  rw [transition_mulVec_add_period hA hP hT hw ht, Pi.smul_apply, smul_eq_mul]
  have habs : 0 < |r| := abs_pos.mpr hr
  have e : Real.exp (-(Real.log |r| / T * (t + T))) =
      Real.exp (-(Real.log |r| / T * t)) / |r| := by
    rw [show -(Real.log |r| / T * (t + T)) = -(Real.log |r| / T * t) + -Real.log |r| by
      field_simp; ring, Real.exp_add, Real.exp_neg (Real.log |r|), Real.exp_log habs]
    ring
  rw [e]
  field_simp

/-- **Frequency locking of a real mode.** For a real multiplier `r ≠ 0` (eigenvector `w`) the
envelope-removed mode `p(t) = e^{−λt} (Φ(t, 0) w)_i`, `λ = ln |r| / T`, has over every window
`[s, s + 2T]`, `s ≥ 0`, no content at the half-integer frequencies `(k + ½)Ω` when `r > 0` (odd
indices) and none at the integer multiples `kΩ` when `r < 0` (even indices): its frequencies are
locked to the pump, `kΩ` or `(k + ½)Ω`. -/
@[tmio T, powerlib_foundation] theorem real_mode_coeff (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) {r : ℝ} (hr : r ≠ 0) {w : X → ℝ} (hw : monodromy A T 0 *ᵥ w = r • w) {s : ℝ}
    (hs : 0 ≤ s) (i : X) {m : ℤ} :
    (0 < r → Odd m → coeff (mul_pos two_pos hT) (fun t =>
        Real.exp (-(Real.log |r| / T * (s + t))) * (transition A (s + t) 0 *ᵥ w) i) m = 0) ∧
      (r < 0 → Even m → coeff (mul_pos two_pos hT) (fun t =>
        Real.exp (-(Real.log |r| / T * (s + t))) * (transition A (s + t) 0 *ᵥ w) i) m = 0) := by
  have hΦ : Continuous fun t => transition A t 0 :=
    continuous_iff_continuousAt.2 fun t => (Dynamics.stm_hasDerivAt hA t 0).continuousAt
  have hc : Continuous fun t =>
      Real.exp (-(Real.log |r| / T * (s + t))) * (transition A (s + t) 0 *ᵥ w) i :=
    (by fun_prop : Continuous fun t => Real.exp (-(Real.log |r| / T * (s + t)))).mul
      ((continuous_apply i).comp
        ((hΦ.comp (continuous_const.add continuous_id)).matrix_mulVec continuous_const))
  have hstep : ∀ t, 0 ≤ t →
      Real.exp (-(Real.log |r| / T * (s + (t + T)))) * (transition A (s + (t + T)) 0 *ᵥ w) i =
        r / |r| * (Real.exp (-(Real.log |r| / T * (s + t))) * (transition A (s + t) 0 *ᵥ w) i) :=
    fun t ht => by
      rw [show s + (t + T) = (s + t) + T by ring]
      exact real_mode_envelope hA hP hT hr hw (by linarith) i
  constructor
  · intro hpos hm
    refine Signature.coeff_eq_zero_of_periodic hT hc.continuousOn (fun t ht => ?_) hm
    rw [hstep t ht, abs_of_pos hpos, div_self hpos.ne', one_mul]
  · intro hneg hm
    refine Signature.coeff_eq_zero_of_antiperiodic hT hc.continuousOn (fun t ht => ?_) hm
    rw [hstep t ht, abs_of_neg hneg, div_neg, div_self hneg.ne, neg_one_mul]

/-- **The two-state separation by the mean trace.** For two states with `∫₀ᵀ tr A < 0` every
Floquet instability is carried by a real multiplier `r`, `|r| > 1`, with a real eigenvector:
its mode, after removing the growth envelope `e^{(ln |r|/T) t}`, is `T`-periodic or
`T`-antiperiodic (`real_mode_envelope`, `real_mode_coeff`), i.e. locked to `kΩ` or `(k + ½)Ω` —
a parametric instability. -/
@[tmio T, powerlib_foundation] theorem real_multiplier_of_floquetUnstable
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hA : Continuous A) (hP : Periodic A T)
    (h : ∫ r in (0 : ℝ)..T, (A r).trace < 0) (hU : FloquetUnstable A T) :
    ∃ r : ℝ, 1 < |r| ∧ ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ monodromy A T 0 *ᵥ w = r • w := by
  obtain ⟨μ, hμ, h1⟩ := hU
  have him := im_eq_zero_of_integral_trace_neg hA hP h hμ h1.le
  have hμr : μ = (μ.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hμr] at hμ h1
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  exact ⟨μ.re, h1, exists_real_eigvec hμ⟩

/-! ## Second-order systems with time-varying damping and stiffness -/

section SecondOrder

variable {m T : ℝ} {D K : ℝ → ℝ}

@[tmio T, powerlib_foundation] private theorem secondOrder_continuous (hD : Continuous D)
    (hK : Continuous K) : Continuous fun t => oscMatrix (D t / (2 * m)) (K t / m) := by
  unfold oscMatrix
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

@[tmio T, powerlib_foundation] private theorem secondOrder_integral_trace (hm : m ≠ 0) :
    ∫ r in (0 : ℝ)..T, (oscMatrix (D r / (2 * m)) (K r / m)).trace =
      -(∫ r in (0 : ℝ)..T, D r) / m := by
  simp only [trace_oscMatrix]
  rw [show (fun r => -(2 * (D r / (2 * m)))) = fun r => -(D r / m) by
    funext r; field_simp, intervalIntegral.integral_neg, intervalIntegral.integral_div]
  ring

/-- `m δ̈ + D(t) δ̇ + K(t) δ = 0` in the state `(δ, δ̇)`: `ẋ = oscMatrix (D/(2m)) (K/m) x`. The
product of the multipliers is `det M = exp(−(1/m) ∫₀ᵀ D)`: only the mean damping enters. -/
@[tmio T, powerlib_foundation] theorem det_monodromy_secondOrder (hD : Continuous D)
    (hK : Continuous K) (hDP : Periodic D T) (hKP : Periodic K T) (hm : m ≠ 0) :
    (monodromy (fun t => oscMatrix (D t / (2 * m)) (K t / m)) T 0).det =
      Real.exp (-(∫ r in (0 : ℝ)..T, D r) / m) := by
  rw [det_monodromy (secondOrder_continuous hD hK) (fun t => by simp only [hDP t, hKP t]) 0,
    secondOrder_integral_trace hm]

/-- **Negative mean damping: unstable for every stiffness modulation.** For
`m δ̈ + D(t) δ̇ + K(t) δ = 0` with `m > 0` and `∫₀ᵀ D < 0` some multiplier lies outside the unit
circle, for every continuous `T`-periodic `K` (and every sign pattern of `D(t)`): an oscillatory
small-signal instability cannot be removed by any modulation. -/
@[tmio T, powerlib_foundation] theorem secondOrder_floquetUnstable_of_mean_damping_neg
    (hD : Continuous D) (hK : Continuous K) (hDP : Periodic D T) (hKP : Periodic K T)
    (hm : 0 < m) (h : ∫ r in (0 : ℝ)..T, D r < 0) :
    FloquetUnstable (fun t => oscMatrix (D t / (2 * m)) (K t / m)) T := by
  refine floquetUnstable_of_integral_trace_pos (secondOrder_continuous hD hK)
    (fun t => by simp only [hDP t, hKP t]) ?_
  rw [secondOrder_integral_trace hm.ne']
  exact div_pos (neg_pos.mpr h) hm

/-- **Positive mean damping: every instability is parametric.** For
`m δ̈ + D(t) δ̇ + K(t) δ = 0` with `m > 0` and `∫₀ᵀ D > 0`: every non-real multiplier has
`|μ| = exp(−(1/(2m)) ∫₀ᵀ D) < 1`, and a Floquet instability is carried by a real multiplier
`|r| > 1` with a real eigenvector, whose envelope-removed mode is locked to `kΩ` or `(k + ½)Ω`
(`real_mode_coeff`). The separating parameter is the mean damping `(1/T) ∫₀ᵀ D`, not the frozen
damping `D(t)`. -/
@[tmio T, powerlib_foundation] theorem secondOrder_parametric_of_mean_damping_pos
    (hD : Continuous D) (hK : Continuous K) (hDP : Periodic D T) (hKP : Periodic K T)
    (hm : 0 < m) (h : 0 < ∫ r in (0 : ℝ)..T, D r) :
    (∀ μ ∈ spectrum ℂ ((monodromy (fun t => oscMatrix (D t / (2 * m)) (K t / m)) T 0).map
        (algebraMap ℝ ℂ)), μ.im ≠ 0 →
        ‖μ‖ = Real.exp (-(∫ r in (0 : ℝ)..T, D r) / (2 * m)) ∧ ‖μ‖ < 1) ∧
      (FloquetUnstable (fun t => oscMatrix (D t / (2 * m)) (K t / m)) T →
        ∃ r : ℝ, 1 < |r| ∧ ∃ w : Fin 2 → ℝ, w ≠ 0 ∧
          monodromy (fun t => oscMatrix (D t / (2 * m)) (K t / m)) T 0 *ᵥ w = r • w) := by
  have hA := secondOrder_continuous (m := m) hD hK
  have hP : Periodic (fun t => oscMatrix (D t / (2 * m)) (K t / m)) T := fun t => by
    simp only [hDP t, hKP t]
  have htr := secondOrder_integral_trace (D := D) (K := K) (T := T) hm.ne'
  have hneg : ∫ r in (0 : ℝ)..T, (oscMatrix (D r / (2 * m)) (K r / m)).trace < 0 := by
    rw [htr]; exact div_neg_of_neg_of_pos (neg_neg_of_pos h) hm
  refine ⟨fun μ hμ him => ?_, real_multiplier_of_floquetUnstable hA hP hneg⟩
  have hn := norm_multiplier_of_im_ne_zero hA hP hμ him
  rw [htr] at hn
  refine ⟨by rw [hn]; congr 1; field_simp, ?_⟩
  rw [hn, Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos h) hm) two_pos

/-- **Agreement of the levels for negative mean damping.** With `m > 0`, `T > 0` and
`∫₀ᵀ D < 0`, the averaged small-signal matrix `oscMatrix (D̄/(2m)) k̄`, `D̄ = (1/T) ∫₀ᵀ D`, is not
Hurwitz for any stiffness `k̄` (its trace `−D̄/m` is positive), and the periodic system is Floquet
unstable for every stiffness modulation: small-signal and Floquet analysis agree. -/
@[tmio T, powerlib_foundation] theorem secondOrder_levels_agree_of_mean_damping_neg
    (hD : Continuous D) (hK : Continuous K) (hDP : Periodic D T) (hKP : Periodic K T)
    (hm : 0 < m) (hT : 0 < T) (h : ∫ r in (0 : ℝ)..T, D r < 0) :
    (∀ kbar : ℝ,
        ¬ LinearSystems.IsHurwitz (oscMatrix ((∫ r in (0 : ℝ)..T, D r) / T / (2 * m)) kbar)) ∧
      FloquetUnstable (fun t => oscMatrix (D t / (2 * m)) (K t / m)) T := by
  refine ⟨fun kbar hH => ?_,
    secondOrder_floquetUnstable_of_mean_damping_neg hD hK hDP hKP hm h⟩
  rw [Criteria.isHurwitz_fin_two_iff, trace_oscMatrix] at hH
  have : (∫ r in (0 : ℝ)..T, D r) / T / (2 * m) < 0 :=
    div_neg_of_neg_of_pos (div_neg_of_neg_of_pos h hT) (by positivity)
  linarith [hH.1]

end SecondOrder

end powerlib.Periodic
