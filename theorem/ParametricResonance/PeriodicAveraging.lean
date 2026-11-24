import theorem.Periodic.Floquet
import theorem.Criteria.Hurwitz2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # First-order averaging of a periodic linear system in standard form

For `ẏ = ε F(t) y` the transition matrix over one period is `I + ε ∫₀ᵀ F + O(ε²)` with an explicit
remainder; for two states, Floquet stability for all small `ε > 0` is decided by the averaged
matrix `F̄ = (1/T)∫₀ᵀ F`: Hurwitz `F̄` gives Schur-stable monodromy, and `tr F̄ > 0` or `det F̄ < 0`
gives a Floquet multiplier outside the unit circle.

Scope.
* `ẋ = A(t) x` with continuous `A : ℝ → Matrix X X ℝ`, `‖A t‖ ≤ M` (operator `L∞` norm, sup norm
  on vectors), the transition matrix of `theorem/Periodic/Transition.lean`; then the standard form
  `A = ε F` with `∫₀ᵀ F = T • F̄`. No periodicity is needed for the estimates; the monodromy is the
  transition matrix over `[0, T]`.
* The two-state criteria are stated for `ε → 0⁺` (`∀ᶠ ε in 𝓝[>] 0`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.2 ("一阶平均给出" the 2:1
criterion); the first-order averaging step behind it (Nayfeh–Mook, Yakubovich–Starzhinskii,
cited as [8, 9] there).

Results.
* `transition_eq_integral` — `Φ(t, 0) = I + ∫₀ᵗ A(r) Φ(r, 0) dr`.
* `norm_transition_sub_one_le` — `‖Φ(t, 0) − I‖ ≤ M t ‖I‖ e^{Mt}`.
* `norm_transition_sub_integral_le` — `‖Φ(t, 0) − I − ∫₀ᵗ A‖ ≤ (M t)² ‖I‖ e^{Mt}`.
* `entry_le_norm` — every entry is bounded by the operator norm.
* Two-state Jury conditions: `schurStable_of_jury` (`det P < 1`, `det(I − P) > 0`,
  `det(I + P) > 0` ⇒ every eigenvalue inside the unit circle), `exists_eig_gt_of_det` and
  `exists_eig_gt_of_det_one_sub` (`det P > 1` or `det(I − P) < 0` ⇒ an eigenvalue of modulus
  `> 1`).
* `averaging_schurStable`, `averaging_floquetUnstable` — for `X = Fin 2`, continuous `F` with
  `‖F t‖ ≤ M` and `∫₀ᵀ F = T • F̄`: if `tr F̄ < 0 < det F̄` then the monodromy of `εF` is Schur
  stable for all small `ε > 0`; if `0 < tr F̄` or `det F̄ < 0` then `εF` is Floquet unstable for
  all small `ε > 0`.
-/

noncomputable section
namespace powerlib.ParametricResonance.Averaging

open Matrix Set Filter Topology
open scoped Matrix.Norms.Operator Interval

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The first-order expansion of the transition matrix -/

@[tmio T, powerlib_foundation] theorem continuous_transition {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) : Continuous (fun r => Periodic.transition A r 0) :=
  continuous_iff_continuousAt.2 fun r => (Dynamics.stm_hasDerivAt hA r 0).continuousAt

/-- `Φ(t, 0) = I + ∫₀ᵗ A(r) Φ(r, 0) dr`. -/
@[tmio T, powerlib_foundation] theorem transition_eq_integral {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) (t : ℝ) :
    Periodic.transition A t 0 = 1 + ∫ r in (0 : ℝ)..t, A r * Periodic.transition A r 0 := by
  have hcont : Continuous (fun r => A r * Periodic.transition A r 0) :=
    hA.mul (continuous_transition hA)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => Periodic.transition A r 0) (a := 0) (b := t)
    (fun r _ => Dynamics.stm_hasDerivAt hA r 0) (hcont.intervalIntegrable 0 t)
  rw [h]
  simp [Periodic.transition, LinearSystems.stateTransitionMatrix_self]

@[tmio T, powerlib_foundation] theorem norm_transition_le' {A : ℝ → Matrix X X ℝ} {M : ℝ}
    (hM : ∀ t, ‖A t‖ ≤ M) (hM0 : 0 ≤ M) {r : ℝ} (hr : 0 ≤ r) :
    ‖Periodic.transition A r 0‖ ≤ ‖(1 : Matrix X X ℝ)‖ * Real.exp (M * r) := by
  have h := Periodic.norm_transition_le hM hr
  rwa [Real.coe_toNNReal _ hM0, sub_zero] at h

/-- `‖Φ(t, 0) − I‖ ≤ M t ‖I‖ e^{Mt}`. -/
@[tmio T, powerlib_foundation] theorem norm_transition_sub_one_le {A : ℝ → Matrix X X ℝ} {M : ℝ}
    (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hM0 : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖Periodic.transition A t 0 - 1‖ ≤ M * t * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t)) := by
  rw [transition_eq_integral hA t, add_sub_cancel_left]
  have hb : ∀ r ∈ Ι (0 : ℝ) t, ‖A r * Periodic.transition A r 0‖ ≤
      M * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t)) := by
    intro r hr
    rw [Set.uIoc_of_le ht] at hr
    refine (norm_mul_le _ _).trans (mul_le_mul (hM r) ?_ (norm_nonneg _) hM0)
    refine (norm_transition_le' hM hM0 hr.1.le).trans ?_
    gcongr
    exact hr.2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht] at this
  linarith [this]

/-- `‖Φ(t, 0) − I − ∫₀ᵗ A‖ ≤ (M t)² ‖I‖ e^{Mt}`. -/
@[tmio T, powerlib_foundation] theorem norm_transition_sub_integral_le {A : ℝ → Matrix X X ℝ}
    {M : ℝ} (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hM0 : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖Periodic.transition A t 0 - 1 - ∫ r in (0 : ℝ)..t, A r‖ ≤
      M * t * (M * t * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t))) := by
  have hcont : Continuous (fun r => A r * Periodic.transition A r 0) :=
    hA.mul (continuous_transition hA)
  have e : Periodic.transition A t 0 - 1 - ∫ r in (0 : ℝ)..t, A r =
      ∫ r in (0 : ℝ)..t, A r * (Periodic.transition A r 0 - 1) := by
    rw [transition_eq_integral hA t, add_sub_cancel_left, ← intervalIntegral.integral_sub
      (hcont.intervalIntegrable 0 t) (hA.intervalIntegrable 0 t)]
    congr 1; funext r; rw [Matrix.mul_sub, Matrix.mul_one]
  rw [e]
  have hb : ∀ r ∈ Ι (0 : ℝ) t, ‖A r * (Periodic.transition A r 0 - 1)‖ ≤
      M * (M * t * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t))) := by
    intro r hr
    rw [Set.uIoc_of_le ht] at hr
    refine (norm_mul_le _ _).trans (mul_le_mul (hM r) ?_ (norm_nonneg _) hM0)
    refine (norm_transition_sub_one_le hA hM hM0 hr.1.le).trans ?_
    have h1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
    have hrt : r ≤ t := hr.2
    have : Real.exp (M * r) ≤ Real.exp (M * t) := Real.exp_le_exp.2 (by nlinarith)
    have : M * r ≤ M * t := by nlinarith
    gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht] at this
  linarith [this]

/-- An entry is bounded by the operator `L∞` norm. -/
@[tmio T, powerlib_foundation] theorem entry_le_norm (P : Matrix X X ℝ) (i j : X) :
    |P i j| ≤ ‖P‖ := by
  have h := Matrix.linfty_opNorm_mulVec P (Pi.single j 1)
  have hs : ‖(Pi.single j (1 : ℝ) : X → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have hi : ‖(P *ᵥ Pi.single j 1) i‖ ≤ ‖P *ᵥ Pi.single j 1‖ := norm_le_pi_norm _ i
  have heq : (P *ᵥ Pi.single j 1) i = P i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [heq, Real.norm_eq_abs] at hi
  calc |P i j| ≤ ‖P *ᵥ Pi.single j 1‖ := hi
    _ ≤ ‖P‖ * ‖(Pi.single j (1 : ℝ) : X → ℝ)‖ := h
    _ ≤ ‖P‖ * 1 := by gcongr
    _ = ‖P‖ := mul_one _

/-! ## Two-state Jury conditions -/

/-- `det(c I + Q) = c² + c tr Q + det Q` for a `2 × 2` matrix. -/
@[tmio T, powerlib_foundation] theorem det_smul_one_add (c : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Q).det = c ^ 2 + c * Q.trace + Q.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring

/-- An eigenvalue of a real `2 × 2` matrix is a root of `z² − tr z + det`. -/
@[tmio T, powerlib_foundation] theorem eig_root {P : Matrix (Fin 2) (Fin 2) ℝ} {μ : ℂ}
    {v : Fin 2 → ℂ} (hv : v ≠ 0) (h : P.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ ^ 2 - (P.trace : ℂ) * μ + (P.det : ℂ) = 0 := by
  have hz : Linear.characteristicMatrix P μ *ᵥ v = 0 := by
    rw [Linear.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [Linear.complexify, h, sub_self]
  have hdet := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hz⟩
  rw [Criteria.det_characteristicMatrix_fin_two] at hdet
  exact hdet

/-- A root of `z² − a z + b` with `b < 1`, `1 − a + b > 0`, `1 + a + b > 0` lies inside the unit
circle. -/
@[tmio T, powerlib_foundation] theorem norm_lt_one_of_jury {a b : ℝ} {μ : ℂ}
    (h : μ ^ 2 - (a : ℂ) * μ + (b : ℂ) = 0) (hb : b < 1) (h1 : 0 < 1 - a + b)
    (h2 : 0 < 1 + a + b) : ‖μ‖ < 1 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  set x := μ.re
  set y := μ.im
  have hn : ‖μ‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : x ^ 2 + y ^ 2 < 1 := by
    by_cases hy : y = 0
    · rw [hy] at hre ⊢
      have hx1 : x < 1 := by nlinarith
      have hx2 : -1 < x := by nlinarith
      nlinarith
    · have hx : 2 * x = a := by
        have : y * (2 * x - a) = 0 := by linarith
        exact by linarith [(mul_eq_zero.mp this).resolve_left hy]
      nlinarith
  have : ‖μ‖ ^ 2 < 1 := by rw [hn]; exact key
  nlinarith [norm_nonneg μ]

/-- Jury: `det P < 1`, `det(I − P) > 0` and `det(I + P) > 0` make every eigenvalue of a real
`2 × 2` matrix lie inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem schurStable_of_jury {P : Matrix (Fin 2) (Fin 2) ℝ}
    (h0 : P.det < 1) (h1 : 0 < (1 - P).det) (h2 : 0 < (1 + P).det) : LTI.SchurStable P := by
  intro μ v hv h
  have hr := eig_root hv h
  have e1 : (1 - P).det = 1 - P.trace + P.det := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
  have e2 : (1 + P).det = 1 + P.trace + P.det := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
  exact norm_lt_one_of_jury hr h0 (by linarith) (by linarith)

/-- Both roots of `z² − tr z + det` are eigenvalues. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_of_root {P : Matrix (Fin 2) (Fin 2) ℝ} {μ : ℂ}
    (h : μ ^ 2 - (P.trace : ℂ) * μ + (P.det : ℂ) = 0) :
    μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) := by
  rw [LTI.mem_spectrum_iff_exists_eigvec]
  have hdet : (Linear.characteristicMatrix P μ).det = 0 := by
    rw [Criteria.det_characteristicMatrix_fin_two]; exact h
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Linear.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at hz
  exact hz.symm

/-- `det P > 1` gives an eigenvalue of modulus `> 1`. -/
@[tmio T, powerlib_foundation] theorem exists_eig_gt_of_det {P : Matrix (Fin 2) (Fin 2) ℝ}
    (h : 1 < P.det) : ∃ μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)), 1 < ‖μ‖ := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((P.trace : ℂ) ^ 2 - 4 * P.det) two_pos
  set μ : ℂ := ((P.trace : ℂ) + w) / 2
  have h1 : μ ^ 2 - (P.trace : ℂ) * μ + (P.det : ℂ) = 0 := by
    simp only [μ]; linear_combination hw / 4
  set ν := (P.trace : ℂ) - μ
  have h2 : ν ^ 2 - (P.trace : ℂ) * ν + (P.det : ℂ) = 0 := by
    simp only [ν]; linear_combination h1
  have hprod : μ * ν = P.det := by simp only [ν]; linear_combination -h1
  have hn : ‖μ‖ * ‖ν‖ = P.det := by
    rw [← norm_mul, hprod, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  by_cases hm : 1 < ‖μ‖
  · exact ⟨μ, mem_spectrum_of_root h1, hm⟩
  · refine ⟨ν, mem_spectrum_of_root h2, ?_⟩
    push Not at hm
    by_contra hν
    push Not at hν
    have : ‖μ‖ * ‖ν‖ ≤ 1 := by
      calc ‖μ‖ * ‖ν‖ ≤ 1 * 1 := mul_le_mul hm hν (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    linarith

/-- `det(I − P) < 0` gives a real eigenvalue `> 1`. -/
@[tmio T, powerlib_foundation] theorem exists_eig_gt_of_det_one_sub
    {P : Matrix (Fin 2) (Fin 2) ℝ} (h : (1 - P).det < 0) :
    ∃ μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)), 1 < ‖μ‖ := by
  have e1 : (1 - P).det = 1 - P.trace + P.det := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
  set a := P.trace
  set b := P.det
  have hdisc : 0 ≤ a ^ 2 - 4 * b := by nlinarith [sq_nonneg (a - 2)]
  set z := (a + √(a ^ 2 - 4 * b)) / 2
  have hs := Real.sq_sqrt hdisc
  have hroot : (z : ℂ) ^ 2 - (a : ℂ) * z + (b : ℂ) = 0 := by
    have : z ^ 2 - a * z + b = 0 := by simp only [z]; nlinarith
    exact_mod_cast this
  have hz : 1 < z := by
    have hsq : 0 ≤ √(a ^ 2 - 4 * b) := Real.sqrt_nonneg _
    by_cases ha : 2 ≤ a
    · have : 0 < √(a ^ 2 - 4 * b) := by
        apply Real.sqrt_pos.2; nlinarith
      simp only [z]; linarith
    · push Not at ha
      have : (2 - a) ^ 2 < √(a ^ 2 - 4 * b) ^ 2 := by rw [hs]; nlinarith
      have : 2 - a < √(a ^ 2 - 4 * b) := lt_of_pow_lt_pow_left₀ 2 hsq this
      simp only [z]; linarith
  refine ⟨z, mem_spectrum_of_root hroot, ?_⟩
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  exact hz

/-! ## Eventual sign from an asymptotic bound -/

/-- If `|h ε − b εᵏ| ≤ C εᵏ⁺¹` on `(0, 1]` and `b > 0`, then `h ε > 0` for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem eventually_pos_of_bound {h : ℝ → ℝ} {b C : ℝ} (k : ℕ)
    (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ ε, 0 < ε → ε ≤ 1 → |h ε - b * ε ^ k| ≤ C * ε ^ (k + 1)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < h ε := by
  have hδ : 0 < min 1 (b / (C + 1)) := lt_min one_pos (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  obtain ⟨h0, h1⟩ := hε
  have hε1 : ε ≤ 1 := (h1.trans_le (min_le_left _ _)).le
  have hεb : ε < b / (C + 1) := h1.trans_le (min_le_right _ _)
  have hk : 0 < ε ^ k := pow_pos h0 k
  have hb' := hbound ε h0 hε1
  have : C * ε ^ (k + 1) < b * ε ^ k := by
    rw [pow_succ]
    have : C * ε < b := by
      rw [lt_div_iff₀ (by positivity)] at hεb
      nlinarith
    nlinarith
  have := (abs_le.mp hb').1
  linarith

/-! ## Two-state averaging -/

/-- The averaged expansion: `Φ_ε(T) = I + εT F̄ + R_ε` with `‖R_ε‖ ≤ (εMT)² ‖I‖ e^{MT}` for
`0 ≤ ε ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem monodromy_expansion {F : ℝ → Matrix X X ℝ} {M T ε : ℝ}
    (hF : Continuous F) (hM : ∀ t, ‖F t‖ ≤ M) (hM0 : 0 ≤ M) (hT : 0 ≤ T)
    {Fbar : Matrix X X ℝ} (havg : ∫ r in (0 : ℝ)..T, F r = T • Fbar) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖Periodic.monodromy (fun t => ε • F t) T 0 - 1 - (ε * T) • Fbar‖ ≤
      ε ^ 2 * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * T)))) := by
  have hA : Continuous (fun t => ε • F t) := hF.const_smul ε
  have hMε : ∀ t, ‖ε • F t‖ ≤ ε * M := fun t => by
    rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hM t) hε
  have h := norm_transition_sub_integral_le hA hMε (mul_nonneg hε hM0) hT
  rw [intervalIntegral.integral_smul, havg, smul_smul] at h
  rw [Periodic.monodromy, zero_add]
  refine h.trans ?_
  have hexp : Real.exp (ε * M * T) ≤ Real.exp (M * T) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hM0 hT])
  have h1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
  have hMT : 0 ≤ M * T := mul_nonneg hM0 hT
  calc ε * M * T * (ε * M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (ε * M * T)))
      = ε ^ 2 * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (ε * M * T)))) := by ring
    _ ≤ ε ^ 2 * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * T)))) := by gcongr

/-- Bounds of trace and determinant of `Q = εT F̄ + R` with `‖R‖ ≤ K ε²`. -/
@[tmio T, powerlib_foundation] theorem trace_det_bounds {Fbar R : Matrix (Fin 2) (Fin 2) ℝ}
    {T K ε : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hR : ‖R‖ ≤ K * ε ^ 2) :
    |((ε * T) • Fbar + R).trace - (T * Fbar.trace) * ε| ≤ (2 * K) * ε ^ 2 ∧
      |((ε * T) • Fbar + R).det - (T ^ 2 * Fbar.det) * ε ^ 2| ≤
        (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 3 := by
  have hr : ∀ i j, |R i j| ≤ K * ε ^ 2 := fun i j => (entry_le_norm R i j).trans hR
  have hf : ∀ i j, |Fbar i j| ≤ ‖Fbar‖ := fun i j => entry_le_norm Fbar i j
  have hε2 : ε ^ 4 ≤ ε ^ 3 := by
    have := pow_le_pow_of_le_one hε hε1 (show 3 ≤ 4 by norm_num); exact this
  constructor
  · simp only [Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have e : ε * T * Fbar 0 0 + R 0 0 + (ε * T * Fbar 1 1 + R 1 1) -
        T * (Fbar 0 0 + Fbar 1 1) * ε = R 0 0 + R 1 1 := by ring
    rw [e]
    calc |R 0 0 + R 1 1| ≤ |R 0 0| + |R 1 1| := abs_add_le _ _
      _ ≤ K * ε ^ 2 + K * ε ^ 2 := add_le_add (hr 0 0) (hr 1 1)
      _ = 2 * K * ε ^ 2 := by ring
  · simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have e : (ε * T * Fbar 0 0 + R 0 0) * (ε * T * Fbar 1 1 + R 1 1) -
        (ε * T * Fbar 0 1 + R 0 1) * (ε * T * Fbar 1 0 + R 1 0) -
        T ^ 2 * (Fbar 0 0 * Fbar 1 1 - Fbar 0 1 * Fbar 1 0) * ε ^ 2 =
        ε * T * (Fbar 0 0 * R 1 1 + Fbar 1 1 * R 0 0 - Fbar 0 1 * R 1 0 - Fbar 1 0 * R 0 1) +
          (R 0 0 * R 1 1 - R 0 1 * R 1 0) := by ring
    rw [e]
    have hm : ∀ i j k l, |Fbar i j * R k l| ≤ ‖Fbar‖ * (K * ε ^ 2) := fun i j k l => by
      rw [abs_mul]; exact mul_le_mul (hf i j) (hr k l) (abs_nonneg _) (norm_nonneg _)
    have hrr : ∀ i j k l, |R i j * R k l| ≤ (K * ε ^ 2) * (K * ε ^ 2) := fun i j k l => by
      rw [abs_mul]; exact mul_le_mul (hr i j) (hr k l) (abs_nonneg _) (by positivity)
    have hA : |Fbar 0 0 * R 1 1 + Fbar 1 1 * R 0 0 - Fbar 0 1 * R 1 0 - Fbar 1 0 * R 0 1| ≤
        4 * (‖Fbar‖ * (K * ε ^ 2)) := by
      have := hm 0 0 1 1; have := hm 1 1 0 0; have := hm 0 1 1 0; have := hm 1 0 0 1
      calc _ ≤ |Fbar 0 0 * R 1 1| + |Fbar 1 1 * R 0 0| + |Fbar 0 1 * R 1 0| +
            |Fbar 1 0 * R 0 1| := by
            refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
        _ ≤ _ := by linarith
    have hB : |R 0 0 * R 1 1 - R 0 1 * R 1 0| ≤ 2 * ((K * ε ^ 2) * (K * ε ^ 2)) := by
      have := hrr 0 0 1 1; have := hrr 0 1 1 0
      calc _ ≤ |R 0 0 * R 1 1| + |R 0 1 * R 1 0| := abs_sub _ _
        _ ≤ _ := by linarith
    have hεT : |ε * T| = ε * T := abs_of_nonneg (mul_nonneg hε hT)
    calc |ε * T * (Fbar 0 0 * R 1 1 + Fbar 1 1 * R 0 0 - Fbar 0 1 * R 1 0 - Fbar 1 0 * R 0 1) +
          (R 0 0 * R 1 1 - R 0 1 * R 1 0)|
        ≤ ε * T * (4 * (‖Fbar‖ * (K * ε ^ 2))) + 2 * ((K * ε ^ 2) * (K * ε ^ 2)) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ hB)
          rw [abs_mul, hεT]; exact mul_le_mul_of_nonneg_left hA (mul_nonneg hε hT)
      _ = 4 * T * ‖Fbar‖ * K * ε ^ 3 + 2 * K ^ 2 * ε ^ 4 := by ring
      _ ≤ 4 * T * ‖Fbar‖ * K * ε ^ 3 + 2 * K ^ 2 * ε ^ 3 := by gcongr
      _ = _ := by ring

/-- First-order averaging, stability: if `tr F̄ < 0 < det F̄`, the monodromy of `ẏ = εF(t)y` is
Schur stable for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averaging_schurStable {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {M T : ℝ} (hF : Continuous F) (hM : ∀ t, ‖F t‖ ≤ M) (hM0 : 0 ≤ M) (hT : 0 < T)
    {Fbar : Matrix (Fin 2) (Fin 2) ℝ} (havg : ∫ r in (0 : ℝ)..T, F r = T • Fbar)
    (htr : Fbar.trace < 0) (hdet : 0 < Fbar.det) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable (Periodic.monodromy (fun t => ε • F t) T 0) := by
  set K := M * T * (M * T * (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * Real.exp (M * T)))
  have hK : 0 ≤ K := by positivity
  set R : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun ε =>
    Periodic.monodromy (fun t => ε • F t) T 0 - 1 - (ε * T) • Fbar
  have hRb : ∀ ε, 0 < ε → ε ≤ 1 → ‖R ε‖ ≤ K * ε ^ 2 := fun ε h0 h1 => by
    rw [mul_comm]; exact monodromy_expansion hF hM hM0 hT.le havg h0.le h1
  have hP : ∀ ε, Periodic.monodromy (fun t => ε • F t) T 0 = 1 + ((ε * T) • Fbar + R ε) := by
    intro ε; simp only [R]; abel
  have hb := fun ε (h0 : 0 < ε) (h1 : ε ≤ 1) =>
    trace_det_bounds (Fbar := Fbar) hT.le hK h0.le h1 (hRb ε h0 h1)
  -- `1 − det P > 0`
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < -(((ε * T) • Fbar + R ε).trace +
      ((ε * T) • Fbar + R ε).det) := by
    refine eventually_pos_of_bound (b := -(T * Fbar.trace))
      (C := 2 * K + (T ^ 2 * |Fbar.det| + (4 * T * ‖Fbar‖ * K + 2 * K ^ 2))) 1
      (by nlinarith) (by positivity) ?_
    intro ε h0 h1
    obtain ⟨b1, b2⟩ := hb ε h0 h1
    have hd2 : |T ^ 2 * Fbar.det * ε ^ 2| ≤ T ^ 2 * |Fbar.det| * ε ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ T ^ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
    have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
    have h3 : (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 3 ≤
        (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 2 :=
      mul_le_mul_of_nonneg_left hε3 (by positivity)
    have hC : (2 * K + (T ^ 2 * |Fbar.det| + (4 * T * ‖Fbar‖ * K + 2 * K ^ 2))) * ε ^ (1 + 1) =
        2 * K * ε ^ 2 + T ^ 2 * |Fbar.det| * ε ^ 2 + (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 2 := by
      ring
    rw [hC, pow_one]
    rw [abs_le] at b1 b2 hd2 ⊢
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, hd2.1, hd2.2]
  -- `det(I − P) > 0`
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ((ε * T) • Fbar + R ε).det := by
    refine eventually_pos_of_bound (b := T ^ 2 * Fbar.det)
      (C := 4 * T * ‖Fbar‖ * K + 2 * K ^ 2) 2 (by positivity) (by positivity) ?_
    intro ε h0 h1
    exact (hb ε h0 h1).2
  -- `det(I + P) > 0`
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 4 + 2 * ((ε * T) • Fbar + R ε).trace +
      ((ε * T) • Fbar + R ε).det := by
    refine eventually_pos_of_bound (b := 4)
      (C := 2 * (T * |Fbar.trace| + 2 * K) + (T ^ 2 * |Fbar.det| +
        (4 * T * ‖Fbar‖ * K + 2 * K ^ 2))) 0 (by norm_num) (by positivity) ?_
    intro ε h0 h1
    obtain ⟨b1, b2⟩ := hb ε h0 h1
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have hε3 : ε ^ 3 ≤ ε := by nlinarith [pow_le_pow_of_le_one h0.le h1 (show 2 ≤ 3 by norm_num)]
    have ht1 : |T * Fbar.trace * ε| ≤ T * |Fbar.trace| * ε := by
      rw [abs_mul, abs_mul, abs_of_nonneg hT.le, abs_of_nonneg h0.le]
    have hd2 : |T ^ 2 * Fbar.det * ε ^ 2| ≤ T ^ 2 * |Fbar.det| * ε ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ T ^ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
    have m1 : 2 * K * ε ^ 2 ≤ 2 * K * ε := mul_le_mul_of_nonneg_left hε2 (by positivity)
    have m2 : T ^ 2 * |Fbar.det| * ε ^ 2 ≤ T ^ 2 * |Fbar.det| * ε :=
      mul_le_mul_of_nonneg_left hε2 (by positivity)
    have m3 : (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 3 ≤ (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε :=
      mul_le_mul_of_nonneg_left hε3 (by positivity)
    have hC : (2 * (T * |Fbar.trace| + 2 * K) + (T ^ 2 * |Fbar.det| +
        (4 * T * ‖Fbar‖ * K + 2 * K ^ 2))) * ε ^ (0 + 1) =
        2 * (T * |Fbar.trace| * ε) + 2 * (2 * K * ε) + T ^ 2 * |Fbar.det| * ε +
          (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε := by ring
    rw [hC, pow_zero, mul_one]
    rw [abs_le] at b1 b2 ht1 hd2 ⊢
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, ht1.1, ht1.2, hd2.1, hd2.2]
  filter_upwards [e1, e2, e3] with ε h1 h2 h3
  rw [hP]
  refine schurStable_of_jury ?_ ?_ ?_
  · have := det_smul_one_add 1 ((ε * T) • Fbar + R ε)
    rw [one_smul] at this; rw [this]; nlinarith
  · rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 + ((ε * T) • Fbar + R ε)) =
        -((ε * T) • Fbar + R ε) by abel]
    rw [show -((ε * T) • Fbar + R ε) = (-1 : ℝ) • ((ε * T) • Fbar + R ε) by rw [neg_one_smul],
      Matrix.det_smul]
    simpa using h2
  · rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 + ((ε * T) • Fbar + R ε)) =
        (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ((ε * T) • Fbar + R ε) by
        rw [two_smul]; abel, det_smul_one_add]
    nlinarith

/-- First-order averaging, instability: if `tr F̄ > 0` or `det F̄ < 0`, the system `ẏ = εF(t)y` is
Floquet unstable for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averaging_floquetUnstable
    {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M T : ℝ} (hF : Continuous F) (hM : ∀ t, ‖F t‖ ≤ M)
    (hM0 : 0 ≤ M) (hT : 0 < T) {Fbar : Matrix (Fin 2) (Fin 2) ℝ}
    (havg : ∫ r in (0 : ℝ)..T, F r = T • Fbar) (h : 0 < Fbar.trace ∨ Fbar.det < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fun t => ε • F t) T := by
  set K := M * T * (M * T * (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * Real.exp (M * T)))
  have hK : 0 ≤ K := by positivity
  set R : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun ε =>
    Periodic.monodromy (fun t => ε • F t) T 0 - 1 - (ε * T) • Fbar
  have hRb : ∀ ε, 0 < ε → ε ≤ 1 → ‖R ε‖ ≤ K * ε ^ 2 := fun ε h0 h1 => by
    rw [mul_comm]; exact monodromy_expansion hF hM hM0 hT.le havg h0.le h1
  have hP : ∀ ε, Periodic.monodromy (fun t => ε • F t) T 0 = 1 + ((ε * T) • Fbar + R ε) := by
    intro ε; simp only [R]; abel
  have hb := fun ε (h0 : 0 < ε) (h1 : ε ≤ 1) =>
    trace_det_bounds (Fbar := Fbar) hT.le hK h0.le h1 (hRb ε h0 h1)
  rcases h with htr | hdet
  · have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ((ε * T) • Fbar + R ε).trace +
        ((ε * T) • Fbar + R ε).det := by
      refine eventually_pos_of_bound (b := T * Fbar.trace)
        (C := 2 * K + (T ^ 2 * |Fbar.det| + (4 * T * ‖Fbar‖ * K + 2 * K ^ 2))) 1
        (by positivity) (by positivity) ?_
      intro ε h0 h1
      obtain ⟨b1, b2⟩ := hb ε h0 h1
      have hd2 : |T ^ 2 * Fbar.det * ε ^ 2| ≤ T ^ 2 * |Fbar.det| * ε ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ T ^ 2),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
      have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
      have h3 : (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 3 ≤
          (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 2 :=
        mul_le_mul_of_nonneg_left hε3 (by positivity)
      have hC : (2 * K + (T ^ 2 * |Fbar.det| + (4 * T * ‖Fbar‖ * K + 2 * K ^ 2))) * ε ^ (1 + 1) =
          2 * K * ε ^ 2 + T ^ 2 * |Fbar.det| * ε ^ 2 +
            (4 * T * ‖Fbar‖ * K + 2 * K ^ 2) * ε ^ 2 := by ring
      rw [hC, pow_one]
      rw [abs_le] at b1 b2 hd2 ⊢
      constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, hd2.1, hd2.2]
    filter_upwards [e1] with ε h1
    refine exists_eig_gt_of_det ?_
    rw [hP]
    have := det_smul_one_add 1 ((ε * T) • Fbar + R ε)
    rw [one_smul] at this; rw [this]; nlinarith
  · have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < -((ε * T) • Fbar + R ε).det := by
      refine eventually_pos_of_bound (b := -(T ^ 2 * Fbar.det))
        (C := 4 * T * ‖Fbar‖ * K + 2 * K ^ 2) 2 (by nlinarith [sq_pos_of_pos hT]) (by positivity) ?_
      intro ε h0 h1
      have := (hb ε h0 h1).2
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2]
    filter_upwards [e2] with ε h2
    refine exists_eig_gt_of_det_one_sub ?_
    rw [hP, show (1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 + ((ε * T) • Fbar + R ε)) =
        (-1 : ℝ) • ((ε * T) • Fbar + R ε) by rw [neg_one_smul]; abel, Matrix.det_smul]
    simp
    linarith

end powerlib.ParametricResonance.Averaging
