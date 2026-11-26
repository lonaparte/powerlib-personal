import theorem.ParametricResonance.ForcedOrbitFloquet

/-! # The norm condition on the stable block is not reachable by a choice of basis

The averaging chain (`BlockAveraging` to `SmoothForcedOrbit`) first asked for a contraction of the
stable block in the chosen coordinates, `‖e^{TA_s}‖∞ < 1`. This file shows that such a condition
can fail in every real basis of a block that is nevertheless spectrally contracting; the chain
therefore uses the basis-free condition `ρ(e^{TA_s}) < 1` instead.

Scope.
* Real `2 × 2` blocks, operator `∞`-norm (`Matrix.Norms.Operator`); the damped rotation block
  `A_s = base(σ, β)` of `TwoToOne`; real changes of basis `S` with `det S` a unit.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.2 (the stable remainder of first-order averaging). The counterexample concerns a
hypothesis of the formalization, not a claim of the report.

Results.
* `row_sum_le_norm`, `one_le_norm_of_trace_det` — a real `2 × 2` `N` with `tr N > 1` and
  `det N > 1 − tr N + (tr N)²/2` has `‖N‖∞ ≥ 1`.
* `expS_base`, `expS_conj` — `e^{t base(σ, β)} = e^{−σt} R(βt)` and `e^{t S⁻¹AS} = S⁻¹ e^{tA} S`.
* `no_contracting_basis` — with `βT = π/4` and `e^{−σT}√2 > 1`, `‖e^{T S⁻¹A_sS}‖∞ ≥ 1` for every
  real basis `S` (trace and determinant do not depend on `S`).
* `spectralRadius_expS_base` — for `σT > 0` the same block has every eigenvalue of `e^{TA_s}` of
  modulus `e^{−σT} < 1`.

Corrections.
The hypothesis `‖e^{TA_s}‖∞ < 1` used earlier in the formalization depends on the basis and can
fail in all bases (for example `σT = 0.1`, `βT = π/4`); it is replaced by `ρ(e^{TA_s}) < 1`.

Family and connection conclusions.
None: static evidence on the linear algebra of the stable block.
-/

noncomputable section
namespace powerlib.ParametricResonance.StableBlockNorm
open Matrix
open scoped Matrix.Norms.Operator
open TwoToOne (base)
open NormalForm (rot quarter)
open BlockAveraging (expS)

/-- A row sum is bounded by the `∞`-operator norm. -/
@[tmio T, powerlib_foundation] theorem row_sum_le_norm (N : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    |N i 0| + |N i 1| ≤ ‖N‖ := by
  set v : Fin 2 → ℝ := fun j => if 0 ≤ N i j then 1 else -1 with hv
  have hsign : ∀ a : ℝ, a * (if 0 ≤ a then 1 else -1) = |a| := by
    intro a; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (not_le.1 h)]
  have hvn : ‖v‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    simp only [hv]; split_ifs <;> simp
  have h1 : (N *ᵥ v) i = |N i 0| + |N i 1| := by
    simp only [mulVec, dotProduct, Fin.sum_univ_two, hv, hsign]
  calc |N i 0| + |N i 1| = (N *ᵥ v) i := h1.symm
    _ ≤ ‖N *ᵥ v‖ := (le_abs_self _).trans (by
        have := norm_le_pi_norm (N *ᵥ v) i; rwa [Real.norm_eq_abs] at this)
    _ ≤ ‖N‖ * ‖v‖ := linfty_opNorm_mulVec _ _
    _ ≤ ‖N‖ := by nlinarith [norm_nonneg N, norm_nonneg v]

/-- A real `2 × 2` matrix with `tr N > 1` and `det N > 1 − tr N + (tr N)²/2` has `‖N‖∞ ≥ 1`. -/
@[tmio T, powerlib_foundation] theorem one_le_norm_of_trace_det {N : Matrix (Fin 2) (Fin 2) ℝ}
    (ht : 1 < N.trace) (hd : 1 - N.trace + N.trace ^ 2 / 2 < N.det) : 1 ≤ ‖N‖ := by
  by_contra h
  rw [not_le] at h
  have r0 := row_sum_le_norm N 0
  have r1 := row_sum_le_norm N 1
  rw [trace_fin_two] at ht hd
  rw [det_fin_two] at hd
  have hx1 : |N 0 0| < 1 := by linarith [abs_nonneg (N 0 1)]
  have hy1 : |N 1 1| < 1 := by linarith [abs_nonneg (N 1 0)]
  have hx : 0 < N 0 0 := by linarith [le_abs_self (N 1 1)]
  have hy : 0 < N 1 1 := by linarith [le_abs_self (N 0 0)]
  rw [abs_of_pos hx] at r0
  rw [abs_of_pos hy] at r1
  have hb : |N 0 1| ≤ 1 - N 0 0 := by linarith
  have hc : |N 1 0| ≤ 1 - N 1 1 := by linarith
  have hbc : -(N 0 1 * N 1 0) ≤ (1 - N 0 0) * (1 - N 1 1) := by
    have h1 : -(N 0 1 * N 1 0) ≤ |N 0 1| * |N 1 0| := by
      rw [← abs_mul]; exact neg_le_abs _
    exact h1.trans (mul_le_mul hb hc (abs_nonneg _) (by linarith [le_abs_self (N 0 0)]))
  nlinarith [sq_nonneg (N 0 0 - N 1 1)]

/-- `e^{t base(σ, β)} = e^{−σt} R(βt)`. -/
@[tmio T, powerlib_foundation] theorem expS_base (σ β t : ℝ) :
    expS (base σ β) t = Real.exp (-(σ * t)) • rot (β * t) := by
  refine (ForcedOrbit.eq_expS_of_hasDerivAt (Z := Fin 2) (B := base σ β)
    (Yf := fun t => Real.exp (-(σ * t)) • rot (β * t)) (fun t => ?_) ?_ t).symm
  · have hr := NormalForm.hasDerivAt_rot (2 * β) t
    have e : (fun t => rot (2 * β * t / 2)) = fun t => rot (β * t) := by
      funext t; congr 1; ring
    rw [e] at hr
    have he : HasDerivAt (fun t => Real.exp (-(σ * t))) (Real.exp (-(σ * t)) * -σ) t := by
      have := ((hasDerivAt_id t).const_mul σ).neg.exp
      simpa using this
    refine (he.smul hr).congr_deriv ?_
    have hb : base σ β = -σ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • quarter := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [base, quarter]
    rw [hb, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [show (2 * β / 2) = β by ring, show 2 * β * t / 2 = β * t by ring]
    module
  · simp [rot]

/-- `e^{t S⁻¹ A S} = S⁻¹ e^{tA} S`. -/
@[tmio T, powerlib_foundation] theorem expS_conj (A S : Matrix (Fin 2) (Fin 2) ℝ) (hS : IsUnit S.det)
    (t : ℝ) : expS (S⁻¹ * A * S) t = S⁻¹ * expS A t * S := by
  refine (ForcedOrbit.eq_expS_of_hasDerivAt (Z := Fin 2) (B := S⁻¹ * A * S)
    (Yf := fun t => S⁻¹ * expS A t * S) (fun t => ?_) ?_ t).symm
  · refine (((BlockAveraging.hasDerivAt_expS A t).const_mul S⁻¹).mul_const S).congr_deriv ?_
    calc S⁻¹ * (expS A t * A) * S = S⁻¹ * (expS A t * (S * S⁻¹) * A * S) := by
          rw [Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · simp [ForcedOrbit.expS_zero, Matrix.nonsing_inv_mul _ hS]

/-- The block `A_s = base(σ, β)` with `βT = π/4` and `e^{−σT} √2 > 1`: in **every** real basis
`S` the `∞`-operator norm of `e^{T S⁻¹A_sS}` is at least one. -/
@[tmio T, powerlib_foundation] theorem no_contracting_basis {σ β T : ℝ} (hβ : β * T = Real.pi / 4)
    (hr : 1 < Real.exp (-(σ * T)) * Real.sqrt 2) (S : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : IsUnit S.det) : 1 ≤ ‖expS (S⁻¹ * base σ β * S) T‖ := by
  rw [expS_conj _ _ hS, expS_base, hβ]
  set r := Real.exp (-(σ * T)) with hrd
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have htr : (S⁻¹ * (r • rot (Real.pi / 4)) * S).trace = r * Real.sqrt 2 := by
    rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]
    simp [rot, quarter, trace_fin_two, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hdet : (S⁻¹ * (r • rot (Real.pi / 4)) * S).det = r ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, mul_comm, ← mul_assoc,
      Ring.mul_inverse_cancel _ hS, one_mul]
    simp [rot, quarter, det_fin_two, Real.cos_pi_div_four, Real.sin_pi_div_four]
    nlinarith [h2]
  refine one_le_norm_of_trace_det (by rw [htr]; linarith) ?_
  rw [htr, hdet]
  nlinarith [h2]

/-- The same block is spectrally contracting when `σ T > 0`: every eigenvalue of `e^{TA_s}` has
modulus `e^{−σT} < 1` (`e^{4TA_s} = −e^{−4σT} I`). -/
@[tmio T, powerlib_foundation] theorem spectralRadius_expS_base {σ β T : ℝ} (hβ : β * T = Real.pi / 4)
    (hσ : 0 < σ * T) :
    spectralRadius ℂ ((expS (base σ β) T).map (algebraMap ℝ ℂ)) < 1 := by
  rw [← LTI.schurStable_iff_spectralRadius_lt_one]
  intro μ v hv heq
  have h4 : expS (base σ β) T ^ 4 = (-Real.exp (-(4 * (σ * T)))) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have e : expS (base σ β) T ^ 4 = expS (base σ β) (T + T + T + T) := by
      rw [← ForcedOrbit.expS_add, ← ForcedOrbit.expS_add, ← ForcedOrbit.expS_add]
      simp [pow_succ, Matrix.mul_assoc]
    rw [e, expS_base, show β * (T + T + T + T) = Real.pi by linarith]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rot, quarter] <;> ring_nf
  have hv4 := Linear.mulVec_pow_of_eigen heq 4
  have hmp : ((expS (base σ β) T).map (algebraMap ℝ ℂ)) ^ 4 =
      ((expS (base σ β) T) ^ 4).map (algebraMap ℝ ℂ) := by
    have h := (RingHom.mapMatrix (algebraMap ℝ ℂ) :
      Matrix (Fin 2) (Fin 2) ℝ →+* Matrix (Fin 2) (Fin 2) ℂ).map_pow (expS (base σ β) T) 4
    simpa [RingHom.mapMatrix_apply] using h.symm
  rw [hmp, h4] at hv4
  have hm : ((-Real.exp (-(4 * (σ * T)))) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).map
      (algebraMap ℝ ℂ) *ᵥ v = ((-Real.exp (-(4 * (σ * T))) : ℝ) : ℂ) • v := by
    rw [show ((-Real.exp (-(4 * (σ * T)))) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).map
        (algebraMap ℝ ℂ) = ((-Real.exp (-(4 * (σ * T))) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) by
        ext i j; simp [Matrix.one_apply]; split_ifs <;> simp,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hm] at hv4
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hc := congrFun hv4 i
  simp only [Pi.smul_apply, smul_eq_mul] at hc
  have hμ4 : μ ^ 4 = ((-Real.exp (-(4 * (σ * T))) : ℝ) : ℂ) := mul_right_cancel₀ hi hc.symm
  have hn : ‖μ‖ ^ 4 = Real.exp (-(4 * (σ * T))) := by
    rw [← norm_pow, hμ4, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (Real.exp_pos _)]
  have hlt : ‖μ‖ ^ 4 < 1 := by rw [hn, Real.exp_lt_one_iff]; linarith
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hlt

end powerlib.ParametricResonance.StableBlockNorm
