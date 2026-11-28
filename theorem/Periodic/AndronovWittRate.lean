import theorem.Periodic.AndronovWitt

/-! # The Andronov–Witt theorem at the optimal rate, with a Lipschitz asymptotic phase

`theorem/Periodic/AndronovWitt.lean` proves, for a nonconstant `T`-periodic orbit `x_*` of
`ẋ = f(x)` whose nontrivial multipliers lie strictly inside the unit circle, orbital exponential
stability with asymptotic phase at some rate `λ = −log q/(3T/2)` and with a phase bounded by
`C ‖x(0) − x_*(σ)‖`. This module sharpens both statements and shows that the sharpened rate is
the best possible. Let `ρ` be the spectral radius of the Poincaré Jacobian
`DΠ(p) = sectionMatrix M f(p)`, `p = x_*(0)` (the largest modulus of a nontrivial multiplier,
`PoincareSection.mem_spectrum_deflate_iff`).

* **Every rate below `−log ρ/T`.** If every eigenvalue of `DΠ(p)` has modulus `< q = e^{−λT}`,
  `q⁻¹ DΠ(p)` is Schur stable and some power satisfies `‖DΠ(p)ᵐ‖ < qᵐ`
  (`exists_pow_norm_lt_pow`). The adapted norm `ν(x) = Σ_{j<m} q^{−j} ‖DΠ(p)ʲ x‖` satisfies
  `ν(DΠ(p) x) ≤ q ν(x) − c ‖x‖`, `c > 0`, and with the strict derivative `Π` is a
  `q`-contraction for `ν` on a `ν`-ball about `p`: `‖Πᵏ ξ − Πᵏ ξ'‖ ≤ N qᵏ ‖ξ − ξ'‖`
  (`exists_contraction_of_spectrum`). The return times then satisfy
  `|τ(Πᵏ ξ) − T| ≤ L N qᵏ ‖ξ − p‖`, the crossing times are `t_k = kT − Θ(ξ) + O(qᵏ)`, and on
  `[t_k, t_{k+1}]` the time is `t ≤ (k + 1) T + O(‖ξ − p‖)`, so `qᵏ ≤ E e^{−λt}` at the rate `λ`
  itself (the earlier proof only used `t_{k+1} ≤ (k + 1)(3T/2)`).
* **A Lipschitz asymptotic phase.** `Θ(ξ) = −Σ_j (τ(Πʲ ξ) − T)`, the limit of `kT − t_k(ξ)`,
  and `|Θ(ξ) − Θ(ξ')| ≤ Σ_j |τ(Πʲ ξ) − τ(Πʲ ξ')| ≤ L N ‖ξ − ξ'‖/(1 − q)`: the return time is
  Lipschitz near `p` and `Π` contracts differences geometrically. From a point `x_*(σ)` the phase
  is `Θ` composed with the flow over the time `T − (σ mod T)`, which is `e^{KT}`-Lipschitz.
* **Optimality.** If the orbit attracts the solutions starting near `p` at a rate `λ`,
  `dist(x(t), x_*(ℝ)) ≤ C e^{−λt} ‖x(0) − p‖`, every eigenvalue of `DΠ(p)` has modulus
  `≤ e^{−λT}` (`spectrum_sectionMatrix_le_of_decay`). The flow over `kT` has the derivative `Mᵏ`
  at `p`, near `p` the orbit is tangent to `f(p)` (`orbit_tangent`: every return of the orbit to
  `p` is a period), so the projection `P` along `f(p)` onto `f(p)^⊥` satisfies
  `‖P Mᵏ‖ ≤ ‖P‖ |C| e^{−λkT}`, and `DΠ(p)ᵏ⁺¹ = P Mᵏ⁺¹`. For `λ > 0` this also forces the trivial
  multiplier to be simple (`multipliers_le_of_decay`). Together with `andronov_witt_rate`: the
  supremum of the rates of orbital attraction is exactly `−log ρ/T`.

Scope.
* As in `theorem/Periodic/AndronovWitt.lean`: `ẋ = f(x)` on `ℝ^{Fin n}` with the sup norm, `f`
  of class `C¹` and globally `K`-Lipschitz, `x_*` a global nonconstant `T`-periodic solution
  (`T > 0`, `f(x_*(0)) ≠ 0`; `T` need not be the minimal period), solutions on `[0, ∞)`
  (Mathlib `IsIntegralCurveOn`), orbital distance `Metric.infDist` to the range of `x_*`. The
  localization to fields without a global Lipschitz bound (`AndronovWitt.andronov_witt_local`)
  is not repeated here.
* The rate hypothesis is on the spectrum of `DΠ(p)` (`asymptoticPhase_rate_of_section`,
  `asymptoticPhase_rate`, `infDist_orbit_rate`), or equivalently on the multipliers
  (`andronov_witt_rate`: `1` simple, every other multiplier of modulus `< e^{−λT}`); `λ > 0`.
  The constants `δ`, `C`, `L` depend on `λ` and are not explicit.
* The phase function `Θ_σ` belongs to the point `x_*(σ)` and is defined and Lipschitz on the
  ball `‖ξ − x_*(σ)‖ < δ`, with `Θ_σ(x_*(σ)) = 0`; asymptotic phases are unique only up to the
  periods of `x_*`, and this fixes the branch.
* The rate `−log ρ/T` itself is not decided here (one expects it to be attained when the
  eigenvalues of modulus `ρ` are semisimple and to fail at a Jordan block; neither is proved).
  The converse uses only the solutions from the ball about `x_*(0)`, sampled at the times `kT`.
  The hypothesis and the conclusion on the eigenvalues are the spectral-radius inequalities
  `ρ(DΠ(p)) < e^{−λT}` resp. `ρ(DΠ(p)) ≤ e^{−λT}` (`spectralRadius_lt_ofReal_iff`,
  `spectralRadius_le_ofReal_iff`).
* Generic mathematics; no model family.

Source: A. A. Andronov and A. A. Witt, "Zur Stabilität nach Liapounoff", Phys. Z. Sowjetunion 4
(1933); Coddington and Levinson, *Theory of Ordinary Differential Equations*, Ch. 13 §2 (orbital
asymptotic stability with asymptotic phase); Hartman, *Ordinary Differential Equations* (the
asymptotic phase); Katok and Hasselblatt, *Introduction to the Modern Theory of Dynamical
Systems*, §1.2 (adapted norms: a norm in which a linear map contracts at any rate above its
spectral radius); Gelfand's spectral radius formula; the open item of
`theorem/Periodic/AndronovWitt.lean` (Scope: "the rate is `λ = −log q/(3T/2)` with `q < 1` a
geometric rate of `Π` …, not the optimal `−log ρ(DΠ(p))/T`"; the phase only bounded,
`|θ| ≤ C ‖x(0) − x_*(σ)‖`).

Results.
* Linear algebra and maps: `exists_pow_norm_lt_pow` (every eigenvalue of modulus `< q` gives
  `‖Aᵐ‖ < qᵐ`), `exists_contraction_of_spectrum` (a map with strict derivative `A` at a fixed
  point contracts differences at the rate `q`: `‖Fᵏ ξ − Fᵏ ξ'‖ ≤ N qᵏ ‖ξ − ξ'‖`).
* **Optimal rate and Lipschitz phase**: `asymptoticPhase_rate_of_section` (from `x_*(0)`),
  `asymptoticPhase_rate` (uniformly from every `x_*(σ)`), `infDist_orbit_rate` (orbital
  exponential stability at the rate `λ`), `spectrum_sectionMatrix_lt` (the multiplier
  hypothesis bounds the spectrum of `DΠ(p)`), **the theorem** `andronov_witt_rate`.
* **Optimality**: `orbit_tangent`, `spectrum_sectionMatrix_le_of_decay`,
  `multipliers_le_of_decay`; the spectral-radius forms `spectralRadius_lt_ofReal_iff`,
  `spectralRadius_le_ofReal_iff`.

Corrections.
None: a sharpening (the optimal rate, the Lipschitz phase and the optimality of the rate, which
`theorem/Periodic/AndronovWitt.lean` left open).

Family and connection conclusions.
None: static evidence on autonomous ODEs (orbital stability of a periodic orbit).
-/

noncomputable section
namespace powerlib.Periodic.AndronovWittRate

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative FlipOrbit PoincareSection

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

/-- **A spectral bound gives a power bound.** If every complex eigenvalue of a real matrix `A`
has modulus `< q`, `q > 0`, then `‖Aᵐ‖ < qᵐ` for some `m > 0` (the matrix `q⁻¹ A` is Schur stable,
`LTI.exists_pow_norm_lt_one`). -/
@[tmio T, powerlib_foundation] theorem exists_pow_norm_lt_pow {A : Matrix (Fin n) (Fin n) ℝ}
    {q : ℝ} (hq : 0 < q) (hA : ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), ‖μ‖ < q) :
    ∃ m : ℕ, 0 < m ∧ ‖A ^ m‖ < q ^ m := by
  set B := q⁻¹ • A with hB
  have hBS : LTI.SchurStable B := by
    intro μ v hv hBv
    have hmap : B.map (algebraMap ℝ ℂ) = ((q⁻¹ : ℝ) : ℂ) • A.map (algebraMap ℝ ℂ) := by
      ext i j; simp [hB]
    have hAv : A.map (algebraMap ℝ ℂ) *ᵥ v = ((q : ℂ) * μ) • v := by
      rw [hmap, Matrix.smul_mulVec] at hBv
      have hq' : ((q : ℂ)) ≠ 0 := by exact_mod_cast hq.ne'
      calc A.map (algebraMap ℝ ℂ) *ᵥ v
          = (q : ℂ) • (((q⁻¹ : ℝ) : ℂ) • (A.map (algebraMap ℝ ℂ) *ᵥ v)) := by
            rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hq', one_smul]
        _ = ((q : ℂ) * μ) • v := by rw [hBv, smul_smul]
    have hmem : (q : ℂ) * μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) :=
      LTI.mem_spectrum_iff_exists_eigvec.2 ⟨v, hv, hAv⟩
    have h := hA _ hmem
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le] at h
    exact (mul_lt_iff_lt_one_right hq).1 h
  obtain ⟨m, hm, hlt⟩ :=
    LTI.exists_pow_norm_lt_one B ((LTI.schurStable_iff_spectralRadius_lt_one B).1 hBS)
  refine ⟨m, hm, ?_⟩
  have hAB : A ^ m = q ^ m • B ^ m := by
    rw [hB, smul_pow, smul_smul, ← mul_pow, mul_inv_cancel₀ hq.ne', one_pow, one_smul]
  rw [hAB, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc q ^ m * ‖B ^ m‖ < q ^ m * 1 := mul_lt_mul_of_pos_left hlt (by positivity)
    _ = q ^ m := mul_one _

/-- **Contraction at every rate above the spectral radius.** Let `F` fix `p` with strict
derivative `A` there, and let every complex eigenvalue of `A` have modulus `< q`, `0 < q ≤ 1`.
Then there are `r > 0`, `N ≥ 1` with `‖Fᵏ ξ − Fᵏ ξ'‖ ≤ N qᵏ ‖ξ − ξ'‖` for all `ξ`, `ξ'` in the
ball `‖· − p‖ < r` and all `k`. (In the adapted norm `ν(x) = Σ_{j<m} q^{−j} ‖Aʲ x‖`, with
`‖Aᵐ‖ < qᵐ`, `F` is a `q`-contraction on a `ν`-ball about `p`.) -/
@[tmio T, powerlib_foundation] theorem exists_contraction_of_spectrum
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' A).toContinuousLinearMap p) (hFp : F p = p)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hA : ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), ‖μ‖ < q) :
    ∃ r N : ℝ, 0 < r ∧ 1 ≤ N ∧ ∀ ξ ξ', ‖ξ - p‖ < r → ‖ξ' - p‖ < r → ∀ k : ℕ,
      ‖F^[k] ξ - F^[k] ξ'‖ ≤ N * q ^ k * ‖ξ - ξ'‖ := by
  obtain ⟨m, hm, hAm⟩ := exists_pow_norm_lt_pow hq0 hA
  set ν : (Fin n → ℝ) → ℝ := fun x => ∑ j ∈ Finset.range m, (q ^ j)⁻¹ * ‖(A ^ j) *ᵥ x‖ with hν
  set N₀ := ∑ j ∈ Finset.range m, (q ^ j)⁻¹ * ‖A ^ j‖ with hN₀
  have hN₀0 : 0 ≤ N₀ := Finset.sum_nonneg fun j _ => by positivity
  have hν_ge : ∀ x, ‖x‖ ≤ ν x := fun x => by
    have h0 : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.2 hm
    have h := Finset.single_le_sum (f := fun j => (q ^ j)⁻¹ * ‖(A ^ j) *ᵥ x‖)
      (fun j _ => by positivity) h0
    simpa using h
  have hν_le : ∀ x, ν x ≤ N₀ * ‖x‖ := fun x => by
    rw [hN₀, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) (by positivity)
  have hν_add : ∀ x y, ν (x + y) ≤ ν x + ν y := fun x y => by
    simp only [hν, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.mulVec_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
  have hν_neg : ∀ x, ν (-x) = ν x := fun x => by
    simp only [hν, Matrix.mulVec_neg, norm_neg]
  have hν_sub : ∀ x y, ν (x - y) ≤ ν x + ν y := fun x y => by
    rw [sub_eq_add_neg]; exact (hν_add _ _).trans (by rw [hν_neg])
  set c := q - q * ((q ^ m)⁻¹ * ‖A ^ m‖) with hc
  have hc0 : 0 < c := by
    have h1 : (q ^ m)⁻¹ * ‖A ^ m‖ < 1 := by
      rw [inv_mul_lt_iff₀ (by positivity), mul_one]; exact hAm
    rw [hc]; nlinarith
  have hν_A : ∀ x, ν (A *ᵥ x) ≤ q * ν x - c * ‖x‖ := fun x => by
    set a : ℕ → ℝ := fun j => (q ^ j)⁻¹ * ‖(A ^ j) *ᵥ x‖ with ha
    have hνA : ν (A *ᵥ x) = q * ∑ j ∈ Finset.range m, a (j + 1) := by
      simp only [hν, ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_mulVec, ← pow_succ, pow_succ q j, mul_inv]
      field_simp
    have hsplit : ∑ j ∈ Finset.range m, a (j + 1) = ν x + a m - a 0 := by
      have h1 := Finset.sum_range_succ' a m
      have h2 := Finset.sum_range_succ a m
      have : ν x = ∑ j ∈ Finset.range m, a j := rfl
      linarith
    have ha0 : a 0 = ‖x‖ := by simp [ha]
    have ham : a m ≤ (q ^ m)⁻¹ * ‖A ^ m‖ * ‖x‖ := by
      rw [ha, mul_assoc]
      exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) (by positivity)
    rw [hνA, hsplit, ha0, hc]
    nlinarith
  -- the strict derivative on a ball
  set ε := c / (N₀ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hlo := (hasStrictFDerivAt_iff_isLittleO.1 hF).def hε0
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.1 hlo
  have hrem : ∀ ξ ξ', ‖ξ - p‖ < ρ → ‖ξ' - p‖ < ρ →
      ‖F ξ - F ξ' - A *ᵥ (ξ - ξ')‖ ≤ ε * ‖ξ - ξ'‖ := fun ξ ξ' hξ hξ' => by
    have h := hρb (y := (ξ, ξ')) (by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hξ, hξ'⟩)
    simpa using h
  have hstep : ∀ ξ ξ', ‖ξ - p‖ < ρ → ‖ξ' - p‖ < ρ → ν (F ξ - F ξ') ≤ q * ν (ξ - ξ') :=
    fun ξ ξ' hξ hξ' => by
      have e : F ξ - F ξ' = A *ᵥ (ξ - ξ') + (F ξ - F ξ' - A *ᵥ (ξ - ξ')) := by abel
      have h1 := hν_A (ξ - ξ')
      have h2 := hν_le (F ξ - F ξ' - A *ᵥ (ξ - ξ'))
      have h3 := hrem ξ ξ' hξ hξ'
      have h4 : N₀ * ‖F ξ - F ξ' - A *ᵥ (ξ - ξ')‖ ≤ c * ‖ξ - ξ'‖ := by
        calc N₀ * ‖F ξ - F ξ' - A *ᵥ (ξ - ξ')‖ ≤ N₀ * (ε * ‖ξ - ξ'‖) :=
              mul_le_mul_of_nonneg_left h3 hN₀0
          _ ≤ (N₀ + 1) * (ε * ‖ξ - ξ'‖) := by nlinarith [norm_nonneg (ξ - ξ')]
          _ = c * ‖ξ - ξ'‖ := by rw [hε]; field_simp
      rw [e]
      linarith [hν_add (A *ᵥ (ξ - ξ')) (F ξ - F ξ' - A *ᵥ (ξ - ξ'))]
  have hin : ∀ ξ, ν (ξ - p) < ρ → ‖ξ - p‖ < ρ := fun ξ h => (hν_ge _).trans_lt h
  have hiter : ∀ ξ ξ', ν (ξ - p) < ρ → ν (ξ' - p) < ρ → ∀ k : ℕ,
      ν (F^[k] ξ - F^[k] ξ') ≤ q ^ k * ν (ξ - ξ') ∧ ν (F^[k] ξ - p) < ρ ∧
        ν (F^[k] ξ' - p) < ρ := fun ξ ξ' hξ hξ' k => by
    induction k with
    | zero => simpa using ⟨hξ, hξ'⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hp : F^[k] p = p := Function.iterate_fixed hFp k
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨?_, ?_, ?_⟩
      · calc ν (F (F^[k] ξ) - F (F^[k] ξ')) ≤ q * ν (F^[k] ξ - F^[k] ξ') :=
              hstep _ _ (hin _ h2) (hin _ h3)
          _ ≤ q * (q ^ k * ν (ξ - ξ')) := mul_le_mul_of_nonneg_left h1 hq0.le
          _ = q ^ (k + 1) * ν (ξ - ξ') := by ring
      · have := hstep (F^[k] ξ) p (hin _ h2) (by simpa using hρ)
        rw [hFp] at this
        have hν0 : 0 ≤ ν (F^[k] ξ - p) := (norm_nonneg _).trans (hν_ge _)
        nlinarith
      · have := hstep (F^[k] ξ') p (hin _ h3) (by simpa using hρ)
        rw [hFp] at this
        have hν0 : 0 ≤ ν (F^[k] ξ' - p) := (norm_nonneg _).trans (hν_ge _)
        nlinarith
  refine ⟨ρ / (N₀ + 1), N₀ + 1, by positivity, by linarith, fun ξ ξ' hξ hξ' k => ?_⟩
  have hU : ∀ ξ, ‖ξ - p‖ < ρ / (N₀ + 1) → ν (ξ - p) < ρ := fun ξ h => by
    calc ν (ξ - p) ≤ N₀ * ‖ξ - p‖ := hν_le _
      _ ≤ (N₀ + 1) * ‖ξ - p‖ := by nlinarith [norm_nonneg (ξ - p)]
      _ < (N₀ + 1) * (ρ / (N₀ + 1)) := mul_lt_mul_of_pos_left h (by positivity)
      _ = ρ := by field_simp
  have h := (hiter ξ ξ' (hU ξ hξ) (hU ξ' hξ') k).1
  calc ‖F^[k] ξ - F^[k] ξ'‖ ≤ ν (F^[k] ξ - F^[k] ξ') := hν_ge _
    _ ≤ q ^ k * ν (ξ - ξ') := h
    _ ≤ q ^ k * (N₀ * ‖ξ - ξ'‖) := mul_le_mul_of_nonneg_left (hν_le _) (by positivity)
    _ ≤ (N₀ + 1) * q ^ k * ‖ξ - ξ'‖ := by
        have := pow_nonneg hq0.le k
        nlinarith [norm_nonneg (ξ - ξ'), mul_nonneg this (norm_nonneg (ξ - ξ'))]


/-- The orbit of a `T`-periodic solution of `ẋ = f(x)` is a Lipschitz function of time. -/
@[tmio T, powerlib_foundation] private theorem exists_lipschitzWith_orbit (hf : ContDiff ℝ 1 f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) : ∃ B : NNReal, LipschitzWith B xs := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (hf.continuous.comp hxc).continuousOn
  refine ⟨Real.toNNReal B, lipschitzWith_of_nnnorm_deriv_le (fun t => (hxs t).differentiableAt)
    fun t => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hT t
  rw [(hxs t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal', hty]
  exact (hB y (Ico_subset_Icc_self hy)).trans (le_max_left _ _)

/-- **The asymptotic phase at the section point, at every rate allowed by the spectrum, and
Lipschitz.** Let `x_*` be a nonconstant `T`-periodic orbit of `ẋ = f(x)` (`f` of class `C¹`,
globally Lipschitz) and let every eigenvalue of the Poincaré Jacobian
`DΠ(p) = sectionMatrix M f(p)`, `p = x_*(0)`, have modulus `< e^{−λT}`, `λ > 0` (the spectral
radius `ρ` of `DΠ(p)` satisfies `λ < −log ρ/T`). Then there are `δ > 0`, `C, L ≥ 0` and a phase
function `Θ` with `Θ(p) = 0`, `L`-Lipschitz on the ball `‖ξ − p‖ < δ`, such that every solution
`x` on `[0, ∞)` with `‖x(0) − p‖ < δ` satisfies
`‖x(t) − x_*(t + Θ(x(0)))‖ ≤ C e^{−λt} ‖x(0) − p‖` for `t ≥ 0`. The phase is
`Θ(ξ) = −Σ_j (τ(Πʲ ξ) − T)`, the limit of `kT − t_k(ξ)` over the crossing times `t_k`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_rate_of_section (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hρ : ∀ μ ∈ spectrum ℂ ((sectionMatrix (monodromy (variationalMatrix f xs) T 0)
      (f (xs 0))).map (algebraMap ℝ ℂ)), ‖μ‖ < Real.exp (-(lam * T))) :
    ∃ δ C L : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 ≤ L ∧ ∃ Θ : (Fin n → ℝ) → ℝ, Θ (xs 0) = 0 ∧
      (∀ ξ ξ', ‖ξ - xs 0‖ < δ → ‖ξ' - xs 0‖ < δ → |Θ ξ - Θ ξ'| ≤ L * ‖ξ - ξ'‖) ∧
      ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs 0‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - xs (t + Θ (x 0))‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs 0‖ := by
  obtain ⟨τ, hτp, hτD, ⟨r, s, hr, hs, hsT, hsec, -⟩, hPp, hPD, -, -, -, -⟩ :=
    exists_poincareMap hf hfK hxs hT hper hne
  set P := poincareMap hfK τ with hP
  set p := xs 0 with hp
  set q := Real.exp (-(lam * T)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  obtain ⟨r₁, N, hr₁, hN, hcon⟩ := exists_contraction_of_spectrum hPD hPp hq0 hq1.le hρ
  have hN0 : 0 < N := by linarith
  -- the return time is Lipschitz near `p`
  obtain ⟨Lτ', U, hU, hLip⟩ := hτD.exists_lipschitzOnWith
  obtain ⟨r₂, hr₂, hr₂U⟩ := Metric.mem_nhds_iff.1 hU
  set Lτ : ℝ := (Lτ' : ℝ) with hLτ
  have hLτ0 : 0 ≤ Lτ := Lτ'.2
  have hτL : ∀ ξ ξ', ‖ξ - p‖ < r₂ → ‖ξ' - p‖ < r₂ → |τ ξ - τ ξ'| ≤ Lτ * ‖ξ - ξ'‖ :=
    fun ξ ξ' hξ hξ' => by
      have h := hLip.dist_le_mul ξ (hr₂U (by rwa [Metric.mem_ball, dist_eq_norm]))
        ξ' (hr₂U (by rwa [Metric.mem_ball, dist_eq_norm]))
      rwa [Real.dist_eq, dist_eq_norm] at h
  obtain ⟨Bn, hBn⟩ := exists_lipschitzWith_orbit hf hxs hT hper
  set B : ℝ := (Bn : ℝ) with hBdef
  have hB0 : 0 ≤ B := Bn.2
  have hB : ∀ a b, ‖xs a - xs b‖ ≤ B * |a - b| := fun a b => by
    have h := hBn.dist_le_mul a b
    rwa [dist_eq_norm, Real.dist_eq] at h
  -- the radii
  set ρ₀ := min r r₂ with hρ₀
  have hρ₀0 : 0 < ρ₀ := lt_min hr hr₂
  set δ := min r₁ (ρ₀ / N) with hδ
  have hδ0 : 0 < δ := lt_min hr₁ (div_pos hρ₀0 hN0)
  have hitp : ∀ ξ, ‖ξ - p‖ < δ → ∀ k : ℕ, ‖P^[k] ξ - p‖ ≤ N * q ^ k * ‖ξ - p‖ :=
    fun ξ hξ k => by
      have h := hcon ξ p (hξ.trans_le (min_le_left _ _)) (by simpa using hr₁) k
      rwa [Function.iterate_fixed hPp] at h
  have hitb : ∀ ξ, ‖ξ - p‖ < δ → ∀ k : ℕ, ‖P^[k] ξ - p‖ < ρ₀ := fun ξ hξ k => by
    have h1 : N * q ^ k * ‖ξ - p‖ ≤ N * ‖ξ - p‖ := by
      have := pow_le_one₀ hq0.le hq1.le (n := k)
      have : N * q ^ k ≤ N * 1 := mul_le_mul_of_nonneg_left this hN0.le
      nlinarith [norm_nonneg (ξ - p)]
    have h2 : N * ‖ξ - p‖ < ρ₀ := by
      have := hξ.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀' hN0] at this
    exact (hitp ξ hξ k).trans_lt (h1.trans_lt h2)
  have hitd : ∀ ξ ξ', ‖ξ - p‖ < δ → ‖ξ' - p‖ < δ → ∀ k : ℕ,
      |τ (P^[k] ξ) - τ (P^[k] ξ')| ≤ Lτ * N * ‖ξ - ξ'‖ * q ^ k := fun ξ ξ' hξ hξ' k => by
    refine (hτL _ _ ((hitb ξ hξ k).trans_le (min_le_right _ _))
      ((hitb ξ' hξ' k).trans_le (min_le_right _ _))).trans ?_
    have h := hcon ξ ξ' (hξ.trans_le (min_le_left _ _)) (hξ'.trans_le (min_le_left _ _)) k
    calc Lτ * ‖P^[k] ξ - P^[k] ξ'‖ ≤ Lτ * (N * q ^ k * ‖ξ - ξ'‖) :=
          mul_le_mul_of_nonneg_left h hLτ0
      _ = Lτ * N * ‖ξ - ξ'‖ * q ^ k := by ring
  have hpδ : ‖p - p‖ < δ := by simpa using hδ0
  have hu : ∀ ξ, ‖ξ - p‖ < δ → ∀ j : ℕ, |τ (P^[j] ξ) - T| ≤ Lτ * N * ‖ξ - p‖ * q ^ j :=
    fun ξ hξ j => by
      have h := hitd ξ p hξ hpδ j
      rwa [Function.iterate_fixed hPp, hτp] at h
  have h1q : 0 < 1 - q := by linarith
  set Cθ := Lτ * N / (1 - q) with hCθ
  have hCθ0 : 0 ≤ Cθ := by positivity
  have hsum : ∀ ξ, ‖ξ - p‖ < δ → Summable fun j : ℕ => τ (P^[j] ξ) - T := fun ξ hξ =>
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hq0.le hq1).mul_left (Lτ * N * ‖ξ - p‖))
      fun j => by rw [Real.norm_eq_abs]; exact hu ξ hξ j
  -- the phase
  set Θ : (Fin n → ℝ) → ℝ := fun ξ => -∑' j : ℕ, (τ (P^[j] ξ) - T) with hΘ
  have hΘp : Θ p = 0 := by simp [hΘ, Function.iterate_fixed hPp, hτp]
  have hΘL : ∀ ξ ξ', ‖ξ - p‖ < δ → ‖ξ' - p‖ < δ → |Θ ξ - Θ ξ'| ≤ Cθ * ‖ξ - ξ'‖ :=
    fun ξ ξ' hξ hξ' => by
      have e : Θ ξ - Θ ξ' = ∑' j : ℕ, (τ (P^[j] ξ') - τ (P^[j] ξ)) := by
        rw [show (fun j : ℕ => τ (P^[j] ξ') - τ (P^[j] ξ)) =
          fun j => (τ (P^[j] ξ') - T) - (τ (P^[j] ξ) - T) from funext fun j => by ring]
        rw [(hsum ξ' hξ').tsum_sub (hsum ξ hξ)]; simp only [hΘ]; ring
      rw [e]
      have hg : HasSum (fun j : ℕ => Lτ * N * ‖ξ - ξ'‖ * q ^ j)
          (Lτ * N * ‖ξ - ξ'‖ * (1 - q)⁻¹) :=
        (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
      have h := tsum_of_norm_bounded (f := fun j : ℕ => τ (P^[j] ξ') - τ (P^[j] ξ)) hg
        fun j => by
          rw [Real.norm_eq_abs]
          have := hitd ξ' ξ hξ' hξ j
          rwa [norm_sub_rev] at this
      rw [Real.norm_eq_abs] at h
      calc _ ≤ _ := h
        _ = Cθ * ‖ξ - ξ'‖ := by rw [hCθ]; field_simp
  set E₀ := Real.exp (lam * (T + 2 * Cθ * δ)) with hE₀
  refine ⟨δ, (N + B * Cθ) * Real.exp (K * (3 * T / 2)) * E₀, Cθ, hδ0, by positivity, hCθ0, Θ,
    hΘp, hΘL, fun x hx hx0 t ht => ?_⟩
  set ξ := x 0 with hξ
  set d := ‖ξ - p‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hτs : ∀ k : ℕ, |τ (P^[k] ξ) - T| < s := fun k =>
    (hsec _ ((hitb ξ hx0 k).trans_le (min_le_left _ _))).1
  have hτpos : ∀ k : ℕ, T / 2 ≤ τ (P^[k] ξ) := fun k => by
    have := abs_lt.1 (hτs k); linarith
  have hτup : ∀ k : ℕ, τ (P^[k] ξ) ≤ 3 * T / 2 := fun k => by
    have := abs_lt.1 (hτs k); linarith
  -- the accumulated return times
  set tt : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, τ (P^[j] ξ) with htt
  have htt_iter : ∀ k : ℕ, P^[k] ξ = x (tt k) := fun k =>
    AndronovWitt.iterate_poincareMap hfK τ hx k fun j _ => le_trans (by linarith) (hτpos j)
  have htt_succ : ∀ k : ℕ, tt (k + 1) = tt k + τ (P^[k] ξ) := fun k =>
    Finset.sum_range_succ _ _
  have htt_ge : ∀ k : ℕ, (k : ℝ) * (T / 2) ≤ tt k := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτpos k]
  set u : ℕ → ℝ := fun j => τ (P^[j] ξ) - T with hu'
  have husum : Summable u := hsum ξ hx0
  set θ' := ∑' j, u j with hθ'
  have hΘx : Θ ξ = -θ' := rfl
  have htail : ∀ k : ℕ, |tt k - k * T - θ'| ≤ Cθ * d * q ^ k := fun k => by
    have hsplit := husum.sum_add_tsum_nat_add k
    have hsum' : tt k - k * T = ∑ j ∈ Finset.range k, u j := by
      simp only [htt, hu', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have he : tt k - k * T - θ' = -∑' j, u (j + k) := by
      rw [hsum', hθ', ← hsplit]; ring
    rw [he, abs_neg]
    have hg : HasSum (fun j : ℕ => Lτ * N * d * q ^ k * q ^ j)
        (Lτ * N * d * q ^ k * (1 - q)⁻¹) :=
      (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
    have hb := tsum_of_norm_bounded hg fun j => by
      rw [Real.norm_eq_abs]
      calc |u (j + k)| ≤ Lτ * N * d * q ^ (j + k) := hu ξ hx0 (j + k)
        _ = Lτ * N * d * q ^ k * q ^ j := by rw [pow_add]; ring
    rw [Real.norm_eq_abs] at hb
    calc |∑' j, u (j + k)| ≤ Lτ * N * d * q ^ k * (1 - q)⁻¹ := hb
      _ = Cθ * d * q ^ k := by rw [hCθ]; field_simp
  have hθ'b : |θ'| ≤ Cθ * d := by
    have h := htail 0
    simpa [htt] using h
  -- the period containing `t`
  have hex : ∃ k : ℕ, t < tt (k + 1) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (t / (T / 2))
    refine ⟨k, lt_of_lt_of_le ?_ (htt_ge (k + 1))⟩
    rw [div_lt_iff₀ (by positivity)] at hk
    push_cast; nlinarith
  classical
  set k := Nat.find hex with hk
  have hk1 : t < tt (k + 1) := Nat.find_spec hex
  have hk0 : tt k ≤ t := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simpa [htt] using ht
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel hpos] at this
      exact not_lt.1 this
  -- Grönwall on `[t_k, t]`
  have hxs' : IsIntegralCurveOn (fun r => xs (r + Θ ξ)) (fun _ => f) (Icc (tt k) t) :=
    fun r _ => ((hxs (r + Θ ξ)).comp_add_const r (Θ ξ)).hasDerivWithinAt
  have htk0 : 0 ≤ tt k := le_trans (by positivity) (htt_ge k)
  have hxI : IsIntegralCurveOn x (fun _ => f) (Icc (tt k) t) :=
    hx.mono fun q hq => mem_Ici.2 (htk0.trans hq.1)
  have hgr := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK) hxI hxs' t ⟨hk0, le_rfl⟩
  rw [dist_eq_norm, dist_eq_norm] at hgr
  -- the deviation at the crossing `t_k`
  have hdev : ‖x (tt k) - xs (tt k + Θ ξ)‖ ≤ (N + B * Cθ) * q ^ k * d := by
    have hpk : xs (k * T) = p := hper.nat_mul_eq k
    calc ‖x (tt k) - xs (tt k + Θ ξ)‖ = ‖(P^[k] ξ - p) + (xs (k * T) - xs (tt k + Θ ξ))‖ := by
          rw [htt_iter, hpk]; abel_nf
      _ ≤ ‖P^[k] ξ - p‖ + ‖xs (k * T) - xs (tt k + Θ ξ)‖ := norm_add_le _ _
      _ ≤ N * q ^ k * d + B * |k * T - (tt k + Θ ξ)| :=
          add_le_add (hitp ξ hx0 k) (hB _ _)
      _ = N * q ^ k * d + B * |tt k - k * T - θ'| := by
          rw [hΘx, abs_sub_comm]; ring_nf
      _ ≤ N * q ^ k * d + B * (Cθ * d * q ^ k) := by gcongr; exact htail k
      _ = (N + B * Cθ) * q ^ k * d := by ring
  -- the rate
  have hqk : q ^ k ≤ E₀ * Real.exp (-(lam * t)) := by
    have h1 : tt (k + 1) ≤ (k + 1 : ℕ) * T + 2 * Cθ * δ := by
      have h2 := htail (k + 1)
      have h3 : Cθ * d * q ^ (k + 1) ≤ Cθ * d := by
        have := pow_le_one₀ hq0.le hq1.le (n := k + 1)
        have : 0 ≤ Cθ * d := mul_nonneg hCθ0 hd0
        nlinarith
      have h4 : Cθ * d ≤ Cθ * δ := mul_le_mul_of_nonneg_left hx0.le hCθ0
      have := abs_le.1 h2
      have := abs_le.1 hθ'b
      linarith
    have h5 : q ^ k = Real.exp (-(lam * (k * T))) := by
      rw [hq, ← Real.exp_nat_mul]; ring_nf
    rw [h5, hE₀, ← Real.exp_add, Real.exp_le_exp]
    push_cast at h1
    nlinarith
  have hgap : t - tt k ≤ 3 * T / 2 := by
    have := htt_succ k; linarith [hτup k]
  calc ‖x t - xs (t + Θ ξ)‖ ≤ ‖x (tt k) - xs (tt k + Θ ξ)‖ * Real.exp (K * (t - tt k)) := hgr
    _ ≤ (N + B * Cθ) * q ^ k * d * Real.exp (K * (3 * T / 2)) := by
        have he : Real.exp (K * (t - tt k)) ≤ Real.exp (K * (3 * T / 2)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hgap K.2)
        exact mul_le_mul hdev he (Real.exp_pos _).le (by positivity)
    _ ≤ (N + B * Cθ) * (E₀ * Real.exp (-(lam * t))) * d * Real.exp (K * (3 * T / 2)) := by
        have hNB : 0 ≤ N + B * Cθ := by have := mul_nonneg hB0 hCθ0; linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqk hNB) hd0) (Real.exp_pos _).le
    _ = (N + B * Cθ) * Real.exp (K * (3 * T / 2)) * E₀ * Real.exp (-(lam * t)) * d := by ring


/-- **The asymptotic phase at every rate allowed by the spectrum, Lipschitz, uniformly along the
orbit.** Under the hypotheses of `asymptoticPhase_rate_of_section` there are `δ > 0` and
`C, L ≥ 0` such that for every point `x_*(σ)` of the orbit there is a phase function `Θ_σ`,
`Θ_σ(x_*(σ)) = 0`, `L`-Lipschitz on the ball `‖ξ − x_*(σ)‖ < δ`, with
`‖x(t) − x_*(t + σ + Θ_σ(x(0)))‖ ≤ C e^{−λt} ‖x(0) − x_*(σ)‖` for every solution `x` on
`[0, ∞)` starting in that ball and every `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_rate (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hρ : ∀ μ ∈ spectrum ℂ ((sectionMatrix (monodromy (variationalMatrix f xs) T 0)
      (f (xs 0))).map (algebraMap ℝ ℂ)), ‖μ‖ < Real.exp (-(lam * T))) :
    ∃ δ C L : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 ≤ L ∧ ∀ σ : ℝ, ∃ Θ : (Fin n → ℝ) → ℝ, Θ (xs σ) = 0 ∧
      (∀ ξ ξ', ‖ξ - xs σ‖ < δ → ‖ξ' - xs σ‖ < δ → |Θ ξ - Θ ξ'| ≤ L * ‖ξ - ξ'‖) ∧
      ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs σ‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - xs (t + σ + Θ (x 0))‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs σ‖ := by
  obtain ⟨δ₀, C₀, L₀, hδ₀, hC₀, hL₀, Θ₀, hΘ₀p, hΘ₀L, hmain⟩ :=
    asymptoticPhase_rate_of_section hf hfK hxs hT hper hne hlam hρ
  obtain ⟨Bn, hBn⟩ := exists_lipschitzWith_orbit hf hxs hT hper
  set B : ℝ := (Bn : ℝ) with hBdef
  have hB0 : 0 ≤ B := Bn.2
  have hB : ∀ a b, ‖xs a - xs b‖ ≤ B * |a - b| := fun a b => by
    have h := hBn.dist_le_mul a b
    rwa [dist_eq_norm, Real.dist_eq] at h
  set E := Real.exp (K * T) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg K.2 hT.le)
  have hE0 : 0 < E := by linarith
  set F := Real.exp (lam * T) with hF
  have hF1 : 1 ≤ F := Real.one_le_exp (mul_nonneg hlam.le hT.le)
  set hGc : Continuous (uncurry fun _ : ℝ => f) := hfK.continuous.comp continuous_snd
  set fl := flow (G := fun _ => f) hGc (fun _ => hfK) 0 with hfl
  have hflI : ∀ ξ, IsIntegralCurveOn (fl ξ) (fun _ => f) (Ici 0) :=
    fun ξ => flow_solution hGc (fun _ => hfK) 0 ξ
  have hfl0 : ∀ ξ, fl ξ 0 = ξ := fun ξ => flow_start hGc (fun _ => hfK) 0 ξ
  refine ⟨δ₀ / E, (C₀ + 1 + B * L₀) * E * F, L₀ * E, div_pos hδ₀ hE0, by positivity,
    by positivity, fun σ => ?_⟩
  -- the phase of `σ` in `[0, T)`
  set σ' := toIcoMod hT 0 σ with hσ'
  have hσ'I : σ' ∈ Ico 0 T := by simpa using toIcoMod_mem_Ico hT 0 σ
  have hshift : ∀ a, xs (a + σ) = xs (a + σ') := fun a => by
    have h := toIcoMod_add_toIcoDiv_zsmul hT 0 σ
    rw [← h, ← add_assoc]
    exact (hper.zsmul _) _
  have hσσ' : xs σ = xs σ' := by have := hshift 0; rwa [zero_add, zero_add] at this
  set u := T - σ' with hu
  have hu0 : 0 < u := by have := hσ'I.2; linarith
  have huT : u ≤ T := by have := hσ'I.1; linarith
  have hxs' : ∀ a b : ℝ, IsIntegralCurveOn (fun r => xs (r + σ')) (fun _ => f) (Icc a b) :=
    fun _ _ r _ => ((hxs (r + σ')).comp_add_const r σ').hasDerivWithinAt
  -- the flow over `[0, u]` is `E`-Lipschitz and takes `x_*(σ)` to `x_*(0)`
  have hflL : ∀ ξ ξ', ‖fl ξ u - fl ξ' u‖ ≤ E * ‖ξ - ξ'‖ := fun ξ ξ' => by
    have h := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK)
      ((hflI ξ).mono fun q hq => mem_Ici.2 hq.1) ((hflI ξ').mono fun q hq => mem_Ici.2 hq.1)
      u ⟨hu0.le, le_rfl⟩
    rw [dist_eq_norm, dist_eq_norm, hfl0, hfl0, sub_zero] at h
    rw [mul_comm E]
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left huT K.2
  have hflσ : fl (xs σ) u = xs 0 := by
    have h := flow_eq hGc (fun _ => hfK) (ξ := xs σ) (β := fun r => xs (r + σ')) (by
      simp only [zero_add]; exact hσσ'.symm) (hxs' 0 u) u ⟨hu0.le, le_rfl⟩
    rw [hfl, ← h, hu, sub_add_cancel, show xs T = xs 0 by simpa using hper 0]
  set Θ : (Fin n → ℝ) → ℝ := fun ξ => Θ₀ (fl ξ u) with hΘ
  have hnear : ∀ ξ, ‖ξ - xs σ‖ < δ₀ / E → ‖fl ξ u - xs 0‖ < δ₀ := fun ξ hξ => by
    rw [← hflσ]
    calc ‖fl ξ u - fl (xs σ) u‖ ≤ E * ‖ξ - xs σ‖ := hflL _ _
      _ < E * (δ₀ / E) := mul_lt_mul_of_pos_left hξ hE0
      _ = δ₀ := by field_simp
  have hΘL : ∀ ξ ξ', ‖ξ - xs σ‖ < δ₀ / E → ‖ξ' - xs σ‖ < δ₀ / E →
      |Θ ξ - Θ ξ'| ≤ L₀ * E * ‖ξ - ξ'‖ := fun ξ ξ' hξ hξ' => by
    refine (hΘ₀L _ _ (hnear ξ hξ) (hnear ξ' hξ')).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hflL ξ ξ') hL₀
  have hΘσ : Θ (xs σ) = 0 := by rw [hΘ]; simp only; rw [hflσ]; exact hΘ₀p
  refine ⟨Θ, hΘσ, hΘL, fun x hx hx0 t ht => ?_⟩
  set d₀ := ‖x 0 - xs σ‖ with hd₀
  have hd0 : 0 ≤ d₀ := norm_nonneg _
  have hθ : |Θ (x 0)| ≤ L₀ * E * d₀ := by
    have h := hΘL (x 0) (xs σ) hx0 (by simpa using div_pos hδ₀ hE0)
    rwa [hΘσ, sub_zero] at h
  -- up to the time `u` the solution follows `x_*(· + σ')`
  have hfollow : ∀ r ∈ Icc 0 u, ‖x r - xs (r + σ')‖ ≤ E * d₀ := fun r hr => by
    have h := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK)
      (hx.mono fun q hq => mem_Ici.2 hq.1) (hxs' 0 u) r hr
    rw [dist_eq_norm, dist_eq_norm, zero_add, ← hσσ', sub_zero] at h
    rw [mul_comm] at h
    refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hd0)
    exact mul_le_mul_of_nonneg_left (hr.2.trans huT) K.2
  -- from the time `u` on, the phase of `asymptoticPhase_rate_of_section`
  set y : ℝ → Fin n → ℝ := fun r => x (r + u) with hy
  have hyI : IsIntegralCurveOn y (fun _ => f) (Ici 0) :=
    (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
      (Ici_subset_Ici.2 (by linarith))
  have hxu : x u = fl (x 0) u :=
    flow_eq hGc (fun _ => hfK) rfl (hx.mono fun q hq => mem_Ici.2 hq.1) u ⟨hu0.le, le_rfl⟩
  have hy0 : y 0 = fl (x 0) u := by simp only [hy, zero_add]; exact hxu
  have hy0' : ‖y 0 - xs 0‖ ≤ E * d₀ := by
    rw [hy0, ← hflσ]; exact hflL _ _
  have hΘy : Θ (x 0) = Θ₀ (y 0) := by rw [hy0]
  obtain hyθ := hmain y hyI (by rw [hy0]; exact hnear _ hx0)
  have hphase : xs (t + σ + Θ (x 0)) = xs (t + Θ (x 0) + σ') := by
    rw [show t + σ + Θ (x 0) = (t + Θ (x 0)) + σ by ring, hshift]
  rw [hphase]
  rcases le_or_gt u t with hut | htu
  · -- after the time `u`
    have h := hyθ (t - u) (by linarith)
    simp only [hy, sub_add_cancel] at h
    rw [← hΘy] at h
    have hper' : xs (t - u + Θ (x 0)) = xs (t + Θ (x 0) + σ') := by
      rw [hu, show t - (T - σ') + Θ (x 0) = (t + Θ (x 0) + σ') - T by ring]
      exact hper.sub_eq _
    rw [hper'] at h
    refine h.trans ?_
    have hexp : Real.exp (-(lam * (t - u))) ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hy0'' : ‖x (0 + u) - xs 0‖ ≤ E * d₀ := by simpa [hy] using hy0'
    calc C₀ * Real.exp (-(lam * (t - u))) * ‖x (0 + u) - xs 0‖
        ≤ C₀ * (F * Real.exp (-(lam * t))) * (E * d₀) := by
          have := Real.exp_pos (-(lam * (t - u)))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hC₀) hy0'' (norm_nonneg _)
            (by positivity)
      _ = C₀ * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ (C₀ + 1 + B * L₀) * E * F * Real.exp (-(lam * t)) * d₀ := by
          have h1 : C₀ ≤ C₀ + 1 + B * L₀ := by nlinarith [mul_nonneg hB0 hL₀]
          have h2 : 0 ≤ E * F * Real.exp (-(lam * t)) * d₀ := by positivity
          nlinarith
  · -- before the time `u`
    have h1 := hfollow t ⟨ht, htu.le⟩
    have h2 : ‖xs (t + σ') - xs (t + Θ (x 0) + σ')‖ ≤ B * |Θ (x 0)| := by
      refine (hB _ _).trans_eq ?_
      congr 1
      rw [show t + σ' - (t + Θ (x 0) + σ') = -Θ (x 0) by ring, abs_neg]
    have hexp : 1 ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖x t - xs (t + Θ (x 0) + σ')‖
        = ‖(x t - xs (t + σ')) + (xs (t + σ') - xs (t + Θ (x 0) + σ'))‖ := by abel_nf
      _ ≤ ‖x t - xs (t + σ')‖ + ‖xs (t + σ') - xs (t + Θ (x 0) + σ')‖ := norm_add_le _ _
      _ ≤ E * d₀ + B * (L₀ * E * d₀) :=
          add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hθ hB0))
      _ = (1 + B * L₀) * E * d₀ * 1 := by ring
      _ ≤ (1 + B * L₀) * E * d₀ * (F * Real.exp (-(lam * t))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (1 + B * L₀) * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ (C₀ + 1 + B * L₀) * E * F * Real.exp (-(lam * t)) * d₀ := by
          have h2 : 0 ≤ E * F * Real.exp (-(lam * t)) * d₀ := by positivity
          nlinarith


/-- **Orbital exponential stability at every rate allowed by the spectrum.** Under the hypotheses
of `asymptoticPhase_rate_of_section`, every solution `x` on `[0, ∞)` with
`dist(x(0), x_*(ℝ)) < δ` satisfies `dist(x(t), x_*(ℝ)) ≤ C e^{−λt} dist(x(0), x_*(ℝ))`. -/
@[tmio T, powerlib_foundation] theorem infDist_orbit_rate (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hρ : ∀ μ ∈ spectrum ℂ ((sectionMatrix (monodromy (variationalMatrix f xs) T 0)
      (f (xs 0))).map (algebraMap ℝ ℂ)), ‖μ‖ < Real.exp (-(lam * T))) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → Metric.infDist (x 0) (range xs) < δ →
      ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
        C * Real.exp (-(lam * t)) * Metric.infDist (x 0) (range xs) := by
  obtain ⟨δ, C, L, hδ, hC, _, hph⟩ := asymptoticPhase_rate hf hfK hxs hT hper hne hlam hρ
  refine ⟨δ, C, hδ, hC, fun x hx hx0 t ht => ?_⟩
  set D := Metric.infDist (x 0) (range xs) with hD
  set c := C * Real.exp (-(lam * t)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hne' : (range xs).Nonempty := range_nonempty xs
  have key : ∀ η, 0 < η → D + η < δ → Metric.infDist (x t) (range xs) ≤ c * (D + η) := by
    intro η hη hδη
    obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff hne').1
      (show D < D + η by linarith)
    rw [dist_eq_norm] at hσ
    obtain ⟨Θ, -, -, hΘ⟩ := hph σ
    calc Metric.infDist (x t) (range xs) ≤ dist (x t) (xs (t + σ + Θ (x 0))) :=
          Metric.infDist_le_dist_of_mem (mem_range_self _)
      _ = ‖x t - xs (t + σ + Θ (x 0))‖ := dist_eq_norm _ _
      _ ≤ c * ‖x 0 - xs σ‖ := hΘ x hx (hσ.trans hδη) t ht
      _ ≤ c * (D + η) := mul_le_mul_of_nonneg_left hσ.le hc0
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η := min (ε / (c + 1)) ((δ - D) / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by linarith)
  have hη1 : η ≤ ε / (c + 1) := min_le_left _ _
  have hη2 : D + η < δ := by have := min_le_right (ε / (c + 1)) ((δ - D) / 2); linarith
  have h := key η hη0 hη2
  have hcη : c * η ≤ ε := by
    calc c * η ≤ (c + 1) * η := by nlinarith
      _ ≤ (c + 1) * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hη1 (by positivity)
      _ = ε := by field_simp
  linarith [mul_add c D η]

/-- **The nontrivial multipliers bound the spectrum of the Poincaré Jacobian.** If the trivial
multiplier `1` is a simple root of `χ_M` and every other multiplier has modulus `< b`, `b > 0`,
then every eigenvalue of `DΠ(p) = sectionMatrix M f(p)` has modulus `< b` (its eigenvalues are
`0` and the nontrivial multipliers, `PoincareSection.mem_spectrum_deflate_iff`). -/
@[tmio T, powerlib_foundation] theorem spectrum_sectionMatrix_lt (hf : ContDiff ℝ 1 f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {b : ℝ} (hb0 : 0 < b)
    (h1 : (monodromy (variationalMatrix f xs) T 0).charpoly.rootMultiplicity 1 = 1)
    (hμ : ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)),
      μ ≠ 1 → ‖μ‖ < b) :
    ∀ μ ∈ spectrum ℂ ((sectionMatrix (monodromy (variationalMatrix f xs) T 0)
      (f (xs 0))).map (algebraMap ℝ ℂ)), ‖μ‖ < b := by
  set M := monodromy (variationalMatrix f xs) T 0 with hM
  have hMv := monodromy_mulVec_velocity hf hxs hT hper
  have hw := sectionVec_dotProduct hMv hne
  intro μ hμS
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simpa using hb0
  rcases eq_or_ne μ 1 with rfl | hμ1
  · exfalso
    have hd := (one_mem_spectrum_deflate_iff hMv hw).1 hμS
    have hM0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
    have h2 : 2 ≤ M.charpoly.rootMultiplicity 1 := by
      rw [Polynomial.le_rootMultiplicity_iff hM0, map_one]; exact hd
    omega
  · exact hμ μ ((mem_spectrum_deflate_iff hMv hw hμ0 hμ1).1 hμS) hμ1

/-- **The Andronov–Witt theorem at the optimal rate.** Let `x_*` be a nonconstant `T`-periodic
orbit of `ẋ = f(x)` (`f` of class `C¹`, globally Lipschitz) whose trivial multiplier `1` is a
simple root of `χ_M` and whose other multipliers all have modulus `< e^{−λT}`, `λ > 0` — every
`λ < −log ρ/T`, `ρ` the largest modulus of a nontrivial multiplier. Then the asymptotic phase
exists at the rate `λ` and is a Lipschitz function of the initial state (the conclusion of
`asymptoticPhase_rate`), and the orbit attracts at the rate `λ` (`infDist_orbit_rate`). -/
@[tmio T, powerlib_foundation] theorem andronov_witt_rate (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (h1 : (monodromy (variationalMatrix f xs) T 0).charpoly.rootMultiplicity 1 = 1)
    (hμ : ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)),
      μ ≠ 1 → ‖μ‖ < Real.exp (-(lam * T))) :
    (∃ δ C L : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 ≤ L ∧ ∀ σ : ℝ, ∃ Θ : (Fin n → ℝ) → ℝ, Θ (xs σ) = 0 ∧
      (∀ ξ ξ', ‖ξ - xs σ‖ < δ → ‖ξ' - xs σ‖ < δ → |Θ ξ - Θ ξ'| ≤ L * ‖ξ - ξ'‖) ∧
      ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs σ‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - xs (t + σ + Θ (x 0))‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs σ‖) ∧
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → Metric.infDist (x 0) (range xs) < δ →
      ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
        C * Real.exp (-(lam * t)) * Metric.infDist (x 0) (range xs) := by
  have hρ := spectrum_sectionMatrix_lt hf hxs hT hper hne (Real.exp_pos _) h1 hμ
  exact ⟨asymptoticPhase_rate hf hfK hxs hT hper hne hlam hρ,
    infDist_orbit_rate hf hfK hxs hT hper hne hlam hρ⟩


/-! ## The rate cannot be improved -/

/-- **Near `x_*(0)` the orbit is tangent to the velocity.** For every matrix `P` killing
`v = f(x_*(0))` and every `η > 0` there is `ρ > 0` such that every point `x_*(σ)` of the orbit
within `ρ` of `p = x_*(0)` satisfies `‖P (x_*(σ) − p)‖ ≤ η ‖x_*(σ) − p‖`: near `p` the orbit is
the arc through `p` (every return of the orbit to `p` is a period, by uniqueness of solutions),
whose chord is `s v + o(s)`. -/
@[tmio T, powerlib_foundation] theorem orbit_tangent (hf : ContDiff ℝ 1 f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P *ᵥ f (xs 0) = 0) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ σ, ‖xs σ - xs 0‖ < ρ → ‖P *ᵥ (xs σ - xs 0)‖ ≤ η * ‖xs σ - xs 0‖ := by
  set p := xs 0 with hp
  set v := f (xs 0) with hv
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hne
  set η₁ := min (‖v‖ / 2) (η * ‖v‖ / (2 * (‖P‖ + 1))) with hη₁
  have hη₁0 : 0 < η₁ := lt_min (by positivity) (by positivity)
  have hlo := (hasDerivAt_iff_isLittleO.1 (hxs 0)).def hη₁0
  obtain ⟨s₀, hs₀, hb⟩ := Metric.eventually_nhds_iff.1 hlo
  -- near the time `0`
  have hloc : ∀ s, |s| < s₀ → ‖P *ᵥ (xs s - p)‖ ≤ η * ‖xs s - p‖ := fun s hs => by
    have h := hb (y := s) (by rwa [Real.dist_eq, sub_zero])
    simp only [sub_zero, Real.norm_eq_abs] at h
    have h1 : ‖P *ᵥ (xs s - p)‖ ≤ ‖P‖ * (η₁ * |s|) := by
      have e : P *ᵥ (xs s - p) = P *ᵥ (xs s - p - s • v) := by
        rw [Matrix.mulVec_sub P (xs s - p), Matrix.mulVec_smul, hP, smul_zero, sub_zero]
      rw [e]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
    have h2 : |s| * ‖v‖ / 2 ≤ ‖xs s - p‖ := by
      have h3 : ‖s • v‖ ≤ ‖xs s - p‖ + ‖xs s - p - s • v‖ := by
        calc ‖s • v‖ = ‖(xs s - p) - (xs s - p - s • v)‖ := by abel_nf
          _ ≤ _ := norm_sub_le _ _
      rw [norm_smul, Real.norm_eq_abs] at h3
      have := min_le_left (‖v‖ / 2) (η * ‖v‖ / (2 * (‖P‖ + 1)))
      nlinarith [abs_nonneg s]
    have h4 : ‖P‖ * η₁ ≤ η * ‖v‖ / 2 := by
      have h3 : η₁ ≤ η * ‖v‖ / (2 * (‖P‖ + 1)) := min_le_right _ _
      calc ‖P‖ * η₁ ≤ (‖P‖ + 1) * η₁ := by nlinarith [norm_nonneg P]
        _ ≤ (‖P‖ + 1) * (η * ‖v‖ / (2 * (‖P‖ + 1))) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = η * ‖v‖ / 2 := by field_simp
    calc ‖P *ᵥ (xs s - p)‖ ≤ ‖P‖ * (η₁ * |s|) := h1
      _ = ‖P‖ * η₁ * |s| := by ring
      _ ≤ η * ‖v‖ / 2 * |s| := mul_le_mul_of_nonneg_right h4 (abs_nonneg s)
      _ = η * (|s| * ‖v‖ / 2) := by ring
      _ ≤ η * ‖xs s - p‖ := mul_le_mul_of_nonneg_left h2 hη.le
  -- every return to `p` is a period
  have hGd : ∀ (t : ℝ) x, DifferentiableAt ℝ ((fun _ : ℝ => f) t) x :=
    fun _ x => (hf.differentiable one_ne_zero) x
  have hD : Continuous fun q : ℝ × (Fin n → ℝ) => fderiv ℝ ((fun _ : ℝ => f) q.1) q.2 :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_snd
  have hret : ∀ σ₀, xs σ₀ = p → ∀ s, xs (σ₀ + s) = xs s := fun σ₀ h0 s => by
    have h := LocalField.eq_of_hasDerivAt_of_fderiv hGd hD (x := fun s => xs (σ₀ + s)) (y := xs)
      (fun t => (hxs (σ₀ + t)).comp_const_add σ₀ t) hxs (t₀ := 0) (by simpa using h0)
    exact congrFun h s
  -- away from the returns the orbit stays away from `p`
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  set Z := {σ ∈ Icc 0 T | xs σ = p} with hZ
  set W := Icc 0 T ∩ ⋂ σ₀ ∈ Z, {σ : ℝ | s₀ ≤ |σ - σ₀|} with hW
  have hWc : IsCompact W := by
    refine isCompact_Icc.inter_right (isClosed_biInter fun σ₀ _ => ?_)
    exact isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)
  obtain ⟨ρ₁, hρ₁, hρ₁W⟩ : ∃ ρ₁ > 0, ∀ σ ∈ W, ρ₁ ≤ ‖xs σ - p‖ := by
    by_cases hWne : W.Nonempty
    · obtain ⟨σm, hσm, hmin⟩ := hWc.exists_isMinOn hWne
        ((continuous_norm.comp (hxc.sub continuous_const)).continuousOn)
      refine ⟨‖xs σm - p‖, ?_, fun σ hσ => hmin hσ⟩
      refine norm_pos_iff.2 fun h0 => ?_
      have hZm : σm ∈ Z := ⟨hσm.1, sub_eq_zero.1 h0⟩
      have : s₀ ≤ |σm - σm| := mem_iInter₂.1 hσm.2 σm hZm
      simp only [sub_self, abs_zero] at this
      linarith
    · exact ⟨1, one_pos, fun σ hσ => absurd ⟨σ, hσ⟩ hWne⟩
  refine ⟨ρ₁, hρ₁, fun σ hσ => ?_⟩
  set σ' := toIcoMod hT 0 σ with hσ'
  have hσ'I : σ' ∈ Ico 0 T := by simpa using toIcoMod_mem_Ico hT 0 σ
  have hσσ' : xs σ = xs σ' := by
    have h := toIcoMod_add_toIcoDiv_zsmul hT 0 σ
    rw [← h]
    exact (hper.zsmul _) _
  rw [hσσ'] at hσ ⊢
  have hσ'W : σ' ∉ W := fun h => absurd (hρ₁W σ' h) (not_le.2 hσ)
  have : ∃ σ₀ ∈ Z, |σ' - σ₀| < s₀ := by
    by_contra hcon
    push Not at hcon
    exact hσ'W ⟨Ico_subset_Icc_self hσ'I, mem_iInter₂.2 fun σ₀ h => hcon σ₀ h⟩
  obtain ⟨σ₀, hσ₀Z, hσ₀⟩ := this
  have e : xs σ' = xs (σ' - σ₀) := by
    rw [← hret σ₀ hσ₀Z.2 (σ' - σ₀), add_sub_cancel]
  rw [e]
  exact hloc _ hσ₀


/-- **A map attracted to a set tangent to `ker P` has `P A` small.** Let `Φ` have the derivative
`A` at a fixed point `p`, map the ball `‖ξ − p‖ < δ` into the `c ‖ξ − p‖`-neighbourhood of a set
`O`, and let `O` be tangent to `ker P` at `p` (`‖P (z − p)‖ ≤ η ‖z − p‖` for `z ∈ O` near `p`,
for every `η > 0`). Then `‖P A h‖ ≤ ‖P‖ |c| ‖h‖` for every `h`. -/
@[tmio T, powerlib_foundation] private theorem norm_mulVec_le_of_infDist
    {Φ : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : Set (Fin n → ℝ)} (hO : O.Nonempty)
    (hΦ : HasFDerivAt Φ (Matrix.toLin' A).toContinuousLinearMap p) (hΦp : Φ p = p)
    {δ c : ℝ} (hδ : 0 < δ) (hdec : ∀ ξ, ‖ξ - p‖ < δ → Metric.infDist (Φ ξ) O ≤ c * ‖ξ - p‖)
    (htan : ∀ η > 0, ∃ ρ > 0, ∀ z ∈ O, ‖z - p‖ < ρ → ‖P *ᵥ (z - p)‖ ≤ η * ‖z - p‖)
    (h : Fin n → ℝ) : ‖P *ᵥ (A *ᵥ h)‖ ≤ ‖P‖ * |c| * ‖h‖ := by
  set R := |c| + 2 + ‖A‖ with hR
  have hR0 : 0 ≤ R := by positivity
  set Q := ‖h‖ * (2 * ‖P‖ + R) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have key : ∀ η, 0 < η → η ≤ 1 → ‖P *ᵥ (A *ᵥ h)‖ ≤ ‖P‖ * |c| * ‖h‖ + η * Q := by
    intro η hη hη1
    rcases eq_or_ne h 0 with rfl | hh
    · simp [hQ]
    have hh0 : 0 < ‖h‖ := norm_pos_iff.2 hh
    obtain ⟨ρ₂, hρ₂, hG⟩ := htan η hη
    obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff.1 (hΦ.isLittleO.def hη)
    set m₀ := min (min δ ρ₁) (ρ₂ / (R + 1)) with hm₀
    have hm₀0 : 0 < m₀ := lt_min (lt_min hδ hρ₁) (by positivity)
    have hm₁ : m₀ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
    have hm₂ : m₀ ≤ ρ₁ := (min_le_left _ _).trans (min_le_right _ _)
    have hm₃ : m₀ ≤ ρ₂ / (R + 1) := min_le_right _ _
    set ε := m₀ / (2 * ‖h‖) with hε
    have hε0 : 0 < ε := by positivity
    set d := ε * ‖h‖ with hd
    have hdm : d = m₀ / 2 := by rw [hd, hε]; field_simp
    have hd0 : 0 < d := by positivity
    set e := ε • h with he
    have hen : ‖e‖ = d := by rw [he, norm_smul, Real.norm_of_nonneg hε0.le]
    have hpe : ‖(p + e) - p‖ = d := by rw [add_sub_cancel_left, hen]
    -- a point of `O` close to `Φ(p + e)`
    have hdist := hdec (p + e) (by rw [hpe, hdm]; linarith)
    rw [hpe] at hdist
    obtain ⟨z, hzO, hz⟩ := (Metric.infDist_lt_iff hO).1
      (show Metric.infDist (Φ (p + e)) O < c * d + η * d by
        have := mul_pos hη hd0; linarith)
    rw [dist_eq_norm] at hz
    -- the linearization
    have hlin : ‖Φ (p + e) - p - A *ᵥ e‖ ≤ η * d := by
      have h1 := hb (y := p + e) (by rw [dist_eq_norm, hpe, hdm]; linarith)
      simp only [hΦp, add_sub_cancel_left, LinearMap.coe_toContinuousLinearMap',
        Matrix.toLin'_apply] at h1
      rwa [hen] at h1
    have hAe : ‖A *ᵥ e‖ ≤ ‖A‖ * d := by rw [← hen]; exact Matrix.linfty_opNorm_mulVec _ _
    have hcd : c * d ≤ |c| * d := mul_le_mul_of_nonneg_right (le_abs_self c) hd0.le
    have hzp : ‖z - p‖ ≤ d * R := by
      have e1 : z - p = -(Φ (p + e) - z) + (Φ (p + e) - p - A *ᵥ e) + A *ᵥ e := by abel
      calc ‖z - p‖ ≤ ‖Φ (p + e) - z‖ + ‖Φ (p + e) - p - A *ᵥ e‖ + ‖A *ᵥ e‖ := by
            rw [e1]
            refine (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _ |>.trans ?_)
            rw [norm_neg]
        _ ≤ (|c| * d + η * d) + η * d + ‖A‖ * d := by
            have := hz.le; linarith
        _ = d * (|c| + 2 * η + ‖A‖) := by ring
        _ ≤ d * R := mul_le_mul_of_nonneg_left (by rw [hR]; linarith) hd0.le
    have hzρ : ‖z - p‖ < ρ₂ := by
      calc ‖z - p‖ ≤ d * R := hzp
        _ = m₀ / 2 * R := by rw [hdm]
        _ ≤ ρ₂ / (R + 1) / 2 * R := by gcongr
        _ < ρ₂ := by
            rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
    have hGz := hG z hzO hzρ
    have hsplit : ε • (P *ᵥ (A *ᵥ h)) = P *ᵥ (A *ᵥ e - (Φ (p + e) - p)) +
        P *ᵥ (Φ (p + e) - z) + P *ᵥ (z - p) := by
      rw [← Matrix.mulVec_add, ← Matrix.mulVec_add,
        show A *ᵥ e - (Φ (p + e) - p) + (Φ (p + e) - z) + (z - p) = A *ᵥ e by abel,
        he, Matrix.mulVec_smul, Matrix.mulVec_smul]
    have h1 : ‖P *ᵥ (A *ᵥ e - (Φ (p + e) - p))‖ ≤ ‖P‖ * (η * d) := by
      refine (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [norm_sub_rev, show Φ (p + e) - p - A *ᵥ e = Φ (p + e) - p - A *ᵥ e from rfl]
      exact hlin
    have h2 : ‖P *ᵥ (Φ (p + e) - z)‖ ≤ ‖P‖ * (|c| * d + η * d) :=
      (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_left (by linarith [hz.le]) (norm_nonneg _))
    have h3 : ‖P *ᵥ (z - p)‖ ≤ η * (d * R) := hGz.trans (mul_le_mul_of_nonneg_left hzp hη.le)
    have hmain : ε * ‖P *ᵥ (A *ᵥ h)‖ ≤ ε * (‖P‖ * |c| * ‖h‖ + η * Q) := by
      have hnorm : ‖ε • (P *ᵥ (A *ᵥ h))‖ = ε * ‖P *ᵥ (A *ᵥ h)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hε0.le]
      rw [← hnorm, hsplit]
      calc ‖P *ᵥ (A *ᵥ e - (Φ (p + e) - p)) + P *ᵥ (Φ (p + e) - z) + P *ᵥ (z - p)‖
          ≤ ‖P *ᵥ (A *ᵥ e - (Φ (p + e) - p))‖ + ‖P *ᵥ (Φ (p + e) - z)‖ + ‖P *ᵥ (z - p)‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
        _ ≤ ‖P‖ * (η * d) + ‖P‖ * (|c| * d + η * d) + η * (d * R) := by
            linarith
        _ = ε * (‖P‖ * |c| * ‖h‖ + η * Q) := by rw [hd, hQ]; ring
    exact le_of_mul_le_mul_left hmain hε0
  by_contra hcon
  push Not at hcon
  set a := ‖P *ᵥ (A *ᵥ h)‖ - ‖P‖ * |c| * ‖h‖ with ha
  have ha0 : 0 < a := by linarith
  set η := min 1 (a / (2 * (Q + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have h1 := key η hη0 (min_le_left _ _)
  have h2 : η * Q < a := by
    calc η * Q ≤ a / (2 * (Q + 1)) * Q := mul_le_mul_of_nonneg_right (min_le_right _ _) hQ0
      _ < a := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  linarith

/-- **The rate `−log ρ/T` cannot be improved.** Let `x_*` be a nonconstant `T`-periodic orbit of
`ẋ = f(x)` (`f` of class `C¹`, globally Lipschitz), and suppose the orbit attracts the solutions
starting near `p = x_*(0)` at the rate `λ`: for some `δ > 0`, `C`, every solution `x` on
`[0, ∞)` with `‖x(0) − p‖ < δ` satisfies `dist(x(t), x_*(ℝ)) ≤ C e^{−λt} ‖x(0) − p‖`. Then every
eigenvalue of the Poincaré Jacobian `DΠ(p) = sectionMatrix M f(p)` has modulus `≤ e^{−λT}`.
(The flow over `kT` has the derivative `Mᵏ` at `p`; near `p` the orbit is tangent to `f(p)`
(`orbit_tangent`), so the projection `P` along `f(p)` of `Mᵏ h` is bounded by
`‖P‖ |C| e^{−λkT} ‖h‖`, and `DΠ(p)ᵏ⁺¹ = P Mᵏ⁺¹`.) -/
@[tmio T, powerlib_foundation] theorem spectrum_sectionMatrix_le_of_decay (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {lam δ C : ℝ}
    (hδ : 0 < δ)
    (hdec : ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      ‖x 0 - xs 0‖ < δ → ∀ t, 0 ≤ t →
        Metric.infDist (x t) (range xs) ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs 0‖) :
    ∀ μ ∈ spectrum ℂ ((sectionMatrix (monodromy (variationalMatrix f xs) T 0)
      (f (xs 0))).map (algebraMap ℝ ℂ)), ‖μ‖ ≤ Real.exp (-(lam * T)) := by
  set p := xs 0 with hp
  set v := f (xs 0) with hv
  set M := monodromy (variationalMatrix f xs) T 0 with hM
  set S := sectionMatrix M v with hS
  set Pm := sectionMatrix 1 v with hPm
  set q := Real.exp (-(lam * T)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hMv : M *ᵥ v = v := monodromy_mulVec_velocity hf hxs hT hper
  have hcv : v ⬝ᵥ v ≠ 0 := fun h => hne (dotProduct_self_eq_zero.1 h)
  have hPmy : ∀ y, Pm *ᵥ y = y - ((v ⬝ᵥ y) / (v ⬝ᵥ v)) • v := fun y => by
    rw [hPm, sectionMatrix_mulVec, Matrix.one_mulVec]
  have hPmv : Pm *ᵥ v = 0 := by rw [hPmy, div_self hcv, one_smul, sub_self]
  have hSy : ∀ e, S *ᵥ e = Pm *ᵥ (M *ᵥ e) := fun e => by rw [hS, sectionMatrix_mulVec, hPmy]
  have hSk : ∀ k : ℕ, ∀ e, S ^ (k + 1) *ᵥ e = Pm *ᵥ (M ^ (k + 1) *ᵥ e) := by
    intro k
    induction k with
    | zero => intro e; simpa using hSy e
    | succ k ih =>
      intro e
      rw [pow_succ' S, ← Matrix.mulVec_mulVec, ih, hSy, pow_succ' M (k + 1),
        ← Matrix.mulVec_mulVec, hPmy (M ^ (k + 1) *ᵥ e), Matrix.mulVec_sub, Matrix.mulVec_smul,
        hMv, Matrix.mulVec_sub, Matrix.mulVec_smul, hPmv, smul_zero, sub_zero]
  -- the flow over `k` periods and its derivative `Mᵏ`
  set hGc : Continuous (uncurry fun _ : ℝ => f) := hfK.continuous.comp continuous_snd
  set fl := flow (G := fun _ => f) hGc (fun _ => hfK) 0 with hfl
  have hflI : ∀ ξ, IsIntegralCurveOn (fl ξ) (fun _ => f) (Ici 0) :=
    fun ξ => flow_solution hGc (fun _ => hfK) 0 ξ
  have hfl0 : ∀ ξ, fl ξ 0 = ξ := fun ξ => flow_start hGc (fun _ => hfK) 0 ξ
  have hGd : ∀ (t : ℝ) x, DifferentiableAt ℝ ((fun _ : ℝ => f) t) x :=
    fun _ x => (hf.differentiable one_ne_zero) x
  have hD : Continuous fun q : ℝ × (Fin n → ℝ) => fderiv ℝ ((fun _ : ℝ => f) q.1) q.2 :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_snd
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hAc := variationalMatrix_continuous hf hxc
  obtain ⟨MA, hMA⟩ := exists_bound_of_periodic hAc (variationalMatrix_periodic hper) hT
  have hflp : ∀ r, 0 ≤ r → fl p r = xs r := fun r hr =>
    (flow_eq hGc (fun _ => hfK) (ξ := p) (β := xs) rfl
      (fun s _ => (hxs s).hasDerivWithinAt) r ⟨hr, le_rfl⟩).symm
  have hDk : ∀ k : ℕ, HasStrictFDerivAt (fun ξ => fl ξ (k * T))
      (Matrix.toLin' (M ^ k)).toContinuousLinearMap p := fun k => by
    have h := hasStrictFDerivAt_flow hGc hGd hD (fun _ => hfK) (s := 0) (t := k * T)
      (by positivity) (ξ₀ := p) hAc (fun r hr w => by
        rw [variationalMatrix_mulVec]; congr 2; exact (hflp r hr.1).symm)
    have htr := transition_add_nat_mul_period hAc hMA hT.le (variationalMatrix_periodic hper) 0 k
    rw [zero_add] at htr
    rwa [htr] at h
  -- the bound on `P Mᵏ`
  have htan : ∀ η > 0, ∃ ρ > 0, ∀ z ∈ range xs, ‖z - p‖ < ρ → ‖Pm *ᵥ (z - p)‖ ≤ η * ‖z - p‖ :=
    fun η hη => by
      obtain ⟨ρ, hρ, hG⟩ := orbit_tangent hf hxs hT hper hne hPmv hη
      exact ⟨ρ, hρ, fun z ⟨σ, hσ⟩ => hσ ▸ hG σ⟩
  have hB : ∀ (k : ℕ) (h : Fin n → ℝ), ‖Pm *ᵥ (M ^ k *ᵥ h)‖ ≤ ‖Pm‖ * |C| * q ^ k * ‖h‖ := by
    intro k h
    have hqk : Real.exp (-(lam * (k * T))) = q ^ k := by
      rw [hq, ← Real.exp_nat_mul]; ring_nf
    have hflpk : fl p (k * T) = p := by rw [hflp _ (by positivity)]; exact hper.nat_mul_eq k
    have h1 := norm_mulVec_le_of_infDist (range_nonempty xs) (hDk k).hasFDerivAt hflpk hδ
      (c := C * q ^ k) (fun ξ hξ => by
        have h2 := hdec (fl ξ) (hflI ξ) (by rwa [hfl0]) (k * T) (by positivity)
        rwa [hfl0, hqk] at h2) htan h
    rwa [abs_mul, abs_of_pos (pow_pos hq0 k), ← mul_assoc] at h1
  -- the eigenvalues
  have hnorm : ∀ k : ℕ, ‖S ^ (k + 1)‖ ≤ ‖Pm‖ * |C| * q ^ (k + 1) := fun k => by
    rw [Matrix.linfty_opNorm_eq_opNorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    have h := hB (k + 1) y
    rw [← hSk] at h
    simpa using h
  intro μ hμ
  obtain ⟨w, hw, hSw⟩ := LTI.mem_spectrum_iff_exists_eigvec.1 hμ
  have hpow : ∀ j : ℕ, (S.map (algebraMap ℝ ℂ)) ^ j *ᵥ w = μ ^ j • w := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hSw, smul_smul, pow_succ,
        mul_comm]
  have hmap : ∀ j : ℕ, (S ^ j).map (algebraMap ℝ ℂ) = (S.map (algebraMap ℝ ℂ)) ^ j := fun j => by
    have h := map_pow ((algebraMap ℝ ℂ).mapMatrix (m := Fin n)) S j
    simpa [RingHom.mapMatrix_apply] using h
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hμk : ∀ k : ℕ, ‖μ‖ ^ (k + 1) ≤ ‖Pm‖ * |C| * q ^ (k + 1) := fun k => by
    have h1 : ‖μ‖ ^ (k + 1) * ‖w‖ ≤ ‖S ^ (k + 1)‖ * ‖w‖ := by
      calc ‖μ‖ ^ (k + 1) * ‖w‖ = ‖μ ^ (k + 1) • w‖ := by rw [norm_smul, norm_pow]
        _ = ‖(S ^ (k + 1)).map (algebraMap ℝ ℂ) *ᵥ w‖ := by rw [hmap, hpow]
        _ ≤ ‖(S ^ (k + 1)).map (algebraMap ℝ ℂ)‖ * ‖w‖ := Matrix.linfty_opNorm_mulVec _ _
        _ = ‖S ^ (k + 1)‖ * ‖w‖ := by rw [LTI.norm_map_algebraMap]
    exact (le_of_mul_le_mul_right h1 hw0).trans (hnorm k)
  by_contra hcon
  push Not at hcon
  set r := ‖μ‖ / q with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hq0, one_mul]; exact hcon
  obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_gt_atTop
    (‖Pm‖ * |C|)).exists
  have h1 := hμk j
  have h2 : r ^ (j + 1) * q ^ (j + 1) = ‖μ‖ ^ (j + 1) := by
    rw [← mul_pow, hr, div_mul_cancel₀ _ hq0.ne']
  have h3 : r ^ j ≤ r ^ (j + 1) := pow_le_pow_right₀ hr1.le (Nat.le_succ j)
  have h4 : ‖Pm‖ * |C| * q ^ (j + 1) < r ^ (j + 1) * q ^ (j + 1) :=
    mul_lt_mul_of_pos_right (hj.trans_le h3) (by positivity)
  linarith


/-- **Orbital decay at a positive rate forces the multipliers.** Under the decay hypothesis of
`spectrum_sectionMatrix_le_of_decay` with `λ > 0`, the trivial multiplier `1` is a simple root of
`χ_M` and every other multiplier has modulus `≤ e^{−λT}`. With `andronov_witt_rate`: the
supremum of the rates `λ` at which the orbit attracts is `−log ρ/T`, `ρ` the largest modulus of a
nontrivial multiplier (every smaller rate is attained, no larger one). -/
@[tmio T, powerlib_foundation] theorem multipliers_le_of_decay (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {lam δ C : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ)
    (hdec : ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      ‖x 0 - xs 0‖ < δ → ∀ t, 0 ≤ t →
        Metric.infDist (x t) (range xs) ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs 0‖) :
    (monodromy (variationalMatrix f xs) T 0).charpoly.rootMultiplicity 1 = 1 ∧
      ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix f xs) T 0).map (algebraMap ℝ ℂ)),
        μ ≠ 1 → ‖μ‖ ≤ Real.exp (-(lam * T)) := by
  have hS := spectrum_sectionMatrix_le_of_decay hf hfK hxs hT hper hne hδ hdec
  have hMv := monodromy_mulVec_velocity hf hxs hT hper
  have hw := sectionVec_dotProduct hMv hne
  have hq1 : Real.exp (-(lam * T)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have hSchur : LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0)
      (f (xs 0))) := fun μ z hz hSz =>
    (hS μ (LTI.mem_spectrum_iff_exists_eigvec.2 ⟨z, hz, hSz⟩)).trans_lt hq1
  refine ⟨((schurStable_sectionMatrix_iff hMv hne hw).2.1 hSchur).1, fun μ hμ hμ1 => ?_⟩
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simpa using (Real.exp_pos _).le
  · exact hS μ ((mem_spectrum_deflate_iff hMv hw hμ0 hμ1).2 hμ)

/-! ## The spectral radius -/

/-- **The spectral-radius form of the rate hypothesis.** For `q > 0`, the spectral radius of a
real matrix (of its complexification) is `< q` exactly when every eigenvalue has modulus `< q`;
so `λ < −log ρ(DΠ(p))/T` is the hypothesis `∀ μ, ‖μ‖ < e^{−λT}` of `asymptoticPhase_rate`. -/
@[tmio T, powerlib_foundation] theorem spectralRadius_lt_ofReal_iff
    (A : Matrix (Fin n) (Fin n) ℝ) {q : ℝ} (hq : 0 < q) :
    spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) < ENNReal.ofReal q ↔
      ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), ‖μ‖ < q := by
  have hq' : ENNReal.ofReal q = ((Real.toNNReal q : NNReal) : ENNReal) := rfl
  constructor
  · intro h μ hμ
    have hle : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) =>
        (‖k‖₊ : ENNReal)) μ hμ
    have hlt := hle.trans_lt h
    rw [hq', ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm,
      Real.coe_toNNReal _ hq.le] at hlt
    exact hlt
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Subsingleton.elim (A.map (algebraMap ℝ ℂ)) 0, spectrum.spectralRadius_zero]
      exact ENNReal.ofReal_pos.2 hq
    · have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
      rw [hq']
      apply spectrum.spectralRadius_lt_of_forall_lt
      intro z hz
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.coe_toNNReal _ hq.le]
      exact h z hz

/-- **The spectral-radius form of the optimality.** For `q ≥ 0`, the spectral radius of a real
matrix is `≤ q` exactly when every eigenvalue has modulus `≤ q`; so
`spectrum_sectionMatrix_le_of_decay` says `ρ(DΠ(p)) ≤ e^{−λT}`, i.e. `λ ≤ −log ρ/T`. -/
@[tmio T, powerlib_foundation] theorem spectralRadius_le_ofReal_iff
    (A : Matrix (Fin n) (Fin n) ℝ) {q : ℝ} (hq : 0 ≤ q) :
    spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) ≤ ENNReal.ofReal q ↔
      ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), ‖μ‖ ≤ q := by
  have hq' : ENNReal.ofReal q = ((Real.toNNReal q : NNReal) : ENNReal) := rfl
  rw [spectralRadius_eq_of_unital, iSup₂_le_iff]
  refine forall₂_congr fun μ _ => ?_
  rw [hq', ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hq]

end powerlib.Periodic.AndronovWittRate
