import theorem.LTI.Discrete
import theorem.Map.Basic
import theorem.Port.Defs

/-! # Linearization of maps

The first theorems of the map semantics: a map whose Jacobian at a fixed point is Schur stable is
locally exponentially stable there, and a map whose Jacobian has every eigenvalue outside the
closed unit disk is unstable there. Only differentiability at the fixed point is needed.

Scope. Maps `F : ℝⁿ → ℝⁿ` differentiable at a fixed point; Schur stability of a real matrix as in
`theorem/LTI/Discrete.lean`; operator norms on `ℝⁿ = EuclideanSpace ℝ (Fin n)`; no model.

Source: the map semantics (`theorem/Map/Defs.lean`); work-sync `theory/T-numerical-integration.md`
§2.7 (the discrete recursion `x_{k+1} = R(hA) x_k`).

Results.
* `pow_bound_toEuclideanCLM`, `exists_pow_norm_toEuclideanCLM_lt_one`: Schur stability of `A`
  gives `‖A^k‖ ≤ C ρ^k` as operators on `ℝⁿ` (`LTI.SchurStable.exists_pow_bound`), hence a power
  of norm below one.
* `locallyExponentiallyStable_of_pow_norm_lt_one`: a map differentiable at a fixed point whose
  derivative has a contractive power is locally exponentially stable (abstract form; the
  contraction of one block of steps is spread over the steps by `LTI.exp_neg_pow_div_le`).
* `locallyExponentiallyStable_of_schurStable` (main): `HasFDerivAt F A x`, `F x = x`, `A` Schur
  ⇒ `Map.LocallyExponentiallyStable F x`; `holds_locallyExponentiallyStable` reads it for the
  zero-input map of a discrete system.
* `globallyExponentiallyStable_of_schurStable`: the linear map of a Schur matrix is globally
  exponentially stable at the origin.
* `unstable_of_expanding`, `unstable_of_inverse_schurStable`, `holds_unstable`: a Jacobian with a
  Schur stable left inverse (every eigenvalue outside the closed unit disk) gives instability
  (`n > 0`).
  Instability from a single Jacobian eigenvalue outside the unit circle is not proved here; it
  needs a spectral splitting with adapted norms (for the linear map itself it is
  `Map.unstable_op_of_eigenvalue`, `theorem/Map/LinearReading.lean`). -/

noncomputable section

namespace powerlib.Map

open Filter Topology Matrix

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The operator of a matrix on `ℝⁿ`. -/
abbrev op (A : Matrix (Fin n) (Fin n) ℝ) : ℝⁿ →L[ℝ] ℝⁿ := Matrix.toEuclideanCLM (𝕜 := ℝ) A

open scoped Matrix.Norms.Operator in
/-- Schur stability gives a geometric bound on the operator norms of the powers (the matrix bound
`LTI.SchurStable.exists_pow_bound` read through the coordinate equivalence of `ℝⁿ`). -/
@[powerlib_foundation] theorem pow_bound_toEuclideanCLM {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LTI.SchurStable A) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖op A ^ k‖ ≤ C * ρ ^ k := by
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := hA.exists_pow_bound
  let e₁ : ℝⁿ →L[ℝ] (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ : ℝⁿ →L[ℝ] (Fin n → ℝ))
  let e₂ : (Fin n → ℝ) →L[ℝ] ℝⁿ :=
    ((EuclideanSpace.equiv (Fin n) ℝ).symm : (Fin n → ℝ) →L[ℝ] ℝⁿ)
  refine ⟨‖e₂‖ * C * ‖e₁‖, ρ, by positivity, hρ0.le, hρ1, fun k => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hw : (op A ^ k) w = e₂ ((A ^ k) *ᵥ e₁ w) := by
    rw [op, ← map_pow]
    rfl
  calc ‖(op A ^ k) w‖ = ‖e₂ ((A ^ k) *ᵥ e₁ w)‖ := by rw [hw]
    _ ≤ ‖e₂‖ * (‖A ^ k‖ * ‖e₁ w‖) :=
        (e₂.le_opNorm _).trans (by gcongr; exact Matrix.linfty_opNorm_mulVec _ _)
    _ ≤ ‖e₂‖ * (C * ρ ^ k * (‖e₁‖ * ‖w‖)) := by gcongr; exacts [hb k, e₁.le_opNorm w]
    _ = ‖e₂‖ * C * ‖e₁‖ * ρ ^ k * ‖w‖ := by ring

/-- Schur stability gives a power of operator norm below one. -/
@[powerlib_foundation] theorem exists_pow_norm_toEuclideanCLM_lt_one
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LTI.SchurStable A) :
    ∃ m : ℕ, 0 < m ∧ ‖op A ^ m‖ < 1 := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := pow_bound_toEuclideanCLM hA
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
  obtain ⟨m, hm1, hm0⟩ :=
    ((hlim.eventually (gt_mem_nhds one_pos)).and (eventually_gt_atTop 0)).exists
  exact ⟨m, hm0, (hb m).trans_lt hm1⟩

/-- Near a fixed point, a map differentiable there is bounded by its derivative plus `ε`. -/
@[powerlib_foundation] theorem eventually_norm_sub_le {G : ℝⁿ → ℝⁿ} {L : ℝⁿ →L[ℝ] ℝⁿ}
    {x : ℝⁿ} (hG : HasFDerivAt G L x) (hx : G x = x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ‖G y - x‖ ≤ (‖L‖ + ε) * ‖y - x‖ := by
  filter_upwards [hG.isLittleO.def hε] with y hy
  rw [hx] at hy
  calc ‖G y - x‖ = ‖(G y - x - L (y - x)) + L (y - x)‖ := by congr 1; abel
    _ ≤ ‖G y - x - L (y - x)‖ + ‖L (y - x)‖ := norm_add_le _ _
    _ ≤ ε * ‖y - x‖ + ‖L‖ * ‖y - x‖ := add_le_add hy (L.le_opNorm _)
    _ = (‖L‖ + ε) * ‖y - x‖ := by ring

/-- A map differentiable at a fixed point, whose derivative has a power of norm below one, is
locally exponentially stable there. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_pow_norm_lt_one {F : ℝⁿ → ℝⁿ}
    {L : ℝⁿ →L[ℝ] ℝⁿ} {x : ℝⁿ} (hF : HasFDerivAt F L x) (hx : F x = x) {m : ℕ} (hm : 0 < m)
    (hL : ‖L ^ m‖ < 1) : LocallyExponentiallyStable F x := by
  set q : ℝ := (‖L ^ m‖ + 1) / 2 with hq
  have hq0 : 0 < q := by have := norm_nonneg (L ^ m); rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  set K : ℝ := 1 + ∑ j ∈ Finset.range m, (‖L ^ j‖ + 1) with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ j ∈ Finset.range m, (‖L ^ j‖ + 1) :=
      Finset.sum_nonneg fun j _ => by positivity
    linarith
  -- one block of `m` steps contracts by `q` near `x`
  have hcon : ∀ᶠ y in 𝓝 x, ‖F^[m] y - x‖ ≤ q * ‖y - x‖ := by
    have hε : 0 < (1 - ‖L ^ m‖) / 2 := by linarith
    filter_upwards [eventually_norm_sub_le (hF.iterate hx m) (Function.iterate_fixed hx m) hε]
      with y hy
    calc ‖F^[m] y - x‖ ≤ (‖L ^ m‖ + (1 - ‖L ^ m‖) / 2) * ‖y - x‖ := hy
      _ = q * ‖y - x‖ := by rw [hq]; ring
  -- fewer than `m` steps grow by at most `K` near `x`
  have hbd : ∀ᶠ y in 𝓝 x, ∀ j : Fin m, ‖F^[j] y - x‖ ≤ K * ‖y - x‖ := by
    rw [Filter.eventually_all]
    intro j
    filter_upwards [eventually_norm_sub_le (hF.iterate hx j) (Function.iterate_fixed hx j)
      one_pos] with y hy
    refine hy.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ‖L ^ (j : ℕ)‖ + 1 ≤ ∑ i ∈ Finset.range m, (‖L ^ i‖ + 1) :=
      Finset.single_le_sum (f := fun i => ‖L ^ i‖ + 1) (fun i _ => by positivity)
        (Finset.mem_range.mpr j.isLt)
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hcon.and hbd)
  -- `q = e^{−γ}`; a block of `m` steps contracts by `e^{−γ}`, one step by `e^{−γ/m}`
  set γ : ℝ := -Real.log q with hγ
  have hγ0 : 0 < γ := neg_pos.mpr (Real.log_neg hq0 hq1)
  have hqγ : Real.exp (-γ) = q := by rw [hγ, neg_neg, Real.exp_log hq0]
  refine ⟨r, K * Real.exp γ, Real.exp (-(γ / m)), hr,
    one_le_mul_of_one_le_of_one_le hK1 (Real.one_le_exp hγ0.le), (Real.exp_pos _).le,
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hγ0 (Nat.cast_pos.mpr hm))),
    fun y hy k => ?_⟩
  -- the orbit at multiples of `m`
  have hmul : ∀ i : ℕ, ‖F^[m * i] y - x‖ ≤ q ^ i * ‖y - x‖ ∧ dist (F^[m * i] y) x < r := by
    intro i
    induction i with
    | zero => simpa [dist_eq_norm] using hy
    | succ i ih =>
      have hstep := (hball ih.2).1
      have hle : ‖F^[m * (i + 1)] y - x‖ ≤ q ^ (i + 1) * ‖y - x‖ := by
        rw [show m * (i + 1) = m + m * i by ring, Function.iterate_add_apply]
        calc ‖F^[m] (F^[m * i] y) - x‖ ≤ q * ‖F^[m * i] y - x‖ := hstep
          _ ≤ q * (q ^ i * ‖y - x‖) := by gcongr; exact ih.1
          _ = q ^ (i + 1) * ‖y - x‖ := by ring
      refine ⟨hle, ?_⟩
      rw [dist_eq_norm]
      calc ‖F^[m * (i + 1)] y - x‖ ≤ q ^ (i + 1) * ‖y - x‖ := hle
        _ ≤ 1 * ‖y - x‖ := by gcongr; exact pow_le_one₀ hq0.le hq1.le
        _ < r := by simpa [dist_eq_norm] using hy
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < m ∧ k = j + m * i :=
    ⟨k / m, k % m, Nat.mod_lt k hm, (Nat.mod_add_div k m).symm⟩
  have h1 : ‖F^[j + m * i] y - x‖ ≤ K * (q ^ i * ‖y - x‖) := by
    rw [Function.iterate_add_apply]
    calc ‖F^[j] (F^[m * i] y) - x‖ ≤ K * ‖F^[m * i] y - x‖ := (hball (hmul i).2).2 ⟨j, hj⟩
      _ ≤ K * (q ^ i * ‖y - x‖) := by gcongr; exact (hmul i).1
  have h2 : q ^ i ≤ Real.exp γ * Real.exp (-(γ / m)) ^ (j + m * i) := by
    have := LTI.exp_neg_pow_div_le hγ0.le hm (j + m * i)
    rwa [hqγ, Nat.add_mul_div_left j i hm, Nat.div_eq_of_lt hj, zero_add] at this
  calc ‖F^[j + m * i] y - x‖ ≤ K * (q ^ i * ‖y - x‖) := h1
    _ ≤ K * (Real.exp γ * Real.exp (-(γ / m)) ^ (j + m * i) * ‖y - x‖) := by gcongr
    _ = K * Real.exp γ * Real.exp (-(γ / m)) ^ (j + m * i) * ‖y - x‖ := by ring

/-- **Linearization of maps.** A map with a fixed point `x`, differentiable at `x` with a Schur
stable Jacobian matrix `A`, is locally exponentially stable at `x`. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_schurStable {F : ℝⁿ → ℝⁿ}
    {A : Matrix (Fin n) (Fin n) ℝ} {x : ℝⁿ} (hF : HasFDerivAt F (op A) x) (hx : F x = x)
    (hA : LTI.SchurStable A) : LocallyExponentiallyStable F x := by
  obtain ⟨m, hm, hlt⟩ := exists_pow_norm_toEuclideanCLM_lt_one hA
  exact locallyExponentiallyStable_of_pow_norm_lt_one hF hx hm hlt

/-- The same with the sentence interpretation: local exponential stability holds for a discrete
system whose zero-input map has a Schur Jacobian at the origin. -/
@[powerlib_foundation] theorem holds_locallyExponentiallyStable {p : ℕ} {s : System n p}
    {A : Matrix (Fin n) (Fin n) ℝ} (hF : HasFDerivAt s.zeroInput (op A) 0)
    (hx : s.zeroInput 0 = 0) (hA : LTI.SchurStable A) :
    (Sentence.flow .locallyExponentiallyStable).holds (Behaviour.discrete s) :=
  locallyExponentiallyStable_of_schurStable hF hx hA

/-- The linear map of a Schur matrix is globally exponentially stable at the origin. -/
@[powerlib_foundation] theorem globallyExponentiallyStable_of_schurStable
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LTI.SchurStable A) :
    GloballyExponentiallyStable (op A) 0 := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := pow_bound_toEuclideanCLM hA
  refine ⟨map_zero _, max C 1, ρ, le_max_right _ _, hρ0, hρ1, fun y k => ?_⟩
  rw [sub_zero, sub_zero, ← FunLike.coe_pow_eq_iterate]
  calc ‖(op A ^ k) y‖ ≤ ‖op A ^ k‖ * ‖y‖ := (op A ^ k).le_opNorm y
    _ ≤ C * ρ ^ k * ‖y‖ := by gcongr; exact hb k
    _ ≤ max C 1 * ρ ^ k * ‖y‖ := by gcongr; exact le_max_left _ _

/-! ## Repelling fixed points -/

/-- Near a fixed point, a map differentiable there is bounded below by its derivative minus `ε`. -/
@[powerlib_foundation] theorem eventually_norm_sub_ge {G : ℝⁿ → ℝⁿ} {L : ℝⁿ →L[ℝ] ℝⁿ}
    {x : ℝⁿ} (hG : HasFDerivAt G L x) (hx : G x = x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ‖L (y - x)‖ - ε * ‖y - x‖ ≤ ‖G y - x‖ := by
  filter_upwards [hG.isLittleO.def hε] with y hy
  rw [hx] at hy
  have : ‖L (y - x)‖ ≤ ‖G y - x‖ + ‖G y - x - L (y - x)‖ := by
    calc ‖L (y - x)‖ = ‖(G y - x) - (G y - x - L (y - x))‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- A map differentiable at a fixed point whose derivative has an expanding power is unstable. -/
@[powerlib_foundation] theorem unstable_of_expanding {F : ℝⁿ → ℝⁿ} {L : ℝⁿ →L[ℝ] ℝⁿ}
    {x : ℝⁿ} (hF : HasFDerivAt F L x) (hx : F x = x) {m : ℕ} {q : ℝ} (hq1 : q < 1)
    (hexp : ∀ v, ‖v‖ ≤ q * ‖(L ^ m) v‖) (hn : 0 < n) : Unstable F x := by
  set q₁ : ℝ := max q (1 / 2) with hq₁
  have hq₁0 : 0 < q₁ := lt_max_of_lt_right (by norm_num)
  have hq₁1 : q₁ < 1 := max_lt hq1 (by norm_num)
  have hexp₁ : ∀ v, ‖v‖ / q₁ ≤ ‖(L ^ m) v‖ := fun v => by
    rw [div_le_iff₀ hq₁0]
    calc ‖v‖ ≤ q * ‖(L ^ m) v‖ := hexp v
      _ ≤ q₁ * ‖(L ^ m) v‖ := by gcongr; exact le_max_left _ _
      _ = ‖(L ^ m) v‖ * q₁ := mul_comm _ _
  have hinv : 1 < 1 / q₁ := by rw [lt_div_iff₀ hq₁0]; linarith
  set ε : ℝ := (1 / q₁ - 1) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set l : ℝ := 1 + ε with hl
  have hl1 : 1 < l := by linarith
  have hgrow : ∀ᶠ y in 𝓝 x, l * ‖y - x‖ ≤ ‖F^[m] y - x‖ := by
    filter_upwards [eventually_norm_sub_ge (hF.iterate hx m) (Function.iterate_fixed hx m) hε]
      with y hy
    have h1 := hexp₁ (y - x)
    have h2 : l * ‖y - x‖ = 1 / q₁ * ‖y - x‖ - ε * ‖y - x‖ := by rw [hl, hε_def]; ring
    have h3 : 1 / q₁ * ‖y - x‖ = ‖y - x‖ / q₁ := by ring
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hgrow
  intro hstab
  obtain ⟨δ, hδ, hb⟩ := hstab r hr
  set t : ℝ := min δ r / 2 with ht
  have ht0 : 0 < t := by rw [ht]; exact half_pos (lt_min hδ hr)
  have htδ : t < δ := by
    rw [ht]; linarith [min_le_left δ r, half_lt_self (lt_min hδ hr)]
  let e : ℝⁿ := EuclideanSpace.single ⟨0, hn⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  set y : ℝⁿ := x + t • e with hy_def
  have hy : ‖y - x‖ = t := by
    rw [hy_def, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
  have hin : ∀ k, ‖F^[k] y - x‖ < r := hb y (by rw [hy]; exact htδ)
  have hpow : ∀ i : ℕ, l ^ i * t ≤ ‖F^[m * i] y - x‖ := by
    intro i
    induction i with
    | zero => simp [hy]
    | succ i ih =>
      rw [show m * (i + 1) = m + m * i by ring, Function.iterate_add_apply]
      have h := hball (show dist (F^[m * i] y) x < r by rw [dist_eq_norm]; exact hin _)
      calc l ^ (i + 1) * t = l * (l ^ i * t) := by ring
        _ ≤ l * ‖F^[m * i] y - x‖ := by gcongr
        _ ≤ ‖F^[m] (F^[m * i] y) - x‖ := h
  obtain ⟨i, hi⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hl1).eventually_ge_atTop (r / t)).exists
  have h1 := hpow i
  have h2 := hin (m * i)
  have h3 : r ≤ l ^ i * t := by rw [div_le_iff₀ ht0] at hi; exact hi
  linarith

/-- **Repelling fixed points.** A map with a fixed point `x`, differentiable at `x` with a Jacobian
matrix `A` that has a Schur stable left inverse `B` (every eigenvalue of `A` outside the closed unit
disk), is unstable at `x` (`n > 0`). -/
@[powerlib_foundation] theorem unstable_of_inverse_schurStable {F : ℝⁿ → ℝⁿ}
    {A B : Matrix (Fin n) (Fin n) ℝ} {x : ℝⁿ} (hF : HasFDerivAt F (op A) x) (hx : F x = x)
    (hBA : B * A = 1) (hB : LTI.SchurStable B) (hn : 0 < n) : Unstable F x := by
  obtain ⟨m, -, hlt⟩ := exists_pow_norm_toEuclideanCLM_lt_one hB
  refine unstable_of_expanding hF hx hlt (m := m) (fun v => ?_) hn
  have hpow : ∀ k : ℕ, B ^ k * A ^ k = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc B ^ (k + 1) * A ^ (k + 1) = B ^ k * (B * A) * A ^ k := by
            rw [pow_succ, pow_succ']; simp only [mul_assoc]
        _ = 1 := by rw [hBA, mul_one, ih]
  have hop : op B ^ m * op A ^ m = 1 := by
    rw [op, op, ← map_pow, ← map_pow, ← map_mul, hpow m, map_one]
  have hinv : (op B ^ m) ((op A ^ m) v) = v := by
    calc (op B ^ m) ((op A ^ m) v) = (op B ^ m * op A ^ m) v := rfl
      _ = v := by rw [hop]; rfl
  calc ‖v‖ = ‖(op B ^ m) ((op A ^ m) v)‖ := by rw [hinv]
    _ ≤ ‖op B ^ m‖ * ‖(op A ^ m) v‖ := (op B ^ m).le_opNorm _

/-- The same with the sentence interpretation. -/
@[powerlib_foundation] theorem holds_unstable {p : ℕ} {s : System n p}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hF : HasFDerivAt s.zeroInput (op A) 0)
    (hx : s.zeroInput 0 = 0) (hBA : B * A = 1) (hB : LTI.SchurStable B) (hn : 0 < n) :
    (Sentence.flow .unstable).holds (Behaviour.discrete s) :=
  unstable_of_inverse_schurStable hF hx hBA hB hn

end powerlib.Map
