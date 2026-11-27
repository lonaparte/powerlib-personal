import theorem.Periodic.PoincareSection
import theorem.Periodic.FlipOrbitUniform
import theorem.Periodic.OrbitalInstability

/-! # Andronov–Witt (draft)

Scope.
* draft

Source: draft.

Results.
* draft
-/

noncomputable section
namespace powerlib.Periodic.AndronovWitt

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative FlipOrbit PoincareSection

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Iterates of the Poincaré map are the solution at the accumulated return times -/

/-- **The orbit of the Poincaré map is the solution sampled at the return times.** If the return
times of the first `k` iterates are nonnegative, `Πᵏ(x(0)) = x(t_k)` with
`t_k = τ(x(0)) + τ(Π(x(0))) + ⋯ + τ(Π^{k−1}(x(0)))`, for every solution `x` on `[0, ∞)`. -/
@[tmio T, powerlib_foundation] theorem iterate_poincareMap (hfK : LipschitzWith K f)
    (τ : (Fin n → ℝ) → ℝ) {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    (k : ℕ) (hτ : ∀ j < k, 0 ≤ τ ((poincareMap hfK τ)^[j] (x 0))) :
    (poincareMap hfK τ)^[k] (x 0) =
      x (∑ j ∈ Finset.range k, τ ((poincareMap hfK τ)^[j] (x 0))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j hj => hτ j (Nat.lt_succ_of_lt hj))
    set tk := ∑ j ∈ Finset.range k, τ ((poincareMap hfK τ)^[j] (x 0)) with htk
    have htk0 : 0 ≤ tk :=
      Finset.sum_nonneg fun j hj => hτ j (Nat.lt_succ_of_lt (Finset.mem_range.1 hj))
    have hy : IsIntegralCurveOn (fun r => x (r + tk)) (fun _ => f) (Ici 0) :=
      (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
        (Ici_subset_Ici.2 (by linarith))
    have hy0 : x (0 + tk) = (poincareMap hfK τ)^[k] (x 0) := by
      rw [zero_add]; exact ih'.symm
    have hτk := hτ k (Nat.lt_succ_self k)
    have h := poincareMap_eq hfK τ hy (by rw [hy0]; exact hτk)
    rw [hy0] at h
    rw [Function.iterate_succ_apply', Finset.sum_range_succ, h, add_comm]

/-! ## Local exponential stability of a map, in the sup norm -/

/-- A map of `Fin n → ℝ` with fixed point `p` and Schur stable strict derivative `A` there is
locally exponentially stable in the sup norm (`Map.locallyExponentiallyStable_of_schurStable`,
read through `euclidMap`), with a rate `0 < q < 1`. -/
@[tmio T, powerlib_foundation] private theorem exp_stable_coord {F : (Fin n → ℝ) → Fin n → ℝ}
    {p : Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hF : HasStrictFDerivAt F (Matrix.toLin' A).toContinuousLinearMap p) (hFp : F p = p)
    (hA : LTI.SchurStable A) :
    ∃ r C q : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < q ∧ q < 1 ∧
      ∀ ξ, ‖ξ - p‖ < r → ∀ k : ℕ, ‖F^[k] ξ - p‖ ≤ C * q ^ k * ‖ξ - p‖ := by
  set ε := EuclideanSpace.equiv (Fin n) ℝ with hε
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (ε : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  have h1 : HasStrictFDerivAt F (Matrix.toLin' A).toContinuousLinearMap (ε (ε.symm p)) := by
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have h := (ε.symm.hasStrictFDerivAt (x := F (ε (ε.symm p)))).comp (ε.symm p)
    (h1.comp (ε.symm p) ε.hasStrictFDerivAt)
  have hfun : euclidMap F = fun x => ε.symm (F (ε x)) := rfl
  have hM : Linear.op A = (ε.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ).comp
      ((Matrix.toLin' A).toContinuousLinearMap.comp (ε : ℝⁿ →L[ℝ] (Fin n → ℝ))) := by
    ext1 y; rfl
  have hE : HasStrictFDerivAt (euclidMap F) (Linear.op A) (ε.symm p) := by
    rw [hfun, hM]; exact h
  have hEp : euclidMap F (ε.symm p) = ε.symm p := by
    show ε.symm (F (ε (ε.symm p))) = ε.symm p
    rw [ContinuousLinearEquiv.apply_symm_apply, hFp]
  obtain ⟨r, C, q, hr, hC, hq0, hq1, hb⟩ :=
    Map.locallyExponentiallyStable_of_schurStable hE.hasFDerivAt hEp hA
  set q' := max q (1 / 2) with hq'
  have hq'0 : 0 < q' := lt_max_of_lt_right (by norm_num)
  have hq'1 : q' < 1 := max_lt hq1 (by norm_num)
  refine ⟨r / (‖εS‖ + 1), ‖εL‖ * C * ‖εS‖ + 1, q', by positivity,
    le_add_of_nonneg_left (by positivity), hq'0, hq'1, fun ξ hξ k => ?_⟩
  have hξE : ‖ε.symm ξ - ε.symm p‖ < r := by
    rw [← map_sub]
    calc ‖ε.symm (ξ - p)‖ ≤ ‖εS‖ * ‖ξ - p‖ := εS.le_opNorm _
      _ ≤ (‖εS‖ + 1) * ‖ξ - p‖ := by nlinarith [norm_nonneg (ξ - p)]
      _ < r := by rwa [lt_div_iff₀' (by positivity)] at hξ
  have hk := hb (ε.symm ξ) hξE k
  rw [iterate_euclidMap, ContinuousLinearEquiv.apply_symm_apply, ← map_sub] at hk
  rw [← map_sub] at hk
  have hqk : q ^ k ≤ q' ^ k := pow_le_pow_left₀ hq0 (le_max_left _ _) k
  calc ‖F^[k] ξ - p‖ = ‖ε (ε.symm (F^[k] ξ - p))‖ := by
        rw [ContinuousLinearEquiv.apply_symm_apply]
    _ ≤ ‖εL‖ * ‖ε.symm (F^[k] ξ - p)‖ := εL.le_opNorm _
    _ ≤ ‖εL‖ * (C * q ^ k * ‖ε.symm (ξ - p)‖) := by gcongr
    _ ≤ ‖εL‖ * (C * q' ^ k * (‖εS‖ * ‖ξ - p‖)) := by
        have hC0 : (0 : ℝ) ≤ C := by linarith
        have h2 : C * q ^ k ≤ C * q' ^ k := mul_le_mul_of_nonneg_left hqk hC0
        have h3 : ‖ε.symm (ξ - p)‖ ≤ ‖εS‖ * ‖ξ - p‖ := εS.le_opNorm _
        have h4 : C * q ^ k * ‖ε.symm (ξ - p)‖ ≤ C * q' ^ k * (‖εS‖ * ‖ξ - p‖) :=
          mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ ≤ (‖εL‖ * C * ‖εS‖ + 1) * q' ^ k * ‖ξ - p‖ := by
        have := pow_nonneg hq'0.le k
        have := norm_nonneg (ξ - p)
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg εL) (by linarith : (0 : ℝ) ≤ C))
          (norm_nonneg εS)]

/-! ## Orbital asymptotic stability with asymptotic phase -/

/-- The orbit of a `T`-periodic solution of `ẋ = f(x)` moves with bounded speed:
`‖x_*(a) − x_*(b)‖ ≤ B |a − b|`. -/
@[tmio T, powerlib_foundation] private theorem exists_speed_bound (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b, ‖xs a - xs b‖ ≤ B * |a - b| := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (hfK.continuous.comp hxc).continuousOn
  have hBall : ∀ t, ‖f (xs t)‖ ≤ B := fun t => by
    obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hT t
    rw [hty]
    exact hB y (Ico_subset_Icc_self hy)
  refine ⟨max B 0, le_max_right _ _, fun a b => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
    (fun t _ => (hxs t).hasDerivWithinAt) (fun t _ => (hBall t).trans (le_max_left B 0))
    convex_univ (mem_univ b) (mem_univ a)
  rwa [Real.norm_eq_abs] at h

/-- **Andronov–Witt at the point `x_*(0)`, with asymptotic phase.** Let `x_*` be a nonconstant
`T`-periodic orbit of `ẋ = f(x)` (`f` of class `C¹`, globally Lipschitz) whose Poincaré Jacobian
`sectionMatrix M f(x_*(0))` is Schur stable. Then there are `δ > 0`, `C ≥ 0` and a rate `λ > 0`
such that every solution `x` on `[0, ∞)` with `‖x(0) − x_*(0)‖ < δ` has an asymptotic phase `θ`,
`|θ| ≤ C ‖x(0) − x_*(0)‖`, with
`‖x(t) − x_*(t + θ)‖ ≤ C e^{−λt} ‖x(0) − x_*(0)‖` for all `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_of_section (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (hS : LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)))) :
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs 0‖ < δ →
      ∃ θ : ℝ, |θ| ≤ C * ‖x 0 - xs 0‖ ∧
        ∀ t, 0 ≤ t → ‖x t - xs (t + θ)‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs 0‖ := by
  obtain ⟨τ, hτp, hτD, ⟨r, s, hr, hs, hsT, hsec, -⟩, hPp, hPD, -, -, -, -⟩ :=
    exists_poincareMap hf hfK hxs hT hper hne
  set P := poincareMap hfK τ with hP
  set p := xs 0 with hp
  obtain ⟨r₁, C₁, q, hr₁, hC₁, hq0, hq1, hexp⟩ := exp_stable_coord hPD hPp hS
  -- the return time is Lipschitz at `p`
  obtain ⟨L₀, hL₀⟩ := hτD.hasFDerivAt.isBigO_sub.bound
  obtain ⟨r₂, hr₂, hτL₀⟩ := Metric.eventually_nhds_iff.1 hL₀
  set L := max L₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hτL : ∀ ξ, ‖ξ - p‖ < r₂ → |τ ξ - T| ≤ L * ‖ξ - p‖ := fun ξ hξ => by
    have h := hτL₀ (show dist ξ p < r₂ by rwa [dist_eq_norm])
    rw [Real.norm_eq_abs, hτp] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨B, hB0, hB⟩ := exists_speed_bound hfK hxs hT hper
  -- the constants
  set c₀ := 3 * T / 2 with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set lam := -Real.log q / c₀ with hlam
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hlam0 : 0 < lam := div_pos (by linarith) hc₀0
  have h1q : 0 < 1 - q := by linarith
  set Cθ := L * C₁ / (1 - q) with hCθ
  set Cx := Real.exp (K * c₀) * (C₁ + B * Cθ) / q with hCx
  have hCθ0 : 0 ≤ Cθ := by positivity
  have hCx0 : 0 ≤ Cx := by positivity
  set δ := min r₁ (min r r₂ / C₁) with hδ
  have hC₁0 : 0 < C₁ := by linarith
  have hδ0 : 0 < δ := lt_min hr₁ (div_pos (lt_min hr hr₂) hC₁0)
  refine ⟨δ, max Cθ Cx, lam, hδ0, le_max_of_le_left hCθ0, hlam0, fun x hx hx0 => ?_⟩
  set ξ := x 0 with hξ
  set d := ‖ξ - p‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  -- the iterates stay in the box of the section
  have hy : ∀ k : ℕ, ‖P^[k] ξ - p‖ ≤ C₁ * q ^ k * d := hexp ξ (hx0.trans_le (min_le_left _ _))
  have hy' : ∀ k : ℕ, ‖P^[k] ξ - p‖ < min r r₂ := fun k => by
    have h1 : C₁ * q ^ k * d ≤ C₁ * d := by
      have := pow_le_one₀ hq0.le hq1.le (n := k)
      have : C₁ * q ^ k ≤ C₁ * 1 := mul_le_mul_of_nonneg_left this hC₁0.le
      nlinarith
    have h2 : C₁ * d < min r r₂ := by
      have := hx0.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀' hC₁0] at this
    exact (hy k).trans_lt (h1.trans_lt h2)
  have hτs : ∀ k : ℕ, |τ (P^[k] ξ) - T| < s := fun k =>
    (hsec _ ((hy' k).trans_le (min_le_left _ _))).1
  have hτpos : ∀ k : ℕ, T / 2 ≤ τ (P^[k] ξ) := fun k => by
    have := abs_lt.1 (hτs k); linarith
  have hτup : ∀ k : ℕ, τ (P^[k] ξ) ≤ c₀ := fun k => by
    have := abs_lt.1 (hτs k); rw [hc₀]; linarith
  have hτT : ∀ k : ℕ, |τ (P^[k] ξ) - T| ≤ L * C₁ * d * q ^ k := fun k => by
    refine (hτL _ ((hy' k).trans_le (min_le_right _ _))).trans ?_
    calc L * ‖P^[k] ξ - p‖ ≤ L * (C₁ * q ^ k * d) := mul_le_mul_of_nonneg_left (hy k) hL0
      _ = L * C₁ * d * q ^ k := by ring
  -- the accumulated return times
  set tt : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, τ (P^[j] ξ) with htt
  have htt_iter : ∀ k : ℕ, P^[k] ξ = x (tt k) := fun k =>
    iterate_poincareMap hfK τ hx k fun j _ => le_trans (by linarith) (hτpos j)
  have htt_succ : ∀ k : ℕ, tt (k + 1) = tt k + τ (P^[k] ξ) := fun k =>
    Finset.sum_range_succ _ _
  have htt_ge : ∀ k : ℕ, (k : ℝ) * (T / 2) ≤ tt k := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτpos k]
  have htt_le : ∀ k : ℕ, tt k ≤ k * c₀ := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτup k]
  -- the phase
  set u : ℕ → ℝ := fun j => τ (P^[j] ξ) - T with hu
  have hgeom : HasSum (fun j : ℕ => L * C₁ * d * q ^ j) (L * C₁ * d * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
  have husum : Summable u :=
    Summable.of_norm_bounded hgeom.summable fun j => by rw [Real.norm_eq_abs]; exact hτT j
  set θ' := ∑' j, u j with hθ'
  have htail : ∀ k : ℕ, |tt k - k * T - θ'| ≤ Cθ * d * q ^ k := fun k => by
    have hsplit := husum.sum_add_tsum_nat_add k
    have hsum : tt k - k * T = ∑ j ∈ Finset.range k, u j := by
      simp only [htt, hu, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have he : tt k - k * T - θ' = -∑' j, u (j + k) := by
      rw [hsum, hθ', ← hsplit]; ring
    rw [he, abs_neg]
    have hg : HasSum (fun j : ℕ => L * C₁ * d * q ^ k * q ^ j)
        (L * C₁ * d * q ^ k * (1 - q)⁻¹) :=
      (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
    have hb := tsum_of_norm_bounded hg fun j => by
      rw [Real.norm_eq_abs]
      calc |u (j + k)| ≤ L * C₁ * d * q ^ (j + k) := hτT (j + k)
        _ = L * C₁ * d * q ^ k * q ^ j := by rw [pow_add]; ring
    rw [Real.norm_eq_abs] at hb
    calc |∑' j, u (j + k)| ≤ L * C₁ * d * q ^ k * (1 - q)⁻¹ := hb
      _ = Cθ * d * q ^ k := by rw [hCθ]; field_simp
  refine ⟨-θ', ?_, fun t ht => ?_⟩
  · have h := htail 0
    simp only [htt, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, sub_zero,
      zero_sub, abs_neg, pow_zero, mul_one] at h
    rw [abs_neg]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0)
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
  have hxs' : IsIntegralCurveOn (fun r => xs (r + -θ')) (fun _ => f) (Icc (tt k) t) :=
    fun r _ => ((hxs (r + -θ')).comp_add_const r (-θ')).hasDerivWithinAt
  have htk0 : 0 ≤ tt k := le_trans (by positivity) (htt_ge k)
  have hxI : IsIntegralCurveOn x (fun _ => f) (Icc (tt k) t) :=
    hx.mono fun q hq => mem_Ici.2 (htk0.trans hq.1)
  have hgr := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK) hxI hxs' t ⟨hk0, le_rfl⟩
  rw [dist_eq_norm, dist_eq_norm] at hgr
  -- the deviation at the crossing `t_k`
  have hdev : ‖x (tt k) - xs (tt k + -θ')‖ ≤ (C₁ + B * Cθ) * q ^ k * d := by
    have hpk : xs (k * T) = p := hper.nat_mul_eq k
    calc ‖x (tt k) - xs (tt k + -θ')‖ = ‖(P^[k] ξ - p) + (xs (k * T) - xs (tt k + -θ'))‖ := by
          rw [htt_iter, hpk]; abel_nf
      _ ≤ ‖P^[k] ξ - p‖ + ‖xs (k * T) - xs (tt k + -θ')‖ := norm_add_le _ _
      _ ≤ C₁ * q ^ k * d + B * |k * T - (tt k + -θ')| := add_le_add (hy k) (hB _ _)
      _ = C₁ * q ^ k * d + B * |tt k - k * T - θ'| := by
          rw [abs_sub_comm]; ring_nf
      _ ≤ C₁ * q ^ k * d + B * (Cθ * d * q ^ k) := by gcongr; exact htail k
      _ = (C₁ + B * Cθ) * q ^ k * d := by ring
  -- the rate
  have hqk : q ^ k ≤ Real.exp (-(lam * t)) / q := by
    rw [le_div_iff₀ hq0, ← pow_succ]
    have h1 : t ≤ (k + 1 : ℕ) * c₀ := (hk1.le.trans (htt_le (k + 1)))
    have h2 : Real.exp (-(lam * ((k + 1 : ℕ) * c₀))) = q ^ (k + 1) := by
      rw [hlam, show -(-Real.log q / c₀ * ((k + 1 : ℕ) * c₀)) = (k + 1 : ℕ) * Real.log q by
        field_simp, Real.exp_nat_mul, Real.exp_log hq0]
    rw [← h2]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hgap : t - tt k ≤ c₀ := by
    have := htt_succ k; linarith [hτup k]
  calc ‖x t - xs (t + -θ')‖ ≤ ‖x (tt k) - xs (tt k + -θ')‖ * Real.exp (K * (t - tt k)) := hgr
    _ ≤ (C₁ + B * Cθ) * q ^ k * d * Real.exp (K * c₀) := by
        have he : Real.exp (K * (t - tt k)) ≤ Real.exp (K * c₀) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hgap K.2)
        exact mul_le_mul hdev he (Real.exp_pos _).le (by positivity)
    _ ≤ (C₁ + B * Cθ) * (Real.exp (-(lam * t)) / q) * d * Real.exp (K * c₀) := by gcongr
    _ = Cx * Real.exp (-(lam * t)) * d := by rw [hCx]; field_simp
    _ ≤ max Cθ Cx * Real.exp (-(lam * t)) * d := by gcongr; exact le_max_right _ _

/-- **Andronov–Witt with asymptotic phase, uniformly along the orbit.** Under the hypotheses of
`asymptoticPhase_of_section` there are `δ > 0`, `C ≥ 0` and `λ > 0` such that every solution `x`
on `[0, ∞)` starting within `δ` of any point `x_*(σ)` of the orbit has an asymptotic phase `θ`,
`|θ| ≤ C ‖x(0) − x_*(σ)‖`, with `‖x(t) − x_*(t + σ + θ)‖ ≤ C e^{−λt} ‖x(0) − x_*(σ)‖` for all
`t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (hS : LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)))) :
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ (σ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → ‖x 0 - xs σ‖ < δ →
      ∃ θ : ℝ, |θ| ≤ C * ‖x 0 - xs σ‖ ∧
        ∀ t, 0 ≤ t → ‖x t - xs (t + σ + θ)‖ ≤ C * Real.exp (-(lam * t)) * ‖x 0 - xs σ‖ := by
  obtain ⟨δ₀, C₀, lam, hδ₀, hC₀, hlam, hmain⟩ :=
    asymptoticPhase_of_section hf hfK hxs hT hper hne hS
  obtain ⟨B, hB0, hB⟩ := exists_speed_bound hfK hxs hT hper
  set E := Real.exp (K * T) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg K.2 hT.le)
  have hE0 : 0 < E := by linarith
  set F := Real.exp (lam * T) with hF
  have hF1 : 1 ≤ F := Real.one_le_exp (mul_nonneg hlam.le hT.le)
  set C := max (C₀ * E) ((C₀ + 1 + B * C₀) * E * F) with hC
  refine ⟨δ₀ / E, C, lam, div_pos hδ₀ hE0, le_max_of_le_left (by positivity), hlam,
    fun σ x hx hx0 => ?_⟩
  set d₀ := ‖x 0 - xs σ‖ with hd₀
  have hd0 : 0 ≤ d₀ := norm_nonneg _
  -- the phase of `σ` in `[0, T)`
  set σ' := toIcoMod hT 0 σ with hσ'
  have hσ'I : σ' ∈ Ico 0 T := by simpa using toIcoMod_mem_Ico hT 0 σ
  have hshift : ∀ a, xs (a + σ) = xs (a + σ') := fun a => by
    have h := toIcoMod_add_toIcoDiv_zsmul hT 0 σ
    rw [← h, ← add_assoc]
    exact (hper.zsmul _) _
  set u := T - σ' with hu
  have hu0 : 0 < u := by have := hσ'I.2; linarith
  have huT : u ≤ T := by have := hσ'I.1; linarith
  -- up to the time `u` the solution follows `x_*(· + σ')`
  have hxs' : ∀ a b : ℝ, IsIntegralCurveOn (fun r => xs (r + σ')) (fun _ => f) (Icc a b) :=
    fun _ _ r _ => ((hxs (r + σ')).comp_add_const r σ').hasDerivWithinAt
  have hfollow : ∀ r ∈ Icc 0 u, ‖x r - xs (r + σ')‖ ≤ E * d₀ := fun r hr => by
    have h := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK)
      (hx.mono fun q hq => mem_Ici.2 hq.1) (hxs' 0 u) r hr
    have hσσ' : xs σ = xs σ' := by have := hshift 0; rwa [zero_add, zero_add] at this
    rw [dist_eq_norm, dist_eq_norm, zero_add, ← hσσ', sub_zero] at h
    rw [mul_comm] at h
    refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hd0)
    exact mul_le_mul_of_nonneg_left (hr.2.trans huT) K.2
  have hxu : ‖x u - xs 0‖ ≤ E * d₀ := by
    have h := hfollow u ⟨hu0.le, le_rfl⟩
    rwa [hu, sub_add_cancel, show xs T = xs 0 by simpa using hper 0] at h
  -- from the time `u` on, the phase of `asymptoticPhase_of_section`
  set y : ℝ → Fin n → ℝ := fun r => x (r + u) with hy
  have hyI : IsIntegralCurveOn y (fun _ => f) (Ici 0) :=
    (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
      (Ici_subset_Ici.2 (by linarith))
  have hy0 : ‖y 0 - xs 0‖ < δ₀ := by
    simp only [hy, zero_add]
    calc ‖x u - xs 0‖ ≤ E * d₀ := hxu
      _ < E * (δ₀ / E) := mul_lt_mul_of_pos_left hx0 hE0
      _ = δ₀ := by field_simp
  obtain ⟨θ, hθ, hyθ⟩ := hmain y hyI hy0
  have hy0' : ‖y 0 - xs 0‖ ≤ E * d₀ := by simpa [hy] using hxu
  have hθd : |θ| ≤ C₀ * E * d₀ :=
    hθ.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hy0' hC₀)
  have hθC : |θ| ≤ C * d₀ := hθd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0)
  refine ⟨θ, hθC, fun t ht => ?_⟩
  have hphase : xs (t + σ + θ) = xs (t + θ + σ') := by
    rw [show t + σ + θ = (t + θ) + σ by ring, hshift]
  rw [hphase]
  rcases le_or_gt u t with hut | htu
  · -- after the time `u`
    have h := hyθ (t - u) (by linarith)
    simp only [hy, sub_add_cancel] at h
    have hper' : xs (t - u + θ) = xs (t + θ + σ') := by
      rw [hu, show t - (T - σ') + θ = (t + θ + σ') - T by ring]
      exact hper.sub_eq _
    rw [hper'] at h
    refine h.trans ?_
    have hexp : Real.exp (-(lam * (t - u))) ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc C₀ * Real.exp (-(lam * (t - u))) * ‖y 0 - xs 0‖
        ≤ C₀ * (F * Real.exp (-(lam * t))) * (E * d₀) := by gcongr
      _ = C₀ * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ C * Real.exp (-(lam * t)) * d₀ := by
          gcongr
          rw [hC]
          refine le_max_of_le_right ?_
          have := mul_le_mul_of_nonneg_left hF1 (by positivity : (0 : ℝ) ≤ C₀ * E)
          nlinarith [mul_nonneg (mul_nonneg hB0 hC₀) (by positivity : (0 : ℝ) ≤ E * F),
            mul_nonneg hE0.le (by linarith : (0 : ℝ) ≤ F)]
  · -- before the time `u`
    have h1 := hfollow t ⟨ht, htu.le⟩
    have h2 : ‖xs (t + σ') - xs (t + θ + σ')‖ ≤ B * |θ| := by
      refine (hB _ _).trans_eq ?_
      congr 1
      rw [show t + σ' - (t + θ + σ') = -θ by ring, abs_neg]
    have hexp : 1 ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖x t - xs (t + θ + σ')‖ = ‖(x t - xs (t + σ')) + (xs (t + σ') - xs (t + θ + σ'))‖ := by
          abel_nf
      _ ≤ ‖x t - xs (t + σ')‖ + ‖xs (t + σ') - xs (t + θ + σ')‖ := norm_add_le _ _
      _ ≤ E * d₀ + B * (C₀ * E * d₀) := add_le_add h1 (h2.trans (by gcongr))
      _ = (1 + B * C₀) * E * d₀ * 1 := by ring
      _ ≤ (1 + B * C₀) * E * d₀ * (F * Real.exp (-(lam * t))) := by gcongr
      _ = (1 + B * C₀) * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ C * Real.exp (-(lam * t)) * d₀ := by
          gcongr
          rw [hC]
          refine le_max_of_le_right ?_
          have := mul_nonneg hC₀ (by positivity : (0 : ℝ) ≤ E * F)
          nlinarith

/-- **Orbital exponential stability.** Under the hypotheses of `asymptoticPhase_of_section`, the
distance to the orbit decays exponentially: every solution `x` on `[0, ∞)` with
`dist(x(0), x_*(ℝ)) < δ` satisfies `dist(x(t), x_*(ℝ)) ≤ C e^{−λt} dist(x(0), x_*(ℝ))` for
`t ≥ 0` (`Metric.infDist` to the range of `x_*`). -/
@[tmio T, powerlib_foundation] theorem infDist_orbit_le (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0)
    (hS : LTI.SchurStable (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)))) :
    ∃ δ C lam : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < lam ∧ ∀ x : ℝ → Fin n → ℝ,
      IsIntegralCurveOn x (fun _ => f) (Ici 0) → Metric.infDist (x 0) (range xs) < δ →
      ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
        C * Real.exp (-(lam * t)) * Metric.infDist (x 0) (range xs) := by
  obtain ⟨δ, C, lam, hδ, hC, hlam, hph⟩ := asymptoticPhase hf hfK hxs hT hper hne hS
  refine ⟨δ, C, lam, hδ, hC, hlam, fun x hx hx0 t ht => ?_⟩
  set D := Metric.infDist (x 0) (range xs) with hD
  set c := C * Real.exp (-(lam * t)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hne' : (range xs).Nonempty := range_nonempty xs
  -- for every margin `η` a point of the orbit within `D + η`
  have key : ∀ η, 0 < η → D + η < δ → Metric.infDist (x t) (range xs) ≤ c * (D + η) := by
    intro η hη hδη
    obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff hne').1
      (show D < D + η by linarith)
    rw [dist_eq_norm] at hσ
    obtain ⟨θ, -, hθ⟩ := hph σ x hx (hσ.trans hδη)
    calc Metric.infDist (x t) (range xs) ≤ dist (x t) (xs (t + σ + θ)) :=
          Metric.infDist_le_dist_of_mem (mem_range_self _)
      _ = ‖x t - xs (t + σ + θ)‖ := dist_eq_norm _ _
      _ ≤ c * ‖x 0 - xs σ‖ := hθ t ht
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

end powerlib.Periodic.AndronovWitt
