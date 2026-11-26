import dependencies.Mathlib
import theorem.Attributes

/-! # A logistic amplitude with a vanishing perturbation converges to zero or to one

A nonnegative function `y = r²` of time whose derivative is that of the logistic amplitude
`ṙ = a r (1 − r)` up to a perturbation that vanishes relative to `r (1 + r)`,
`|y' − 2a(1 − √y) y| ≤ 2 √y (1 + √y) h(t)` with `h(t) → 0`, converges either to `0` or to `1`:
the converging-input converging-state dichotomy of the scalar logistic equation, whose
equilibria are the unstable origin and the attracting level `r = 1`.

Scope.
* Generic: real functions of time `y, y', h : ℝ → ℝ` on `[0, ∞)`, a rate `a > 0`. No model.

Source: the converging-input converging-state argument (E. D. Sontag, "A remark on the
converging-input converging-state property", *IEEE Trans. Autom. Control* 48 (2003) 313–314)
for the scalar logistic equation; the fences are the comparison theorem
`image_le_of_deriv_right_lt_deriv_boundary'` of Mathlib.

Results.
* `ge_of_fence`, `le_of_fence`: a level that the derivative crosses strictly upwards
  (downwards) is never crossed back.
* `tendsto_zero_or_one`: under the bound above, `y(t) → 0` or `y(t) → 1`. For every
  `δ ∈ (0, 1/2]`, once `h ≤ aδ/8`, either `y < δ²` from then on or `y` enters
  `[(1 − δ)², (1 + δ)²]` and stays there.
-/

noncomputable section
namespace powerlib.Dynamics.LogisticDichotomy

open Set Filter Topology

/-- **Lower fence.** If `y' > 0` wherever `y = c` after `t₀` and `y(t₀) ≥ c`, then `y ≥ c` after
`t₀`. -/
@[tmio T, powerlib_foundation] theorem ge_of_fence {y y' : ℝ → ℝ} {c t₀ : ℝ}
    (hy : ∀ t, t₀ ≤ t → HasDerivAt y (y' t) t) (hbar : ∀ t, t₀ ≤ t → y t = c → 0 < y' t)
    (h0 : c ≤ y t₀) {t : ℝ} (ht : t₀ ≤ t) : c ≤ y t := by
  have hc : ContinuousOn (fun s => -y s) (Icc t₀ t) := fun s hs =>
    (hy s hs.1).continuousAt.continuousWithinAt.neg
  have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => -y s)
    (f' := fun s => -y' s) (B := fun _ => -c) (B' := fun _ => 0) hc
    (fun s hs => (hy s hs.1).neg.hasDerivWithinAt) (by simpa using h0) continuousOn_const
    (fun s _ => hasDerivWithinAt_const _ _ _)
    (fun s hs he => by
      have := hbar s hs.1 (by simpa using he)
      simpa using this) (right_mem_Icc.mpr ht)
  simpa using this

/-- **Upper fence.** If `y' < 0` wherever `y = c` after `t₀` and `y(t₀) ≤ c`, then `y ≤ c` after
`t₀`. -/
@[tmio T, powerlib_foundation] theorem le_of_fence {y y' : ℝ → ℝ} {c t₀ : ℝ}
    (hy : ∀ t, t₀ ≤ t → HasDerivAt y (y' t) t) (hbar : ∀ t, t₀ ≤ t → y t = c → y' t < 0)
    (h0 : y t₀ ≤ c) {t : ℝ} (ht : t₀ ≤ t) : y t ≤ c := by
  have h := ge_of_fence (y := fun s => -y s) (y' := fun s => -y' s) (c := -c)
    (fun s hs => (hy s hs).neg) (fun s hs he => by
      have := hbar s hs (by linarith [show -y s = -c from he])
      linarith) (by linarith) ht
  linarith

/-- A derivative bounded below by `κ > 0` on `[t₀, ∞)` makes `y` exceed every bound. -/
@[powerlib_foundation] private theorem exists_ge_of_deriv_ge {y y' : ℝ → ℝ} {κ t₀ : ℝ}
    (hκ : 0 < κ) (hy : ∀ t, t₀ ≤ t → HasDerivAt y (y' t) t)
    (hd : ∀ t, t₀ ≤ t → κ ≤ y' t) (M : ℝ) : ∃ t, t₀ ≤ t ∧ M ≤ y t := by
  have hmono : MonotoneOn (fun s => y s - κ * s) (Ici t₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t₀) (f' := fun s => y' s - κ)
      (fun s hs => ((hy s hs).continuousAt.sub (continuousAt_const.mul
        continuousAt_id)).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ici] at hs
      exact ((hy s (le_of_lt hs)).sub ((hasDerivAt_id s).const_mul κ)).hasDerivWithinAt.congr_deriv
        (by simp)
    · rw [interior_Ici] at hs
      linarith [hd s (le_of_lt hs)]
  refine ⟨t₀ + |M - y t₀| / κ, by have := div_nonneg (abs_nonneg (M - y t₀)) hκ.le; linarith,
    ?_⟩
  have h := hmono (Set.self_mem_Ici) (show t₀ ≤ t₀ + |M - y t₀| / κ from by
    have := div_nonneg (abs_nonneg (M - y t₀)) hκ.le; linarith)
    (show t₀ ≤ t₀ + |M - y t₀| / κ from by
      have := div_nonneg (abs_nonneg (M - y t₀)) hκ.le; linarith)
  simp only at h
  have hk : κ * (|M - y t₀| / κ) = |M - y t₀| := by field_simp
  nlinarith [le_abs_self (M - y t₀)]

/-- **Logistic dichotomy.** Let `y ≥ 0` have derivative `y'` on `[0, ∞)` with
`|y' − 2a(1 − √y) y| ≤ 2 √y (1 + √y) h(t)`, `a > 0`, `h(t) → 0`. Then `y(t) → 0` or `y(t) → 1`. -/
@[tmio T, powerlib_foundation] theorem tendsto_zero_or_one {a : ℝ} (ha : 0 < a)
    {y y' h : ℝ → ℝ} (hy0 : ∀ t, 0 ≤ t → 0 ≤ y t) (hy : ∀ t, 0 ≤ t → HasDerivAt y (y' t) t)
    (hb : ∀ t, 0 ≤ t →
      |y' t - 2 * a * (1 - Real.sqrt (y t)) * y t| ≤
        2 * Real.sqrt (y t) * (1 + Real.sqrt (y t)) * h t)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto y atTop (𝓝 0) ∨ Tendsto y atTop (𝓝 1) := by
  -- after `T δ` the perturbation is below `a δ / 8`
  have hT : ∀ δ : ℝ, 0 < δ → ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → h t ≤ a * δ / 8 := by
    intro δ hδ
    have hpos : (0 : ℝ) < a * δ / 8 := by positivity
    obtain ⟨T, hT⟩ := (hh.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    exact ⟨max T 0, le_max_right _ _, fun t ht => (hT t (le_of_max_le_left ht)).le⟩
  -- the derivative in terms of `r = √y`
  have hsq : ∀ t, 0 ≤ t → y t = Real.sqrt (y t) ^ 2 := fun t ht =>
    (Real.sq_sqrt (hy0 t ht)).symm
  have hlow : ∀ t, 0 ≤ t → 2 * a * (1 - Real.sqrt (y t)) * y t -
      2 * Real.sqrt (y t) * (1 + Real.sqrt (y t)) * h t ≤ y' t := fun t ht => by
    have := (abs_le.mp (hb t ht)).1; linarith
  have hup : ∀ t, 0 ≤ t → y' t ≤ 2 * a * (1 - Real.sqrt (y t)) * y t +
      2 * Real.sqrt (y t) * (1 + Real.sqrt (y t)) * h t := fun t ht => by
    have := (abs_le.mp (hb t ht)).2; linarith
  -- the case analysis for one `δ`
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∃ T, 0 ≤ T ∧
      ((∀ t, T ≤ t → y t < δ ^ 2) ∨
        ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (1 - δ) ^ 2 ≤ y t ∧ y t ≤ (1 + δ) ^ 2) := by
    intro δ hδ hδ2
    obtain ⟨T, hT0, hTh⟩ := hT δ hδ
    refine ⟨T, hT0, ?_⟩
    by_cases hcase : ∀ t, T ≤ t → y t < δ ^ 2
    · exact Or.inl hcase
    right
    push Not at hcase
    obtain ⟨t₀, ht₀, hyt₀⟩ := hcase
    have hyT : ∀ t, T ≤ t → HasDerivAt y (y' t) t := fun t ht => hy t (hT0.trans ht)
    -- inside `[δ, 1 − δ]` the derivative is at least `a δ² / 2`
    have hmid : ∀ t, T ≤ t → δ ≤ Real.sqrt (y t) → Real.sqrt (y t) ≤ 1 - δ →
        a * δ ^ 2 / 2 ≤ y' t := by
      intro t ht h1 h2
      have h0t : 0 ≤ t := hT0.trans ht
      have hl := hlow t h0t
      have hyr := hsq t h0t
      set r := Real.sqrt (y t)
      rw [hyr] at hl
      have hht := hTh t ht
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hprod : δ / 2 ≤ (1 - r) * r := by nlinarith
      have e1 : a * r * δ ≤ 2 * a * (1 - r) * r ^ 2 := by
        have := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 * a * r)
        nlinarith
      have e2 : 2 * r * (1 + r) * h t ≤ 2 * r * (1 + r) * (a * δ / 8) :=
        mul_le_mul_of_nonneg_left hht (by positivity)
      have e3 : 2 * r * (1 + r) * (a * δ / 8) ≤ a * r * δ / 2 := by
        have : 0 ≤ a * r * δ := by positivity
        nlinarith
      have e4 : a * δ ^ 2 / 2 ≤ a * r * δ / 2 := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ a * δ)
        nlinarith
      linarith
    -- the lower fences at `δ²` and `(1 − δ)²`
    have hfence : ∀ c : ℝ, δ ≤ c → c ≤ 1 - δ → ∀ t, T ≤ t → y t = c ^ 2 → 0 < y' t := by
      intro c hc1 hc2 t ht he
      have h0t : 0 ≤ t := hT0.trans ht
      have hc0 : 0 ≤ c := hδ.le.trans hc1
      have hr : Real.sqrt (y t) = c := by rw [he, Real.sqrt_sq hc0]
      have := hmid t ht (by rw [hr]; exact hc1) (by rw [hr]; exact hc2)
      have : 0 < a * δ ^ 2 / 2 := by positivity
      linarith
    have hstay1 : ∀ t, t₀ ≤ t → δ ^ 2 ≤ y t := fun t ht =>
      ge_of_fence (fun s hs => hyT s (ht₀.trans hs))
        (fun s hs => hfence δ le_rfl (by linarith) s (ht₀.trans hs)) hyt₀ ht
    -- `y` reaches `(1 − δ)²`
    obtain ⟨t₁, ht₁, hyt₁⟩ : ∃ t₁, t₀ ≤ t₁ ∧ (1 - δ) ^ 2 ≤ y t₁ := by
      by_contra hno
      push Not at hno
      obtain ⟨t, ht, hyt⟩ := exists_ge_of_deriv_ge (y := y) (y' := y') (κ := a * δ ^ 2 / 2)
        (by positivity) (fun s hs => hyT s (ht₀.trans hs))
        (fun s hs => by
          have hs0 : 0 ≤ s := hT0.trans (ht₀.trans hs)
          refine hmid s (ht₀.trans hs) ?_ ?_
          · rw [show δ = Real.sqrt (δ ^ 2) from (Real.sqrt_sq hδ.le).symm]
            exact Real.sqrt_le_sqrt (hstay1 s hs)
          · rw [show 1 - δ = Real.sqrt ((1 - δ) ^ 2) from
              (Real.sqrt_sq (by linarith)).symm]
            exact Real.sqrt_le_sqrt (hno s hs).le) 1
      have := hno t ht
      nlinarith
    have hstay2 : ∀ t, t₁ ≤ t → (1 - δ) ^ 2 ≤ y t := fun t ht =>
      ge_of_fence (fun s hs => hyT s ((ht₀.trans ht₁).trans hs))
        (fun s hs => hfence (1 - δ) (by linarith) le_rfl s ((ht₀.trans ht₁).trans hs)) hyt₁ ht
    -- above `1 + δ` the derivative is at most `−a δ`
    have hhigh : ∀ t, T ≤ t → 1 + δ ≤ Real.sqrt (y t) → y' t ≤ -(a * δ) := by
      intro t ht h1
      have h0t : 0 ≤ t := hT0.trans ht
      have hu := hup t h0t
      have hyr := hsq t h0t
      set r := Real.sqrt (y t)
      rw [hyr] at hu
      have hht := hTh t ht
      have hr1 : 1 ≤ r := by linarith
      have e1 : 2 * a * (1 - r) * r ^ 2 ≤ -(2 * a * δ * r ^ 2) := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * a * r ^ 2)
        nlinarith
      have e2 : 2 * r * (1 + r) * h t ≤ 2 * r * (1 + r) * (a * δ / 8) :=
        mul_le_mul_of_nonneg_left hht (by positivity)
      have e3 : 2 * r * (1 + r) * (a * δ / 8) ≤ a * δ * r ^ 2 / 2 := by
        have : 0 ≤ a * δ * r := by positivity
        nlinarith
      have e4 : a * δ ≤ a * δ * r ^ 2 := by
        have : 1 ≤ r ^ 2 := by nlinarith
        have : 0 ≤ a * δ := by positivity
        nlinarith
      have : 0 < a * δ := by positivity
      linarith
    -- `y` comes down to `(1 + δ)²`
    obtain ⟨t₂, ht₂, hyt₂⟩ : ∃ t₂, t₁ ≤ t₂ ∧ y t₂ ≤ (1 + δ) ^ 2 := by
      by_contra hno
      push Not at hno
      obtain ⟨t, ht, hyt⟩ := exists_ge_of_deriv_ge (y := fun s => -y s) (y' := fun s => -y' s)
        (κ := a * δ) (by positivity) (fun s hs => (hyT s ((ht₀.trans ht₁).trans hs)).neg)
        (fun s hs => by
          have := hhigh s ((ht₀.trans ht₁).trans hs) (by
            rw [show 1 + δ = Real.sqrt ((1 + δ) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
            exact Real.sqrt_le_sqrt (hno s hs).le)
          linarith) 1
      have := hno t ht
      nlinarith
    have hstay3 : ∀ t, t₂ ≤ t → y t ≤ (1 + δ) ^ 2 := fun t ht =>
      le_of_fence (fun s hs => hyT s (((ht₀.trans ht₁).trans ht₂).trans hs))
        (fun s hs he => by
          have hr : Real.sqrt (y s) = 1 + δ := by rw [he, Real.sqrt_sq (by linarith)]
          have := hhigh s (((ht₀.trans ht₁).trans ht₂).trans hs) hr.ge
          have : 0 < a * δ := by positivity
          linarith) hyt₂ ht
    exact ⟨t₂, ht₀.trans (ht₁.trans ht₂), fun t ht => ⟨hstay2 t (ht₂.trans ht), hstay3 t ht⟩⟩
  -- assemble
  by_cases hone : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ T, 0 ≤ T ∧
      ∀ t, T ≤ t → (1 - δ) ^ 2 ≤ y t ∧ y t ≤ (1 + δ) ^ 2
  · right
    obtain ⟨δ₀, hδ₀, hδ₀2, T₀, hT₀, hband⟩ := hone
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ := min (1 / 2) (ε / 4) with hδdef
    have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
    have hδε : δ ≤ ε / 4 := min_le_right _ _
    obtain ⟨T, hT0', hcase⟩ := key δ hδ hδ2
    rcases hcase with hsmall | ⟨T', hTT', hT'⟩
    · exfalso
      have h1 := hsmall (max T T₀) (le_max_left _ _)
      have h2 := (hband (max T T₀) (le_max_right _ _)).1
      have : (1 / 4 : ℝ) ≤ (1 - δ₀) ^ 2 := by nlinarith
      nlinarith
    · refine ⟨T', fun t ht => ?_⟩
      obtain ⟨hl, hu⟩ := hT' t ht
      rw [Real.dist_eq, abs_lt]
      constructor <;> nlinarith
  · left
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ := min (1 / 2) (Real.sqrt ε / 2) with hδdef
    have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
    have hδε : δ ≤ Real.sqrt ε / 2 := min_le_right _ _
    obtain ⟨T, hT0', hcase⟩ := key δ hδ hδ2
    rcases hcase with hsmall | ⟨T', hTT', hT'⟩
    · refine ⟨T, fun t ht => ?_⟩
      have h1 := hsmall t ht
      have h0 := hy0 t (hT0'.trans ht)
      have hsq' : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
      nlinarith
    · exact absurd ⟨δ, hδ, hδ2, T', hT0'.trans hTT', hT'⟩ hone

end powerlib.Dynamics.LogisticDichotomy
