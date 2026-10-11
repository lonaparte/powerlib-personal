import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue

/-! # Zeros of a second-order trigonometric polynomial (foundation)

`trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = c₀ + c₁ cos θ + s₁ sin θ + c₂ cos 2θ + s₂ sin 2θ`.

* `trigPoly2_eval_cexp`: with `z = e^{jθ}`, `z² · h(θ) = P(z)` for the degree-≤-4 complex
  polynomial `P = trigPoly2Poly …` (the substitution `z = e^{jθ}`).
* `trigPoly2_zeroSet_finite`, `trigPoly2_ncard_zeroSet_le_four`: if the five coefficients are not
  all zero, then in every period window `[a, a + 2π)` the zero set is finite and has at most four
  elements (distinct `θ` in a window give distinct `z` on the unit circle, all roots of `P ≠ 0`).
* `even_ncard_zeroSet_of_simple`: a general parity lemma — a continuous `T`-periodic function
  whose zeros in each window are finitely many and all simple (nonzero derivative) has an even
  number of zeros in every window `[a, a + T)` (sign changes around the circle).
* `trigPoly2_even_ncard_zeroSet`, `trigPoly2_ncard_zeroSet_mem`: if every zero of `h` is simple,
  the number of zeros in a period is even, hence `0`, `2` or `4`.

This is a foundation module: it states nothing about any power system. It is used for counting
equilibria of reduced PLL models whose phase-detector characteristic is a trigonometric
polynomial of order two (`T-gfl-dynamics` §1.8–§1.9, `T-gfl-ph` §1.5, `T-pll-dynamics` §1.13).

Source: work-sync `theory/T-gfl-dynamics.md` §1.8–§1.9 and §1.14 (counts 2 or 4 per period),
`theory/T-gfl-ph.md` §1.5, `theory/T-pll-dynamics.md` §1.13(a). The notes state the counts
("2 or 4", "two stable and two saddles") without proof; this module proves the general bound
(at most 4) and the parity (even when all zeros are simple). It does not prove that 4 zeros
actually occur for the GFL form-B characteristic (see `theorem/GFL/FormB.lean`: for the exact
quasi-steady line solution the `2θ` coefficients vanish).
-/

noncomputable section
namespace powerlib.GFL
open Complex Polynomial Set Filter Topology

/-! ## The trigonometric polynomial and its derivative -/

/-- `h(θ) = c₀ + c₁ cos θ + s₁ sin θ + c₂ cos 2θ + s₂ sin 2θ`. -/
def trigPoly2 (c₀ c₁ s₁ c₂ s₂ : ℝ) (θ : ℝ) : ℝ :=
  c₀ + c₁ * Real.cos θ + s₁ * Real.sin θ + c₂ * Real.cos (2 * θ) + s₂ * Real.sin (2 * θ)

/-- `h'(θ) = −c₁ sin θ + s₁ cos θ − 2 c₂ sin 2θ + 2 s₂ cos 2θ`. -/
def trigPoly2Deriv (c₁ s₁ c₂ s₂ : ℝ) (θ : ℝ) : ℝ :=
  -c₁ * Real.sin θ + s₁ * Real.cos θ - 2 * c₂ * Real.sin (2 * θ) + 2 * s₂ * Real.cos (2 * θ)

/-- The zeros of `trigPoly2` in the period window `[a, a + 2π)`. -/
def trigPoly2ZeroSet (c₀ c₁ s₁ c₂ s₂ a : ℝ) : Set ℝ :=
  {θ | θ ∈ Ico a (a + 2 * Real.pi) ∧ trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = 0}

@[powerlib_foundation] theorem hasDerivAt_trigPoly2 (c₀ c₁ s₁ c₂ s₂ θ : ℝ) :
    HasDerivAt (trigPoly2 c₀ c₁ s₁ c₂ s₂) (trigPoly2Deriv c₁ s₁ c₂ s₂ θ) θ := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := ((((hasDerivAt_const θ c₀).add ((Real.hasDerivAt_cos θ).const_mul c₁)).add
    ((Real.hasDerivAt_sin θ).const_mul s₁)).add
    (((Real.hasDerivAt_cos (2 * θ)).comp θ h2).const_mul c₂)).add
    (((Real.hasDerivAt_sin (2 * θ)).comp θ h2).const_mul s₂)
  refine HasDerivAt.congr_deriv h ?_
  simp only [trigPoly2Deriv]
  ring

@[powerlib_foundation] theorem deriv_trigPoly2 (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    deriv (trigPoly2 c₀ c₁ s₁ c₂ s₂) = trigPoly2Deriv c₁ s₁ c₂ s₂ := by
  funext θ
  exact (hasDerivAt_trigPoly2 c₀ c₁ s₁ c₂ s₂ θ).deriv

@[powerlib_foundation] theorem continuous_trigPoly2 (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    Continuous (trigPoly2 c₀ c₁ s₁ c₂ s₂) := by
  unfold trigPoly2
  fun_prop

@[powerlib_foundation] theorem contDiff_trigPoly2 (c₀ c₁ s₁ c₂ s₂ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (trigPoly2 c₀ c₁ s₁ c₂ s₂) := by
  unfold trigPoly2
  fun_prop

@[powerlib_foundation] theorem trigPoly2_periodic (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    Function.Periodic (trigPoly2 c₀ c₁ s₁ c₂ s₂) (2 * Real.pi) := by
  intro θ
  have e : 2 * (θ + 2 * Real.pi) = 2 * θ + 2 * Real.pi + 2 * Real.pi := by ring
  simp only [trigPoly2, e, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-! ## The substitution `z = e^{jθ}` -/

/-- `P(z) = ((c₂ − j s₂)/2) z⁴ + ((c₁ − j s₁)/2) z³ + c₀ z² + ((c₁ + j s₁)/2) z + (c₂ + j s₂)/2`. -/
def trigPoly2Poly (c₀ c₁ s₁ c₂ s₂ : ℝ) : ℂ[X] :=
  C (((c₂ : ℂ) - s₂ * I) / 2) * X ^ 4 + C (((c₁ : ℂ) - s₁ * I) / 2) * X ^ 3 +
    C (c₀ : ℂ) * X ^ 2 + C (((c₁ : ℂ) + s₁ * I) / 2) * X + C (((c₂ : ℂ) + s₂ * I) / 2)

@[powerlib_foundation] theorem trigPoly2Poly_natDegree_le (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    (trigPoly2Poly c₀ c₁ s₁ c₂ s₂).natDegree ≤ 4 := by
  unfold trigPoly2Poly
  compute_degree

/-- `P(e^{jθ}) = e^{2jθ} h(θ)`. -/
@[powerlib_foundation] theorem trigPoly2_eval_cexp (c₀ c₁ s₁ c₂ s₂ θ : ℝ) :
    (trigPoly2Poly c₀ c₁ s₁ c₂ s₂).eval (exp (θ * I)) =
      exp (θ * I) ^ 2 * (trigPoly2 c₀ c₁ s₁ c₂ s₂ θ : ℂ) := by
  set z := exp ((θ : ℂ) * I) with hz
  have hz0 : z ≠ 0 := exp_ne_zero _
  have hinv : exp (-((θ : ℂ) * I)) = z⁻¹ := by rw [exp_neg]
  have hinv' : exp (-(θ : ℂ) * I) = z⁻¹ := by rw [neg_mul, hinv]
  have hcos : Complex.cos (θ : ℂ) = (z + z⁻¹) / 2 := by
    rw [Complex.cos, hinv']
  have hsin : Complex.sin (θ : ℂ) = (z⁻¹ - z) * I / 2 := by
    rw [Complex.sin, hinv']
  have hz2 : exp ((2 * (θ : ℂ)) * I) = z ^ 2 := by
    rw [hz, ← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv2 : exp (-(2 * (θ : ℂ)) * I) = (z ^ 2)⁻¹ := by
    rw [neg_mul, exp_neg, hz2]
  have hcos2 : Complex.cos (2 * (θ : ℂ)) = (z ^ 2 + (z ^ 2)⁻¹) / 2 := by
    rw [Complex.cos, hz2, hinv2]
  have hsin2 : Complex.sin (2 * (θ : ℂ)) = ((z ^ 2)⁻¹ - z ^ 2) * I / 2 := by
    rw [Complex.sin, hz2, hinv2]
  simp only [trigPoly2Poly, trigPoly2, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  push_cast
  rw [hcos, hsin, hcos2, hsin2]
  field_simp
  ring

@[powerlib_foundation] theorem trigPoly2Poly_ne_zero {c₀ c₁ s₁ c₂ s₂ : ℝ}
    (hne : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ s₁ = 0 ∧ c₂ = 0 ∧ s₂ = 0)) :
    trigPoly2Poly c₀ c₁ s₁ c₂ s₂ ≠ 0 := by
  intro hP
  have k4 := congrArg (fun p => Polynomial.coeff p 4) hP
  have k3 := congrArg (fun p => Polynomial.coeff p 3) hP
  have k2 := congrArg (fun p => Polynomial.coeff p 2) hP
  simp [trigPoly2Poly, coeff_X_pow] at k4 k3 k2
  apply hne
  have r4 := congrArg Complex.re k4
  have i4 := congrArg Complex.im k4
  have r3 := congrArg Complex.re k3
  have i3 := congrArg Complex.im k3
  simp at r4 i4 r3 i3
  exact ⟨k2, r3, by linarith, r4, by linarith⟩

/-- `θ ↦ e^{jθ}` is injective on every window `[a, a + 2π)`. -/
@[powerlib_foundation] theorem injOn_cexp_mul_I_Ico (a : ℝ) :
    InjOn (fun θ : ℝ => exp ((θ : ℂ) * I)) (Ico a (a + 2 * Real.pi)) := by
  intro θ hθ θ' hθ' h
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp h
  have him := congrArg Complex.im hn
  simp at him
  have hpi := Real.pi_pos
  have hlt : |θ - θ'| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  have hd : θ - θ' = n * (2 * Real.pi) := by linarith
  rw [hd, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hlt
  have hn1 : |(n : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hn1
    rw [abs_lt] at this
    omega
  rw [hn0] at hd
  simp at hd
  linarith

/-! ## At most four zeros per period -/

@[powerlib_foundation] theorem trigPoly2_zeroSet_mapsTo {c₀ c₁ s₁ c₂ s₂ a : ℝ} :
    MapsTo (fun θ : ℝ => exp ((θ : ℂ) * I)) (trigPoly2ZeroSet c₀ c₁ s₁ c₂ s₂ a)
      {z | (trigPoly2Poly c₀ c₁ s₁ c₂ s₂).IsRoot z} := by
  intro θ hθ
  simp only [mem_ofPred_eq, IsRoot.def, trigPoly2_eval_cexp, hθ.2, ofReal_zero, mul_zero]

@[powerlib_foundation] theorem trigPoly2_zeroSet_finite {c₀ c₁ s₁ c₂ s₂ : ℝ}
    (hne : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ s₁ = 0 ∧ c₂ = 0 ∧ s₂ = 0)) (a : ℝ) :
    (trigPoly2ZeroSet c₀ c₁ s₁ c₂ s₂ a).Finite := by
  have hP := trigPoly2Poly_ne_zero hne
  have hroots : {z | (trigPoly2Poly c₀ c₁ s₁ c₂ s₂).IsRoot z}.Finite :=
    Polynomial.finite_setOfPred_isRoot hP
  exact Finite.of_finite_image (hroots.subset (image_subset_iff.mpr trigPoly2_zeroSet_mapsTo))
    ((injOn_cexp_mul_I_Ico a).mono fun _ h => h.1)

/-- At most four zeros in every period window, unless all coefficients vanish. -/
@[powerlib_foundation] theorem trigPoly2_ncard_zeroSet_le_four {c₀ c₁ s₁ c₂ s₂ : ℝ}
    (hne : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ s₁ = 0 ∧ c₂ = 0 ∧ s₂ = 0)) (a : ℝ) :
    (trigPoly2ZeroSet c₀ c₁ s₁ c₂ s₂ a).ncard ≤ 4 := by
  have hP := trigPoly2Poly_ne_zero hne
  set P := trigPoly2Poly c₀ c₁ s₁ c₂ s₂
  have hroots : {z | P.IsRoot z} = (P.roots.toFinset : Set ℂ) := by
    ext z
    simp [Polynomial.mem_roots hP]
  have h1 := ncard_le_ncard_of_injOn (fun θ : ℝ => exp ((θ : ℂ) * I))
    (fun θ hθ => trigPoly2_zeroSet_mapsTo hθ) ((injOn_cexp_mul_I_Ico a).mono fun _ h => h.1)
    (Polynomial.finite_setOfPred_isRoot hP)
  rw [hroots, ncard_coe_finset] at h1
  calc _ ≤ P.roots.toFinset.card := h1
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 4 := trigPoly2Poly_natDegree_le c₀ c₁ s₁ c₂ s₂

/-! ## Parity of the number of simple zeros of a periodic function -/

section Parity

variable {f : ℝ → ℝ}

/-- Without zeros in `(a, b)`, `f a` and `f b` have the same sign (intermediate value theorem). -/
@[powerlib_foundation] private lemma mul_pos_of_no_zero (hf : Continuous f) {a b : ℝ}
    (hab : a < b) (ha : f a ≠ 0) (hb : f b ≠ 0) (hz : ∀ θ ∈ Ioo a b, f θ ≠ 0) :
    0 < f a * f b := by
  by_contra hneg
  push Not at hneg
  have hlt : f a * f b < 0 := lt_of_le_of_ne hneg (mul_ne_zero ha hb)
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · have hb' : 0 < f b := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg_of_nonpos_of_nonpos ha'.le h]
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo hab.le hf.continuousOn ⟨ha', hb'⟩
    exact hz c hc hfc
  · have hb' : f b < 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg ha'.le h]
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' hab.le hf.continuousOn ⟨hb', ha'⟩
    exact hz c hc hfc

/-- Near a simple zero `θ₀` (`f' (θ₀) = g ≠ 0`), `f · g` is negative on the left and positive on
the right. -/
@[powerlib_foundation] private lemma exists_sign_near_simple_zero {θ₀ g l r : ℝ}
    (hzero : f θ₀ = 0) (hd : HasDerivAt f g θ₀) (hg : g ≠ 0) (hl : l < θ₀) (hr : θ₀ < r) :
    (∃ d ∈ Ioo l θ₀, f d * g < 0) ∧ (∃ c ∈ Ioo θ₀ r, 0 < f c * g) := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hlim : Tendsto (fun x => slope f θ₀ x * g) (𝓝[≠] θ₀) (𝓝 (g * g)) :=
    hslope.mul_const g
  have hev : ∀ᶠ x in 𝓝[≠] θ₀, 0 < slope f θ₀ x * g :=
    hlim.eventually (lt_mem_nhds (mul_self_pos.mpr hg))
  have hsl (x : ℝ) : slope f θ₀ x = f x / (x - θ₀) := by
    rw [slope_def_field, hzero, sub_zero]
  constructor
  · have hev' : ∀ᶠ x in 𝓝[<] θ₀, 0 < slope f θ₀ x * g :=
      hev.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
    obtain ⟨d, hd1, hd2⟩ := (hev'.and (Ioo_mem_nhdsLT hl)).exists
    refine ⟨d, hd2, ?_⟩
    rw [hsl] at hd1
    have hneg : d - θ₀ < 0 := by linarith [hd2.2]
    have hne : d - θ₀ ≠ 0 := hneg.ne
    have : f d * g = (f d / (d - θ₀) * g) * (d - θ₀) := by
      field_simp
    rw [this]
    exact mul_neg_of_pos_of_neg hd1 hneg
  · have hev' : ∀ᶠ x in 𝓝[>] θ₀, 0 < slope f θ₀ x * g :=
      hev.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    obtain ⟨c, hc1, hc2⟩ := (hev'.and (Ioo_mem_nhdsGT hr)).exists
    refine ⟨c, hc2, ?_⟩
    rw [hsl] at hc1
    have hpos : 0 < c - θ₀ := by linarith [hc2.1]
    have hne : c - θ₀ ≠ 0 := hpos.ne'
    have : f c * g = (f c / (c - θ₀) * g) * (c - θ₀) := by
      field_simp
    rw [this]
    exact mul_pos hc1 hpos

/-- Sign rule on an interval: with `n` zeros in `(a, b)`, all simple,
`0 < f a · f b · (−1)ⁿ`. -/
@[powerlib_foundation] private lemma sign_rule (hf : Continuous f)
    (hsimple : ∀ θ, f θ = 0 → ∃ g, g ≠ 0 ∧ HasDerivAt f g θ) :
    ∀ (n : ℕ) (a b : ℝ), a < b → f a ≠ 0 → f b ≠ 0 →
      {θ | θ ∈ Ioo a b ∧ f θ = 0}.Finite →
      {θ | θ ∈ Ioo a b ∧ f θ = 0}.ncard = n → 0 < f a * f b * (-1) ^ n := by
  intro n
  induction n with
  | zero =>
    intro a b hab ha hb hfin hcard
    rw [pow_zero, mul_one]
    have hempty := (ncard_eq_zero hfin).mp hcard
    refine mul_pos_of_no_zero hf hab ha hb fun θ hθ hfθ => ?_
    have : θ ∈ {θ | θ ∈ Ioo a b ∧ f θ = 0} := ⟨hθ, hfθ⟩
    rw [hempty] at this
    exact this
  | succ n ih =>
    intro a b hab ha hb hfin hcard
    set S := {θ | θ ∈ Ioo a b ∧ f θ = 0} with hS
    have hSne : S.Nonempty := nonempty_of_ncard_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero n)
    obtain ⟨θ₁, hθ₁S, hθ₁min⟩ := exists_min_image S id hfin hSne
    -- the next zero to the right of `θ₁`, or `b`
    obtain ⟨R, hθR, hRb, hRnext⟩ : ∃ R, θ₁ < R ∧ R ≤ b ∧ ∀ θ ∈ S, θ ≠ θ₁ → R ≤ θ := by
      by_cases hS' : (S \ {θ₁}).Nonempty
      · obtain ⟨R, hRS, hRmin⟩ := exists_min_image (S \ {θ₁}) id (hfin.subset sdiff_subset) hS'
        refine ⟨R, lt_of_le_of_ne (hθ₁min R hRS.1) (Ne.symm hRS.2), hRS.1.1.2.le, ?_⟩
        intro θ hθ hne
        exact hRmin θ ⟨hθ, hne⟩
      · refine ⟨b, hθ₁S.1.2, le_rfl, ?_⟩
        intro θ hθ hne
        exact absurd ⟨θ, hθ, hne⟩ hS'
    obtain ⟨g, hg, hderiv⟩ := hsimple θ₁ hθ₁S.2
    obtain ⟨⟨d, hd, hdg⟩, ⟨c, hc, hcg⟩⟩ :=
      exists_sign_near_simple_zero hθ₁S.2 hderiv hg hθ₁S.1.1 hθR
    have hfd : f d ≠ 0 := fun h => by rw [h, zero_mul] at hdg; exact lt_irrefl _ hdg
    have hfc : f c ≠ 0 := fun h => by rw [h, zero_mul] at hcg; exact lt_irrefl _ hcg
    -- left piece `(a, d)`: no zeros
    have hleft : 0 < f a * f d := by
      refine mul_pos_of_no_zero hf hd.1 ha hfd fun θ hθ hfθ => ?_
      have hmin := hθ₁min θ ⟨⟨hθ.1, hθ.2.trans (hd.2.trans hθ₁S.1.2)⟩, hfθ⟩
      simp only [id] at hmin
      linarith [hθ.2, hd.2]
    -- right piece `(c, b)`: exactly the remaining `n` zeros
    have hset : {θ | θ ∈ Ioo c b ∧ f θ = 0} = S \ {θ₁} := by
      ext θ
      simp only [mem_ofPred_eq, Set.mem_sdiff, mem_singleton_iff, hS]
      constructor
      · rintro ⟨hθ, hfθ⟩
        refine ⟨⟨⟨hθ₁S.1.1.trans (hc.1.trans hθ.1), hθ.2⟩, hfθ⟩, ?_⟩
        intro h
        rw [h] at hθ
        linarith [hθ.1, hc.1]
      · rintro ⟨hθ, hne⟩
        exact ⟨⟨lt_of_lt_of_le hc.2 (hRnext θ hθ hne), hθ.1.2⟩, hθ.2⟩
    have hright : 0 < f c * f b * (-1) ^ n := by
      refine ih c b (lt_of_lt_of_le hc.2 hRb) hfc hb ?_ ?_
      · rw [hset]
        exact hfin.subset sdiff_subset
      · rw [hset, ncard_sdiff_singleton_of_mem hθ₁S, hcard]
        rfl
    have hdc : f d * f c < 0 := by
      have : (f d * g) * (f c * g) < 0 := mul_neg_of_neg_of_pos hdg hcg
      have hg2 : 0 < g * g := mul_self_pos.mpr hg
      by_contra h
      push Not at h
      nlinarith
    have key : 0 < (f a * f d) * (f c * f b * (-1) ^ n) * (-(f d * f c)) :=
      mul_pos (mul_pos hleft hright) (neg_pos.mpr hdc)
    have hsq : 0 < (f d * f c) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hfd hfc)
    have eq : (f a * f d) * (f c * f b * (-1) ^ n) * (-(f d * f c)) =
        (f a * f b * (-1) ^ (n + 1)) * (f d * f c) ^ 2 := by
      rw [pow_succ]
      ring
    rw [eq] at key
    exact pos_of_mul_pos_left key hsq.le

end Parity

/-- For a `T`-periodic function, the number of zeros in a window `[a, a + T)` does not depend on
`a`. -/
@[powerlib_foundation] theorem ncard_zeros_Ico_eq_of_periodic {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic f T) (a b : ℝ) :
    {θ | θ ∈ Ico a (a + T) ∧ f θ = 0}.ncard = {θ | θ ∈ Ico b (b + T) ∧ f θ = 0}.ncard := by
  have hval (x c : ℝ) : f (toIcoMod hT c x) = f x := by
    rw [toIcoMod]
    exact hper.sub_zsmul_eq _
  refine ncard_congr (fun θ _ => toIcoMod hT b θ) ?_ ?_ ?_
  · intro θ hθ
    exact ⟨toIcoMod_mem_Ico hT b θ, by rw [hval]; exact hθ.2⟩
  · intro θ θ' hθ hθ' h
    obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod hT).mp h
    have h2 : toIcoMod hT a θ = toIcoMod hT a θ' := (toIcoMod_eq_toIcoMod hT).mpr ⟨n, hn⟩
    rwa [(toIcoMod_eq_self hT).mpr hθ.1, (toIcoMod_eq_self hT).mpr hθ'.1] at h2
  · intro y hy
    refine ⟨toIcoMod hT a y, ⟨toIcoMod_mem_Ico hT a y, by rw [hval]; exact hy.2⟩, ?_⟩
    have h1 : toIcoMod hT b (toIcoMod hT a y) = toIcoMod hT b y := by
      rw [toIcoMod_eq_toIcoMod]
      refine ⟨toIcoDiv hT a y, ?_⟩
      rw [toIcoMod]
      abel
    rw [h1, (toIcoMod_eq_self hT).mpr hy.1]

/-- A continuous `T`-periodic function with finitely many zeros per window, all of them simple,
has an even number of zeros in every window `[a, a + T)`. -/
@[powerlib_foundation] theorem even_ncard_zeroSet_of_simple {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hper : Function.Periodic f T)
    (hfin : ∀ a, {θ | θ ∈ Ico a (a + T) ∧ f θ = 0}.Finite)
    (hsimple : ∀ θ, f θ = 0 → ∃ g, g ≠ 0 ∧ HasDerivAt f g θ) (a : ℝ) :
    Even {θ | θ ∈ Ico a (a + T) ∧ f θ = 0}.ncard := by
  -- a base point that is not a zero
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, f a₀ ≠ 0 := by
    have hinf : (Ico a (a + T) \ {θ | θ ∈ Ico a (a + T) ∧ f θ = 0}).Nonempty :=
      ((Ico_infinite (by linarith : a < a + T)).sdiff (hfin a)).nonempty
    obtain ⟨x, hx1, hx2⟩ := hinf
    exact ⟨x, fun h => hx2 ⟨hx1, h⟩⟩
  rw [ncard_zeros_Ico_eq_of_periodic hT hper a a₀]
  have hset : {θ | θ ∈ Ico a₀ (a₀ + T) ∧ f θ = 0} = {θ | θ ∈ Ioo a₀ (a₀ + T) ∧ f θ = 0} := by
    ext θ
    simp only [mem_ofPred_eq, mem_Ico, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨lt_of_le_of_ne h1 ?_, h2⟩, h3⟩
      rintro rfl
      exact ha₀ h3
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.le, h2⟩, h3⟩
  rw [hset]
  have hfin' : {θ | θ ∈ Ioo a₀ (a₀ + T) ∧ f θ = 0}.Finite := by
    rw [← hset]
    exact hfin a₀
  have hb : f (a₀ + T) ≠ 0 := by rw [hper]; exact ha₀
  have key := sign_rule hf hsimple _ a₀ (a₀ + T) (by linarith) ha₀ hb hfin' rfl
  rw [hper] at key
  rcases Nat.even_or_odd ({θ | θ ∈ Ioo a₀ (a₀ + T) ∧ f θ = 0}.ncard) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at key
    nlinarith [mul_self_pos.mpr ha₀]

/-! ## Simple zeros of `trigPoly2`: an even number, hence 0, 2 or 4 -/

/-- If every zero of `h` is simple (`h' ≠ 0` there), the number of zeros in every period window
is even. -/
@[powerlib_foundation] theorem trigPoly2_even_ncard_zeroSet {c₀ c₁ s₁ c₂ s₂ : ℝ}
    (hsimple : ∀ θ, trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = 0 → trigPoly2Deriv c₁ s₁ c₂ s₂ θ ≠ 0)
    (a : ℝ) : Even (trigPoly2ZeroSet c₀ c₁ s₁ c₂ s₂ a).ncard := by
  have hne : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ s₁ = 0 ∧ c₂ = 0 ∧ s₂ = 0) := by
    rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact hsimple 0 (by simp [trigPoly2]) (by simp [trigPoly2Deriv])
  exact even_ncard_zeroSet_of_simple (by positivity) (continuous_trigPoly2 _ _ _ _ _)
    (trigPoly2_periodic _ _ _ _ _) (trigPoly2_zeroSet_finite hne)
    (fun θ hθ => ⟨_, hsimple θ hθ, hasDerivAt_trigPoly2 _ _ _ _ _ θ⟩) a

/-- If every zero is simple, a period window contains `0`, `2` or `4` zeros. -/
@[powerlib_foundation] theorem trigPoly2_ncard_zeroSet_mem {c₀ c₁ s₁ c₂ s₂ : ℝ}
    (hsimple : ∀ θ, trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = 0 → trigPoly2Deriv c₁ s₁ c₂ s₂ θ ≠ 0)
    (a : ℝ) :
    (trigPoly2ZeroSet c₀ c₁ s₁ c₂ s₂ a).ncard = 0 ∨ (trigPoly2ZeroSet c₀ c₁ s₁ c₂ s₂ a).ncard = 2 ∨
      (trigPoly2ZeroSet c₀ c₁ s₁ c₂ s₂ a).ncard = 4 := by
  have hne : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ s₁ = 0 ∧ c₂ = 0 ∧ s₂ = 0) := by
    rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact hsimple 0 (by simp [trigPoly2]) (by simp [trigPoly2Deriv])
  have hle := trigPoly2_ncard_zeroSet_le_four hne a
  obtain ⟨k, hk⟩ := trigPoly2_even_ncard_zeroSet hsimple a
  omega

end powerlib.GFL
