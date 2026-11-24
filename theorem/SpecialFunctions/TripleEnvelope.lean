import theorem.SpecialFunctions.ComplexProduct
import theorem.SpecialFunctions.Helly

/-! # The largest cross term of two complex numbers under finitely many bounds (foundation)

Finitely many bounds `‖p_i z₁ + q_i z₂‖ ≤ r_i` (`i : ι`, real `p_i`, `q_i`, `r_i ≥ 0`) on a pair
`(z₁, z₂) ∈ ℂ²`: the largest cross term `Im(z₁ z̄₂)` under all of them is the smallest of the
largest cross terms under three of them (for at least three bounds, each triple having a largest
cross term). The pair is lifted to
`(x, y, c) = (‖z₁‖², ‖z₂‖², Re(z₁ z̄₂)) ∈ ℝ³`, where each bound is the half-space
`p_i² x + q_i² y + 2p_iq_i c ≤ r_i²` and `Im(z₁ z̄₂)² = x y − c²`, so the level `Im(z₁ z̄₂) ≥ m`
(`m ≥ 0`) lifts into the convex rotated cone `{x, y ≥ 0, m² + c² ≤ x y}`. Helly's theorem in
`ℝ³` (every four of the convex sets meet) applies to the cone and the half-spaces: four of them
without the cone contain the origin, four with the cone contain at most three bounds, which some
triple reaching the level satisfies. A common point is realized by a pair after lowering `x`
until the cone is tight (the `x`-coefficients `p_i²` are nonnegative), with the phase of
`z₁ z̄₂` chosen to put the level into the imaginary part.

A triple of pairwise independent bounds has a closed form. In the coordinates
`w₁ = p₁z₁ + q₁z₂`, `w₂ = p₂z₁ + q₂z₂` (determinant `δ = p₁q₂ − p₂q₁ ≠ 0`) the cross term scales,
`Im(w₁ w̄₂) = δ Im(z₁ z̄₂)`, the first two bounds are a bidisk and the third reads
`‖λw₁ + μw₂‖ ≤ r₃` for `(p₃, q₃) = λ(p₁, q₁) + μ(p₂, q₂)`; the complex form of `reactiveMax`
(`isGreatest_im_mul_conj`) gives the largest cross term `√reactiveMax(λ²r₁², μ²r₂², r₃²)/(2|λμδ|)`.
With the determinants `d₁₂ = p₁q₂ − p₂q₁`, `d₂₃ = p₂q₃ − p₃q₂`, `d₃₁ = p₃q₁ − p₁q₃` (Cramer's rule:
`λ = −d₂₃/d₁₂`, `μ = −d₃₁/d₁₂`) the same value is
`√reactiveMax(d₂₃²r₁², d₃₁²r₂², d₁₂²r₃²)/(2|d₁₂d₂₃d₃₁|)` (`tripleMax`). Two independent bounds
alone give `r₁r₂/|δ|`.

Scope.
* Generic static algebra and convex geometry of two complex numbers and finitely many real
  parameters; nothing here describes a physical system and no model is defined. A triple with
  two parallel coefficient vectors is not given a closed form here; the Helly reduction
  (`isGreatest_im_mul_conj_of_three`) takes any values for the triples.

Source: Helly's theorem (E. Helly, 1923) as `Convex.helly_theorem'` of Mathlib
(`Mathlib/Analysis/Convex/Radon.lean`); the convexity of the rotated second-order cone, from
`(t + cc')² ≤ (t + c²)(t + c'²)` and AM–GM; the complex form of `reactiveMax`,
`theorem/SpecialFunctions/ComplexProduct.lean`; elementary linear algebra of a real change of
coordinates; no paper.

Results.
* `convex_rotatedCone`: for `t ≥ 0` the cone `{(x, y, c) | x, y ≥ 0, t + c² ≤ x y}` is convex.
* `im_comb_mul_conj_comb`: `Im((p₁z₁ + q₁z₂) conj(p₂z₁ + q₂z₂)) = (p₁q₂ − p₂q₁) Im(z₁ z̄₂)`.
* `isGreatest_im_mul_conj_of_three` (Helly reduction): if every at most three of the bounds
  admit a pair with cross term at least `m`, and some subfamily caps the cross term at `m`, then
  `m` is the largest cross term under all the bounds.
* `isGreatest_im_mul_conj_of_triples`: for a finite set of index triples covering every set of
  at most three indices, with largest cross term `v t` under the three bounds of each triple `t`,
  the largest cross term under all the bounds is the smallest `v t`.
* `isGreatest_im_mul_conj_inf'`: for at least three bounds, with largest cross term `v T` under
  each three-element subfamily `T`, the largest cross term under all the bounds is the smallest
  `v T`.
* `isGreatest_im_mul_conj_pair`: under two bounds with `p₁q₂ − p₂q₁ ≠ 0`, the largest cross term
  is `r₁r₂/|p₁q₂ − p₂q₁|`.
* `isGreatest_im_mul_conj_triple`: under three bounds with `p₁q₂ − p₂q₁ ≠ 0`,
  `(p₃, q₃) = λ(p₁, q₁) + μ(p₂, q₂)` and `λ, μ ≠ 0`, the largest cross term is
  `√reactiveMax(λ²r₁², μ²r₂², r₃²)/(2|λμ(p₁q₂ − p₂q₁)|)`.
* `tripleMax` (definition): `√reactiveMax(d₂₃²r₁², d₃₁²r₂², d₁₂²r₃²)/(2|d₁₂d₂₃d₃₁|)`;
  `isGreatest_tripleMax`: under three bounds with nonzero `d₁₂`, `d₂₃`, `d₃₁` it is the largest
  cross term.
-/

noncomputable section
namespace powerlib.SpecialFunctions

open ComplexConjugate

/-! ## The lift to `ℝ³` -/

/-- The bound in lifted coordinates: `‖p z₁ + q z₂‖² = p²‖z₁‖² + q²‖z₂‖² + 2pq Re(z₁ z̄₂)`. -/
@[tmio T, powerlib_foundation] private theorem sq_norm_comb (p q : ℝ) (z₁ z₂ : ℂ) :
    p ^ 2 * ‖z₁‖ ^ 2 + q ^ 2 * ‖z₂‖ ^ 2 + 2 * (p * q) * (z₁ * conj z₂).re =
      ‖(p : ℂ) * z₁ + (q : ℂ) * z₂‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The cross term in lifted coordinates: `‖z₁‖²‖z₂‖² = Re(z₁ z̄₂)² + Im(z₁ z̄₂)²`. -/
@[tmio T, powerlib_foundation] private theorem sq_norm_mul_sq_norm (z₁ z₂ : ℂ) :
    ‖z₁‖ ^ 2 * ‖z₂‖ ^ 2 = (z₁ * conj z₂).re ^ 2 + (z₁ * conj z₂).im ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Every lifted point on the cone is a pair: for `x, y ≥ 0` and `c² + s² = x y` some pair has
`‖z₁‖² = x`, `‖z₂‖² = y` and `z₁ z̄₂ = c + j s`. -/
@[tmio T, powerlib_foundation] private theorem exists_lift_eq {x y c s : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : c ^ 2 + s ^ 2 = x * y) :
    ∃ z₁ z₂ : ℂ, ‖z₁‖ ^ 2 = x ∧ ‖z₂‖ ^ 2 = y ∧ (z₁ * conj z₂).re = c ∧
      (z₁ * conj z₂).im = s := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    have hc : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg s]
    have hs : s = 0 := by nlinarith [sq_nonneg c, sq_nonneg s]
    refine ⟨0, (Real.sqrt y : ℂ), by simp, ?_, by simp [hc], by simp [hs]⟩
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hy]
  · have hr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hpos
    refine ⟨(Real.sqrt x : ℂ), ⟨c / Real.sqrt x, -(s / Real.sqrt x)⟩, ?_, ?_, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hx]
    · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mk]
      field_simp
      rw [Real.sq_sqrt hx]
      linarith
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, zero_mul, sub_zero]
      field_simp
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, zero_mul, add_zero, neg_neg]
      field_simp

/-- The rotated second-order cone `{(x, y, c) | x, y ≥ 0, t + c² ≤ x y}` is convex for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem convex_rotatedCone {t : ℝ} (ht : 0 ≤ t) :
    Convex ℝ {X : ℝ × ℝ × ℝ | 0 ≤ X.1 ∧ 0 ≤ X.2.1 ∧ t + X.2.2 ^ 2 ≤ X.1 * X.2.1} := by
  rintro ⟨x, y, c⟩ ⟨hx, hy, h⟩ ⟨x', y', c'⟩ ⟨hx', hy', h'⟩ a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at *
  obtain rfl : b = 1 - a := by linarith
  refine ⟨add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hx'),
    add_nonneg (mul_nonneg ha hy) (mul_nonneg hb hy'), ?_⟩
  have hprod : (t + c ^ 2) * (t + c' ^ 2) ≤ (x * y') * (x' * y) := by
    calc (t + c ^ 2) * (t + c' ^ 2) ≤ (x * y) * (x' * y') :=
          mul_le_mul h h' (by positivity) (by positivity)
      _ = (x * y') * (x' * y) := by ring
  have hS : 0 ≤ x * y' + x' * y := by positivity
  -- `(t + cc')² ≤ (t + c²)(t + c'²) ≤ (x y')(x' y) ≤ ((x y' + x' y)/2)²`
  have hsq : (2 * (t + c * c')) ^ 2 ≤ (x * y' + x' * y) ^ 2 := by
    nlinarith [sq_nonneg (x * y' - x' * y), mul_nonneg ht (sq_nonneg (c - c'))]
  have key : 2 * (t + c * c') ≤ x * y' + x' * y := (abs_le_of_sq_le_sq' hsq hS).2
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg a),
    mul_le_mul_of_nonneg_left h' (sq_nonneg (1 - a)),
    mul_le_mul_of_nonneg_left key (mul_nonneg ha hb)]

/-! ## The Helly reduction to three bounds -/

/-- **Helly reduction**: if every at most three of the bounds `‖p_i z₁ + q_i z₂‖ ≤ r_i`
(`r_i ≥ 0`) admit a pair with cross term at least `m`, and the cross term under some subfamily is
at most `m`, then `m` is the largest cross term `Im(z₁ z̄₂)` under all the bounds. -/
@[tmio T, powerlib_foundation] theorem isGreatest_im_mul_conj_of_three {ι : Type*} [Fintype ι]
    {p q r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {m : ℝ}
    (hlow : ∀ T : Finset ι, T.card ≤ 3 → ∃ z₁ z₂ : ℂ,
      (∀ i ∈ T, ‖(p i : ℂ) * z₁ + (q i : ℂ) * z₂‖ ≤ r i) ∧ m ≤ (z₁ * conj z₂).im)
    (hup : ∃ T : Finset ι, ∀ z₁ z₂ : ℂ,
      (∀ i ∈ T, ‖(p i : ℂ) * z₁ + (q i : ℂ) * z₂‖ ≤ r i) → (z₁ * conj z₂).im ≤ m) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ, (∀ i, ‖(p i : ℂ) * z₁ + (q i : ℂ) * z₂‖ ≤ r i) ∧
      x = (z₁ * conj z₂).im} m := by
  classical
  obtain ⟨T₀, hT₀⟩ := hup
  refine ⟨?_, ?_⟩
  swap
  · rintro x ⟨z₁, z₂, hz, rfl⟩
    exact hT₀ z₁ z₂ fun i _ => hz i
  have hm0 : 0 ≤ m := by simpa using hT₀ 0 0 fun i _ => by simpa using hr i
  -- the cone of the level `m` and the half-spaces of the bounds, in `ℝ³`
  let F : Option ι → Set (ℝ × ℝ × ℝ) := fun o => Option.elim o
    {X | 0 ≤ X.1 ∧ 0 ≤ X.2.1 ∧ m ^ 2 + X.2.2 ^ 2 ≤ X.1 * X.2.1}
    fun i => {X | p i ^ 2 * X.1 + q i ^ 2 * X.2.1 + 2 * (p i * q i) * X.2.2 ≤ r i ^ 2}
  have hconv : ∀ o ∈ (Finset.univ : Finset (Option ι)), Convex ℝ (F o) := by
    rintro (_ | i) -
    · exact convex_rotatedCone (sq_nonneg m)
    · exact convex_halfSpace_le
        ⟨fun _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring,
          fun _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩ _
  have hinter : ∀ I ⊆ (Finset.univ : Finset (Option ι)),
      I.card ≤ Module.finrank ℝ (ℝ × ℝ × ℝ) + 1 → (⋂ o ∈ I, F o).Nonempty := by
    intro I _ hI
    have hfin : Module.finrank ℝ (ℝ × ℝ × ℝ) = 3 := by simp
    rw [hfin] at hI
    by_cases hn : none ∈ I
    · -- with the cone: a pair meeting the at most three bounds of `I` at the level
      have hc : (Finset.eraseNone I).card ≤ 3 := by
        rw [Finset.card_eraseNone_of_mem hn]
        omega
      obtain ⟨z₁, z₂, hz, hmz⟩ := hlow _ hc
      refine ⟨(‖z₁‖ ^ 2, ‖z₂‖ ^ 2, (z₁ * conj z₂).re), Set.mem_iInter₂.mpr ?_⟩
      rintro (_ | i) hi
      · refine ⟨sq_nonneg _, sq_nonneg _, ?_⟩
        have hsq : m ^ 2 ≤ (z₁ * conj z₂).im ^ 2 := pow_le_pow_left₀ hm0 hmz 2
        show m ^ 2 + (z₁ * conj z₂).re ^ 2 ≤ ‖z₁‖ ^ 2 * ‖z₂‖ ^ 2
        rw [sq_norm_mul_sq_norm]
        linarith
      · show p i ^ 2 * ‖z₁‖ ^ 2 + q i ^ 2 * ‖z₂‖ ^ 2 + 2 * (p i * q i) * (z₁ * conj z₂).re ≤
          r i ^ 2
        rw [sq_norm_comb]
        exact pow_le_pow_left₀ (norm_nonneg _) (hz i (Finset.mem_eraseNone.mpr hi)) 2
    · -- without the cone: the origin
      refine ⟨0, Set.mem_iInter₂.mpr ?_⟩
      rintro (_ | i) hi
      · exact absurd hi hn
      · show p i ^ 2 * 0 + q i ^ 2 * 0 + 2 * (p i * q i) * 0 ≤ r i ^ 2
        simpa using sq_nonneg (r i)
  obtain ⟨⟨x, y, c⟩, hX⟩ := Convex.helly_theorem' hconv hinter
  rw [Set.mem_iInter₂] at hX
  obtain ⟨hx, hy, hcone⟩ : 0 ≤ x ∧ 0 ≤ y ∧ m ^ 2 + c ^ 2 ≤ x * y := hX none (Finset.mem_univ _)
  have hlin : ∀ i, p i ^ 2 * x + q i ^ 2 * y + 2 * (p i * q i) * c ≤ r i ^ 2 :=
    fun i => hX (some i) (Finset.mem_univ _)
  -- lower `x` until the cone is tight: `x' y = m² + c²`, `x' ≤ x`
  obtain ⟨x', hx'def⟩ : ∃ x', x' = (m ^ 2 + c ^ 2) / y := ⟨_, rfl⟩
  have hx'0 : 0 ≤ x' := hx'def ▸ div_nonneg (by positivity) hy
  have hx'x : x' ≤ x := hx'def ▸ div_le_of_le_mul₀ hy hx (by linarith)
  have htight : c ^ 2 + m ^ 2 = x' * y := by
    rcases eq_or_lt_of_le hy with hy0 | hypos
    · rw [← hy0, mul_zero] at hcone
      rw [← hy0, mul_zero]
      nlinarith [sq_nonneg c, sq_nonneg m]
    · rw [hx'def]
      field_simp
      ring
  obtain ⟨z₁, z₂, h₁, h₂, hre, him⟩ := exists_lift_eq hx'0 hy htight
  refine ⟨z₁, z₂, fun i => ?_, him.symm⟩
  refine (sq_le_sq₀ (norm_nonneg _) (hr i)).mp ?_
  rw [← sq_norm_comb, h₁, h₂, hre]
  linarith [mul_le_mul_of_nonneg_left hx'x (sq_nonneg (p i)), hlin i]

/-- The largest cross term under all the bounds is the smallest over a set `𝒯` of index triples
covering every set of at most three indices, given the largest cross term `v t` under the three
bounds of each triple `t ∈ 𝒯`. -/
@[tmio T, powerlib_foundation] theorem isGreatest_im_mul_conj_of_triples {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p q r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {𝒯 : Finset (ι × ι × ι)}
    (h𝒯 : 𝒯.Nonempty) {v : ι × ι × ι → ℝ}
    (hcover : ∀ T : Finset ι, T.card ≤ 3 → ∃ t ∈ 𝒯, T ⊆ {t.1, t.2.1, t.2.2})
    (hv : ∀ t ∈ 𝒯, IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ,
      ‖(p t.1 : ℂ) * z₁ + (q t.1 : ℂ) * z₂‖ ≤ r t.1 ∧
        ‖(p t.2.1 : ℂ) * z₁ + (q t.2.1 : ℂ) * z₂‖ ≤ r t.2.1 ∧
          ‖(p t.2.2 : ℂ) * z₁ + (q t.2.2 : ℂ) * z₂‖ ≤ r t.2.2 ∧ x = (z₁ * conj z₂).im} (v t)) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ, (∀ i, ‖(p i : ℂ) * z₁ + (q i : ℂ) * z₂‖ ≤ r i) ∧
      x = (z₁ * conj z₂).im} (𝒯.inf' h𝒯 v) := by
  apply isGreatest_im_mul_conj_of_three hr
  · intro T hT
    obtain ⟨t, ht, hsub⟩ := hcover T hT
    obtain ⟨⟨z₁, z₂, h₁, h₂, h₃, hx⟩, -⟩ := hv t ht
    refine ⟨z₁, z₂, fun i hi => ?_, hx ▸ Finset.inf'_le v ht⟩
    have hi' := hsub hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl
    exacts [h₁, h₂, h₃]
  · obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_inf' h𝒯 v
    refine ⟨{t.1, t.2.1, t.2.2}, fun z₁ z₂ hz => ?_⟩
    rw [he]
    exact (hv t ht).2 ⟨z₁, z₂, hz _ (by simp), hz _ (by simp), hz _ (by simp), rfl⟩

/-- With at least three bounds, the largest cross term under all of them is the smallest of the
largest cross terms `v T` under the three-element subfamilies `T`. -/
@[tmio T, powerlib_foundation] theorem isGreatest_im_mul_conj_inf' {ι : Type*} [Fintype ι]
    {p q r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (h3 : 3 ≤ Fintype.card ι) {v : Finset ι → ℝ}
    (hv : ∀ T : Finset ι, T.card = 3 → IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ,
      (∀ i ∈ T, ‖(p i : ℂ) * z₁ + (q i : ℂ) * z₂‖ ≤ r i) ∧ x = (z₁ * conj z₂).im} (v T)) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ, (∀ i, ‖(p i : ℂ) * z₁ + (q i : ℂ) * z₂‖ ≤ r i) ∧
      x = (z₁ * conj z₂).im}
      ((Finset.univ.powersetCard 3).inf'
        (Finset.powersetCard_nonempty.mpr (h3.trans_eq Finset.card_univ.symm)) v) := by
  apply isGreatest_im_mul_conj_of_three hr
  · intro T hT
    obtain ⟨T', hTT', hT'⟩ := Finset.exists_superset_card_eq hT h3
    obtain ⟨⟨z₁, z₂, hz, hx⟩, -⟩ := hv T' hT'
    exact ⟨z₁, z₂, fun i hi => hz i (hTT' hi),
      hx ▸ Finset.inf'_le v (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT'⟩)⟩
  · obtain ⟨T, hT, he⟩ := Finset.exists_mem_eq_inf'
      (Finset.powersetCard_nonempty.mpr (h3.trans_eq Finset.card_univ.symm)) v
    refine ⟨T, fun z₁ z₂ hz => ?_⟩
    rw [he]
    exact (hv T (Finset.mem_powersetCard.mp hT).2).2 ⟨z₁, z₂, hz, rfl⟩

/-! ## Closed forms of two and three bounds -/

/-- The cross term in the coordinates `w_k = p_k z₁ + q_k z₂`:
`Im((p₁z₁ + q₁z₂) conj(p₂z₁ + q₂z₂)) = (p₁q₂ − p₂q₁) Im(z₁ z̄₂)`. -/
@[tmio T, powerlib_foundation] theorem im_comb_mul_conj_comb (p₁ q₁ p₂ q₂ : ℝ) (z₁ z₂ : ℂ) :
    (((p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂) * conj ((p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂)).im =
      (p₁ * q₂ - p₂ * q₁) * (z₁ * conj z₂).im := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- A change of coordinates `w_k = p_k z₁ + q_k z₂` with determinant `δ = p₁q₂ − p₂q₁ ≠ 0`
divides the largest cross term by `|δ|`, for a condition on `(w₁, w₂)` kept by conjugation. -/
@[tmio T, powerlib_foundation] private theorem isGreatest_im_of_change {p₁ q₁ p₂ q₂ m : ℝ}
    (hδ : p₁ * q₂ - p₂ * q₁ ≠ 0) {C : ℂ → ℂ → Prop}
    (hC : ∀ w₁ w₂, C w₁ w₂ → C (conj w₁) (conj w₂))
    (hm : IsGreatest {x : ℝ | ∃ w₁ w₂ : ℂ, C w₁ w₂ ∧ x = (w₁ * conj w₂).im} m) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ,
      C ((p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂) ((p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂) ∧
        x = (z₁ * conj z₂).im} (m / |p₁ * q₂ - p₂ * q₁|) := by
  have hδ' : ((p₁ * q₂ - p₂ * q₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδ
  have hδa : 0 < |p₁ * q₂ - p₂ * q₁| := abs_pos.mpr hδ
  -- the inverse change of coordinates
  have inv : ∀ w₁ w₂ : ℂ, ∃ z₁ z₂ : ℂ,
      (p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂ = w₁ ∧ (p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂ = w₂ := by
    intro w₁ w₂
    refine ⟨((q₂ : ℂ) * w₁ - (q₁ : ℂ) * w₂) / ((p₁ * q₂ - p₂ * q₁ : ℝ) : ℂ),
      ((p₁ : ℂ) * w₂ - (p₂ : ℂ) * w₁) / ((p₁ * q₂ - p₂ * q₁ : ℝ) : ℂ), ?_, ?_⟩
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hδ']
      push_cast
      ring
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hδ']
      push_cast
      ring
  have hconj : ∀ w₁ w₂ : ℂ, (conj w₁ * conj (conj w₂)).im = -(w₁ * conj w₂).im := by
    intro w₁ w₂
    simp only [Complex.conj_conj, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  constructor
  · obtain ⟨w₁, w₂, hw, rfl⟩ := hm.1
    rcases lt_or_gt_of_ne hδ with hneg | hpos
    · -- `δ < 0`: realize the conjugate pair
      obtain ⟨z₁, z₂, e₁, e₂⟩ := inv (conj w₁) (conj w₂)
      refine ⟨z₁, z₂, e₁ ▸ e₂ ▸ hC w₁ w₂ hw, ?_⟩
      have h := im_comb_mul_conj_comb p₁ q₁ p₂ q₂ z₁ z₂
      rw [e₁, e₂, hconj] at h
      rw [abs_of_neg hneg, div_eq_iff (by linarith)]
      linarith
    · obtain ⟨z₁, z₂, e₁, e₂⟩ := inv w₁ w₂
      refine ⟨z₁, z₂, e₁ ▸ e₂ ▸ hw, ?_⟩
      have h := im_comb_mul_conj_comb p₁ q₁ p₂ q₂ z₁ z₂
      rw [e₁, e₂] at h
      rw [abs_of_pos hpos, div_eq_iff hpos.ne']
      linarith
  · rintro x ⟨z₁, z₂, hz, rfl⟩
    have h₁ := hm.2 ⟨_, _, hz, rfl⟩
    have h₂ := hm.2 ⟨_, _, hC _ _ hz, rfl⟩
    rw [im_comb_mul_conj_comb] at h₁
    rw [hconj, im_comb_mul_conj_comb] at h₂
    rw [le_div_iff₀ hδa]
    rcases abs_cases (p₁ * q₂ - p₂ * q₁) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- Two bounds in the coordinates `(w₁, w₂)` themselves: the bidisk `‖w₁‖ ≤ r₁`, `‖w₂‖ ≤ r₂` has
largest cross term `r₁ r₂`. -/
@[tmio T, powerlib_foundation] private theorem isGreatest_im_mul_conj_bidisk {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    IsGreatest {x : ℝ | ∃ w₁ w₂ : ℂ, (‖w₁‖ ≤ r₁ ∧ ‖w₂‖ ≤ r₂) ∧ x = (w₁ * conj w₂).im}
      (r₁ * r₂) := by
  constructor
  · refine ⟨(r₁ : ℂ), -((r₂ : ℂ) * Complex.I), ⟨?_, ?_⟩, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₁]
    · rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr₂]
    · simp
  · rintro x ⟨w₁, w₂, ⟨h₁, h₂⟩, rfl⟩
    calc (w₁ * conj w₂).im ≤ ‖w₁ * conj w₂‖ := Complex.im_le_norm _
      _ = ‖w₁‖ * ‖w₂‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ r₁ * r₂ := mul_le_mul h₁ h₂ (norm_nonneg _) hr₁

/-- Two bounds with `δ = p₁q₂ − p₂q₁ ≠ 0`: the largest cross term is `r₁ r₂/|δ|`. -/
@[tmio T, powerlib_foundation] theorem isGreatest_im_mul_conj_pair {p₁ q₁ r₁ p₂ q₂ r₂ : ℝ}
    (hδ : p₁ * q₂ - p₂ * q₁ ≠ 0) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ, ‖(p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂‖ ≤ r₁ ∧
        ‖(p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂‖ ≤ r₂ ∧ x = (z₁ * conj z₂).im}
      (r₁ * r₂ / |p₁ * q₂ - p₂ * q₁|) := by
  have h := isGreatest_im_of_change hδ (C := fun w₁ w₂ => ‖w₁‖ ≤ r₁ ∧ ‖w₂‖ ≤ r₂)
    (fun w₁ w₂ hw => by simpa only [Complex.norm_conj] using hw)
    (isGreatest_im_mul_conj_bidisk hr₁ hr₂)
  simpa only [and_assoc] using h

/-- Three bounds with `δ = p₁q₂ − p₂q₁ ≠ 0` and `(p₃, q₃) = λ(p₁, q₁) + μ(p₂, q₂)`, `λ, μ ≠ 0`:
the largest cross term is `√reactiveMax(λ²r₁², μ²r₂², r₃²)/(2|λμδ|)`. -/
@[tmio T, powerlib_foundation] theorem isGreatest_im_mul_conj_triple
    {p₁ q₁ r₁ p₂ q₂ r₂ p₃ q₃ r₃ c₁ c₂ : ℝ} (hδ : p₁ * q₂ - p₂ * q₁ ≠ 0)
    (hp₃ : p₃ = c₁ * p₁ + c₂ * p₂) (hq₃ : q₃ = c₁ * q₁ + c₂ * q₂) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ, ‖(p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂‖ ≤ r₁ ∧
        ‖(p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂‖ ≤ r₂ ∧ ‖(p₃ : ℂ) * z₁ + (q₃ : ℂ) * z₂‖ ≤ r₃ ∧
          x = (z₁ * conj z₂).im}
      (Real.sqrt (reactiveMax (c₁ ^ 2 * r₁ ^ 2) (c₂ ^ 2 * r₂ ^ 2) (r₃ ^ 2)) /
        (2 * |c₁ * c₂ * (p₁ * q₂ - p₂ * q₁)|)) := by
  have hm : IsGreatest {x : ℝ | ∃ w₁ w₂ : ℂ,
      (‖w₁‖ ≤ r₁ ∧ ‖w₂‖ ≤ r₂ ∧ ‖(c₁ : ℂ) * w₁ + (c₂ : ℂ) * w₂‖ ≤ r₃) ∧
        x = (w₁ * conj w₂).im}
      (Real.sqrt (reactiveMax (c₁ ^ 2 * r₁ ^ 2) (c₂ ^ 2 * r₂ ^ 2) (r₃ ^ 2)) /
        (2 * |c₁ * c₂|)) := by
    simpa only [and_assoc] using isGreatest_im_mul_conj hc₁ hc₂ hr₁ hr₂ hr₃
  have hC : ∀ w₁ w₂ : ℂ,
      (‖w₁‖ ≤ r₁ ∧ ‖w₂‖ ≤ r₂ ∧ ‖(c₁ : ℂ) * w₁ + (c₂ : ℂ) * w₂‖ ≤ r₃) →
        (‖conj w₁‖ ≤ r₁ ∧ ‖conj w₂‖ ≤ r₂ ∧ ‖(c₁ : ℂ) * conj w₁ + (c₂ : ℂ) * conj w₂‖ ≤ r₃) := by
    intro w₁ w₂ hw
    have e : (c₁ : ℂ) * conj w₁ + (c₂ : ℂ) * conj w₂ = conj ((c₁ : ℂ) * w₁ + (c₂ : ℂ) * w₂) := by
      simp only [map_add, map_mul, Complex.conj_ofReal]
    rw [e, Complex.norm_conj, Complex.norm_conj, Complex.norm_conj]
    exact hw
  have e : ∀ z₁ z₂ : ℂ, (c₁ : ℂ) * ((p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂) +
      (c₂ : ℂ) * ((p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂) = (p₃ : ℂ) * z₁ + (q₃ : ℂ) * z₂ := by
    intro z₁ z₂
    rw [hp₃, hq₃]
    push_cast
    ring
  have h := isGreatest_im_of_change hδ hC hm
  simp only [e, and_assoc] at h
  rwa [div_div, mul_assoc, ← abs_mul] at h

/-- The largest cross term under three bounds in general position, in determinant form:
`√reactiveMax(d₂₃²r₁², d₃₁²r₂², d₁₂²r₃²)/(2|d₁₂d₂₃d₃₁|)` with `d_jk = p_jq_k − p_kq_j`. -/
def tripleMax (p₁ q₁ r₁ p₂ q₂ r₂ p₃ q₃ r₃ : ℝ) : ℝ :=
  Real.sqrt (reactiveMax ((p₂ * q₃ - p₃ * q₂) ^ 2 * r₁ ^ 2) ((p₃ * q₁ - p₁ * q₃) ^ 2 * r₂ ^ 2)
      ((p₁ * q₂ - p₂ * q₁) ^ 2 * r₃ ^ 2)) /
    (2 * |(p₁ * q₂ - p₂ * q₁) * (p₂ * q₃ - p₃ * q₂) * (p₃ * q₁ - p₁ * q₃)|)

/-- Three bounds with pairwise independent coefficient vectors (`d₁₂, d₂₃, d₃₁ ≠ 0`): the largest
cross term is `tripleMax`. -/
@[tmio T, powerlib_foundation] theorem isGreatest_tripleMax {p₁ q₁ r₁ p₂ q₂ r₂ p₃ q₃ r₃ : ℝ}
    (h₁₂ : p₁ * q₂ - p₂ * q₁ ≠ 0) (h₂₃ : p₂ * q₃ - p₃ * q₂ ≠ 0) (h₃₁ : p₃ * q₁ - p₁ * q₃ ≠ 0)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ, ‖(p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂‖ ≤ r₁ ∧
        ‖(p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂‖ ≤ r₂ ∧ ‖(p₃ : ℂ) * z₁ + (q₃ : ℂ) * z₂‖ ≤ r₃ ∧
          x = (z₁ * conj z₂).im} (tripleMax p₁ q₁ r₁ p₂ q₂ r₂ p₃ q₃ r₃) := by
  set d₁₂ := p₁ * q₂ - p₂ * q₁ with hd₁₂
  set d₂₃ := p₂ * q₃ - p₃ * q₂ with hd₂₃
  set d₃₁ := p₃ * q₁ - p₁ * q₃ with hd₃₁
  have ha : 0 < |d₁₂| := abs_pos.mpr h₁₂
  -- the third bound, scaled by `|d₁₂|`, in the coordinates `(w₁, w₂)`
  have hm : IsGreatest {x : ℝ | ∃ w₁ w₂ : ℂ,
      (‖w₁‖ ≤ r₁ ∧ ‖w₂‖ ≤ r₂ ∧ ‖(d₂₃ : ℂ) * w₁ + (d₃₁ : ℂ) * w₂‖ ≤ |d₁₂| * r₃) ∧
        x = (w₁ * conj w₂).im}
      (Real.sqrt (reactiveMax (d₂₃ ^ 2 * r₁ ^ 2) (d₃₁ ^ 2 * r₂ ^ 2) ((|d₁₂| * r₃) ^ 2)) /
        (2 * |d₂₃ * d₃₁|)) := by
    simpa only [and_assoc] using
      isGreatest_im_mul_conj h₂₃ h₃₁ hr₁ hr₂ (mul_nonneg ha.le hr₃)
  have hC : ∀ w₁ w₂ : ℂ,
      (‖w₁‖ ≤ r₁ ∧ ‖w₂‖ ≤ r₂ ∧ ‖(d₂₃ : ℂ) * w₁ + (d₃₁ : ℂ) * w₂‖ ≤ |d₁₂| * r₃) →
        (‖conj w₁‖ ≤ r₁ ∧ ‖conj w₂‖ ≤ r₂ ∧
          ‖(d₂₃ : ℂ) * conj w₁ + (d₃₁ : ℂ) * conj w₂‖ ≤ |d₁₂| * r₃) := by
    intro w₁ w₂ hw
    have e : (d₂₃ : ℂ) * conj w₁ + (d₃₁ : ℂ) * conj w₂ =
        conj ((d₂₃ : ℂ) * w₁ + (d₃₁ : ℂ) * w₂) := by
      simp only [map_add, map_mul, Complex.conj_ofReal]
    rw [e, Complex.norm_conj, Complex.norm_conj, Complex.norm_conj]
    exact hw
  -- `d₂₃ w₁ + d₃₁ w₂ = −d₁₂ (p₃z₁ + q₃z₂)`
  have e : ∀ z₁ z₂ : ℂ, ‖(d₂₃ : ℂ) * ((p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂) +
      (d₃₁ : ℂ) * ((p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂)‖ ≤ |d₁₂| * r₃ ↔
        ‖(p₃ : ℂ) * z₁ + (q₃ : ℂ) * z₂‖ ≤ r₃ := by
    intro z₁ z₂
    have hz : (d₂₃ : ℂ) * ((p₁ : ℂ) * z₁ + (q₁ : ℂ) * z₂) +
        (d₃₁ : ℂ) * ((p₂ : ℂ) * z₁ + (q₂ : ℂ) * z₂) =
          -((d₁₂ : ℂ) * ((p₃ : ℂ) * z₁ + (q₃ : ℂ) * z₂)) := by
      rw [hd₁₂, hd₂₃, hd₃₁]
      push_cast
      ring
    rw [hz, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_le_mul_iff_right₀ ha]
  have h := isGreatest_im_of_change h₁₂ hC hm
  simp only [e, and_assoc] at h
  have hv : Real.sqrt (reactiveMax (d₂₃ ^ 2 * r₁ ^ 2) (d₃₁ ^ 2 * r₂ ^ 2) ((|d₁₂| * r₃) ^ 2)) /
      (2 * |d₂₃ * d₃₁|) / |d₁₂| = tripleMax p₁ q₁ r₁ p₂ q₂ r₂ p₃ q₃ r₃ := by
    rw [tripleMax, ← hd₁₂, ← hd₂₃, ← hd₃₁, mul_pow, sq_abs, div_div, mul_assoc, ← abs_mul,
      mul_comm (d₂₃ * d₃₁) d₁₂, ← mul_assoc]
  rwa [hv] at h

end powerlib.SpecialFunctions
