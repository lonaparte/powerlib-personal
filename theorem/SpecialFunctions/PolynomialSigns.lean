import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Polynomial.Basic

/-! # Sign patterns, positive roots and the root zero of polynomials (foundation)

The number of positive real roots of a real polynomial from the signs of its coefficients
(Descartes' rule of signs, read from Mathlib), its parity from the signs of the leading and
constant coefficients, and the multiplicity of the root `0` from the two lowest coefficients;
and the step from such a count to the shape of a periodic function: a continuous periodic function
that takes no level three times within one period has exactly one local maximum and one local
minimum per period.

Scope.
* Pure algebra of polynomials (real ones, except the root-zero law over any commutative ring) and
  real analysis of one continuous periodic real function; no model and no family. Example users:
  an equilibrium count through the positive roots of a quartic
  (`theorem/GridTiedConverter/GFM/QVDroop.lean`,
  `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`), a double zero eigenvalue read
  from the characteristic polynomial (`theorem/GridTiedConverter/GFM/Bifurcation.lean`), the one
  maximum and one minimum per period of a quasi-static power characteristic whose levels are such
  counts (`QVDroop.existsUnique_isLocalMax_Ptilde`).

Source: Descartes' rule of signs (Mathlib `Polynomial.roots_countP_pos_le_signVariations`); the
parity law from the factorization `P = ∏ (X − r) · Q` over the positive roots `r` and the
intermediate value theorem for the factor `Q` without positive roots; the root-zero law from
Mathlib `Polynomial.le_rootMultiplicity_iff` and `Polynomial.X_pow_dvd_iff`; the extremum law from
the extreme value theorem on a compact period and the intermediate value theorem
(`intermediate_value_Ioo`): a level just below a second peak is crossed three times.

Results.
* `ncard_pos_isRoot_le_countP`: the number of distinct positive roots is at most the number of
  positive roots counted with multiplicity (`P ≠ 0`).
* `countP_pos_roots_le_two_of_quartic`: the quartic `a₄ X⁴ + a₃ X³ + a₂ X² + a₁ X + a₀` with
  `a₄ > 0`, `a₃ ≥ 0`, `a₀ ≥ 0` has at most two positive roots counted with multiplicity: its
  coefficient list has at most two sign variations (Descartes).
* `even_countP_pos_roots_iff`: for `P(0) ≠ 0` the number of positive roots counted with
  multiplicity is even iff the leading coefficient and `P(0)` have the same sign.
* `two_le_rootMultiplicity_zero_iff`: a nonzero polynomial over a commutative ring has the root
  `0` with multiplicity at least two iff its linear and constant coefficients vanish (`X² ∣ P`).
* `existsUnique_isLocalMax_of_levels`, `existsUnique_isLocalMin_of_levels`: a continuous
  `T`-periodic real function (`T > 0`) that takes no value at three points `x < y < z < x + T`
  has exactly one local maximum and exactly one local minimum in every window `[a, a + T)`; the
  local maximum is the global one.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Polynomial Filter

/-- The number of distinct positive roots is at most the number of positive roots counted with
multiplicity. -/
@[tmio T, powerlib_foundation] theorem ncard_pos_isRoot_le_countP {P : ℝ[X]} (hP : P ≠ 0) :
    {x : ℝ | 0 < x ∧ P.IsRoot x}.ncard ≤ P.roots.countP (0 < ·) := by
  classical
  have hset : {x : ℝ | 0 < x ∧ P.IsRoot x} = ↑(P.roots.filter (0 < ·)).toFinset := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_filter,
      mem_roots hP]
    exact and_comm
  rw [hset, Set.ncard_coe_finset, Multiset.countP_eq_card_filter]
  exact Multiset.toFinset_card_le _

/-- **A quartic sign pattern.** If `a₄ > 0`, `a₃ ≥ 0` and `a₀ ≥ 0`, the quartic
`a₄ X⁴ + a₃ X³ + a₂ X² + a₁ X + a₀` has at most two positive roots counted with multiplicity:
its coefficient list `(+, ≥ 0, ?, ?, ≥ 0)` has at most two sign variations
(`Polynomial.roots_countP_pos_le_signVariations`). -/
@[tmio T, powerlib_foundation] theorem countP_pos_roots_le_two_of_quartic {a₄ a₃ a₂ a₁ a₀ : ℝ}
    (h₄ : 0 < a₄) (h₃ : 0 ≤ a₃) (h₀ : 0 ≤ a₀) :
    (C a₄ * X ^ 4 + C a₃ * X ^ 3 + C a₂ * X ^ 2 + C a₁ * X + C a₀).roots.countP (0 < ·) ≤ 2 := by
  set P := C a₄ * X ^ 4 + C a₃ * X ^ 3 + C a₂ * X ^ 2 + C a₁ * X + C a₀ with hP
  have hdeg : P.natDegree = 4 := by rw [hP]; compute_degree!; exact h₄.ne'
  have hne : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hlist : P.coeffList = [a₄, a₃, a₂, a₁, a₀] := by
    rw [coeffList, withBotSucc_degree_eq_natDegree_add_one hne, hdeg]
    simp [hP, List.range_succ, coeff_X_pow, coeff_X, coeff_C]
  refine (roots_countP_pos_le_signVariations P).trans ?_
  rw [Polynomial.signVariations, hlist, ← List.signVariations_map_sign]
  have key : ∀ s₃ s₂ s₁ s₀ : SignType, s₃ ≠ -1 → s₀ ≠ -1 →
      List.signVariations [1, s₃, s₂, s₁, s₀] ≤ 2 := by decide
  have h₃' : SignType.sign a₃ ≠ -1 := by rw [Ne, sign_eq_neg_one_iff]; linarith
  have h₀' : SignType.sign a₀ ≠ -1 := by rw [Ne, sign_eq_neg_one_iff]; linarith
  simpa [sign_pos h₄] using key _ (SignType.sign a₂) (SignType.sign a₁) _ h₃' h₀'

/-- A real polynomial without positive roots and with `Q(0) ≠ 0`: `Q(0)` has the sign of the
leading coefficient (intermediate value theorem on `[0, x]` for large `x`). -/
@[tmio T, powerlib_foundation] private theorem mul_eval_zero_pos_of_no_pos_root {Q : ℝ[X]}
    (h0 : Q.eval 0 ≠ 0) (hpos : ∀ x, 0 < x → ¬ Q.IsRoot x) :
    0 < Q.leadingCoeff * Q.eval 0 := by
  wlog hl : 0 < Q.leadingCoeff generalizing Q
  · have hQ : Q ≠ 0 := by rintro rfl; simp at h0
    have hl' : Q.leadingCoeff < 0 :=
      lt_of_le_of_ne (not_lt.mp hl) (leadingCoeff_ne_zero.mpr hQ)
    have h := this (Q := -Q) (by simpa using h0)
      (fun x hx hr => hpos x hx (by simpa using hr)) (by rw [leadingCoeff_neg]; linarith)
    simpa [leadingCoeff_neg] using h
  refine mul_pos hl ((lt_or_gt_of_ne h0).resolve_left fun hneg => ?_)
  rcases Nat.eq_zero_or_pos Q.natDegree with hd | hd
  · rw [eq_C_of_natDegree_eq_zero hd] at hneg hl
    simp only [eval_C, leadingCoeff_C] at hneg hl
    linarith
  · have ht := tendsto_atTop_of_leadingCoeff_nonneg Q (natDegree_pos_iff_degree_pos.mp hd) hl.le
    obtain ⟨x, hx, hx0⟩ := ((ht.eventually (eventually_gt_atTop 0)).and
      (eventually_gt_atTop 0)).exists
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hx0.le Q.continuous.continuousOn
      ⟨hneg.le, hx.le⟩
    have hcpos : 0 < c := lt_of_le_of_ne hc.1 (by rintro rfl; exact h0 hc0)
    exact hpos c hcpos hc0

/-- **Parity of the positive roots.** For a real polynomial with `P(0) ≠ 0`, the number of
positive roots counted with multiplicity is even iff the leading coefficient and `P(0)` have the
same sign: `P = ∏ (X − r) · Q` over the positive roots `r`, `P(0) = (−1)ᵏ (∏ r) Q(0)` and `Q(0)`
has the sign of the leading coefficient. -/
@[tmio T, powerlib_foundation] theorem even_countP_pos_roots_iff {P : ℝ[X]} (h0 : P.eval 0 ≠ 0) :
    Even (P.roots.countP (0 < ·)) ↔ 0 < P.leadingCoeff * P.eval 0 := by
  classical
  have hP : P ≠ 0 := by rintro rfl; simp at h0
  set s := P.roots.filter (0 < ·) with hs
  have hmon : ((s.map fun a => X - C a).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  obtain ⟨Q, hQ⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hP s).mpr (Multiset.filter_le _ _)
  have hQ0 : Q ≠ 0 := by rintro rfl; rw [mul_zero] at hQ; exact hP hQ
  have hroots : P.roots = s + Q.roots := by
    rw [hQ, roots_mul (hQ ▸ hP), roots_multiset_prod_X_sub_C]
  have hcount : P.roots.countP (0 < ·) = Multiset.card s := by
    rw [hs, Multiset.countP_eq_card_filter]
  have hspos : ∀ a ∈ s, 0 < a := fun a ha => (Multiset.mem_filter.mp ha).2
  have hQpos : ∀ x, 0 < x → ¬ Q.IsRoot x := by
    intro x hx hr
    have hlt : 0 < Q.roots.countP (0 < ·) :=
      Multiset.countP_pos.mpr ⟨x, (mem_roots hQ0).mpr hr, hx⟩
    have hss : s.countP (0 < ·) = Multiset.card s := Multiset.countP_eq_card.mpr hspos
    have h := hcount
    rw [hroots, Multiset.countP_add, hss] at h
    omega
  have hlead : P.leadingCoeff = Q.leadingCoeff := by
    rw [hQ, leadingCoeff_mul, hmon.leadingCoeff, one_mul]
  have heval : P.eval 0 = (-1) ^ Multiset.card s * s.prod * Q.eval 0 := by
    rw [hQ, eval_mul, eval_multiset_prod, Multiset.map_map]
    have hm : (s.map ((eval 0) ∘ fun a => X - C a)) = s.map Neg.neg := by
      refine Multiset.map_congr rfl fun a _ => ?_
      simp
    rw [hm, Multiset.prod_map_neg]
  have hQe : Q.eval 0 ≠ 0 := by
    intro h
    rw [heval, h, mul_zero] at h0
    exact h0 rfl
  have hB := mul_eval_zero_pos_of_no_pos_root hQe hQpos
  have hA : 0 < s.prod := Multiset.prod_pos hspos
  have hfac : P.leadingCoeff * P.eval 0 =
      (-1) ^ Multiset.card s * (s.prod * (Q.leadingCoeff * Q.eval 0)) := by
    rw [hlead, heval]; ring
  rw [hcount, hfac]
  rcases Nat.even_or_odd (Multiset.card s) with he | ho
  · rw [he.neg_one_pow, one_mul]
    exact ⟨fun _ => mul_pos hA hB, fun _ => he⟩
  · rw [ho.neg_one_pow]
    refine ⟨fun he => absurd ho (Nat.not_odd_iff_even.mpr he), fun h => ?_⟩
    nlinarith [mul_pos hA hB]

/-- **A double root at zero.** A nonzero polynomial over a commutative ring has the root `0` with
multiplicity at least two iff its linear and constant coefficients vanish: `X² ∣ P`. -/
@[tmio T, powerlib_foundation] theorem two_le_rootMultiplicity_zero_iff {R : Type*} [CommRing R]
    {P : R[X]} (hP : P ≠ 0) : 2 ≤ P.rootMultiplicity 0 ↔ P.coeff 1 = 0 ∧ P.coeff 0 = 0 := by
  rw [le_rootMultiplicity_iff hP, map_zero, sub_zero, X_pow_dvd_iff]
  refine ⟨fun h => ⟨h 1 one_lt_two, h 0 two_pos⟩, fun ⟨h1, h0⟩ d hd => ?_⟩
  interval_cases d <;> assumption

/-! ## Extrema of a periodic function from its level sets -/

section Levels
open Set Topology

variable {f : ℝ → ℝ} {T : ℝ}

/-- A function `f` with `f ≤ c` on `(u, v)`, `u < v ≤ u + T`, that takes no level three times
within less than `T` lies strictly below `c` somewhere in `(u, v)`. -/
@[tmio T, powerlib_foundation] private theorem exists_lt_of_forall_le
    (h3 : ∀ x y z, x < y → y < z → z < x + T → f x = f y → f y = f z → False) {u v c : ℝ}
    (huv : u < v) (hv : v ≤ u + T) (hle : ∀ x ∈ Ioo u v, f x ≤ c) : ∃ z ∈ Ioo u v, f z < c := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have e : ∀ x ∈ Ioo u v, f x = c := fun x hx => le_antisymm (hle x hx) (h x hx)
  have m1 : u + (v - u) / 4 ∈ Ioo u v := ⟨by linarith, by linarith⟩
  have m2 : u + (v - u) / 2 ∈ Ioo u v := ⟨by linarith, by linarith⟩
  have m3 : u + 3 * (v - u) / 4 ∈ Ioo u v := ⟨by linarith, by linarith⟩
  exact h3 _ _ _ (by linarith) (by linarith) (by linarith) ((e _ m1).trans (e _ m2).symm)
    ((e _ m2).trans (e _ m3).symm)

/-- A dip on both sides of a peak within less than one period crosses a level three times. -/
@[tmio T, powerlib_foundation] private theorem false_of_dip (hf : Continuous f)
    (h3 : ∀ x y z, x < y → y < z → z < x + T → f x = f y → f y = f z → False)
    {y z₁ p z₂ : ℝ} (hy : y < z₁) (hz₁ : z₁ < p) (hp : p < z₂) (hz₂ : z₂ < y + T)
    (h₁ : f z₁ < f y) (h₂ : f z₂ < f y) (hyp : f y ≤ f p) : False := by
  set c := (max (f z₁) (f z₂) + f y) / 2
  have hc₁ : f z₁ < c := by have := le_max_left (f z₁) (f z₂); simp only [c]; linarith
  have hc₂ : f z₂ < c := by have := le_max_right (f z₁) (f z₂); simp only [c]; linarith
  have hcy : c < f y := by
    have := max_lt h₁ h₂; simp only [c]; linarith
  obtain ⟨t₁, ht₁, e₁⟩ := intermediate_value_Ioo' hy.le hf.continuousOn ⟨hc₁, hcy⟩
  obtain ⟨t₂, ht₂, e₂⟩ := intermediate_value_Ioo hz₁.le hf.continuousOn
    ⟨hc₁, hcy.trans_le hyp⟩
  obtain ⟨t₃, ht₃, e₃⟩ := intermediate_value_Ioo' hp.le hf.continuousOn
    ⟨hc₂, hcy.trans_le hyp⟩
  exact h3 t₁ t₂ t₃ (ht₁.2.trans ht₂.1) (ht₂.2.trans ht₃.1) (by linarith [ht₁.1, ht₃.2])
    (e₁.trans e₂.symm) (e₂.trans e₃.symm)

/-- **Extrema from level sets.** A continuous `T`-periodic function (`T > 0`) that takes no
level three times within less than one period, `x < y < z < x + T`, has exactly one local
maximum in every period window `[a, a + T)`: every local maximum is a global one (otherwise a
level just below it is crossed three times), and two global maxima in one window would make a
level just below the maximum be crossed three times. -/
@[tmio T, powerlib_foundation] theorem existsUnique_isLocalMax_of_levels (hf : Continuous f)
    (hper : Function.Periodic f T) (hT : 0 < T)
    (h3 : ∀ x y z, x < y → y < z → z < x + T → f x = f y → f y = f z → False)
    (a : ℝ) : ∃! x, x ∈ Ico a (a + T) ∧ IsLocalMax f x := by
  obtain ⟨xM, -, hM⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by linarith))
    hf.continuousOn (s := Icc a (a + T))
  obtain ⟨x₀, hx₀, e₀⟩ := hper.exists_mem_Ico hT xM a
  have hglob : ∀ x, f x ≤ f x₀ := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico hT x a
    rw [hxy, ← e₀]
    exact hM (Ico_subset_Icc_self hy)
  -- every local maximum is a global one
  have hval : ∀ y, IsLocalMax f y → f y = f x₀ := by
    intro y hy
    refine le_antisymm (hglob y) (not_lt.mp fun hlt => ?_)
    obtain ⟨p, hp, ep⟩ := hper.exists_mem_Ico hT x₀ y
    have hyp : y < p := lt_of_le_of_ne hp.1 (by rintro rfl; exact hlt.ne ep.symm)
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp hy
    have hball : ∀ x, |x - y| < ε → f x ≤ f y := fun x hx => hε' (by rwa [Real.dist_eq])
    obtain ⟨z₁, hz₁, hf₁⟩ := exists_lt_of_forall_le h3 (u := y) (v := min (y + ε) p) (c := f y)
      (lt_min (by linarith) hyp) ((min_le_right _ _).trans hp.2.le) fun x hx =>
        hball x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2.trans_le (min_le_left _ _)])
    obtain ⟨z₂, hz₂, hf₂⟩ := exists_lt_of_forall_le h3 (u := max (y + T - ε) p) (v := y + T)
      (c := f y) (max_lt (by linarith) hp.2) (by linarith [le_max_right (y + T - ε) p])
      fun x hx => by
        rw [← hper.sub_eq x]
        exact hball _ (by
          rw [abs_lt]; constructor <;> linarith [hx.2, (le_max_left (y + T - ε) p).trans_lt hx.1])
    exact false_of_dip hf h3 hz₁.1 (hz₁.2.trans_le (min_le_right _ _))
      ((le_max_right _ _).trans_lt hz₂.1) hz₂.2 hf₁ hf₂ (by rw [← ep]; exact hlt.le)
  refine ⟨x₀, ⟨hx₀, IsMaxOn.isLocalMax (fun x _ => hglob x) univ_mem⟩, ?_⟩
  -- two global maxima in one window are impossible
  have huniq : ∀ y₁ y₂, y₁ ∈ Ico a (a + T) → y₂ ∈ Ico a (a + T) → y₁ < y₂ →
      f y₁ = f x₀ → f y₂ = f x₀ → False := by
    intro y₁ y₂ h₁ h₂ hlt e₁ e₂
    have hb : ∀ x, f x ≤ f y₁ := fun x => e₁ ▸ hglob x
    obtain ⟨z₁, hz₁, hf₁⟩ := exists_lt_of_forall_le h3 hlt (by linarith [h₁.1, h₂.2])
      fun x _ => hb x
    obtain ⟨z₂, hz₂, hf₂⟩ := exists_lt_of_forall_le h3 (u := y₂) (v := y₁ + T)
      (by linarith [h₁.1, h₂.2]) (by linarith) fun x _ => hb x
    exact false_of_dip hf h3 hz₁.1 hz₁.2 hz₂.1 hz₂.2 hf₁ hf₂ (by rw [e₁, e₂])
  rintro y ⟨hy, hyl⟩
  rcases lt_trichotomy y x₀ with h | h | h
  · exact (huniq y x₀ hy hx₀ h (hval y hyl) rfl).elim
  · exact h
  · exact (huniq x₀ y hx₀ hy h rfl (hval y hyl)).elim

/-- **Extrema from level sets, minimum.** Under the same hypotheses there is exactly one local
minimum in every period window (`existsUnique_isLocalMax_of_levels` for `−f`). -/
@[tmio T, powerlib_foundation] theorem existsUnique_isLocalMin_of_levels (hf : Continuous f)
    (hper : Function.Periodic f T) (hT : 0 < T)
    (h3 : ∀ x y z, x < y → y < z → z < x + T → f x = f y → f y = f z → False)
    (a : ℝ) : ∃! x, x ∈ Ico a (a + T) ∧ IsLocalMin f x := by
  have h := existsUnique_isLocalMax_of_levels (f := fun x => -f x) hf.neg
    (fun x => by simp [hper x]) hT
    (fun x y z hxy hyz hzx e₁ e₂ => h3 x y z hxy hyz hzx (neg_inj.mp e₁) (neg_inj.mp e₂)) a
  have hiff : ∀ x, IsLocalMax (fun x => -f x) x ↔ IsLocalMin f x :=
    fun x => ⟨fun h => by simpa using h.neg, fun h => h.neg⟩
  simpa only [hiff] using h

end Levels

end powerlib.SpecialFunctions
