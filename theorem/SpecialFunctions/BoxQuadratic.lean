import theorem.Attributes
import dependencies.Mathlib

/-! # The largest quadratic form on a box and the largest Hermitian form on a bidisk (foundation)

The maximum of the real quadratic form `q(x, y) = a x² + b y² + 2 c x y` over the box
`0 ≤ x ≤ A`, `0 ≤ y ≤ B`, for `c ≥ 0` and any signs of `a` and `b`, in closed form
`boxQuadMax a b c A B`, and the maximum of the Hermitian form
`a ‖z₁‖² + b ‖z₂‖² + 2 Re(c z₁ z̄₂)` over the bidisk `‖z₁‖ ≤ A`, `‖z₂‖ ≤ B` (`c` complex), which is
`boxQuadMax a b ‖c‖ A B`. Last, the lift `(z₁, z₂) ↦ (‖z₁‖², ‖z₂‖², z₁ z̄₂)` of the bidisk: every
Hermitian form of `(z₁, z₂)` is an affine function of the lift, the lifted bidisk
`bidiskLift A B` is convex, and each of its points is realized by a point of the bidisk with the
same second and third coordinates and a smaller first one.

The form is homogeneous of degree two: if `q(x, y) > 0`, scaling `(x, y)` by `t ≥ 1` until it
meets the edge `x = A` or the edge `y = B` multiplies `q` by `t² ≥ 1`. So the maximum is `0` (the
origin) or the maximum on one of these two edges. On the edge `x = A` the form is the parabola
`a A² + 2 c A y + b y²` in `y ∈ [0, B]`; for `c, A ≥ 0` it is nondecreasing up to its vertex
`y = c A/(−b)` when `b < 0` and everywhere when `b ≥ 0`, so its maximum is at the vertex when
`b < 0` and the vertex lies below `B`, else at the corner `y = B` (`edgeQuadMax`). On the bidisk
`Re(c z₁ z̄₂) ≤ ‖c‖ ‖z₁‖ ‖z₂‖`, with equality when the phase of `z₁` cancels that of `c`.

Scope.
* Generic static real and complex algebra: closed-form maxima of quadratic and Hermitian forms
  of two variables on a box and on a bidisk, and the convex lift of the bidisk; no model family
  and no engineering object.

Source: elementary constrained optimization of a homogeneous quadratic form (scaling to the
boundary, the vertex of a parabola); the phase alignment of a complex product; the convexity of
the rotated second-order cone `‖w‖² ≤ U W`, from `‖w‖ ‖w'‖ ≤ √(U W' · U' W)` and AM–GM; no
paper.

Results.
* `edgeQuadMax a b c A B` (the largest `a A² + 2 c A y + b y²` over `0 ≤ y ≤ B`: the vertex value
  `A² (a − c²/b)` if `b < 0` and `c A < −b B`, else the corner value
  `a A² + 2 c A B + b B²`), `boxQuadMax a b c A B` (`max 0 (max (edgeQuadMax a b c A B)
  (edgeQuadMax b a c B A))`).
* `le_boxQuadMax` (for `c ≥ 0`, every point of the box has
  `a x² + b y² + 2 c x y ≤ boxQuadMax a b c A B`), `exists_eq_boxQuadMax` (for `c, A, B ≥ 0` a
  point of the box attains it), `isGreatest_boxQuadMax` (it is the greatest value of the form on
  the box).
* `hermitian_le_boxQuadMax` (on the bidisk,
  `a ‖z₁‖² + b ‖z₂‖² + 2 Re(c z₁ z̄₂) ≤ boxQuadMax a b ‖c‖ A B`), `exists_hermitian_eq_boxQuadMax`
  (for `A, B ≥ 0` a point of the bidisk attains it), `isGreatest_hermitian_boxQuadMax` (it is the
  greatest value of the Hermitian form on the bidisk).
* `bidiskLift A B` (the set `{(U, W, w) | 0 ≤ U ≤ A², 0 ≤ W ≤ B², ‖w‖² ≤ U W}`),
  `convex_bidiskLift` (it is convex), `lift_mem_bidiskLift` (the lift of a point of the bidisk
  lies in it), `exists_lift_of_mem_bidiskLift` (for `A, B ≥ 0` every `(U, W, w)` in it is
  realized by `z₁, z₂` in the bidisk with `‖z₁‖² ≤ U`, `‖z₂‖² = W`, `z₁ z̄₂ = w`).
-/

noncomputable section

namespace powerlib.SpecialFunctions

open ComplexConjugate

/-- The largest value of `a A² + 2 c A y + b y²` over `0 ≤ y ≤ B` (the edge `x = A` of the box,
for `c, A ≥ 0`): the vertex value `A² (a − c²/b)` at `y = c A/(−b)` when `b < 0` and the vertex
lies below `B`, else the corner value at `y = B`. -/
def edgeQuadMax (a b c A B : ℝ) : ℝ :=
  if b < 0 ∧ c * A < -b * B then A ^ 2 * (a - c ^ 2 / b)
  else a * A ^ 2 + 2 * c * A * B + b * B ^ 2

/-- The largest value of `a x² + b y² + 2 c x y` over the box `0 ≤ x ≤ A`, `0 ≤ y ≤ B`
(`c ≥ 0`): the origin or the best point of the edges `x = A` and `y = B`. -/
def boxQuadMax (a b c A B : ℝ) : ℝ :=
  max 0 (max (edgeQuadMax a b c A B) (edgeQuadMax b a c B A))

/-- On the edge `x = A`: `a A² + 2 c A y + b y² ≤ edgeQuadMax a b c A B` for `0 ≤ y ≤ B`. -/
@[tmio T, powerlib_foundation] private theorem edge_le {a b c A B y : ℝ} (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hy : 0 ≤ y) (hyB : y ≤ B) :
    a * A ^ 2 + 2 * c * A * y + b * y ^ 2 ≤ edgeQuadMax a b c A B := by
  unfold edgeQuadMax
  split_ifs with h
  · obtain ⟨hb, -⟩ := h
    have hb0 : b ≠ 0 := hb.ne
    have e : A ^ 2 * (a - c ^ 2 / b) - (a * A ^ 2 + 2 * c * A * y + b * y ^ 2) =
        -(c * A + b * y) ^ 2 / b := by
      field_simp
      ring
    have : 0 ≤ -(c * A + b * y) ^ 2 / b :=
      div_nonneg_of_nonpos (neg_nonpos.2 (sq_nonneg _)) hb.le
    linarith
  · have key : 0 ≤ (B - y) * (2 * c * A + b * (B + y)) := by
      apply mul_nonneg (by linarith)
      by_cases hb : b < 0
      · have : -b * B ≤ c * A := by
          by_contra h'
          exact h ⟨hb, lt_of_not_ge h'⟩
        nlinarith
      · nlinarith [mul_nonneg hc hA, not_lt.mp hb]
    nlinarith

/-- The edge maximum is attained: at the vertex `y = c A/(−b)` or at the corner `y = B`. -/
@[tmio T, powerlib_foundation] private theorem exists_edge_eq {a b c A B : ℝ} (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ y, 0 ≤ y ∧ y ≤ B ∧ a * A ^ 2 + 2 * c * A * y + b * y ^ 2 = edgeQuadMax a b c A B := by
  unfold edgeQuadMax
  split_ifs with h
  · obtain ⟨hb, hlt⟩ := h
    refine ⟨c * A / -b, div_nonneg (mul_nonneg hc hA) (by linarith), ?_, ?_⟩
    · rw [div_le_iff₀ (by linarith)]
      linarith
    · field_simp
      ring
  · exact ⟨B, hB, le_rfl, rfl⟩

/-- Scaling to the edge `x = A`: when `A y ≤ B x`, every point of the box has
`a x² + b y² + 2 c x y ≤ max 0 (edgeQuadMax a b c A B)`. -/
@[tmio T, powerlib_foundation] private theorem le_max_edge {a b c A B x y : ℝ} (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hxA : x ≤ A) (hy : 0 ≤ y) (hyB : y ≤ B) (hd : A * y ≤ B * x) :
    a * x ^ 2 + b * y ^ 2 + 2 * c * x * y ≤ max 0 (edgeQuadMax a b c A B) := by
  rcases le_or_gt (a * x ^ 2 + b * y ^ 2 + 2 * c * x * y) 0 with hq | hq
  · exact hq.trans (le_max_left _ _)
  refine le_max_of_le_right ?_
  have hA : 0 ≤ A := hx.trans hxA
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst hx0
    rcases eq_or_lt_of_le hA with hA0 | hA0
    · subst hA0
      have := edge_le (a := a) (b := b) hc le_rfl hy hyB
      nlinarith
    · have : y = 0 := le_antisymm (by nlinarith) hy
      subst this
      norm_num at hq
  · have ht : 1 ≤ A / x := by rw [le_div_iff₀ hx0]; linarith
    have hty : A / x * y ≤ B := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hx0]
      linarith
    have e := edge_le (a := a) (b := b) hc hA (mul_nonneg (by positivity) hy) hty
    have hAt : A = A / x * x := by field_simp
    have hs : a * A ^ 2 + 2 * c * A * (A / x * y) + b * (A / x * y) ^ 2 =
        (A / x) ^ 2 * (a * x ^ 2 + b * y ^ 2 + 2 * c * x * y) := by
      rw [hAt]
      field_simp
      ring
    have ht2 : 1 ≤ (A / x) ^ 2 := one_le_pow₀ ht
    nlinarith

/-- Every point of the box `0 ≤ x ≤ A`, `0 ≤ y ≤ B` has
`a x² + b y² + 2 c x y ≤ boxQuadMax a b c A B` (`c ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem le_boxQuadMax {a b c A B x y : ℝ} (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hxA : x ≤ A) (hy : 0 ≤ y) (hyB : y ≤ B) :
    a * x ^ 2 + b * y ^ 2 + 2 * c * x * y ≤ boxQuadMax a b c A B := by
  unfold boxQuadMax
  rcases le_total (A * y) (B * x) with hd | hd
  · exact (le_max_edge hc hx hxA hy hyB hd).trans (max_le_max le_rfl (le_max_left _ _))
  · have := le_max_edge (a := b) (b := a) hc hy hyB hx hxA hd
    calc a * x ^ 2 + b * y ^ 2 + 2 * c * x * y = b * y ^ 2 + a * x ^ 2 + 2 * c * y * x := by
          ring
      _ ≤ _ := this.trans (max_le_max le_rfl (le_max_right _ _))

/-- The maximum is attained: for `c, A, B ≥ 0` some point of the box has
`a x² + b y² + 2 c x y = boxQuadMax a b c A B`. -/
@[tmio T, powerlib_foundation] theorem exists_eq_boxQuadMax {a b c A B : ℝ} (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ x y, 0 ≤ x ∧ x ≤ A ∧ 0 ≤ y ∧ y ≤ B ∧
      a * x ^ 2 + b * y ^ 2 + 2 * c * x * y = boxQuadMax a b c A B := by
  obtain ⟨y₁, hy₁, hy₁B, e₁⟩ := exists_edge_eq (a := a) (b := b) hc hA hB
  obtain ⟨x₂, hx₂, hx₂A, e₂⟩ := exists_edge_eq (a := b) (b := a) hc hB hA
  unfold boxQuadMax
  rcases max_choice 0 (max (edgeQuadMax a b c A B) (edgeQuadMax b a c B A)) with h | h <;>
    rw [h]
  · exact ⟨0, 0, le_rfl, hA, le_rfl, hB, by ring⟩
  rcases max_choice (edgeQuadMax a b c A B) (edgeQuadMax b a c B A) with h' | h' <;> rw [h']
  · exact ⟨A, y₁, hA, le_rfl, hy₁, hy₁B, by rw [← e₁]; ring⟩
  · exact ⟨x₂, B, hx₂, hx₂A, hB, le_rfl, by rw [← e₂]; ring⟩

/-- `boxQuadMax a b c A B` is the greatest value of `a x² + b y² + 2 c x y` over the box
`0 ≤ x ≤ A`, `0 ≤ y ≤ B` (`c, A, B ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem isGreatest_boxQuadMax {a b c A B : ℝ} (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsGreatest {q | ∃ x y, 0 ≤ x ∧ x ≤ A ∧ 0 ≤ y ∧ y ≤ B ∧
        q = a * x ^ 2 + b * y ^ 2 + 2 * c * x * y} (boxQuadMax a b c A B) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, y, hx, hxA, hy, hyB, e⟩ := exists_eq_boxQuadMax (a := a) (b := b) hc hA hB
    exact ⟨x, y, hx, hxA, hy, hyB, e.symm⟩
  · rintro q ⟨x, y, hx, hxA, hy, hyB, rfl⟩
    exact le_boxQuadMax hc hx hxA hy hyB

/-! ## The Hermitian form on the bidisk -/

/-- On the bidisk `‖z₁‖ ≤ A`, `‖z₂‖ ≤ B`:
`a ‖z₁‖² + b ‖z₂‖² + 2 Re(c z₁ z̄₂) ≤ boxQuadMax a b ‖c‖ A B`. -/
@[tmio T, powerlib_foundation] theorem hermitian_le_boxQuadMax {a b A B : ℝ} {c z₁ z₂ : ℂ}
    (h₁ : ‖z₁‖ ≤ A) (h₂ : ‖z₂‖ ≤ B) :
    a * ‖z₁‖ ^ 2 + b * ‖z₂‖ ^ 2 + 2 * (c * z₁ * conj z₂).re ≤ boxQuadMax a b ‖c‖ A B := by
  have hre : (c * z₁ * conj z₂).re ≤ ‖c‖ * ‖z₁‖ * ‖z₂‖ := by
    calc (c * z₁ * conj z₂).re ≤ ‖c * z₁ * conj z₂‖ := Complex.re_le_norm _
      _ = ‖c‖ * ‖z₁‖ * ‖z₂‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]
  have := le_boxQuadMax (a := a) (b := b) (norm_nonneg c) (norm_nonneg z₁) h₁ (norm_nonneg z₂) h₂
  linarith

/-- A unit complex number that turns `c` real and nonnegative: `‖u‖ = 1`, `c u = ‖c‖`. -/
@[tmio T, powerlib_foundation] private theorem exists_phase (c : ℂ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ c * u = ‖c‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨1, norm_one, by simp⟩
  have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
  refine ⟨conj c / ‖c‖, ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr hc)]
  · rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring

/-- The bidisk maximum is attained: for `A, B ≥ 0` some `‖z₁‖ ≤ A`, `‖z₂‖ ≤ B` has
`a ‖z₁‖² + b ‖z₂‖² + 2 Re(c z₁ z̄₂) = boxQuadMax a b ‖c‖ A B`. -/
@[tmio T, powerlib_foundation] theorem exists_hermitian_eq_boxQuadMax {a b A B : ℝ} (c : ℂ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ z₁ z₂ : ℂ, ‖z₁‖ ≤ A ∧ ‖z₂‖ ≤ B ∧
      a * ‖z₁‖ ^ 2 + b * ‖z₂‖ ^ 2 + 2 * (c * z₁ * conj z₂).re = boxQuadMax a b ‖c‖ A B := by
  obtain ⟨x, y, hx, hxA, hy, hyB, e⟩ :=
    exists_eq_boxQuadMax (a := a) (b := b) (norm_nonneg c) hA hB
  obtain ⟨u, hu, hcu⟩ := exists_phase c
  have n₁ : ‖(x : ℂ) * u‖ = x := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  have n₂ : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
  refine ⟨x * u, y, n₁.symm ▸ hxA, n₂.symm ▸ hyB, ?_⟩
  have hre : (c * (x * u) * conj (y : ℂ)).re = ‖c‖ * x * y := by
    rw [Complex.conj_ofReal, show c * (x * u) * (y : ℂ) = (c * u) * x * y by ring, hcu]
    norm_cast
  rw [n₁, n₂, hre, ← e]
  ring

/-- `boxQuadMax a b ‖c‖ A B` is the greatest value of `a ‖z₁‖² + b ‖z₂‖² + 2 Re(c z₁ z̄₂)` over
the bidisk `‖z₁‖ ≤ A`, `‖z₂‖ ≤ B` (`A, B ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem isGreatest_hermitian_boxQuadMax {a b A B : ℝ} (c : ℂ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsGreatest {q | ∃ z₁ z₂ : ℂ, ‖z₁‖ ≤ A ∧ ‖z₂‖ ≤ B ∧
        q = a * ‖z₁‖ ^ 2 + b * ‖z₂‖ ^ 2 + 2 * (c * z₁ * conj z₂).re}
      (boxQuadMax a b ‖c‖ A B) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z₁, z₂, h₁, h₂, e⟩ := exists_hermitian_eq_boxQuadMax (a := a) (b := b) c hA hB
    exact ⟨z₁, z₂, h₁, h₂, e.symm⟩
  · rintro q ⟨z₁, z₂, h₁, h₂, rfl⟩
    exact hermitian_le_boxQuadMax h₁ h₂

/-! ## The convex lift of the bidisk -/

/-- The lifted bidisk `{(U, W, w) | 0 ≤ U ≤ A², 0 ≤ W ≤ B², ‖w‖² ≤ U W}`: the lifts
`(‖z₁‖², ‖z₂‖², z₁ z̄₂)` of the bidisk and the points they dominate in the first coordinate. -/
def bidiskLift (A B : ℝ) : Set (ℝ × ℝ × ℂ) :=
  {x | 0 ≤ x.1 ∧ x.1 ≤ A ^ 2 ∧ 0 ≤ x.2.1 ∧ x.2.1 ≤ B ^ 2 ∧ ‖x.2.2‖ ^ 2 ≤ x.1 * x.2.1}

/-- The lifted bidisk is convex. -/
@[tmio T, powerlib_foundation] theorem convex_bidiskLift (A B : ℝ) :
    Convex ℝ (bidiskLift A B) := by
  rintro ⟨U, W, z⟩ ⟨hU, hUA, hW, hWB, hz⟩ ⟨U', W', z'⟩ ⟨hU', hUA', hW', hWB', hz'⟩ a b ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at *
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · nlinarith
  · nlinarith
  set s := ‖z‖
  set s' := ‖z'‖
  have hs : 0 ≤ s := norm_nonneg _
  have hs' : 0 ≤ s' := norm_nonneg _
  -- `(s s')² ≤ (U W')(U' W) ≤ ((U W' + U' W)/2)²`
  have hprod : (s * s') ^ 2 ≤ (U * W') * (U' * W) := by
    calc (s * s') ^ 2 = s ^ 2 * s' ^ 2 := by ring
      _ ≤ (U * W) * (U' * W') := mul_le_mul hz hz' (by positivity) (by positivity)
      _ = (U * W') * (U' * W) := by ring
  have hsq : (2 * (s * s')) ^ 2 ≤ (U * W' + U' * W) ^ 2 := by
    nlinarith [sq_nonneg (U * W' - U' * W)]
  have key : 2 * (s * s') ≤ U * W' + U' * W :=
    (abs_le_of_sq_le_sq' hsq (by positivity)).2
  have hn : ‖a • z + b • z'‖ ≤ a * s + b * s' := by
    calc ‖a • z + b • z'‖ ≤ ‖a • z‖ + ‖b • z'‖ := norm_add_le _ _
      _ = a * s + b * s' := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have hn2 : ‖a • z + b • z'‖ ^ 2 ≤ (a * s + b * s') ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  refine hn2.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hz (sq_nonneg a),
    mul_le_mul_of_nonneg_left hz' (sq_nonneg b), mul_le_mul_of_nonneg_left key (mul_nonneg ha hb)]

/-- The lift `(‖z₁‖², ‖z₂‖², z₁ z̄₂)` of a point of the bidisk `‖z₁‖ ≤ A`, `‖z₂‖ ≤ B` lies in
the lifted bidisk. -/
@[tmio T, powerlib_foundation] theorem lift_mem_bidiskLift {A B : ℝ} {z₁ z₂ : ℂ}
    (h₁ : ‖z₁‖ ≤ A) (h₂ : ‖z₂‖ ≤ B) :
    (‖z₁‖ ^ 2, ‖z₂‖ ^ 2, z₁ * conj z₂) ∈ bidiskLift A B := by
  refine ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _) h₁ 2, sq_nonneg _,
    pow_le_pow_left₀ (norm_nonneg _) h₂ 2, ?_⟩
  rw [norm_mul, Complex.norm_conj, mul_pow]

/-- Every point `(U, W, w)` of the lifted bidisk (`A, B ≥ 0`) is realized by a point of the
bidisk: `‖z₁‖ ≤ A`, `‖z₂‖ ≤ B`, `‖z₁‖² ≤ U`, `‖z₂‖² = W` and `z₁ z̄₂ = w`. -/
@[tmio T, powerlib_foundation] theorem exists_lift_of_mem_bidiskLift {A B : ℝ}
    {x : ℝ × ℝ × ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : x ∈ bidiskLift A B) :
    ∃ z₁ z₂ : ℂ, ‖z₁‖ ≤ A ∧ ‖z₂‖ ≤ B ∧ ‖z₁‖ ^ 2 ≤ x.1 ∧ ‖z₂‖ ^ 2 = x.2.1 ∧
      z₁ * conj z₂ = x.2.2 := by
  obtain ⟨U, W, z⟩ := x
  obtain ⟨hU, hUA, hW, hWB, hz⟩ := hx
  simp only at *
  have hle : ∀ {v : ℂ} {r R : ℝ}, 0 ≤ R → ‖v‖ ^ 2 ≤ r → r ≤ R ^ 2 → ‖v‖ ≤ R := fun hR h h' =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp (h.trans h')
  rcases eq_or_lt_of_le hW with hW0 | hW0
  · subst hW0
    have : z = 0 := by
      rw [mul_zero] at hz
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hz (sq_nonneg _)))
    subst this
    refine ⟨0, 0, by simpa using hA, by simpa using hB, by simpa using hU, by simp, by simp⟩
  · set r := Real.sqrt W
    have hr : 0 < r := Real.sqrt_pos.mpr hW0
    have hr2 : r ^ 2 = W := Real.sq_sqrt hW
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have n₂ : ‖(r : ℂ)‖ ^ 2 = W := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hr2]
    have n₁ : ‖z / r‖ ^ 2 ≤ U := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_pow, hr2,
        div_le_iff₀ hW0]
      exact hz
    refine ⟨z / r, r, hle hA n₁ hUA, hle hB n₂.le hWB, n₁, n₂, ?_⟩
    rw [Complex.conj_ofReal, div_mul_cancel₀ _ hr']

end powerlib.SpecialFunctions
