import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import theorem.Attributes

/-! # Positive realness on the whole imaginary axis: polynomials in `ω²` on `[0, ∞)`

Along `s = jω` the Hermitian part of a real-rational port matrix has trace and determinant that
are even in `ω`, hence polynomials in `x = ω²`; positive realness at every frequency is then the
nonnegativity of those polynomials on `x ≥ 0`. This module decides it exactly, in the
coefficients, for degrees up to three.

Scope.
* Real polynomials of degree `≤ 3` on the closed half-line `x ≥ 0`, every real coefficient (the
  cubic law with `a > 0` as hypothesis, its combination `forall_nonneg_iff_halfLineNonneg`
  without); the cubic discriminant is Mathlib's `Cubic.discr`. No matrix, transfer or stability
  statement here; the port laws that reduce positive realness at `jω` to these signs are
  `theorem/PH/PositiveRealFinTwo.lean` and the port modules that read them.

Source: Descartes' rule of signs and the discriminant of the cubic (B. L. van der Waerden,
*Algebra*, vol. 1, §64; the critical values `(G ∓ 2 (b² − 3ac)^{3/2})/(27 a²)`,
`G = 2b³ − 9abc + 27a²d`, with `27 a² Δ = 4 (b² − 3ac)³ − G²`); positive realness along the
axis, work-sync `theory/T-ph.md` §1.10.

Results.
* `forall_sq_iff`: a property of `ω²` at every real `ω` is the property on `x ≥ 0`.
* `forall_nonneg_quadratic_iff`: `a x² + b x + c ≥ 0` on `x ≥ 0` iff `a ≥ 0`, `c ≥ 0` and
  (`b ≥ 0` or `b² ≤ 4ac`).
* `forall_nonneg_cubic_iff`: for `a > 0`, `a x³ + b x² + c x + d ≥ 0` on `x ≥ 0` iff `d ≥ 0` and
  either `b, c ≥ 0` (no sign change) or the discriminant `Δ ≤ 0` with `d > 0` or `c > 0`. Proof:
  a negative value at some `x₀ > 0` with `d > 0` gives three real roots (intermediate values on
  both sides), hence `Δ = a⁴ ∏ (rᵢ − rⱼ)² > 0`; conversely `Δ > 0` with `b < 0` or `c < 0` makes
  the cubic negative at its local minimum `x₊ = (−b + √(b² − 3ac))/(3a) > 0`.
* `HalfLineNonneg`, `forall_nonneg_iff_halfLineNonneg`: every leading coefficient at once
  (`a < 0` fails for large `x`, `a = 0` drops to the quadratic law).

Family and connection conclusions.
* None: real-algebraic static facts (public foundation).
-/

noncomputable section
namespace powerlib.PH

/-- A property of `ω²` at every real frequency is the property on the closed half-line
`x ≥ 0` (`x = ω²`, `ω = √x`). -/
@[tmio T, powerlib_foundation] theorem forall_sq_iff {P : ℝ → Prop} :
    (∀ ω : ℝ, P (ω ^ 2)) ↔ ∀ x : ℝ, 0 ≤ x → P x := by
  constructor
  · intro h x hx
    simpa [Real.sq_sqrt hx] using h (Real.sqrt x)
  · intro h ω
    exact h _ (sq_nonneg ω)

/-- A quadratic with `a ≥ 0` on `[0, ∞)`: nonnegative iff `c ≥ 0` and (`b ≥ 0` or `b² ≤ 4ac`). -/
@[tmio T, powerlib_foundation] private theorem forall_nonneg_quadratic_iff_of_nonneg {a b c : ℝ}
    (ha : 0 ≤ a) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ a * x ^ 2 + b * x + c) ↔ 0 ≤ c ∧ (0 ≤ b ∨ b ^ 2 ≤ 4 * a * c) := by
  constructor
  · intro h
    have hc : 0 ≤ c := by simpa using h 0 le_rfl
    refine ⟨hc, ?_⟩
    by_contra hb
    push Not at hb
    obtain ⟨hb0, hb4⟩ := hb
    rcases ha.lt_or_eq with ha' | ha'
    · have h1 := h (-b / (2 * a)) (div_nonneg (by linarith) (by linarith))
      have e : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = c - b ^ 2 / (4 * a) := by
        field_simp; ring
      rw [e, sub_nonneg, div_le_iff₀ (by positivity)] at h1
      linarith
    · have h1 := h ((c + 1) / (-b)) (div_nonneg (by linarith) (by linarith))
      have hb' : b ≠ 0 := hb0.ne
      have e : b * ((c + 1) / -b) = -(c + 1) := by field_simp
      rw [← ha', e] at h1
      linarith
  · rintro ⟨hc, hb | hb⟩ x hx
    · nlinarith [mul_nonneg ha (sq_nonneg x), mul_nonneg hb hx]
    · rcases ha.lt_or_eq with ha' | ha'
      · nlinarith [sq_nonneg (2 * a * x + b)]
      · rw [← ha'] at hb ⊢
        have : b = 0 := by nlinarith [sq_nonneg b]
        rw [this]; linarith

/-- A negative leading coefficient makes a quadratic negative far out on `[0, ∞)`:
at `X = 1 + (|b| + |c|)/(−a)`, `a X² + b X + c ≤ X (a X + |b| + |c|) = a X < 0`. -/
@[tmio T, powerlib_foundation] private theorem exists_neg_quadratic_of_neg {a b c : ℝ}
    (ha : a < 0) : ∃ x : ℝ, 0 ≤ x ∧ a * x ^ 2 + b * x + c < 0 := by
  set S := |b| + |c| with hS
  have hS0 : 0 ≤ S := by positivity
  have hq : 0 ≤ S / -a := div_nonneg hS0 (by linarith)
  set X := 1 + S / -a with hX
  have ha' : a ≠ 0 := ha.ne
  have hXa : a * X = a - S := by rw [hX]; field_simp; ring
  refine ⟨X, by linarith, ?_⟩
  have hX1 : 1 ≤ X := by linarith
  have h1 : b * X ≤ |b| * X := by nlinarith [le_abs_self b]
  have h2 : c ≤ |c| * X := by nlinarith [le_abs_self c, abs_nonneg c]
  nlinarith

/-- **A quadratic on `[0, ∞)`.** `a x² + b x + c ≥ 0` for every `x ≥ 0` iff `a ≥ 0`, `c ≥ 0` and
either `b ≥ 0` or `b² ≤ 4 a c` (a negative `a` fails far out,
`exists_neg_quadratic_of_neg`). -/
@[tmio T, powerlib_foundation] theorem forall_nonneg_quadratic_iff {a b c : ℝ} :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ a * x ^ 2 + b * x + c) ↔
      0 ≤ a ∧ 0 ≤ c ∧ (0 ≤ b ∨ b ^ 2 ≤ 4 * a * c) := by
  rcases lt_or_ge a 0 with ha | ha
  · obtain ⟨x, hx, hn⟩ := exists_neg_quadratic_of_neg (b := b) (c := c) ha
    exact ⟨fun h => absurd (h x hx) (not_le.mpr hn), fun h => absurd h.1 (not_le.mpr ha)⟩
  · rw [forall_nonneg_quadratic_iff_of_nonneg ha]
    exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

/-- Three distinct real roots of a cubic with `a ≠ 0` make its discriminant positive:
`Δ = (a² (r₁ − r₂)(r₁ − r₃)(r₂ − r₃))²` by Vieta (divided differences of the root equations). -/
@[tmio T, powerlib_foundation] private theorem cubic_three_roots {a b c d r₁ r₂ r₃ : ℝ}
    (ha : a ≠ 0) (h12 : r₁ < r₂) (h23 : r₂ < r₃)
    (e₁ : a * r₁ ^ 3 + b * r₁ ^ 2 + c * r₁ + d = 0)
    (e₂ : a * r₂ ^ 3 + b * r₂ ^ 2 + c * r₂ + d = 0)
    (e₃ : a * r₃ ^ 3 + b * r₃ ^ 2 + c * r₃ + d = 0) :
    0 < (⟨a, b, c, d⟩ : Cubic ℝ).discr := by
  have n12 : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr h12.ne
  have n23 : r₂ - r₃ ≠ 0 := sub_ne_zero.mpr h23.ne
  have n13 : r₁ - r₃ ≠ 0 := sub_ne_zero.mpr (h12.trans h23).ne
  have g12 : a * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) + b * (r₁ + r₂) + c = 0 := by
    apply mul_left_cancel₀ n12; linear_combination e₁ - e₂
  have g23 : a * (r₂ ^ 2 + r₂ * r₃ + r₃ ^ 2) + b * (r₂ + r₃) + c = 0 := by
    apply mul_left_cancel₀ n23; linear_combination e₂ - e₃
  have hb : b = -(a * (r₁ + r₂ + r₃)) := by
    apply mul_left_cancel₀ n13; linear_combination g12 - g23
  have hc : c = a * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) := by linear_combination g12 - (r₁ + r₂) * hb
  have hd : d = -(a * (r₁ * r₂ * r₃)) := by
    linear_combination e₁ - r₁ ^ 2 * hb - r₁ * hc
  have e : (⟨a, b, c, d⟩ : Cubic ℝ).discr = (a ^ 2 * (r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 := by
    simp only [Cubic.discr]; rw [hb, hc, hd]; ring
  rw [e]
  have : a ^ 2 * (r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃) ≠ 0 := by
    have := pow_ne_zero 2 ha
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero this n12) n13) n23
  positivity


/-- The cubic `p(x) = a x³ + b x² + c x + d` is continuous. -/
@[tmio T, powerlib_foundation] private theorem continuous_cubic (a b c d : ℝ) :
    Continuous fun x : ℝ => a * x ^ 3 + b * x ^ 2 + c * x + d := by fun_prop

/-- A negative value on `[0, ∞)` of a cubic with `a > 0`, `d > 0` forces three real roots, hence
a positive discriminant. -/
@[tmio T, powerlib_foundation] private theorem discr_pos_of_neg {a b c d x₀ : ℝ} (ha : 0 < a)
    (hd : 0 < d) (hx : 0 ≤ x₀) (hp : a * x₀ ^ 3 + b * x₀ ^ 2 + c * x₀ + d < 0) :
    0 < (⟨a, b, c, d⟩ : Cubic ℝ).discr := by
  have hcont := continuous_cubic a b c d
  set S := |b| + |c| + |d| with hS
  have hS0 : 0 ≤ S := by positivity
  have hb := neg_abs_le b
  have hc := neg_abs_le c
  have hd' := neg_abs_le d
  have hb' := le_abs_self b
  have hc' := le_abs_self c
  have hd'' := le_abs_self d
  -- a point to the right with `p ≥ 0`
  set X := x₀ + 1 + S / a with hX
  have hSa : S / a * a = S := div_mul_cancel₀ S ha.ne'
  have hX1 : 1 ≤ X := by have : 0 ≤ S / a := div_nonneg hS0 ha.le; linarith
  have hXa : S ≤ a * X := by
    have : 0 ≤ S / a := div_nonneg hS0 ha.le
    nlinarith
  have hpX : 0 ≤ a * X ^ 3 + b * X ^ 2 + c * X + d := by
    have hX2 : X ≤ X ^ 2 := by nlinarith
    have h1 : -(|b| * X ^ 2) ≤ b * X ^ 2 := by nlinarith [sq_nonneg X]
    have h2 : -(|c| * X ^ 2) ≤ c * X := by nlinarith [abs_nonneg c]
    have h3 : -(|d| * X ^ 2) ≤ d := by nlinarith [abs_nonneg d, sq_nonneg X]
    have h4 : 0 ≤ X ^ 2 * (a * X - S) := mul_nonneg (sq_nonneg X) (by linarith)
    nlinarith
  -- a point to the left with `p ≤ 0`
  set Y := -(1 + S / a) with hY
  have hY1 : Y ≤ -1 := by have : 0 ≤ S / a := div_nonneg hS0 ha.le; linarith
  have hYa : a * Y = -a - S := by rw [hY]; field_simp; ring
  have hpY : a * Y ^ 3 + b * Y ^ 2 + c * Y + d ≤ 0 := by
    have hY2 : -Y ≤ Y ^ 2 := by nlinarith
    have h1 : b * Y ^ 2 ≤ |b| * Y ^ 2 := by nlinarith [sq_nonneg Y]
    have h2 : c * Y ≤ |c| * Y ^ 2 := by nlinarith [abs_nonneg c]
    have h3 : d ≤ |d| * Y ^ 2 := by nlinarith [abs_nonneg d, sq_nonneg Y]
    have h4 : Y ^ 2 * (a * Y + S) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg Y) (by linarith)
    nlinarith
  have hx0 : 0 < x₀ := by
    rcases hx.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hp; simp at hp; linarith
  -- the three roots
  obtain ⟨r₁, ⟨hr₁a, hr₁b⟩, hr₁⟩ := intermediate_value_Icc (show Y ≤ 0 by linarith)
    hcont.continuousOn ⟨hpY, by simp; exact hd.le⟩
  obtain ⟨r₂, ⟨hr₂a, hr₂b⟩, hr₂⟩ := intermediate_value_Icc' hx hcont.continuousOn
    ⟨hp.le, by simp; exact hd.le⟩
  obtain ⟨r₃, ⟨hr₃a, hr₃b⟩, hr₃⟩ := intermediate_value_Icc (show x₀ ≤ X by
    have : 0 ≤ S / a := div_nonneg hS0 ha.le; linarith) hcont.continuousOn ⟨hp.le, hpX⟩
  simp only at hr₁ hr₂ hr₃
  have h1 : r₁ < r₂ := by
    have : r₁ ≠ 0 := by rintro rfl; simp at hr₁; linarith
    have : r₂ ≠ 0 := by rintro rfl; simp at hr₂; linarith
    have : r₁ < 0 := lt_of_le_of_ne hr₁b ‹_›
    have : 0 < r₂ := lt_of_le_of_ne hr₂a (Ne.symm ‹_›)
    linarith
  have h2 : r₂ < r₃ := by
    have : r₂ ≠ x₀ := by rintro rfl; linarith
    have : r₃ ≠ x₀ := by rintro rfl; linarith
    have : r₂ < x₀ := lt_of_le_of_ne hr₂b ‹_›
    have : x₀ < r₃ := lt_of_le_of_ne hr₃a (Ne.symm ‹_›)
    linarith
  exact cubic_three_roots ha.ne' h1 h2 hr₁ hr₂ hr₃

/-- With `a > 0`, a positive discriminant and a sign change `b < 0` or `c < 0`, the cubic is
negative at its local minimum `x₊ = (−b + √(b² − 3ac))/(3a) > 0`. -/
@[tmio T, powerlib_foundation] private theorem exists_neg_of_discr_pos {a b c d : ℝ} (ha : 0 < a)
    (hdisc : 0 < (⟨a, b, c, d⟩ : Cubic ℝ).discr) (hbc : b < 0 ∨ c < 0) :
    ∃ x, 0 ≤ x ∧ a * x ^ 3 + b * x ^ 2 + c * x + d < 0 := by
  set Δ := b ^ 2 - 3 * a * c with hΔ
  set G := 2 * b ^ 3 - 9 * a * b * c + 27 * a ^ 2 * d with hG
  have hid : 27 * a ^ 2 * (⟨a, b, c, d⟩ : Cubic ℝ).discr = 4 * Δ ^ 3 - G ^ 2 := by
    simp only [Cubic.discr, hΔ, hG]; ring
  have hΔ3 : G ^ 2 < 4 * Δ ^ 3 := by
    have : 0 < 27 * a ^ 2 * (⟨a, b, c, d⟩ : Cubic ℝ).discr := by positivity
    nlinarith [sq_nonneg G]
  have hΔ0 : 0 < Δ := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg G, mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg Δ)]
  set r := Real.sqrt Δ with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hΔ0
  have hr2 : r ^ 2 = Δ := Real.sq_sqrt hΔ0.le
  have hrb : b < r := by
    rcases hbc with hb | hc
    · linarith
    · have : b ^ 2 < r ^ 2 := by rw [hr2, hΔ]; nlinarith
      nlinarith [abs_lt_of_sq_lt_sq this hr0.le, le_abs_self b]
  set x := (-b + r) / (3 * a) with hxdef
  have hx3 : 3 * a * x = -b + r := by rw [hxdef]; field_simp
  have hval : 27 * a ^ 2 * (a * x ^ 3 + b * x ^ 2 + c * x + d) = G - 2 * r ^ 3 := by
    have e : 27 * a ^ 2 * (a * x ^ 3 + b * x ^ 2 + c * x + d) = (3 * a * x) ^ 3 +
        3 * b * (3 * a * x) ^ 2 + 9 * a * c * (3 * a * x) + 27 * a ^ 2 * d := by ring
    rw [e, hx3, hG]
    linear_combination (3 * r) * hr2
  have hG' : G < 2 * r ^ 3 := by
    have h6 : (2 * r ^ 3) ^ 2 = 4 * Δ ^ 3 := by rw [← hr2]; ring
    have := abs_lt_of_sq_lt_sq (a := G) (b := 2 * r ^ 3) (by rw [h6]; exact hΔ3) (by positivity)
    linarith [le_abs_self G]
  have h27 : 0 < 27 * a ^ 2 := by positivity
  refine ⟨x, div_nonneg (by linarith) (by linarith), ?_⟩
  by_contra hneg
  push Not at hneg
  nlinarith [mul_nonneg h27.le hneg]


/-- **A cubic on `[0, ∞)`.** For `a > 0`: `a x³ + b x² + c x + d ≥ 0` for every `x ≥ 0` iff
`d ≥ 0` and either `b, c ≥ 0` (no sign change) or the discriminant is `≤ 0` with `d > 0` or
`c > 0`. -/
@[tmio T, powerlib_foundation] theorem forall_nonneg_cubic_iff {a b c d : ℝ} (ha : 0 < a) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ a * x ^ 3 + b * x ^ 2 + c * x + d) ↔ 0 ≤ d ∧
      ((0 ≤ b ∧ 0 ≤ c) ∨ ((⟨a, b, c, d⟩ : Cubic ℝ).discr ≤ 0 ∧ (0 < d ∨ 0 < c))) := by
  have hd0 : ∀ {c : ℝ}, (⟨a, b, c, 0⟩ : Cubic ℝ).discr = c ^ 2 * (b ^ 2 - 4 * a * c) := by
    intro c; simp only [Cubic.discr]; ring
  constructor
  · intro h
    have hd : 0 ≤ d := by simpa using h 0 le_rfl
    refine ⟨hd, ?_⟩
    by_cases hbc : 0 ≤ b ∧ 0 ≤ c
    · exact Or.inl hbc
    right
    have hbc' : b < 0 ∨ c < 0 := by
      by_contra hn
      push Not at hn
      exact hbc hn
    have hdisc : (⟨a, b, c, d⟩ : Cubic ℝ).discr ≤ 0 := by
      by_contra hn
      push Not at hn
      obtain ⟨x, hx, hp⟩ := exists_neg_of_discr_pos ha hn hbc'
      exact absurd (h x hx) (not_le.mpr hp)
    refine ⟨hdisc, ?_⟩
    rcases hd.lt_or_eq with hd' | hd'
    · exact Or.inl hd'
    right
    subst hd'
    rw [hd0] at hdisc
    rcases lt_trichotomy c 0 with hc | hc | hc
    · exfalso
      have h1 : 0 < c ^ 2 := by nlinarith
      have h2 : 0 < b ^ 2 - 4 * a * c := by nlinarith [sq_nonneg b]
      linarith [mul_pos h1 h2]
    · exfalso
      subst hc
      have hb : b < 0 := by rcases hbc' with hb | hb; exact hb; exact absurd hb (lt_irrefl 0)
      have h1 := h (-b / (2 * a)) (div_nonneg (by linarith) (by linarith))
      have e : a * (-b / (2 * a)) ^ 3 + b * (-b / (2 * a)) ^ 2 + 0 * (-b / (2 * a)) + 0 =
          b ^ 3 / (8 * a ^ 2) := by
        field_simp; ring
      rw [e] at h1
      have hb2 : 0 < b ^ 2 := by nlinarith
      have hb3 : b ^ 3 < 0 := by nlinarith
      have : b ^ 3 / (8 * a ^ 2) < 0 := div_neg_of_neg_of_pos hb3 (by positivity)
      linarith
    · exact hc
  · rintro ⟨hd, ⟨hb, hc⟩ | ⟨hdisc, hdc⟩⟩ x hx
    · have : 0 ≤ x ^ 3 := pow_nonneg hx 3
      nlinarith [mul_nonneg ha.le this, mul_nonneg hb (sq_nonneg x), mul_nonneg hc hx]
    · rcases hd.lt_or_eq with hd' | hd'
      · by_contra hn
        push Not at hn
        exact absurd (discr_pos_of_neg ha hd' hx hn) (not_lt.mpr hdisc)
      · subst hd'
        have hc : 0 < c := by rcases hdc with h | h; exact absurd h (lt_irrefl 0); exact h
        rw [hd0] at hdisc
        have h4 : b ^ 2 ≤ 4 * a * c := by
          by_contra hn
          push Not at hn
          have h1 : 0 < c ^ 2 := by positivity
          have h2 : 0 < b ^ 2 - 4 * a * c := by linarith
          linarith [mul_pos h1 h2]
        have hq : 0 ≤ a * x ^ 2 + b * x + c := by nlinarith [sq_nonneg (2 * a * x + b)]
        nlinarith [mul_nonneg hx hq]


/-- A negative leading coefficient makes a cubic negative far out on `[0, ∞)`:
at `X = 1 + (|b| + |c| + |d|)/(−a)`, `p(X) ≤ X² (a X + |b| + |c| + |d|) = a X² < 0`. -/
@[tmio T, powerlib_foundation] private theorem exists_neg_cubic_of_neg {a b c d : ℝ}
    (ha : a < 0) : ∃ x : ℝ, 0 ≤ x ∧ a * x ^ 3 + b * x ^ 2 + c * x + d < 0 := by
  set S := |b| + |c| + |d| with hS
  have hS0 : 0 ≤ S := by positivity
  have hq : 0 ≤ S / -a := div_nonneg hS0 (by linarith)
  set X := 1 + S / -a with hX
  have ha' : a ≠ 0 := ha.ne
  have hXa : a * X = a - S := by rw [hX]; field_simp; ring
  refine ⟨X, by linarith, ?_⟩
  have hX1 : 1 ≤ X := by linarith
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have h1 : b * X ^ 2 ≤ |b| * X ^ 2 := by nlinarith [le_abs_self b, sq_nonneg X]
  have h2 : c * X ≤ |c| * X ^ 2 := by nlinarith [le_abs_self c, abs_nonneg c]
  have h3 : d ≤ |d| * X ^ 2 := by nlinarith [le_abs_self d, abs_nonneg d]
  have h4 : a * X ^ 3 = (a - S) * X ^ 2 := by rw [← hXa]; ring
  nlinarith [sq_nonneg X]

/-- The closed form of nonnegativity on `[0, ∞)` of `a x³ + b x² + c x + d`, every real `a`:
for `a > 0` the cubic condition of `forall_nonneg_cubic_iff`, for `a = 0` the quadratic
condition `b ≥ 0`, `d ≥ 0`, (`c ≥ 0` or `c² ≤ 4bd`); `a < 0` is excluded. -/
def HalfLineNonneg (P : Cubic ℝ) : Prop :=
  (0 < P.a ∧ 0 ≤ P.d ∧ ((0 ≤ P.b ∧ 0 ≤ P.c) ∨ (P.discr ≤ 0 ∧ (0 < P.d ∨ 0 < P.c)))) ∨
    (P.a = 0 ∧ 0 ≤ P.b ∧ 0 ≤ P.d ∧ (0 ≤ P.c ∨ P.c ^ 2 ≤ 4 * P.b * P.d))

/-- **A polynomial of degree `≤ 3` on `[0, ∞)`, every leading coefficient.**
`a x³ + b x² + c x + d ≥ 0` for every `x ≥ 0` iff `HalfLineNonneg ⟨a, b, c, d⟩`: a negative `a`
fails far out (`exists_neg_cubic_of_neg`), `a = 0` is `forall_nonneg_quadratic_iff`, `a > 0` is
`forall_nonneg_cubic_iff`. -/
@[tmio T, powerlib_foundation] theorem forall_nonneg_iff_halfLineNonneg (P : Cubic ℝ) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d) ↔ HalfLineNonneg P := by
  rcases lt_trichotomy P.a 0 with ha | ha | ha
  · obtain ⟨x, hx, hn⟩ := exists_neg_cubic_of_neg (b := P.b) (c := P.c) (d := P.d) ha
    refine ⟨fun h => absurd (h x hx) (not_le.mpr hn), ?_⟩
    rintro (⟨ha', -⟩ | ⟨ha', -⟩) <;> linarith
  · have e : ∀ x : ℝ, P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = P.b * x ^ 2 + P.c * x + P.d :=
      fun x => by rw [ha]; ring
    simp only [e]
    rw [forall_nonneg_quadratic_iff]
    simp only [HalfLineNonneg, ha, lt_irrefl, false_and, false_or, true_and]
  · have h := forall_nonneg_cubic_iff (b := P.b) (c := P.c) (d := P.d) ha
    simp only [HalfLineNonneg, ha, true_and, ha.ne', false_and, or_false]
    exact h

end powerlib.PH
