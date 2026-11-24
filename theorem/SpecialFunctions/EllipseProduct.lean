import theorem.Attributes
import dependencies.Mathlib
import theorem.SpecialFunctions.ProductBound
import theorem.SpecialFunctions.Helly

/-! # The largest product under two ellipses, and on a box cut by two ellipses (foundation)

The maximum of `a · b` over `a, b ≥ 0` under two filled ellipses `p₁² a² + q₁² b² ≤ K₁` and
`p₂² a² + q₂² b² ≤ K₂` (`p_k, q_k > 0`), in closed piecewise form `ellipseMax`, and the maximum over
the box `0 ≤ a ≤ A`, `0 ≤ b ≤ B` cut by both ellipses, `boxEllipseMax`, each together with a point
that attains it.

In the squared coordinates `x = a²`, `y = b²` the ellipses are the half-planes
`p_k² x + q_k² y ≤ K_k` and the objective is `a · b = √(x y)`. The optimum of the first ellipse
alone is `p₁² x = q₁² y = K₁/2`, with value `K₁/(2 p₁ q₁)`; if it satisfies the second ellipse,
`p₂² K₁/(2p₁²) + q₂² K₁/(2q₁²) ≤ K₂`, it is the answer (first branch), and symmetrically with the
roles exchanged (second branch). Otherwise both ellipses bind: the boundary lines cross at
`x× = (K₁q₂² − K₂q₁²)/δ`, `y× = (p₁²K₂ − p₂²K₁)/δ` with `δ = p₁²q₂² − p₂²q₁² ≠ 0`, and the value is
`√(x× y×)` (third branch). Its certificate is a positive combination `ν₁ E₁ + ν₂ E₂` of the two
constraints, with `ν₁ = K₂(p₁²q₂² + p₂²q₁²) − 2p₂²q₂²K₁` and `ν₂ = K₁(p₁²q₂² + p₂²q₁²) − 2p₁²q₁²K₂`:
these are positive exactly because neither single-ellipse optimum satisfies the other ellipse, and
the combined half-plane `P x + Q y ≤ K` (`P = ν₁p₁² + ν₂p₂²`, `Q = ν₁q₁² + ν₂q₂²`,
`K = ν₁K₁ + ν₂K₂`) touches the hyperbola `x y = x× y×` at the crossing point, `P x× = Q y×`, so
AM–GM, `4 P Q x y ≤ (P x + Q y)² ≤ K² = 4 P Q x× y×`, bounds every feasible point.
Two proportional ellipses are nested, so one of the first two branches applies to them.

With the box, `boxEllipseMax` is the smallest of three relaxations: the box with the first ellipse
and the box with the second (`productMax` of `theorem/SpecialFunctions/ProductBound.lean`), and the
two ellipses without the box (`ellipseMax`). The smallest relaxation is attained: in the plane of
`(x, y)` the box, the two half-planes and the superlevel set `{x, y ≥ 0, x y ≥ s²}` (convex: for two
of its points, `x y' + x' y ≥ 2 √(x y x' y') ≥ 2 s²`) are four convex sets of which every three
meet, at the origin or at the optimizer of a relaxation, so by Helly's theorem all four meet.

Scope.
* Generic static real algebra and planar convexity: two piecewise functions of real parameters
  and the constrained maxima they record; nothing here describes a physical system and no model
  family is defined.

Source: elementary constrained optimization — AM–GM on a positive combination of the two
constraints (the Lagrange multipliers of the crossing point), and Helly's theorem in the drop-one
form `nonempty_iInter_of_drop_one` of `theorem/SpecialFunctions/Helly.lean`, applied to the
box–ellipse optimum `isGreatest_productMax` of `theorem/SpecialFunctions/ProductBound.lean`; no
paper.

Results.
* `ellipseFeasible p₁ q₁ K₁ p₂ q₂ K₂`: the feasible set
  `{(a, b) | 0 ≤ a, 0 ≤ b, p₁² a² + q₁² b² ≤ K₁, p₂² a² + q₂² b² ≤ K₂}`.
* `ellipseMax p₁ q₁ K₁ p₂ q₂ K₂`: the piecewise maximum of `a · b` over it (definition).
* `mul_le_ellipseMax`: for `p_k, q_k > 0`, every real `(a, b)` with
  `p_k² a² + q_k² b² ≤ K_k` (`k = 1, 2`) has `a · b ≤ ellipseMax p₁ q₁ K₁ p₂ q₂ K₂`.
* `exists_mul_eq_ellipseMax`: for `p_k, q_k > 0`, `K_k ≥ 0`, some point of `ellipseFeasible`
  attains `ellipseMax`.
* `isGreatest_ellipseMax`: for `p_k, q_k > 0`, `K_k ≥ 0`, `ellipseMax` is the greatest element of
  the image of `ellipseFeasible` under `(a, b) ↦ a · b`.
* `ellipseMax_nonneg`: for `p_k, q_k > 0`, `K_k ≥ 0`, `0 ≤ ellipseMax`.
* `boxEllipseFeasible p₁ q₁ K₁ p₂ q₂ K₂ A B`: the box `[0, A] × [0, B]` cut by both ellipses.
* `boxEllipseMax p₁ q₁ K₁ p₂ q₂ K₂ A B`: the smallest of `productMax p₁ q₁ K₁ A B`,
  `productMax p₂ q₂ K₂ A B` and `ellipseMax p₁ q₁ K₁ p₂ q₂ K₂` (definition).
* `mul_le_boxEllipseMax`: for `p_k, q_k > 0`, every point of `boxEllipseFeasible` has
  `a · b ≤ boxEllipseMax`.
* `exists_mul_eq_boxEllipseMax`: for `p_k, q_k > 0`, `K_k, A, B ≥ 0`, some point of
  `boxEllipseFeasible` attains `boxEllipseMax`.
* `isGreatest_boxEllipseMax`: for `p_k, q_k > 0`, `K_k, A, B ≥ 0`, `boxEllipseMax` is the greatest
  element of the image of `boxEllipseFeasible` under `(a, b) ↦ a · b`.
* `boxEllipseMax_nonneg`: for `p_k, q_k > 0`, `K_k, A, B ≥ 0`, `0 ≤ boxEllipseMax`.
-/

noncomputable section
namespace powerlib.SpecialFunctions

/-- The closed first quadrant cut by the filled ellipses `p₁² a² + q₁² b² ≤ K₁` and
`p₂² a² + q₂² b² ≤ K₂`. -/
def ellipseFeasible (p₁ q₁ K₁ p₂ q₂ K₂ : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ p₁ ^ 2 * x.1 ^ 2 + q₁ ^ 2 * x.2 ^ 2 ≤ K₁ ∧
    p₂ ^ 2 * x.1 ^ 2 + q₂ ^ 2 * x.2 ^ 2 ≤ K₂}

/-- The largest product `a · b` over `ellipseFeasible`: the optimum of one ellipse when it
satisfies the other, otherwise `√(x× y×)` at the crossing `(x×, y×)` of the two boundaries in the
squared coordinates `(a², b²)`. -/
def ellipseMax (p₁ q₁ K₁ p₂ q₂ K₂ : ℝ) : ℝ :=
  if p₂ ^ 2 * (K₁ / (2 * p₁ ^ 2)) + q₂ ^ 2 * (K₁ / (2 * q₁ ^ 2)) ≤ K₂ then K₁ / (2 * p₁ * q₁)
  else if p₁ ^ 2 * (K₂ / (2 * p₂ ^ 2)) + q₁ ^ 2 * (K₂ / (2 * q₂ ^ 2)) ≤ K₁ then
    K₂ / (2 * p₂ * q₂)
  else Real.sqrt ((K₁ * q₂ ^ 2 - K₂ * q₁ ^ 2) / (p₁ ^ 2 * q₂ ^ 2 - p₂ ^ 2 * q₁ ^ 2) *
    ((p₁ ^ 2 * K₂ - p₂ ^ 2 * K₁) / (p₁ ^ 2 * q₂ ^ 2 - p₂ ^ 2 * q₁ ^ 2)))

/-- AM–GM on a tangent half-plane: if `P X = Q Y` and `P X + Q Y = K`, every `x, y ≥ 0` with
`P x + Q y ≤ K` has `x y ≤ X Y`. -/
@[tmio T, powerlib_foundation] private theorem mul_le_of_tangent {P Q K X Y x y : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : P * x + Q * y ≤ K)
    (hK : P * X + Q * Y = K) (ht : P * X = Q * Y) : x * y ≤ X * Y := by
  have h1 : 4 * (P * Q) * (x * y) ≤ (P * x + Q * y) ^ 2 := by
    nlinarith [sq_nonneg (P * x - Q * y)]
  have h2 : (P * x + Q * y) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have h3 : K ^ 2 = 4 * (P * Q) * (X * Y) := by
    rw [← hK]
    linear_combination (P * X - Q * Y) * ht
  exact le_of_mul_le_mul_left (show 4 * (P * Q) * (x * y) ≤ 4 * (P * Q) * (X * Y) by linarith)
    (by positivity)

/-- The optimum `P₁ x = Q₁ y = K₁/2` of the first half-plane alone violates the second one:
`2 P₁ Q₁ K₂ < K₁ (P₁ Q₂ + P₂ Q₁)`. -/
@[tmio T, powerlib_foundation] private theorem pos_of_not_le {P₁ Q₁ K₁ P₂ Q₂ K₂ : ℝ}
    (hP₁ : 0 < P₁) (hQ₁ : 0 < Q₁)
    (h : ¬ P₂ * (K₁ / (2 * P₁)) + Q₂ * (K₁ / (2 * Q₁)) ≤ K₂) :
    0 < K₁ * (P₁ * Q₂ + P₂ * Q₁) - 2 * P₁ * Q₁ * K₂ := by
  have e : P₂ * (K₁ / (2 * P₁)) + Q₂ * (K₁ / (2 * Q₁)) =
      K₁ * (P₁ * Q₂ + P₂ * Q₁) / (2 * P₁ * Q₁) := by
    field_simp
    ring
  rw [e, not_le, lt_div_iff₀ (by positivity)] at h
  linarith

/-- When neither single optimum is feasible for the other half-plane, the two boundary lines are
not parallel: `P₁ Q₂ − P₂ Q₁ ≠ 0`. -/
@[tmio T, powerlib_foundation] private theorem cross_ne {P₁ Q₁ K₁ P₂ Q₂ K₂ : ℝ}
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hn₁ : 0 < K₂ * (P₂ * Q₁ + P₁ * Q₂) - 2 * P₂ * Q₂ * K₁)
    (hn₂ : 0 < K₁ * (P₁ * Q₂ + P₂ * Q₁) - 2 * P₁ * Q₁ * K₂) :
    P₁ * Q₂ - P₂ * Q₁ ≠ 0 := by
  intro hδ
  have e : P₁ * (K₂ * (P₂ * Q₁ + P₁ * Q₂) - 2 * P₂ * Q₂ * K₁) +
      P₂ * (K₁ * (P₁ * Q₂ + P₂ * Q₁) - 2 * P₁ * Q₁ * K₂) =
      (P₁ * Q₂ - P₂ * Q₁) * (P₁ * K₂ - P₂ * K₁) := by ring
  rw [hδ, zero_mul] at e
  linarith [mul_pos hP₁ hn₁, mul_pos hP₂ hn₂]

/-- The crossing point `(X, Y)` of the two boundary lines lies on both, bounds the product of
every point under both half-planes, and is in the closed quadrant when `K₁, K₂ ≥ 0`. The
certificate is the combination with the multipliers `ν₁`, `ν₂` (the positive numbers `hn₁`,
`hn₂`), which is tangent to `x y = X Y` at `(X, Y)`. -/
@[tmio T, powerlib_foundation] private theorem cross {P₁ Q₁ K₁ P₂ Q₂ K₂ X Y : ℝ}
    (hP₁ : 0 < P₁) (hQ₁ : 0 < Q₁) (hP₂ : 0 < P₂) (hQ₂ : 0 < Q₂)
    (hn₁ : 0 < K₂ * (P₂ * Q₁ + P₁ * Q₂) - 2 * P₂ * Q₂ * K₁)
    (hn₂ : 0 < K₁ * (P₁ * Q₂ + P₂ * Q₁) - 2 * P₁ * Q₁ * K₂)
    (hX : (P₁ * Q₂ - P₂ * Q₁) * X = K₁ * Q₂ - K₂ * Q₁)
    (hY : (P₁ * Q₂ - P₂ * Q₁) * Y = P₁ * K₂ - P₂ * K₁) :
    P₁ * X + Q₁ * Y = K₁ ∧ P₂ * X + Q₂ * Y = K₂ ∧ (0 ≤ K₁ → 0 ≤ K₂ → 0 ≤ X ∧ 0 ≤ Y) ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → P₁ * x + Q₁ * y ≤ K₁ → P₂ * x + Q₂ * y ≤ K₂ →
        x * y ≤ X * Y := by
  have hδ := cross_ne hP₁ hP₂ hn₁ hn₂
  set ν₁ := K₂ * (P₂ * Q₁ + P₁ * Q₂) - 2 * P₂ * Q₂ * K₁
  set ν₂ := K₁ * (P₁ * Q₂ + P₂ * Q₁) - 2 * P₁ * Q₁ * K₂
  have hl₁ : P₁ * X + Q₁ * Y = K₁ :=
    mul_left_cancel₀ hδ (by linear_combination P₁ * hX + Q₁ * hY)
  have hl₂ : P₂ * X + Q₂ * Y = K₂ :=
    mul_left_cancel₀ hδ (by linear_combination P₂ * hX + Q₂ * hY)
  have hP : 0 < ν₁ * P₁ + ν₂ * P₂ := by positivity
  have hQ : 0 < ν₁ * Q₁ + ν₂ * Q₂ := by positivity
  have hK : (ν₁ * P₁ + ν₂ * P₂) * X + (ν₁ * Q₁ + ν₂ * Q₂) * Y = ν₁ * K₁ + ν₂ * K₂ := by
    linear_combination ν₁ * hl₁ + ν₂ * hl₂
  have ht : (ν₁ * P₁ + ν₂ * P₂) * X = (ν₁ * Q₁ + ν₂ * Q₂) * Y := by
    linear_combination ((P₁ * Q₂ - P₂ * Q₁) * Y) * hX - ((P₁ * Q₂ - P₂ * Q₁) * X) * hY
  refine ⟨hl₁, hl₂, fun hK₁ hK₂ => ?_, fun x y hx hy h₁ h₂ => ?_⟩
  · have hK0 : 0 ≤ ν₁ * K₁ + ν₂ * K₂ := by positivity
    constructor
    · by_contra hneg
      have : (ν₁ * P₁ + ν₂ * P₂) * X < 0 := mul_neg_of_pos_of_neg hP (lt_of_not_ge hneg)
      linarith
    · by_contra hneg
      have : (ν₁ * Q₁ + ν₂ * Q₂) * Y < 0 := mul_neg_of_pos_of_neg hQ (lt_of_not_ge hneg)
      linarith
  · refine mul_le_of_tangent hP hQ hx hy ?_ hK ht
    nlinarith [mul_le_mul_of_nonneg_left h₁ hn₁.le, mul_le_mul_of_nonneg_left h₂ hn₂.le]

/-- Every real `(a, b)` under both ellipses has product at most `ellipseMax`. -/
@[tmio T, powerlib_foundation] theorem mul_le_ellipseMax {p₁ q₁ K₁ p₂ q₂ K₂ a b : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂)
    (h₁ : p₁ ^ 2 * a ^ 2 + q₁ ^ 2 * b ^ 2 ≤ K₁) (h₂ : p₂ ^ 2 * a ^ 2 + q₂ ^ 2 * b ^ 2 ≤ K₂) :
    a * b ≤ ellipseMax p₁ q₁ K₁ p₂ q₂ K₂ := by
  unfold ellipseMax
  split_ifs with hc₁ hc₂
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p₁ * a - q₁ * b)]
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p₂ * a - q₂ * b)]
  · have hn₂ := pos_of_not_le (pow_pos hp₁ 2) (pow_pos hq₁ 2) hc₁
    have hn₁ := pos_of_not_le (pow_pos hp₂ 2) (pow_pos hq₂ 2) hc₂
    have hδ := cross_ne (pow_pos hp₁ 2) (pow_pos hp₂ 2) hn₁ hn₂
    obtain ⟨-, -, -, hle⟩ := cross (pow_pos hp₁ 2) (pow_pos hq₁ 2) (pow_pos hp₂ 2)
      (pow_pos hq₂ 2) hn₁ hn₂ (mul_div_cancel₀ _ hδ) (mul_div_cancel₀ _ hδ)
    have hab := hle (a ^ 2) (b ^ 2) (sq_nonneg a) (sq_nonneg b) h₁ h₂
    rw [← mul_pow] at hab
    exact (le_abs_self _).trans (Real.abs_le_sqrt hab)

/-- The point `(√X, √Y)` has squares `X`, `Y` and product `√(X Y)`. -/
@[tmio T, powerlib_foundation] private theorem exists_sq_point {X Y : ℝ} (hX : 0 ≤ X)
    (hY : 0 ≤ Y) : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ^ 2 = X ∧ b ^ 2 = Y ∧
      a * b = Real.sqrt (X * Y) :=
  ⟨Real.sqrt X, Real.sqrt Y, Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sq_sqrt hX,
    Real.sq_sqrt hY, (Real.sqrt_mul hX Y).symm⟩

/-- The optimum of one ellipse alone, `p² a² = q² b² = K/2`, has product `K/(2 p q)`. -/
@[tmio T, powerlib_foundation] private theorem sqrt_single {p q K : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hK : 0 ≤ K) : Real.sqrt (K / (2 * p ^ 2) * (K / (2 * q ^ 2))) = K / (2 * p * q) := by
  rw [show K / (2 * p ^ 2) * (K / (2 * q ^ 2)) = (K / (2 * p * q)) ^ 2 by field_simp]
  exact Real.sqrt_sq (by positivity)

/-- Some point under both ellipses attains `ellipseMax`. -/
@[tmio T, powerlib_foundation] theorem exists_mul_eq_ellipseMax {p₁ q₁ K₁ p₂ q₂ K₂ : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    ∃ x ∈ ellipseFeasible p₁ q₁ K₁ p₂ q₂ K₂, x.1 * x.2 = ellipseMax p₁ q₁ K₁ p₂ q₂ K₂ := by
  unfold ellipseMax
  split_ifs with hc₁ hc₂
  · obtain ⟨a, b, ha, hb, ha2, hb2, hab⟩ :=
      exists_sq_point (X := K₁ / (2 * p₁ ^ 2)) (Y := K₁ / (2 * q₁ ^ 2)) (by positivity)
        (by positivity)
    refine ⟨(a, b), ⟨ha, hb, ?_, ?_⟩, ?_⟩
    · show p₁ ^ 2 * a ^ 2 + q₁ ^ 2 * b ^ 2 ≤ K₁
      rw [ha2, hb2]
      field_simp
      linarith
    · show p₂ ^ 2 * a ^ 2 + q₂ ^ 2 * b ^ 2 ≤ K₂
      rw [ha2, hb2]
      exact hc₁
    · rw [show (a, b).1 * (a, b).2 = a * b from rfl, hab, sqrt_single hp₁ hq₁ hK₁]
  · obtain ⟨a, b, ha, hb, ha2, hb2, hab⟩ :=
      exists_sq_point (X := K₂ / (2 * p₂ ^ 2)) (Y := K₂ / (2 * q₂ ^ 2)) (by positivity)
        (by positivity)
    refine ⟨(a, b), ⟨ha, hb, ?_, ?_⟩, ?_⟩
    · show p₁ ^ 2 * a ^ 2 + q₁ ^ 2 * b ^ 2 ≤ K₁
      rw [ha2, hb2]
      exact hc₂
    · show p₂ ^ 2 * a ^ 2 + q₂ ^ 2 * b ^ 2 ≤ K₂
      rw [ha2, hb2]
      field_simp
      linarith
    · rw [show (a, b).1 * (a, b).2 = a * b from rfl, hab, sqrt_single hp₂ hq₂ hK₂]
  · have hn₂ := pos_of_not_le (pow_pos hp₁ 2) (pow_pos hq₁ 2) hc₁
    have hn₁ := pos_of_not_le (pow_pos hp₂ 2) (pow_pos hq₂ 2) hc₂
    have hδ := cross_ne (pow_pos hp₁ 2) (pow_pos hp₂ 2) hn₁ hn₂
    obtain ⟨hl₁, hl₂, hnn, -⟩ := cross (pow_pos hp₁ 2) (pow_pos hq₁ 2) (pow_pos hp₂ 2)
      (pow_pos hq₂ 2) hn₁ hn₂ (mul_div_cancel₀ _ hδ) (mul_div_cancel₀ _ hδ)
    obtain ⟨hX, hY⟩ := hnn hK₁ hK₂
    obtain ⟨a, b, ha, hb, ha2, hb2, hab⟩ := exists_sq_point hX hY
    refine ⟨(a, b), ⟨ha, hb, ?_, ?_⟩, hab⟩
    · show p₁ ^ 2 * a ^ 2 + q₁ ^ 2 * b ^ 2 ≤ K₁
      rw [ha2, hb2, hl₁]
    · show p₂ ^ 2 * a ^ 2 + q₂ ^ 2 * b ^ 2 ≤ K₂
      rw [ha2, hb2, hl₂]

/-- `ellipseMax` is the greatest product under both ellipses. -/
@[tmio T, powerlib_foundation] theorem isGreatest_ellipseMax {p₁ q₁ K₁ p₂ q₂ K₂ : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    IsGreatest ((fun x : ℝ × ℝ => x.1 * x.2) '' ellipseFeasible p₁ q₁ K₁ p₂ q₂ K₂)
      (ellipseMax p₁ q₁ K₁ p₂ q₂ K₂) := by
  obtain ⟨x, hx, hxeq⟩ := exists_mul_eq_ellipseMax hp₁ hq₁ hp₂ hq₂ hK₁ hK₂
  refine ⟨⟨x, hx, hxeq⟩, ?_⟩
  rintro _ ⟨y, ⟨-, -, hy₁, hy₂⟩, rfl⟩
  exact mul_le_ellipseMax hp₁ hq₁ hp₂ hq₂ hy₁ hy₂

/-- The largest product under two ellipses is nonnegative. -/
@[tmio T, powerlib_foundation] theorem ellipseMax_nonneg {p₁ q₁ K₁ p₂ q₂ K₂ : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    0 ≤ ellipseMax p₁ q₁ K₁ p₂ q₂ K₂ := by
  simpa using mul_le_ellipseMax (a := 0) (b := 0) hp₁ hq₁ hp₂ hq₂ (by simpa using hK₁)
    (by simpa using hK₂)

/-! ## The box cut by two ellipses -/

/-- The box `[0, A] × [0, B]` cut by both filled ellipses. -/
def boxEllipseFeasible (p₁ q₁ K₁ p₂ q₂ K₂ A B : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ x.1 ≤ A ∧ 0 ≤ x.2 ∧ x.2 ≤ B ∧ p₁ ^ 2 * x.1 ^ 2 + q₁ ^ 2 * x.2 ^ 2 ≤ K₁ ∧
    p₂ ^ 2 * x.1 ^ 2 + q₂ ^ 2 * x.2 ^ 2 ≤ K₂}

/-- The largest product `a · b` over `boxEllipseFeasible`: the smallest of the three relaxations
dropping one of the box and the two ellipses. -/
def boxEllipseMax (p₁ q₁ K₁ p₂ q₂ K₂ A B : ℝ) : ℝ :=
  min (min (productMax p₁ q₁ K₁ A B) (productMax p₂ q₂ K₂ A B)) (ellipseMax p₁ q₁ K₁ p₂ q₂ K₂)

/-- Every point of the box cut by both ellipses has product at most `boxEllipseMax`. -/
@[tmio T, powerlib_foundation] theorem mul_le_boxEllipseMax {p₁ q₁ K₁ p₂ q₂ K₂ A B a b : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (ha : 0 ≤ a) (haA : a ≤ A)
    (hb : 0 ≤ b) (hbB : b ≤ B) (h₁ : p₁ ^ 2 * a ^ 2 + q₁ ^ 2 * b ^ 2 ≤ K₁)
    (h₂ : p₂ ^ 2 * a ^ 2 + q₂ ^ 2 * b ^ 2 ≤ K₂) :
    a * b ≤ boxEllipseMax p₁ q₁ K₁ p₂ q₂ K₂ A B :=
  le_min (le_min (mul_le_productMax hp₁ hq₁ ha haA hb hbB h₁)
    (mul_le_productMax hp₂ hq₂ ha haA hb hbB h₂)) (mul_le_ellipseMax hp₁ hq₁ hp₂ hq₂ h₁ h₂)

/-- The largest product over the box cut by both ellipses is nonnegative. -/
@[tmio T, powerlib_foundation] theorem boxEllipseMax_nonneg {p₁ q₁ K₁ p₂ q₂ K₂ A B : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ boxEllipseMax p₁ q₁ K₁ p₂ q₂ K₂ A B := by
  simpa using mul_le_boxEllipseMax (a := 0) (b := 0) hp₁ hq₁ hp₂ hq₂ le_rfl hA le_rfl hB
    (by simpa using hK₁) (by simpa using hK₂)

/-- A half-plane `c x + d y ≤ K` of the plane is convex. -/
@[tmio T, powerlib_foundation] private theorem convex_halfPlane (c d K : ℝ) :
    Convex ℝ {z : ℝ × ℝ | c * z.1 + d * z.2 ≤ K} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hx hy ⊢
  have e : K = a * K + b * K := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-- A box `x ≤ U`, `y ≤ V` of the plane is convex. -/
@[tmio T, powerlib_foundation] private theorem convex_box (U V : ℝ) :
    Convex ℝ {z : ℝ × ℝ | z.1 ≤ U ∧ z.2 ≤ V} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hx hy ⊢
  have eU : U = a * U + b * U := by rw [← add_mul, hab, one_mul]
  have eV : V = a * V + b * V := by rw [← add_mul, hab, one_mul]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hx.1 ha, mul_le_mul_of_nonneg_left hy.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

/-- A product of two nonnegative numbers at least `t²` has sum at least `2 t`. -/
@[tmio T, powerlib_foundation] private theorem two_mul_le_add {t u v : ℝ} (ht : 0 ≤ t)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (h : t * t ≤ u * v) : 2 * t ≤ u + v := by
  have h4 : (2 * t) ^ 2 ≤ (u + v) ^ 2 := by nlinarith [sq_nonneg (u - v)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp h4

/-- The superlevel set `{x, y ≥ 0, x y ≥ t}` (`t ≥ 0`) is convex. -/
@[tmio T, powerlib_foundation] private theorem convex_le_mul {t : ℝ} (ht : 0 ≤ t) :
    Convex ℝ {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ t ≤ z.1 * z.2} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hx hy ⊢
  obtain ⟨hx1, hx2, hxt⟩ := hx
  obtain ⟨hy1, hy2, hyt⟩ := hy
  refine ⟨by positivity, by positivity, ?_⟩
  have hcross : 2 * t ≤ x.1 * y.2 + y.1 * x.2 :=
    two_mul_le_add ht (by positivity) (by positivity)
      (by nlinarith [mul_le_mul hxt hyt ht (by positivity)])
  have e : t = (a + b) ^ 2 * t := by rw [hab]; ring
  nlinarith [mul_le_mul_of_nonneg_left hxt (sq_nonneg a),
    mul_le_mul_of_nonneg_left hyt (sq_nonneg b), mul_le_mul_of_nonneg_left hcross
      (mul_nonneg ha hb)]

/-- Some point of the box cut by both ellipses attains `boxEllipseMax` (Helly's theorem in the
squared coordinates `(a², b²)`). -/
@[tmio T, powerlib_foundation] theorem exists_mul_eq_boxEllipseMax
    {p₁ q₁ K₁ p₂ q₂ K₂ A B : ℝ} (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ x ∈ boxEllipseFeasible p₁ q₁ K₁ p₂ q₂ K₂ A B,
      x.1 * x.2 = boxEllipseMax p₁ q₁ K₁ p₂ q₂ K₂ A B := by
  set s := boxEllipseMax p₁ q₁ K₁ p₂ q₂ K₂ A B with hs
  have hs0 : 0 ≤ s := boxEllipseMax_nonneg hp₁ hq₁ hp₂ hq₂ hK₁ hK₂ hA hB
  have hs1 : s ≤ productMax p₁ q₁ K₁ A B := (min_le_left _ _).trans (min_le_left _ _)
  have hs2 : s ≤ productMax p₂ q₂ K₂ A B := (min_le_left _ _).trans (min_le_right _ _)
  have hs3 : s ≤ ellipseMax p₁ q₁ K₁ p₂ q₂ K₂ := min_le_right _ _
  have hsq : ∀ a b : ℝ, s ≤ a * b → s ^ 2 ≤ a ^ 2 * b ^ 2 := fun a b h => by
    rw [← mul_pow]; exact pow_le_pow_left₀ hs0 h 2
  let F : Fin (2 + 2) → Set (ℝ × ℝ) :=
    ![{z | z.1 ≤ A ^ 2 ∧ z.2 ≤ B ^ 2}, {z | p₁ ^ 2 * z.1 + q₁ ^ 2 * z.2 ≤ K₁},
      {z | p₂ ^ 2 * z.1 + q₂ ^ 2 * z.2 ≤ K₂}, {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ s ^ 2 ≤ z.1 * z.2}]
  have hF : ∀ i, Convex ℝ (F i) := by
    intro i
    fin_cases i
    · exact convex_box (A ^ 2) (B ^ 2)
    · exact convex_halfPlane _ _ _
    · exact convex_halfPlane _ _ _
    · exact convex_le_mul (sq_nonneg s)
  have hdrop : ∀ j, ∃ z, ∀ i, i ≠ j → z ∈ F i := by
    intro j
    fin_cases j
    · -- without the box: the optimizer of the two ellipses
      obtain ⟨⟨a, b⟩, ⟨-, -, h₁, h₂⟩, hab⟩ := exists_mul_eq_ellipseMax hp₁ hq₁ hp₂ hq₂ hK₁ hK₂
      refine ⟨(a ^ 2, b ^ 2), fun i hi => ?_⟩
      fin_cases i
      · exact absurd rfl hi
      · exact h₁
      · exact h₂
      · exact ⟨sq_nonneg a, sq_nonneg b, hsq a b (hab ▸ hs3)⟩
    · -- without the first ellipse: the optimizer of the box and the second ellipse
      obtain ⟨⟨a, b⟩, ⟨ha, haA, hb, hbB, h₂⟩, hab⟩ := exists_mul_eq_productMax hp₂ hq₂ hK₂ hA hB
      refine ⟨(a ^ 2, b ^ 2), fun i hi => ?_⟩
      fin_cases i
      · exact ⟨pow_le_pow_left₀ ha haA 2, pow_le_pow_left₀ hb hbB 2⟩
      · exact absurd rfl hi
      · exact h₂
      · exact ⟨sq_nonneg a, sq_nonneg b, hsq a b (hab ▸ hs2)⟩
    · -- without the second ellipse: the optimizer of the box and the first ellipse
      obtain ⟨⟨a, b⟩, ⟨ha, haA, hb, hbB, h₁⟩, hab⟩ := exists_mul_eq_productMax hp₁ hq₁ hK₁ hA hB
      refine ⟨(a ^ 2, b ^ 2), fun i hi => ?_⟩
      fin_cases i
      · exact ⟨pow_le_pow_left₀ ha haA 2, pow_le_pow_left₀ hb hbB 2⟩
      · exact h₁
      · exact absurd rfl hi
      · exact ⟨sq_nonneg a, sq_nonneg b, hsq a b (hab ▸ hs1)⟩
    · -- without the level set: the origin
      refine ⟨(0, 0), fun i hi => ?_⟩
      fin_cases i
      · exact ⟨sq_nonneg A, sq_nonneg B⟩
      · show p₁ ^ 2 * 0 + q₁ ^ 2 * 0 ≤ K₁
        simpa using hK₁
      · show p₂ ^ 2 * 0 + q₂ ^ 2 * 0 ≤ K₂
        simpa using hK₂
      · exact absurd rfl hi
  obtain ⟨z, hz⟩ := nonempty_iInter_of_drop_one (E := ℝ × ℝ) (d := 2) (by simp) F hF hdrop
  obtain ⟨hzA, hzB⟩ : z.1 ≤ A ^ 2 ∧ z.2 ≤ B ^ 2 := hz 0
  have hz₁ : p₁ ^ 2 * z.1 + q₁ ^ 2 * z.2 ≤ K₁ := hz 1
  have hz₂ : p₂ ^ 2 * z.1 + q₂ ^ 2 * z.2 ≤ K₂ := hz 2
  obtain ⟨hx0, hy0, hxy⟩ : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ s ^ 2 ≤ z.1 * z.2 := hz 3
  rcases hy0.eq_or_lt with hy | hy
  · -- `y = 0` forces `s = 0`: the origin attains it
    rw [← hy, mul_zero] at hxy
    have hs' : s = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hxy (sq_nonneg s))
    refine ⟨(0, 0), ⟨le_rfl, hA, le_rfl, hB, by simpa using hK₁, by simpa using hK₂⟩, ?_⟩
    rw [hs', mul_zero]
  · -- shrink `x` to `s²/y` on the level curve `x y = s²`
    set b := Real.sqrt z.2
    have hb : 0 < b := Real.sqrt_pos.mpr hy
    have hb2 : b ^ 2 = z.2 := Real.sq_sqrt hy0
    have ha0 : 0 ≤ s / b := div_nonneg hs0 hb.le
    have ha2 : (s / b) ^ 2 ≤ z.1 := by
      rw [div_pow, hb2, div_le_iff₀ hy]
      linarith
    refine ⟨(s / b, b), ⟨ha0, ?_, hb.le, ?_, ?_, ?_⟩, div_mul_cancel₀ s hb.ne'⟩
    · exact (sq_le_sq₀ ha0 hA).mp (ha2.trans hzA)
    · exact (sq_le_sq₀ hb.le hB).mp (hb2 ▸ hzB)
    · show p₁ ^ 2 * (s / b) ^ 2 + q₁ ^ 2 * b ^ 2 ≤ K₁
      rw [hb2]
      nlinarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg p₁)]
    · show p₂ ^ 2 * (s / b) ^ 2 + q₂ ^ 2 * b ^ 2 ≤ K₂
      rw [hb2]
      nlinarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg p₂)]

/-- `boxEllipseMax` is the greatest product over the box cut by both ellipses. -/
@[tmio T, powerlib_foundation] theorem isGreatest_boxEllipseMax {p₁ q₁ K₁ p₂ q₂ K₂ A B : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsGreatest ((fun x : ℝ × ℝ => x.1 * x.2) '' boxEllipseFeasible p₁ q₁ K₁ p₂ q₂ K₂ A B)
      (boxEllipseMax p₁ q₁ K₁ p₂ q₂ K₂ A B) := by
  obtain ⟨x, hx, hxeq⟩ := exists_mul_eq_boxEllipseMax hp₁ hq₁ hp₂ hq₂ hK₁ hK₂ hA hB
  refine ⟨⟨x, hx, hxeq⟩, ?_⟩
  rintro _ ⟨y, ⟨hy1, hy2, hy3, hy4, hy5, hy6⟩, rfl⟩
  exact mul_le_boxEllipseMax hp₁ hq₁ hp₂ hq₂ hy1 hy2 hy3 hy4 hy5 hy6

end powerlib.SpecialFunctions
