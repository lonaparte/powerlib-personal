import theorem.Attributes
import dependencies.Mathlib

/-! # The largest product on a box cut by an ellipse (foundation)

The maximum of `a · b` over the box `0 ≤ a ≤ A`, `0 ≤ b ≤ B` intersected with the filled ellipse
`p² a² + q² b² ≤ K` (`p, q > 0`), in closed piecewise form `productMax p q K A B`, together with a
point that attains it.

Write `s = √(K/2)`. Without the box the optimum is `p a = q b = s` with value `K/(2 p q)`. If that
point lies in the box it is the answer (first branch). Otherwise some face of the box cuts the
ellipse before the optimum: when `A < s/p` the face `a = A` is active and the best `b` on it is
`min B (√(K − p² A²)/q)` (second branch; when both faces cut, this is the corner `A · B`); else
`B < s/q` and the face `b = B` is active, symmetrically (third branch).

Scope.
* Generic static real algebra: one piecewise function of five real parameters and the constrained
  maximum it records; nothing here describes a physical system and no model family is defined.

Source: elementary constrained optimization — AM–GM on the ellipse,
`2 p q a b ≤ p² a² + q² b²`, and monotonicity of `x ↦ x (K − p² x)` below its vertex
`x = K/(2p²)`, whose increment is `(X − x)(K − p² (X + x))`; no paper.

Results.
* `productFeasible p q K A B`: the feasible set
  `{(a, b) | 0 ≤ a ≤ A, 0 ≤ b ≤ B, p² a² + q² b² ≤ K}`.
* `productMax p q K A B`: the piecewise maximum of `a · b` over it (definition).
* `mul_le_productMax`: for `p, q > 0`, every feasible `(a, b)` has `a · b ≤ productMax p q K A B`.
* `exists_mul_eq_productMax`: for `p, q > 0`, `K, A, B ≥ 0`, some feasible point attains
  `productMax p q K A B`.
* `isGreatest_productMax`: for `p, q > 0`, `K, A, B ≥ 0`, `productMax p q K A B` is the greatest
  element of the image of the feasible set under `(a, b) ↦ a · b`.
* `productMax_nonneg`: for `p, q > 0`, `K, A, B ≥ 0`, `0 ≤ productMax p q K A B`.
-/

noncomputable section
namespace powerlib.SpecialFunctions

/-- The box `[0, A] × [0, B]` cut by the filled ellipse `p² a² + q² b² ≤ K`. -/
def productFeasible (p q K A B : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ x.1 ≤ A ∧ 0 ≤ x.2 ∧ x.2 ≤ B ∧ p ^ 2 * x.1 ^ 2 + q ^ 2 * x.2 ^ 2 ≤ K}

/-- The largest product `a · b` over `productFeasible p q K A B`: the ellipse optimum
`p a = q b = √(K/2)` when it lies in the box, otherwise the best point on the active face. -/
def productMax (p q K A B : ℝ) : ℝ :=
  if Real.sqrt (K / 2) / p ≤ A ∧ Real.sqrt (K / 2) / q ≤ B then K / (2 * p * q)
  else if A < Real.sqrt (K / 2) / p then A * min B (Real.sqrt (K - p ^ 2 * A ^ 2) / q)
  else B * min A (Real.sqrt (K - q ^ 2 * B ^ 2) / p)

/-- A face below the ellipse optimum, `0 ≤ A < √(K/2)/p`, gives `2 p² A² < K`. -/
@[tmio T, powerlib_foundation] private theorem two_mul_sq_lt_of_lt_sqrt {p K A : ℝ} (hp : 0 < p)
    (hA : 0 ≤ A) (h : A < Real.sqrt (K / 2) / p) : 2 * (p ^ 2 * A ^ 2) < K := by
  rw [lt_div_iff₀ hp] at h
  have hpA : 0 ≤ A * p := mul_nonneg hA hp.le
  have hK : 0 < K / 2 := Real.sqrt_pos.mp (hpA.trans_lt h)
  have hs := Real.sq_sqrt hK.le
  nlinarith [mul_self_lt_mul_self hpA h]

/-- The face bound: below the optimum on the face `a = A`, every feasible point has
`a · b ≤ A · min B (√(K − p² A²)/q)`. -/
@[tmio T, powerlib_foundation] private theorem mul_le_face {p q K A B a b : ℝ} (hp : 0 < p)
    (hq : 0 < q) (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B)
    (hE : p ^ 2 * a ^ 2 + q ^ 2 * b ^ 2 ≤ K) (h : A < Real.sqrt (K / 2) / p) :
    a * b ≤ A * min B (Real.sqrt (K - p ^ 2 * A ^ 2) / q) := by
  have hA : 0 ≤ A := ha.trans haA
  have h2 := two_mul_sq_lt_of_lt_sqrt hp hA h
  have hR := Real.sq_sqrt (show 0 ≤ K - p ^ 2 * A ^ 2 by nlinarith [sq_nonneg (p * A)])
  rw [mul_min_of_nonneg _ _ hA]
  refine le_min (mul_le_mul haA hbB hb hA) ?_
  rw [← mul_div_assoc, le_div_iff₀ hq]
  refine (sq_le_sq₀ (by positivity) (mul_nonneg hA (Real.sqrt_nonneg _))).mp ?_
  have hmono : a ^ 2 * (K - p ^ 2 * a ^ 2) ≤ A ^ 2 * (K - p ^ 2 * A ^ 2) := by
    have hsq : a ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ha haA 2
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq)
      (show 0 ≤ K - p ^ 2 * (A ^ 2 + a ^ 2) by nlinarith [sq_nonneg p])]
  have hcut : a ^ 2 * (q ^ 2 * b ^ 2) ≤ a ^ 2 * (K - p ^ 2 * a ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg a)
  rw [mul_pow A, hR]
  nlinarith

/-- The best point of the face `a = A` below the optimum is feasible. -/
@[tmio T, powerlib_foundation] private theorem face_feasible {p q K A B : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A < Real.sqrt (K / 2) / p) :
    0 ≤ min B (Real.sqrt (K - p ^ 2 * A ^ 2) / q) ∧
      p ^ 2 * A ^ 2 + q ^ 2 * min B (Real.sqrt (K - p ^ 2 * A ^ 2) / q) ^ 2 ≤ K := by
  have h2 := two_mul_sq_lt_of_lt_sqrt hp hA h
  have hR := Real.sq_sqrt (show 0 ≤ K - p ^ 2 * A ^ 2 by nlinarith [sq_nonneg (p * A)])
  have hm0 : 0 ≤ min B (Real.sqrt (K - p ^ 2 * A ^ 2) / q) :=
    le_min hB (div_nonneg (Real.sqrt_nonneg _) hq.le)
  refine ⟨hm0, ?_⟩
  have hmR : min B (Real.sqrt (K - p ^ 2 * A ^ 2) / q) * q ≤ Real.sqrt (K - p ^ 2 * A ^ 2) :=
    (le_div_iff₀ hq).mp (min_le_right _ _)
  have hsq := pow_le_pow_left₀ (mul_nonneg hm0 hq.le) hmR 2
  rw [hR, mul_pow] at hsq
  linarith

/-- Every point of the box cut by the ellipse has product at most `productMax`. -/
@[tmio T, powerlib_foundation] theorem mul_le_productMax {p q K A B a b : ℝ} (hp : 0 < p)
    (hq : 0 < q) (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B)
    (hE : p ^ 2 * a ^ 2 + q ^ 2 * b ^ 2 ≤ K) : a * b ≤ productMax p q K A B := by
  unfold productMax
  split_ifs with h1 h2
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p * a - q * b)]
  · exact mul_le_face hp hq ha haA hb hbB hE h2
  · have hpA : Real.sqrt (K / 2) / p ≤ A := not_lt.mp h2
    have hB : B < Real.sqrt (K / 2) / q := lt_of_not_ge fun h => h1 ⟨hpA, h⟩
    rw [mul_comm a b]
    exact mul_le_face hq hp hb hbB ha haA (by linarith) hB

/-- Some point of the box cut by the ellipse attains `productMax`. -/
@[tmio T, powerlib_foundation] theorem exists_mul_eq_productMax {p q K A B : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ x ∈ productFeasible p q K A B, x.1 * x.2 = productMax p q K A B := by
  unfold productMax
  split_ifs with h1 h2
  · have hs := Real.sq_sqrt (show 0 ≤ K / 2 by linarith)
    refine ⟨(Real.sqrt (K / 2) / p, Real.sqrt (K / 2) / q),
      ⟨by positivity, h1.1, by positivity, h1.2, ?_⟩, ?_⟩
    · rw [div_pow, div_pow, hs]
      field_simp
      linarith
    · rw [div_mul_div_comm, ← sq, hs]
      field_simp
  · obtain ⟨hm0, hmE⟩ := face_feasible hp hq hA hB h2
    exact ⟨(A, min B (Real.sqrt (K - p ^ 2 * A ^ 2) / q)),
      ⟨hA, le_rfl, hm0, min_le_left _ _, hmE⟩, rfl⟩
  · have hpA : Real.sqrt (K / 2) / p ≤ A := not_lt.mp h2
    have hqB : B < Real.sqrt (K / 2) / q := lt_of_not_ge fun h => h1 ⟨hpA, h⟩
    obtain ⟨hm0, hmE⟩ := face_feasible hq hp hB hA hqB
    exact ⟨(min A (Real.sqrt (K - q ^ 2 * B ^ 2) / p), B),
      ⟨hm0, min_le_left _ _, hB, le_rfl, by linarith⟩, mul_comm _ _⟩

/-- `productMax` is the greatest product over the box cut by the ellipse. -/
@[tmio T, powerlib_foundation] theorem isGreatest_productMax {p q K A B : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsGreatest ((fun x : ℝ × ℝ => x.1 * x.2) '' productFeasible p q K A B)
      (productMax p q K A B) := by
  obtain ⟨x, hx, hxeq⟩ := exists_mul_eq_productMax hp hq hK hA hB
  refine ⟨⟨x, hx, hxeq⟩, ?_⟩
  rintro _ ⟨y, ⟨hy1, hy2, hy3, hy4, hy5⟩, rfl⟩
  exact mul_le_productMax hp hq hy1 hy2 hy3 hy4 hy5

/-- The largest product is nonnegative. -/
@[tmio T, powerlib_foundation] theorem productMax_nonneg {p q K A B : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ productMax p q K A B := by
  simpa using mul_le_productMax hp hq le_rfl hA le_rfl hB (by simpa using hK)

end powerlib.SpecialFunctions
