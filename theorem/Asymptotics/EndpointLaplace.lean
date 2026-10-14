import theorem.Asymptotics.GaussianMoments

/-! # Endpoint versus interior Laplace: the truncated moment table

The *term table* of the endpoint Laplace note: the three leading contributions of
`∫ g(y) e^{-X φ(y)} dy`, summed over the half line (endpoint minimum) and over the full line
(interior minimum).

Scope.
* After the Taylor substitution `y = y* + ξ`, `g = g₀ + g₁ ξ + …`,
  `φ = φ* + φ₂ ξ²/2 + φ₃ ξ³/6 + …`, the table is
  `g₀ ∫ e^{-bξ²/2}`, `g₁ ∫ ξ e^{-bξ²/2}`, `-g₀ (X φ₃/6) ∫ ξ³ e^{-bξ²/2}`, with `b = X φ₂`,
  integrated over the half line or the full line. The common factor `e^{-X φ*}` is omitted.
* This is an exact statement about the truncated table, not the Laplace asymptotic theorem
  itself (no remainder estimate for the discarded Taylor terms is proved here). The
  remainder-controlled correction orders — interior `1 + O(1/X)`, endpoint `1 + O(X^{−1/2})` —
  are `laplace_interior_rate` / `laplace_endpoint_rate` (and their `IsBigO` forms) in
  `Asymptotics/LaplaceMethod.lean`.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.1 (moment table and the
`X^{-1/2}` vs `X^{-1}` comparison).

Results.
* `endpointTable_eq` — on the half line the table sums to
  `½ g₀ √(2π/(X φ₂)) (1 + c X^{-1/2})` with
  `c = √(2/π) (g₁/g₀ - φ₃/(3 φ₂)) / √φ₂`; the prefactor `½` is the half Gaussian, and both
  odd terms contribute at relative order `X^{-1/2}`.
* `endpointCorrection_ne_zero_iff` — the half-order term is present iff
  `g₁/g₀ ≠ φ₃/(3 φ₂)`.
* `interiorTable_eq` — on the full line the odd terms vanish identically and the table is
  `g₀ √(2π/(X φ₂))`, with no `X^{-1/2}` term.

Corrections.
* The note states "端点处……修正从 `O(X^{-1})` 变成 `O(X^{-1/2})`" and, for the guard barrier,
  "修正确为半阶" from `U''' ≠ 0` alone. The half-order coefficient is
  `√(2/π)(g₁/g₀ - φ₃/(3φ₂))/√φ₂`, so `φ₃ ≠ 0` is not sufficient: the half-order term is absent
  exactly when `g₁/g₀ = φ₃/(3φ₂)`. The formal statement carries this extra hypothesis.
-/

noncomputable section
namespace powerlib.Asymptotics

open Real MeasureTheory Set

/-- The three table terms over the half line (minimum at the left endpoint). -/
def endpointTable (g₀ g₁ φ₂ φ₃ X : ℝ) : ℝ :=
  g₀ * (∫ ξ in Ioi (0 : ℝ), Real.exp (-(X * φ₂ / 2) * ξ ^ 2)) +
    g₁ * (∫ ξ in Ioi (0 : ℝ), ξ * Real.exp (-(X * φ₂ / 2) * ξ ^ 2)) -
    g₀ * (X * φ₃ / 6) * (∫ ξ in Ioi (0 : ℝ), ξ ^ 3 * Real.exp (-(X * φ₂ / 2) * ξ ^ 2))

/-- The same three terms over the full line (interior minimum). -/
def interiorTable (g₀ g₁ φ₂ φ₃ X : ℝ) : ℝ :=
  g₀ * (∫ ξ : ℝ, Real.exp (-(X * φ₂ / 2) * ξ ^ 2)) +
    g₁ * (∫ ξ : ℝ, ξ * Real.exp (-(X * φ₂ / 2) * ξ ^ 2)) -
    g₀ * (X * φ₃ / 6) * (∫ ξ : ℝ, ξ ^ 3 * Real.exp (-(X * φ₂ / 2) * ξ ^ 2))

/-- Coefficient of the relative `X^{-1/2}` correction in the endpoint table. -/
def endpointCorrection (g₀ g₁ φ₂ φ₃ : ℝ) : ℝ :=
  Real.sqrt (2 / π) * (g₁ / g₀ - φ₃ / (3 * φ₂)) / Real.sqrt φ₂

/-- The algebraic core of `endpointTable_eq`, in the square-root variables `x = √X`,
`p = √φ₂`. -/
@[powerlib_foundation] private theorem endpointTable_core {g₀ g₁ φ₃ x p : ℝ} (hg : g₀ ≠ 0)
    (hx : 0 < x) (hp : 0 < p) :
    g₀ * (Real.sqrt 2 * Real.sqrt π / (x * p) / 2) + g₁ * (1 / (x ^ 2 * p ^ 2)) -
        g₀ * (x ^ 2 * φ₃ / 6) * (2 / (x ^ 2 * p ^ 2) ^ 2) =
      1 / 2 * g₀ * (Real.sqrt 2 * Real.sqrt π / (x * p)) *
        (1 + Real.sqrt 2 / Real.sqrt π * (g₁ / g₀ - φ₃ / (3 * p ^ 2)) / p / x) := by
  have hsπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have q2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt two_pos.le
  field_simp
  ring_nf
  rw [q2]
  ring

@[powerlib_foundation] theorem endpointTable_eq {g₀ g₁ φ₂ φ₃ X : ℝ} (hg : g₀ ≠ 0)
    (hφ : 0 < φ₂) (hX : 0 < X) :
    endpointTable g₀ g₁ φ₂ φ₃ X =
      1 / 2 * g₀ * Real.sqrt (2 * π / (X * φ₂)) *
        (1 + endpointCorrection g₀ g₁ φ₂ φ₃ / Real.sqrt X) := by
  have hb : 0 < X * φ₂ := mul_pos hX hφ
  rw [endpointTable, halfMoment0 hb, halfMoment1 hb, halfMoment3 hb, endpointCorrection]
  have hpi : 0 < π := Real.pi_pos
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hsφ : 0 < Real.sqrt φ₂ := Real.sqrt_pos.mpr hφ
  have e1 : Real.sqrt (2 * π / (X * φ₂)) =
      Real.sqrt 2 * Real.sqrt π / (Real.sqrt X * Real.sqrt φ₂) := by
    rw [Real.sqrt_div' _ hb.le, Real.sqrt_mul two_pos.le, Real.sqrt_mul hX.le]
  have e2 : Real.sqrt (2 / π) = Real.sqrt 2 / Real.sqrt π := Real.sqrt_div' _ hpi.le
  have qX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  have qφ : Real.sqrt φ₂ ^ 2 = φ₂ := Real.sq_sqrt hφ.le
  have h := endpointTable_core (g₁ := g₁) (φ₃ := φ₃) hg hsX hsφ
  rw [qX, qφ] at h
  rw [e1, e2]
  convert h using 2

@[powerlib_foundation] theorem endpointCorrection_ne_zero_iff {g₀ g₁ φ₂ φ₃ : ℝ}
    (hφ : 0 < φ₂) :
    endpointCorrection g₀ g₁ φ₂ φ₃ ≠ 0 ↔ g₁ / g₀ ≠ φ₃ / (3 * φ₂) := by
  have h2π : 0 < Real.sqrt (2 / π) := Real.sqrt_pos.mpr (div_pos two_pos Real.pi_pos)
  have hsφ : 0 < Real.sqrt φ₂ := Real.sqrt_pos.mpr hφ
  rw [endpointCorrection, Ne, div_eq_zero_iff, mul_eq_zero, not_or, not_or, sub_eq_zero]
  constructor
  · exact fun h => h.1.2
  · exact fun h => ⟨⟨h2π.ne', h⟩, hsφ.ne'⟩

/-- Full line: the odd terms vanish and no half-order correction appears. -/
@[powerlib_foundation] theorem interiorTable_eq {g₀ g₁ φ₂ φ₃ X : ℝ} (hφ : 0 < φ₂)
    (hX : 0 < X) :
    interiorTable g₀ g₁ φ₂ φ₃ X = g₀ * Real.sqrt (2 * π / (X * φ₂)) := by
  obtain ⟨h1, h3⟩ := integral_odd_moments_vanish (X * φ₂)
  have hmain : ∫ ξ : ℝ, Real.exp (-(X * φ₂ / 2) * ξ ^ 2) = Real.sqrt (2 * π / (X * φ₂)) := by
    rw [integral_gaussian]
    congr 1
    field_simp
  rw [interiorTable, h1, h3, hmain]
  ring

/-- The endpoint main term is exactly half the interior main term. -/
@[powerlib_foundation] theorem endpoint_main_term_half {b : ℝ} (hb : 0 < b) :
    (∫ ξ in Ioi (0 : ℝ), Real.exp (-(b / 2) * ξ ^ 2)) =
      (1 / 2) * ∫ ξ : ℝ, Real.exp (-(b / 2) * ξ ^ 2) := by
  rw [halfMoment0 hb, integral_gaussian]
  have : π / (b / 2) = 2 * π / b := by field_simp
  rw [this]
  ring

end powerlib.Asymptotics
