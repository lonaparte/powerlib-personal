import theorem.Attributes
import dependencies.Mathlib

/-! # The largest product less a free square on a box cut by a half-space (foundation)

The maximum of `4 u v − r²` over real `(u, v, r)` with `0 ≤ u ≤ U`, `0 ≤ v ≤ V` and
`u + v + r ≤ K` (`U, V, K ≥ 0`, `r` free in sign), in closed piecewise form
`reactiveMax U V K`, together with the point `reactiveArg U V K` that attains it.

If the corner `(U, V)` fits under the budget (`U + V ≤ K`) it is the answer with `r = 0`
(first branch). If one box side exceeds the other by at least `K`, the budget binds on the short
side and the optimum is `4 U K` or `4 V K`, attained with `r = −2U` or `r = −2V` (second and third
branches). Otherwise the corner is kept and the excess `U + V − K` is paid by `r`, giving
`4 U V − (U + V − K)²` (fourth branch).

Scope.
* Generic static real algebra: one piecewise function of three real parameters and the constrained
  maximum it records; nothing here describes a physical system and no model is defined.

Source: elementary algebra; no paper. Certificates:
* always, from `v ≤ K − u − r`, `4uv − r² ≤ 4uK − (2u + r)² ≤ 4uK`, symmetrically `≤ 4vK`, and
  `4uv − r² ≤ 4uv ≤ 4UV`;
* in the fourth branch, with `α = U − u`, `β = V − v`, `T = U + V − K > 0`, `t = u + v − K`:
  if `t ≥ 0` then `r² ≥ t²` and
  `4UV − T² − (4uv − t²) = 2α(V − U + K) + 2β(U − V + K) + (α − β)²`; if `t < 0` then
  `4UV − 4uv = α(4v + 2β) + β(4u + 2α) ≥ (α + β) T ≥ T²`;
* the attained values are `4U(U + K) − (2U)² = 4UK` and `4UV − (K − U − V)²`.

Results.
* `reactiveMax U V K`: the piecewise maximum of `4 u v − r²` (definition).
* `reactiveArg U V K`: the maximizing point `(u, v, r)` (definition).
* `le_reactiveMax`: for `K ≥ 0`, every `(u, v, r)` with `0 ≤ u ≤ U`, `0 ≤ v ≤ V`,
  `u + v + r ≤ K` has `4 u v − r² ≤ reactiveMax U V K`.
* `reactiveArg_feasible`: for `U, V, K ≥ 0`, the components of `reactiveArg U V K` satisfy the
  constraints.
* `reactiveArg_value`: `reactiveArg U V K` attains `reactiveMax U V K`.
* `reactiveMax_nonneg`: for `U, V, K ≥ 0`, `0 ≤ reactiveMax U V K`.
* `isGreatest_reactiveMax`: for `U, V, K ≥ 0`, `reactiveMax U V K` is the greatest value of
  `4 u v − r²` over the constraint set.
-/

noncomputable section
namespace powerlib.SpecialFunctions

/-- The largest value of `4 u v − r²` over `0 ≤ u ≤ U`, `0 ≤ v ≤ V`, `u + v + r ≤ K`. -/
def reactiveMax (U V K : ℝ) : ℝ :=
  if U + V ≤ K then 4 * U * V
  else if U + K ≤ V then 4 * U * K
  else if V + K ≤ U then 4 * V * K
  else 4 * U * V - (U + V - K) ^ 2

/-- A point `(u, v, r)` attaining `reactiveMax U V K`. -/
def reactiveArg (U V K : ℝ) : ℝ × ℝ × ℝ :=
  if U + V ≤ K then (U, V, 0)
  else if U + K ≤ V then (U, U + K, -(2 * U))
  else if V + K ≤ U then (V + K, V, -(2 * V))
  else (U, V, K - U - V)

/-- The budget bound on the first side: `4 u v − r² ≤ 4 u K − (2u + r)² ≤ 4 u K`. -/
@[tmio T, powerlib_foundation] private theorem le_four_mul_budget {u v r K : ℝ} (hu : 0 ≤ u)
    (hS : u + v + r ≤ K) : 4 * u * v - r ^ 2 ≤ 4 * u * K := by
  nlinarith [mul_le_mul_of_nonneg_left (show v ≤ K - u - r by linarith) hu, sq_nonneg (2 * u + r)]

/-- The fourth branch: `4 u v − r² ≤ 4 U V − (U + V − K)²` when no side or corner is slack. -/
@[tmio T, powerlib_foundation] private theorem le_interior {U V K u v r : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ U) (hv : 0 ≤ v) (hvV : v ≤ V) (hS : u + v + r ≤ K) (h1 : K < U + V)
    (h2 : V < U + K) (h3 : U < V + K) : 4 * u * v - r ^ 2 ≤ 4 * U * V - (U + V - K) ^ 2 := by
  have hα : 0 ≤ U - u := sub_nonneg.mpr huU
  have hβ : 0 ≤ V - v := sub_nonneg.mpr hvV
  rcases le_or_gt 0 (u + v - K) with ht | ht
  · have hr : (u + v - K) ^ 2 ≤ r ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ -r - (u + v - K) by linarith)
        (show 0 ≤ -r + (u + v - K) by linarith)]
    nlinarith [mul_nonneg hα (show 0 ≤ V - U + K by linarith),
      mul_nonneg hβ (show 0 ≤ U - V + K by linarith), sq_nonneg ((U - u) - (V - v))]
  · have hT : 0 ≤ U + V - K := by linarith
    have ha := mul_le_mul_of_nonneg_left
      (show U + V - K ≤ 4 * v + 2 * (V - v) by linarith) hα
    have hb := mul_le_mul_of_nonneg_left
      (show U + V - K ≤ 4 * u + 2 * (U - u) by linarith) hβ
    have hc := mul_le_mul_of_nonneg_right
      (show U + V - K ≤ (U - u) + (V - v) by linarith) hT
    nlinarith [sq_nonneg r]

/-- Every feasible `(u, v, r)` has `4 u v − r² ≤ reactiveMax U V K`. -/
@[tmio T, powerlib_foundation] theorem le_reactiveMax {U V K u v r : ℝ} (hK : 0 ≤ K)
    (hu : 0 ≤ u) (huU : u ≤ U) (hv : 0 ≤ v) (hvV : v ≤ V) (hS : u + v + r ≤ K) :
    4 * u * v - r ^ 2 ≤ reactiveMax U V K := by
  unfold reactiveMax
  split_ifs with h1 h2 h3
  · nlinarith [mul_le_mul huU hvV hv (hu.trans huU), sq_nonneg r]
  · nlinarith [le_four_mul_budget hu hS, mul_le_mul_of_nonneg_right huU hK]
  · have hS' : v + u + r ≤ K := by linarith
    nlinarith [le_four_mul_budget hv hS', mul_le_mul_of_nonneg_right hvV hK]
  · exact le_interior hu huU hv hvV hS (not_le.mp h1) (by linarith [not_le.mp h2])
      (by linarith [not_le.mp h3])

/-- The point `reactiveArg U V K` satisfies the constraints. -/
@[tmio T, powerlib_foundation] theorem reactiveArg_feasible {U V K : ℝ} (hU : 0 ≤ U)
    (hV : 0 ≤ V) (hK : 0 ≤ K) :
    0 ≤ (reactiveArg U V K).1 ∧ (reactiveArg U V K).1 ≤ U ∧
      0 ≤ (reactiveArg U V K).2.1 ∧ (reactiveArg U V K).2.1 ≤ V ∧
      (reactiveArg U V K).1 + (reactiveArg U V K).2.1 + (reactiveArg U V K).2.2 ≤ K := by
  unfold reactiveArg
  split_ifs with h1 h2 h3
  · exact ⟨hU, le_rfl, hV, le_rfl, by simpa using h1⟩
  · exact ⟨hU, le_rfl, by linarith, h2, by linarith⟩
  · exact ⟨by linarith, h3, hV, le_rfl, by linarith⟩
  · exact ⟨hU, le_rfl, hV, le_rfl, by linarith⟩

/-- The point `reactiveArg U V K` attains `reactiveMax U V K`. -/
@[tmio T, powerlib_foundation] theorem reactiveArg_value (U V K : ℝ) :
    4 * (reactiveArg U V K).1 * (reactiveArg U V K).2.1 - (reactiveArg U V K).2.2 ^ 2 =
      reactiveMax U V K := by
  unfold reactiveArg reactiveMax
  split_ifs <;> ring

/-- The largest value is nonnegative. -/
@[tmio T, powerlib_foundation] theorem reactiveMax_nonneg {U V K : ℝ} (hU : 0 ≤ U)
    (hV : 0 ≤ V) (hK : 0 ≤ K) : 0 ≤ reactiveMax U V K := by
  simpa using le_reactiveMax (r := 0) hK le_rfl hU le_rfl hV (by simpa using hK)

/-- `reactiveMax U V K` is the greatest value of `4 u v − r²` over the constraint set. -/
@[tmio T, powerlib_foundation] theorem isGreatest_reactiveMax {U V K : ℝ} (hU : 0 ≤ U)
    (hV : 0 ≤ V) (hK : 0 ≤ K) :
    IsGreatest {x : ℝ | ∃ u v r, 0 ≤ u ∧ u ≤ U ∧ 0 ≤ v ∧ v ≤ V ∧ u + v + r ≤ K ∧
      x = 4 * u * v - r ^ 2} (reactiveMax U V K) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := reactiveArg_feasible hU hV hK
  refine ⟨⟨_, _, _, h1, h2, h3, h4, h5, (reactiveArg_value U V K).symm⟩, ?_⟩
  rintro _ ⟨u, v, r, hu, huU, hv, hvV, hS, rfl⟩
  exact le_reactiveMax hK hu huU hv hvV hS

end powerlib.SpecialFunctions
