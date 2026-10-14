import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Subcritical-Hopf guard potential: exact identities

Foundation layer. Every statement is an exact real-algebra or one-variable calculus identity
about the explicit scalar functions below; none of them is a stability, escape-time or
first-passage theorem about a power-electronic system.

Objects (all real, one-dimensional, continuous time):
* `guardDrift α l₁ r = -α r + l₁ r³` — the truncated radial normal form `ṙ = -α r + l₁ r³` of a
  subcritical Hopf point in normal-form amplitude coordinates, with `α = -Re λ > 0` and
  `l₁ = Re c₁ > 0`. No higher-order (quintic) normal-form term, no noise, no forcing.
* `guardPotential α l₁ r = α r²/2 - l₁ r⁴/4`, the potential with `ṙ = -U'(r)`: the well is at
  `r = 0`, the barrier top at `guardRadius α l₁ = √(α/l₁)`.
* `barrierHeight α l₁ = α²/(4 l₁)` and the asymptotic prefactor `guardPrefactor`.

Results:
* `ṙ = -U'(r)`, `U'(r_c) = 0`, `ΔU = U(r_c) - U(0) = α²/(4 l₁)`, `U''(r_c) = -2α`,
  `U'''(r) = -6 l₁ r` (so `U'''(r_c) ≠ 0`, the endpoint hypothesis of the endpoint Laplace
  expansion), and `U(u r_c) - U(r_c) = -ΔU (u² - 1)²`, which equals `-9 ΔU` at `u = 2`.
* The unstable Floquet exponent of the truncated normal form at the cycle radius:
  `d(ṙ)/dr |_{r_c} = +2α`, independent of `l₁` (the leading-order `κ = 2α`).
* `ln T = X + ln P` with `P = (√π/2) √(D̃ l₁)/α² = √π/(4 α √X)` for `X = ΔU/D̃`.
* Lifetime sensitivity: for `T(α) = c α⁻² e^{α²/(4 l D)}` and `X = α²/(4 l D)`,
  `T(α(1+ε))/T(α) = e^{X[(1+ε)²−1]}/(1+ε)²` (`lifetime_ratio`); at `X = 10`, `ε = 0.1` it lies
  in `(6.74, 6.76)`, versus `8.16 < e^{2.1} < 8.17` for the exponential factor alone
  (`lifetime_ratio_num`, `exp_tenth_bounds`, `exp_two_point_one_bounds`; work-sync
  `theory/T-cramer-rao-bound.md` §1.6).

The amplitude coordinate and the factor conventions are those of the source notes; the
relation between this scalar normal form and any concrete converter model is not
formalized here.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.2, §1.3, §1.5;
projects/basin-guard/notes/concepts/stochastic-drive.md §3–§4 (the same `ΔU = α²/(4 l₁)`,
proved once here); projects/gfl-gfm-stability-tree/notes/concepts/frozen-and-basin.md
("κ 领头阶与潜伏对数律": `d ṙ/dr |_{r_c} = +2α`).
-/

noncomputable section
namespace powerlib.Asymptotics.Guard

open Real

/-- Truncated radial normal form `ṙ = -α r + l₁ r³`. -/
def guardDrift (α l₁ r : ℝ) : ℝ := -α * r + l₁ * r ^ 3

/-- Potential with `ṙ = -U'(r)`: `U(r) = α r²/2 - l₁ r⁴/4`. -/
def guardPotential (α l₁ r : ℝ) : ℝ := α * r ^ 2 / 2 - l₁ * r ^ 4 / 4

/-- Barrier-top (unstable-cycle) radius `r_c = √(α/l₁)`. -/
def guardRadius (α l₁ : ℝ) : ℝ := Real.sqrt (α / l₁)

/-- Barrier height `ΔU = α²/(4 l₁)`. -/
def barrierHeight (α l₁ : ℝ) : ℝ := α ^ 2 / (4 * l₁)

/-- Escape prefactor `P = (√π/2) √(D̃ l₁)/α²` of the first-arrival time `T = P e^X`. -/
def guardPrefactor (α l₁ D : ℝ) : ℝ := Real.sqrt π / 2 * Real.sqrt (D * l₁) / α ^ 2

variable {α l₁ : ℝ}

@[powerlib_foundation] theorem guardRadius_sq (hα : 0 ≤ α) (hl : 0 < l₁) :
    guardRadius α l₁ ^ 2 = α / l₁ := by
  rw [guardRadius, Real.sq_sqrt (div_nonneg hα hl.le)]

@[powerlib_foundation] theorem hasDerivAt_guardPotential (α l₁ r : ℝ) :
    HasDerivAt (guardPotential α l₁) (-guardDrift α l₁ r) r := by
  have h := ((hasDerivAt_pow 2 r).const_mul (α / 2)).sub ((hasDerivAt_pow 4 r).const_mul (l₁ / 4))
  convert h using 1
  · funext x; simp [guardPotential]; ring
  · simp [guardDrift]; ring

/-- The potential gradient is the negative drift: `ṙ = -U'(r)`. -/
@[powerlib_foundation] theorem deriv_guardPotential (α l₁ : ℝ) :
    deriv (guardPotential α l₁) = fun r => α * r - l₁ * r ^ 3 := by
  funext r
  rw [(hasDerivAt_guardPotential α l₁ r).deriv, guardDrift]; ring

@[powerlib_foundation] theorem deriv2_guardPotential (α l₁ : ℝ) :
    deriv (deriv (guardPotential α l₁)) = fun r => α - 3 * l₁ * r ^ 2 := by
  rw [deriv_guardPotential]
  funext r
  have h : HasDerivAt (fun r => α * r - l₁ * r ^ 3) (α - 3 * l₁ * r ^ 2) r := by
    have h := ((hasDerivAt_id' r).const_mul α).sub ((hasDerivAt_pow 3 r).const_mul l₁)
    convert h using 1
    simp; ring
  exact h.deriv

@[powerlib_foundation] theorem deriv3_guardPotential (α l₁ : ℝ) :
    deriv (deriv (deriv (guardPotential α l₁))) = fun r => -6 * l₁ * r := by
  rw [deriv2_guardPotential]
  funext r
  have h : HasDerivAt (fun r => α - 3 * l₁ * r ^ 2) (-6 * l₁ * r) r := by
    have h := (hasDerivAt_const r α).sub ((hasDerivAt_pow 2 r).const_mul (3 * l₁))
    convert h using 1
    simp; ring
  exact h.deriv

/-- The barrier top is a critical point of `U` (equilibrium of the drift). -/
@[powerlib_foundation] theorem guardDrift_guardRadius (hα : 0 ≤ α) (hl : 0 < l₁) :
    guardDrift α l₁ (guardRadius α l₁) = 0 := by
  have h2 := guardRadius_sq hα hl
  have : guardRadius α l₁ ^ 3 = guardRadius α l₁ * (α / l₁) := by rw [← h2]; ring
  rw [guardDrift, this]
  field_simp
  ring

/-- `ΔU = U(r_c) - U(0) = α²/(4 l₁)`. -/
@[powerlib_foundation] theorem guardPotential_barrier (hα : 0 ≤ α) (hl : 0 < l₁) :
    guardPotential α l₁ (guardRadius α l₁) - guardPotential α l₁ 0 = barrierHeight α l₁ := by
  have h2 := guardRadius_sq hα hl
  have h4 : guardRadius α l₁ ^ 4 = (α / l₁) ^ 2 := by rw [← h2]; ring
  rw [guardPotential, guardPotential, h4, h2, barrierHeight]
  field_simp
  ring

/-- Barrier curvature `U''(r_c) = -2α`. -/
@[powerlib_foundation] theorem deriv2_guardPotential_guardRadius (hα : 0 ≤ α) (hl : 0 < l₁) :
    deriv (deriv (guardPotential α l₁)) (guardRadius α l₁) = -2 * α := by
  rw [deriv2_guardPotential]
  simp only
  rw [guardRadius_sq hα hl]
  field_simp
  ring

/-- `U'''(r_c) = -6 l₁ r_c`, nonzero for `α, l₁ > 0`: the barrier top is a non-degenerate
endpoint in the sense of the endpoint Laplace expansion. -/
@[powerlib_foundation] theorem deriv3_guardPotential_guardRadius_ne_zero
    (hα : 0 < α) (hl : 0 < l₁) :
    deriv (deriv (deriv (guardPotential α l₁))) (guardRadius α l₁) =
        -6 * l₁ * guardRadius α l₁ ∧
      deriv (deriv (deriv (guardPotential α l₁))) (guardRadius α l₁) ≠ 0 := by
  rw [deriv3_guardPotential]
  refine ⟨rfl, ?_⟩
  have hr : 0 < guardRadius α l₁ := Real.sqrt_pos.mpr (div_pos hα hl)
  have : 0 < 6 * l₁ * guardRadius α l₁ := by positivity
  simp only
  linarith

/-- Leading-order unstable exponent of the truncated normal form at the cycle radius:
`d(ṙ)/dr |_{r_c} = -α + 3 l₁ r_c² = +2α`; the cubic coefficient `l₁` cancels exactly. -/
@[powerlib_foundation] theorem deriv_guardDrift_guardRadius (hα : 0 ≤ α) (hl : 0 < l₁) :
    deriv (guardDrift α l₁) (guardRadius α l₁) = 2 * α := by
  have h : ∀ r, HasDerivAt (guardDrift α l₁) (-α + 3 * l₁ * r ^ 2) r := by
    intro r
    have h := ((hasDerivAt_id' r).const_mul (-α)).add ((hasDerivAt_pow 3 r).const_mul l₁)
    convert h using 1
    · funext x; simp [guardDrift]
    · simp; ring
  rw [(h _).deriv, guardRadius_sq hα hl]
  field_simp
  ring

/-- In the scaled coordinate `u = r/r_c`: `U(u r_c) - U(r_c) = -ΔU (u² - 1)²`. -/
@[powerlib_foundation] theorem guardPotential_scaled (hα : 0 ≤ α) (hl : 0 < l₁) (u : ℝ) :
    guardPotential α l₁ (u * guardRadius α l₁) - guardPotential α l₁ (guardRadius α l₁) =
      -barrierHeight α l₁ * (u ^ 2 - 1) ^ 2 := by
  have h2 := guardRadius_sq hα hl
  have h4 : guardRadius α l₁ ^ 4 = (α / l₁) ^ 2 := by rw [← h2]; ring
  have hu2 : (u * guardRadius α l₁) ^ 2 = u ^ 2 * (α / l₁) := by rw [mul_pow, h2]
  have hu4 : (u * guardRadius α l₁) ^ 4 = u ^ 4 * (α / l₁) ^ 2 := by rw [mul_pow, h4]
  rw [guardPotential, guardPotential, hu2, hu4, h2, h4, barrierHeight]
  field_simp
  ring

/-- Past the barrier top the integrand `e^{(U(u r_c) - U(r_c))/D̃}` is cut off as
`e^{-X (u²-1)²}`; at `u = 2` it equals `e^{-9X}`, `X = ΔU/D̃`. -/
@[powerlib_foundation] theorem guard_tail_cutoff_at_two (hα : 0 ≤ α) (hl : 0 < l₁) (D : ℝ) :
    Real.exp ((guardPotential α l₁ (2 * guardRadius α l₁) -
        guardPotential α l₁ (guardRadius α l₁)) / D) =
      Real.exp (-9 * (barrierHeight α l₁ / D)) := by
  rw [guardPotential_scaled hα hl]
  congr 1
  ring

/-- The two forms of the first-arrival prefactor agree:
`(√π/2) √(D̃ l₁)/α² = √π/(4 α √X)` with `X = α²/(4 l₁ D̃)`. -/
@[powerlib_foundation] theorem guardPrefactor_eq (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    guardPrefactor α l₁ D =
      Real.sqrt π / (4 * α * Real.sqrt (barrierHeight α l₁ / D)) := by
  have hX : barrierHeight α l₁ / D = (α / 2) ^ 2 / (D * l₁) := by
    rw [barrierHeight]; field_simp; ring
  have hs : Real.sqrt (barrierHeight α l₁ / D) = (α / 2) / Real.sqrt (D * l₁) := by
    rw [hX, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  have hDl : 0 < Real.sqrt (D * l₁) := Real.sqrt_pos.mpr (by positivity)
  rw [hs, guardPrefactor]
  field_simp
  ring

/-- Representability is decided on `ln T = X + ln P`, not on `X` alone. -/
@[powerlib_foundation] theorem log_prefactor_mul_exp {P : ℝ} (hP : 0 < P) (X : ℝ) :
    Real.log (P * Real.exp X) = X + Real.log P := by
  rw [Real.log_mul hP.ne' (Real.exp_pos X).ne', Real.log_exp, add_comm]

/-! ## Lifetime sensitivity of `T(α) = c α⁻² e^{α²/(4 l D)}` -/

/-- **Lifetime ratio (§1.6)**: for `T(α) = c α⁻² e^{α²/(4 l D)}` and `X = α²/(4 l D)`,
`T(α(1+ε))/T(α) = e^{X[(1+ε)²−1]}/(1+ε)²`. -/
@[powerlib_foundation] theorem lifetime_ratio {c α l D ε : ℝ} (hc : c ≠ 0) (hα : α ≠ 0)
    (hε : 1 + ε ≠ 0) :
    (c / (α * (1 + ε)) ^ 2 * exp ((α * (1 + ε)) ^ 2 / (4 * l * D))) /
        (c / α ^ 2 * exp (α ^ 2 / (4 * l * D))) =
      exp (α ^ 2 / (4 * l * D) * ((1 + ε) ^ 2 - 1)) / (1 + ε) ^ 2 := by
  have h1 : exp ((α * (1 + ε)) ^ 2 / (4 * l * D)) =
      exp (α ^ 2 / (4 * l * D) * ((1 + ε) ^ 2 - 1)) * exp (α ^ 2 / (4 * l * D)) := by
    rw [← exp_add]; congr 1; ring
  have hF : exp (α ^ 2 / (4 * l * D)) ≠ 0 := (exp_pos _).ne'
  rw [h1]
  field_simp

/-- `e^{0.1}` to four decimals (Taylor bound, Mathlib `Real.exp_bound`). -/
@[powerlib_foundation] theorem exp_tenth_bounds :
    1.1047 < exp (0.1 : ℝ) ∧ exp (0.1 : ℝ) < 1.1053 := by
  have h := Real.exp_bound (x := (0.1 : ℝ)) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num [abs_of_pos] at h
  constructor <;> linarith [h.1, h.2]

@[powerlib_foundation] theorem exp_two_point_one_bounds :
    8.16 < exp (2.1 : ℝ) ∧ exp (2.1 : ℝ) < 8.17 := by
  have e : exp (2.1 : ℝ) = exp 1 * exp 1 * exp 0.1 := by
    rw [← exp_add, ← exp_add]; norm_num
  obtain ⟨l1, u1⟩ := exp_tenth_bounds
  have l0 := Real.exp_one_gt_d9
  have u0 := Real.exp_one_lt_d9
  have p0 : 0 < exp (1 : ℝ) := exp_pos 1
  rw [e]
  constructor <;> nlinarith [mul_pos p0 p0, mul_lt_mul'' l0 l0 (by norm_num) (by norm_num),
    mul_lt_mul'' u0 u0 (by positivity) (by positivity)]

/-- **Numeric check (§1.6)**: at `X = 10`, `ε = 0.1` the ratio `e^{10·0.21}/1.21` lies in
`(6.74, 6.76)` (the note's closed form `6.75`), while the exponential factor alone exceeds
`8.16`. -/
@[powerlib_foundation] theorem lifetime_ratio_num :
    6.74 < exp ((10 : ℝ) * ((1 + 0.1) ^ 2 - 1)) / (1 + 0.1) ^ 2 ∧
      exp ((10 : ℝ) * ((1 + 0.1) ^ 2 - 1)) / (1 + 0.1) ^ 2 < 6.76 ∧
      8.16 < exp ((10 : ℝ) * ((1 + 0.1) ^ 2 - 1)) := by
  have e : (10 : ℝ) * ((1 + 0.1) ^ 2 - 1) = 2.1 := by norm_num
  rw [e]
  obtain ⟨l, u⟩ := exp_two_point_one_bounds
  refine ⟨?_, ?_, l⟩
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith

end powerlib.Asymptotics.Guard
