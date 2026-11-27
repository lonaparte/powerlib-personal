import theorem.Periodic.RobustThreshold
import theorem.ParametricResonance.RobustVsUniversal
import theorem.ParametricResonance.Kapitza
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The exponential-bound robust threshold never beats the universal one

For the second-order model `m δ̈ + D δ̇ + K(t) δ = 0` with `|K(t) − K̄| ≤ εK̄` in the state
`(δ, δ̇)`, `Periodic.Robust.secondOrder_schurStable` certifies stability for every period and
waveform from any exponential bound `‖e^{τA₀}‖ ≤ K_c e^{−ατ}` (sup norm, `L∞` operator norm) of
`A₀ = oscMatrix c k`, `c = D/(2m)`, `k = K̄/m`, through the robust condition `K_c εk < α`.
`Periodic.Robust.secondOrder_robust_le_universal` showed that this condition implies the
universal condition `ε/√(1 − ε) < D/√(mK̄)` of
`theorem/ParametricResonance/UniversalThreshold.lean` when `m + 2D ≤ 4K̄`, using only `K_c ≥ 1`
and `α ≤ c`; for `m + 2D > 4K̄` those two facts are not enough. This module decides the open
case: **every** exponential bound satisfies

  `α ≤ K_c · k · thresholdCurve ξ = K_c · 2c (√(c² + k) − c)`,  `ξ = c/√k = D/(2√(mK̄))`,

so the exponential-bound robust radius `α/K_c` never exceeds the universal radius
`k · thresholdCurve ξ` (`RobustVsUniversal.thresholdCurve`), and the robust condition implies the
universal one for all `m > 0`, `K̄ > 0`, `D`, in particular in the whole region `m + 2D > 4K̄`.
There is no parameter region in which the exponential-bound robust condition certifies a depth
that the universal condition does not.

The proof bounds `K_c` from below by the impulse response `x(τ) = (e^{τA₀})₀₁` of
`δ̈ + 2cδ̇ + kδ = 0` at one well-chosen time: `|x(τ)| ≤ ‖e^{τA₀}‖ ≤ K_c e^{−ατ}`, and
`x(τ) = e^{−cτ} sin(ντ)/ν`, `e^{−cτ} τ` or `e^{−cτ} sinh(κτ)/κ` (`ν² = k − c²`, `κ² = c² − k`).
With `α ≤ c` (`Robust.card_mul_le_neg_trace`) and the elementary bounds `x e^{1 − x} ≤ 1`,
`sin x ≥ x − x³/6`, `sinh x ≥ x`, `e^x ≥ 1 + x + x²/2`, `e < 2.7182818286` this gives
`α ≤ K_c B` with an explicit `B` satisfying `B² + 4c²B ≤ 4c²k`, which is
`B ≤ 2c(√(c² + k) − c)`. The time is chosen by the damping regime:
* `ν² ≥ 3c²` (damping ratio `ξ ≤ 1/2`): `τ = π/(2ν)`, the first extremum of `sin`, `B = cν`;
* `9c² ≤ 16ν² < 48c²`: `τ = 1/c`, `B = 6c⁴/(6c² − ν²)`;
* `16ν² < 9c²`: `τ = 2/c`, `B = 3e c⁴/(4(3c² − 2ν²))`;
* critical damping `k = c²` and `5κ² ≤ c²`: `τ = 2/c`, `B = e c²/4`;
* `5κ² > c²`: `τ = 1/σ`, `σ = c − κ` the slow decay rate, `B = 2κσ + σ³/c`.
Only the single entry `(e^{τA₀})₀₁` and the rate bound `α ≤ c` enter, so the conclusion holds for
every exponential bound, whatever its constant `K_c(α)` (which has no closed form in the sup norm).

Scope.
* `A₀ = Periodic.oscMatrix c k` with `k > 0` (state `(δ, δ̇)`, `oscMatrix c k = [[0, 1], [−k, −2c]]`)
  and an arbitrary exponential bound `‖e^{τA₀}‖ ≤ K_c e^{−ατ}` for `τ ≥ 0` with rate `α > 0`;
  vectors carry the sup norm and matrices the `L∞` operator norm (`Matrix.Norms.Operator`), as in
  `theorem/Periodic/RobustThreshold.lean`.
* The second-order statements use `c = D/(2m)`, `k = K̄/m`, `m > 0`, `K̄ > 0`, depth `ε ≥ 0`; they
  compare the two sufficient conditions (no claim about the exact stability boundary).
* Generic mathematics; no model family.

Source: the robust threshold `Periodic.Robust.secondOrder_schurStable` and its comparison
`Periodic.Robust.secondOrder_robust_le_universal` (`theorem/Periodic/RobustThreshold.lean`), the
threshold curve `RobustVsUniversal.thresholdCurve` and `RobustVsUniversal.energy_threshold_le_universal`
(`theorem/ParametricResonance/RobustVsUniversal.lean`); the closed forms
`Meissner.exp_oscMatrix`, `Kapitza.exp_oscMatrix_hyp`, `LTI.exp_smul_eq_of_hasDerivAt`; transient
growth of `e^{τA}` as a lower bound for the constant of an exponential bound (Coppel, *Stability
and Asymptotic Behavior of Differential Equations*, 1965; Khalil, *Nonlinear Systems*, 3rd ed.,
§9.1). Closes the item left open by `Periodic.Robust.secondOrder_robust_le_universal`.

Results.
* `exp_oscMatrix_crit` — critical damping: `e^{hA} = e^{−ch}(I + h(A + cI))` for
  `A = oscMatrix c c²`.
* `impulse_oscMatrix` — the impulse response `(e^{τ oscMatrix c k})₀₁` in the three regimes.
* `impulse_le_of_exp_bound` — `|(e^{τA})ᵢⱼ| ≤ K e^{−ατ}` for an exponential bound.
* `rate_le_threshold` — every exponential bound of `oscMatrix c k` has `α ≤ K_c · 2c(√(c² + k) − c)`.
* `secondOrder_rate_le_universal` — the same as `α ≤ K_c (K̄/m) thresholdCurve (D/(2√(mK̄)))`.
* `secondOrder_robust_imp_universal` — for all `m, K̄ > 0`, `D`: the robust condition
  `K_c εK̄/m < α` implies `ε < 1` and the universal condition `ε/√(1 − ε) < D/√(mK̄)`.
-/

noncomputable section
namespace powerlib.Periodic.ExponentialRobust

open Matrix
open powerlib.Periodic (oscMatrix trace_oscMatrix)
open powerlib.ParametricResonance.Meissner (shear rot)
open powerlib.ParametricResonance.Kapitza (hyp)

/-! ## The impulse response of the oscillator -/

section CriticalExp

open scoped Matrix.Norms.Frobenius

/-- **Critical damping.** For `A = oscMatrix c c²` (`δ̈ + 2cδ̇ + c²δ = 0`), `N = A + cI` has
`N² = 0` and `e^{hA} = e^{−ch}(I + hN)`. -/
@[tmio T, powerlib_foundation] theorem exp_oscMatrix_crit (c h : ℝ) :
    NormedSpace.exp (h • oscMatrix c (c ^ 2)) =
      Real.exp (-(c * h)) • (1 + h • (oscMatrix c (c ^ 2) + c • 1)) := by
  set N := oscMatrix c (c ^ 2) + c • (1 : Matrix (Fin 2) (Fin 2) ℝ) with hN
  have hN2 : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hN, oscMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hA : oscMatrix c (c ^ 2) = N - c • 1 := by rw [hN]; abel
  have key := LTI.exp_smul_eq_of_hasDerivAt (A := oscMatrix c (c ^ 2))
    (E := fun s => Real.exp (-(c * s)) • (1 + s • N)) (by simp) (fun s => by
      have he : HasDerivAt (fun s => Real.exp (-(c * s))) (Real.exp (-(c * s)) * (-c)) s := by
        have := ((hasDerivAt_id s).const_mul c).neg.exp
        simpa using this
      have hl := ((hasDerivAt_id' s).smul_const N).const_add (1 : Matrix (Fin 2) (Fin 2) ℝ)
      convert! he.smul hl using 1
      rw [hA]
      simp only [one_smul, mul_smul_comm, smul_mul_assoc, sub_mul, mul_add, mul_one, one_mul, hN2]
      module) h
  exact key.symm

end CriticalExp

open scoped Matrix.Norms.Operator

/-- **The impulse response `x(τ) = (e^{τA})₀₁` of `δ̈ + 2cδ̇ + kδ = 0`** (`δ(0) = 0`, `δ̇(0) = 1`):
`e^{−cτ} sin(ντ)/ν` with `ν = √(k − c²)` (underdamped), `e^{−cτ} τ` (critical),
`e^{−cτ} sinh(κτ)/κ` with `κ = √(c² − k)` (overdamped). -/
@[tmio T, powerlib_foundation] theorem impulse_oscMatrix (c k τ : ℝ) :
    (0 < k - c ^ 2 → (NormedSpace.exp (τ • oscMatrix c k)) 0 1 =
      Real.exp (-(c * τ)) * (Real.sin (√(k - c ^ 2) * τ) / √(k - c ^ 2))) ∧
    (k = c ^ 2 → (NormedSpace.exp (τ • oscMatrix c k)) 0 1 = Real.exp (-(c * τ)) * τ) ∧
    (0 < c ^ 2 - k → (NormedSpace.exp (τ • oscMatrix c k)) 0 1 =
      Real.exp (-(c * τ)) * (Real.sinh (√(c ^ 2 - k) * τ) / √(c ^ 2 - k))) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [ParametricResonance.Meissner.exp_oscMatrix (Real.sq_sqrt h.le)
      (Real.sqrt_pos.mpr h).ne' τ]
    simp [shear, rot]
  · subst h
    rw [exp_oscMatrix_crit]
    simp [oscMatrix]
  · rw [ParametricResonance.Kapitza.exp_oscMatrix_hyp (Real.sq_sqrt h.le)
      (Real.sqrt_pos.mpr h).ne' τ]
    simp [shear, hyp]

/-- **An exponential bound bounds every entry.** `‖e^{τA}‖ ≤ K e^{−ατ}` gives
`|(e^{τA})ᵢⱼ| ≤ K e^{−ατ}` (`L∞` operator norm): the transient of a single response is a lower
bound for `K`. -/
@[tmio T, powerlib_foundation] theorem impulse_le_of_exp_bound {X : Type*} [Fintype X]
    [DecidableEq X] {A : Matrix X X ℝ} {K α : ℝ}
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A)‖ ≤ K * Real.exp (-(α * τ))) {τ : ℝ}
    (hτ : 0 ≤ τ) (i j : X) : |(NormedSpace.exp (τ • A)) i j| ≤ K * Real.exp (-(α * τ)) :=
  (ParametricResonance.Averaging.entry_le_norm _ i j).trans (hexp τ hτ)


/-! ## Elementary bounds -/

/-- `x e^{1 − x} ≤ 1`: for `c > 0` and every `α`, `α e^{1 − α/c} ≤ c`. -/
@[tmio T, powerlib_foundation] private theorem mul_exp_one_sub_le {c α : ℝ} (hc : 0 < c) :
    α * Real.exp (1 - α / c) ≤ c := by
  have h1 : α / c ≤ Real.exp (α / c - 1) := by linarith [Real.add_one_le_exp (α / c - 1)]
  have h2 : α / c * Real.exp (1 - α / c) ≤ Real.exp (α / c - 1) * Real.exp (1 - α / c) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  rw [← Real.exp_add, show α / c - 1 + (1 - α / c) = 0 by ring, Real.exp_zero] at h2
  calc α * Real.exp (1 - α / c) = c * (α / c * Real.exp (1 - α / c)) := by field_simp
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left h2 hc.le
    _ = c := mul_one c

/-- `α e^{(c − α) τ} ≤ c` for `0 < α ≤ c`, `τ ≥ 0`, `cτ ≤ 1`. -/
@[tmio T, powerlib_foundation] private theorem mul_exp_le_of_mul_le_one {c α τ : ℝ} (hα : 0 < α)
    (hαc : α ≤ c) (hτ : 0 ≤ τ) (hcτ : c * τ ≤ 1) : α * Real.exp ((c - α) * τ) ≤ c := by
  have hx1 : (c - α) * τ < 1 := by
    rcases hτ.eq_or_lt with h | h
    · rw [← h, mul_zero]; norm_num
    · have : 0 < α * τ := mul_pos hα h
      have e : (c - α) * τ = c * τ - α * τ := by ring
      linarith
  have h1 : (1 - (c - α) * τ) * Real.exp ((c - α) * τ) ≤ 1 := by
    have := Real.add_one_le_exp (-((c - α) * τ))
    have h2 : (1 - (c - α) * τ) * Real.exp ((c - α) * τ) ≤
        Real.exp (-((c - α) * τ)) * Real.exp ((c - α) * τ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have h3 : α ≤ c * (1 - (c - α) * τ) := by
    have : 0 ≤ (c - α) * (1 - c * τ) := mul_nonneg (by linarith) (by linarith)
    have e : c * (1 - (c - α) * τ) - α = (c - α) * (1 - c * τ) := by ring
    linarith
  calc α * Real.exp ((c - α) * τ) ≤ c * (1 - (c - α) * τ) * Real.exp ((c - α) * τ) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = c * ((1 - (c - α) * τ) * Real.exp ((c - α) * τ)) := by ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = c := mul_one c

/-- From `e^{−cτ} X ≤ K e^{−ατ}`: `X ≤ K e^{(c − α)τ}`. -/
@[tmio T, powerlib_foundation] private theorem le_of_impulse {c α τ X K : ℝ}
    (h : Real.exp (-(c * τ)) * X ≤ K * Real.exp (-(α * τ))) :
    X ≤ K * Real.exp ((c - α) * τ) := by
  have h1 := mul_le_mul_of_nonneg_left h (Real.exp_pos (c * τ)).le
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h1
  calc X ≤ Real.exp (c * τ) * (K * Real.exp (-(α * τ))) := h1
    _ = K * (Real.exp (c * τ) * Real.exp (-(α * τ))) := by ring
    _ = K * Real.exp ((c - α) * τ) := by rw [← Real.exp_add]; ring_nf

/-- The bound at the time `τ = 2/c`: `e^{−2} X ≤ K e^{−2α/c}` gives `α X ≤ K c e/2`. -/
@[tmio T, powerlib_foundation] private theorem two_time {c α K X : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hK : 0 < K) (hX : Real.exp (-(c * (2 / c))) * X ≤ K * Real.exp (-(α * (2 / c)))) :
    α * X ≤ K * (c * Real.exp 1 / 2) := by
  have h1 := le_of_impulse hX
  have h2 : α * Real.exp ((c - α) * (2 / c)) ≤ c * Real.exp 1 / 2 := by
    have e : (c - α) * (2 / c) = 1 + (1 - α / (c / 2)) := by field_simp; ring
    rw [e, Real.exp_add]
    have h3 := mul_exp_one_sub_le (α := α) (half_pos hc)
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos 1).le
    calc α * (Real.exp 1 * Real.exp (1 - α / (c / 2))) =
          Real.exp 1 * (α * Real.exp (1 - α / (c / 2))) := by ring
      _ ≤ Real.exp 1 * (c / 2) := h4
      _ = c * Real.exp 1 / 2 := by ring
  calc α * X ≤ α * (K * Real.exp ((c - α) * (2 / c))) := mul_le_mul_of_nonneg_left h1 hα.le
    _ = K * (α * Real.exp ((c - α) * (2 / c))) := by ring
    _ ≤ K * (c * Real.exp 1 / 2) := mul_le_mul_of_nonneg_left h2 hK.le

/-- Scaling of the normalized inequality: `β² + 4β ≤ 4r` gives
`(c²β)² + 4c²(c²β) ≤ 4c²(c²r)`. -/
@[tmio T, powerlib_foundation] private theorem scaled_quad {c β r : ℝ}
    (h : β ^ 2 + 4 * β ≤ 4 * r) :
    (c ^ 2 * β) ^ 2 + 4 * c ^ 2 * (c ^ 2 * β) ≤ 4 * c ^ 2 * (c ^ 2 * r) := by
  have h1 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ c ^ 4)
  calc (c ^ 2 * β) ^ 2 + 4 * c ^ 2 * (c ^ 2 * β) = c ^ 4 * (β ^ 2 + 4 * β) := by ring
    _ ≤ c ^ 4 * (4 * r) := h1
    _ = 4 * c ^ 2 * (c ^ 2 * r) := by ring

/-- `(e/4)² + e ≤ 16/5` from `e < 2.7182818286`. -/
@[tmio T, powerlib_foundation] private theorem e_quad :
    (Real.exp 1 / 4) ^ 2 + 4 * (Real.exp 1 / 4) ≤ 16 / 5 := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  nlinarith

/-- The normalized inequality of the time `1/c`: `9/16 ≤ W ≤ 3` gives
`β² + 4β ≤ 4(1 + W)` for `β = 1/(1 − W/6)`. -/
@[tmio T, powerlib_foundation] private theorem quad_mid {W : ℝ} (h1 : 9 / 16 ≤ W) (h3 : W ≤ 3) :
    (1 / (1 - W / 6)) ^ 2 + 4 * (1 / (1 - W / 6)) ≤ 4 * (1 + W) := by
  have hu : 0 < 6 - W := by linarith
  have e : (1 / (1 - W / 6)) ^ 2 + 4 * (1 / (1 - W / 6)) =
      (36 + 24 * (6 - W)) / (6 - W) ^ 2 := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3)) (sub_nonneg.mpr h1)]

/-- The normalized inequality of the time `2/c`, underdamped: `5/8 ≤ v ≤ 1`
(`v = 1 − 2W/3`) gives `β² + 4β ≤ 10 − 6v = 4(1 + W)` for `β = (e/4)/v`. -/
@[tmio T, powerlib_foundation] private theorem quad_low {v : ℝ} (hv1 : 5 / 8 ≤ v) (hv2 : v ≤ 1) :
    (Real.exp 1 / 4 / v) ^ 2 + 4 * (Real.exp 1 / 4 / v) ≤ 10 - 6 * v := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hv0 : 0 < v := by linarith
  have e : (Real.exp 1 / 4 / v) ^ 2 + 4 * (Real.exp 1 / 4 / v) =
      (Real.exp 1 ^ 2 / 16 + Real.exp 1 * v) / v ^ 2 := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  have h1 : Real.exp 1 * v ≤ 2.7182818286 * v := mul_le_mul_of_nonneg_right he.le hv0.le
  have h2 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ he0.le he.le 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hv1) (sub_nonneg.mpr hv2),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hv1) (sub_nonneg.mpr hv2)) hv0.le]

/-! ## The bound in each damping regime -/

section Regimes

variable {c k K α : ℝ}

/-- Light damping `ν² ≥ 3c²`: the time `π/(2ν)` gives `α ≤ K cν`. -/
@[tmio T, powerlib_foundation] private theorem bound_quarter {ν : ℝ} (hK : 0 < K) (hα : 0 < α)
    (hαc : α ≤ c) (hc : 0 < c) (hν0 : 0 < ν) (hk : k = c ^ 2 + ν ^ 2) (h3 : 3 * c ^ 2 ≤ ν ^ 2)
    (hx : ∀ τ, 0 ≤ τ → Real.exp (-(c * τ)) * (Real.sin (ν * τ) / ν) ≤ K * Real.exp (-(α * τ))) :
    ∃ B, α ≤ K * B ∧ 0 ≤ B ∧ B ^ 2 + 4 * c ^ 2 * B ≤ 4 * c ^ 2 * k := by
  have hπ := Real.pi_pos
  have hτ0 : 0 ≤ Real.pi / (2 * ν) := by positivity
  have hcτ : c * (Real.pi / (2 * ν)) ≤ 1 := by
    rw [mul_div_assoc', div_le_one (by positivity)]
    have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2]
    have h4 : (c * Real.pi) ^ 2 ≤ (2 * ν) ^ 2 := by
      have : c ^ 2 * Real.pi ^ 2 ≤ c ^ 2 * 10 := mul_le_mul_of_nonneg_left hpi.le (sq_nonneg c)
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h4
  have h1 := le_of_impulse (hx _ hτ0)
  rw [show ν * (Real.pi / (2 * ν)) = Real.pi / 2 by field_simp, Real.sin_pi_div_two] at h1
  have h2 := mul_exp_le_of_mul_le_one hα hαc hτ0 hcτ
  refine ⟨c * ν, ?_, by positivity, ?_⟩
  · have h4 : α * (1 / ν) ≤ K * c :=
      calc α * (1 / ν) ≤ α * (K * Real.exp ((c - α) * (Real.pi / (2 * ν)))) :=
            mul_le_mul_of_nonneg_left h1 hα.le
        _ = K * (α * Real.exp ((c - α) * (Real.pi / (2 * ν)))) := by ring
        _ ≤ K * c := mul_le_mul_of_nonneg_left h2 hK.le
    calc α = α * (1 / ν) * ν := by field_simp
      _ ≤ K * c * ν := mul_le_mul_of_nonneg_right h4 hν0.le
      _ = K * (c * ν) := by ring
  · rw [hk]
    have : 0 ≤ c ^ 2 * ((2 * c - ν) ^ 2 + 2 * ν ^ 2) := by positivity
    nlinarith

/-- Moderate damping `9c² ≤ 16ν² < 48c²`: the time `1/c` gives `α ≤ K c²/(1 − ν²/(6c²))`. -/
@[tmio T, powerlib_foundation] private theorem bound_mid {ν : ℝ} (hK : 0 < K) (hα : 0 < α)
    (hc : 0 < c) (hν0 : 0 < ν) (hk : k = c ^ 2 + ν ^ 2) (h9 : 9 * c ^ 2 ≤ 16 * ν ^ 2)
    (h3 : ν ^ 2 < 3 * c ^ 2)
    (hx : ∀ τ, 0 ≤ τ → Real.exp (-(c * τ)) * (Real.sin (ν * τ) / ν) ≤ K * Real.exp (-(α * τ))) :
    ∃ B, α ≤ K * B ∧ 0 ≤ B ∧ B ^ 2 + 4 * c ^ 2 * B ≤ 4 * c ^ 2 * k := by
  set W := ν ^ 2 / c ^ 2 with hW
  have hc2 : 0 < c ^ 2 := by positivity
  have hW1 : 9 / 16 ≤ W := by rw [hW, le_div_iff₀ hc2]; linarith
  have hW3 : W < 3 := by rw [hW, div_lt_iff₀ hc2]; linarith
  have hv : 0 < 1 - W / 6 := by linarith
  have h1 := le_of_impulse (hx _ (by positivity : (0 : ℝ) ≤ 1 / c))
  rw [show (c - α) * (1 / c) = 1 - α / c by field_simp] at h1
  have hsin : 1 / c * (1 - W / 6) ≤ Real.sin (ν * (1 / c)) / ν := by
    have := Real.sin_ge_sub_cube (x := ν / c) (by positivity)
    rw [show ν * (1 / c) = ν / c by ring, le_div_iff₀ hν0]
    have e : 1 / c * (1 - W / 6) * ν = ν / c - (ν / c) ^ 3 / 6 := by rw [hW]; field_simp
    linarith
  have h2 : α * (1 / c * (1 - W / 6)) ≤ K * c :=
    calc α * (1 / c * (1 - W / 6)) ≤ α * (Real.sin (ν * (1 / c)) / ν) :=
          mul_le_mul_of_nonneg_left hsin hα.le
      _ ≤ α * (K * Real.exp (1 - α / c)) := mul_le_mul_of_nonneg_left h1 hα.le
      _ = K * (α * Real.exp (1 - α / c)) := by ring
      _ ≤ K * c := mul_le_mul_of_nonneg_left (mul_exp_one_sub_le hc) hK.le
  refine ⟨c ^ 2 * (1 / (1 - W / 6)), ?_, by positivity, ?_⟩
  · have h3 : α * (1 - W / 6) ≤ K * c ^ 2 := by
      have := mul_le_mul_of_nonneg_left h2 hc.le
      have e : c * (α * (1 / c * (1 - W / 6))) = α * (1 - W / 6) := by field_simp
      have e' : c * (K * c) = K * c ^ 2 := by ring
      linarith
    rw [show K * (c ^ 2 * (1 / (1 - W / 6))) = K * c ^ 2 / (1 - W / 6) by ring,
      le_div_iff₀ hv]
    exact h3
  · have hk' : k = c ^ 2 * (1 + W) := by rw [hk, hW]; field_simp
    rw [hk']
    exact scaled_quad (quad_mid hW1 hW3.le)

/-- Damping near critical from below, `16ν² < 9c²`: the time `2/c` gives
`α ≤ K (e c²/4)/(1 − 2ν²/(3c²))`. -/
@[tmio T, powerlib_foundation] private theorem bound_low {ν : ℝ} (hK : 0 < K) (hα : 0 < α)
    (hc : 0 < c) (hν0 : 0 < ν) (hk : k = c ^ 2 + ν ^ 2) (h9 : 16 * ν ^ 2 < 9 * c ^ 2)
    (hx : ∀ τ, 0 ≤ τ → Real.exp (-(c * τ)) * (Real.sin (ν * τ) / ν) ≤ K * Real.exp (-(α * τ))) :
    ∃ B, α ≤ K * B ∧ 0 ≤ B ∧ B ^ 2 + 4 * c ^ 2 * B ≤ 4 * c ^ 2 * k := by
  set W := ν ^ 2 / c ^ 2 with hW
  have hc2 : 0 < c ^ 2 := by positivity
  have hW0 : 0 ≤ W := by positivity
  have hW1 : W < 9 / 16 := by rw [hW, div_lt_iff₀ hc2]; linarith
  have hv : 0 < 1 - 2 * W / 3 := by linarith
  have hsin : 2 / c * (1 - 2 * W / 3) ≤ Real.sin (ν * (2 / c)) / ν := by
    have := Real.sin_ge_sub_cube (x := 2 * ν / c) (by positivity)
    rw [show ν * (2 / c) = 2 * ν / c by ring, le_div_iff₀ hν0]
    have e : 2 / c * (1 - 2 * W / 3) * ν = 2 * ν / c - (2 * ν / c) ^ 3 / 6 := by
      rw [hW]; field_simp; ring
    linarith
  have h3 : α * (2 / c * (1 - 2 * W / 3)) ≤ K * (c * Real.exp 1 / 2) :=
    (mul_le_mul_of_nonneg_left hsin hα.le).trans (two_time hc hα hK (hx _ (by positivity)))
  refine ⟨c ^ 2 * (Real.exp 1 / 4 / (1 - 2 * W / 3)), ?_, by positivity, ?_⟩
  · have h4 : α * (1 - 2 * W / 3) ≤ K * (c ^ 2 * (Real.exp 1 / 4)) := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ c / 2)
      have e : c / 2 * (α * (2 / c * (1 - 2 * W / 3))) = α * (1 - 2 * W / 3) := by field_simp
      have e' : c / 2 * (K * (c * Real.exp 1 / 2)) = K * (c ^ 2 * (Real.exp 1 / 4)) := by ring
      linarith
    rw [show K * (c ^ 2 * (Real.exp 1 / 4 / (1 - 2 * W / 3))) =
      K * (c ^ 2 * (Real.exp 1 / 4)) / (1 - 2 * W / 3) by ring, le_div_iff₀ hv]
    exact h4
  · have hk' : k = c ^ 2 * (1 + W) := by rw [hk, hW]; field_simp
    rw [hk']
    have hq := quad_low (v := 1 - 2 * W / 3) (by linarith) (by linarith)
    rw [show 10 - 6 * (1 - 2 * W / 3) = 4 * (1 + W) by ring] at hq
    exact scaled_quad hq

/-- Critical damping, or overdamping with `5κ² ≤ c²`: an impulse response at least
`e^{−cτ} τ` at `τ = 2/c` gives `α ≤ K e c²/4`. -/
@[tmio T, powerlib_foundation] private theorem bound_crit {κ X : ℝ} (hK : 0 < K) (hα : 0 < α)
    (hc : 0 < c) (hk : k = c ^ 2 - κ ^ 2) (h5 : 5 * κ ^ 2 ≤ c ^ 2) (hX : 2 / c ≤ X)
    (hx : Real.exp (-(c * (2 / c))) * X ≤ K * Real.exp (-(α * (2 / c)))) :
    ∃ B, α ≤ K * B ∧ 0 ≤ B ∧ B ^ 2 + 4 * c ^ 2 * B ≤ 4 * c ^ 2 * k := by
  have h3 : α * (2 / c) ≤ K * (c * Real.exp 1 / 2) :=
    (mul_le_mul_of_nonneg_left hX hα.le).trans (two_time hc hα hK hx)
  refine ⟨c ^ 2 * (Real.exp 1 / 4), ?_, by positivity, ?_⟩
  · have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ c / 2)
    have e : c / 2 * (α * (2 / c)) = α := by field_simp
    have e' : c / 2 * (K * (c * Real.exp 1 / 2)) = K * (c ^ 2 * (Real.exp 1 / 4)) := by ring
    linarith
  · have hq := e_quad
    have h1 := scaled_quad (c := c) (β := Real.exp 1 / 4) (r := 4 / 5) (by linarith)
    have h2 : 4 * c ^ 2 * (c ^ 2 * (4 / 5)) ≤ 4 * c ^ 2 * k := by
      rw [hk]
      have : 0 ≤ c ^ 2 * (c ^ 2 - 5 * κ ^ 2) := mul_nonneg (sq_nonneg c) (by linarith)
      nlinarith
    linarith

/-- Strong overdamping `5κ² > c²`: the time `1/σ`, `σ = c − κ`, gives `α ≤ K(2κσ + σ³/c)`. -/
@[tmio T, powerlib_foundation] private theorem bound_over {κ : ℝ} (hK : 0 < K) (hα : 0 < α)
    (hc : 0 < c) (hκ0 : 0 < κ) (hκc : κ < c) (hk : k = c ^ 2 - κ ^ 2) (h5 : c ^ 2 < 5 * κ ^ 2)
    (hx : ∀ τ, 0 ≤ τ →
      Real.exp (-(c * τ)) * (Real.sinh (κ * τ) / κ) ≤ K * Real.exp (-(α * τ))) :
    ∃ B, α ≤ K * B ∧ 0 ≤ B ∧ B ^ 2 + 4 * c ^ 2 * B ≤ 4 * c ^ 2 * k := by
  set σ := c - κ with hσ
  have hσ0 : 0 < σ := by linarith
  have h1 := le_of_impulse (hx _ (by positivity : (0 : ℝ) ≤ 1 / σ))
  set ρ := 2 * κ / σ with hρ
  have hρ0 : 0 < ρ := by positivity
  -- `sinh(κ/σ) = e^{κ/σ}(1 − e^{−ρ})/2` and `e^{(c − α)/σ} = e^{κ/σ} e^{1 − α/σ}`
  have hsh : Real.sinh (κ * (1 / σ)) = Real.exp (κ / σ) * (1 - Real.exp (-ρ)) / 2 := by
    rw [Real.sinh_eq, show κ * (1 / σ) = κ / σ by ring, hρ]
    have : Real.exp (κ / σ) * Real.exp (-(2 * κ / σ)) = Real.exp (-(κ / σ)) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (1 / 2 : ℝ) * this
  have hexp' : Real.exp ((c - α) * (1 / σ)) = Real.exp (κ / σ) * Real.exp (1 - α / σ) := by
    rw [← Real.exp_add]; congr 1
    have hcσ : c = σ + κ := by rw [hσ]; ring
    rw [hcσ]; field_simp; ring
  rw [hsh, hexp'] at h1
  have hE : 0 < Real.exp (κ / σ) := Real.exp_pos _
  have h3 : 1 - Real.exp (-ρ) ≤ 2 * κ * K * Real.exp (1 - α / σ) := by
    have h4 : Real.exp (κ / σ) * (1 - Real.exp (-ρ)) ≤
        Real.exp (κ / σ) * (2 * κ * K * Real.exp (1 - α / σ)) := by
      have h5 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * κ)
      have e : 2 * κ * (Real.exp (κ / σ) * (1 - Real.exp (-ρ)) / 2 / κ) =
          Real.exp (κ / σ) * (1 - Real.exp (-ρ)) := by field_simp
      have e' : 2 * κ * (K * (Real.exp (κ / σ) * Real.exp (1 - α / σ))) =
          Real.exp (κ / σ) * (2 * κ * K * Real.exp (1 - α / σ)) := by ring
      linarith
    exact le_of_mul_le_mul_left h4 hE
  have h2 : α * (1 - Real.exp (-ρ)) ≤ 2 * κ * K * σ :=
    calc α * (1 - Real.exp (-ρ)) ≤ α * (2 * κ * K * Real.exp (1 - α / σ)) :=
          mul_le_mul_of_nonneg_left h3 hα.le
      _ = 2 * κ * K * (α * Real.exp (1 - α / σ)) := by ring
      _ ≤ 2 * κ * K * σ := mul_le_mul_of_nonneg_left (mul_exp_one_sub_le hσ0) (by positivity)
  -- `e^{−ρ} q ≤ 1`, `q = 1 + ρ + ρ²/2`
  have hq : Real.exp (-ρ) * (1 + ρ + ρ ^ 2 / 2) ≤ 1 := by
    have := Real.quadratic_le_exp_of_nonneg hρ0.le
    have h5 := mul_le_mul_of_nonneg_left this (Real.exp_pos (-ρ)).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h5
  refine ⟨2 * κ * σ + σ ^ 3 / c, ?_, by positivity, ?_⟩
  · -- `α (ρ + ρ²/2) ≤ α q (1 − e^{−ρ}) ≤ 2κσK q`, with `ρ + ρ²/2 = 2κc/σ²`
    have hqpos : 0 < 1 + ρ + ρ ^ 2 / 2 := by positivity
    have h6 : α * (ρ + ρ ^ 2 / 2) ≤ 2 * κ * K * σ * (1 + ρ + ρ ^ 2 / 2) := by
      have h7 := mul_le_mul_of_nonneg_right h2 hqpos.le
      have h8 : α * (ρ + ρ ^ 2 / 2) ≤ α * (1 - Real.exp (-ρ)) * (1 + ρ + ρ ^ 2 / 2) := by
        have : α * (1 - Real.exp (-ρ)) * (1 + ρ + ρ ^ 2 / 2) - α * (ρ + ρ ^ 2 / 2) =
            α * (1 - Real.exp (-ρ) * (1 + ρ + ρ ^ 2 / 2)) := by ring
        have : 0 ≤ α * (1 - Real.exp (-ρ) * (1 + ρ + ρ ^ 2 / 2)) :=
          mul_nonneg hα.le (by linarith)
        linarith
      linarith
    have hq1 : ρ + ρ ^ 2 / 2 = 2 * κ * c / σ ^ 2 := by rw [hρ, hσ]; field_simp; ring
    have hq2 : 1 + ρ + ρ ^ 2 / 2 = (σ ^ 2 + 2 * κ * c) / σ ^ 2 := by
      rw [add_assoc, hq1]; field_simp
    rw [hq1, hq2] at h6
    have hs2 : 0 < σ ^ 2 := by positivity
    have h7 : α * (2 * κ * c) ≤ 2 * κ * K * σ * (σ ^ 2 + 2 * κ * c) := by
      have h8 := mul_le_mul_of_nonneg_right h6 hs2.le
      have e1 : α * (2 * κ * c / σ ^ 2) * σ ^ 2 = α * (2 * κ * c) := by field_simp
      have e2 : 2 * κ * K * σ * ((σ ^ 2 + 2 * κ * c) / σ ^ 2) * σ ^ 2 =
          2 * κ * K * σ * (σ ^ 2 + 2 * κ * c) := by field_simp
      linarith
    have h8 : α * c ≤ K * (σ ^ 3 + 2 * κ * c * σ) := by
      have e : 2 * κ * K * σ * (σ ^ 2 + 2 * κ * c) = 2 * κ * (K * (σ ^ 3 + 2 * κ * c * σ)) := by
        ring
      have e' : α * (2 * κ * c) = 2 * κ * (α * c) := by ring
      rw [e, e'] at h7
      exact le_of_mul_le_mul_left h7 (by positivity)
    rw [show K * (2 * κ * σ + σ ^ 3 / c) = K * (σ ^ 3 + 2 * κ * c * σ) / c by
      field_simp; ring, le_div_iff₀ hc]
    exact h8
  · -- `B² + 4c²B − 4c²k = σ³(σ³ − 4cκ²)/c² ≤ 0`
    have hcm : σ ^ 3 ≤ 4 * c * κ ^ 2 := by
      have h4 : 0 < 4 * κ ^ 2 + κ * c - c ^ 2 := by nlinarith
      have h5 : σ ^ 2 ≤ c ^ 2 := by nlinarith
      have h6 : σ ^ 3 ≤ σ * c ^ 2 := by
        have := mul_le_mul_of_nonneg_left h5 hσ0.le
        nlinarith
      have h7 : σ * c ^ 2 ≤ 4 * c * κ ^ 2 := by
        have e : 4 * c * κ ^ 2 - σ * c ^ 2 = c * (4 * κ ^ 2 + κ * c - c ^ 2) := by rw [hσ]; ring
        have : 0 ≤ c * (4 * κ ^ 2 + κ * c - c ^ 2) := mul_nonneg hc.le h4.le
        linarith
      linarith
    rw [hk]
    have e : (2 * κ * σ + σ ^ 3 / c) ^ 2 + 4 * c ^ 2 * (2 * κ * σ + σ ^ 3 / c) -
        4 * c ^ 2 * (c ^ 2 - κ ^ 2) = σ ^ 3 * (σ ^ 3 - 4 * c * κ ^ 2) / c ^ 2 := by
      rw [hσ]; field_simp; ring
    have : σ ^ 3 * (σ ^ 3 - 4 * c * κ ^ 2) / c ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (by linarith)) (by positivity)
    linarith

end Regimes

/-! ## The robust radius against the universal one -/

/-- **Every exponential bound of the oscillator has `α/K_c ≤ 2c(√(c² + k) − c)`.** For
`k > 0` and `‖e^{τ oscMatrix c k}‖ ≤ K e^{−ατ}` (`τ ≥ 0`, `L∞` operator norm) with `α > 0`:
`α ≤ K · 2c(√(c² + k) − c)`. The right side is `k · thresholdCurve (c/√k)`, the universal
radius; the proof evaluates the impulse response at one time chosen by the damping regime
(module docstring) and checks `B² + 4c²B ≤ 4c²k` for the resulting `α ≤ K B`. -/
@[tmio T, powerlib_foundation] theorem rate_le_threshold {c k K α : ℝ} (hk : 0 < k)
    (hα : 0 < α)
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • oscMatrix c k)‖ ≤ K * Real.exp (-(α * τ))) :
    α ≤ K * (2 * c * (√(c ^ 2 + k) - c)) := by
  have hK1 : 1 ≤ K := Robust.one_le_of_exp_bound hexp
  have hK0 : 0 < K := by linarith
  have htr := Robust.card_mul_le_neg_trace hexp
  rw [trace_oscMatrix, Fintype.card_fin] at htr
  have hαc : α ≤ c := by push_cast at htr; linarith
  have hc : 0 < c := hα.trans_le hαc
  have hent : ∀ τ, 0 ≤ τ →
      (NormedSpace.exp (τ • oscMatrix c k)) 0 1 ≤ K * Real.exp (-(α * τ)) :=
    fun τ hτ => (le_abs_self _).trans (impulse_le_of_exp_bound hexp hτ 0 1)
  suffices h : ∃ B, α ≤ K * B ∧ 0 ≤ B ∧ B ^ 2 + 4 * c ^ 2 * B ≤ 4 * c ^ 2 * k by
    obtain ⟨B, hB, hB0, hBq⟩ := h
    refine hB.trans (mul_le_mul_of_nonneg_left ?_ hK0.le)
    have hr2 : √(c ^ 2 + k) ^ 2 = c ^ 2 + k := Real.sq_sqrt (by positivity)
    have hr0 := Real.sqrt_nonneg (c ^ 2 + k)
    have h1 : (B + 2 * c ^ 2) ^ 2 ≤ (2 * c * √(c ^ 2 + k)) ^ 2 := by
      rw [mul_pow, hr2]; nlinarith
    have h2 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
    linarith
  rcases lt_trichotomy (c ^ 2) k with hlt | heq | hgt
  · -- underdamped: `x(τ) = e^{−cτ} sin(ντ)/ν`
    have hpos : 0 < k - c ^ 2 := by linarith
    have hν0 : 0 < √(k - c ^ 2) := Real.sqrt_pos.mpr hpos
    have hk : k = c ^ 2 + √(k - c ^ 2) ^ 2 := by rw [Real.sq_sqrt hpos.le]; ring
    have hx : ∀ τ, 0 ≤ τ → Real.exp (-(c * τ)) * (Real.sin (√(k - c ^ 2) * τ) / √(k - c ^ 2)) ≤
        K * Real.exp (-(α * τ)) := fun τ hτ => by
      rw [← (impulse_oscMatrix c k τ).1 hpos]; exact hent τ hτ
    rcases le_or_gt (3 * c ^ 2) (√(k - c ^ 2) ^ 2) with h3 | h3
    · exact bound_quarter hK0 hα hαc hc hν0 hk h3 hx
    rcases le_or_gt (9 * c ^ 2) (16 * √(k - c ^ 2) ^ 2) with h9 | h9
    · exact bound_mid hK0 hα hc hν0 hk h9 h3 hx
    · exact bound_low hK0 hα hc hν0 hk h9 hx
  · -- critical damping: `x(τ) = e^{−cτ} τ`
    have hx := hent (2 / c) (by positivity)
    rw [(impulse_oscMatrix c k (2 / c)).2.1 heq.symm] at hx
    exact bound_crit (κ := 0) hK0 hα hc (by rw [← heq]; ring) (by nlinarith [sq_nonneg c]) le_rfl hx
  · -- overdamped: `x(τ) = e^{−cτ} sinh(κτ)/κ`
    have hpos : 0 < c ^ 2 - k := by linarith
    have hκ0 : 0 < √(c ^ 2 - k) := Real.sqrt_pos.mpr hpos
    have hκ2 : √(c ^ 2 - k) ^ 2 = c ^ 2 - k := Real.sq_sqrt hpos.le
    have hk : k = c ^ 2 - √(c ^ 2 - k) ^ 2 := by rw [hκ2]; ring
    have hκc : √(c ^ 2 - k) < c :=
      (pow_lt_pow_iff_left₀ hκ0.le hc.le two_ne_zero).mp (by rw [hκ2]; linarith)
    have hx : ∀ τ, 0 ≤ τ →
        Real.exp (-(c * τ)) * (Real.sinh (√(c ^ 2 - k) * τ) / √(c ^ 2 - k)) ≤
          K * Real.exp (-(α * τ)) := fun τ hτ => by
      rw [← (impulse_oscMatrix c k τ).2.2 hpos]; exact hent τ hτ
    rcases le_or_gt (5 * √(c ^ 2 - k) ^ 2) (c ^ 2) with h5 | h5
    · have hX : 2 / c ≤ Real.sinh (√(c ^ 2 - k) * (2 / c)) / √(c ^ 2 - k) := by
        rw [le_div_iff₀ hκ0]
        have := Real.self_le_sinh_iff.mpr (by positivity : (0 : ℝ) ≤ √(c ^ 2 - k) * (2 / c))
        linarith
      exact bound_crit hK0 hα hc hk h5 hX (hx _ (by positivity))
    · exact bound_over hK0 hα hc hκ0 hκc hk h5 hx

/-- **The robust radius never exceeds the universal radius, second-order model.** For
`m δ̈ + D δ̇ + K(t) δ = 0` in the state `(δ, δ̇)`, `m > 0`, `K̄ > 0`, every exponential bound
`‖e^{τA₀}‖ ≤ K_c e^{−ατ}` of `A₀ = oscMatrix (D/(2m)) (K̄/m)` with `α > 0` satisfies
`α/K_c ≤ (K̄/m) · thresholdCurve (D/(2√(mK̄)))`: the depth `α m/(K_c K̄)` certified by the
robust condition is at most the universal threshold `thresholdCurve ξ`, `ξ = D/(2√(mK̄))`, of
`RobustVsUniversal.energy_threshold_le_universal`, in every parameter region. -/
@[tmio T, powerlib_foundation] theorem secondOrder_rate_le_universal {m D Kbar Kc α : ℝ}
    (hm : 0 < m) (hKbar : 0 < Kbar) (hα : 0 < α)
    (hexp : ∀ τ, 0 ≤ τ →
      ‖NormedSpace.exp (τ • oscMatrix (D / (2 * m)) (Kbar / m))‖ ≤ Kc * Real.exp (-(α * τ))) :
    α ≤ Kc * (Kbar / m * ParametricResonance.RobustVsUniversal.thresholdCurve
      (D / (2 * √(m * Kbar)))) := by
  have h := rate_le_threshold (div_pos hKbar hm) hα hexp
  refine h.trans_eq ?_
  congr 1
  have hk : 0 < Kbar / m := div_pos hKbar hm
  have hsk : 0 < √(Kbar / m) := Real.sqrt_pos.mpr hk
  have hsk2 : √(Kbar / m) ^ 2 = Kbar / m := Real.sq_sqrt hk.le
  -- `D/(2√(mK̄)) = c/√k` and `k thresholdCurve(c/√k) = 2c(√(c² + k) − c)`
  have hξ : D / (2 * √(m * Kbar)) = D / (2 * m) / √(Kbar / m) := by
    have : √(m * Kbar) = m * √(Kbar / m) := by
      rw [show m * Kbar = m ^ 2 * (Kbar / m) by field_simp, Real.sqrt_mul (sq_nonneg m),
        Real.sqrt_sq hm.le]
    rw [this]; field_simp
  rw [hξ, ParametricResonance.RobustVsUniversal.thresholdCurve]
  set c := D / (2 * m)
  set k := Kbar / m
  have hroot : √(1 + (c / √k) ^ 2) = √(c ^ 2 + k) / √k := by
    rw [div_pow, hsk2, show 1 + c ^ 2 / k = (c ^ 2 + k) / k by field_simp; ring,
      Real.sqrt_div' _ hk.le]
  rw [hroot]
  field_simp
  rw [hsk2]
  ring

/-- **The exponential-bound robust condition implies the universal condition, in every region.**
For `m δ̈ + D δ̇ + K(t) δ = 0` with `m > 0`, `K̄ > 0`, `ε ≥ 0` and any exponential bound
`‖e^{τA₀}‖ ≤ K_c e^{−ατ}` of `A₀ = oscMatrix (D/(2m)) (K̄/m)`: the robust condition
`K_c εK̄/m < α` of `Periodic.Robust.secondOrder_schurStable` implies `ε < 1` and the universal
condition `ε/√(1 − ε) < D/√(mK̄)` of
`ParametricResonance.UniversalThreshold.schurStable_of_threshold` — without the restriction
`m + 2D ≤ 4K̄` of `Periodic.Robust.secondOrder_robust_le_universal`. The exponential-bound robust
threshold never certifies a depth that the universal threshold does not
(`secondOrder_rate_le_universal`). -/
@[tmio T, powerlib_foundation] theorem secondOrder_robust_imp_universal {m D Kbar Kc α ε : ℝ}
    (hm : 0 < m) (hKbar : 0 < Kbar) (hε : 0 ≤ ε)
    (hexp : ∀ τ, 0 ≤ τ →
      ‖NormedSpace.exp (τ • oscMatrix (D / (2 * m)) (Kbar / m))‖ ≤ Kc * Real.exp (-(α * τ)))
    (hrob : Kc * (ε * Kbar / m) < α) :
    ε < 1 ∧ ε / √(1 - ε) < D / √(m * Kbar) := by
  have hK1 : 1 ≤ Kc := Robust.one_le_of_exp_bound hexp
  have hK0 : 0 < Kc := by linarith
  have hk : 0 < Kbar / m := div_pos hKbar hm
  have h0 : 0 ≤ Kc * (ε * Kbar / m) := mul_nonneg hK0.le (by positivity)
  have hα : 0 < α := h0.trans_lt hrob
  have htr := Robust.card_mul_le_neg_trace hexp
  rw [trace_oscMatrix, Fintype.card_fin] at htr
  have hD : 0 < D := by
    have : 0 < D / (2 * m) := by push_cast at htr; linarith
    have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * m)).mp this
    exact this
  have h := secondOrder_rate_le_universal hm hKbar hα hexp
  have hlt : ε < ParametricResonance.RobustVsUniversal.thresholdCurve (D / (2 * √(m * Kbar))) := by
    have h1 : Kc * (Kbar / m * ε) < Kc * (Kbar / m *
        ParametricResonance.RobustVsUniversal.thresholdCurve (D / (2 * √(m * Kbar)))) := by
      have e : Kc * (ε * Kbar / m) = Kc * (Kbar / m * ε) := by ring
      linarith
    exact lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_left h1 hK0.le) hk.le
  -- `thresholdCurve x < 1`
  have h1 : ParametricResonance.RobustVsUniversal.thresholdCurve (D / (2 * √(m * Kbar))) < 1 := by
    set x := D / (2 * √(m * Kbar))
    have hx : 0 < x := by positivity
    have hs2 : √(1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ √(1 + x ^ 2) := Real.sqrt_nonneg _
    have hxs : x < √(1 + x ^ 2) := by nlinarith
    unfold ParametricResonance.RobustVsUniversal.thresholdCurve
    nlinarith
  have hε1 : ε < 1 := hlt.trans h1
  exact ⟨hε1, ((ParametricResonance.RobustVsUniversal.energy_threshold_le_universal hm hKbar
    hD).2.2 ε hε hε1).mpr hlt⟩

end powerlib.Periodic.ExponentialRobust
