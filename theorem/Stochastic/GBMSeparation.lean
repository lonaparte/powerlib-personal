import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Brownian
import Mathlib.Probability.StrongLaw

/-! # Geometric Brownian motion: almost-sure versus moment exponents

Scalar geometric Brownian motion can be almost surely stable while its second moment diverges:
almost-sure stability does not imply moment stability.

Scope.
* GBM is the explicit functional `X_t = x₀ exp((a − b²/2) t + b W_t)` of a Mathlib pre-Brownian
  motion `W` (`Stochastic.BM.gbm`); that it solves the SDE is not claimed.
* The almost-sure exponent is taken along integer times `t = n` (the discrete-time exponent
  used in `Stochastic.StochStab.as_exponent_le`).
* A result about an explicit process, not an engineering stability conclusion.

Source: work-sync theory/T-lyapunov-stability-stochastic.md (almost-sure Lyapunov exponent
`λ_as = lim (1/t) log |X_t|` versus moment exponent `Λ(p) = lim (1/t) log E|X_t|^p`, `λ_as ≤
Λ(p)/p`; scalar GBM `dX = a X dt + b X dW` has `λ_as = a − b²/2` and `Λ(2) = 2a + b²`, so for
`a − b²/2 < 0 < a + b²/2` it is almost surely stable but second-moment unstable).

Results.
* `brownian_div_tendsto_zero` — `W_n / n → 0` a.s. (strong law of large numbers for the i.i.d.
  `N(0,1)` unit increments, Mathlib `strong_law_ae`).
* `gbm_as_exponent` — `(1/n) log |X_n| → a − b²/2` a.s.
* `gbm_as_stable_moment_unstable` — if `a − b²/2 < 0 < a + b²/2`, then `X_n → 0` a.s. while
  `E X_n² → ∞` (indeed `Λ(2) = 2a + b² > 0`, `Stochastic.BM.gbm_log_second_moment`): the
  inequality `λ_as ≤ Λ(2)/2` holds with opposite signs, so a.s. stability does not imply moment
  stability.
-/

noncomputable section
namespace powerlib.Stochastic.BM

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Unit-time increments `W_{k+1} − W_k`. -/
def unitIncr (B : ℝ≥0 → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := B ((k + 1 : ℕ) : ℝ≥0) ω - B (k : ℝ≥0) ω

@[tmio T, powerlib_foundation] theorem unitIncr_hasLaw (hB : IsPreBrownianReal B P) (k : ℕ) :
    HasLaw (unitIncr B k) (gaussianReal 0 1) P := by
  have h := increment_hasLaw hB (s := (k : ℝ≥0)) (t := ((k + 1 : ℕ) : ℝ≥0))
    (by exact_mod_cast Nat.le_succ k)
  have e : ((k + 1 : ℕ) : ℝ≥0) - (k : ℝ≥0) = 1 := by
    rw [Nat.cast_succ, add_tsub_cancel_left]
  rw [e] at h
  exact h

@[powerlib_foundation] theorem unitIncr_indep (hB : IsPreBrownianReal B P) :
    Pairwise (Function.onFun (fun X Y : Ω → ℝ => IndepFun X Y P) (unitIncr B)) := by
  have h := hB.hasIndepIncrements.nat (P := P) (t := fun k : ℕ => (k : ℝ≥0))
    Nat.mono_cast
  intro i j hij
  exact h.indepFun hij

@[powerlib_foundation] theorem unitIncr_identDistrib (hB : IsPreBrownianReal B P) (i : ℕ) :
    IdentDistrib (unitIncr B i) (unitIncr B 0) P P :=
  ⟨(unitIncr_hasLaw hB i).aemeasurable, (unitIncr_hasLaw hB 0).aemeasurable,
    (unitIncr_hasLaw hB i).map_eq.trans (unitIncr_hasLaw hB 0).map_eq.symm⟩

/-- **`W_n / n → 0` almost surely** (strong law of large numbers). -/
@[powerlib_foundation] theorem brownian_div_tendsto_zero (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => B (n : ℝ≥0) ω / n) atTop (𝓝 0) := by
  have hint : Integrable (unitIncr B 0) P :=
    (unitIncr_hasLaw hB 0).integrable (memLp_one_iff_integrable.mp (by
      simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 1))
  have hmean : ∫ ω, unitIncr B 0 ω ∂P = 0 := by
    rw [(unitIncr_hasLaw hB 0).integral_eq, integral_id_gaussianReal]
  have hslln := strong_law_ae (μ := P) (unitIncr B) hint (unitIncr_indep hB)
    (unitIncr_identDistrib hB)
  have h0 : B 0 =ᵐ[P] fun _ => 0 := by
    have h := hB.hasLaw_eval 0
    rw [show ((0 : ℝ≥0) : ℝ≥0) = 0 from rfl, gaussianReal_zero_var] at h
    exact h.ae_eq_of_dirac
  filter_upwards [hslln, h0] with ω hω hω0
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  have e := sum_range_sub (fun k : ℕ => B (k : ℝ≥0) ω) n
  rw [smul_eq_mul, show (∑ i ∈ range n, unitIncr B i ω) = B (n : ℝ≥0) ω - B ((0 : ℕ) : ℝ≥0) ω
    from e, Nat.cast_zero, hω0, sub_zero, inv_mul_eq_div]

/-- **Almost-sure exponent of GBM**: `(1/n) log |X_n| → a − b²/2` a.s. -/
@[powerlib_foundation] theorem gbm_as_exponent (hB : IsPreBrownianReal B P) {x₀ : ℝ}
    (hx : x₀ ≠ 0) (a b : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => log |gbm x₀ a b B n ω| / n) atTop (𝓝 (a - b ^ 2 / 2)) := by
  filter_upwards [brownian_div_tendsto_zero hB] with ω hω
  have hlog : ∀ n : ℕ, n ≠ 0 → log |gbm x₀ a b B n ω| / n =
      log |x₀| / n + (a - b ^ 2 / 2) + b * (B (n : ℝ≥0) ω / n) := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [gbm, abs_mul, abs_exp, log_mul (abs_pos.mpr hx).ne' (exp_pos _).ne', log_exp,
      NNReal.coe_natCast]
    field_simp
    ring
  have hlim : Tendsto (fun n : ℕ => log |x₀| / n + (a - b ^ 2 / 2) + b * (B (n : ℝ≥0) ω / n))
      atTop (𝓝 (0 + (a - b ^ 2 / 2) + b * 0)) :=
    ((tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds).add (hω.const_mul b)
  rw [zero_add, mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (hlog n hn).symm

/-- **A.s. stable but second-moment unstable**: if `a − b²/2 < 0 < a + b²/2`, then `X_n → 0`
almost surely while `E X_n² → ∞`. -/
@[powerlib_foundation] theorem gbm_as_stable_moment_unstable (hB : IsPreBrownianReal B P)
    {x₀ : ℝ} (hx : x₀ ≠ 0) {a b : ℝ} (h1 : a - b ^ 2 / 2 < 0) (h2 : 0 < a + b ^ 2 / 2) :
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => gbm x₀ a b B n ω) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => ∫ ω, gbm x₀ a b B n ω ^ 2 ∂P) atTop atTop := by
  constructor
  · filter_upwards [gbm_as_exponent hB hx a b] with ω hω
    have hlog : Tendsto (fun n : ℕ => (n : ℝ) * (log |gbm x₀ a b B n ω| / n)) atTop atBot :=
      tendsto_natCast_atTop_atTop.atTop_mul_neg h1 hω
    have hlog' : Tendsto (fun n : ℕ => log |gbm x₀ a b B n ω|) atTop atBot := by
      refine hlog.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
    have habs : Tendsto (fun n : ℕ => |gbm x₀ a b B n ω|) atTop (𝓝 0) := by
      have h := tendsto_exp_atBot.comp hlog'
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [exp_log]
      exact abs_pos.mpr (by unfold gbm; exact mul_ne_zero hx (exp_pos _).ne')
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  · have hc : 0 < 2 * a + b ^ 2 := by linarith
    have hx2 : 0 < x₀ ^ 2 := by positivity
    have e : (fun n : ℕ => ∫ ω, gbm x₀ a b B n ω ^ 2 ∂P) =
        fun n : ℕ => x₀ ^ 2 * exp ((2 * a + b ^ 2) * n) := by
      funext n
      rw [gbm_second_moment hB, NNReal.coe_natCast]
    rw [e]
    exact (tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc)).const_mul_atTop hx2

end powerlib.Stochastic.BM
