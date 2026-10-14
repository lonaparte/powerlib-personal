import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation

/-! # Brownian motion: Mathlib interface, martingales of the natural filtration, GBM moments

Mathlib's Brownian motion with its basic laws, the three classical martingales of its natural
filtration, and the moments of geometric Brownian motion.

Scope.
* Brownian motion is Mathlib's `ProbabilityTheory.IsPreBrownianReal` / `IsBrownianReal`
  (finite-dimensional laws of BM, resp. plus a.s. continuous paths) on a probability space; time
  is `ℝ≥0`. The natural filtration is `Filtration.natural B`, which needs each `B t` to be
  (strongly) measurable — an explicit hypothesis.
* No Itô integral is used: the martingale statements are proved from independence of increments
  (`indepFun_shift`, the weak Markov property) and `condExp_indep_eq`.
* GBM is treated as the explicit functional `X₀ exp((μ − σ²/2)t + σW_t)` of `W`; that it solves
  the SDE `dX = μX dt + σX dW` is **not** claimed (Itô calculus).

Source: work-sync theory/T-sde-systems.md §1.2 (Wiener process: `W₀ = 0`, independent
Gaussian increments `W_t − W_s ~ N(0, t − s)`, `Cov(W_s, W_t) = min(s, t)`), §1.9 (geometric
Brownian motion `X_t = X₀ exp((μ − σ²/2)t + σW_t)`);
theory/T-martingales-stopping-times.md §1.2 (`W_t` and `W_t² − t` are martingales), §1.6.2
(`exp(θW_t − θ²t/2)` is a martingale); theory/T-markov-processes.md §1.6 item 2 (Brownian
motion: the future increment is independent of the past).

Results.
* Mathlib wrappers (Mathlib declarations in brackets): `brownian_hasLaw` [`hasLaw_eval`],
  `brownian_mean` [`integral_eval`], `brownian_cov` [`covariance_eval`],
  `brownian_indepIncrements` [`hasIndepIncrements`], `brownian_increment_hasLaw` [`hasLaw_sub`],
  `brownian_weakMarkov` [`IsPreBrownianReal.indepFun_shift`], `brownian_scaling`
  [`IsBrownianReal.smul`].
* `condExp_increment`, `condExp_increment_zero` — increments are independent of the past:
  `E[f(W_t − W_s) | 𝓕_s] = E f(W_t − W_s)` a.s., in particular `E[W_t − W_s | 𝓕_s] = 0`.
* `martingale_brownian`, `martingale_brownian_sq`, `martingale_brownian_exp` — `W_t`,
  `W_t² − t` and `exp(θ W_t − θ² t/2)` are martingales for the natural filtration.
* `gbm_mean`, `gbm_second_moment`, `gbm_variance`, `gbm_log_second_moment` — for
  `gbm` `X_t = x₀ exp((μ − σ²/2) t + σ W_t)`: `E X_t = x₀ e^{μ t}`,
  `E X_t² = x₀² e^{(2μ + σ²) t}`, `Var X_t = x₀² e^{2μt} (e^{σ² t} − 1)`, and the second-moment
  Lyapunov exponent `Λ(2) = 2μ + σ²` (from `integral_exp_brownian`, `E[e^{c W_t}] = e^{c² t/2}`).
-/

noncomputable section
namespace powerlib.Stochastic.BM

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ## Mathlib wrappers: Brownian motion -/

/-- `W_t ~ N(0, t)` (Mathlib `IsPreBrownianReal.hasLaw_eval`). -/
@[powerlib_foundation] theorem brownian_hasLaw (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    HasLaw (B t) (gaussianReal 0 t) P := hB.hasLaw_eval t

/-- `E W_t = 0` (Mathlib `IsPreBrownianReal.integral_eval`). -/
@[powerlib_foundation] theorem brownian_mean (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∫ ω, B t ω ∂P = 0 := hB.integral_eval t

/-- `Cov(W_s, W_t) = min(s, t)` (Mathlib `IsPreBrownianReal.covariance_eval`). -/
@[powerlib_foundation] theorem brownian_cov (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[B s, B t; P] = min s t := hB.covariance_eval s t

/-- Independent increments (Mathlib `IsPreBrownianReal.hasIndepIncrements`). -/
@[powerlib_foundation] theorem brownian_indepIncrements (hB : IsPreBrownianReal B P) :
    HasIndepIncrements B P := hB.hasIndepIncrements

/-- `W_s − W_t ~ N(0, |s − t|)` (Mathlib `IsPreBrownianReal.hasLaw_sub`). -/
@[powerlib_foundation] theorem brownian_increment_hasLaw (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) : HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) P := hB.hasLaw_sub s t

/-- **Weak Markov property** (Mathlib `IsPreBrownianReal.indepFun_shift`): the shifted process
`u ↦ W_{t₀+u} − W_{t₀}` is independent of the past `(W_r)_{r ≤ t₀}`. -/
@[powerlib_foundation] theorem brownian_weakMarkov (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    IndepFun (fun ω t => B (t₀ + t) ω - B t₀ ω) (fun ω (t : Set.Iic t₀) => B t ω) P :=
  hB.indepFun_shift t₀

/-- Brownian scaling `t ↦ c^{−1/2} W_{ct}` (Mathlib `IsBrownianReal.smul`). -/
@[powerlib_foundation] theorem brownian_scaling (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω => (√c)⁻¹ * B (c * t) ω) P := hB.smul hc

/-! ## Increments and the natural filtration -/

/-- Second moment of a centred Gaussian. -/
@[powerlib_foundation] theorem integral_sq_gaussianReal_zero (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The increment `W_t − W_s` (`s ≤ t`) has law `N(0, t − s)`. -/
@[powerlib_foundation] theorem increment_hasLaw (hB : IsPreBrownianReal B P) {s t : ℝ≥0}
    (hst : s ≤ t) : HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s)) P := by
  have h := hB.hasLaw_sub t s
  have e : nndist t.1 s.1 = t - s := by
    apply NNReal.eq
    rw [coe_nndist, Real.dist_eq, NNReal.coe_sub hst]
    exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hst))
  rw [e] at h
  exact h

/-- The increment after `s` is measurable for the σ-algebra generated by the shifted process. -/
@[powerlib_foundation] theorem increment_measurable_shift {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[MeasurableSpace.comap (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω)
      MeasurableSpace.pi] (fun ω => B t ω - B s ω) := by
  have e : (fun ω => B t ω - B s ω) =
      (fun x : ℝ≥0 → ℝ => x (t - s)) ∘ (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω) := by
    funext ω; simp [add_tsub_cancel_of_le hst]
  rw [e]
  exact (measurable_pi_apply (t - s)).comp (Measurable.of_comap_le le_rfl)

/-- **Increments are independent of the past**: for any function `f` of the increment
`W_t − W_s`, `E[f(W_t − W_s) | 𝓕_s] = E f(W_t − W_s)` a.s. (natural filtration). -/
@[powerlib_foundation] theorem condExp_increment (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {f : ℝ → ℝ}
    (hf : Measurable f) :
    P[fun ω => f (B t ω - B s ω) | Filtration.natural B hm s] =ᵐ[P]
      fun _ => ∫ ω, f (B t ω - B s ω) ∂P := by
  have hind := hB.indepFun_shift s
  rw [IndepFun_iff_Indep] at hind
  have hshift : Measurable (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω) :=
    measurable_pi_iff.mpr fun u => ((hm (s + u)).measurable.sub (hm s).measurable)
  have hle₁ : MeasurableSpace.comap (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω)
      MeasurableSpace.pi ≤ mΩ := hshift.comap_le
  have hnat := Filtration.natural_eq_comap B hm s
  have hle₂ : Filtration.natural B hm s ≤ mΩ := (Filtration.natural B hm).le s
  have hfm : StronglyMeasurable[MeasurableSpace.comap
      (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω) MeasurableSpace.pi]
      (fun ω => f (B t ω - B s ω)) :=
    (hf.comp (increment_measurable_shift hst)).stronglyMeasurable
  rw [← hnat] at hind
  exact condExp_indep_eq hle₁ hle₂ hfm hind

omit [IsProbabilityMeasure P] in
/-- `W_t` is integrable and square integrable. -/
@[powerlib_foundation] theorem memLp_two (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    MemLp (B t) 2 P :=
  (hB.hasLaw_eval t).memLp (memLp_id_gaussianReal 2)

/-- `E[W_t − W_s | 𝓕_s] = 0`. -/
@[powerlib_foundation] theorem condExp_increment_zero (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[B t - B s | Filtration.natural B hm s] =ᵐ[P] fun _ => (0 : ℝ) := by
  have hint : ∀ r, Integrable (B r) P := fun r => (memLp_two hB r).integrable one_le_two
  have h := condExp_increment hB hm hst (f := fun x => x) measurable_id'
  have hmean : ∫ ω, B t ω - B s ω ∂P = 0 := by
    rw [integral_sub (hint t) (hint s), hB.integral_eval, hB.integral_eval, sub_self]
  rw [hmean] at h
  exact h

/-! ## Martingales of Brownian motion (no Itô integral needed) -/

/-- **`W` is a martingale** for its natural filtration (T-martingales §1.2). -/
@[powerlib_foundation] theorem martingale_brownian (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) : Martingale B (Filtration.natural B hm) P := by
  refine ⟨Filtration.stronglyAdapted_natural hm, fun s t hst => ?_⟩
  have hint : ∀ r, Integrable (B r) P := fun r => (memLp_two hB r).integrable one_le_two
  have hsplit : B t = (B t - B s) + B s := by abel
  rw [hsplit]
  refine (condExp_add ((hint t).sub (hint s)) (hint s) _).trans ?_
  rw [condExp_of_stronglyMeasurable ((Filtration.natural B hm).le s)
    (Filtration.stronglyAdapted_natural hm s) (hint s)]
  filter_upwards [condExp_increment_zero hB hm hst] with ω hω
  simp only [Pi.add_apply] at hω ⊢
  rw [hω, zero_add]

/-- **`W_t² − t` is a martingale** for the natural filtration (T-martingales §1.2). -/
@[powerlib_foundation] theorem martingale_brownian_sq (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) :
    Martingale (fun t ω => B t ω ^ 2 - t) (Filtration.natural B hm) P := by
  have hadapt := Filtration.stronglyAdapted_natural hm
  refine ⟨fun t => ((hadapt t).pow 2).sub stronglyMeasurable_const, fun s t hst => ?_⟩
  show P[fun ω => B t ω ^ 2 - (t : ℝ) | Filtration.natural B hm s] =ᵐ[P]
    fun ω => B s ω ^ 2 - (s : ℝ)
  have hL2 := memLp_two hB
  have hint : ∀ r, Integrable (B r) P := fun r => (hL2 r).integrable one_le_two
  have hsq : ∀ r, Integrable (fun ω => B r ω ^ 2) P := fun r => (hL2 r).integrable_sq
  set F := Filtration.natural B hm s
  have hle : F ≤ mΩ := (Filtration.natural B hm).le s
  -- pieces
  have hD : Integrable (fun ω => (B t ω - B s ω) ^ 2) P := ((hL2 t).sub (hL2 s)).integrable_sq
  have hX : Integrable (fun ω => B s ω * (B t ω - B s ω)) P :=
    (hL2 s).integrable_mul ((hL2 t).sub (hL2 s))
  have hDm : ∫ ω, (B t ω - B s ω) ^ 2 ∂P = (t : ℝ) - s := by
    have := (increment_hasLaw hB hst).integral_comp (f := fun x : ℝ => x ^ 2)
      (by fun_prop)
    simp only [Function.comp_def] at this
    rw [this, integral_sq_gaussianReal_zero]
    push_cast [hst]; ring
  have h1 := condExp_increment hB hm hst (f := fun x => x ^ 2) (by fun_prop)
  have h2 : P[fun ω => B s ω * (B t ω - B s ω) | F] =ᵐ[P] fun ω => B s ω * 0 := by
    have := condExp_mul_of_stronglyMeasurable_left (m := F) (hadapt s) hX
      ((hint t).sub (hint s))
    refine this.trans ?_
    filter_upwards [condExp_increment_zero hB hm hst] with ω hω
    simp only [Pi.mul_apply] at hω ⊢
    rw [show (fun ω => B t ω - B s ω) = B t - B s from rfl, hω]
  have h3 : P[fun ω => B s ω ^ 2 - (t : ℝ) | F] = fun ω => B s ω ^ 2 - (t : ℝ) :=
    condExp_of_stronglyMeasurable hle (((hadapt s).pow 2).sub stronglyMeasurable_const)
      ((hsq s).sub (integrable_const _))
  have hsplit : (fun ω => B t ω ^ 2 - (t : ℝ)) = (fun ω => (B t ω - B s ω) ^ 2) +
      (fun ω => 2 * (B s ω * (B t ω - B s ω))) + (fun ω => B s ω ^ 2 - (t : ℝ)) := by
    funext ω; simp only [Pi.add_apply]; ring
  have hc : Integrable (fun ω => B s ω ^ 2 - (t : ℝ)) P := (hsq s).sub (integrable_const _)
  have h2X : Integrable (fun ω => 2 * (B s ω * (B t ω - B s ω))) P := hX.const_mul 2
  have hAB : Integrable ((fun ω => (B t ω - B s ω) ^ 2) +
      fun ω => 2 * (B s ω * (B t ω - B s ω))) P := hD.add h2X
  rw [hsplit]
  refine (condExp_add hAB hc _).trans ?_
  refine (EventuallyEq.add (condExp_add hD h2X _) EventuallyEq.rfl).trans ?_
  rw [h3]
  have h2' : P[fun ω => 2 * (B s ω * (B t ω - B s ω)) | F] =ᵐ[P]
      fun ω => 2 * (B s ω * 0) := by
    refine (condExp_smul (2 : ℝ) (fun ω => B s ω * (B t ω - B s ω)) F).trans ?_
    filter_upwards [h2] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω ⊢
    rw [hω]
  filter_upwards [h1, h2'] with ω hω1 hω2
  simp only [Pi.add_apply] at hω1 hω2 ⊢
  rw [hω1, hω2, hDm]
  ring

/-- **Exponential martingale** `exp(θ W_t − θ² t/2)` (T-martingales §1.6.2). -/
@[powerlib_foundation] theorem martingale_brownian_exp (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (θ : ℝ) :
    Martingale (fun t ω => exp (θ * B t ω - θ ^ 2 * t / 2)) (Filtration.natural B hm) P := by
  have hadapt := Filtration.stronglyAdapted_natural hm
  refine ⟨fun t => continuous_exp.comp_stronglyMeasurable
    (((hadapt t).const_mul θ).sub stronglyMeasurable_const), fun s t hst => ?_⟩
  show P[fun ω => exp (θ * B t ω - θ ^ 2 * t / 2) | Filtration.natural B hm s] =ᵐ[P]
    fun ω => exp (θ * B s ω - θ ^ 2 * s / 2)
  set F := Filtration.natural B hm s
  have hle : F ≤ mΩ := (Filtration.natural B hm).le s
  -- integrability of exponentials of Gaussians
  have hexpint : ∀ r (c : ℝ), Integrable (fun ω => exp (c * B r ω)) P := fun r c =>
    (hB.hasLaw_eval r).integrable_comp (f := fun x => exp (c * x))
      (integrable_exp_mul_gaussianReal c)
  have hincint : Integrable (fun ω => exp (θ * (B t ω - B s ω))) P :=
    (increment_hasLaw hB hst).integrable_comp (f := fun x => exp (θ * x))
      (integrable_exp_mul_gaussianReal θ)
  have hmgf : ∫ ω, exp (θ * (B t ω - B s ω)) ∂P = exp ((t - s : ℝ) * θ ^ 2 / 2) := by
    have := mgf_gaussianReal (increment_hasLaw hB hst) θ
    rw [mgf] at this
    rw [this]; congr 1; push_cast [hst]; ring
  have hinc := condExp_increment hB hm hst (f := fun x => exp (θ * x)) (by fun_prop)
  -- `M_t = exp(θ W_s − θ² t/2) · exp(θ (W_t − W_s))`
  have hsplit : (fun ω => exp (θ * B t ω - θ ^ 2 * t / 2)) =
      (fun ω => exp (θ * B s ω - θ ^ 2 * t / 2)) * (fun ω => exp (θ * (B t ω - B s ω))) := by
    funext ω; simp only [Pi.mul_apply]; rw [← exp_add]; congr 1; ring
  have hfm : StronglyMeasurable[F] (fun ω => exp (θ * B s ω - θ ^ 2 * t / 2)) :=
    continuous_exp.comp_stronglyMeasurable (((hadapt s).const_mul θ).sub stronglyMeasurable_const)
  have hprod : Integrable ((fun ω => exp (θ * B s ω - θ ^ 2 * t / 2)) *
      (fun ω => exp (θ * (B t ω - B s ω)))) P := by
    rw [← hsplit]
    have := (hexpint t θ).const_mul (exp (-(θ ^ 2 * t / 2)))
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only; rw [← exp_add]; congr 1; ring
  rw [hsplit]
  refine (condExp_mul_of_stronglyMeasurable_left hfm hprod hincint).trans ?_
  filter_upwards [hinc] with ω hω
  simp only [Pi.mul_apply] at hω ⊢
  rw [hω, hmgf, ← exp_add]
  congr 1
  ring

/-! ## Geometric Brownian motion as an explicit functional of `W` (§1.9) -/

/-- `X_t = x₀ exp((μ − σ²/2) t + σ W_t)`. -/
def gbm (x₀ μ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ * exp ((μ - σ ^ 2 / 2) * t + σ * B t ω)

omit [IsProbabilityMeasure P] in
/-- `E[e^{c W_t}] = e^{c² t/2}`. -/
@[powerlib_foundation] theorem integral_exp_brownian (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (c : ℝ) : ∫ ω, exp (c * B t ω) ∂P = exp (t * c ^ 2 / 2) := by
  have := mgf_gaussianReal (hB.hasLaw_eval t) c
  rw [mgf] at this
  rw [this]; congr 1; ring

omit [IsProbabilityMeasure P] in
/-- **GBM mean** `E X_t = x₀ e^{μ t}`. -/
@[powerlib_foundation] theorem gbm_mean (hB : IsPreBrownianReal B P) (x₀ μ σ : ℝ) (t : ℝ≥0) :
    ∫ ω, gbm x₀ μ σ B t ω ∂P = x₀ * exp (μ * t) := by
  have e : (fun ω => gbm x₀ μ σ B t ω) =
      fun ω => x₀ * exp ((μ - σ ^ 2 / 2) * t) * exp (σ * B t ω) := by
    funext ω; simp only [gbm]; rw [mul_assoc, ← exp_add]
  rw [e, integral_const_mul, integral_exp_brownian hB, mul_assoc, ← exp_add]
  congr 2; ring

omit [IsProbabilityMeasure P] in
/-- **GBM second moment** `E X_t² = x₀² e^{(2μ + σ²) t}`. -/
@[powerlib_foundation] theorem gbm_second_moment (hB : IsPreBrownianReal B P) (x₀ μ σ : ℝ)
    (t : ℝ≥0) : ∫ ω, gbm x₀ μ σ B t ω ^ 2 ∂P = x₀ ^ 2 * exp ((2 * μ + σ ^ 2) * t) := by
  have e : (fun ω => gbm x₀ μ σ B t ω ^ 2) =
      fun ω => x₀ ^ 2 * exp (2 * (μ - σ ^ 2 / 2) * t) * exp ((2 * σ) * B t ω) := by
    funext ω; simp only [gbm]; rw [mul_pow, ← exp_nat_mul, mul_assoc, ← exp_add]
    congr 2; push_cast; ring
  rw [e, integral_const_mul, integral_exp_brownian hB, mul_assoc, ← exp_add]
  congr 2; ring

omit [IsProbabilityMeasure P] in
/-- **GBM variance** `Var X_t = x₀² e^{2μt} (e^{σ² t} − 1)`. -/
@[powerlib_foundation] theorem gbm_variance (hB : IsPreBrownianReal B P) (x₀ μ σ : ℝ) (t : ℝ≥0) :
    ∫ ω, gbm x₀ μ σ B t ω ^ 2 ∂P - (∫ ω, gbm x₀ μ σ B t ω ∂P) ^ 2 =
      x₀ ^ 2 * exp (2 * μ * t) * (exp (σ ^ 2 * t) - 1) := by
  rw [gbm_second_moment hB, gbm_mean hB, mul_pow, ← exp_nat_mul, mul_sub, mul_one, mul_assoc,
    ← exp_add]
  push_cast
  ring_nf

omit [IsProbabilityMeasure P] in
/-- Second-moment Lyapunov exponent of GBM: `(1/t) log E X_t² = (2/t) log|x₀| + 2μ + σ²`, so
`Λ(2) = 2μ + σ²`. -/
@[powerlib_foundation] theorem gbm_log_second_moment (hB : IsPreBrownianReal B P) {x₀ : ℝ}
    (hx : x₀ ≠ 0) (μ σ : ℝ) {t : ℝ≥0} (ht : t ≠ 0) :
    log (∫ ω, gbm x₀ μ σ B t ω ^ 2 ∂P) / t = 2 * log |x₀| / t + (2 * μ + σ ^ 2) := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  rw [gbm_second_moment hB, log_mul (by positivity) (exp_pos _).ne', log_exp,
    show x₀ ^ 2 = |x₀| ^ 2 by rw [sq_abs], log_pow]
  field_simp
  push_cast
  ring

end powerlib.Stochastic.BM
