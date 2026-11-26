import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.BrownianMotion.Basic
import theorem.Stochastic.Brownian
import Mathlib.MeasureTheory.Integral.Prod

/-! # Pathwise Wiener integrals of deterministic integrands

The Wiener integral `∫₀ᵗ g dw` of a deterministic `C¹` integrand against a continuous path,
defined path by path through integration by parts; its linearity, its dependence on the
increments of the path only, and its consistency with the classical integral; and its first and
second moments when the path is a sample path of a process with Brownian second moments: the
expectation commutes with the integral, and the Wiener isometry
`E[∫₀ᵗ f dW_k · ∫₀ˢ g dW_l] = Q_kl ∫₀^{min(t,s)} f(r) g(r) dr` holds.

Scope.
* Paths `w : ℝ → ℝ` (one noise channel; several channels are summed in
  `theorem/Stochastic/LinearSDE.lean`); integrands `g : ℝ → F` with values in a real Banach space
  `F`, `C¹` (`ContDiff ℝ 1`). The integral is the pathwise expression
  `w(t) g(t) − w(0) g(0) − ∫₀ᵗ w(s) g'(s) ds` (`wienerIntegral`); it needs no continuity of `w`
  to be defined, and depends only on the increments of `w` and on its values on `[0, t]`. For a
  deterministic integrand this pathwise expression is the stochastic integral; no Itô calculus
  is used. Its agreement with limits of Riemann–Stieltjes sums is not proved (not needed here).
* Moments: a process `W : ℝ → Ω → ℝ` on a probability space with every path continuous and every
  marginal measurable and square integrable; its second moments enter as hypotheses
  (`E[W(u)²]` bounded on `(0, t]`; `E[W_k(u) W_l(v)] = Q_kl min(u, v)` for `u, v ≥ 0`;
  `E W(u) = 0`). Mathlib's pre-Brownian motion (`IsPreBrownianReal`, time `ℝ≥0`, read on `ℝ`
  through `u ↦ B(max u 0)`) with continuous paths, measurable marginals and pairwise independent
  components satisfies them with `Q = 1` (`integral_mul_brownian`). Only first and second
  moments are computed; the Gaussian law of the integral is not stated.
* Generic mathematics; no model.

Source: the pathwise (integration-by-parts) Wiener integral of a deterministic integrand, as
needed for the additive-noise SDEs of IEEE PES TR-110 "Forced Oscillations in Power Systems"
(2023) §3.6.1, eq. (3-33) (`x_ou = σ ∫₀ᵗ e^{−γ(t−s)} dB_s`, "evaluating the Itô integral"), and
the ambient input of §2.1, eqs. (2-12), (2-14).

Results.
* `wienerIntegral` — the pathwise integral; `wienerIntegral_zero_time`; linearity in the path
  (`wienerIntegral_add_path`, `wienerIntegral_smul_path`) and in the integrand
  (`wienerIntegral_add_integrand`, `wienerIntegral_smul_integrand`); `wienerIntegral_const`
  (`∫₀ᵗ v dw = (w(t) − w(0)) v`); `wienerIntegral_add_const` (only the increments of the path
  matter); `wienerIntegral_eq_incr` (`∫₀ᵗ g dw = ŵ(t) g(t) − ∫₀ᵗ ŵ g'`, `ŵ = w − w(0)`);
  `wienerIntegral_congr` (only the path on `[0, t]` matters); `wienerIntegral_map` (continuous
  linear maps commute with the integral); `continuous_wienerIntegral` (continuity in time).
* `wienerIntegral_eq_integral` — **consistency**: for a `C¹` path, `∫₀ᵗ g dw = ∫₀ᵗ w'(s) g(s) ds`.
* `wienerIntegral_stopped` — for `C¹` `p` and `c ≥ 0`,
  `∫₀ᵗ g d(p(min(·, c))) = ∫₀^{min(t, c)} p'(s) g(s) ds` (the deterministic kernel computation
  behind the isometry).
* `measurable_wienerIntegral` — measurability in the sample; `memLp_wienerIntegral` — the
  integral of a process with bounded second moments is square integrable; `integral_mul_wienerIntegral` — **the expectation commutes with the integral**,
  `E[Y ∫₀ᵗ g dW] = ∫₀ᵗ g dφ` with the deterministic path `φ(u) = E[Y W(u)]` (Fubini);
  `integral_wienerIntegral` — mean zero for centred noise; `sqMoment_le` — the second moments of
  a Brownian-type covariance are bounded on `(0, t]`.
* `integral_wienerIntegral_mul` — **Wiener isometry**
  `E[∫₀ᵗ f dW_k ∫₀ˢ g dW_l] = Q_kl ∫₀^{min(t, s)} f g`; `covariance_wienerIntegral` — the same
  for the covariance of centred noise.
* `integral_mul_brownian` — `E[B_k(u) B_l(v)] = δ_kl min(u, v)` for pairwise independent
  pre-Brownian motions; `covariance_wienerIntegral_brownian` — the isometry for Brownian motion,
  `Cov(∫₀ᵗ f dB_k, ∫₀ˢ g dB_l) = δ_kl ∫₀^{min(t, s)} f g`.
-/

noncomputable section
namespace powerlib.Stochastic.Wiener

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Pathwise Wiener integral** of a `C¹` deterministic integrand `g` against a path `w`,
defined by integration by parts: `∫₀ᵗ g dw = w(t) g(t) − w(0) g(0) − ∫₀ᵗ w(s) g'(s) ds`. -/
def wienerIntegral (g : ℝ → F) (w : ℝ → ℝ) (t : ℝ) : F :=
  w t • g t - w 0 • g 0 - ∫ s in (0 : ℝ)..t, w s • deriv g s

@[tmio T, powerlib_foundation] theorem wienerIntegral_zero_time (g : ℝ → F) (w : ℝ → ℝ) :
    wienerIntegral g w 0 = 0 := by
  simp [wienerIntegral]

variable [CompleteSpace F]

omit [CompleteSpace F] in
@[tmio T, powerlib_foundation] private theorem intervalIntegrable_smul_deriv {g : ℝ → F}
    (hg : ContDiff ℝ 1 g) {w : ℝ → ℝ} (hw : Continuous w) (a b : ℝ) :
    IntervalIntegrable (fun s => w s • deriv g s) MeasureTheory.volume a b :=
  (hw.smul (hg.continuous_deriv le_rfl)).intervalIntegrable a b

omit [CompleteSpace F] in
/-- Linearity in the path. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_add_path {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {w₁ w₂ : ℝ → ℝ} (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) (t : ℝ) :
    wienerIntegral g (w₁ + w₂) t = wienerIntegral g w₁ t + wienerIntegral g w₂ t := by
  simp only [wienerIntegral, Pi.add_apply, add_smul]
  rw [intervalIntegral.integral_add (intervalIntegrable_smul_deriv hg hw₁ 0 t)
    (intervalIntegrable_smul_deriv hg hw₂ 0 t)]
  abel

omit [CompleteSpace F] in
@[tmio T, powerlib_foundation] theorem wienerIntegral_smul_path (g : ℝ → F) (c : ℝ)
    (w : ℝ → ℝ) (t : ℝ) :
    wienerIntegral g (c • w) t = c • wienerIntegral g w t := by
  simp only [wienerIntegral, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sub]
  rw [← intervalIntegral.integral_smul]

omit [CompleteSpace F] in
/-- Linearity in the integrand. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_add_integrand {g₁ g₂ : ℝ → F}
    (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    wienerIntegral (g₁ + g₂) w t = wienerIntegral g₁ w t + wienerIntegral g₂ w t := by
  have hd : deriv (g₁ + g₂) = deriv g₁ + deriv g₂ := by
    funext s
    exact deriv_add ((hg₁.differentiable one_ne_zero) s) ((hg₂.differentiable one_ne_zero) s)
  simp only [wienerIntegral, hd, Pi.add_apply, smul_add]
  rw [intervalIntegral.integral_add (intervalIntegrable_smul_deriv hg₁ hw 0 t)
    (intervalIntegrable_smul_deriv hg₂ hw 0 t)]
  abel

omit [CompleteSpace F] in
@[tmio T, powerlib_foundation] theorem wienerIntegral_smul_integrand {g : ℝ → F}
    (hg : ContDiff ℝ 1 g) (c : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    wienerIntegral (c • g) w t = c • wienerIntegral g w t := by
  have hd : deriv (c • g) = c • deriv g := by
    funext s
    exact deriv_const_smul c ((hg.differentiable one_ne_zero) s)
  simp only [wienerIntegral, hd, Pi.smul_apply, smul_sub]
  rw [← intervalIntegral.integral_smul]
  simp only [smul_comm c]

omit [CompleteSpace F] in
/-- A constant integrand: `∫₀ᵗ v dw = (w(t) − w(0)) v`. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_const (v : F) (w : ℝ → ℝ) (t : ℝ) :
    wienerIntegral (fun _ => v) w t = (w t - w 0) • v := by
  simp [wienerIntegral, sub_smul]

/-- The integral depends only on the increments of the path: adding a constant changes nothing. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_add_const {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {w : ℝ → ℝ} (hw : Continuous w) (c : ℝ) (t : ℝ) :
    wienerIntegral g (fun s => w s + c) t = wienerIntegral g w t := by
  have hI : ∫ s in (0 : ℝ)..t, deriv g s = g t - g 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => (hg.differentiable one_ne_zero) x)
      ((hg.continuous_deriv le_rfl).intervalIntegrable 0 t)
  have hc : IntervalIntegrable (fun s => c • deriv g s) MeasureTheory.volume 0 t :=
    (continuous_const.smul (hg.continuous_deriv le_rfl)).intervalIntegrable 0 t
  simp only [wienerIntegral, add_smul]
  rw [intervalIntegral.integral_add (intervalIntegrable_smul_deriv hg hw 0 t) hc,
    intervalIntegral.integral_smul, hI, smul_sub]
  abel

/-- The integral in terms of the increments `ŵ = w − w(0)`:
`∫₀ᵗ g dw = ŵ(t) g(t) − ∫₀ᵗ ŵ(s) g'(s) ds`. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_eq_incr {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    wienerIntegral g w t = (w t - w 0) • g t - ∫ s in (0 : ℝ)..t, (w s - w 0) • deriv g s := by
  have h := wienerIntegral_add_const hg (w := fun s => w s - w 0) (hw.sub continuous_const) (w 0) t
  have e : (fun s => (w s - w 0) + w 0) = w := funext fun s => by ring
  rw [e] at h
  rw [h]
  simp [wienerIntegral]

/-- The integral is continuous in time for a continuous path. -/
@[tmio T, powerlib_foundation] theorem continuous_wienerIntegral {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {w : ℝ → ℝ} (hw : Continuous w) : Continuous (wienerIntegral g w) := by
  have hI : Continuous fun t => ∫ s in (0 : ℝ)..t, w s • deriv g s :=
    continuous_iff_continuousAt.2 fun t =>
      ((hw.smul (hg.continuous_deriv le_rfl)).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  exact ((hw.smul hg.continuous).sub continuous_const).sub hI

omit [CompleteSpace F] in
/-- The integral at time `t` depends only on the path on `[0, t]`. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_congr (g : ℝ → F) {w₁ w₂ : ℝ → ℝ} {t : ℝ}
    (h : ∀ s ∈ uIcc 0 t, w₁ s = w₂ s) :
    wienerIntegral g w₁ t = wienerIntegral g w₂ t := by
  unfold wienerIntegral
  rw [h t right_mem_uIcc, h 0 left_mem_uIcc,
    intervalIntegral.integral_congr (g := fun s => w₂ s • deriv g s) fun s hs => by
      simp only [h s hs]]

/-- **Consistency with the classical integral.** For a `C¹` path with derivative `w'`,
`∫₀ᵗ g dw = ∫₀ᵗ w'(s) g(s) ds`. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_eq_integral {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {w w' : ℝ → ℝ} (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (t : ℝ) :
    wienerIntegral g w t = ∫ s in (0 : ℝ)..t, w' s • g s := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s => (hw s).continuousAt
  have hd : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun s => w s • g s) (w' s • g s + w s • deriv g s) s := fun s _ =>
    ((hw s).smul ((hg.differentiable one_ne_zero) s).hasDerivAt).congr_deriv (add_comm _ _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((hw'.smul hg.continuous).add (hwc.smul (hg.continuous_deriv le_rfl))).intervalIntegrable 0 t)
  have h1 : IntervalIntegrable (fun s => w' s • g s) MeasureTheory.volume 0 t :=
    (hw'.smul hg.continuous).intervalIntegrable 0 t
  rw [intervalIntegral.integral_add h1 (intervalIntegrable_smul_deriv hg hwc 0 t)] at hFTC
  unfold wienerIntegral
  rw [← hFTC]
  abel

/-- A continuous linear map commutes with the integral. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_map {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (T : F →L[ℝ] G) {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    wienerIntegral (fun s => T (g s)) w t = T (wienerIntegral g w t) := by
  have hd : deriv (fun s => T (g s)) = fun s => T (deriv g s) := by
    funext s
    exact (T.hasFDerivAt.comp_hasDerivAt s ((hg.differentiable one_ne_zero) s).hasDerivAt).deriv
  simp only [wienerIntegral, hd, map_sub, map_smul]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm T (intervalIntegrable_smul_deriv hg hw 0 t)]
  simp only [map_smul]

/-- **Stopped paths.** For a `C¹` function `p` and `c ≥ 0`, the path `v ↦ p(min v c)` integrates
to `∫₀ᵗ g d(p(min · c)) = ∫₀^{min t c} p'(s) g(s) ds`. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_stopped {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {p p' : ℝ → ℝ} (hp : ∀ s, HasDerivAt p (p' s) s) (hp' : Continuous p') {c : ℝ} (hc : 0 ≤ c)
    (t : ℝ) :
    wienerIntegral g (fun v => p (min v c)) t = ∫ s in (0 : ℝ)..min t c, p' s • g s := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun s => (hp s).continuousAt
  rcases le_or_gt t c with htc | hct
  · rw [min_eq_left htc, ← wienerIntegral_eq_integral hg hp hp' t]
    refine wienerIntegral_congr g fun s hs => ?_
    have : s ≤ c := (hs.2).trans (max_le hc htc)
    rw [min_eq_left this]
  · rw [min_eq_right hct.le, ← wienerIntegral_eq_integral hg hp hp' c]
    have hq : Continuous fun v => p (min v c) := hpc.comp (continuous_id.min continuous_const)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_smul_deriv hg hq 0 c) (intervalIntegrable_smul_deriv hg hq c t)
    have h1 : ∫ s in (0 : ℝ)..c, p (min s c) • deriv g s = ∫ s in (0 : ℝ)..c, p s • deriv g s :=
      intervalIntegral.integral_congr fun s hs => by
        have : s ≤ c := hs.2.trans (max_le hc le_rfl)
        simp only [min_eq_left this]
    have h2 : ∫ s in c..t, p (min s c) • deriv g s = p c • (g t - g c) := by
      rw [intervalIntegral.integral_congr (g := fun s => p c • deriv g s) fun s hs => by
        have : c ≤ s := by
          rw [uIcc_of_le hct.le] at hs; exact hs.1
        simp only [min_eq_right this], intervalIntegral.integral_smul,
        intervalIntegral.integral_deriv_eq_sub (fun x _ => (hg.differentiable one_ne_zero) x)
          ((hg.continuous_deriv le_rfl).intervalIntegrable c t)]
    unfold wienerIntegral
    rw [← hsplit, h1, h2]
    simp only [min_eq_right hct.le, min_eq_left hc, smul_sub]
    abel

/-! ## Second moments of Wiener integrals of a second-order process -/

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(∫₀ᵗ φ)² ≤ t ∫₀ᵗ φ²` for continuous `φ` and `t ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem sq_intervalIntegral_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, φ u) ^ 2 ≤ t * ∫ u in (0 : ℝ)..t, φ u ^ 2 := by
  rcases ht.eq_or_lt with rfl | htpos
  · simp
  set I := ∫ u in (0 : ℝ)..t, φ u
  set m := I / t
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..t, (φ u - m) ^ 2 :=
    intervalIntegral.integral_nonneg ht fun u _ => sq_nonneg _
  have hexp : ∫ u in (0 : ℝ)..t, (φ u - m) ^ 2 =
      (∫ u in (0 : ℝ)..t, φ u ^ 2) - 2 * m * I + m ^ 2 * t := by
    have e : ∀ u, (φ u - m) ^ 2 = φ u ^ 2 - 2 * m * φ u + m ^ 2 := fun u => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul]
    · simp
      ring
    all_goals first
      | exact (hφ.pow 2).intervalIntegrable 0 t
      | exact (continuous_const.mul hφ).intervalIntegrable 0 t
      | exact ((hφ.pow 2).sub (continuous_const.mul hφ)).intervalIntegrable 0 t
      | exact continuous_const.intervalIntegrable 0 t
  rw [hexp] at hnn
  have hm : m * t = I := div_mul_cancel₀ I htpos.ne'
  nlinarith [hm]

/-- Joint measurability of a process with continuous paths and measurable marginals. -/
@[tmio T, powerlib_foundation] private theorem measurable_process {W : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u)) :
    Measurable fun p : Ω × ℝ => W p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap

variable {W : ℝ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- The pathwise integral of a process with continuous paths and measurable marginals is a
measurable random variable. -/
@[tmio T, powerlib_foundation] theorem measurable_wienerIntegral
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u)) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (t : ℝ) :
    Measurable fun ω => wienerIntegral g (fun u => W u ω) t := by
  have hmeas := measurable_process hc hm
  have hF : StronglyMeasurable fun p : Ω × ℝ => W p.2 p.1 * deriv g p.2 :=
    (hmeas.mul ((hg.continuous_deriv le_rfl).measurable.comp measurable_snd)).stronglyMeasurable
  have h1 := hF.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) t))
  have h2 := hF.integral_prod_right' (ν := volume.restrict (Ioc t (0 : ℝ)))
  have hI : Measurable fun ω => ∫ u in (0 : ℝ)..t, W u ω * deriv g u :=
    h1.measurable.sub h2.measurable
  simp only [wienerIntegral, smul_eq_mul]
  exact (((hm t).mul_const _).sub ((hm 0).mul_const _)).sub hI

/-- Square integrability of the process on `Ω × (0, t]` under bounded second moments. -/
@[tmio T, powerlib_foundation] private theorem integrable_sq_prod
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P) {t C : ℝ} (hbd : ∀ u ∈ Ioc 0 t, ∫ ω, W u ω ^ 2 ∂P ≤ C) :
    Integrable (fun p : Ω × ℝ => W p.2 p.1 ^ 2) (P.prod (volume.restrict (Ioc 0 t))) := by
  have hmeas := measurable_process hc hm
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  rw [integrable_prod_iff' (hmeas.pow_const 2).aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun u => (hL2 u).integrable_sq, ?_⟩
  refine Integrable.of_bound ((hmeas.pow_const 2).norm.stronglyMeasurable.integral_prod_left'
    ).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have e : ∫ ω, ‖W u ω ^ 2‖ ∂P = ∫ ω, W u ω ^ 2 ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp [sq_abs])
  rw [e, Real.norm_of_nonneg (integral_nonneg fun ω => sq_nonneg _)]
  exact hbd u hu

/-- **Fubini for a time integral of the process**: `E[Y ∫₀ᵗ W(u) h(u) du] = ∫₀ᵗ E[Y W(u)] h(u) du`
for square-integrable `Y` and continuous `h`. -/
@[tmio T, powerlib_foundation] private theorem integral_mul_intervalIntegral
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P) {t C : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ u ∈ Ioc 0 t, ∫ ω, W u ω ^ 2 ∂P ≤ C) {h : ℝ → ℝ} (hh : Continuous h)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    ∫ ω, Y ω * (∫ u in (0 : ℝ)..t, W u ω * h u) ∂P =
      ∫ u in (0 : ℝ)..t, (∫ ω, Y ω * W u ω ∂P) * h u := by
  have hmeas := measurable_process hc hm
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hh.continuousOn
  set F : Ω × ℝ → ℝ := fun p => Y p.1 * (W p.2 p.1 * h p.2) with hF
  have hFm : AEStronglyMeasurable F (P.prod (volume.restrict (Ioc 0 t))) :=
    hY.aestronglyMeasurable.comp_fst.mul
      (hmeas.mul (hh.measurable.comp measurable_snd)).aestronglyMeasurable
  have hFi : Integrable F (P.prod (volume.restrict (Ioc 0 t))) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall fun u => ?_, ?_⟩
    · have := (hY.integrable_mul (hL2 u)).mul_const (h u)
      simpa [hF, mul_assoc] using this
    · refine Integrable.of_bound hFm.norm.prod_swap.integral_prod_right'
        (Ch * ((∫ ω, Y ω ^ 2 ∂P) + C) / 2) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hYW : Integrable (fun ω => Y ω * W u ω) P := hY.integrable_mul (hL2 u)
      have hYW2 : Integrable (fun ω => (Y ω ^ 2 + W u ω ^ 2) / 2) P :=
        (hY.integrable_sq.add (hL2 u).integrable_sq).div_const 2
      have hb : ∫ ω, ‖F (ω, u)‖ ∂P ≤ Ch * ((∫ ω, Y ω ^ 2 ∂P) + C) / 2 := by
        have e : ∀ ω, ‖F (ω, u)‖ = ‖h u‖ * |Y ω * W u ω| := fun ω => by
          simp only [hF, norm_mul, Real.norm_eq_abs, abs_mul]; ring
        simp_rw [e]
        rw [integral_const_mul]
        have h1 : ∫ ω, |Y ω * W u ω| ∂P ≤ ∫ ω, (Y ω ^ 2 + W u ω ^ 2) / 2 ∂P :=
          integral_mono hYW.abs hYW2 fun ω => by
            have := two_mul_le_add_sq (|Y ω|) (|W u ω|)
            rw [abs_mul, sq_abs, sq_abs] at *
            linarith [abs_nonneg (Y ω), abs_nonneg (W u ω)]
        have h2 : ∫ ω, (Y ω ^ 2 + W u ω ^ 2) / 2 ∂P = ((∫ ω, Y ω ^ 2 ∂P) + ∫ ω, W u ω ^ 2 ∂P) / 2 := by
          rw [integral_div, integral_add hY.integrable_sq (hL2 u).integrable_sq]
        have hhu : ‖h u‖ ≤ Ch := hCh u (Ioc_subset_Icc_self hu)
        have hW := hbd u hu
        have hnn : 0 ≤ ∫ ω, |Y ω * W u ω| ∂P := integral_nonneg fun ω => abs_nonneg _
        have hCh0 : 0 ≤ Ch := (norm_nonneg _).trans hhu
        calc ‖h u‖ * ∫ ω, |Y ω * W u ω| ∂P ≤ Ch * (((∫ ω, Y ω ^ 2 ∂P) + ∫ ω, W u ω ^ 2 ∂P) / 2) :=
              mul_le_mul hhu (h1.trans h2.le) hnn hCh0
          _ ≤ Ch * ((∫ ω, Y ω ^ 2 ∂P) + C) / 2 := by
              rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_left (by linarith) hCh0
      rwa [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
  calc ∫ ω, Y ω * (∫ u in (0 : ℝ)..t, W u ω * h u) ∂P
      = ∫ ω, ∫ u, F (ω, u) ∂(volume.restrict (Ioc 0 t)) ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [hF]
        rw [intervalIntegral.integral_of_le ht, ← integral_const_mul]
    _ = ∫ u, ∫ ω, F (ω, u) ∂P ∂(volume.restrict (Ioc 0 t)) :=
        integral_integral_swap (f := fun ω u => F (ω, u)) hFi
    _ = ∫ u in (0 : ℝ)..t, (∫ ω, Y ω * W u ω ∂P) * h u := by
        rw [intervalIntegral.integral_of_le ht]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [hF]
        rw [← integral_mul_const]
        simp_rw [mul_assoc]

/-- The time integral `∫₀ᵗ W(u) h(u) du` of the process is square integrable. -/
@[tmio T, powerlib_foundation] private theorem memLp_intervalIntegral
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P) {t C : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ u ∈ Ioc 0 t, ∫ ω, W u ω ^ 2 ∂P ≤ C) {h : ℝ → ℝ} (hh : Continuous h) :
    MemLp (fun ω => ∫ u in (0 : ℝ)..t, W u ω * h u) 2 P := by
  have hmeas := measurable_process hc hm
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hh.continuousOn
  have hZm : AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..t, W u ω * h u) P := by
    have : StronglyMeasurable
        (fun ω => ∫ u, W u ω * h u ∂(volume.restrict (Ioc (0 : ℝ) t))) :=
      (hmeas.mul (hh.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'
    refine this.aestronglyMeasurable.congr (Eventually.of_forall fun ω => ?_)
    simp only [intervalIntegral.integral_of_le ht]
  have hS : Integrable (fun ω => ∫ u, W u ω ^ 2 ∂(volume.restrict (Ioc (0 : ℝ) t))) P :=
    (integrable_sq_prod hc hm hL2 hbd).integral_prod_left
  rw [memLp_two_iff_integrable_sq hZm]
  refine Integrable.mono' (hS.const_mul (t * Ch ^ 2)) (hZm.pow 2)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hφ : Continuous fun u => W u ω * h u := (hc ω).mul hh
  calc (∫ u in (0 : ℝ)..t, W u ω * h u) ^ 2
      ≤ t * ∫ u in (0 : ℝ)..t, (W u ω * h u) ^ 2 := sq_intervalIntegral_le hφ ht
    _ ≤ t * ∫ u in (0 : ℝ)..t, Ch ^ 2 * W u ω ^ 2 := by
        refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on ht
          ((hφ.pow 2).intervalIntegrable 0 t)
          ((continuous_const.mul ((hc ω).pow 2)).intervalIntegrable 0 t) fun u hu => ?_) ht
        have hu' := hCh u hu
        rw [Real.norm_eq_abs] at hu'
        have hh2 : h u ^ 2 ≤ Ch ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu' 2
        rw [mul_pow, mul_comm (Ch ^ 2)]
        exact mul_le_mul_of_nonneg_left hh2 (sq_nonneg _)
    _ = t * Ch ^ 2 * ∫ u, W u ω ^ 2 ∂(volume.restrict (Ioc (0 : ℝ) t)) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le ht]; ring

/-- The pathwise Wiener integral of a process with continuous paths and bounded second moments
is square integrable. -/
@[tmio T, powerlib_foundation] theorem memLp_wienerIntegral
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P) {t C : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ u ∈ Ioc 0 t, ∫ ω, W u ω ^ 2 ∂P ≤ C) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    MemLp (fun ω => wienerIntegral g (fun u => W u ω) t) 2 P := by
  have hZ := memLp_intervalIntegral hc hm hL2 ht hbd (hg.continuous_deriv le_rfl)
  simp only [wienerIntegral, smul_eq_mul]
  exact (((hL2 t).mul_const (g t)).sub ((hL2 0).mul_const (g 0))).sub hZ

/-- **The expectation commutes with the pathwise Wiener integral**: for square-integrable `Y`,
`E[Y ∫₀ᵗ g dW] = ∫₀ᵗ g dφ` with the deterministic path `φ(u) = E[Y W(u)]`. -/
@[tmio T, powerlib_foundation] theorem integral_mul_wienerIntegral
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P) {t C : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ u ∈ Ioc 0 t, ∫ ω, W u ω ^ 2 ∂P ≤ C) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    ∫ ω, Y ω * wienerIntegral g (fun u => W u ω) t ∂P =
      wienerIntegral g (fun u => ∫ ω, Y ω * W u ω ∂P) t := by
  have hg' := hg.continuous_deriv le_rfl
  have hZ := memLp_intervalIntegral hc hm hL2 ht hbd hg'
  have hYt : Integrable (fun ω => Y ω * W t ω * g t) P := (hY.integrable_mul (hL2 t)).mul_const _
  have hY0 : Integrable (fun ω => Y ω * W 0 ω * g 0) P := (hY.integrable_mul (hL2 0)).mul_const _
  have hYZ : Integrable (fun ω => Y ω * ∫ u in (0 : ℝ)..t, W u ω * deriv g u) P :=
    hY.integrable_mul hZ
  have e : ∀ ω, Y ω * wienerIntegral g (fun u => W u ω) t =
      Y ω * W t ω * g t - Y ω * W 0 ω * g 0 - Y ω * ∫ u in (0 : ℝ)..t, W u ω * deriv g u := by
    intro ω; simp only [wienerIntegral, smul_eq_mul]; ring
  simp_rw [e]
  rw [integral_sub (f := fun ω => Y ω * W t ω * g t - Y ω * W 0 ω * g 0) (hYt.sub hY0) hYZ,
    integral_sub hYt hY0, integral_mul_const, integral_mul_const,
    integral_mul_intervalIntegral hc hm hL2 ht hbd hg' hY]
  simp only [wienerIntegral, smul_eq_mul]

/-- **Mean of the pathwise Wiener integral** of a centred process: `E ∫₀ᵗ g dW = 0`. -/
@[tmio T, powerlib_foundation] theorem integral_wienerIntegral
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P) {t C : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ u ∈ Ioc 0 t, ∫ ω, W u ω ^ 2 ∂P ≤ C) (hmean : ∀ u, 0 ≤ u → ∫ ω, W u ω ∂P = 0)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    ∫ ω, wienerIntegral g (fun u => W u ω) t ∂P = 0 := by
  have h := integral_mul_wienerIntegral hc hm hL2 ht hbd hg (memLp_const (1 : ℝ))
  simp only [one_mul] at h
  rw [h, wienerIntegral_congr g (w₂ := fun _ => (0 : ℝ)) fun u hu => by
    rw [uIcc_of_le ht] at hu; simp [hmean u hu.1]]
  simp [wienerIntegral]

omit [IsProbabilityMeasure P] in
/-- Bounded second moments on `(0, t]` from a covariance of Brownian type:
`E[W_k(u)²] = Q_kk u ≤ |Q_kk| t`. -/
@[tmio T, powerlib_foundation] theorem sqMoment_le {ι : Type*} {W : ι → ℝ → Ω → ℝ}
    {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v) (k : ι)
    (t : ℝ) : ∀ u ∈ Ioc 0 t, ∫ ω, W k u ω ^ 2 ∂P ≤ |Q k k| * t := by
  intro u hu
  simp_rw [sq]
  rw [hQ k k u u hu.1.le hu.1.le, min_self]
  exact mul_le_mul (le_abs_self _) hu.2 hu.1.le (abs_nonneg _)

/-- **Wiener isometry** for pathwise integrals. Let `W_k` (`k ∈ ι`) be processes with continuous
paths, measurable and square-integrable marginals and second moments
`E[W_k(u) W_l(v)] = Q_kl min(u, v)` for `u, v ≥ 0` (independent standard Brownian motions:
`Q = 1`). For `C¹` integrands `f, g` and `t, s ≥ 0`,
`E[∫₀ᵗ f dW_k · ∫₀ˢ g dW_l] = Q_kl ∫₀^{min(t, s)} f(r) g(r) dr`. -/
@[tmio T, powerlib_foundation] theorem integral_wienerIntegral_mul {ι : Type*}
    {W : ι → ℝ → Ω → ℝ} (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (k l : ι) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ∫ ω, wienerIntegral f (fun u => W k u ω) t * wienerIntegral g (fun u => W l u ω) s ∂P =
      Q k l * ∫ r in (0 : ℝ)..min t s, f r * g r := by
  set Y : Ω → ℝ := fun ω => wienerIntegral g (fun u => W l u ω) s with hYdef
  have hY : MemLp Y 2 P :=
    memLp_wienerIntegral (hc l) (hm l) (hL2 l) hs (sqMoment_le hQ l s) g hg
  -- the inner moment `E[W_k(u) ∫₀ˢ g dW_l] = Q_kl ∫₀^{min(u,s)} g`
  set G : ℝ → ℝ := fun x => ∫ r in (0 : ℝ)..x, g r with hG
  have hGd : ∀ x, HasDerivAt G (g x) x := fun x =>
    (hg.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hinner : ∀ u, 0 ≤ u → ∫ ω, Y ω * W k u ω ∂P = Q k l * G (min u s) := by
    intro u hu
    have h1 := integral_mul_wienerIntegral (hc l) (hm l) (hL2 l) hs (sqMoment_le hQ l s) hg
      (hL2 k u)
    rw [show (fun ω => Y ω * W k u ω) = fun ω => W k u ω * Y ω from funext fun ω => mul_comm _ _]
    have h3 := wienerIntegral_stopped hg (p := fun x => x) (p' := fun _ => 1)
      (fun x => hasDerivAt_id' x) continuous_const hu s
    simp only [one_smul] at h3
    rw [h1, wienerIntegral_congr g (w₂ := Q k l • fun v => min v u) fun v hv => by
      rw [uIcc_of_le hs] at hv
      simp [hQ k l u v hu hv.1, min_comm], wienerIntegral_smul_path, h3]
    simp [hG, min_comm, smul_eq_mul]
  have h2 := integral_mul_wienerIntegral (hc k) (hm k) (hL2 k) ht (sqMoment_le hQ k t) hf hY
  calc ∫ ω, wienerIntegral f (fun u => W k u ω) t * Y ω ∂P
      = ∫ ω, Y ω * wienerIntegral f (fun u => W k u ω) t ∂P :=
        integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    _ = wienerIntegral f (fun u => ∫ ω, Y ω * W k u ω ∂P) t := h2
    _ = wienerIntegral f (Q k l • fun u => G (min u s)) t :=
        wienerIntegral_congr f fun u hu => by
          rw [uIcc_of_le ht] at hu
          simp [hinner u hu.1, smul_eq_mul]
    _ = Q k l * ∫ r in (0 : ℝ)..min t s, f r * g r := by
        rw [wienerIntegral_smul_path, wienerIntegral_stopped hf hGd hg.continuous hs, smul_eq_mul]
        simp_rw [smul_eq_mul, mul_comm (g _)]

/-- **Covariance of pathwise Wiener integrals** of centred processes:
`Cov(∫₀ᵗ f dW_k, ∫₀ˢ g dW_l) = Q_kl ∫₀^{min(t, s)} f g`. -/
@[tmio T, powerlib_foundation] theorem covariance_wienerIntegral {ι : Type*}
    {W : ι → ℝ → Ω → ℝ} (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (k l : ι) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cov[fun ω => wienerIntegral f (fun u => W k u ω) t,
      fun ω => wienerIntegral g (fun u => W l u ω) s; P] =
      Q k l * ∫ r in (0 : ℝ)..min t s, f r * g r := by
  rw [covariance_eq_sub (memLp_wienerIntegral (hc k) (hm k) (hL2 k) ht (sqMoment_le hQ k t) f hf)
    (memLp_wienerIntegral (hc l) (hm l) (hL2 l) hs (sqMoment_le hQ l s) g hg),
    integral_wienerIntegral (hc k) (hm k) (hL2 k) ht (sqMoment_le hQ k t) (hmean k) hf]
  simp only [zero_mul, sub_zero]
  exact integral_wienerIntegral_mul hc hm hL2 hQ hf hg k l ht hs

/-! ### Brownian motion -/

open scoped NNReal

/-- **Second moments of independent Brownian motions.** Mathlib's pre-Brownian motions
`B_k : ℝ≥0 → Ω → ℝ`, pairwise independent across components, read on `ℝ` through
`u ↦ B_k(max u 0)`, satisfy `E[B_k(u) B_l(v)] = δ_kl min(u, v)` for `u, v ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem integral_mul_brownian {ι : Type*} [DecidableEq ι]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ k, IsPreBrownianReal (B k) P)
    (hind : ∀ k l, k ≠ l → ∀ s t, IndepFun (B k s) (B l t) P) (k l : ι) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ ω, B k u.toNNReal ω * B l v.toNNReal ω ∂P = (1 : Matrix ι ι ℝ) k l * min u v := by
  by_cases hkl : k = l
  · subst hkl
    have h := covariance_eq_sub (BM.memLp_two (hB k) u.toNNReal) (BM.memLp_two (hB k) v.toNNReal)
    rw [(hB k).covariance_eval, (hB k).integral_eval, zero_mul, sub_zero] at h
    rw [Matrix.one_apply_eq, one_mul]
    have e : (∫ ω, B k u.toNNReal ω * B k v.toNNReal ω ∂P) = P[B k u.toNNReal * B k v.toNNReal] :=
      rfl
    rw [e, ← h, NNReal.coe_min, Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv]
  · rw [Matrix.one_apply_ne hkl, zero_mul,
      (hind k l hkl _ _).integral_fun_mul_eq_mul_integral
        ((hB k).aemeasurable _).aestronglyMeasurable ((hB l).aemeasurable _).aestronglyMeasurable,
      (hB k).integral_eval, zero_mul]

/-- **Wiener isometry for Brownian motion.** For pairwise independent pre-Brownian motions with
continuous paths and measurable marginals, `C¹` integrands `f, g` and `t, s ≥ 0`,
`Cov(∫₀ᵗ f dB_k, ∫₀ˢ g dB_l) = δ_kl ∫₀^{min(t, s)} f(r) g(r) dr`. -/
@[tmio T, powerlib_foundation] theorem covariance_wienerIntegral_brownian {ι : Type*}
    [DecidableEq ι] {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ k, IsPreBrownianReal (B k) P)
    (hind : ∀ k l, k ≠ l → ∀ s t, IndepFun (B k s) (B l t) P)
    (hc : ∀ k ω, Continuous fun t => B k t ω) (hm : ∀ k t, Measurable (B k t))
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (k l : ι) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cov[fun ω => wienerIntegral f (fun u => B k u.toNNReal ω) t,
      fun ω => wienerIntegral g (fun u => B l u.toNNReal ω) s; P] =
      (1 : Matrix ι ι ℝ) k l * ∫ r in (0 : ℝ)..min t s, f r * g r :=
  covariance_wienerIntegral (W := fun k u ω => B k u.toNNReal ω)
    (fun k ω => (hc k ω).comp continuous_real_toNNReal) (fun k _ => hm k _)
    (fun k _ => BM.memLp_two (hB k) _) (fun k l _ _ hu hv => integral_mul_brownian hB hind k l hu hv)
    (fun k _ _ => (hB k).integral_eval _) hf hg k l ht hs

end Moments

end powerlib.Stochastic.Wiener
