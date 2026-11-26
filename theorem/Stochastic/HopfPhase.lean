import theorem.Stochastic.NoisyHopf
import theorem.Stochastic.OUSDE

/-! # Amplitude and phase noise of the noisy Hopf cycle (TR-110 (3-28))

The linear response of the noisy normal form (3-26) along its limit cycle, in the co-rotating
frame: the tangential component of the variational solution is the rotated noise, and its radial
component is the Ornstein–Uhlenbeck response of rate `2γ` to the rotated noise; under
independent Brownian-type noise the rotated noise is again standard, so the amplitude
fluctuation is an OU process of rate `2γ`, the phase fluctuation a Brownian motion, and the two
are uncorrelated — the exact first-order content of (3-28).

Model boundary.
* The normal form of (3-26), `Hopf.tr110Params γ ω_h` (`ż = (γ + iω_h)z − |z|²z`), `γ > 0`, on
  `State 2`; its cycle `x₀(t) = √γ (cos ω_h t, sin ω_h t)` (`Hopf.cycle`, radius and frequency
  from `Hopf.tr110_limitCycle`); the variational equation along it,
  `ζ(t) = ∫₀ᵗ f'(x₀(s)) ζ(s) ds + (w(t) − w(0))`, driven by a continuous noise path `w` (the
  first-order term of `NoisyHopf.noisyHopf_expansion` for initial state on the cycle), on
  `[0, T]`.
* Co-rotating coordinates: radial `⟪(cos ω_h t, sin ω_h t), ζ⟫` (`radProj`), tangential
  `⟪(−sin ω_h t, cos ω_h t), ζ⟫` (`tanProj`); rotated noise `∫₀ᵗ rot(−ω_h s) dw(s)` (pathwise
  Wiener integrals, `radNoise`, `tanNoise`, as a process `rotNoise`).
* Moments: two noise components with continuous paths, measurable square-integrable centred
  marginals and `E[W_k(u) W_l(v)] = δ_kl min(u, v)` (independent standard Brownian motions,
  `Wiener.integral_mul_brownian`). Only second moments are computed.
* A normal form, not an engineering model; public foundation.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.1, eqs. (3-26)–(3-28)
(`z ≈ (√γ + p(t)) e^{iφ(t)}`, `ṗ = −2γp + σ_p ξ_p` an OU process independent of `φ`,
`φ̇ = ω_h + (σ_φ/√γ) ξ_φ` a Brownian motion with drift) and Table 3-1 (limit-cycle row).

Results.
* `radProj`, `tanProj`, `radNoise`, `tanNoise`; `radNoise_eq`, `tanNoise_eq` — closed forms in the
  increments of the noise.
* `tan_jac_cycle`, `rad_jac_cycle` — the rows of `f'(x₀(t))` in the co-rotating frame (the
  component form of `NoisyHopf.tr110_corotating_jac`).
* `variational_frame` — **pathwise decomposition**: `tanProj ζ = tanNoise` and
  `radProj ζ = lagSDESol (2γ) 0 1 0 radNoise` on `[0, T]` (`OUSDE.lagSDESol`: the OU response of
  rate `2γ`).
* `path`, `rotNoise`; `integral_pair_mul` — second moments of two-channel Wiener integrals;
  `rotNoise_standard` — **the rotated noise is again standard** (rotation invariance at the level
  of second moments).
* `covariance_frame` — `Cov(p(t), p(s)) = e^{−2γ(t−s)} (1 − e^{−4γs})/(4γ)` (`OU.ouVar (2γ) 1 s`),
  `Cov(q(t), q(s)) = min(t, s)`, `Cov(p(t), q(s)) = 0` for `0 ≤ s ≤ t ≤ T`.
* `tr110_amplitude_phase` — **(3-28) to first order, path by path**: for the noisy normal form
  started on its cycle, `⟪u, x_σ⟫ = √γ + σ p + O(σ²)` and `⟪u⊥, x_σ⟫ = σ q + O(σ²)` uniformly on
  `[0, T]` (from `SmallNoise.norm_sub_sub_smul_le` with `x₀ = cycle`).
-/

noncomputable section
namespace powerlib.Stochastic.HopfPhase

open Set Filter Topology Matrix MeasureTheory ProbabilityTheory
open powerlib.Dynamics (State)
open powerlib.PhasePlane powerlib.NormalForm.Hopf powerlib.Stochastic.Wiener
  powerlib.Stochastic.OUSDE powerlib.Stochastic.NoisyHopf

/-! ## Radial and tangential coordinates in the co-rotating frame -/

/-- Radial component `⟪(cos ωt, sin ωt), ζ(t)⟫` of a perturbation of the cycle. -/
def radProj (ω : ℝ) (ζ : ℝ → State 2) (t : ℝ) : ℝ :=
  Real.cos (ω * t) * ζ t 0 + Real.sin (ω * t) * ζ t 1

/-- Tangential component `⟪(−sin ωt, cos ωt), ζ(t)⟫` of a perturbation of the cycle. -/
def tanProj (ω : ℝ) (ζ : ℝ → State 2) (t : ℝ) : ℝ :=
  -Real.sin (ω * t) * ζ t 0 + Real.cos (ω * t) * ζ t 1

/-- Radial component of the noise in the co-rotating frame,
`∫₀ᵗ cos(ωs) dw₀(s) + ∫₀ᵗ sin(ωs) dw₁(s)` (pathwise Wiener integrals). -/
def radNoise (ω : ℝ) (w : ℝ → State 2) (t : ℝ) : ℝ :=
  wienerIntegral (fun s => Real.cos (ω * s)) (fun s => w s 0) t +
    wienerIntegral (fun s => Real.sin (ω * s)) (fun s => w s 1) t

/-- Tangential component of the noise in the co-rotating frame,
`−∫₀ᵗ sin(ωs) dw₀(s) + ∫₀ᵗ cos(ωs) dw₁(s)`. -/
def tanNoise (ω : ℝ) (w : ℝ → State 2) (t : ℝ) : ℝ :=
  wienerIntegral (fun s => -Real.sin (ω * s)) (fun s => w s 0) t +
    wienerIntegral (fun s => Real.cos (ω * s)) (fun s => w s 1) t

@[tmio T, powerlib_foundation] private theorem hasDerivAt_cos_mul (ω s : ℝ) :
    HasDerivAt (fun s => Real.cos (ω * s)) (-(ω * Real.sin (ω * s))) s := by
  simpa [mul_comm] using ((hasDerivAt_id' s).const_mul ω).cos

@[tmio T, powerlib_foundation] private theorem hasDerivAt_sin_mul (ω s : ℝ) :
    HasDerivAt (fun s => Real.sin (ω * s)) (ω * Real.cos (ω * s)) s := by
  simpa [mul_comm] using ((hasDerivAt_id' s).const_mul ω).sin

@[tmio T, powerlib_foundation] private theorem contDiff_cos_mul (ω : ℝ) :
    ContDiff ℝ 1 (fun s => Real.cos (ω * s)) := by fun_prop

@[tmio T, powerlib_foundation] private theorem contDiff_sin_mul (ω : ℝ) :
    ContDiff ℝ 1 (fun s => Real.sin (ω * s)) := by fun_prop

@[tmio T, powerlib_foundation] private theorem contDiff_neg_sin_mul (ω : ℝ) :
    ContDiff ℝ 1 (fun s => -Real.sin (ω * s)) := by fun_prop

/-- Closed form of the radial noise, `ŵ_k = w_k − w_k(0)`:
`cos(ωt) ŵ₀(t) + sin(ωt) ŵ₁(t) + ω ∫₀ᵗ (sin(ωr) ŵ₀(r) − cos(ωr) ŵ₁(r)) dr`. -/
@[tmio T, powerlib_foundation] theorem radNoise_eq (ω : ℝ) {w : ℝ → State 2} (hw : Continuous w)
    (t : ℝ) :
    radNoise ω w t = Real.cos (ω * t) * (w t 0 - w 0 0) + Real.sin (ω * t) * (w t 1 - w 0 1) +
      ω * ∫ r in (0 : ℝ)..t, (Real.sin (ω * r) * (w r 0 - w 0 0) -
        Real.cos (ω * r) * (w r 1 - w 0 1)) := by
  have hw0 : Continuous fun s => w s 0 := (PiLp.continuous_apply 2 _ 0).comp hw
  have hw1 : Continuous fun s => w s 1 := (PiLp.continuous_apply 2 _ 1).comp hw
  have hdc : deriv (fun s => Real.cos (ω * s)) = fun s => -(ω * Real.sin (ω * s)) :=
    funext fun s => (hasDerivAt_cos_mul ω s).deriv
  have hds : deriv (fun s => Real.sin (ω * s)) = fun s => ω * Real.cos (ω * s) :=
    funext fun s => (hasDerivAt_sin_mul ω s).deriv
  have i0 : IntervalIntegrable (fun r => Real.sin (ω * r) * (w r 0 - w 0 0)) volume 0 t :=
    ((by fun_prop : Continuous fun r => Real.sin (ω * r)).mul
      (hw0.sub continuous_const)).intervalIntegrable 0 t
  have i1 : IntervalIntegrable (fun r => Real.cos (ω * r) * (w r 1 - w 0 1)) volume 0 t :=
    ((by fun_prop : Continuous fun r => Real.cos (ω * r)).mul
      (hw1.sub continuous_const)).intervalIntegrable 0 t
  rw [radNoise, wienerIntegral_eq_incr (contDiff_cos_mul ω) hw0,
    wienerIntegral_eq_incr (contDiff_sin_mul ω) hw1, hdc, hds, intervalIntegral.integral_sub i0 i1]
  simp only [smul_eq_mul]
  have e1 : ∫ r in (0 : ℝ)..t, (w r 0 - w 0 0) * -(ω * Real.sin (ω * r)) =
      -(ω * ∫ r in (0 : ℝ)..t, Real.sin (ω * r) * (w r 0 - w 0 0)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext r; ring
  have e2 : ∫ r in (0 : ℝ)..t, (w r 1 - w 0 1) * (ω * Real.cos (ω * r)) =
      ω * ∫ r in (0 : ℝ)..t, Real.cos (ω * r) * (w r 1 - w 0 1) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext r; ring
  rw [e1, e2]
  ring

/-- Closed form of the tangential noise:
`−sin(ωt) ŵ₀(t) + cos(ωt) ŵ₁(t) + ω ∫₀ᵗ (cos(ωr) ŵ₀(r) + sin(ωr) ŵ₁(r)) dr`. -/
@[tmio T, powerlib_foundation] theorem tanNoise_eq (ω : ℝ) {w : ℝ → State 2} (hw : Continuous w)
    (t : ℝ) :
    tanNoise ω w t = -Real.sin (ω * t) * (w t 0 - w 0 0) + Real.cos (ω * t) * (w t 1 - w 0 1) +
      ω * ∫ r in (0 : ℝ)..t, (Real.cos (ω * r) * (w r 0 - w 0 0) +
        Real.sin (ω * r) * (w r 1 - w 0 1)) := by
  have hw0 : Continuous fun s => w s 0 := (PiLp.continuous_apply 2 _ 0).comp hw
  have hw1 : Continuous fun s => w s 1 := (PiLp.continuous_apply 2 _ 1).comp hw
  have hdc : deriv (fun s => Real.cos (ω * s)) = fun s => -(ω * Real.sin (ω * s)) :=
    funext fun s => (hasDerivAt_cos_mul ω s).deriv
  have hds : deriv (fun s => -Real.sin (ω * s)) = fun s => -(ω * Real.cos (ω * s)) :=
    funext fun s => (hasDerivAt_sin_mul ω s).neg.deriv
  have i0 : IntervalIntegrable (fun r => Real.cos (ω * r) * (w r 0 - w 0 0)) volume 0 t :=
    ((by fun_prop : Continuous fun r => Real.cos (ω * r)).mul
      (hw0.sub continuous_const)).intervalIntegrable 0 t
  have i1 : IntervalIntegrable (fun r => Real.sin (ω * r) * (w r 1 - w 0 1)) volume 0 t :=
    ((by fun_prop : Continuous fun r => Real.sin (ω * r)).mul
      (hw1.sub continuous_const)).intervalIntegrable 0 t
  rw [tanNoise, wienerIntegral_eq_incr (contDiff_neg_sin_mul ω) hw0,
    wienerIntegral_eq_incr (contDiff_cos_mul ω) hw1, hdc, hds, intervalIntegral.integral_add i0 i1]
  simp only [smul_eq_mul]
  have e1 : ∫ r in (0 : ℝ)..t, (w r 0 - w 0 0) * -(ω * Real.cos (ω * r)) =
      -(ω * ∫ r in (0 : ℝ)..t, Real.cos (ω * r) * (w r 0 - w 0 0)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext r; ring
  have e2 : ∫ r in (0 : ℝ)..t, (w r 1 - w 0 1) * -(ω * Real.sin (ω * r)) =
      -(ω * ∫ r in (0 : ℝ)..t, Real.sin (ω * r) * (w r 1 - w 0 1)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext r; ring
  rw [e1, e2]
  ring

/-! ## Jacobian identities along the cycle of (3-26) -/

/-- The tangential row of the variational matrix along the cycle of (3-26):
`(−sin, cos)·f'(x₀(t)) v = ω_h (cos, sin)·v`. -/
@[tmio M, powerlib_foundation] theorem tan_jac_cycle {γ : ℝ} (hγ : 0 < γ) (ωh t : ℝ)
    (v : State 2) :
    -Real.sin (ωh * t) * (fderiv ℝ (field (tr110Params γ ωh)) (cycle (tr110Params γ ωh) t) v) 0 +
      Real.cos (ωh * t) * (fderiv ℝ (field (tr110Params γ ωh)) (cycle (tr110Params γ ωh) t) v) 1 =
      ωh * (Real.cos (ωh * t) * v 0 + Real.sin (ωh * t) * v 1) := by
  obtain ⟨hrad, hfreq, -⟩ := tr110_limitCycle hγ ωh
  have hsq : √γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hsc := Real.sin_sq_add_cos_sq (ωh * t)
  rw [fderiv_field, toEuclideanCLM_apply_zero, toEuclideanCLM_apply_one]
  simp only [jac, cycle, mk_apply_zero, mk_apply_one, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  rw [hrad, hfreq]
  simp only [tr110Params]
  set c := Real.cos (ωh * t)
  set s := Real.sin (ωh * t)
  linear_combination (s * (c ^ 2 + s ^ 2) * v 0 - c * (c ^ 2 + s ^ 2) * v 1) * hsq +
    (γ * s * v 0 - γ * c * v 1) * hsc

/-- The radial row of the variational matrix along the cycle of (3-26):
`(cos, sin)·f'(x₀(t)) v = −2γ (cos, sin)·v + ω_h (sin, −cos)·v`. -/
@[tmio M, powerlib_foundation] theorem rad_jac_cycle {γ : ℝ} (hγ : 0 < γ) (ωh t : ℝ)
    (v : State 2) :
    Real.cos (ωh * t) * (fderiv ℝ (field (tr110Params γ ωh)) (cycle (tr110Params γ ωh) t) v) 0 +
      Real.sin (ωh * t) * (fderiv ℝ (field (tr110Params γ ωh)) (cycle (tr110Params γ ωh) t) v) 1 =
      -2 * γ * (Real.cos (ωh * t) * v 0 + Real.sin (ωh * t) * v 1) +
        ωh * (Real.sin (ωh * t) * v 0 - Real.cos (ωh * t) * v 1) := by
  obtain ⟨hrad, hfreq, -⟩ := tr110_limitCycle hγ ωh
  have hsq : √γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hsc := Real.sin_sq_add_cos_sq (ωh * t)
  rw [fderiv_field, toEuclideanCLM_apply_zero, toEuclideanCLM_apply_one]
  simp only [jac, cycle, mk_apply_zero, mk_apply_one, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  rw [hrad, hfreq]
  simp only [tr110Params]
  set c := Real.cos (ωh * t)
  set s := Real.sin (ωh * t)
  linear_combination (-3 * c * (c ^ 2 + s ^ 2) * v 0 - 3 * s * (c ^ 2 + s ^ 2) * v 1) * hsq +
    (-3 * γ * c * v 0 - 3 * γ * s * v 1) * hsc

/-! ## The linear response on the cycle: an OU amplitude and a Brownian phase -/

/-- A function on `[0, T]` with zero derivative and zero initial value vanishes. -/
@[tmio T, powerlib_foundation] private theorem eqOn_zero_of_deriv {Φ Φ' : ℝ → ℝ} {T K : ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ' t) t) (h0 : Φ 0 = 0)
    (hb : ∀ t ∈ Ico (0 : ℝ) T, |Φ' t| ≤ K * |Φ t|) : ∀ t ∈ Icc (0 : ℝ) T, Φ t = 0 :=
  eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (continuous_iff_continuousAt.2 fun t => (hΦ t).continuousAt).continuousOn
    (fun t _ => (hΦ t).hasDerivWithinAt) h0 (fun t ht => by simpa using hb t ht)

/-- **Amplitude–phase decomposition of the linear response on the cycle of (3-26).** Let `ζ` be
a continuous solution on `[0, T]` of the variational equation along the cycle
`x₀(t) = √γ (cos ω_h t, sin ω_h t)` of `ż = (γ + iω_h)z − |z|²z`, driven by a continuous noise
path `w`. In the co-rotating frame its tangential component is exactly the rotated noise and its
radial component is the Ornstein–Uhlenbeck response of rate `2γ` to the rotated noise:
`⟪u⊥, ζ⟫ = W̃₁` and `⟪u, ζ⟫ = lagSDESol (2γ) 0 1 0 W̃₀`, i.e.
`⟪u, ζ⟫(t) = −2γ ∫₀ᵗ ⟪u, ζ⟫ + W̃₀(t)`. -/
@[tmio M, powerlib_foundation] theorem variational_frame {γ : ℝ} (hγ : 0 < γ) (ωh : ℝ)
    {w : ℝ → State 2} (hw : Continuous w) {T : ℝ} {ζ : ℝ → State 2} (hζ : Continuous ζ)
    (hζeq : ∀ t ∈ Icc 0 T, ζ t = (∫ s in (0 : ℝ)..t,
      fderiv ℝ (field (tr110Params γ ωh)) (cycle (tr110Params γ ωh) s) (ζ s)) + (w t - w 0)) :
    ∀ t ∈ Icc 0 T, tanProj ωh ζ t = tanNoise ωh w t ∧
      radProj ωh ζ t = lagSDESol (2 * γ) 0 1 (fun _ => 0) (radNoise ωh w) t := by
  set p := tr110Params γ ωh with hp
  have hl : p.l₁ ≠ 0 := by simp [p, tr110Params]
  have hR : 0 ≤ -p.μ / p.l₁ := by simp [p, tr110Params]; exact hγ.le
  have hcyc : Continuous (cycle p) :=
    continuous_iff_continuousAt.2 fun t => (cycle_hasDerivAt p hl hR t).continuousAt
  set A : ℝ → State 2 := fun s => fderiv ℝ (field p) (cycle p s) (ζ s) with hAdef
  have hA : Continuous A :=
    (((field_contDiff p).continuous_fderiv one_ne_zero).comp hcyc).clm_apply hζ
  have hA0 : Continuous fun s => A s 0 := (PiLp.continuous_apply 2 _ 0).comp hA
  have hA1 : Continuous fun s => A s 1 := (PiLp.continuous_apply 2 _ 1).comp hA
  set η0 : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, A s 0
  set η1 : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, A s 1
  have hη0 : ∀ t, HasDerivAt η0 (A t 0) t := fun t =>
    (hA0.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hη1 : ∀ t, HasDerivAt η1 (A t 1) t := fun t =>
    (hA1.integral_hasStrictDerivAt 0 t).hasDerivAt
  set u0 : ℝ → ℝ := fun t => w t 0 - w 0 0
  set u1 : ℝ → ℝ := fun t => w t 1 - w 0 1
  have hu0 : Continuous u0 := ((PiLp.continuous_apply 2 _ 0).comp hw).sub continuous_const
  have hu1 : Continuous u1 := ((PiLp.continuous_apply 2 _ 1).comp hw).sub continuous_const
  have hζk : ∀ t ∈ Icc 0 T, ζ t 0 = η0 t + u0 t ∧ ζ t 1 = η1 t + u1 t := by
    intro t ht
    have hint : IntervalIntegrable A volume 0 t := hA.intervalIntegrable 0 t
    have e : ∀ k : Fin 2, (∫ s in (0 : ℝ)..t, A s) k = ∫ s in (0 : ℝ)..t, A s k := fun k => by
      have := ContinuousLinearMap.intervalIntegral_comp_comm (EuclideanSpace.proj k) hint
      simpa using this.symm
    have h := hζeq t ht
    refine ⟨?_, ?_⟩
    · rw [h, PiLp.add_apply, PiLp.sub_apply, e 0]
    · rw [h, PiLp.add_apply, PiLp.sub_apply, e 1]
  have hC : ∀ t, HasDerivAt (fun t => Real.cos (ωh * t)) (-(ωh * Real.sin (ωh * t))) t :=
    hasDerivAt_cos_mul ωh
  have hS : ∀ t, HasDerivAt (fun t => Real.sin (ωh * t)) (ωh * Real.cos (ωh * t)) t :=
    hasDerivAt_sin_mul ωh
  have hCc : Continuous fun t => Real.cos (ωh * t) := by fun_prop
  have hSc : Continuous fun t => Real.sin (ωh * t) := by fun_prop
  -- tangential component
  have htan : ∀ t ∈ Icc 0 T, tanProj ωh ζ t = tanNoise ωh w t := by
    have hg : Continuous fun r => Real.cos (ωh * r) * (w r 0 - w 0 0) +
        Real.sin (ωh * r) * (w r 1 - w 0 1) := (hCc.mul hu0).add (hSc.mul hu1)
    have hΦ : ∀ t, HasDerivAt (fun t => -Real.sin (ωh * t) * η0 t + Real.cos (ωh * t) * η1 t -
        ωh * ∫ r in (0 : ℝ)..t, (Real.cos (ωh * r) * (w r 0 - w 0 0) +
          Real.sin (ωh * r) * (w r 1 - w 0 1)))
        (-(ωh * Real.cos (ωh * t)) * η0 t - Real.sin (ωh * t) * A t 0 +
          (-(ωh * Real.sin (ωh * t)) * η1 t + Real.cos (ωh * t) * A t 1) -
          ωh * (Real.cos (ωh * t) * (w t 0 - w 0 0) + Real.sin (ωh * t) * (w t 1 - w 0 1))) t :=
      fun t => ((((hS t).neg.mul (hη0 t)).add ((hC t).mul (hη1 t))).sub
        ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul ωh)).congr_deriv
        (by simp only [Pi.neg_apply]; ring)
    have hz := eqOn_zero_of_deriv (T := T) (K := 0) hΦ (by simp [η0, η1]) (fun t ht => by
      have htT : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      obtain ⟨h0, h1⟩ := hζk t htT
      have hj : -Real.sin (ωh * t) * A t 0 + Real.cos (ωh * t) * A t 1 =
          ωh * (Real.cos (ωh * t) * ζ t 0 + Real.sin (ωh * t) * ζ t 1) :=
        tan_jac_cycle hγ ωh t (ζ t)
      have : -(ωh * Real.cos (ωh * t)) * η0 t - Real.sin (ωh * t) * A t 0 +
          (-(ωh * Real.sin (ωh * t)) * η1 t + Real.cos (ωh * t) * A t 1) -
          ωh * (Real.cos (ωh * t) * (w t 0 - w 0 0) + Real.sin (ωh * t) * (w t 1 - w 0 1)) = 0 := by
        linear_combination hj + ωh * Real.cos (ωh * t) * h0 + ωh * Real.sin (ωh * t) * h1
      rw [this, abs_zero, zero_mul])
    intro t ht
    obtain ⟨h0, h1⟩ := hζk t ht
    have hzt := hz t ht
    rw [tanNoise_eq ωh hw t, tanProj, h0, h1]
    linear_combination hzt
  -- radial component
  have hrc : Continuous (radProj ωh ζ) :=
    (hCc.mul ((PiLp.continuous_apply 2 _ 0).comp hζ)).add
      (hSc.mul ((PiLp.continuous_apply 2 _ 1).comp hζ))
  have hradEq : ∀ t ∈ Icc 0 T, radProj ωh ζ t =
      -(2 * γ) * (∫ r in (0 : ℝ)..t, radProj ωh ζ r) + radNoise ωh w t := by
    have hg : Continuous fun r => Real.sin (ωh * r) * (w r 0 - w 0 0) -
        Real.cos (ωh * r) * (w r 1 - w 0 1) := (hSc.mul hu0).sub (hCc.mul hu1)
    have hΨ : ∀ t, HasDerivAt (fun t => Real.cos (ωh * t) * η0 t + Real.sin (ωh * t) * η1 t -
        ωh * (∫ r in (0 : ℝ)..t, (Real.sin (ωh * r) * (w r 0 - w 0 0) -
          Real.cos (ωh * r) * (w r 1 - w 0 1))) + 2 * γ * ∫ r in (0 : ℝ)..t, radProj ωh ζ r)
        (-(ωh * Real.sin (ωh * t)) * η0 t + Real.cos (ωh * t) * A t 0 +
          (ωh * Real.cos (ωh * t) * η1 t + Real.sin (ωh * t) * A t 1) -
          ωh * (Real.sin (ωh * t) * (w t 0 - w 0 0) - Real.cos (ωh * t) * (w t 1 - w 0 1)) +
          2 * γ * radProj ωh ζ t) t :=
      fun t => (((((hC t).mul (hη0 t)).add ((hS t).mul (hη1 t))).sub
        ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul ωh)).add
        ((hrc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul (2 * γ))).congr_deriv (by ring)
    have hz := eqOn_zero_of_deriv (T := T) (K := 0) hΨ (by simp [η0, η1]) (fun t ht => by
      have htT : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      obtain ⟨h0, h1⟩ := hζk t htT
      have hj : Real.cos (ωh * t) * A t 0 + Real.sin (ωh * t) * A t 1 =
          -2 * γ * (Real.cos (ωh * t) * ζ t 0 + Real.sin (ωh * t) * ζ t 1) +
            ωh * (Real.sin (ωh * t) * ζ t 0 - Real.cos (ωh * t) * ζ t 1) :=
        rad_jac_cycle hγ ωh t (ζ t)
      have : -(ωh * Real.sin (ωh * t)) * η0 t + Real.cos (ωh * t) * A t 0 +
          (ωh * Real.cos (ωh * t) * η1 t + Real.sin (ωh * t) * A t 1) -
          ωh * (Real.sin (ωh * t) * (w t 0 - w 0 0) - Real.cos (ωh * t) * (w t 1 - w 0 1)) +
          2 * γ * radProj ωh ζ t = 0 := by
        simp only [radProj]
        linear_combination hj + ωh * Real.sin (ωh * t) * h0 - ωh * Real.cos (ωh * t) * h1
      rw [this, abs_zero, zero_mul])
    intro t ht
    obtain ⟨h0, h1⟩ := hζk t ht
    have hzt := hz t ht
    rw [radNoise_eq ωh hw t]
    simp only [radProj] at hzt ⊢
    rw [h0, h1]
    linear_combination hzt
  -- identification with the noisy lag of rate `2γ`
  have hRN : Continuous (radNoise ωh w) :=
    (continuous_wienerIntegral (contDiff_cos_mul ωh) ((PiLp.continuous_apply 2 _ 0).comp hw)).add
      (continuous_wienerIntegral (contDiff_sin_mul ωh) ((PiLp.continuous_apply 2 _ 1).comp hw))
  have hRN0 : radNoise ωh w 0 = 0 := by simp [radNoise, wienerIntegral_zero_time]
  set X := lagSDESol (2 * γ) 0 1 (fun _ => 0) (radNoise ωh w) with hXdef
  have hX : ∀ t, X t = 0 + (∫ s in (0 : ℝ)..t, -(2 * γ) * (X s - 0)) +
      1 * (radNoise ωh w t - radNoise ωh w 0) :=
    lagSDESol_integral_eq (2 * γ) 0 1 continuous_const hRN
  have hXc : Continuous X := by
    have hcorr : Continuous fun s => (0 : ℝ) - 1 * (radNoise ωh w s - radNoise ωh w 0) :=
      continuous_const.sub (continuous_const.mul (hRN.sub continuous_const))
    have h : X = fun t => LagLimit.lagSol (2 * γ) 0
        (fun s => (0 : ℝ) - 1 * (radNoise ωh w s - radNoise ωh w 0)) t +
        1 * (radNoise ωh w t - radNoise ωh w 0) :=
      funext (lagSDESol_eq (2 * γ) 0 1 continuous_const hRN)
    rw [h]
    exact (continuous_iff_continuousAt.2 fun t =>
      (LagLimit.lagSol_hasDerivAt (2 * γ) 0 hcorr t).continuousAt).add
      (continuous_const.mul (hRN.sub continuous_const))
  have hdiff : Continuous fun r => radProj ωh ζ r - X r := hrc.sub hXc
  have hD : ∀ t, HasDerivAt (fun t => ∫ r in (0 : ℝ)..t, (radProj ωh ζ r - X r))
      (radProj ωh ζ t - X t) t := fun t => (hdiff.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hDeq : ∀ t ∈ Icc 0 T, radProj ωh ζ t - X t =
      -(2 * γ) * ∫ r in (0 : ℝ)..t, (radProj ωh ζ r - X r) := by
    intro t ht
    rw [intervalIntegral.integral_sub (hrc.intervalIntegrable 0 t) (hXc.intervalIntegrable 0 t),
      hradEq t ht, hX t, hRN0]
    simp only [sub_zero, zero_add, one_mul, intervalIntegral.integral_const_mul]
    ring
  have hz := eqOn_zero_of_deriv (T := T) (K := 2 * γ) hD (by simp) (fun t ht => by
    rw [hDeq t (Ico_subset_Icc_self ht), abs_mul, abs_neg, abs_of_pos (by linarith : 0 < 2 * γ)])
  intro t ht
  refine ⟨htan t ht, ?_⟩
  have h1 := hDeq t ht
  rw [hz t ht, mul_zero] at h1
  linarith

/-! ## The amplitude–phase form (3-28) of the noisy cycle to first order -/

@[tmio T, powerlib_foundation] private theorem abs_rot_comb_le (a b : ℝ) (v : State 2) :
    |a * v 0 + b * v 1| ≤ √(a ^ 2 + b ^ 2) * ‖v‖ := by
  rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [sq_abs, norm_sq_eq]
  nlinarith [sq_nonneg (a * v 1 - b * v 0)]

@[tmio T, powerlib_foundation] private theorem abs_radProj_le (ω : ℝ) (ζ : ℝ → State 2) (t : ℝ) :
    |radProj ω ζ t| ≤ ‖ζ t‖ := by
  have h := abs_rot_comb_le (Real.cos (ω * t)) (Real.sin (ω * t)) (ζ t)
  rwa [Real.cos_sq_add_sin_sq, Real.sqrt_one, one_mul] at h

@[tmio T, powerlib_foundation] private theorem abs_tanProj_le (ω : ℝ) (ζ : ℝ → State 2) (t : ℝ) :
    |tanProj ω ζ t| ≤ ‖ζ t‖ := by
  have h := abs_rot_comb_le (-Real.sin (ω * t)) (Real.cos (ω * t)) (ζ t)
  rwa [neg_sq, Real.sin_sq_add_cos_sq, Real.sqrt_one, one_mul] at h

/-- **TR-110 (3-28) to first order, path by path.** For the noisy normal form (3-26) started on
its cycle, `x_σ(0) = (√γ, 0)`, and every continuous noise path there are the variational solution
`ζ` along the cycle, `σ₀ > 0` and `C` such that for `|σ| ≤ σ₀` every solution satisfies, uniformly
on `[0, T]`,
`⟪u(t), x_σ(t)⟫ = √γ + σ p(t) + O(σ²)` and `⟪u⊥(t), x_σ(t)⟫ = σ q(t) + O(σ²)` with
`u = (cos ω_h t, sin ω_h t)`, `p = radProj ζ` (an OU process of rate `2γ`) and `q = tanProj ζ` (a
Brownian motion), by `variational_frame` and `covariance_frame`: the amplitude is `√γ + σp` and
the phase lag `σq/√γ` to first order. -/
@[tmio M, powerlib_foundation] theorem tr110_amplitude_phase {γ : ℝ} (hγ : 0 < γ) (ωh : ℝ)
    {w : ℝ → State 2} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    ∃ ζ : ℝ → State 2, Continuous ζ ∧
      (∀ t ∈ Icc 0 T, ζ t = (∫ s in (0 : ℝ)..t,
        fderiv ℝ (field (tr110Params γ ωh)) (cycle (tr110Params γ ωh) s) (ζ s)) + (w t - w 0)) ∧
      ∃ σ₀ > 0, ∃ C, ∀ σ : ℝ, |σ| ≤ σ₀ → ∀ x : ℝ → State 2, Continuous x →
        (∀ t ∈ Icc 0 T, x t = cycle (tr110Params γ ωh) 0 +
          (∫ s in (0 : ℝ)..t, field (tr110Params γ ωh) (x s)) + σ • (w t - w 0)) →
        ∀ t ∈ Icc 0 T, |radProj ωh x t - √γ - σ * radProj ωh ζ t| ≤ C * σ ^ 2 ∧
          |tanProj ωh x t - σ * tanProj ωh ζ t| ≤ C * σ ^ 2 := by
  set p := tr110Params γ ωh
  obtain ⟨hrad, hfreq, -⟩ := tr110_limitCycle hγ ωh
  have hrad' : radius p = √γ := hrad
  have hfreq' : frequency p = ωh := hfreq
  have hl : p.l₁ ≠ 0 := by simp [p, tr110Params]
  have hR : 0 ≤ -p.μ / p.l₁ := by simp [p, tr110Params]; exact hγ.le
  have hcd := cycle_hasDerivAt p hl hR
  have hcyc : Continuous (cycle p) := continuous_iff_continuousAt.2 fun t => (hcd t).continuousAt
  have h₀ : ∀ t ∈ Icc 0 T, cycle p t = cycle p 0 + ∫ s in (0 : ℝ)..t, field p (cycle p s) := by
    intro t _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hcd s)
      (((field_contDiff p (k := 1)).continuous.comp hcyc).intervalIntegrable 0 t)]
    abel
  obtain ⟨ζ, hζ, hζeq⟩ := SmallNoise.exists_variational (field_contDiff p) hcyc hw hT
  obtain ⟨σ₀, hσ₀, C, hC⟩ :=
    SmallNoise.norm_sub_sub_smul_le (field_contDiff p) hw hcyc h₀ hζ hζeq
  refine ⟨ζ, hζ, hζeq, σ₀, hσ₀, C, fun σ hσ x hx hxeq t ht => ?_⟩
  have hb := hC σ hσ x hx hxeq t ht
  have hc0 : radProj ωh (cycle p) t = √γ := by
    simp only [radProj, cycle, mk_apply_zero, mk_apply_one, hrad', hfreq']
    have := Real.cos_sq_add_sin_sq (ωh * t)
    linear_combination √γ * this
  have hc1 : tanProj ωh (cycle p) t = 0 := by
    simp only [tanProj, cycle, mk_apply_zero, mk_apply_one, hrad', hfreq']
    ring
  set v : ℝ → State 2 := fun τ => x τ - cycle p τ - σ • ζ τ
  have hrv : radProj ωh x t - √γ - σ * radProj ωh ζ t = radProj ωh v t := by
    rw [← hc0]; simp only [radProj, v, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have htv : tanProj ωh x t - σ * tanProj ωh ζ t = tanProj ωh v t := by
    rw [show tanProj ωh x t - σ * tanProj ωh ζ t =
      tanProj ωh x t - tanProj ωh (cycle p) t - σ * tanProj ωh ζ t by rw [hc1, sub_zero]]
    simp only [tanProj, v, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [hrv, htv]
  exact ⟨(abs_radProj_le ωh v t).trans hb, (abs_tanProj_le ωh v t).trans hb⟩

/-! ## Second moments: the rotated noise is again standard, OU amplitude and Brownian phase -/

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : Fin 2 → ℝ → Ω → ℝ}

/-- The noise path of a sample: `t ↦ (W₀(t, ω), W₁(t, ω))`. -/
def path (W : Fin 2 → ℝ → Ω → ℝ) (ω : Ω) (t : ℝ) : State 2 := WithLp.toLp 2 fun k => W k t ω

omit [IsProbabilityMeasure P] in
@[tmio T, powerlib_foundation] private theorem continuous_path
    (hc : ∀ k ω, Continuous fun u => W k u ω) (ω : Ω) : Continuous (path W ω) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => hc k ω)

/-- Second moment of two-channel Wiener integrals of independent standard noise:
`E[(∫ a₀ dW₀ + ∫ a₁ dW₁)(u) (∫ b₀ dW₀ + ∫ b₁ dW₁)(v)] = ∫₀^{min(u,v)} (a₀b₀ + a₁b₁)`. -/
@[tmio T, powerlib_foundation] theorem integral_pair_mul
    (hc : ∀ k ω, Continuous fun u => W k u ω) (hm : ∀ k u, Measurable (W k u))
    (hL2 : ∀ k u, MemLp (W k u) 2 P)
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, W k u ω * W l v ω ∂P = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l * min u v)
    {a₀ a₁ b₀ b₁ : ℝ → ℝ} (ha₀ : ContDiff ℝ 1 a₀) (ha₁ : ContDiff ℝ 1 a₁)
    (hb₀ : ContDiff ℝ 1 b₀) (hb₁ : ContDiff ℝ 1 b₁) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ ω, (wienerIntegral a₀ (fun r => W 0 r ω) u + wienerIntegral a₁ (fun r => W 1 r ω) u) *
      (wienerIntegral b₀ (fun r => W 0 r ω) v + wienerIntegral b₁ (fun r => W 1 r ω) v) ∂P =
      ∫ r in (0 : ℝ)..min u v, (a₀ r * b₀ r + a₁ r * b₁ r) := by
  have hI : ∀ (k : Fin 2) {g : ℝ → ℝ}, ContDiff ℝ 1 g → ∀ {τ : ℝ}, 0 ≤ τ →
      MemLp (fun ω => wienerIntegral g (fun r => W k r ω) τ) 2 P := fun k g hg τ hτ =>
    memLp_wienerIntegral (hc k) (hm k) (hL2 k) hτ (sqMoment_le hQ k τ) g hg
  have e : ∀ ω, (wienerIntegral a₀ (fun r => W 0 r ω) u + wienerIntegral a₁ (fun r => W 1 r ω) u) *
      (wienerIntegral b₀ (fun r => W 0 r ω) v + wienerIntegral b₁ (fun r => W 1 r ω) v) =
      wienerIntegral a₀ (fun r => W 0 r ω) u * wienerIntegral b₀ (fun r => W 0 r ω) v +
      wienerIntegral a₀ (fun r => W 0 r ω) u * wienerIntegral b₁ (fun r => W 1 r ω) v +
      (wienerIntegral a₁ (fun r => W 1 r ω) u * wienerIntegral b₀ (fun r => W 0 r ω) v +
      wienerIntegral a₁ (fun r => W 1 r ω) u * wienerIntegral b₁ (fun r => W 1 r ω) v) :=
    fun ω => by ring
  simp_rw [e]
  set A₀ := fun ω => wienerIntegral a₀ (fun r => W 0 r ω) u
  set A₁ := fun ω => wienerIntegral a₁ (fun r => W 1 r ω) u
  set B₀ := fun ω => wienerIntegral b₀ (fun r => W 0 r ω) v
  set B₁ := fun ω => wienerIntegral b₁ (fun r => W 1 r ω) v
  have i00 : Integrable (fun ω => A₀ ω * B₀ ω) P := (hI 0 ha₀ hu).integrable_mul (hI 0 hb₀ hv)
  have i01 : Integrable (fun ω => A₀ ω * B₁ ω) P := (hI 0 ha₀ hu).integrable_mul (hI 1 hb₁ hv)
  have i10 : Integrable (fun ω => A₁ ω * B₀ ω) P := (hI 1 ha₁ hu).integrable_mul (hI 0 hb₀ hv)
  have i11 : Integrable (fun ω => A₁ ω * B₁ ω) P := (hI 1 ha₁ hu).integrable_mul (hI 1 hb₁ hv)
  have j0 : Integrable (fun ω => A₀ ω * B₀ ω + A₀ ω * B₁ ω) P := i00.add i01
  have j1 : Integrable (fun ω => A₁ ω * B₀ ω + A₁ ω * B₁ ω) P := i10.add i11
  rw [integral_add j0 j1, integral_add i00 i01, integral_add i10 i11]
  simp only [A₀, A₁, B₀, B₁]
  rw [integral_wienerIntegral_mul hc hm hL2 hQ ha₀ hb₀ 0 0 hu hv,
    integral_wienerIntegral_mul hc hm hL2 hQ ha₀ hb₁ 0 1 hu hv,
    integral_wienerIntegral_mul hc hm hL2 hQ ha₁ hb₀ 1 0 hu hv,
    integral_wienerIntegral_mul hc hm hL2 hQ ha₁ hb₁ 1 1 hu hv]
  have k0 : IntervalIntegrable (fun r => a₀ r * b₀ r) volume 0 (min u v) :=
    (ha₀.continuous.mul hb₀.continuous).intervalIntegrable _ _
  have k1 : IntervalIntegrable (fun r => a₁ r * b₁ r) volume 0 (min u v) :=
    (ha₁.continuous.mul hb₁.continuous).intervalIntegrable _ _
  rw [intervalIntegral.integral_add k0 k1]
  simp

/-- The noise in the co-rotating frame as a two-component process (radial `0`, tangential `1`),
frozen at its initial value for negative times. -/
def rotNoise (ωh : ℝ) (W : Fin 2 → ℝ → Ω → ℝ) (k : Fin 2) (u : ℝ) (ω : Ω) : ℝ :=
  (![radNoise ωh (path W ω) (max u 0), tanNoise ωh (path W ω) (max u 0)] : Fin 2 → ℝ) k

omit [IsProbabilityMeasure P] in
@[tmio T, powerlib_foundation] private theorem radNoise_path (ωh : ℝ) (ω : Ω) (t : ℝ) :
    radNoise ωh (path W ω) t = wienerIntegral (fun s => Real.cos (ωh * s)) (fun s => W 0 s ω) t +
      wienerIntegral (fun s => Real.sin (ωh * s)) (fun s => W 1 s ω) t := rfl

omit [IsProbabilityMeasure P] in
@[tmio T, powerlib_foundation] private theorem tanNoise_path (ωh : ℝ) (ω : Ω) (t : ℝ) :
    tanNoise ωh (path W ω) t = wienerIntegral (fun s => -Real.sin (ωh * s)) (fun s => W 0 s ω) t +
      wienerIntegral (fun s => Real.cos (ωh * s)) (fun s => W 1 s ω) t := rfl

/-- **The rotated noise is again a pair of independent standard Brownian-type noises**
(rotation invariance at the level of second moments): continuous paths, measurable square
integrable centred marginals and `E[W̃_j(u) W̃_k(v)] = δ_jk min(u, v)`. -/
@[tmio T, powerlib_foundation] theorem rotNoise_standard (ωh : ℝ)
    (hc : ∀ k ω, Continuous fun u => W k u ω) (hm : ∀ k u, Measurable (W k u))
    (hL2 : ∀ k u, MemLp (W k u) 2 P)
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, W k u ω * W l v ω ∂P = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) :
    (∀ k ω, Continuous fun u => rotNoise ωh W k u ω) ∧ (∀ k u, Measurable (rotNoise ωh W k u)) ∧
    (∀ k u, MemLp (rotNoise ωh W k u) 2 P) ∧
    (∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, rotNoise ωh W k u ω * rotNoise ωh W l v ω ∂P =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) k l * min u v) ∧
    (∀ k u, 0 ≤ u → ∫ ω, rotNoise ωh W k u ω ∂P = 0) := by
  have hmax : Continuous fun u : ℝ => max u 0 := continuous_id.max continuous_const
  have hI : ∀ (k : Fin 2) {g : ℝ → ℝ}, ContDiff ℝ 1 g → ∀ {τ : ℝ}, 0 ≤ τ →
      MemLp (fun ω => wienerIntegral g (fun r => W k r ω) τ) 2 P := fun k g hg τ hτ =>
    memLp_wienerIntegral (hc k) (hm k) (hL2 k) hτ (sqMoment_le hQ k τ) g hg
  have hE : ∀ (k : Fin 2) {g : ℝ → ℝ}, ContDiff ℝ 1 g → ∀ {τ : ℝ}, 0 ≤ τ →
      ∫ ω, wienerIntegral g (fun r => W k r ω) τ ∂P = 0 := fun k g hg τ hτ =>
    integral_wienerIntegral (hc k) (hm k) (hL2 k) hτ (sqMoment_le hQ k τ) (hmean k) hg
  have hcs : ∀ r : ℝ, Real.cos (ωh * r) * Real.cos (ωh * r) +
      Real.sin (ωh * r) * Real.sin (ωh * r) = 1 := fun r => by
    rw [← sq, ← sq, Real.cos_sq_add_sin_sq]
  have hsc : ∀ r : ℝ, -Real.sin (ωh * r) * -Real.sin (ωh * r) +
      Real.cos (ωh * r) * Real.cos (ωh * r) = 1 := fun r => by
    rw [neg_mul_neg, ← sq, ← sq, Real.sin_sq_add_cos_sq]
  have hx : ∀ r : ℝ, Real.cos (ωh * r) * -Real.sin (ωh * r) +
      Real.sin (ωh * r) * Real.cos (ωh * r) = 0 := fun r => by ring
  have hx' : ∀ r : ℝ, -Real.sin (ωh * r) * Real.cos (ωh * r) +
      Real.cos (ωh * r) * Real.sin (ωh * r) = 0 := fun r => by ring
  refine ⟨fun k ω => ?_, fun k u => ?_, fun k u => ?_, fun k l u v hu hv => ?_, fun k u hu => ?_⟩
  · have h0 : Continuous fun u => radNoise ωh (path W ω) (max u 0) :=
      ((continuous_wienerIntegral (contDiff_cos_mul ωh) (hc 0 ω)).add
        (continuous_wienerIntegral (contDiff_sin_mul ωh) (hc 1 ω))).comp hmax
    have h1 : Continuous fun u => tanNoise ωh (path W ω) (max u 0) :=
      ((continuous_wienerIntegral (contDiff_neg_sin_mul ωh) (hc 0 ω)).add
        (continuous_wienerIntegral (contDiff_cos_mul ωh) (hc 1 ω))).comp hmax
    fin_cases k
    · exact h0
    · exact h1
  · fin_cases k
    · exact (measurable_wienerIntegral (hc 0) (hm 0) (contDiff_cos_mul ωh) _).add
        (measurable_wienerIntegral (hc 1) (hm 1) (contDiff_sin_mul ωh) _)
    · exact (measurable_wienerIntegral (hc 0) (hm 0) (contDiff_neg_sin_mul ωh) _).add
        (measurable_wienerIntegral (hc 1) (hm 1) (contDiff_cos_mul ωh) _)
  · have hu : 0 ≤ max u 0 := le_max_right _ _
    fin_cases k
    · exact (hI 0 (contDiff_cos_mul ωh) hu).add (hI 1 (contDiff_sin_mul ωh) hu)
    · exact (hI 0 (contDiff_neg_sin_mul ωh) hu).add (hI 1 (contDiff_cos_mul ωh) hu)
  · have eu : max u 0 = u := max_eq_left hu
    have ev : max v 0 = v := max_eq_left hv
    have hm0 : 0 ≤ min u v := le_min hu hv
    fin_cases k <;> fin_cases l <;>
      simp only [rotNoise, eu, ev, radNoise_path, tanNoise_path, Fin.zero_eta, Fin.mk_one,
        cons_val_zero, cons_val_one, Matrix.one_apply_eq, one_mul]
    · rw [integral_pair_mul hc hm hL2 hQ (contDiff_cos_mul ωh) (contDiff_sin_mul ωh)
        (contDiff_cos_mul ωh) (contDiff_sin_mul ωh) hu hv]
      simp only [hcs, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    · rw [integral_pair_mul hc hm hL2 hQ (contDiff_cos_mul ωh) (contDiff_sin_mul ωh)
        (contDiff_neg_sin_mul ωh) (contDiff_cos_mul ωh) hu hv]
      simp only [hx, intervalIntegral.integral_zero]
      simp
    · rw [integral_pair_mul hc hm hL2 hQ (contDiff_neg_sin_mul ωh) (contDiff_cos_mul ωh)
        (contDiff_cos_mul ωh) (contDiff_sin_mul ωh) hu hv]
      simp only [hx', intervalIntegral.integral_zero]
      simp
    · rw [integral_pair_mul hc hm hL2 hQ (contDiff_neg_sin_mul ωh) (contDiff_cos_mul ωh)
        (contDiff_neg_sin_mul ωh) (contDiff_cos_mul ωh) hu hv]
      simp only [hsc, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  · have hu' : 0 ≤ max u 0 := le_max_right _ _
    fin_cases k
    · simp only [rotNoise, radNoise_path, Fin.zero_eta, cons_val_zero]
      rw [integral_add ((hI 0 (contDiff_cos_mul ωh) hu').integrable one_le_two)
        ((hI 1 (contDiff_sin_mul ωh) hu').integrable one_le_two),
        hE 0 (contDiff_cos_mul ωh) hu', hE 1 (contDiff_sin_mul ωh) hu', add_zero]
    · simp only [rotNoise, tanNoise_path, Fin.mk_one, cons_val_one, cons_val_zero]
      rw [integral_add ((hI 0 (contDiff_neg_sin_mul ωh) hu').integrable one_le_two)
        ((hI 1 (contDiff_cos_mul ωh) hu').integrable one_le_two),
        hE 0 (contDiff_neg_sin_mul ωh) hu', hE 1 (contDiff_cos_mul ωh) hu', add_zero]

/-- **TR-110 (3-28): an Ornstein–Uhlenbeck amplitude and a Brownian phase.** Let the noise be a
pair of independent standard Brownian-type processes and, sample by sample, let `ζ_ω` be a
continuous solution on `[0, T]` of the variational equation along the cycle
`√γ (cos ω_h t, sin ω_h t)` of (3-26) driven by the sample path. Then for `0 ≤ s ≤ t ≤ T` the
radial component `p = ⟪u, ζ⟫` is an OU process of rate `2γ`,
`Cov(p(t), p(s)) = e^{−2γ(t−s)} (1 − e^{−4γs})/(4γ)`, the tangential component `q = ⟪u⊥, ζ⟫` is a
Brownian motion, `Cov(q(t), q(s)) = min(t, s)`, and the two are uncorrelated. With the expansion
`x_σ = x₀ + σζ + O(σ²)` (`NoisyHopf.noisyHopf_expansion`) the amplitude deviation is `σ p` (the
`p` of (3-28), `σ_p = σ`) and the phase deviation is `σ q/√γ` (the `φ − ω_h t` of (3-28),
`σ_φ = σ`) to first order. -/
@[tmio M, powerlib_foundation] theorem covariance_frame {γ : ℝ} (hγ : 0 < γ) (ωh : ℝ)
    (hc : ∀ k ω, Continuous fun u => W k u ω) (hm : ∀ k u, Measurable (W k u))
    (hL2 : ∀ k u, MemLp (W k u) 2 P)
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, W k u ω * W l v ω ∂P = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {T : ℝ} {ζ : Ω → ℝ → State 2}
    (hζ : ∀ ω, Continuous (ζ ω))
    (hζeq : ∀ ω, ∀ t ∈ Icc 0 T, ζ ω t = (∫ s in (0 : ℝ)..t,
      fderiv ℝ (field (tr110Params γ ωh)) (cycle (tr110Params γ ωh) s) (ζ ω s)) +
        (path W ω t - path W ω 0))
    {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    cov[fun ω => radProj ωh (ζ ω) t, fun ω => radProj ωh (ζ ω) s; P] =
        Real.exp (-(2 * γ) * (t - s)) * OU.ouVar (2 * γ) 1 s ∧
      cov[fun ω => tanProj ωh (ζ ω) t, fun ω => tanProj ωh (ζ ω) s; P] = min t s ∧
      cov[fun ω => radProj ωh (ζ ω) t, fun ω => tanProj ωh (ζ ω) s; P] = 0 := by
  obtain ⟨hc', hm', hL2', hQ', hmean'⟩ := rotNoise_standard ωh hc hm hL2 hQ hmean
  have ht : 0 ≤ t := hs.trans hst
  have htI : t ∈ Icc 0 T := ⟨ht, htT⟩
  have hsI : s ∈ Icc 0 T := ⟨hs, hst.trans htT⟩
  have hdec := fun ω => variational_frame hγ ωh (continuous_path hc ω) (hζ ω) (hζeq ω)
  -- the radial component is the noisy lag of the rotated radial noise
  have hrad : ∀ τ ∈ Icc 0 T, (fun ω => radProj ωh (ζ ω) τ) =
      fun ω => lagSDESol (2 * γ) 0 1 (fun _ => 0) (fun u => rotNoise ωh W 0 u ω) τ := by
    intro τ hτ
    funext ω
    rw [(hdec ω τ hτ).2]
    simp only [lagSDESol]
    congr 2
    refine wienerIntegral_congr _ fun u hu => ?_
    rw [uIcc_of_le hτ.1] at hu
    simp [rotNoise, max_eq_left hu.1]
  have htan : ∀ τ ∈ Icc 0 T, (fun ω => tanProj ωh (ζ ω) τ) = fun ω => rotNoise ωh W 1 τ ω := by
    intro τ hτ
    funext ω
    rw [(hdec ω τ hτ).1]
    simp [rotNoise, max_eq_left hτ.1]
  have hBM : ∀ u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, rotNoise ωh W 0 u ω * rotNoise ωh W 0 v ω ∂P = min u v := fun u v hu hv => by
    rw [hQ' 0 0 u v hu hv, Matrix.one_apply_eq, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrad t htI, hrad s hsI]
    exact covariance_lagSDESol (by positivity) 0 1 _ (hc' 0) (hm' 0) (hL2' 0) hBM (hmean' 0)
      hs hst
  · rw [htan t htI, htan s hsI, covariance_eq_sub (hL2' 1 t) (hL2' 1 s), hmean' 1 t ht,
      zero_mul, sub_zero]
    exact (hQ' 1 1 t s ht hs).trans (by rw [Matrix.one_apply_eq, one_mul])
  · rw [hrad t htI, htan s hsI]
    have hk : ContDiff ℝ 1 fun r => Real.exp (-(2 * γ) * (t - r)) := by fun_prop
    have hI := memLp_wienerIntegral (hc' 0) (hm' 0) (hL2' 0) ht (sqMoment_le hQ' 0 t) _ hk
    have hlag0 : LagLimit.lagSol (2 * γ) 0 (fun _ => 0) t = 0 := by simp [LagLimit.lagSol]
    simp only [lagSDESol, hlag0, zero_add, one_mul]
    rw [covariance_eq_sub hI (hL2' 1 s),
      integral_wienerIntegral (hc' 0) (hm' 0) (hL2' 0) ht (sqMoment_le hQ' 0 t) (hmean' 0) hk,
      zero_mul, sub_zero]
    have h := integral_mul_wienerIntegral (hc' 0) (hm' 0) (hL2' 0) ht (sqMoment_le hQ' 0 t) hk
      (hL2' 1 s)
    simp only [Pi.mul_apply]
    rw [show (fun ω => wienerIntegral (fun r => Real.exp (-(2 * γ) * (t - r)))
        (fun u => rotNoise ωh W 0 u ω) t * rotNoise ωh W 1 s ω) = fun ω => rotNoise ωh W 1 s ω *
        wienerIntegral (fun r => Real.exp (-(2 * γ) * (t - r))) (fun u => rotNoise ωh W 0 u ω) t
        from funext fun ω => mul_comm _ _, h,
      wienerIntegral_congr _ (w₂ := fun _ => 0) fun u hu => by
        rw [uIcc_of_le ht] at hu
        rw [hQ' 1 0 s u hs hu.1, Matrix.one_apply_ne (by decide), zero_mul]]
    simp [wienerIntegral]

end Moments

end powerlib.Stochastic.HopfPhase
