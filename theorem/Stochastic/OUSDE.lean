import theorem.Stochastic.LinearSDE
import theorem.Stochastic.LagLimit
import theorem.Stochastic.RotatingOU
import theorem.Criteria.Hurwitz2

/-! # Ornstein–Uhlenbeck SDEs of the periodogram method, path by path

The additive-noise SDEs of the periodogram method solved path by path and their exact
covariances: the scalar first-order lag `ẋ = −β(x − N(t)) + σ ẇ` (the OU input model (3-25) for
`N = 0`, the lag model (3-36) of the classifier), with its closed form, existence, uniqueness,
pathwise and mean-square limit `β → ∞`; the forced rotating OU process (3-30)/(3-31) with its
exact finite-time covariance and stationary autocovariance; and the decoupled vector OU input
(3-25).

Scope.
* Scalar lag: real `β, x₀, σ`, continuous deterministic input `N`, continuous noise path `w`;
  pathwise solution `lagSDESol β x₀ σ N w t = lagSol β x₀ N t + σ ∫₀ᵗ e^{−β(t−s)} dw(s)`
  (`LagLimit.lagSol`, pathwise Wiener integral). Moments for a noise process with
  `E[W(u)W(v)] = min(u, v)` (`u, v ≥ 0`) and mean zero (e.g. `Wiener.integral_mul_brownian` for
  Mathlib's pre-Brownian motion), deterministic `x₀` and `N`.
* Rotating OU: state `(x, y) ∈ ℝ²` (`x` = index `0`), drift `M = RotatingOU.rotMat γ ω₀`,
  forcing `F (cos Ωt, sin Ωt)` (`rotForcing`), noise `σ I` with two independent Brownian-type
  components, deterministic initial state; it is `LinearSDE.sdeSol` for these data. The forcing
  enters only the mean.
* OU input (3-25): `u̇ = −C u + σ ξ` with `C = diag(α)` and independent noise components.
* Only first and second moments are computed (the Gaussian law of the solutions is not stated).
* Generic mathematics of normal forms and filters; no power-system model.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.1, eqs. (3-25)
(`u̇ = −Cu + σξ`), (3-29) (`ẋ = −β(x − N)`, `β → ∞`), (3-30)–(3-35) (forced oscillation,
`x_ou = σ ∫₀ᵗ e^{−γ(t−s)} dB_s`), (3-36) (`ẋ = −β(x − Q) + σ₂ξ`) and Table 3-1.

Corrections and sharpenings.
* (3-29)/(3-36) with `β → ∞`: the report's Laplace argument is noise-free; here the noisy lag
  satisfies `x_β(t) → N(t)` for every continuous noise path and every `σ`
  (`tendsto_lagSDESol`), and `Var x_β(t) = σ²(1 − e^{−2βt})/(2β) → 0` (`tendsto_moments_lagSDESol`):
  the limit-cycle row `β = ∞` of Table 3-1 forces the noise term `σ₂` to vanish in the limit,
  whatever its intensity.
* (3-33): the report's `x_ou = σ ∫₀ᵗ e^{−γ(t−s)} dB_s` holds for one-time marginals only. The
  exact finite-time covariance of the `x`-component is `Cov(x(t), x(s)) = e^{−γ(t−s)}
  cos(ω₀(t−s)) σ²(1 − e^{−2γs})/(2γ)` (`covariance_rotOU_x`; at `s = t` the variance
  `σ²(1 − e^{−2γt})/(2γ)` of the report's expression), its stationary limit is
  `RotatingOU.rotOUAutocov` (`tendsto_covariance_rotOU`), and this is a scalar OU
  autocovariance only for `ω₀ = 0` (`RotatingOU.rotOUAutocov_not_ou`). These theorems about the
  pathwise solution replace the covariance-level model boundary of
  `theorem/Stochastic/RotatingOU.lean`.

Results.
* `lagSDESol`; `wienerIntegral_kernel` — `∫₀ᵗ e^{−β(t−s)} dw = ŵ(t) − β ∫₀ᵗ e^{−β(t−s)} ŵ(s) ds`,
  `ŵ = w − w(0)`; `lagSDESol_eq` — closed form `x = lagSol β x₀ (N − σŵ) + σŵ`.
* `lagSDESol_integral_eq` (existence), `eq_lagSDESol` (uniqueness among continuous solutions of
  `x(t) = x₀ + ∫₀ᵗ −β(x − N) + σ(w(t) − w(0))`), `tendsto_lagSDESol` (pathwise `β → ∞`).
* `integral_lagSDESol` (`E x(t) = lagSol β x₀ N t`), `covariance_lagSDESol`
  (`Cov(x(t), x(s)) = e^{−β(t−s)} σ²(1 − e^{−2βs})/(2β)`, `0 ≤ s ≤ t`),
  `tendsto_covariance_lagSDESol` (stationary autocovariance `OU.ouAutocov β σ τ`),
  `tendsto_moments_lagSDESol` (mean-square limit `β → ∞`).
* `rotForcing`, `exp_rotMat_mul_transpose` (`e^{uM} e^{uMᵀ} = e^{−2γu} I`), `gramian_rotMat`
  (`Σ(s) = σ²(1 − e^{−2γs})/(2γ) I`), `covariance_rotOU` (`Cov(x_i(t), x_j(s)) =
  σ²(1 − e^{−2γs})/(2γ) (e^{(t−s)M})_{ij}`), `covariance_rotOU_x`, `tendsto_covariance_rotOU`
  (`→ RotatingOU.rotOUAutocov γ ω₀ σ τ`, via `LinearSDE.tendsto_covariance_sdeSol`,
  `RotatingOU.rotMat_stationaryCov`, `RotatingOU.lagCov_rotMat` and
  `Criteria.isHurwitz_fin_two_of_iff`).
* `ouInput_eq_sdeSol` — the vector OU input (3-25) with `C = diag(α)` is `LinearSDE.sdeSol` with
  components `lagSDESol (α_i) (u₀_i) σ 0 w_i`; `covariance_ouInput` —
  `Cov(u_i(t), u_j(s)) = δ_ij e^{−α_i(t−s)} σ²(1 − e^{−2α_i s})/(2α_i)`.
-/

noncomputable section
namespace powerlib.Stochastic.OUSDE

open MeasureTheory ProbabilityTheory Set Filter Real
open powerlib.Stochastic.Wiener powerlib.Stochastic.LagLimit
open scoped Topology

/-! ## The scalar first-order lag with additive noise `ẋ = −β(x − N(t)) + σ ẇ` -/

/-- Pathwise solution of `ẋ = −β(x − N(t)) + σ ẇ`, `x(0) = x₀`:
`x(t) = e^{−βt}x₀ + β∫₀ᵗ e^{−β(t−s)} N(s) ds + σ ∫₀ᵗ e^{−β(t−s)} dw(s)`. -/
def lagSDESol (β x₀ σ : ℝ) (N w : ℝ → ℝ) (t : ℝ) : ℝ :=
  lagSol β x₀ N t + σ * wienerIntegral (fun s => exp (-β * (t - s))) w t

@[tmio T, powerlib_foundation] private theorem hasDerivAt_kernel (β t s : ℝ) :
    HasDerivAt (fun s => exp (-β * (t - s))) (β * exp (-β * (t - s))) s := by
  have h : HasDerivAt (fun s => -β * (t - s)) β s := by
    simpa using ((hasDerivAt_id s).const_sub t).const_mul (-β)
  simpa [mul_comm] using h.exp

@[tmio T, powerlib_foundation] private theorem contDiff_kernel (β t : ℝ) :
    ContDiff ℝ 1 (fun s => exp (-β * (t - s))) := by
  fun_prop

/-- The noise term of the lag: `∫₀ᵗ e^{−β(t−s)} dw = ŵ(t) − β ∫₀ᵗ e^{−β(t−s)} ŵ(s) ds`,
`ŵ = w − w(0)`. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_kernel (β : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (t : ℝ) :
    wienerIntegral (fun s => exp (-β * (t - s))) w t =
      (w t - w 0) - β * ∫ s in (0 : ℝ)..t, exp (-β * (t - s)) * (w s - w 0) := by
  have h := wienerIntegral_add_const (contDiff_kernel β t) (w := fun s => w s - w 0)
    (hw.sub continuous_const) (w 0) t
  have e : (fun s => (w s - w 0) + w 0) = w := funext fun s => by ring
  rw [e] at h
  rw [h]
  have hd : deriv (fun s => exp (-β * (t - s))) = fun s => β * exp (-β * (t - s)) :=
    funext fun s => (hasDerivAt_kernel β t s).deriv
  simp only [wienerIntegral, hd, smul_eq_mul, sub_self, mul_zero, exp_zero, mul_one, sub_zero,
    zero_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- **Closed form**: the noisy lag is the noiseless lag of the noise-corrected input,
`x = lagSol β x₀ (N − σŵ) + σŵ`. -/
@[tmio T, powerlib_foundation] theorem lagSDESol_eq (β x₀ σ : ℝ) {N : ℝ → ℝ} (hNc : Continuous N)
    {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    lagSDESol β x₀ σ N w t = lagSol β x₀ (fun s => N s - σ * (w s - w 0)) t + σ * (w t - w 0) := by
  have hN : ∀ N' : ℝ → ℝ, Continuous N' →
      IntervalIntegrable (fun s => exp (-β * (t - s)) * N' s) volume 0 t := fun N' hN' =>
    ((by fun_prop : Continuous fun s => exp (-β * (t - s))).mul hN').intervalIntegrable 0 t
  unfold lagSDESol lagSol
  rw [wienerIntegral_kernel β hw t]
  have e : ∀ s, exp (-β * (t - s)) * (N s - σ * (w s - w 0)) =
      exp (-β * (t - s)) * N s - σ * (exp (-β * (t - s)) * (w s - w 0)) := fun s => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub (hN N hNc) ((hN (fun s => w s - w 0) (hw.sub continuous_const)).const_mul σ),
    intervalIntegral.integral_const_mul]
  ring

@[tmio T, powerlib_foundation] private theorem continuous_corrected {σ : ℝ} {N w : ℝ → ℝ}
    (hN : Continuous N) (hw : Continuous w) : Continuous fun s => N s - σ * (w s - w 0) :=
  hN.sub (continuous_const.mul (hw.sub continuous_const))

/-- **Existence**: the pathwise solution solves the integral equation
`x(t) = x₀ + ∫₀ᵗ −β(x(s) − N(s)) ds + σ(w(t) − w(0))`. -/
@[tmio T, powerlib_foundation] theorem lagSDESol_integral_eq (β x₀ σ : ℝ) {N w : ℝ → ℝ}
    (hN : Continuous N) (hw : Continuous w) (t : ℝ) :
    lagSDESol β x₀ σ N w t =
      x₀ + (∫ s in (0 : ℝ)..t, -β * (lagSDESol β x₀ σ N w s - N s)) + σ * (w t - w 0) := by
  set M := fun s => N s - σ * (w s - w 0)
  have hM : Continuous M := continuous_corrected hN hw
  have hy := lagSol_hasDerivAt β x₀ hM
  have hyc : Continuous (lagSol β x₀ M) :=
    continuous_iff_continuousAt.2 fun s => (hy s).continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hy s)
    ((continuous_const.mul (hyc.sub hM)).intervalIntegrable 0 t)
  have hint : ∫ s in (0 : ℝ)..t, -β * (lagSDESol β x₀ σ N w s - N s) =
      ∫ s in (0 : ℝ)..t, -β * (lagSol β x₀ M s - M s) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [lagSDESol_eq β x₀ σ hN hw s, M]
    ring
  rw [hint, hFTC, lagSol_zero, lagSDESol_eq β x₀ σ hN hw t]
  ring

/-- **Uniqueness**: every continuous solution of the integral equation is the pathwise
solution. -/
@[tmio T, powerlib_foundation] theorem eq_lagSDESol {β x₀ σ : ℝ} {N w : ℝ → ℝ}
    (hN : Continuous N) (hw : Continuous w) {x : ℝ → ℝ} (hx : Continuous x)
    (h : ∀ t, x t = x₀ + (∫ s in (0 : ℝ)..t, -β * (x s - N s)) + σ * (w t - w 0)) :
    x = lagSDESol β x₀ σ N w := by
  set M := fun s => N s - σ * (w s - w 0)
  have hM : Continuous M := continuous_corrected hN hw
  set y : ℝ → ℝ := fun t => x t - σ * (w t - w 0)
  have hyint : y = fun t => x₀ + ∫ s in (0 : ℝ)..t, -β * (x s - N s) :=
    funext fun t => by simp only [y]; rw [h t]; ring
  have hy : ∀ t, HasDerivAt y (-β * (y t - M t)) t := by
    intro t
    have hc : Continuous fun s => -β * (x s - N s) := continuous_const.mul (hx.sub hN)
    have hd := ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add x₀
    rw [← hyint] at hd
    refine hd.congr_deriv ?_
    simp only [y, M]
    ring
  have hy0 : y 0 = x₀ := by rw [hyint]; simp
  have hyl := lagSol_unique hM hy hy0
  funext t
  rw [lagSDESol_eq β x₀ σ hN hw t, ← hyl]
  simp only [y]
  ring

/-- **The fast lag tracks its input, with noise** (TR-110 (3-29), (3-36) as `β → ∞`): for every
continuous noise path, every `t > 0` and every `σ`, `x_β(t) → N(t)` as `β → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_lagSDESol {t : ℝ} (ht : 0 < t) (x₀ σ : ℝ)
    {N w : ℝ → ℝ} (hN : Continuous N) (hw : Continuous w) :
    Tendsto (fun β => lagSDESol β x₀ σ N w t) atTop (𝓝 (N t)) := by
  have h := (tendsto_lagSol ht x₀ (continuous_corrected (σ := σ) hN hw)).add_const
    (σ * (w t - w 0))
  simp only [sub_add_cancel] at h
  exact h.congr fun β => (lagSDESol_eq β x₀ σ hN hw t).symm

/-- `∫₀ˢ e^{−β(t−r)} e^{−β(s−r)} dr = e^{−β(t−s)} (1 − e^{−2βs})/(2β)` for `β ≠ 0`. -/
@[tmio T, powerlib_foundation] private theorem integral_kernel_mul {β : ℝ} (hβ : β ≠ 0)
    (t s : ℝ) :
    ∫ r in (0 : ℝ)..s, exp (-β * (t - r)) * exp (-β * (s - r)) =
      exp (-β * (t - s)) * ((1 - exp (-2 * β * s)) / (2 * β)) := by
  have hd : ∀ r ∈ uIcc (0 : ℝ) s, HasDerivAt
      (fun r => exp (-β * (t - r)) * exp (-β * (s - r)) / (2 * β))
      (exp (-β * (t - r)) * exp (-β * (s - r))) r := by
    intro r _
    have h := ((hasDerivAt_kernel β t r).mul (hasDerivAt_kernel β s r)).div_const (2 * β)
    refine h.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun r => exp (-β * (t - r)) * exp (-β * (s - r))).intervalIntegrable
      0 s)]
  have e1 : exp (-β * (s - s)) = 1 := by simp
  have e2 : exp (-β * (t - 0)) * exp (-β * (s - 0)) = exp (-β * (t - s)) * exp (-2 * β * s) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  rw [e1, e2]
  field_simp

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- A single Brownian-type process as a one-component family with `Q = 1`. -/
@[tmio T, powerlib_foundation] private theorem unitCov
    (hBM : ∀ u v, 0 ≤ u → 0 ≤ v → ∫ ω, W u ω * W v ω ∂P = min u v) :
    ∀ (k l : Unit) (u v : ℝ), 0 ≤ u → 0 ≤ v →
      ∫ ω, (fun _ : Unit => W) k u ω * (fun _ : Unit => W) l v ω ∂P =
        (1 : Matrix Unit Unit ℝ) k l * min u v := by
  intro k l u v hu hv
  simp [hBM u v hu hv]

/-- **Mean of the noisy lag** (centred noise): `E x(t) = lagSol β x₀ N t`. -/
@[tmio T, powerlib_foundation] theorem integral_lagSDESol (β x₀ σ : ℝ) (N : ℝ → ℝ)
    (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P)
    (hBM : ∀ u v, 0 ≤ u → 0 ≤ v → ∫ ω, W u ω * W v ω ∂P = min u v)
    (hmean : ∀ u, 0 ≤ u → ∫ ω, W u ω ∂P = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, lagSDESol β x₀ σ N (fun u => W u ω) t ∂P = lagSol β x₀ N t := by
  have hbd := sqMoment_le (W := fun _ : Unit => W) (unitCov hBM) () t
  have hI := memLp_wienerIntegral hc hm hL2 ht hbd _ (contDiff_kernel β t)
  simp only [lagSDESol]
  rw [integral_add (integrable_const _) ((hI.integrable one_le_two).const_mul σ),
    integral_const_mul, integral_wienerIntegral hc hm hL2 ht hbd hmean (contDiff_kernel β t)]
  simp

/-- **Covariance of the noisy lag** under Brownian-type noise (`E[W(u)W(v)] = min(u, v)`): for
`0 ≤ s ≤ t` and `β ≠ 0`, `Cov(x(t), x(s)) = e^{−β(t−s)} σ²(1 − e^{−2βs})/(2β)` (`OU.ouVar`). -/
@[tmio T, powerlib_foundation] theorem covariance_lagSDESol {β : ℝ} (hβ : β ≠ 0) (x₀ σ : ℝ)
    (N : ℝ → ℝ) (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P)
    (hBM : ∀ u v, 0 ≤ u → 0 ≤ v → ∫ ω, W u ω * W v ω ∂P = min u v)
    (hmean : ∀ u, 0 ≤ u → ∫ ω, W u ω ∂P = 0) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    cov[fun ω => lagSDESol β x₀ σ N (fun u => W u ω) t,
      fun ω => lagSDESol β x₀ σ N (fun u => W u ω) s; P] =
      exp (-β * (t - s)) * OU.ouVar β σ s := by
  have ht : 0 ≤ t := hs.trans hst
  have hIt := memLp_wienerIntegral hc hm hL2 ht
    (sqMoment_le (W := fun _ : Unit => W) (unitCov hBM) () t) _ (contDiff_kernel β t)
  have hIs := memLp_wienerIntegral hc hm hL2 hs
    (sqMoment_le (W := fun _ : Unit => W) (unitCov hBM) () s) _ (contDiff_kernel β s)
  simp only [lagSDESol]
  rw [covariance_const_add_left ((hIt.integrable one_le_two).const_mul σ),
    covariance_const_add_right ((hIs.integrable one_le_two).const_mul σ),
    covariance_const_mul_left, covariance_const_mul_right,
    covariance_wienerIntegral (W := fun _ : Unit => W) (fun _ => hc) (fun _ => hm) (fun _ => hL2)
      (unitCov hBM) (fun _ => hmean) (contDiff_kernel β t) (contDiff_kernel β s) () () ht hs,
    min_eq_right hst, integral_kernel_mul hβ]
  simp only [Matrix.one_apply_eq, one_mul, OU.ouVar]
  field_simp

/-- **Stationary autocovariance of the noisy lag**: for `β > 0` and every lag `τ ≥ 0`,
`Cov(x(s + τ), x(s)) → e^{−βτ} σ²/(2β)` (`OU.ouAutocov`) as `s → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_covariance_lagSDESol {β : ℝ} (hβ : 0 < β)
    (x₀ σ : ℝ) (N : ℝ → ℝ) (hc : ∀ ω, Continuous fun u => W u ω) (hm : ∀ u, Measurable (W u))
    (hL2 : ∀ u, MemLp (W u) 2 P)
    (hBM : ∀ u v, 0 ≤ u → 0 ≤ v → ∫ ω, W u ω * W v ω ∂P = min u v)
    (hmean : ∀ u, 0 ≤ u → ∫ ω, W u ω ∂P = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun s => cov[fun ω => lagSDESol β x₀ σ N (fun u => W u ω) (s + τ),
      fun ω => lagSDESol β x₀ σ N (fun u => W u ω) s; P]) atTop (𝓝 (OU.ouAutocov β σ τ)) := by
  have h := (OU.ouVar_tendsto hβ σ).const_mul (exp (-β * τ))
  rw [show OU.ouAutocov β σ τ = exp (-β * τ) * OU.ouStatVar β σ by
    simp [OU.ouAutocov, abs_of_nonneg hτ]]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with s hs
  rw [covariance_lagSDESol hβ.ne' x₀ σ N hc hm hL2 hBM hmean hs (by linarith), add_sub_cancel_left]

/-- **The fast noisy lag converges in mean square**: for `t > 0`, `E x_β(t) → N(t)` and
`Var x_β(t) = σ²(1 − e^{−2βt})/(2β) → 0` as `β → ∞`, whatever the noise intensity `σ`. -/
@[tmio T, powerlib_foundation] theorem tendsto_moments_lagSDESol {t : ℝ} (ht : 0 < t)
    (x₀ σ : ℝ) {N : ℝ → ℝ} (hN : Continuous N) (hc : ∀ ω, Continuous fun u => W u ω)
    (hm : ∀ u, Measurable (W u)) (hL2 : ∀ u, MemLp (W u) 2 P)
    (hBM : ∀ u v, 0 ≤ u → 0 ≤ v → ∫ ω, W u ω * W v ω ∂P = min u v)
    (hmean : ∀ u, 0 ≤ u → ∫ ω, W u ω ∂P = 0) :
    Tendsto (fun β => ∫ ω, lagSDESol β x₀ σ N (fun u => W u ω) t ∂P) atTop (𝓝 (N t)) ∧
    Tendsto (fun β => Var[fun ω => lagSDESol β x₀ σ N (fun u => W u ω) t; P]) atTop (𝓝 0) := by
  refine ⟨(tendsto_lagSol ht x₀ hN).congr fun β =>
    (integral_lagSDESol β x₀ σ N hc hm hL2 hBM hmean ht.le).symm, ?_⟩
  have hvar : ∀ β, 0 < β → Var[fun ω => lagSDESol β x₀ σ N (fun u => W u ω) t; P] =
      OU.ouVar β σ t := by
    intro β hβ
    have hI := memLp_wienerIntegral hc hm hL2 ht.le
      (sqMoment_le (W := fun _ : Unit => W) (unitCov hBM) () t) _ (contDiff_kernel β t)
    have hX : AEMeasurable (fun ω => lagSDESol β x₀ σ N (fun u => W u ω) t) P := by
      simp only [lagSDESol]
      exact aemeasurable_const.add (hI.aemeasurable.const_mul σ)
    rw [← covariance_self hX, covariance_lagSDESol hβ.ne' x₀ σ N hc hm hL2 hBM hmean ht.le le_rfl]
    simp
  have hbound : ∀ β, 0 < β → 0 ≤ OU.ouVar β σ t ∧ OU.ouVar β σ t ≤ σ ^ 2 / (2 * β) := by
    intro β hβ
    have h1 : 0 ≤ 1 - exp (-2 * β * t) := by
      have : exp (-2 * β * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
      linarith
    have h2 : 1 - exp (-2 * β * t) ≤ 1 := by linarith [exp_pos (-2 * β * t)]
    have h3 : 0 ≤ σ ^ 2 / (2 * β) := by positivity
    exact ⟨mul_nonneg h3 h1, by simpa [OU.ouVar] using mul_le_of_le_one_right h3 h2⟩
  have hlim : Tendsto (fun β : ℝ => σ ^ 2 / (2 * β)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop two_pos)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    rw [hvar β hβ]; exact (hbound β hβ).1
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    rw [hvar β hβ]; exact (hbound β hβ).2

end Moments

/-! ## The rotating Ornstein–Uhlenbeck process of TR-110 (3-30)/(3-31) -/

section Rotating

open Matrix NormedSpace powerlib.Stochastic.LinearSDE powerlib.Stochastic.RotatingOU
open scoped Matrix.Norms.Frobenius

attribute [local instance] powerlib.LinearAlgebra.frobeniusENormedAddMonoid

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The periodic forcing `F (cos Ωt, sin Ωt)` of (3-31). -/
def rotForcing (F Ω : ℝ) (t : ℝ) : ℝ² := WithLp.toLp 2 ![F * Real.cos (Ω * t), F * Real.sin (Ω * t)]

@[tmio T, powerlib_foundation] private theorem noiseCov_smul_one (σ : ℝ) :
    (σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * 1 * (σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ =
      (σ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.mul_one, Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm,
    Matrix.mul_one, sq]

/-- `e^{uM} e^{uMᵀ} = e^{−2γu} I` for the rotating drift `M`. -/
@[tmio T, powerlib_foundation] theorem exp_rotMat_mul_transpose (γ ω₀ u : ℝ) :
    exp (u • rotMat γ ω₀) * exp (u • (rotMat γ ω₀)ᵀ) =
      Real.exp (-2 * γ * u) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [← Matrix.transpose_smul, Matrix.exp_transpose, exp_rotMat]
  have he : Real.exp (-(2 * γ * u)) = Real.exp (-(γ * u)) * Real.exp (-(γ * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsc := Real.sin_sq_add_cos_sq (ω₀ * u)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
      | ring1
      | (rw [he]; linear_combination (Real.exp (-(γ * u)) * Real.exp (-(γ * u))) * hsc)

/-- The Gramian of the rotating drift with isotropic noise: `Σ(s) = σ²(1 − e^{−2γs})/(2γ) I`. -/
@[tmio T, powerlib_foundation] theorem gramian_rotMat {γ : ℝ} (hγ : γ ≠ 0) (ω₀ σ s : ℝ) :
    gramian (rotMat γ ω₀) ((σ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) s =
      OU.ouVar γ σ s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have e : ∀ u : ℝ, exp (u • rotMat γ ω₀) * ((σ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      exp (u • (rotMat γ ω₀)ᵀ) = (σ ^ 2 * Real.exp (-2 * γ * u)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro u
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, exp_rotMat_mul_transpose, smul_smul]
  have hd : ∀ u ∈ uIcc (0 : ℝ) s, HasDerivAt (fun u => -(Real.exp (-2 * γ * u)) / (2 * γ))
      (Real.exp (-2 * γ * u)) u := by
    intro u _
    have h := (((hasDerivAt_id' u).const_mul (-2 * γ)).exp).neg.div_const (2 * γ)
    refine h.congr_deriv ?_
    field_simp
  have hI : ∫ u in (0 : ℝ)..s, Real.exp (-2 * γ * u) = (1 - Real.exp (-2 * γ * s)) / (2 * γ) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun u => Real.exp (-2 * γ * u)).intervalIntegrable 0 s)]
    simp only [mul_zero, Real.exp_zero]
    ring
  simp only [gramian, e]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul, hI]
  congr 1
  simp only [OU.ouVar]
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : Fin 2 → ℝ → Ω → ℝ}

/-- **Covariance of the forced rotating OU process** (TR-110 (3-30)/(3-31), exact). For the
pathwise solution of `dx = (M x + F(cos Ωt, sin Ωt)) dt + σ dw` with `M = rotMat γ ω₀` and
independent Brownian-type noise components, and `0 ≤ s ≤ t`:
`Cov(x_i(t), x_j(s)) = σ²(1 − e^{−2γs})/(2γ) · (e^{(t−s)M})_{ij}`. The forcing only shifts the
mean. -/
@[tmio T, powerlib_foundation] theorem covariance_rotOU {γ : ℝ} (hγ : γ ≠ 0) (ω₀ σ F Ωf : ℝ)
    (x₀ : ℝ²) (hc : ∀ k ω, Continuous fun u => W k u ω) (hm : ∀ k u, Measurable (W k u))
    (hL2 : ∀ k u, MemLp (W k u) 2 P)
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, W k u ω * W l v ω ∂P = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (i j : Fin 2) :
    cov[fun ω => sdeSol (rotMat γ ω₀) (rotForcing F Ωf) (σ • 1) x₀ (fun k u => W k u ω) t i,
      fun ω => sdeSol (rotMat γ ω₀) (rotForcing F Ωf) (σ • 1) x₀ (fun k u => W k u ω) s j; P] =
      OU.ouVar γ σ s * exp ((t - s) • rotMat γ ω₀) i j := by
  rw [covariance_sdeSol_of_le _ _ _ x₀ hc hm hL2 hQ hmean hs hst i j, noiseCov_smul_one,
    gramian_rotMat hγ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]

/-- The `x`-component autocovariance at finite time:
`Cov(x(t), x(s)) = e^{−γ(t−s)} cos(ω₀(t−s)) σ²(1 − e^{−2γs})/(2γ)` for `0 ≤ s ≤ t`; it is not of
the scalar OU form `c e^{−θ(t−s)}` unless `ω₀ = 0` (`RotatingOU.rotOUAutocov_not_ou`). -/
@[tmio T, powerlib_foundation] theorem covariance_rotOU_x {γ : ℝ} (hγ : γ ≠ 0) (ω₀ σ F Ωf : ℝ)
    (x₀ : ℝ²) (hc : ∀ k ω, Continuous fun u => W k u ω) (hm : ∀ k u, Measurable (W k u))
    (hL2 : ∀ k u, MemLp (W k u) 2 P)
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, W k u ω * W l v ω ∂P = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    cov[fun ω => sdeSol (rotMat γ ω₀) (rotForcing F Ωf) (σ • 1) x₀ (fun k u => W k u ω) t 0,
      fun ω => sdeSol (rotMat γ ω₀) (rotForcing F Ωf) (σ • 1) x₀ (fun k u => W k u ω) s 0; P] =
      Real.exp (-γ * (t - s)) * Real.cos (ω₀ * (t - s)) * OU.ouVar γ σ s := by
  rw [covariance_rotOU hγ ω₀ σ F Ωf x₀ hc hm hL2 hQ hmean hs hst 0 0, exp_rotMat]
  simp
  ring

/-- **Stationary autocovariance of the rotating OU process** (replaces the model boundary of
`RotatingOU`): for `γ > 0` and every lag `τ ≥ 0`, `Cov(x(s + τ), x(s)) → σ²/(2γ) e^{−γτ}
cos(ω₀τ)` (`RotatingOU.rotOUAutocov`) as `s → ∞`, obtained from the general stationary theorem
with the Hurwitz drift `M` and the Lyapunov solution `Σ∞ = σ²/(2γ) I`
(`RotatingOU.rotMat_stationaryCov`, `RotatingOU.lagCov_rotMat`). -/
@[tmio T, powerlib_foundation] theorem tendsto_covariance_rotOU {γ : ℝ} (hγ : 0 < γ)
    (ω₀ σ F Ωf : ℝ) (x₀ : ℝ²) (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P)
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, W k u ω * W l v ω ∂P = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun s => cov[fun ω => sdeSol (rotMat γ ω₀) (rotForcing F Ωf) (σ • 1) x₀
        (fun k u => W k u ω) (s + τ) 0,
      fun ω => sdeSol (rotMat γ ω₀) (rotForcing F Ωf) (σ • 1) x₀ (fun k u => W k u ω) s 0; P])
      atTop (𝓝 (rotOUAutocov γ ω₀ σ τ)) := by
  have hA : LinearSystems.IsHurwitz (rotMat γ ω₀) :=
    (Criteria.isHurwitz_fin_two_of_iff (-γ) (-ω₀) ω₀ (-γ)).2 ⟨by linarith, by nlinarith [sq_nonneg ω₀, mul_pos hγ hγ]⟩
  have hP : Lyapunov.SolvesCovLyapunov (rotMat γ ω₀) ((σ ^ 2 / (2 * γ)) • 1)
      ((σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * 1 * (σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ) := by
    rw [noiseCov_smul_one]
    exact (rotMat_stationaryCov hγ.ne' ω₀ σ _).2 rfl
  have h := tendsto_covariance_sdeSol hA (rotForcing F Ωf) (σ • 1) x₀ hc hm hL2 hQ hmean hP hτ 0 0
  rwa [lagCov_rotMat γ ω₀ σ hτ] at h

end Rotating

/-! ## The vector OU input model of TR-110 (3-25) -/

section OUInput

open Matrix NormedSpace powerlib.Stochastic.LinearSDE

/-- **TR-110 (3-25) is decoupled.** For `C = diag(α)` and noise intensity `σ` the pathwise
solution of `u̇ = −C u + σ ξ` (`LinearSDE.sdeSol` with `A = −diag(α)`, `B = σ I`) has the noisy
lags `lagSDESol (α_i) (u₀_i) σ 0 w_i` as components. -/
@[tmio T, powerlib_foundation] theorem ouInput_eq_sdeSol {m : ℕ} (α : Fin m → ℝ) (σ : ℝ)
    (u₀ : Fin m → ℝ) {w : Fin m → ℝ → ℝ} (hw : ∀ k, Continuous (w k)) :
    (fun t => WithLp.toLp 2 (fun i => lagSDESol (α i) (u₀ i) σ (fun _ => 0) (w i) t)) =
      sdeSol (-(diagonal α)) (fun _ => 0) (σ • 1) (WithLp.toLp 2 u₀) w := by
  set x : ℝ → EuclideanSpace ℝ (Fin m) :=
    fun t => WithLp.toLp 2 (fun i => lagSDESol (α i) (u₀ i) σ (fun _ => 0) (w i) t)
  have hcomp : ∀ i, Continuous fun t => lagSDESol (α i) (u₀ i) σ (fun _ => 0) (w i) t := by
    intro i
    have h : (fun t => lagSDESol (α i) (u₀ i) σ (fun _ => 0) (w i) t) = fun t =>
        lagSol (α i) (u₀ i) (fun s => 0 - σ * (w i s - w i 0)) t + σ * (w i t - w i 0) :=
      funext (lagSDESol_eq (α i) (u₀ i) σ continuous_const (hw i))
    rw [h]
    exact (continuous_iff_continuousAt.2 fun t => (lagSol_hasDerivAt (α i) (u₀ i)
      (continuous_corrected continuous_const (hw i)) t).continuousAt).add
      (continuous_const.mul ((hw i).sub continuous_const))
  have hx : Continuous x := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => hcomp i)
  refine eq_sdeSol _ continuous_const _ _ hw hx fun t => ?_
  ext i
  have hop : ∀ s, (Linear.op (-(diagonal α)) (x s) + 0) i =
      -α i * (lagSDESol (α i) (u₀ i) σ (fun _ => 0) (w i) s - 0) := by
    intro s
    simp [x, Linear.op, Matrix.mulVec_diagonal]
  have hint : IntervalIntegrable (fun s => Linear.op (-(diagonal α)) (x s) + 0) volume 0 t :=
    (((Linear.op _).continuous.comp hx).add continuous_const).intervalIntegrable 0 t
  have hproj := ContinuousLinearMap.intervalIntegral_comp_comm (EuclideanSpace.proj i) hint
  simp only [PiLp.proj_apply] at hproj
  rw [PiLp.add_apply, PiLp.add_apply, ← hproj]
  simp_rw [hop]
  change lagSDESol (α i) (u₀ i) σ (fun _ => 0) (w i) t = _
  conv_lhs => rw [lagSDESol_integral_eq (α i) (u₀ i) σ continuous_const (hw i) t]
  simp [noiseIncr, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Covariance of the OU input model (3-25)** with independent Brownian-type noises: for
`α_i ≠ 0` and `0 ≤ s ≤ t`, `Cov(u_i(t), u_j(s)) = δ_ij e^{−α_i(t−s)} σ²(1 − e^{−2α_i s})/(2α_i)`;
for `α_i > 0` the stationary autocovariance is `OU.ouAutocov (α_i) σ`
(`tendsto_covariance_lagSDESol`). -/
@[tmio T, powerlib_foundation] theorem covariance_ouInput {m : ℕ} {α : Fin m → ℝ}
    (hα : ∀ i, α i ≠ 0) (σ : ℝ) (u₀ : Fin m → ℝ) {W : Fin m → ℝ → Ω → ℝ}
    (hc : ∀ k ω, Continuous fun u => W k u ω) (hm : ∀ k u, Measurable (W k u))
    (hL2 : ∀ k u, MemLp (W k u) 2 P)
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v →
      ∫ ω, W k u ω * W l v ω ∂P = (1 : Matrix (Fin m) (Fin m) ℝ) k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (i j : Fin m) :
    cov[fun ω => lagSDESol (α i) (u₀ i) σ (fun _ => 0) (fun u => W i u ω) t,
      fun ω => lagSDESol (α j) (u₀ j) σ (fun _ => 0) (fun u => W j u ω) s; P] =
      if i = j then Real.exp (-α i * (t - s)) * OU.ouVar (α i) σ s else 0 := by
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    exact covariance_lagSDESol (hα i) (u₀ i) σ _ (hc i) (hm i) (hL2 i)
      (fun u v hu hv => by rw [hQ i i u v hu hv, Matrix.one_apply_eq, one_mul])
      (hmean i) hs hst
  · simp only [hij, ↓reduceIte]
    have ht : 0 ≤ t := hs.trans hst
    have hIt := memLp_wienerIntegral (hc i) (hm i) (hL2 i) ht (sqMoment_le hQ i t) _
      (contDiff_kernel (α i) t)
    have hIs := memLp_wienerIntegral (hc j) (hm j) (hL2 j) hs (sqMoment_le hQ j s) _
      (contDiff_kernel (α j) s)
    simp only [lagSDESol]
    rw [covariance_const_add_left ((hIt.integrable one_le_two).const_mul σ),
      covariance_const_add_right ((hIs.integrable one_le_two).const_mul σ),
      covariance_const_mul_left, covariance_const_mul_right,
      covariance_wienerIntegral hc hm hL2 hQ hmean (contDiff_kernel (α i) t)
        (contDiff_kernel (α j) s) i j ht hs, Matrix.one_apply_ne hij]
    ring

end OUInput

end powerlib.Stochastic.OUSDE
