import theorem.Stochastic.WienerIntegral
import theorem.LTI.BoundedForcing
import theorem.LTI.SampledFlow
import theorem.Stochastic.LyapunovCovariance

/-! # Linear stochastic differential equations with additive noise, path by path

The linear SDE `dx = (A x + f(t)) dt + B dw` with additive noise, solved without Itô calculus.
Its pathwise solution `x(t) = e^{tA}x₀ + ∫₀ᵗ e^{(t−s)A} f(s) ds + Σ_k ∫₀ᵗ e^{(t−s)A} b_k dw_k(s)`
(pathwise Wiener integrals) is the unique continuous solution of the integral equation
`x(t) = x₀ + ∫₀ᵗ (A x(s) + f(s)) ds + B(w(t) − w(0))` for every continuous noise path, which is
what the SDE means for additive noise. Under a Brownian law its mean is the deterministic
solution, its covariance is `Cov(x(t), x(s)) = e^{(t−s)A} Σ(s)` (`s ≤ t`) with the Gramian
`Σ(s) = ∫₀ˢ e^{uA} B Q Bᵀ e^{uAᵀ} du`, and for Hurwitz `A` the autocovariance at lag `τ` tends to
`e^{τA} Σ∞` with `Σ∞` the solution of the covariance Lyapunov equation. A linear measurement with
additive measurement noise adds the noise covariance.

Scope.
* State `ℝⁿ = EuclideanSpace ℝ (Fin n)`, constant real `A` acting as `Linear.op A` (operator
  exponential `e^{tA} = exp(t • Linear.op A)`, as in `theorem/LTI/BoundedForcing.lean`), noise
  matrix `B : Matrix (Fin n) ι ℝ` with columns `b_k` (`col`), continuous deterministic input `f`,
  deterministic initial state `x₀`, continuous time `t ∈ ℝ`. The noise paths `w_k : ℝ → ℝ` are
  arbitrary continuous functions in the pathwise statements (deterministic analysis, sample path
  by sample path).
* Moments: noise processes `W_k` as in `theorem/Stochastic/WienerIntegral.lean` (continuous paths,
  measurable square-integrable marginals, `E[W_k(u) W_l(v)] = Q_kl min(u, v)` for `u, v ≥ 0`, mean
  zero); independent standard Brownian components are `Q = 1` (`sdeSol_brownian`,
  `tendsto_covariance_sdeSol_brownian`). Random initial states are not treated; only first and
  second moments are computed (the Gaussian law of the solution is not stated).
* Matrix integrals and limits use the Frobenius norm (`Matrix.Norms.Frobenius`, as in
  `theorem/Stochastic/LyapunovCovariance.lean`, whose Gramian limit `tendsto_integral_gramian` and
  Lyapunov existence `exists_stationaryCov` are reused).
* These theorems replace the model boundary of `theorem/Stochastic/LyapunovCovariance.lean`
  ("that `P(t)` is the covariance of the Itô solution of `dX = AX dt + B dW` is not proved") for
  additive noise: the Gramian `Σ(s)` is the covariance of the pathwise solution and `Σ∞` its
  stationary limit.
* Measurement equation (2-1): `y = C x + μ` with measurement noise `μ` uncorrelated with the
  driving noise. The feedthrough `D e` of a white-noise input has no pointwise value and is not
  treated (`D = 0`).
* Generic mathematics; no model family.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.1, eq. (2-1)
(`ẋ = Ax + B_e e + B_u u`, `y = Cx + De + μ`), eqs. (2-12)/(2-14) (ambient inputs
`Σ_k b_{e,k} e_k`, transient + ambient + forced responses) and §3.6.1, eqs. (3-25), (3-30)–(3-33)
(OU inputs, rotating OU, `x_ou = ∫₀ᵗ e^{(t−s)M} σ dB_s`); work-sync theory/T-sde-systems.md §1.8.2
and §1.12.2 (stationary covariance `A P∞ + P∞ Aᵀ + B Bᵀ = 0`, Gramian).

Results.
* `col`, `detSol` (the deterministic solution `e^{tA}x₀ + ∫₀ᵗ e^{(t−s)A} f(s) ds`), `sdeSol` (the
  pathwise solution), `noiseIncr` (`B(w(t) − w(0))`), `noiseIncr_eq_sum`, `continuous_noiseIncr`.
* `wienerIntegral_exp_sub` — `∫₀ᵗ e^{(t−s)A} v dw = (w(t) − w(0)) v + ∫₀ᵗ (w(s) − w(0))
  e^{(t−s)A} A v ds`; `sdeSol_eq` — closed form `x(t) = e^{tA}x₀ + ∫₀ᵗ e^{(t−s)A}(f(s) +
  A B(w(s) − w(0))) ds + B(w(t) − w(0))`; `continuous_sdeSol`.
* `sdeSol_integral_eq` (**existence**) and `eq_sdeSol` (**uniqueness**: every continuous solution
  of the integral equation is `sdeSol`, from `LTI.variation_of_constants` applied to
  `x − B(w − w(0))`).
* `eq_sdeSol_of_hasDerivAt` — for `C¹` noise paths `ẇ_k = e_k` the solution of the ODE
  `ẋ = A x + Σ_k e_k b_k + g b_f` (TR-110 (2-12)) is `sdeSol`, so the definition extends the
  transient + ambient + forced decomposition (2-14) (`LTI.three_components`).
* `exp_col_apply`, `sdeSol_apply` — components `x_i(t) = x̄_i(t) + Σ_k ∫₀ᵗ (e^{(t−s)A}B)_{ik}
  dw_k(s)`.
* `integral_sdeSol` — `E x(t) = detSol`; `covariance_sdeSol` —
  `Cov(x_i(t), x_j(s)) = ∫₀^{min(t,s)} (e^{(t−r)A} B Q Bᵀ e^{(s−r)Aᵀ})_{ij} dr`.
* `gramian` (`Σ(s)`), `covariance_sdeSol_of_le` — `Cov(x_i(t), x_j(s)) = (e^{(t−s)A} Σ(s))_{ij}`
  for `0 ≤ s ≤ t`; `tendsto_covariance_sdeSol` — for Hurwitz `A` and `A Σ∞ + Σ∞ Aᵀ + B Q Bᵀ = 0`,
  `Cov(x_i(s + τ), x_j(s)) → (e^{τA} Σ∞)_{ij}` (the stationary autocovariance).
* `sdeSol_brownian`, `tendsto_covariance_sdeSol_brownian` — the same for independent Brownian
  components: mean, covariance `e^{(t−s)A} Σ(s)` with `Σ(s) = ∫₀ˢ e^{uA}BBᵀe^{uAᵀ} du`, and, for
  Hurwitz `A`, a positive semidefinite `Σ∞` solving `A Σ∞ + Σ∞ Aᵀ + B Bᵀ = 0` with
  `Cov(x(s + τ), x(s)) → e^{τA} Σ∞`.
* `covariance_measurement` — `Cov((CX + M)_i, (CX' + M')_j) = (C K Cᵀ)_{ij} + Cov(M_i, M'_j)` for
  measurement noise uncorrelated with the state; `covariance_output_sdeSol` — for (2-1),
  `Cov(y_i(t), y_j(s)) = (C e^{(t−s)A} Σ(s) Cᵀ)_{ij} + Cov(μ_i(t), μ_j(s))`.
-/

noncomputable section
namespace powerlib.Stochastic.LinearSDE

open MeasureTheory ProbabilityTheory Set Filter Matrix NormedSpace
open powerlib.Stochastic.Wiener
open scoped Topology

variable {n : ℕ} {ι : Type*} [Fintype ι]

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The `k`-th column of the noise matrix `B` as a state vector. -/
abbrev col (B : Matrix (Fin n) ι ℝ) (k : ι) : ℝⁿ := WithLp.toLp 2 (fun i => B i k)

/-- The deterministic part `e^{tA} x₀ + ∫₀ᵗ e^{(t−s)A} f(s) ds`. -/
def detSol (A : Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝⁿ) (x₀ : ℝⁿ) (t : ℝ) : ℝⁿ :=
  exp (t • Linear.op A) x₀ + ∫ s in (0 : ℝ)..t, exp ((t - s) • Linear.op A) (f s)

/-- **Pathwise solution** of the additive-noise linear SDE `dx = (A x + f(t)) dt + B dw` driven by
the noise paths `w_k` (`k ∈ ι`): `x(t) = e^{tA}x₀ + ∫₀ᵗ e^{(t−s)A} f(s) ds +
Σ_k ∫₀ᵗ e^{(t−s)A} b_k dw_k(s)` with the columns `b_k` of `B` and the pathwise Wiener integral. -/
def sdeSol (A : Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ)
    (w : ι → ℝ → ℝ) (t : ℝ) : ℝⁿ :=
  detSol A f x₀ t + ∑ k, wienerIntegral (fun s => exp ((t - s) • Linear.op A) (col B k)) (w k) t

/-- The noise input `B (w(t) − w(0))`. -/
def noiseIncr (B : Matrix (Fin n) ι ℝ) (w : ι → ℝ → ℝ) (t : ℝ) : ℝⁿ :=
  WithLp.toLp 2 (B *ᵥ fun k => w k t - w k 0)

@[tmio T, powerlib_foundation] theorem noiseIncr_eq_sum (B : Matrix (Fin n) ι ℝ)
    (w : ι → ℝ → ℝ) (t : ℝ) :
    noiseIncr B w t = ∑ k, (w k t - w k 0) • col B k := by
  ext i
  simp [noiseIncr, Matrix.mulVec, dotProduct, mul_comm]

@[tmio T, powerlib_foundation] theorem continuous_noiseIncr (B : Matrix (Fin n) ι ℝ)
    {w : ι → ℝ → ℝ} (hw : ∀ k, Continuous (w k)) : Continuous (noiseIncr B w) := by
  have : noiseIncr B w = fun t => ∑ k, (w k t - w k 0) • col B k :=
    funext (noiseIncr_eq_sum B w)
  rw [this]
  exact continuous_finsetSum _ fun k _ => ((hw k).sub continuous_const).smul continuous_const

/-! ## The integrand `s ↦ e^{(t−s)A} v` -/

@[tmio T, powerlib_foundation] private theorem hasDerivAt_exp_sub (A : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (v : ℝⁿ) (s : ℝ) :
    HasDerivAt (fun s => exp ((t - s) • Linear.op A) v)
      (-(exp ((t - s) • Linear.op A) (Linear.op A v))) s := by
  have h := (LTI.hasDerivAt_exp_apply A v (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
  refine h.congr_deriv ?_
  rw [neg_one_smul, LTI.exp_smul_apply_comm]

@[tmio T, powerlib_foundation] private theorem contDiff_exp_sub (A : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (v : ℝⁿ) : ContDiff ℝ 1 (fun s => exp ((t - s) • Linear.op A) v) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_exp_sub A t v s).differentiableAt, ?_⟩
  have hd : deriv (fun s => exp ((t - s) • Linear.op A) v) =
      fun s => -(exp ((t - s) • Linear.op A) (Linear.op A v)) :=
    funext fun s => (hasDerivAt_exp_sub A t v s).deriv
  rw [hd]
  exact (((LTI.continuous_exp_smul A).comp (continuous_const.sub continuous_id)).clm_apply
    continuous_const).neg

/-- The Wiener integral of `s ↦ e^{(t−s)A} v`:
`∫₀ᵗ e^{(t−s)A} v dw = (w(t) − w(0)) v + ∫₀ᵗ (w(s) − w(0)) e^{(t−s)A} A v ds`. -/
@[tmio T, powerlib_foundation] theorem wienerIntegral_exp_sub (A : Matrix (Fin n) (Fin n) ℝ)
    (v : ℝⁿ) {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    wienerIntegral (fun s => exp ((t - s) • Linear.op A) v) w t =
      (w t - w 0) • v + ∫ s in (0 : ℝ)..t, (w s - w 0) • exp ((t - s) • Linear.op A)
        (Linear.op A v) := by
  have hw' : Continuous fun s => w s - w 0 := hw.sub continuous_const
  have e : w = fun s => (w s - w 0) + w 0 := funext fun s => by ring
  rw [e, wienerIntegral_add_const (contDiff_exp_sub A t v) hw' (w 0)]
  have hd : deriv (fun s => exp ((t - s) • Linear.op A) v) =
      fun s => -(exp ((t - s) • Linear.op A) (Linear.op A v)) :=
    funext fun s => (hasDerivAt_exp_sub A t v s).deriv
  simp only [wienerIntegral, hd, sub_self, LTI.exp_zero_smul, one_apply_eq_self,
    zero_smul, sub_zero, smul_neg, intervalIntegral.integral_neg, sub_neg_eq_add]
  simp

/-- Derivative of the variation-of-constants expression `e^{tA}x₀ + ∫₀ᵗ e^{(t−s)A} u(s) ds`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_duhamel
    (A : Matrix (Fin n) (Fin n) ℝ) {u : ℝ → ℝⁿ} (hu : Continuous u) (x₀ : ℝⁿ) (t : ℝ) :
    HasDerivAt (fun t => exp (t • Linear.op A) x₀ + ∫ s in (0 : ℝ)..t,
        exp ((t - s) • Linear.op A) (u s))
      (Linear.op A (exp (t • Linear.op A) x₀ + ∫ s in (0 : ℝ)..t,
        exp ((t - s) • Linear.op A) (u s)) + u t) t := by
  set M := Linear.op A
  set φ : ℝ → ℝⁿ := fun s => exp ((-s) • M) (u s)
  have hφc : Continuous φ := ((LTI.continuous_exp_smul A).comp continuous_neg).clm_apply hu
  have hrw : ∀ τ, exp (τ • M) x₀ + ∫ s in (0 : ℝ)..τ, exp ((τ - s) • M) (u s) =
      exp (τ • M) (x₀ + ∫ s in (0 : ℝ)..τ, φ s) := by
    intro τ
    rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hφc.intervalIntegrable 0 τ)]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [φ]
    rw [← mul_apply_eq_comp, ← LTI.exp_smul_add, sub_eq_add_neg]
  have hfun : (fun τ => exp (τ • M) x₀ + ∫ s in (0 : ℝ)..τ, exp ((τ - s) • M) (u s)) =
      fun τ => exp (τ • M) (x₀ + ∫ s in (0 : ℝ)..τ, φ s) := funext hrw
  rw [hfun, hrw]
  have hI : HasDerivAt (fun τ => x₀ + ∫ s in (0 : ℝ)..τ, φ s) (φ t) t :=
    (hφc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x₀
  have h := (hasDerivAt_exp_smul_const' M t).clm_apply hI
  refine h.congr_deriv ?_
  simp only [φ, mul_apply_eq_comp]
  rw [← mul_apply_eq_comp (exp (t • M)), LTI.exp_smul_mul_neg,
    one_apply_eq_self]

@[tmio T, powerlib_foundation] private theorem continuous_noiseDrift
    (A : Matrix (Fin n) (Fin n) ℝ) {f : ℝ → ℝⁿ} (hf : Continuous f) (B : Matrix (Fin n) ι ℝ)
    {w : ι → ℝ → ℝ} (hw : ∀ k, Continuous (w k)) :
    Continuous fun s => f s + Linear.op A (noiseIncr B w s) :=
  hf.add ((Linear.op A).continuous.comp (continuous_noiseIncr B hw))

/-- **Closed form** of the pathwise solution:
`x(t) = e^{tA}x₀ + ∫₀ᵗ e^{(t−s)A}(f(s) + A B(w(s) − w(0))) ds + B(w(t) − w(0))`. -/
@[tmio T, powerlib_foundation] theorem sdeSol_eq (A : Matrix (Fin n) (Fin n) ℝ) {f : ℝ → ℝⁿ}
    (hf : Continuous f) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) {w : ι → ℝ → ℝ}
    (hw : ∀ k, Continuous (w k)) (t : ℝ) :
    sdeSol A f B x₀ w t = exp (t • Linear.op A) x₀ + (∫ s in (0 : ℝ)..t,
      exp ((t - s) • Linear.op A) (f s + Linear.op A (noiseIncr B w s))) + noiseIncr B w t := by
  have hexp : Continuous fun s : ℝ => exp ((t - s) • Linear.op A) :=
    (LTI.continuous_exp_smul A).comp (continuous_const.sub continuous_id)
  have hint : ∀ k, IntervalIntegrable (fun s => (w k s - w k 0) •
      exp ((t - s) • Linear.op A) (Linear.op A (col B k))) volume 0 t := fun k =>
    (((hw k).sub continuous_const).smul (hexp.clm_apply continuous_const)).intervalIntegrable 0 t
  have hsum : ∑ k, wienerIntegral (fun s => exp ((t - s) • Linear.op A) (col B k)) (w k) t =
      noiseIncr B w t + ∫ s in (0 : ℝ)..t,
        exp ((t - s) • Linear.op A) (Linear.op A (noiseIncr B w s)) := by
    simp_rw [wienerIntegral_exp_sub A _ (hw _) t]
    rw [Finset.sum_add_distrib, ← noiseIncr_eq_sum,
      ← intervalIntegral.integral_finsetSum fun k _ => hint k]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [noiseIncr_eq_sum, map_sum, map_smul]
  have h1 : IntervalIntegrable (fun s => exp ((t - s) • Linear.op A) (f s)) volume 0 t :=
    (hexp.clm_apply hf).intervalIntegrable 0 t
  have h2 : IntervalIntegrable (fun s => exp ((t - s) • Linear.op A)
      (Linear.op A (noiseIncr B w s))) volume 0 t :=
    (hexp.clm_apply (((Linear.op A).continuous.comp (continuous_noiseIncr B hw)))).intervalIntegrable 0 t
  rw [sdeSol, detSol, hsum]
  simp_rw [map_add]
  rw [intervalIntegral.integral_add h1 h2]
  abel

/-- The pathwise solution is continuous in time. -/
@[tmio T, powerlib_foundation] theorem continuous_sdeSol (A : Matrix (Fin n) (Fin n) ℝ)
    {f : ℝ → ℝⁿ} (hf : Continuous f) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) {w : ι → ℝ → ℝ}
    (hw : ∀ k, Continuous (w k)) : Continuous (sdeSol A f B x₀ w) := by
  have h : sdeSol A f B x₀ w = fun t => (exp (t • Linear.op A) x₀ + ∫ s in (0 : ℝ)..t,
      exp ((t - s) • Linear.op A) (f s + Linear.op A (noiseIncr B w s))) + noiseIncr B w t :=
    funext (sdeSol_eq A hf B x₀ hw)
  rw [h]
  exact (continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_duhamel A (continuous_noiseDrift A hf B hw) x₀ t).continuousAt).add
    (continuous_noiseIncr B hw)

/-- **Existence.** The pathwise solution solves the integral equation of the SDE,
`x(t) = x₀ + ∫₀ᵗ (A x(s) + f(s)) ds + B(w(t) − w(0))`. -/
@[tmio T, powerlib_foundation] theorem sdeSol_integral_eq (A : Matrix (Fin n) (Fin n) ℝ)
    {f : ℝ → ℝⁿ} (hf : Continuous f) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) {w : ι → ℝ → ℝ}
    (hw : ∀ k, Continuous (w k)) (t : ℝ) :
    sdeSol A f B x₀ w t =
      x₀ + (∫ s in (0 : ℝ)..t, (Linear.op A (sdeSol A f B x₀ w s) + f s)) + noiseIncr B w t := by
  set M := Linear.op A
  set u := fun s => f s + M (noiseIncr B w s)
  have hu : Continuous u := continuous_noiseDrift A hf B hw
  set y : ℝ → ℝⁿ := fun t => exp (t • M) x₀ + ∫ s in (0 : ℝ)..t, exp ((t - s) • M) (u s)
  have hxy : ∀ s, sdeSol A f B x₀ w s = y s + noiseIncr B w s := sdeSol_eq A hf B x₀ hw
  have hy : ∀ s, HasDerivAt y (M (y s) + u s) s := hasDerivAt_duhamel A hu x₀
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun s => (hy s).continuousAt
  have hcy : Continuous fun s => M (y s) + u s := (M.continuous.comp hyc).add hu
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hy s)
    (hcy.intervalIntegrable 0 t)
  have hy0 : y 0 = x₀ := by simp [y, LTI.exp_zero_smul]
  have hint : ∫ s in (0 : ℝ)..t, (M (sdeSol A f B x₀ w s) + f s) =
      ∫ s in (0 : ℝ)..t, (M (y s) + u s) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hxy, u, map_add]
    abel
  rw [hint, hFTC, hy0, hxy]
  abel

/-- **Uniqueness.** Every continuous solution of the integral equation
`x(t) = x₀ + ∫₀ᵗ (A x(s) + f(s)) ds + B(w(t) − w(0))` is the pathwise solution. With
`sdeSol_integral_eq` this is the meaning of the additive-noise SDE path by path. -/
@[tmio T, powerlib_foundation] theorem eq_sdeSol (A : Matrix (Fin n) (Fin n) ℝ)
    {f : ℝ → ℝⁿ} (hf : Continuous f) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) {w : ι → ℝ → ℝ}
    (hw : ∀ k, Continuous (w k)) {x : ℝ → ℝⁿ} (hx : Continuous x)
    (h : ∀ t, x t = x₀ + (∫ s in (0 : ℝ)..t, (Linear.op A (x s) + f s)) + noiseIncr B w t) :
    x = sdeSol A f B x₀ w := by
  set M := Linear.op A
  set u := fun s => f s + M (noiseIncr B w s)
  have hu : Continuous u := continuous_noiseDrift A hf B hw
  set y : ℝ → ℝⁿ := fun t => x t - noiseIncr B w t
  have hyint : ∀ t, y t = x₀ + ∫ s in (0 : ℝ)..t, (M (x s) + f s) := fun t => by
    simp only [y]; rw [h t]; abel
  have hy : ∀ t, HasDerivAt y (M (y t) + u t) t := by
    intro t
    have hc : Continuous fun s => M (x s) + f s := (M.continuous.comp hx).add hf
    have hd := ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add x₀
    have hy' : HasDerivAt y (M (x t) + f t) t := by
      rw [show y = fun t => x₀ + ∫ s in (0 : ℝ)..t, (M (x s) + f s) from funext hyint]
      exact hd
    refine hy'.congr_deriv ?_
    simp only [y, u, map_sub]
    abel
  have hy0 : y 0 = x₀ := by rw [hyint 0]; simp
  funext t
  have hv := LTI.variation_of_constants hu hy t
  rw [hy0] at hv
  rw [sdeSol_eq A hf B x₀ hw t, ← hv]
  simp only [y, sub_add_cancel]

/-- **Consistency with the classical ODE and the decomposition (2-14).** If the noise paths are
`C¹`, `ẇ_k = e_k` continuous, every solution of `ẋ = A x + Σ_k e_k(t) b_k + g(t) b_f` (TR-110
(2-12) with ambient inputs `e_k` and forced input `g b_f`) is the pathwise solution with
`f = g b_f`; its three terms are the transient, ambient and forced responses of
`LTI.three_components`. -/
@[tmio T, powerlib_foundation] theorem eq_sdeSol_of_hasDerivAt {K : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin K) ℝ) {e : Fin K → ℝ → ℝ}
    (he : ∀ k, Continuous (e k)) {w : Fin K → ℝ → ℝ} (hw : ∀ k s, HasDerivAt (w k) (e k s) s)
    (bf : ℝⁿ) {g : ℝ → ℝ} (hg : Continuous g) {x : ℝ → ℝⁿ}
    (hx : ∀ t, HasDerivAt x (Linear.op A (x t) + ((∑ k, e k t • col B k) + g t • bf)) t) :
    x = sdeSol A (fun s => g s • bf) B (x 0) w := by
  funext t
  rw [LTI.three_components (col B) e he bf hg hx t, sdeSol, detSol]
  have hk : ∀ k, wienerIntegral (fun s => exp ((t - s) • Linear.op A) (col B k)) (w k) t =
      ∫ s in (0 : ℝ)..t, e k s • exp ((t - s) • Linear.op A) (col B k) := fun k =>
    wienerIntegral_eq_integral (contDiff_exp_sub A t (col B k)) (hw k) (he k) t
  simp_rw [hk, map_smul]
  abel

/-! ## Second moments under a Brownian-type law -/

omit [Fintype ι] in
/-- Entries of `e^{τA} b_k`: `(e^{τA} b_k)_i = (e^{τA} B)_{ik}`. -/
@[tmio T, powerlib_foundation] theorem exp_col_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) ι ℝ) (τ : ℝ) (k : ι) (i : Fin n) :
    exp (τ • Linear.op A) (col B k) i = (exp (τ • A) * B) i k := by
  rw [← LTI.op_exp_smul]
  simp [Linear.op, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [Fintype ι] in
@[tmio T, powerlib_foundation] private theorem contDiff_exp_entry (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) ι ℝ) (t : ℝ) (k : ι) (i : Fin n) :
    ContDiff ℝ 1 (fun s => (exp ((t - s) • A) * B) i k) := by
  have h : (fun s => (exp ((t - s) • A) * B) i k) =
      fun s => EuclideanSpace.proj i (exp ((t - s) • Linear.op A) (col B k)) :=
    funext fun s => by rw [PiLp.proj_apply, exp_col_apply]
  rw [h]
  exact (EuclideanSpace.proj i).contDiff.comp (contDiff_exp_sub A t _)

/-- **Components** of the pathwise solution: `x_i(t) = x̄_i(t) + Σ_k ∫₀ᵗ (e^{(t−s)A} B)_{ik}
dw_k(s)` with the deterministic part `x̄ = detSol`. -/
@[tmio T, powerlib_foundation] theorem sdeSol_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) {w : ι → ℝ → ℝ}
    (hw : ∀ k, Continuous (w k)) (t : ℝ) (i : Fin n) :
    sdeSol A f B x₀ w t i =
      detSol A f x₀ t i + ∑ k, wienerIntegral (fun s => (exp ((t - s) • A) * B) i k) (w k) t := by
  have h : ∀ k, wienerIntegral (fun s => exp ((t - s) • Linear.op A) (col B k)) (w k) t i =
      wienerIntegral (fun s => (exp ((t - s) • A) * B) i k) (w k) t := by
    intro k
    have hm := wienerIntegral_map (EuclideanSpace.proj i) (contDiff_exp_sub A t (col B k))
      (hw k) t
    rw [PiLp.proj_apply] at hm
    rw [← hm]
    congr 1
    funext s
    rw [PiLp.proj_apply, exp_col_apply]
  rw [sdeSol, PiLp.add_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, h]

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ι → ℝ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
@[tmio T, powerlib_foundation] private theorem sdeSol_apply_fun (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) (hc : ∀ k ω, Continuous fun u => W k u ω)
    (t : ℝ) (i : Fin n) :
    (fun ω => sdeSol A f B x₀ (fun k u => W k u ω) t i) = fun ω => detSol A f x₀ t i +
      ∑ k, wienerIntegral (fun s => (exp ((t - s) • A) * B) i k) (fun u => W k u ω) t :=
  funext fun ω => sdeSol_apply A f B x₀ (hc · ω) t i

/-- **Mean** of the pathwise solution driven by centred noise: `E x(t) = e^{tA}x₀ +
∫₀ᵗ e^{(t−s)A} f(s) ds`, the deterministic solution. -/
@[tmio T, powerlib_foundation] theorem integral_sdeSol (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {t : ℝ} (ht : 0 ≤ t) (i : Fin n) :
    ∫ ω, sdeSol A f B x₀ (fun k u => W k u ω) t i ∂P = detSol A f x₀ t i := by
  rw [sdeSol_apply_fun A f B x₀ hc t i]
  have hint : ∀ k, Integrable (fun ω => wienerIntegral (fun s => (exp ((t - s) • A) * B) i k)
      (fun u => W k u ω) t) P := fun k =>
    (memLp_wienerIntegral (hc k) (hm k) (hL2 k) ht (sqMoment_le hQ k t) _
      (contDiff_exp_entry A B t k i)).integrable one_le_two
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ => hint k),
    integral_finsetSum _ fun k _ => hint k]
  simp only [integral_const, probReal_univ, one_smul]
  rw [Finset.sum_eq_zero fun k _ => integral_wienerIntegral (hc k) (hm k) (hL2 k) ht
    (sqMoment_le hQ k t) (hmean k) (contDiff_exp_entry A B t k i), add_zero]

/-- **Covariance** of the pathwise solution, for noise with
`E[W_k(u) W_l(v)] = Q_kl min(u, v)`: for `t, s ≥ 0`,
`Cov(x_i(t), x_j(s)) = ∫₀^{min(t,s)} (e^{(t−r)A} B Q Bᵀ e^{(s−r)Aᵀ})_{ij} dr`. -/
@[tmio T, powerlib_foundation] theorem covariance_sdeSol (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (i j : Fin n) :
    cov[fun ω => sdeSol A f B x₀ (fun k u => W k u ω) t i,
      fun ω => sdeSol A f B x₀ (fun k u => W k u ω) s j; P] =
      ∫ r in (0 : ℝ)..min t s, (exp ((t - r) • A) * B * Q * Bᵀ * exp ((s - r) • Aᵀ)) i j := by
  have hI : ∀ {τ : ℝ}, 0 ≤ τ → ∀ (m : Fin n) k, MemLp (fun ω => wienerIntegral
      (fun r => (exp ((τ - r) • A) * B) m k) (fun u => W k u ω) τ) 2 P := fun hτ m k =>
    memLp_wienerIntegral (hc k) (hm k) (hL2 k) hτ (sqMoment_le hQ k _) _
      (contDiff_exp_entry A B _ k m)
  rw [sdeSol_apply_fun A f B x₀ hc t i, sdeSol_apply_fun A f B x₀ hc s j,
    covariance_const_add_left ((memLp_finsetSum _ fun k _ => hI ht i k).integrable one_le_two),
    covariance_const_add_right ((memLp_finsetSum _ fun k _ => hI hs j k).integrable one_le_two),
    covariance_fun_sum_fun_sum (hI ht i) (hI hs j)]
  simp_rw [covariance_wienerIntegral hc hm hL2 hQ hmean (contDiff_exp_entry A B t _ i)
    (contDiff_exp_entry A B s _ j) _ _ ht hs]
  have hcont : ∀ (τ : ℝ) (m : Fin n) (k : ι), Continuous fun r => (exp ((τ - r) • A) * B) m k :=
    fun τ m k => (contDiff_exp_entry A B τ k m).continuous
  have hint : ∀ k l, IntervalIntegrable (fun r => (exp ((t - r) • A) * B) i k *
      (exp ((s - r) • A) * B) j l) volume 0 (min t s) := fun k l =>
    ((hcont t i k).mul (hcont s j l)).intervalIntegrable _ _
  simp_rw [← intervalIntegral.integral_const_mul]
  have hsum : ∀ k, ∑ l, ∫ r in (0 : ℝ)..min t s, Q k l * ((exp ((t - r) • A) * B) i k *
      (exp ((s - r) • A) * B) j l) = ∫ r in (0 : ℝ)..min t s, ∑ l, Q k l *
      ((exp ((t - r) • A) * B) i k * (exp ((s - r) • A) * B) j l) := fun k =>
    (intervalIntegral.integral_finsetSum fun l _ => (hint k l).const_mul (Q k l)).symm
  simp_rw [hsum]
  have hint2 : ∀ k ∈ (Finset.univ : Finset ι), IntervalIntegrable (fun r => ∑ l, Q k l *
      ((exp ((t - r) • A) * B) i k * (exp ((s - r) • A) * B) j l)) volume 0 (min t s) :=
    fun k _ => (continuous_finsetSum _ fun l _ => continuous_const.mul
      ((hcont t i k).mul (hcont s j l))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum hint2]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have e : exp ((s - r) • Aᵀ) = (exp ((s - r) • A))ᵀ := by
    rw [← Matrix.transpose_smul, Matrix.exp_transpose]
  have e2 : exp ((t - r) • A) * B * Q * Bᵀ * (exp ((s - r) • A))ᵀ =
      exp ((t - r) • A) * B * Q * (exp ((s - r) • A) * B)ᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [e, e2]
  set F := exp ((t - r) • A) * B
  set G := exp ((s - r) • A) * B
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Moments

/-! ## Gramian form and the stationary autocovariance -/

section Stationary

open scoped Matrix.Norms.Frobenius

attribute [local instance] powerlib.LinearAlgebra.frobeniusENormedAddMonoid

/-- The finite-horizon Gramian `Σ(s) = ∫₀ˢ e^{uA} K e^{uAᵀ} du` (covariance of the noise part at
time `s` for `K = B Q Bᵀ`). -/
def gramian (A K : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∫ u in (0 : ℝ)..s, exp (u • A) * K * exp (u • Aᵀ)

@[tmio T, powerlib_foundation] private theorem continuous_gramianIntegrand
    (A K : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun u : ℝ => exp (u • A) * K * exp (u • Aᵀ) :=
  continuous_iff_continuousAt.2 fun u =>
    (((hasDerivAt_exp_smul_const A u).mul_const K).mul (hasDerivAt_exp_smul_const Aᵀ u)).continuousAt

@[tmio T, powerlib_foundation] private theorem gramian_apply (A K : Matrix (Fin n) (Fin n) ℝ)
    (s : ℝ) (i j : Fin n) :
    gramian A K s i j = ∫ u in (0 : ℝ)..s, (exp (u • A) * K * exp (u • Aᵀ)) i j := by
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)
  have h := ContinuousLinearMap.intervalIntegral_comp_comm L
    ((continuous_gramianIntegrand A K).intervalIntegrable (μ := volume) 0 s)
  exact h.symm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ι → ℝ → Ω → ℝ}

/-- **Covariance in Gramian form.** For `0 ≤ s ≤ t`,
`Cov(x_i(t), x_j(s)) = (e^{(t−s)A} Σ(s))_{ij}` with `Σ(s) = ∫₀ˢ e^{uA} B Q Bᵀ e^{uAᵀ} du`
(`gramian`). -/
@[tmio T, powerlib_foundation] theorem covariance_sdeSol_of_le (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ) (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (i j : Fin n) :
    cov[fun ω => sdeSol A f B x₀ (fun k u => W k u ω) t i,
      fun ω => sdeSol A f B x₀ (fun k u => W k u ω) s j; P] =
      (exp ((t - s) • A) * gramian A (B * Q * Bᵀ) s) i j := by
  rw [covariance_sdeSol A f B x₀ hc hm hL2 hQ hmean (hs.trans hst) hs i j, min_eq_right hst]
  set K := B * Q * Bᵀ
  have hsplit : ∀ r, exp ((t - r) • A) * B * Q * Bᵀ * exp ((s - r) • Aᵀ) =
      exp ((t - s) • A) * (exp ((s - r) • A) * K * exp ((s - r) • Aᵀ)) := by
    intro r
    have he : exp ((t - r) • A) = exp ((t - s) • A) * exp ((s - r) • A) := by
      rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left _).smul_right _),
        ← add_smul]
      congr 2; ring
    rw [he]
    simp only [K, Matrix.mul_assoc]
  simp only [hsplit]
  simp only [Matrix.mul_apply (M := exp ((t - s) • A))]
  have hint : ∀ m ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable (fun r =>
      exp ((t - s) • A) i m * (exp ((s - r) • A) * K * exp ((s - r) • Aᵀ)) m j) volume 0 s := by
    intro m _
    have hc' : Continuous fun r : ℝ => (exp ((s - r) • A) * K * exp ((s - r) • Aᵀ)) m j :=
      ((continuous_gramianIntegrand A K).comp (continuous_const.sub continuous_id)).matrix_elem m j
    exact (continuous_const.mul hc').intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, gramian_apply]
  congr 1
  have := intervalIntegral.integral_comp_sub_left
    (fun u => (exp (u • A) * K * exp (u • Aᵀ)) m j) (a := 0) (b := s) s
  simp only [sub_self, sub_zero] at this
  exact this

/-- **Stationary autocovariance.** If `A` is Hurwitz and `Σ∞` solves the covariance Lyapunov
equation `A Σ∞ + Σ∞ Aᵀ + B Q Bᵀ = 0`, then for every lag `τ ≥ 0`
`Cov(x_i(s + τ), x_j(s)) → (e^{τA} Σ∞)_{ij}` as `s → ∞`, from every deterministic initial state
and for every deterministic input `f`. -/
@[tmio T, powerlib_foundation] theorem tendsto_covariance_sdeSol {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ)
    (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {Pinf : Matrix (Fin n) (Fin n) ℝ}
    (hP : Lyapunov.SolvesCovLyapunov A Pinf (B * Q * Bᵀ)) {τ : ℝ} (hτ : 0 ≤ τ) (i j : Fin n) :
    Tendsto (fun s => cov[fun ω => sdeSol A f B x₀ (fun k u => W k u ω) (s + τ) i,
      fun ω => sdeSol A f B x₀ (fun k u => W k u ω) s j; P]) atTop
      (𝓝 ((exp (τ • A) * Pinf) i j)) := by
  have hG : Tendsto (gramian A (B * Q * Bᵀ)) atTop (𝓝 Pinf) :=
    Lyapunov.tendsto_integral_gramian hA hP
  have hlim : Tendsto (fun s => (exp (τ • A) * gramian A (B * Q * Bᵀ) s) i j) atTop
      (𝓝 ((exp (τ • A) * Pinf) i j)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hG' := tendsto_iff_norm_sub_tendsto_zero.mp hG
    have hb : Tendsto (fun s => ‖exp (τ • A)‖ * ‖gramian A (B * Q * Bᵀ) s - Pinf‖) atTop (𝓝 0) := by
      simpa using hG'.const_mul ‖exp (τ • A)‖
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hb
    have h1 := Lyapunov.abs_entry_le_norm (exp (τ • A) * (gramian A (B * Q * Bᵀ) s - Pinf)) i j
    have e : (exp (τ • A) * (gramian A (B * Q * Bᵀ) s - Pinf)) i j =
        (exp (τ • A) * gramian A (B * Q * Bᵀ) s) i j - (exp (τ • A) * Pinf) i j := by
      rw [Matrix.mul_sub, Matrix.sub_apply]
    rw [e] at h1
    rw [Real.norm_eq_abs]
    exact h1.trans (norm_mul_le _ _)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with s hs
  rw [covariance_sdeSol_of_le A f B x₀ hc hm hL2 hQ hmean hs (by linarith) i j, add_sub_cancel_left]

/-! ### Brownian noise -/

open scoped NNReal

/-- **The linear SDE driven by Brownian motion.** Let the noise components be pairwise independent
pre-Brownian motions `β_k` (Mathlib's `IsPreBrownianReal`, time `ℝ≥0`, read on `ℝ` through
`u ↦ β_k(max u 0)`) with continuous paths and measurable marginals, and let `x₀` and `f` be
deterministic. Then for `0 ≤ s ≤ t`: `E x(t) = e^{tA}x₀ + ∫₀ᵗ e^{(t−s)A} f(s) ds` and
`Cov(x_i(t), x_j(s)) = (e^{(t−s)A} Σ(s))_{ij}`, `Σ(s) = ∫₀ˢ e^{uA} B Bᵀ e^{uAᵀ} du`. -/
@[tmio T, powerlib_foundation] theorem sdeSol_brownian [DecidableEq ι]
    (A : Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ)
    {β : ι → ℝ≥0 → Ω → ℝ} (hβ : ∀ k, IsPreBrownianReal (β k) P)
    (hind : ∀ k l, k ≠ l → ∀ s t, IndepFun (β k s) (β l t) P)
    (hc : ∀ k ω, Continuous fun t => β k t ω) (hm : ∀ k t, Measurable (β k t))
    {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i j : Fin n) :
    ∫ ω, sdeSol A f B x₀ (fun k u => β k u.toNNReal ω) t i ∂P = detSol A f x₀ t i ∧
    cov[fun ω => sdeSol A f B x₀ (fun k u => β k u.toNNReal ω) t i,
      fun ω => sdeSol A f B x₀ (fun k u => β k u.toNNReal ω) s j; P] =
      (exp ((t - s) • A) * gramian A (B * Bᵀ) s) i j := by
  have hc' : ∀ k ω, Continuous fun u : ℝ => β k u.toNNReal ω := fun k ω =>
    (hc k ω).comp continuous_real_toNNReal
  have hQ := fun k l (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) => integral_mul_brownian hβ hind k l hu hv
  have hL2 : ∀ k (u : ℝ), MemLp (β k u.toNNReal) 2 P := fun k u => BM.memLp_two (hβ k) _
  have hmean : ∀ k (u : ℝ), 0 ≤ u → ∫ ω, β k u.toNNReal ω ∂P = 0 :=
    fun k u _ => (hβ k).integral_eval _
  refine ⟨integral_sdeSol (W := fun k u ω => β k u.toNNReal ω) A f B x₀ hc' (fun k u => hm k _)
    hL2 hQ hmean (hs.trans hst) i, ?_⟩
  have h := covariance_sdeSol_of_le (W := fun k u ω => β k u.toNNReal ω) A f B x₀ hc'
    (fun k u => hm k _) hL2 hQ hmean hs hst i j
  rwa [Matrix.mul_one] at h

/-- **Stationary autocovariance under Brownian noise.** For Hurwitz `A` the covariance Lyapunov
equation `A Σ∞ + Σ∞ Aᵀ + B Bᵀ = 0` has a positive semidefinite solution `Σ∞`, and
`Cov(x_i(s + τ), x_j(s)) → (e^{τA} Σ∞)_{ij}` as `s → ∞` for every lag `τ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem tendsto_covariance_sdeSol_brownian {m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) (f : ℝ → ℝⁿ)
    (B : Matrix (Fin n) (Fin m) ℝ) (x₀ : ℝⁿ)
    {β : Fin m → ℝ≥0 → Ω → ℝ} (hβ : ∀ k, IsPreBrownianReal (β k) P)
    (hind : ∀ k l, k ≠ l → ∀ s t, IndepFun (β k s) (β l t) P)
    (hc : ∀ k ω, Continuous fun t => β k t ω) (hm : ∀ k t, Measurable (β k t)) :
    ∃ Pinf : Matrix (Fin n) (Fin n) ℝ, Lyapunov.SolvesCovLyapunov A Pinf (B * Bᵀ) ∧
      Pinf.PosSemidef ∧ ∀ τ, 0 ≤ τ → ∀ i j : Fin n,
        Tendsto (fun s => cov[fun ω => sdeSol A f B x₀ (fun k u => β k u.toNNReal ω) (s + τ) i,
          fun ω => sdeSol A f B x₀ (fun k u => β k u.toNNReal ω) s j; P]) atTop
          (𝓝 ((exp (τ • A) * Pinf) i j)) := by
  obtain ⟨Pinf, hP⟩ := Lyapunov.exists_stationaryCov hA B
  refine ⟨Pinf, hP, Lyapunov.stationaryCov_posSemidef hA B hP, fun τ hτ i j => ?_⟩
  have hc' : ∀ k ω, Continuous fun u : ℝ => β k u.toNNReal ω := fun k ω =>
    (hc k ω).comp continuous_real_toNNReal
  have hQ := fun k l (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) => integral_mul_brownian hβ hind k l hu hv
  exact tendsto_covariance_sdeSol (W := fun k u ω => β k u.toNNReal ω) hA f B x₀ hc'
    (fun k u => hm k _) (fun k u => BM.memLp_two (hβ k) _) hQ
    (fun k u _ => (hβ k).integral_eval _) (by rwa [Matrix.mul_one]) hτ i j

/-! ### The measurement equation `y = C x + μ` of TR-110 (2-1) -/

omit [Fintype ι] [IsProbabilityMeasure P] in
/-- **Covariances add under a linear measurement**: for random vectors `X, X'` and measurement
noises `M, M'` uncorrelated with them (all square integrable),
`Cov((C X + M)_i, (C X' + M')_j) = (C K Cᵀ)_{ij} + Cov(M_i, M'_j)` with
`K_{kl} = Cov(X_k, X'_l)`. -/
@[tmio T, powerlib_foundation] theorem covariance_measurement [IsFiniteMeasure P] {p m : ℕ}
    (C : Matrix (Fin p) (Fin m) ℝ) {X X' : Fin m → Ω → ℝ} {M M' : Fin p → Ω → ℝ}
    (hX : ∀ k, MemLp (X k) 2 P) (hX' : ∀ k, MemLp (X' k) 2 P) (hM : ∀ i, MemLp (M i) 2 P)
    (hM' : ∀ i, MemLp (M' i) 2 P) (h1 : ∀ k j, cov[X k, M' j; P] = 0)
    (h2 : ∀ i l, cov[M i, X' l; P] = 0) (i j : Fin p) :
    cov[fun ω => ∑ k, C i k * X k ω + M i ω, fun ω => ∑ l, C j l * X' l ω + M' j ω; P] =
      (C * Matrix.of (fun k l => cov[X k, X' l; P]) * Cᵀ) i j + cov[M i, M' j; P] := by
  have hY : MemLp (fun ω => ∑ k, C i k * X k ω) 2 P :=
    memLp_finsetSum _ fun k _ => (hX k).const_mul _
  have hY' : MemLp (fun ω => ∑ l, C j l * X' l ω) 2 P :=
    memLp_finsetSum _ fun l _ => (hX' l).const_mul _
  have e1 : (fun ω => ∑ k, C i k * X k ω + M i ω) = (fun ω => ∑ k, C i k * X k ω) + M i := rfl
  have e2 : (fun ω => ∑ l, C j l * X' l ω + M' j ω) = (fun ω => ∑ l, C j l * X' l ω) + M' j :=
    rfl
  rw [e1, e2, covariance_add_left hY (hM i) (hY'.add (hM' j)), covariance_add_right hY hY' (hM' j),
    covariance_add_right (hM i) hY' (hM' j),
    covariance_fun_sum_fun_sum (fun k => (hX k).const_mul (C i k)) (fun l => (hX' l).const_mul (C j l)),
    covariance_fun_sum_left (fun k => (hX k).const_mul (C i k)) (hM' j),
    covariance_fun_sum_right (fun l => (hX' l).const_mul (C j l)) (hM i)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, h1, h2, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The pathwise solution is uncorrelated with every square-integrable variable that is
uncorrelated with the driving noise. -/
@[tmio T, powerlib_foundation] private theorem covariance_sdeSol_eq_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ)
    (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hYW : ∀ k u, 0 ≤ u → ∫ ω, Y ω * W k u ω ∂P = 0) {t : ℝ} (ht : 0 ≤ t) (i : Fin n) :
    cov[fun ω => sdeSol A f B x₀ (fun k u => W k u ω) t i, Y; P] = 0 := by
  have hI : ∀ k, MemLp (fun ω => wienerIntegral (fun r => (exp ((t - r) • A) * B) i k)
      (fun u => W k u ω) t) 2 P := fun k =>
    memLp_wienerIntegral (hc k) (hm k) (hL2 k) ht (sqMoment_le hQ k _) _
      (contDiff_exp_entry A B _ k i)
  rw [sdeSol_apply_fun A f B x₀ hc t i,
    covariance_const_add_left ((memLp_finsetSum _ fun k _ => hI k).integrable one_le_two),
    covariance_fun_sum_left hI hY]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [covariance_eq_sub (hI k) hY, integral_wienerIntegral (hc k) (hm k) (hL2 k) ht
    (sqMoment_le hQ k t) (hmean k) (contDiff_exp_entry A B t k i), zero_mul, sub_zero]
  simp only [Pi.mul_apply]
  have h := integral_mul_wienerIntegral (hc k) (hm k) (hL2 k) ht (sqMoment_le hQ k t)
    (contDiff_exp_entry A B t k i) hY
  rw [show (fun ω => wienerIntegral (fun r => (exp ((t - r) • A) * B) i k) (fun u => W k u ω) t *
      Y ω) = fun ω => Y ω * wienerIntegral (fun r => (exp ((t - r) • A) * B) i k)
        (fun u => W k u ω) t from funext fun ω => mul_comm _ _, h,
    wienerIntegral_congr _ (w₂ := fun _ => 0) fun u hu => by
      rw [uIcc_of_le ht] at hu; exact hYW k u hu.1]
  simp [wienerIntegral]

/-- **Output covariance of the measurement equation (2-1)**, `y = C x + μ`, for measurement
noise `μ` uncorrelated with the driving noise: for `0 ≤ s ≤ t`,
`Cov(y_i(t), y_j(s)) = (C e^{(t−s)A} Σ(s) Cᵀ)_{ij} + Cov(μ_i(t), μ_j(s))`. -/
@[tmio T, powerlib_foundation] theorem covariance_output_sdeSol {p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝⁿ) (B : Matrix (Fin n) ι ℝ) (x₀ : ℝⁿ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hc : ∀ k ω, Continuous fun u => W k u ω)
    (hm : ∀ k u, Measurable (W k u)) (hL2 : ∀ k u, MemLp (W k u) 2 P) {Q : Matrix ι ι ℝ}
    (hQ : ∀ k l u v, 0 ≤ u → 0 ≤ v → ∫ ω, W k u ω * W l v ω ∂P = Q k l * min u v)
    (hmean : ∀ k u, 0 ≤ u → ∫ ω, W k u ω ∂P = 0) {μ : ℝ → Fin p → Ω → ℝ}
    (hμ : ∀ t i, MemLp (μ t i) 2 P) (hμW : ∀ t i k u, 0 ≤ u → ∫ ω, μ t i ω * W k u ω ∂P = 0)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i j : Fin p) :
    cov[fun ω => ∑ k, C i k * sdeSol A f B x₀ (fun k u => W k u ω) t k + μ t i ω,
      fun ω => ∑ l, C j l * sdeSol A f B x₀ (fun k u => W k u ω) s l + μ s j ω; P] =
      (C * (exp ((t - s) • A) * gramian A (B * Q * Bᵀ) s) * Cᵀ) i j + cov[μ t i, μ s j; P] := by
  have ht : 0 ≤ t := hs.trans hst
  have hX : ∀ {τ : ℝ}, 0 ≤ τ → ∀ k, MemLp (fun ω => sdeSol A f B x₀ (fun k u => W k u ω) τ k)
      2 P := by
    intro τ hτ k
    have hS : MemLp (fun ω => ∑ l, wienerIntegral (fun r => (exp ((τ - r) • A) * B) k l)
        (fun u => W l u ω) τ) 2 P := memLp_finsetSum _ fun l _ =>
      memLp_wienerIntegral (hc l) (hm l) (hL2 l) hτ (sqMoment_le hQ l _) _
        (contDiff_exp_entry A B _ l k)
    have h2 := (memLp_const (μ := P) (p := 2) (detSol A f x₀ τ k)).add hS
    rw [sdeSol_apply_fun A f B x₀ hc τ k]
    exact h2
  have h := covariance_measurement (X := fun k ω => sdeSol A f B x₀ (fun k u => W k u ω) t k)
    (X' := fun k ω => sdeSol A f B x₀ (fun k u => W k u ω) s k) (M := μ t) (M' := μ s) C
    (hX ht) (hX hs) (hμ t) (hμ s)
    (fun k j => covariance_sdeSol_eq_zero A f B x₀ hc hm hL2 hQ hmean (hμ s j) (hμW s j) ht k)
    (fun i l => by
      rw [covariance_comm]
      exact covariance_sdeSol_eq_zero A f B x₀ hc hm hL2 hQ hmean (hμ t i) (hμW t i) hs l) i j
  have hK : Matrix.of (fun k l => cov[fun ω => sdeSol A f B x₀ (fun k u => W k u ω) t k,
      fun ω => sdeSol A f B x₀ (fun k u => W k u ω) s l; P]) =
      exp ((t - s) • A) * gramian A (B * Q * Bᵀ) s := by
    ext k l
    rw [Matrix.of_apply]
    exact covariance_sdeSol_of_le A f B x₀ hc hm hL2 hQ hmean hs hst k l
  rw [hK] at h
  exact h

end Stationary

end powerlib.Stochastic.LinearSDE

