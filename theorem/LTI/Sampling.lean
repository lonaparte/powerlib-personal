import theorem.LTI.Discrete
import theorem.Periodic.LTI
import theorem.Averaging.StateSpaceAveraging

/-! # Sampling and exact discretization of continuous-time LTI systems

Exact zero-order-hold (ZOH) discretization of `ẋ = A x + B u`, the exact correspondence between
Hurwitz stability of `A` and Schur stability of `e^{TA}`, and the exact stability theory of
sampled-data loops (continuous plant, ZOH, discrete-time LTI controller, optional one-sample
computation delay), intersample behaviour included.

Scope.
* Plant: continuous time, finite state index `X`, input index `U`, constant real matrices,
  `ẋ = A x + B u(t)`. The input is piecewise constant with period `T > 0` (ideal zero-order hold):
  `u(t) = u_k` on `[kT, (k+1)T]`. A trajectory is a Mathlib integral curve on each closed sampling
  interval (one-sided derivatives at the sampling instants), written out in the statements as
  `∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k) (Icc (k * T) ((k + 1) * T))`, the
  piecewise form of `theorem/Averaging/StateSpaceAveraging.lean`; uniqueness is LeanForControl's
  `eqOn_of_isIntegralCurveOn_Icc`.
* Controller: discrete-time LTI, `ξ_{k+1} = A_c ξ_k + B_c x(kT)`, `u_k = C_c ξ_k + D_c x(kT)`
  (ideal synchronous sampler of the full state; a static gain is an empty controller index `Z`).
  A one-sample computation delay, `u_{k+1} = C_c ξ_k + D_c x(kT)`, is the controller with augmented
  state `(ξ_k, u_k)` (`delayedLoopMatrix`). Excluded: quantization, sampling jitter, asynchronous or
  multirate sampling, PWM ripple, saturation and other limits, measurement noise.
* Stability of a lifted matrix on a general finite index type is `spectralRadius < 1` of its
  complexification; for `Fin n` indices this is `SchurStable`
  (`schurStable_iff_spectralRadius_lt_one`).
* Norms: sup norm on states, `L∞` operator norm on matrices (`Matrix.Norms.Operator`); the constants
  depend on this choice, the statements do not.
* Single-semantics rule: no behaviour is defined here. The definitions `zohGamma`,
  `sampledLoopMatrix`, `delayedLoopMatrix` are static matrices; sampled-data trajectories are
  written out in each statement. Every statement holds for arbitrary matrices (model independent):
  foundation results.

Source: work-sync theory/T-control-delay.md §1.4–§1.6 (ZOH, one-sample computation delay, the
delay bound on the bandwidth of a digital current loop), theory/T-numerical-integration.md §2.7
(the discrete recursion as the sampled semantics); `theorem/Dynamics/VariationOfConstants.lean`
(`zoh_exact`, the one-period ZOH step on a Banach space with two-sided derivatives),
`theorem/LTI/Discrete.lean` (Schur stability, contractive powers), `theorem/Periodic/LTI.lean`
(eigenvalues of `e^{TA}`), `theorem/CurrentControl/DigitalPI.lean` and
`theorem/CurrentControl/LoopDelay.lean` (continuous delay models of the same loop).

Results.
* `isHurwitz_iff_schurStable_exp`: for `T > 0`, `A` is Hurwitz iff `e^{TA}` is Schur stable
  (forward through the LeanForControl spectral-mapping lemma
  `spectralRadius_exp_complexification_lt_one`, backward through `e^{TA} v = e^{μT} v`,
  `Periodic.monodromy_const_mulVec_eigen`).
* `zohGamma`, `hasDerivAt_exp_smul_mul`, `mul_zohGamma_add`: `Γ(T) = ∫₀ᵀ e^{sA} B ds` and
  `A Γ(s) + B = e^{sA} B`; `zohGamma_zero`: `Γ(T) = T B` for `A = 0`.
* `zoh_solution`, `zoh_step`: on an interval where the input is held at `u`, every solution is
  `x(t) = e^{(t−a)A} x(a) + Γ(t−a) u`; in particular `x(a + T) = Φ x(a) + Γ u`, `Φ = e^{TA}` (the
  matrix form of `Dynamics.zoh_exact`, for integral curves on the closed interval).
* `sampledLoopMatrix`, `sampledLoop_sample`: the lifted matrix
  `M = [[Φ + Γ D_c, Γ C_c], [B_c, A_c]]` propagates the sampled state,
  `(x(kT), ξ_k) = M^k (x(0), ξ_0)`.
* `sampledLoop_exponentialDecay`: if `M` has spectral radius `< 1` there are `C, a > 0` with
  `‖x(t)‖ ≤ C e^{−at} (‖x(0)‖ + ‖ξ_0‖)` for every `t ≥ 0`, between samples included (uniform bounds
  of `e^{sA}` and `Γ(s)` on `[0, T]`), and `‖ξ_k‖ ≤ C e^{−akT} (‖x(0)‖ + ‖ξ_0‖)`.
* `sampledLoop_exists_trajectory`: every initial state starts a sampled-data trajectory (explicit
  piecewise construction). `spectralRadius_lt_one_of_sampledLoop`: if every trajectory has
  `x(kT) → 0` and `ξ_k → 0`, then `M` has spectral radius `< 1` (Gelfand bound on a contractive
  power). `sampledLoop_exponentialDecay_iff`: uniform exponential decay of every sampled-data
  trajectory holds exactly when `M` has spectral radius `< 1`; the lifted matrix is an exact
  implementation-level criterion, not an approximation.
* `delayedLoopMatrix`, `delayedLoop_exponentialDecay`: the same decay with a one-sample
  computation delay, `‖x(t)‖ ≤ C e^{−at} (‖x(0)‖ + ‖ξ_0‖ + ‖u_0‖)`.
* Static evidence, `schurStable_integratorDelay_iff`: `[[1, b], [−k, 0]]` is Schur stable iff
  `0 < k b < 1`. It is the lifted matrix, on `(x(kT), u_k)`, of the integrator `ẋ = u/L` (exact
  ZOH: `Φ = 1`, `Γ = T/L`, `zohGamma_zero`) under a proportional gain applied with a one-sample
  delay; with `b = Tₛ/L`, `k = K_p = ω_b L` the condition is `0 < ω_b Tₛ < 1`.

Comparison of delay models (the IMC-tuned digital PI current loop, `K_p = ω_b L`, `K_i = ω_b R`,
one-sample computation delay, ZOH; total delay `τ = 1.5 Tₛ`). As `R Tₛ/L → 0` the current mode
of the exact sampled-data loop is the delayed integrator above, with stability boundary
`ω_b Tₛ = 1`. The continuous pure-delay model (`theorem/CurrentControl/LoopDelay.lean`) gives
`ω_b Tₛ < π/3 ≈ 1.047`, the Padé(1,1) platform (`theorem/CurrentControl/DigitalPI.lean`) gives
`ω_b Tₛ < 4/3`: both continuous models overestimate the stable sampling range of the exact loop,
by about `4.7 %` and `33 %`. Numerically (numpy eigenvalues of the 3 × 3 lifted matrix
`[[e^{−RTₛ/L}, 0, (1 − e^{−RTₛ/L})/R], [−Tₛ, 1, 0], [−K_p, K_i, 0]]` on `(i, ξ, u)` with a
forward-Euler integral, scanned over `ω_b Tₛ ∈ (0, 3]`; not formalized) the boundary is
`ω_b Tₛ ≈ 1 + R Tₛ/(2L)`: `1.0006`, `1.005`, `1.050` at `R Tₛ/L = 0.001, 0.01, 0.1`. At `R = 0`
exactly the integral mode sits at `z = 1` and the 3 × 3 matrix is not Schur stable.
-/

noncomputable section
namespace powerlib.LTI
open Matrix Set Filter
open scoped Topology
open scoped Matrix.Norms.Operator

/-! ## Hurwitz versus Schur under exact sampling -/

section Spectral

variable {n : ℕ}

/-- Scaling by a positive time keeps a matrix Hurwitz. -/
@[powerlib_foundation]
private lemma isHurwitz_smul {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A)
    {T : ℝ} (hT : 0 < T) : LinearSystems.IsHurwitz (T • A) := by
  intro μ v hv heig
  have hmap : (T • A).map (algebraMap ℝ ℂ) = (T : ℂ) • A.map (algebraMap ℝ ℂ) := by
    ext i j; simp [Matrix.map_apply]
  rw [hmap, Matrix.smul_mulVec] at heig
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have h2 : A.map (algebraMap ℝ ℂ) *ᵥ v = (μ / T) • v := by
    have := congrArg (fun w => (T : ℂ)⁻¹ • w) heig
    simp only [smul_smul, inv_mul_cancel₀ hT0, one_smul] at this
    rw [this, div_eq_inv_mul]
  have hre := hA _ v hv h2
  rw [Complex.div_ofReal_re] at hre
  simp only [neg_zero] at hre ⊢
  exact (div_neg_iff.mp hre).elim (fun h => absurd h.2 (not_lt.mpr hT.le)) (fun h => h.1)

/-- **Exact sampling preserves exactly the stability of an LTI system.** For a sampling period
`T > 0`, `A` is Hurwitz exactly when `e^{TA}` is Schur stable. -/
@[powerlib_foundation] theorem isHurwitz_iff_schurStable_exp (A : Matrix (Fin n) (Fin n) ℝ)
    {T : ℝ} (hT : 0 < T) :
    LinearSystems.IsHurwitz A ↔ SchurStable (NormedSpace.exp (T • A)) := by
  constructor
  · intro hA
    rw [schurStable_iff_spectralRadius_lt_one, MatrixAlgebra.complexification_exp]
    exact LinearSystems.spectralRadius_exp_complexification_lt_one (isHurwitz_smul hA hT)
  · intro hS μ v hv heig
    have h := Periodic.monodromy_const_mulVec_eigen A hT.le 0 heig
    rw [Periodic.monodromy_const A hT.le] at h
    have h1 := hS _ v hv h
    rw [Periodic.norm_exp_mul_eq] at h1
    have h2 : μ.re * T < 0 := Real.exp_lt_one_iff.mp h1
    simp only [neg_zero]
    exact (mul_neg_iff.mp h2).elim (fun h => absurd h.2 (not_lt.mpr hT.le)) (fun h => h.1)

end Spectral

/-! ## Exact zero-order-hold discretization -/

section ZOH

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-- Exact zero-order-hold input matrix `Γ(T) = ∫₀ᵀ e^{sA} B ds` (the state matrix is
`Φ(T) = e^{TA}`). -/
def zohGamma (T : ℝ) (A : Matrix X X ℝ) (B : Matrix X U ℝ) : Matrix X U ℝ :=
  ∫ s in (0 : ℝ)..T, NormedSpace.exp (s • A) * B

/-- `s ↦ e^{sA} B` has derivative `A e^{sA} B`. -/
@[powerlib_foundation] theorem hasDerivAt_exp_smul_mul (A : Matrix X X ℝ) (B : Matrix X U ℝ)
    (s : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * B) (A * NormedSpace.exp (s • A) * B) s := by
  let L : Matrix X X ℝ →L[ℝ] Matrix X U ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun N => N * B
        map_add' := fun N N' => Matrix.add_mul N N' B
        map_smul' := fun c N => Matrix.smul_mul c N B }
  have h := L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s)
  exact h

@[powerlib_foundation]
private lemma continuous_exp_smul_mul (A : Matrix X X ℝ) (B : Matrix X U ℝ) :
    Continuous fun s : ℝ => NormedSpace.exp (s • A) * B :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_mul A B s).continuousAt

/-- `A Γ(s) + B = e^{sA} B`. -/
@[powerlib_foundation] theorem mul_zohGamma_add (A : Matrix X X ℝ) (B : Matrix X U ℝ) (s : ℝ) :
    A * zohGamma s A B + B = NormedSpace.exp (s • A) * B := by
  let L : Matrix X U ℝ →L[ℝ] Matrix X U ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun N => A * N
        map_add' := fun N N' => Matrix.mul_add A N N'
        map_smul' := fun c N => Matrix.mul_smul A c N }
  have hcont := continuous_exp_smul_mul A B
  have h1 : A * zohGamma s A B = ∫ σ in (0 : ℝ)..s, A * (NormedSpace.exp (σ • A) * B) :=
    (L.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 s)).symm
  have hd : ∀ σ ∈ uIcc (0 : ℝ) s, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * B)
      (A * (NormedSpace.exp (σ • A) * B)) σ := by
    intro σ _
    rw [← Matrix.mul_assoc]
    exact hasDerivAt_exp_smul_mul A B σ
  have hc2 : Continuous fun σ : ℝ => A * (NormedSpace.exp (σ • A) * B) := L.continuous.comp hcont
  rw [h1, intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.intervalIntegrable 0 s)]
  simp

/-- The explicit ZOH solution solves `ẏ = A y + B u`. -/
@[powerlib_foundation]
private lemma hasDerivAt_zohSolution (A : Matrix X X ℝ) (B : Matrix X U ℝ) (u : U → ℝ)
    (a : ℝ) (x₀ : X → ℝ) (t : ℝ) :
    HasDerivAt (fun t => NormedSpace.exp ((t - a) • A) *ᵥ x₀ + zohGamma (t - a) A B *ᵥ u)
      (A *ᵥ (NormedSpace.exp ((t - a) • A) *ᵥ x₀ + zohGamma (t - a) A B *ᵥ u) + B *ᵥ u) t := by
  have h1 := Averaging.hasDerivAt_exp_mulVec A a x₀ t
  have hG : HasDerivAt (fun s => zohGamma s A B) (NormedSpace.exp ((t - a) • A) * B) (t - a) :=
    ((continuous_exp_smul_mul A B).integral_hasStrictDerivAt 0 (t - a)).hasDerivAt
  have hG' := hG.scomp t ((hasDerivAt_id t).sub_const a)
  simp only [Function.comp_def, id, one_smul] at hG'
  let L : Matrix X U ℝ →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun N => N *ᵥ u
        map_add' := fun N N' => Matrix.add_mulVec N N' u
        map_smul' := fun c N => Matrix.smul_mulVec c N u }
  have h2 := L.hasFDerivAt.comp_hasDerivAt t hG'
  change HasDerivAt (fun t => zohGamma (t - a) A B *ᵥ u)
    ((NormedSpace.exp ((t - a) • A) * B) *ᵥ u) t at h2
  convert h1.add h2 using 1
  rw [Matrix.mulVec_add, add_assoc]
  congr 1
  rw [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, mul_zohGamma_add]

/-- **Exact ZOH solution.** On an interval where the input is held at `u`, every solution of
`ẋ = A x + B u` is `x(t) = e^{(t − a)A} x(a) + Γ(t − a) u`. -/
@[powerlib_foundation] theorem zoh_solution {A : Matrix X X ℝ} {B : Matrix X U ℝ} {u : U → ℝ}
    {a b : ℝ} {x : ℝ → X → ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u) (Icc a b)) {t : ℝ}
    (ht : t ∈ Icc a b) :
    x t = NormedSpace.exp ((t - a) • A) *ᵥ x a + zohGamma (t - a) A B *ᵥ u := by
  have hy : IsIntegralCurveOn
      (fun t => NormedSpace.exp ((t - a) • A) *ᵥ x a + zohGamma (t - a) A B *ᵥ u)
      (fun _ y => A *ᵥ y + B *ᵥ u) (Icc a b) :=
    fun r _ => (hasDerivAt_zohSolution A B u a (x a) r).hasDerivWithinAt
  have hlip : ∀ s : ℝ, LipschitzWith (Real.toNNReal ‖A‖)
      ((fun (_ : ℝ) (y : X → ℝ) => A *ᵥ y + B *ᵥ u) s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← Matrix.mulVec_sub,
      Real.coe_toNNReal _ (norm_nonneg _)]
    exact Matrix.linfty_opNorm_mulVec _ _
  exact _root_.eqOn_of_isIntegralCurveOn_Icc hlip hx hy (by simp [zohGamma]) ht

/-- **Exact ZOH step.** If the input is held at `u` on `[a, a + T]`, then
`x(a + T) = e^{TA} x(a) + Γ(T) u`. -/
@[powerlib_foundation] theorem zoh_step {A : Matrix X X ℝ} {B : Matrix X U ℝ} {u : U → ℝ}
    {a T : ℝ} (hT : 0 ≤ T) {x : ℝ → X → ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u) (Icc a (a + T))) :
    x (a + T) = NormedSpace.exp (T • A) *ᵥ x a + zohGamma T A B *ᵥ u := by
  have h := zoh_solution hx (t := a + T) ⟨by linarith, le_rfl⟩
  rwa [add_sub_cancel_left] at h

/-- Uniform bounds on `[0, T]` for `e^{sA}` and `Γ(s)`. -/
@[powerlib_foundation]
private lemma exists_zoh_bounds (A : Matrix X X ℝ) (B : Matrix X U ℝ) (T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp (s • A)‖ ≤ K ∧ ‖zohGamma s A B‖ ≤ K := by
  have hE : Continuous fun s : ℝ => NormedSpace.exp (s • A) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s).continuousAt
  have hG : Continuous fun s : ℝ => zohGamma s A B :=
    continuous_iff_continuousAt.2 fun s =>
      ((continuous_exp_smul_mul A B).integral_hasStrictDerivAt 0 s).hasDerivAt.continuousAt
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun s : ℝ => NormedSpace.exp (s • A)) (s := Icc (0 : ℝ) T) hE.continuousOn
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun s : ℝ => zohGamma s A B) (s := Icc (0 : ℝ) T) hG.continuousOn
  refine ⟨max (max K₁ K₂) 0, le_max_right _ _, fun s hs =>
    ⟨(hK₁ s hs).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hK₂ s hs).trans ((le_max_right _ _).trans (le_max_left _ _))⟩⟩

end ZOH

/-! ## Sampled-data loops -/

section SampledData

variable {X U Z : Type*} [Fintype X] [DecidableEq X] [Fintype U] [Fintype Z] [DecidableEq Z]

omit [DecidableEq X] in
@[powerlib_foundation]
private lemma norm_sumElim_le {Y : Type*} [Fintype Y] (v : X → ℝ) (w : Y → ℝ) :
    ‖Sum.elim v w‖ ≤ ‖v‖ + ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  cases i with
  | inl i => exact (norm_le_pi_norm v i).trans (le_add_of_nonneg_right (norm_nonneg _))
  | inr i => exact (norm_le_pi_norm w i).trans (le_add_of_nonneg_left (norm_nonneg _))

omit [DecidableEq X] in
@[powerlib_foundation]
private lemma norm_le_norm_sumElim_left {Y : Type*} [Fintype Y] (v : X → ℝ) (w : Y → ℝ) :
    ‖v‖ ≤ ‖Sum.elim v w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (Sum.elim v w) (Sum.inl i)

omit [DecidableEq X] in
@[powerlib_foundation]
private lemma norm_le_norm_sumElim_right {Y : Type*} [Fintype Y] (v : X → ℝ) (w : Y → ℝ) :
    ‖w‖ ≤ ‖Sum.elim v w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (Sum.elim v w) (Sum.inr i)

/-- Lifted matrix of the sampled-data loop (plant `ẋ = A x + B u` behind a zero-order hold of
period `T`, discrete controller `ξ⁺ = A_c ξ + B_c x(kT)`, `u_k = C_c ξ_k + D_c x(kT)`), acting on
the sampled state `(x(kT), ξ_k)`: `[[Φ + Γ D_c, Γ C_c], [B_c, A_c]]`. -/
def sampledLoopMatrix (T : ℝ) (A : Matrix X X ℝ) (B : Matrix X U ℝ) (Ac : Matrix Z Z ℝ)
    (Bc : Matrix Z X ℝ) (Cc : Matrix U Z ℝ) (Dc : Matrix U X ℝ) : Matrix (X ⊕ Z) (X ⊕ Z) ℝ :=
  Matrix.fromBlocks (NormedSpace.exp (T • A) + zohGamma T A B * Dc) (zohGamma T A B * Cc) Bc Ac

/-- **Sampled-data loop at the sampling instants.** Every trajectory of the sampled-data loop
satisfies `(x(kT), ξ_k) = M^k (x(0), ξ_0)` with `M = sampledLoopMatrix`. -/
@[powerlib_foundation] theorem sampledLoop_sample {T : ℝ} (hT : 0 ≤ T) {A : Matrix X X ℝ}
    {B : Matrix X U ℝ} {Ac : Matrix Z Z ℝ} {Bc : Matrix Z X ℝ} {Cc : Matrix U Z ℝ}
    {Dc : Matrix U X ℝ} {x : ℝ → X → ℝ} {ξ : ℕ → Z → ℝ} {u : ℕ → U → ℝ}
    (hx : ∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k)
      (Icc (k * T) ((k + 1) * T)))
    (hξ : ∀ k : ℕ, ξ (k + 1) = Ac *ᵥ ξ k + Bc *ᵥ x (k * T))
    (hu : ∀ k : ℕ, u k = Cc *ᵥ ξ k + Dc *ᵥ x (k * T)) (k : ℕ) :
    Sum.elim (x (k * T)) (ξ k) =
      sampledLoopMatrix T A B Ac Bc Cc Dc ^ k *ᵥ Sum.elim (x 0) (ξ 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hxk : IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k)
        (Icc ((k : ℝ) * T) ((k : ℝ) * T + T)) := by
      have e : (k : ℝ) * T + T = ((k : ℝ) + 1) * T := by ring
      rw [e]
      exact hx k
    have hstep := zoh_step hT hxk
    rw [show (k : ℝ) * T + T = ((k : ℝ) + 1) * T by ring] at hstep
    push_cast
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, sampledLoopMatrix, Matrix.fromBlocks_mulVec,
      hξ k, hstep, hu k]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    · simp only [Matrix.mulVec_add, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
      abel
    · rw [add_comm]

/-- **Lifted-matrix stability gives exponential decay of the sampled-data loop, between samples
included.** If the lifted matrix `M` has spectral radius `< 1` (for `Fin`-indexed matrices this
is `SchurStable`, `schurStable_iff_spectralRadius_lt_one`), there are `C, a > 0` such that every
trajectory of the sampled-data loop satisfies `‖x(t)‖ ≤ C e^{−at} (‖x(0)‖ + ‖ξ_0‖)` for all
`t ≥ 0` and `‖ξ_k‖ ≤ C e^{−a kT} (‖x(0)‖ + ‖ξ_0‖)`. -/
@[powerlib_foundation] theorem sampledLoop_exponentialDecay {T : ℝ} (hT : 0 < T)
    {A : Matrix X X ℝ} {B : Matrix X U ℝ} {Ac : Matrix Z Z ℝ} {Bc : Matrix Z X ℝ}
    {Cc : Matrix U Z ℝ} {Dc : Matrix U X ℝ}
    (hM : spectralRadius ℂ ((sampledLoopMatrix T A B Ac Bc Cc Dc).map (algebraMap ℝ ℂ)) < 1) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ (x : ℝ → X → ℝ) (ξ : ℕ → Z → ℝ) (u : ℕ → U → ℝ),
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k)
        (Icc (k * T) ((k + 1) * T))) →
      (∀ k : ℕ, ξ (k + 1) = Ac *ᵥ ξ k + Bc *ᵥ x (k * T)) →
      (∀ k : ℕ, u k = Cc *ᵥ ξ k + Dc *ᵥ x (k * T)) →
      (∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(a * t)) * (‖x 0‖ + ‖ξ 0‖)) ∧
      ∀ k : ℕ, ‖ξ k‖ ≤ C * Real.exp (-(a * (k * T))) * (‖x 0‖ + ‖ξ 0‖) := by
  set M := sampledLoopMatrix T A B Ac Bc Cc Dc
  obtain ⟨m, hm, hlt⟩ := exists_pow_norm_lt_one M hM
  obtain ⟨C₀, γ, hC₀, hγ, hpow⟩ := exists_pow_norm_le_exp hm hlt
  obtain ⟨K, hK0, hK⟩ := exists_zoh_bounds A B T
  set K' := K + K * (‖Cc‖ + ‖Dc‖) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hCbig : C₀ ≤ (K' + 1) * C₀ * Real.exp γ + 1 := by
    have h1 : 1 ≤ Real.exp γ := Real.one_le_exp hγ.le
    have h2 : 1 ≤ (K' + 1) * Real.exp γ := by nlinarith
    have h3 : C₀ ≤ (K' + 1) * Real.exp γ * C₀ := le_mul_of_one_le_left hC₀ h2
    linarith
  refine ⟨(K' + 1) * C₀ * Real.exp γ + 1, γ / T, by positivity, div_pos hγ hT, ?_⟩
  intro x ξ u hx hξ hu
  set N := ‖x 0‖ + ‖ξ 0‖ with hN
  have hN0 : 0 ≤ N := by positivity
  have hz : ∀ k : ℕ, ‖Sum.elim (x (k * T)) (ξ k)‖ ≤ C₀ * Real.exp (-(γ * k)) * N := by
    intro k
    rw [sampledLoop_sample hT.le hx hξ hu k]
    calc ‖M ^ k *ᵥ Sum.elim (x 0) (ξ 0)‖ ≤ ‖M ^ k‖ * ‖Sum.elim (x 0) (ξ 0)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ ≤ C₀ * Real.exp (-(γ * k)) * N :=
          mul_le_mul (hpow k) (norm_sumElim_le _ _) (norm_nonneg _) (by positivity)
  constructor
  · intro t ht
    set k := ⌊t / T⌋₊ with hkdef
    have hk1 : (k : ℝ) * T ≤ t := by
      have := Nat.floor_le (div_nonneg ht hT.le)
      rwa [le_div_iff₀ hT] at this
    have hk2 : t < ((k : ℝ) + 1) * T := by
      have := Nat.lt_floor_add_one (t / T)
      rwa [div_lt_iff₀ hT] at this
    have hsol := zoh_solution (hx k) (t := t) ⟨hk1, hk2.le⟩
    have hs : t - k * T ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
    obtain ⟨hE, hG⟩ := hK _ hs
    have hzk := hz k
    have hxk : ‖x (k * T)‖ ≤ ‖Sum.elim (x (k * T)) (ξ k)‖ := norm_le_norm_sumElim_left _ _
    have hξk : ‖ξ k‖ ≤ ‖Sum.elim (x (k * T)) (ξ k)‖ := norm_le_norm_sumElim_right _ _
    have huk : ‖u k‖ ≤ (‖Cc‖ + ‖Dc‖) * ‖Sum.elim (x (k * T)) (ξ k)‖ := by
      rw [hu k]
      calc ‖Cc *ᵥ ξ k + Dc *ᵥ x (k * T)‖ ≤ ‖Cc‖ * ‖ξ k‖ + ‖Dc‖ * ‖x (k * T)‖ :=
            (norm_add_le _ _).trans
              (add_le_add (Matrix.linfty_opNorm_mulVec _ _) (Matrix.linfty_opNorm_mulVec _ _))
        _ ≤ ‖Cc‖ * ‖Sum.elim (x (k * T)) (ξ k)‖ + ‖Dc‖ * ‖Sum.elim (x (k * T)) (ξ k)‖ := by
            gcongr
        _ = (‖Cc‖ + ‖Dc‖) * ‖Sum.elim (x (k * T)) (ξ k)‖ := by ring
    have hxt : ‖x t‖ ≤ K' * ‖Sum.elim (x (k * T)) (ξ k)‖ := by
      rw [hsol]
      calc ‖NormedSpace.exp ((t - k * T) • A) *ᵥ x (k * T) + zohGamma (t - k * T) A B *ᵥ u k‖
          ≤ ‖NormedSpace.exp ((t - k * T) • A)‖ * ‖x (k * T)‖ +
              ‖zohGamma (t - k * T) A B‖ * ‖u k‖ :=
            (norm_add_le _ _).trans
              (add_le_add (Matrix.linfty_opNorm_mulVec _ _) (Matrix.linfty_opNorm_mulVec _ _))
        _ ≤ K * ‖Sum.elim (x (k * T)) (ξ k)‖ +
              K * ((‖Cc‖ + ‖Dc‖) * ‖Sum.elim (x (k * T)) (ξ k)‖) := by
            gcongr
        _ = K' * ‖Sum.elim (x (k * T)) (ξ k)‖ := by rw [hK']; ring
    have hexp : Real.exp (-(γ * k)) ≤ Real.exp γ * Real.exp (-(γ / T * t)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : t / T < k + 1 := by rw [div_lt_iff₀ hT]; linarith
      have h2 : γ / T * t = γ * (t / T) := by ring
      rw [h2]
      nlinarith
    have hP : 0 ≤ C₀ * Real.exp γ * Real.exp (-(γ / T * t)) * N := by positivity
    have hQ : 0 ≤ Real.exp (-(γ / T * t)) * N := by positivity
    calc ‖x t‖ ≤ K' * ‖Sum.elim (x (k * T)) (ξ k)‖ := hxt
      _ ≤ K' * (C₀ * Real.exp (-(γ * k)) * N) := mul_le_mul_of_nonneg_left hzk hK'0
      _ ≤ K' * (C₀ * (Real.exp γ * Real.exp (-(γ / T * t))) * N) := by gcongr
      _ ≤ ((K' + 1) * C₀ * Real.exp γ + 1) * Real.exp (-(γ / T * t)) * N := by
          nlinarith
  · intro k
    have hξk : ‖ξ k‖ ≤ ‖Sum.elim (x (k * T)) (ξ k)‖ := norm_le_norm_sumElim_right _ _
    have he : γ / T * ((k : ℝ) * T) = γ * k := by
      have := hT.ne'
      field_simp
    rw [he]
    calc ‖ξ k‖ ≤ C₀ * Real.exp (-(γ * k)) * N := hξk.trans (hz k)
      _ ≤ ((K' + 1) * C₀ * Real.exp γ + 1) * Real.exp (-(γ * k)) * N := by gcongr

/-- **Existence of sampled-data trajectories.** Every initial state `(x(0), ξ_0)` starts a
trajectory of the sampled-data loop. -/
@[powerlib_foundation] theorem sampledLoop_exists_trajectory {T : ℝ} (hT : 0 < T)
    (A : Matrix X X ℝ) (B : Matrix X U ℝ) (Ac : Matrix Z Z ℝ) (Bc : Matrix Z X ℝ)
    (Cc : Matrix U Z ℝ) (Dc : Matrix U X ℝ) (x₀ : X → ℝ) (ξ₀ : Z → ℝ) :
    ∃ (x : ℝ → X → ℝ) (ξ : ℕ → Z → ℝ) (u : ℕ → U → ℝ), x 0 = x₀ ∧ ξ 0 = ξ₀ ∧
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k)
        (Icc (k * T) ((k + 1) * T))) ∧
      (∀ k : ℕ, ξ (k + 1) = Ac *ᵥ ξ k + Bc *ᵥ x (k * T)) ∧
      (∀ k : ℕ, u k = Cc *ᵥ ξ k + Dc *ᵥ x (k * T)) := by
  obtain ⟨z, hz⟩ : ∃ z : ℕ → X ⊕ Z → ℝ,
      ∀ k, z k = sampledLoopMatrix T A B Ac Bc Cc Dc ^ k *ᵥ Sum.elim x₀ ξ₀ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → U → ℝ,
      ∀ k, u k = Cc *ᵥ (z k ∘ Sum.inr) + Dc *ᵥ (z k ∘ Sum.inl) := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ → X → ℝ, ∀ k t, y k t =
      NormedSpace.exp ((t - k * T) • A) *ᵥ (z k ∘ Sum.inl) + zohGamma (t - k * T) A B *ᵥ u k :=
    ⟨_, fun _ _ => rfl⟩
  have hzs : ∀ k : ℕ, z (k + 1) = Sum.elim
      ((NormedSpace.exp (T • A) + zohGamma T A B * Dc) *ᵥ (z k ∘ Sum.inl) +
        (zohGamma T A B * Cc) *ᵥ (z k ∘ Sum.inr))
      (Bc *ᵥ (z k ∘ Sum.inl) + Ac *ᵥ (z k ∘ Sum.inr)) := by
    intro k
    rw [hz (k + 1), pow_succ', ← Matrix.mulVec_mulVec, ← hz k, sampledLoopMatrix,
      Matrix.fromBlocks_mulVec]
  have hxs : ∀ k : ℕ, z (k + 1) ∘ Sum.inl = y k (((k : ℝ) + 1) * T) := by
    intro k
    rw [hzs k, Sum.elim_comp_inl, hy, show ((k : ℝ) + 1) * T - k * T = T by ring, hu k]
    simp only [Matrix.add_mulVec, Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    abel
  have hy0 : ∀ k : ℕ, y k (k * T) = z k ∘ Sum.inl := by
    intro k
    rw [hy]
    simp [zohGamma]
  have hfl : ∀ (k : ℕ) (t : ℝ), (k : ℝ) * T ≤ t → t < ((k : ℝ) + 1) * T → ⌊t / T⌋₊ = k := by
    intro k t h1 h2
    have h0 : 0 ≤ t / T := div_nonneg ((by positivity : (0 : ℝ) ≤ k * T).trans h1) hT.le
    rw [Nat.floor_eq_iff h0, le_div_iff₀ hT, div_lt_iff₀ hT]
    exact ⟨h1, h2⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ → X → ℝ, ∀ t, x t = y ⌊t / T⌋₊ t := ⟨_, fun _ => rfl⟩
  have hxk : ∀ k : ℕ, x (k * T) = z k ∘ Sum.inl := by
    intro k
    rw [hx, hfl k (k * T) le_rfl (by nlinarith), hy0]
  have heq : ∀ k : ℕ, ∀ t ∈ Icc ((k : ℝ) * T) (((k : ℝ) + 1) * T), x t = y k t := by
    intro k t ht
    rcases lt_or_eq_of_le ht.2 with h | h
    · rw [hx, hfl k t ht.1 h]
    · rw [h, ← hxs k]
      have := hxk (k + 1)
      push_cast at this
      exact this
  have hcurve : ∀ k : ℕ, IsIntegralCurveOn x (fun _ v => A *ᵥ v + B *ᵥ u k)
      (Icc (k * T) ((k + 1) * T)) := by
    intro k t ht
    have hd := (hasDerivAt_zohSolution A B (u k) (k * T) (z k ∘ Sum.inl) t).hasDerivWithinAt
      (s := Icc ((k : ℝ) * T) (((k : ℝ) + 1) * T))
    have hfun : (fun t => NormedSpace.exp ((t - k * T) • A) *ᵥ (z k ∘ Sum.inl) +
        zohGamma (t - k * T) A B *ᵥ u k) = y k := funext fun t => (hy k t).symm
    rw [hfun, ← hy k t, ← heq k t ht] at hd
    exact hd.congr (fun s hs => heq k s hs) (heq k t ht)
  refine ⟨x, fun k => z k ∘ Sum.inr, u, ?_, ?_, hcurve, ?_, ?_⟩
  · have := hxk 0
    simp only [Nat.cast_zero, zero_mul] at this
    rw [this, hz 0, pow_zero, Matrix.one_mulVec, Sum.elim_comp_inl]
  · show z 0 ∘ Sum.inr = ξ₀
    rw [hz 0, pow_zero, Matrix.one_mulVec, Sum.elim_comp_inr]
  · intro k
    show z (k + 1) ∘ Sum.inr = Ac *ᵥ (z k ∘ Sum.inr) + Bc *ᵥ x (k * T)
    rw [hzs k, Sum.elim_comp_inr, hxk k, add_comm]
  · intro k
    show u k = Cc *ᵥ (z k ∘ Sum.inr) + Dc *ᵥ x (k * T)
    rw [hu k, hxk k]

@[powerlib_foundation]
private lemma norm_le_sum_entries {Y : Type*} [Fintype Y] (P : Matrix Y Y ℝ) :
    ‖P‖ ≤ ∑ i, ∑ j, ‖P i j‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h : (Finset.univ.sup fun i => ∑ j, ‖P i j‖₊) ≤ ∑ i, ∑ j, ‖P i j‖₊ :=
    Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖P i j‖₊)
      (fun _ _ => zero_le) (Finset.mem_univ i)
  have h' : ((Finset.univ.sup fun i => ∑ j, ‖P i j‖₊ : NNReal) : ℝ) ≤
      ((∑ i, ∑ j, ‖P i j‖₊ : NNReal) : ℝ) := by exact_mod_cast h
  exact h'.trans (le_of_eq (by simp))

/-- **Converse: sampled convergence forces lifted-matrix stability.** If every trajectory of the
sampled-data loop has `x(kT) → 0` and `ξ_k → 0`, the lifted matrix has spectral radius `< 1`. -/
@[powerlib_foundation] theorem spectralRadius_lt_one_of_sampledLoop {T : ℝ} (hT : 0 < T)
    {A : Matrix X X ℝ} {B : Matrix X U ℝ} {Ac : Matrix Z Z ℝ} {Bc : Matrix Z X ℝ}
    {Cc : Matrix U Z ℝ} {Dc : Matrix U X ℝ}
    (h : ∀ (x : ℝ → X → ℝ) (ξ : ℕ → Z → ℝ) (u : ℕ → U → ℝ),
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k)
        (Icc (k * T) ((k + 1) * T))) →
      (∀ k : ℕ, ξ (k + 1) = Ac *ᵥ ξ k + Bc *ᵥ x (k * T)) →
      (∀ k : ℕ, u k = Cc *ᵥ ξ k + Dc *ᵥ x (k * T)) →
      Tendsto (fun k : ℕ => x (k * T)) atTop (𝓝 0) ∧ Tendsto ξ atTop (𝓝 0)) :
    spectralRadius ℂ ((sampledLoopMatrix T A B Ac Bc Cc Dc).map (algebraMap ℝ ℂ)) < 1 := by
  obtain ⟨M, hM⟩ : ∃ M, M = sampledLoopMatrix T A B Ac Bc Cc Dc := ⟨_, rfl⟩
  rw [← hM]
  have hv : ∀ v : X ⊕ Z → ℝ, Tendsto (fun k : ℕ => M ^ k *ᵥ v) atTop (𝓝 0) := by
    intro v
    obtain ⟨x, ξ, u, hx0, hξ0, hx, hξ, hu⟩ :=
      sampledLoop_exists_trajectory hT A B Ac Bc Cc Dc (v ∘ Sum.inl) (v ∘ Sum.inr)
    obtain ⟨h1, h2⟩ := h x ξ u hx hξ hu
    have hs := sampledLoop_sample hT.le hx hξ hu
    have hv' : Sum.elim (x 0) (ξ 0) = v := by rw [hx0, hξ0]; exact Sum.elim_comp_inl_inr v
    have hfun : (fun k : ℕ => M ^ k *ᵥ v) = fun k : ℕ => Sum.elim (x (k * T)) (ξ k) := by
      funext k; rw [hs k, hv', hM]
    rw [hfun]
    refine tendsto_pi_nhds.2 fun i => ?_
    rcases i with i | i
    · simpa [Function.comp_def] using ((continuous_apply i).tendsto 0).comp h1
    · simpa [Function.comp_def] using ((continuous_apply i).tendsto 0).comp h2
  have hent : ∀ i j, Tendsto (fun k : ℕ => ‖(M ^ k) i j‖) atTop (𝓝 0) := by
    intro i j
    have h3 := (continuous_norm.tendsto _).comp
      (((continuous_apply i).tendsto _).comp (hv (Pi.single j 1)))
    simpa [Function.comp_def, Matrix.mulVec_single_one] using h3
  have hsum : Tendsto (fun k : ℕ => ∑ i, ∑ j, ‖(M ^ k) i j‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (X ⊕ Z)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (X ⊕ Z)) fun j _ => hent i j
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∑ i, ∑ j, ‖(M ^ (k + 1)) i j‖ < 1 := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds zero_lt_one))
    exact ⟨N, hN (N + 1) (Nat.le_succ N)⟩
  have hnorm : ‖M ^ (k + 1)‖ < 1 := (norm_le_sum_entries _).trans_lt hk
  rcases isEmpty_or_nonempty (X ⊕ Z) with hE | hE
  · rw [Subsingleton.elim (M.map (algebraMap ℝ ℂ)) 0, spectrum.spectralRadius_zero]
    exact zero_lt_one
  · have hn : ‖(M.map (algebraMap ℝ ℂ)) ^ (k + 1)‖ < 1 := by
      rw [← Matrix.map_pow, norm_map_algebraMap]
      exact hnorm
    have hn' : ‖(M.map (algebraMap ℝ ℂ)) ^ (k + 1)‖₊ < 1 := by
      rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact hn
    have hb := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ (M.map (algebraMap ℝ ℂ)) k
    rw [nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow, mul_one] at hb
    exact hb.trans_lt (ENNReal.rpow_lt_one (ENNReal.coe_lt_one_iff.2 hn') (by positivity))

/-- **Lifted-matrix stability is exact for sampled-data loops.** Uniform exponential decay of
every trajectory (state between samples and controller state) holds exactly when the lifted
matrix has spectral radius `< 1`. -/
@[powerlib_foundation] theorem sampledLoop_exponentialDecay_iff {T : ℝ} (hT : 0 < T)
    {A : Matrix X X ℝ} {B : Matrix X U ℝ} {Ac : Matrix Z Z ℝ} {Bc : Matrix Z X ℝ}
    {Cc : Matrix U Z ℝ} {Dc : Matrix U X ℝ} :
    (∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ (x : ℝ → X → ℝ) (ξ : ℕ → Z → ℝ) (u : ℕ → U → ℝ),
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k)
        (Icc (k * T) ((k + 1) * T))) →
      (∀ k : ℕ, ξ (k + 1) = Ac *ᵥ ξ k + Bc *ᵥ x (k * T)) →
      (∀ k : ℕ, u k = Cc *ᵥ ξ k + Dc *ᵥ x (k * T)) →
      (∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(a * t)) * (‖x 0‖ + ‖ξ 0‖)) ∧
      ∀ k : ℕ, ‖ξ k‖ ≤ C * Real.exp (-(a * (k * T))) * (‖x 0‖ + ‖ξ 0‖)) ↔
    spectralRadius ℂ ((sampledLoopMatrix T A B Ac Bc Cc Dc).map (algebraMap ℝ ℂ)) < 1 := by
  refine ⟨fun ⟨C, a, _, ha, hdec⟩ => spectralRadius_lt_one_of_sampledLoop hT
    fun x ξ u hx hξ hu => ?_, sampledLoop_exponentialDecay hT⟩
  obtain ⟨h1, h2⟩ := hdec x ξ u hx hξ hu
  have hlim : Tendsto (fun k : ℕ => C * Real.exp (-(a * (k * T))) * (‖x 0‖ + ‖ξ 0‖)) atTop
      (𝓝 0) := by
    have hlin : Tendsto (fun k : ℕ => a * ((k : ℝ) * T)) atTop atTop :=
      Tendsto.const_mul_atTop ha (Tendsto.atTop_mul_const hT tendsto_natCast_atTop_atTop)
    have he : Tendsto (fun k : ℕ => Real.exp (-(a * (k * T)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    simpa using (he.const_mul C).mul_const (‖x 0‖ + ‖ξ 0‖)
  exact ⟨squeeze_zero_norm (fun k => h1 (k * T) (by positivity)) hlim,
    squeeze_zero_norm (fun k => h2 k) hlim⟩

/-- Lifted matrix of the sampled-data loop with a one-sample computation delay: the output
`C_c ξ_k + D_c x(kT)` computed at `kT` is applied on `[(k+1)T, (k+2)T]`. The controller state is
augmented by the held output, `(ξ_k, u_k)`. -/
def delayedLoopMatrix [DecidableEq U] (T : ℝ) (A : Matrix X X ℝ) (B : Matrix X U ℝ)
    (Ac : Matrix Z Z ℝ) (Bc : Matrix Z X ℝ) (Cc : Matrix U Z ℝ) (Dc : Matrix U X ℝ) :
    Matrix (X ⊕ (Z ⊕ U)) (X ⊕ (Z ⊕ U)) ℝ :=
  sampledLoopMatrix T A B (Matrix.fromBlocks Ac 0 Cc 0) (Matrix.fromRows Bc Dc)
    (Matrix.fromCols 0 1) 0

/-- **Sampled-data loop with one-sample computation delay.** If the lifted matrix of the delayed
loop has spectral radius `< 1`, every trajectory with `u_{k+1} = C_c ξ_k + D_c x(kT)` (input
`u_k` held on `[kT, (k+1)T]`) satisfies `‖x(t)‖ ≤ C e^{−at} (‖x(0)‖ + ‖ξ_0‖ + ‖u_0‖)`. -/
@[powerlib_foundation] theorem delayedLoop_exponentialDecay [DecidableEq U] {T : ℝ} (hT : 0 < T)
    {A : Matrix X X ℝ} {B : Matrix X U ℝ} {Ac : Matrix Z Z ℝ} {Bc : Matrix Z X ℝ}
    {Cc : Matrix U Z ℝ} {Dc : Matrix U X ℝ}
    (hM : spectralRadius ℂ ((delayedLoopMatrix T A B Ac Bc Cc Dc).map (algebraMap ℝ ℂ)) < 1) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ (x : ℝ → X → ℝ) (ξ : ℕ → Z → ℝ) (u : ℕ → U → ℝ),
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A *ᵥ y + B *ᵥ u k)
        (Icc (k * T) ((k + 1) * T))) →
      (∀ k : ℕ, ξ (k + 1) = Ac *ᵥ ξ k + Bc *ᵥ x (k * T)) →
      (∀ k : ℕ, u (k + 1) = Cc *ᵥ ξ k + Dc *ᵥ x (k * T)) →
      ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(a * t)) * (‖x 0‖ + ‖ξ 0‖ + ‖u 0‖) := by
  obtain ⟨C, a, hC, ha, h⟩ := sampledLoop_exponentialDecay (Ac := Matrix.fromBlocks Ac 0 Cc 0)
    (Bc := Matrix.fromRows Bc Dc) (Cc := Matrix.fromCols 0 1) (Dc := 0) hT hM
  refine ⟨C, a, hC, ha, fun x ξ u hx hξ hu t ht => ?_⟩
  have hξ' : ∀ k : ℕ, Sum.elim (ξ (k + 1)) (u (k + 1)) =
      Matrix.fromBlocks Ac 0 Cc 0 *ᵥ Sum.elim (ξ k) (u k) +
        Matrix.fromRows Bc Dc *ᵥ x (k * T) := by
    intro k
    funext i
    rcases i with i | i <;> simp [hξ k, hu k, Matrix.fromBlocks_mulVec]
  have hu' : ∀ k : ℕ, u k = Matrix.fromCols 0 1 *ᵥ Sum.elim (ξ k) (u k) + 0 *ᵥ x (k * T) := by
    intro k
    simp
  have h' := (h x (fun k => Sum.elim (ξ k) (u k)) u hx hξ' hu').1 t ht
  have hs := norm_sumElim_le (ξ 0) (u 0)
  calc ‖x t‖ ≤ C * Real.exp (-(a * t)) * (‖x 0‖ + ‖Sum.elim (ξ 0) (u 0)‖) := h'
    _ ≤ C * Real.exp (-(a * t)) * (‖x 0‖ + ‖ξ 0‖ + ‖u 0‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end SampledData

/-! ## Static evidence: an integrator behind a one-sample delay -/

section IntegratorDelay

/-- ZOH input matrix of the pure integrator `ẋ = B u`: `Γ(T) = T B`. -/
@[powerlib_foundation] theorem zohGamma_zero {X U : Type*} [Fintype X] [DecidableEq X]
    [Fintype U] (T : ℝ) (B : Matrix X U ℝ) : zohGamma T 0 B = T • B := by
  simp [zohGamma]

/-- **Integrator with a one-sample delay under a proportional gain.** The lifted matrix
`[[1, b], [−k, 0]]` (sampled state `(x(kT), u_k)`, exact ZOH of the integrator `x⁺ = x + b u`,
delayed proportional gain `u⁺ = −k x`) is Schur stable exactly when `0 < k b < 1`. -/
@[powerlib_foundation] theorem schurStable_integratorDelay_iff (b k : ℝ) :
    SchurStable !![1, b; -k, 0] ↔ 0 < k * b ∧ k * b < 1 := by
  constructor
  · intro hS
    have key : ∀ μ : ℂ, μ ≠ 0 → μ ^ 2 - μ + (k : ℂ) * b = 0 → ‖μ‖ < 1 := by
      intro μ hμ hroot
      apply hS μ ![μ, -k]
      · intro h0
        exact hμ (by simpa using congrFun h0 0)
      · ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
          first | linear_combination -hroot | linear_combination hroot | ring1
    by_cases hc : k * b ≤ 1 / 4
    · obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2 = 1 - 4 * (k * b) :=
        ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
      have hr : ((1 + s) / 2) ^ 2 - (1 + s) / 2 + k * b = 0 := by
        linear_combination (1 / 4 : ℝ) * hs
      have h := key (((1 + s) / 2 : ℝ) : ℂ) (by exact_mod_cast (by positivity : (1 + s) / 2 ≠ 0))
        (by exact_mod_cast hr)
      rw [Complex.norm_of_nonneg (by positivity)] at h
      constructor
      · nlinarith
      · linarith
    · replace hc := not_le.mp hc
      obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2 = k * b - 1 / 4 :=
        ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
      have hsC : (s : ℂ) ^ 2 = (k : ℂ) * b - 1 / 4 := by
        rw [← Complex.ofReal_pow, hs]
        push_cast
        ring
      have hμ0 : ((1 / 2 : ℝ) : ℂ) + s * Complex.I ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        norm_num at this
      have h := key (((1 / 2 : ℝ) : ℂ) + s * Complex.I) hμ0 (by
        push_cast
        linear_combination (s : ℂ) ^ 2 * Complex.I_sq - hsC)
      have h2 : ‖((1 / 2 : ℝ) : ℂ) + s * Complex.I‖ ^ 2 < 1 := by
        nlinarith [norm_nonneg (((1 / 2 : ℝ) : ℂ) + s * Complex.I)]
      rw [Complex.sq_norm, Complex.normSq_apply] at h2
      simp at h2
      constructor
      · linarith
      · nlinarith
  · rintro ⟨h0, h1⟩ μ v hv heig
    have e0 : v 0 + b * v 1 = μ * v 0 := by
      have := congrFun heig 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      linear_combination this
    have e1 : -(k * v 0) = μ * v 1 := by
      have := congrFun heig 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      linear_combination this
    have hv0 : v 0 ≠ 0 := by
      intro hz
      have hv1 : v 1 ≠ 0 := by
        intro hz1
        apply hv
        funext i
        fin_cases i
        · exact hz
        · exact hz1
      simp only [hz, mul_zero, zero_add] at e0
      have hb : (b : ℂ) = 0 := (mul_eq_zero.mp e0).resolve_right hv1
      have : b = 0 := by exact_mod_cast hb
      rw [this, mul_zero] at h0
      exact lt_irrefl _ h0
    have hq : (μ ^ 2 - μ + (k : ℂ) * b) * v 0 = 0 := by
      linear_combination (-μ) * e0 + (-(b : ℂ)) * e1
    have hq0 : μ ^ 2 - μ + (k : ℂ) * b = 0 := (mul_eq_zero.mp hq).resolve_right hv0
    have hre := congrArg Complex.re hq0
    have him := congrArg Complex.im hq0
    simp [pow_two] at hre him
    have hns : μ.re * μ.re + μ.im * μ.im < 1 := by
      have hfac : μ.im * (2 * μ.re - 1) = 0 := by linear_combination him
      rcases mul_eq_zero.mp hfac with hi | hr
      · rw [hi] at hre ⊢
        nlinarith
      · have : μ.re = 1 / 2 := by linarith
        rw [this] at hre ⊢
        nlinarith
    by_contra hge
    replace hge := not_lt.mp hge
    have : 1 ≤ ‖μ‖ ^ 2 := by nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    linarith

end IntegratorDelay

end powerlib.LTI
