import theorem.Periodic.Floquet
import theorem.Linear.EigenMap

/-! # The forced regime of a periodic linear system and its parametric boundary

A periodically varying linear system driven by a periodic input, `ẋ = A(t) x + f(t)`, has two
regimes separated by the spectral radius `ρ(M)` of its monodromy matrix `M = Φ(T, 0)`. In the
forced regime `ρ(M) < 1` the drive produces exactly one periodic response, given by the
Floquet–Green formula `x_p(0) = (I − M)⁻¹ ∫₀ᵀ Φ(T, s) f(s) ds`, and every solution converges to
it exponentially, uniformly in the initial time. In the parametric regime `ρ(M) > 1` the free
system has a Floquet mode `z(t + T) = μ z(t)` with `|μ| > 1` and a real solution that is
unbounded along the periods; no response whatever attracts all solutions. The boundary between
forced and parametric oscillation is therefore `ρ(M) = 1`.

Scope.
* `ẋ = A(t) x + f(t)` on `ℝ^X` (finite `X`, sup norm; operator `L∞` norm on matrices), with a
  continuous real `T`-periodic state matrix `A` (`T > 0`) and a continuous `T`-periodic input
  `f`; continuous time. The transition and monodromy matrices are those of
  `theorem/Periodic/Transition.lean`; the Floquet multipliers are the complex spectrum of the
  complexified monodromy matrix, `FloquetUnstable` is the predicate of
  `theorem/Periodic/Floquet.lean`.
* Global solutions are curves with `∀ t, HasDerivAt x (A t *ᵥ x t + f t) t`; forward solutions
  are integral curves on `[s, ∞)`. These solution conditions are written out in the statements.
* The constant case `A(t) ≡ A` is the LTI forced response
  (`ParametricResonance.forced_periodic_unique`,
  `ParametricResonance.ForcedOrbit.periodic_eq_green`); here `A` is arbitrary periodic, so the
  system may be a parametrically modulated one.
* Generic mathematics; no model family.

Source: the Floquet mechanism of periodic linear systems (Yakubovich–Starzhinskii, *Linear
Differential Equations with Periodic Coefficients*: monodromy, multipliers, the periodic
solution of the forced equation); IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023)
§3.1 (a forced oscillation is the response of a stable system to a periodic input, a natural one
a poorly damped mode). This module states where that forced regime ends when the parameters of
the system vary periodically.

Results.
* `forced_eq_variation`, `forced_eq_of_eq` — variation of constants for the forced equation
  (`Dynamics.eq_variationOfConstants_of_hasDerivAt` with input matrix `I`) and uniqueness of
  global solutions through one state.
* `periodForcing`, `greenInitial`, `periodicResponse`, `hasDerivAt_forcedResponse`,
  `periodicResponse_zero` — the Floquet–Green initial value and the global solution through it
  (LeanForControl's `forcedResponse`).
* `periodicResponse_periodic`, `periodic_eq_periodicResponse` — if `1` is not a Floquet
  multiplier (`det(I − M) ≠ 0`), the response is `T`-periodic and is the only `T`-periodic
  global solution.
* `isUnit_det_one_sub_monodromy` — `ρ(M) < 1` excludes the multiplier `1`.
* `forced_convergence`, `forced_regime` — for `ρ(M) < 1`: existence, the formula for `x_p(0)`,
  uniqueness among periodic solutions, and `‖x(t) − x_p(t)‖ ≤ K e^{−β(t − s)} ‖x(s) − x_p(s)‖`
  for every forward solution, `β > 0`.
* `transition_add_period_eq_mul`, `transition_mulVec_add_period`, `floquet_mode` —
  `Φ(t + T, 0) = Φ(t, 0) M` (`t ≥ 0`); an eigenvector of `M` (real or complex) starts a Floquet
  mode `z(t + T) = μ z(t)`.
* `floquetUnstable_iff_one_lt_spectralRadius` — `FloquetUnstable A T ↔ 1 < ρ(M)`.
* `exists_unbounded_of_floquetUnstable` — in the parametric regime some real initial state has
  `‖Φ(nT, 0) x₀‖` unbounded in `n`.
* `not_attracting_of_floquetUnstable` — in the parametric regime no curve `p` (in particular no
  bounded forced response) is approached by every global solution of the forced equation.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {f : ℝ → X → ℝ} {T : ℝ}

/-! ## Global solutions of the forced equation -/

/-- Variation of constants for `ẋ = A(t) x + f(t)`:
`x(t) = Φ(t, t₀) x(t₀) + ∫_{t₀}^{t} Φ(t, τ) f(τ) dτ` for every global solution. -/
@[tmio T, powerlib_foundation] theorem forced_eq_variation (hA : Continuous A)
    (hf : Continuous f) {x : ℝ → X → ℝ} (hx : ∀ t, HasDerivAt x (A t *ᵥ x t + f t) t)
    (t₀ t : ℝ) :
    x t = transition A t t₀ *ᵥ x t₀ + ∫ τ in t₀..t, transition A t τ *ᵥ f τ := by
  have h := Dynamics.eq_variationOfConstants_of_hasDerivAt (B := fun _ => (1 : Matrix X X ℝ))
    (u := f) hA continuous_const hf (x := x) (fun t => by simpa using hx t) t₀ t
  simpa using h

/-- Two global solutions of the forced equation that agree at one instant agree everywhere. -/
@[tmio T, powerlib_foundation] theorem forced_eq_of_eq (hA : Continuous A) (hf : Continuous f)
    {x y : ℝ → X → ℝ} (hx : ∀ t, HasDerivAt x (A t *ᵥ x t + f t) t)
    (hy : ∀ t, HasDerivAt y (A t *ᵥ y t + f t) t) {t₀ : ℝ} (h0 : x t₀ = y t₀) : x = y := by
  funext t
  rw [forced_eq_variation hA hf hx t₀ t, forced_eq_variation hA hf hy t₀ t, h0]

/-! ## The Floquet–Green periodic response -/

/-- The one-period forcing integral `∫₀ᵀ Φ(T, s) f(s) ds`. -/
def periodForcing (A : ℝ → Matrix X X ℝ) (f : ℝ → X → ℝ) (T : ℝ) : X → ℝ :=
  ∫ s in (0 : ℝ)..T, transition A T s *ᵥ f s

/-- The Floquet–Green initial value `x_p(0) = (I − M)⁻¹ ∫₀ᵀ Φ(T, s) f(s) ds`, `M = Φ(T, 0)`. -/
def greenInitial (A : ℝ → Matrix X X ℝ) (f : ℝ → X → ℝ) (T : ℝ) : X → ℝ :=
  (1 - monodromy A T 0)⁻¹ *ᵥ periodForcing A f T

/-- The periodic response: the global solution of `ẋ = A(t) x + f(t)` through
`x(0) = greenInitial A f T` (LeanForControl's forced response with input matrix `I`). -/
def periodicResponse (A : ℝ → Matrix X X ℝ) (f : ℝ → X → ℝ) (T : ℝ) : ℝ → X → ℝ :=
  LinearSystems.forcedResponse A (fun _ => (1 : Matrix X X ℝ)) f 0 (greenInitial A f T)

/-- The forced response from any initial state is a global solution of `ẋ = A(t) x + f(t)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_forcedResponse (hA : Continuous A)
    (hf : Continuous f) (t₀ : ℝ) (x₀ : X → ℝ) (t : ℝ) :
    HasDerivAt (LinearSystems.forcedResponse A (fun _ => (1 : Matrix X X ℝ)) f t₀ x₀)
      (A t *ᵥ LinearSystems.forcedResponse A (fun _ => (1 : Matrix X X ℝ)) f t₀ x₀ t + f t) t := by
  have h := LinearSystems.ContinuousLinearSystem.isTrajectory_forcedResponse
    (⟨A, fun _ => 1, fun _ => 0, fun _ => 0⟩ : LinearSystems.ContinuousLinearSystem X X X ℝ)
    hA continuous_const hf t₀ x₀ t
  simpa [LinearSystems.ContinuousLinearSystem.vectorField] using h

@[tmio T, powerlib_foundation] theorem periodicResponse_zero (A : ℝ → Matrix X X ℝ)
    (f : ℝ → X → ℝ) (T : ℝ) : periodicResponse A f T 0 = greenInitial A f T :=
  LinearSystems.variationOfConstants_self 0 _

/-- If `1` is not a Floquet multiplier, the response closes over one period. -/
@[tmio T, powerlib_foundation] private theorem periodicResponse_period
    (hdet : IsUnit (1 - monodromy A T 0).det) :
    periodicResponse A f T T = periodicResponse A f T 0 := by
  rw [periodicResponse_zero]
  have hM : transition A T 0 = monodromy A T 0 := by rw [monodromy, zero_add]
  have hinv : (1 - monodromy A T 0) * (1 - monodromy A T 0)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have hg : periodForcing A f T = (1 - monodromy A T 0) *ᵥ greenInitial A f T := by
    rw [greenInitial, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  show transition A T 0 *ᵥ greenInitial A f T +
      ∫ τ in (0 : ℝ)..T, transition A T τ *ᵥ ((1 : Matrix X X ℝ) *ᵥ f τ) = greenInitial A f T
  simp only [Matrix.one_mulVec]
  rw [show (∫ τ in (0 : ℝ)..T, transition A T τ *ᵥ f τ) = periodForcing A f T from rfl, hg, hM,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

/-- If `1` is not a Floquet multiplier, the Floquet–Green response is `T`-periodic. -/
@[tmio T, powerlib_foundation] theorem periodicResponse_periodic (hA : Continuous A)
    (hP : Periodic A T) (hf : Continuous f) (hfP : Periodic f T)
    (hdet : IsUnit (1 - monodromy A T 0).det) : Periodic (periodicResponse A f T) T := by
  have hx := hasDerivAt_forcedResponse hA hf 0 (greenInitial A f T)
  have hz : ∀ t, HasDerivAt (fun t => periodicResponse A f T (t + T))
      (A t *ᵥ periodicResponse A f T (t + T) + f t) t := by
    intro t
    have h := (hx (t + T)).comp_add_const t T
    rw [hP t, hfP t] at h
    exact h
  have h := forced_eq_of_eq hA hf hz hx (t₀ := 0) (by
    show periodicResponse A f T (0 + T) = periodicResponse A f T 0
    rw [zero_add]
    exact periodicResponse_period hdet)
  intro t
  exact congrFun h t

/-- If `1` is not a Floquet multiplier, every `T`-periodic global solution of the forced
equation is the Floquet–Green response. -/
@[tmio T, powerlib_foundation] theorem periodic_eq_periodicResponse (hA : Continuous A)
    (hf : Continuous f) (hdet : IsUnit (1 - monodromy A T 0).det) {y : ℝ → X → ℝ}
    (hy : ∀ t, HasDerivAt y (A t *ᵥ y t + f t) t) (hyP : Periodic y T) :
    y = periodicResponse A f T := by
  have hyT := forced_eq_variation hA hf hy 0 T
  rw [show T = 0 + T by ring, hyP 0, ← monodromy] at hyT
  rw [zero_add] at hyT
  have hfix : (1 - monodromy A T 0) *ᵥ y 0 = periodForcing A f T := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    nth_rewrite 1 [hyT]
    rw [periodForcing]
    abel
  have h0 : y 0 = greenInitial A f T := by
    rw [greenInitial, ← hfix, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
  exact forced_eq_of_eq hA hf hy (hasDerivAt_forcedResponse hA hf 0 (greenInitial A f T))
    (t₀ := 0) (by rw [h0, periodicResponse_zero])

/-! ## The forced regime `ρ(M) < 1` -/

/-- A monodromy matrix with spectral radius below one does not have the multiplier `1`. -/
@[tmio T, powerlib_foundation] theorem isUnit_det_one_sub_monodromy
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) :
    IsUnit (1 - monodromy A T 0).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
  set w : X → ℂ := fun i => (v i : ℂ) with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hv
    funext i
    have := congrFun h i
    simpa [hw] using this
  have hMw : (monodromy A T 0).map (algebraMap ℝ ℂ) *ᵥ w = (1 : ℂ) • w := by
    funext i
    have h := congrFun hMv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, one_smul, hw] at h ⊢
    rw [h]
    push_cast
    rfl
  have hmem : (1 : ℂ) ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) :=
    LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨w, hw0, hMw⟩
  have hle : ((‖(1 : ℂ)‖₊ : NNReal) : ENNReal) ≤
      spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ))) =>
      (‖k‖₊ : ENNReal)) 1 hmem
  simp only [nnnorm_one, ENNReal.coe_one] at hle
  exact absurd (hle.trans_lt hρ) (lt_irrefl 1)

/-- In the forced regime every forward solution converges exponentially to the Floquet–Green
response, uniformly in the initial time. -/
@[tmio T, powerlib_foundation] theorem forced_convergence (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) (hf : Continuous f)
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) :
    ∃ K β : ℝ, 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
      IsIntegralCurveOn x (fun t v => A t *ᵥ v + f t) (Ici s) → ∀ t, s ≤ t →
        ‖x t - periodicResponse A f T t‖ ≤
          K * Real.exp (-(β * (t - s))) * ‖x s - periodicResponse A f T s‖ := by
  obtain ⟨K, β, hβ, hK⟩ := trajectory_decay_of_spectralRadius_lt_one hA hP hT hρ
  refine ⟨K, β, hβ, fun s x hx t hst => ?_⟩
  have hp := hasDerivAt_forcedResponse hA hf 0 (greenInitial A f T)
  have he : IsIntegralCurveOn (fun t => x t - periodicResponse A f T t) (vecField A) (Ici s) := by
    intro r hr
    have h : HasDerivWithinAt (fun t => x t - periodicResponse A f T t) _ (Ici s) r :=
      (hx r hr).sub (hp r).hasDerivWithinAt
    refine h.congr_deriv ?_
    show _ = A r *ᵥ (x r - periodicResponse A f T r)
    simp only [Matrix.mulVec_sub]
    abel
  exact hK s _ he t hst

/-- **The forced regime.** For a continuous `T`-periodic state matrix with `ρ(M) < 1` and a
continuous `T`-periodic input there is exactly one `T`-periodic global solution of
`ẋ = A(t) x + f(t)`, with `x_p(0) = (I − M)⁻¹ ∫₀ᵀ Φ(T, s) f(s) ds`, and every forward solution
converges to it exponentially. -/
@[tmio T, powerlib_foundation] theorem forced_regime (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) (hf : Continuous f) (hfP : Periodic f T)
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) :
    (∀ t, HasDerivAt (periodicResponse A f T) (A t *ᵥ periodicResponse A f T t + f t) t) ∧
      Periodic (periodicResponse A f T) T ∧
      periodicResponse A f T 0 =
        (1 - monodromy A T 0)⁻¹ *ᵥ ∫ s in (0 : ℝ)..T, transition A T s *ᵥ f s ∧
      (∀ y : ℝ → X → ℝ, (∀ t, HasDerivAt y (A t *ᵥ y t + f t) t) → Periodic y T →
        y = periodicResponse A f T) ∧
      ∃ K β : ℝ, 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t v => A t *ᵥ v + f t) (Ici s) → ∀ t, s ≤ t →
          ‖x t - periodicResponse A f T t‖ ≤
            K * Real.exp (-(β * (t - s))) * ‖x s - periodicResponse A f T s‖ := by
  have hdet := isUnit_det_one_sub_monodromy hρ
  exact ⟨hasDerivAt_forcedResponse hA hf 0 _, periodicResponse_periodic hA hP hf hfP hdet,
    periodicResponse_zero A f T, fun y hy hyP => periodic_eq_periodicResponse hA hf hdet hy hyP,
    forced_convergence hA hP hT hf hρ⟩

/-! ## Floquet modes -/

/-- `Φ(t + T, 0) = Φ(t, 0) M` for `t ≥ 0`, `M = Φ(T, 0)`. -/
@[tmio T, powerlib_foundation] theorem transition_add_period_eq_mul (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) {t : ℝ} (ht : 0 ≤ t) :
    transition A (t + T) 0 = transition A t 0 * monodromy A T 0 := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  have hshift : transition A (t + T) (0 + T) = transition A t 0 :=
    transition_add_period hA hM hP ht
  rw [zero_add] at hshift
  rw [monodromy, zero_add, ← hshift]
  exact (LinearSystems.stateTransitionMatrix_comp hA (fun r _ => hM r)
    (mem_uIcc_of_le hT.le (by linarith))).symm

/-- A real eigenvector `M w = μ w` of the monodromy matrix starts a real Floquet mode:
`x(t) = Φ(t, 0) w` satisfies `x(t + T) = μ x(t)` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem transition_mulVec_add_period (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) {μ : ℝ} {w : X → ℝ} (hw : monodromy A T 0 *ᵥ w = μ • w)
    {t : ℝ} (ht : 0 ≤ t) :
    transition A (t + T) 0 *ᵥ w = μ • (transition A t 0 *ᵥ w) := by
  rw [transition_add_period_eq_mul hA hP hT ht, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]

/-- **Floquet mode.** A complex eigenvector `M v = μ v` of the complexified monodromy matrix
gives the complex solution `z(t) = Φ(t, 0) v` with `z(t + T) = μ z(t)` (`t ≥ 0`) and
`z(nT) = μⁿ v`. -/
@[tmio T, powerlib_foundation] theorem floquet_mode (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) {μ : ℂ} {v : X → ℂ}
    (hv : (monodromy A T 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (∀ t, 0 ≤ t → (transition A (t + T) 0).map (algebraMap ℝ ℂ) *ᵥ v =
        μ • ((transition A t 0).map (algebraMap ℝ ℂ) *ᵥ v)) ∧
      ∀ n : ℕ, (transition A (n * T) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ ^ n • v := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  refine ⟨fun t ht => ?_, fun n => ?_⟩
  · rw [transition_add_period_eq_mul hA hP hT ht, Matrix.map_mul, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_smul]
  · have h := transition_add_nat_mul_period hA hM hT.le hP 0 n
    rw [zero_add] at h
    rw [h, show (monodromy A T 0 ^ n).map (algebraMap ℝ ℂ) =
        ((monodromy A T 0).map (algebraMap ℝ ℂ)) ^ n from
      map_pow ((algebraMap ℝ ℂ).mapMatrix) _ n]
    exact Linear.mulVec_pow_of_eigen hv n

/-! ## The parametric regime `ρ(M) > 1` -/

/-- Floquet instability is spectral radius above one. -/
@[tmio T, powerlib_foundation] theorem floquetUnstable_iff_one_lt_spectralRadius :
    FloquetUnstable A T ↔ 1 < spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) := by
  constructor
  · rintro ⟨μ, hμ, h1⟩
    have hle : ((‖μ‖₊ : NNReal) : ENNReal) ≤
        spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ))) =>
        (‖k‖₊ : ENNReal)) μ hμ
    refine lt_of_lt_of_le ?_ hle
    exact_mod_cast h1
  · intro h
    rw [spectralRadius_eq_of_unital] at h
    obtain ⟨μ, hμ⟩ := lt_iSup_iff.mp h
    obtain ⟨hmem, h1⟩ := lt_iSup_iff.mp hμ
    exact ⟨μ, hmem, by exact_mod_cast h1⟩

/-- In the parametric regime the free system has a real solution that is unbounded along the
periods: `‖Φ(nT, 0) x₀‖` exceeds every bound. -/
@[tmio T, powerlib_foundation] theorem exists_unbounded_of_floquetUnstable (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) (h : FloquetUnstable A T) :
    ∃ x₀ : X → ℝ, ∀ C : ℝ, ∃ n : ℕ, C < ‖transition A (n * T) 0 *ᵥ x₀‖ := by
  obtain ⟨μ, hμ, h1⟩ := h
  obtain ⟨v, hv, hMv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
  have hmode := (floquet_mode hA hP hT hMv).2
  set w₁ : X → ℝ := fun i => (v i).re
  set w₂ : X → ℝ := fun i => (v i).im
  -- the complex mode splits into the two real solutions from `Re v`, `Im v`
  have hsplit : ∀ (n : ℕ) (i : X), ‖μ‖ ^ n * ‖v i‖ ≤
      ‖transition A (n * T) 0 *ᵥ w₁‖ + ‖transition A (n * T) 0 *ᵥ w₂‖ := by
    intro n i
    have hi := congrFun (hmode n) i
    have hre : ((transition A (n * T) 0).map (algebraMap ℝ ℂ) *ᵥ v) i =
        ((transition A (n * T) 0 *ᵥ w₁) i : ℂ) +
          ((transition A (n * T) 0 *ᵥ w₂) i : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum, w₁, w₂]
    rw [hre, Pi.smul_apply, smul_eq_mul] at hi
    have hn : ‖μ ^ n * v i‖ = ‖μ‖ ^ n * ‖v i‖ := by rw [norm_mul, norm_pow]
    rw [← hn, ← hi]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
    exact add_le_add (norm_le_pi_norm _ i) (norm_le_pi_norm _ i)
  by_contra hcon
  push Not at hcon
  obtain ⟨C₁, hC₁⟩ := hcon w₁
  obtain ⟨C₂, hC₂⟩ := hcon w₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  have htend : Tendsto (fun n : ℕ => ‖μ‖ ^ n * ‖v i‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const hvi
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop (C₁ + C₂)).exists
  have := hsplit n i
  linarith [hC₁ n, hC₂ n]

/-- **No attracting response in the parametric regime.** If some Floquet multiplier lies
outside the unit circle, no curve `p` is approached by every global solution of
`ẋ = A(t) x + f(t)`: in particular no bounded (forced) response attracts all solutions. -/
@[tmio T, powerlib_foundation] theorem not_attracting_of_floquetUnstable (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) (hf : Continuous f) (h : FloquetUnstable A T) :
    ¬ ∃ p : ℝ → X → ℝ, ∀ x : ℝ → X → ℝ, (∀ t, HasDerivAt x (A t *ᵥ x t + f t) t) →
      Tendsto (fun t => x t - p t) atTop (𝓝 0) := by
  rintro ⟨p, hp⟩
  obtain ⟨x₀, hx₀⟩ := exists_unbounded_of_floquetUnstable hA hP hT h
  set x₁ := LinearSystems.forcedResponse A (fun _ => (1 : Matrix X X ℝ)) f 0 0
  have hx₁ := hasDerivAt_forcedResponse hA hf 0 0
  set hfree : ℝ → X → ℝ := fun t => transition A t 0 *ᵥ x₀
  have hfree' : ∀ t, HasDerivAt hfree (A t *ᵥ hfree t) t := by
    intro t
    let L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun N => N *ᵥ x₀
          map_add' := fun N N' => Matrix.add_mulVec N N' x₀
          map_smul' := fun c N => Matrix.smul_mulVec c N x₀ }
    refine (L.hasFDerivAt.comp_hasDerivAt t (Dynamics.stm_hasDerivAt hA t 0)).congr_deriv ?_
    show (A t * transition A t 0) *ᵥ x₀ = A t *ᵥ (transition A t 0 *ᵥ x₀)
    rw [Matrix.mulVec_mulVec]
  have hx₂ : ∀ t, HasDerivAt (fun t => x₁ t + hfree t) (A t *ᵥ (x₁ t + hfree t) + f t) t := by
    intro t
    have h := (hx₁ t).add (hfree' t)
    convert h using 1
    rw [Matrix.mulVec_add]
    abel
  have hdiff : Tendsto hfree atTop (𝓝 0) := by
    have h := (hp _ hx₂).sub (hp _ hx₁)
    simp only [sub_zero] at h
    convert h using 1
    funext t
    show hfree t = x₁ t + hfree t - p t - (x₁ t - p t)
    abel
  have hseq : Tendsto (fun n : ℕ => hfree (n * T)) atTop (𝓝 0) :=
    hdiff.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hT)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hseq)
  obtain ⟨n, hn⟩ := hx₀ C
  exact absurd (hC _ ⟨n, rfl⟩) (not_le.mpr hn)

end powerlib.Periodic
