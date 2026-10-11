import theorem.GFL.PIPLL
import theorem.PLL.Signals
import theorem.PLL.Linear
import theorem.Dynamics.Transport

/-! # SRF-PLL: canonical nonlinear model, coordinate versions, equilibria, local stability

Model boundary (domain module).
* System: three-phase synchronous-reference-frame PLL on an ideal balanced sinusoidal grid of
  constant amplitude `V` and constant frequency `ω_g` (grid angle `θ_g(t) = θ₀ + ω_g t`).
  Phase detector = Park projection of the grid voltage on the PLL frame `θ̂`
  (`theorem/PLL/Signals.lean`, Park convention `T(θ) = [[cos, sin], [−sin, cos]]`); loop filter
  = PI (`K_p`, `K_i`); VCO `θ̂̇ = ω̂`, free-running frequency `ω_s`.
  Physical state `(θ̂, η)`, `η = ∫ V_q dt` (raw integrator, V·s):
  `θ̂̇ = ω_s + K_p V_q + K_i η`, `η̇ = V_q`, `V_q = −V sin(θ̂ − θ_g)` (`physicalField`).
* Excluded: pre-filters (SOGI/DDSRF/MAF), sampling, delay, PWM, current loop, LCL filter,
  grid impedance, saturation, anti-windup, amplitude or frequency variations of the grid.
  Continuous time. Parameters are arbitrary reals unless a theorem states a sign condition.
* Canonical (error-coordinate) model: state `x = (θ̃, η)` in this order, `θ̃ = θ̂ − θ_g`
  (`conventions.md` §D5 swing sign), autonomous field
  `θ̃̇ = (ω_s − ω_g) − K_p V sin θ̃ + K_i η`, `η̇ = −V sin θ̃` (`srfField V K_p K_i δω`,
  `δω = ω_g − ω_s`). It is *literally* the general PI-PLL `GFL.piPLLField h K_p K_i δω` of
  `theorem/GFL/PIPLL.lean` with `h = srfPD V = −V sin`; all equilibrium and linearization
  results below are instantiations of that module (not re-proved).
* Coordinate versions (vector-field conjugacies, foundation):
  - physical `(θ̂, η)` ↔ error `(θ̃, η)` along trajectories (`physical_iff_error`):
    the non-autonomous physical loop becomes autonomous in error coordinates;
  - `(θ_err, ξ)`, `ξ = η / V` (T-invariant-coordinates §1.2, T-gfl-multiscale §1.3:
    `θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`, `a = V K_p`, `b = V K_i`, `Δω = ω_s − ω_g`):
    `xiField a b Δω = srfField 1 a b (−Δω)` and
    `transportField (scaleSecond V⁻¹) 0 (srfField V K_p K_i δω) = srfField 1 (V K_p) (V K_i) δω`;
  - `(e_θ, x_I)`, `x_I = ω_s + K_i η` (T-frequency-measurement §1.1: `ω̂ = K_p V_q + x_I`):
    `measField`, equilibrium `(0, ω_g)`;
  - the port-Hamiltonian coordinates of T-pll-ph are the canonical ones (`theorem/PLL/PH.lean`).
* Level: equilibrium set (every constant `δω`) and local behaviour at an equilibrium via the
  Jacobian computed by `fderiv` from the field (`powerlib.Dynamics.LocallyExponentiallyStable`,
  `powerlib.Dynamics.Unstable`). The Jacobian at the in-phase equilibrium is `linA` of
  `theorem/PLL/Linear.lean` (state matrix of the linear models there).

Results.
* Equilibria (`V ≠ 0`, `K_i ≠ 0`): exactly `(kπ, δω / K_i)`, `k ∈ ℤ`, for every constant
  frequency offset (the integrator absorbs any offset; T-pll-dynamics §1.4).
* In-phase equilibria `(2kπ, δω/K_i)`: locally exponentially stable if `V K_p > 0 ∧ V K_i > 0`;
  unstable (saddle) if `V K_i < 0`; unstable if `V K_p < 0` (`K_i ≠ 0`). The Jacobian there is
  Hurwitz iff `V K_p > 0 ∧ V K_i > 0`.
* Anti-phase equilibria `((2k+1)π, δω/K_i)`: unstable (saddle) whenever `V K_i > 0`.

Source: work-sync `theory/T-pll-dynamics.md` §1.2–§1.4; `theory/T-invariant-coordinates.md`
§1.2; `theory/T-gfl-multiscale-modeling.md` §1.3, §1.8; `theory/T-frequency-measurement.md`
§1.1; `theory/T-pll-ph.md` §1.1.

Sign note: `T-pll-dynamics` §1.3 writes the linearized error equation with
`Δθ̃̇ = −Δω_g − V(K_p Δθ̃ + K_i ξ)`, `ξ̇ = Δθ̃` (normalized integrator `ξ = −η / V`); this module
uses the raw integrator `η` of §1.2 (same closed loop). T-pll-ph's `δω_g` is this `δω`.
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.GFL (piPLLField piPLLState piPLLJacobian)

/-! ## The canonical model -/

/-- SRF phase-detector characteristic `h(θ̃) = −V sin θ̃`. -/
def srfPD (V θ : ℝ) : ℝ := -(V * Real.sin θ)

/-- Canonical SRF-PLL error field in state `(θ̃, η)`:
`θ̃̇ = K_p h(θ̃) + K_i η − δω`, `η̇ = h(θ̃)`, `h = −V sin`, `δω = ω_g − ω_s`. -/
def srfField (V Kp Ki δω : ℝ) : State 2 → State 2 := piPLLField (srfPD V) Kp Ki δω

@[simp, powerlib_foundation] theorem srfField_apply_zero (V Kp Ki δω : ℝ) (x : State 2) :
    srfField V Kp Ki δω x 0 = -δω - Kp * V * Real.sin (x 0) + Ki * x 1 := by
  simp [srfField, srfPD]; ring

@[simp, powerlib_foundation] theorem srfField_apply_one (V Kp Ki δω : ℝ) (x : State 2) :
    srfField V Kp Ki δω x 1 = -(V * Real.sin (x 0)) := by
  simp [srfField, srfPD]

/-- The phase detector of `theorem/PLL/Signals.lean` in error coordinates. -/
@[powerlib_foundation] theorem srfPD_sub (V θg θh : ℝ) :
    srfPD V (θh - θg) = phaseDetector V θg θh := by
  rw [phaseDetector_eq, srfPD]

@[powerlib_foundation] theorem hasDerivAt_srfPD (V θ : ℝ) :
    HasDerivAt (srfPD V) (-(V * Real.cos θ)) θ :=
  ((Real.hasDerivAt_sin θ).const_mul V).neg

@[powerlib_foundation] theorem contDiff_srfPD (V : ℝ) : ContDiff ℝ 1 (srfPD V) :=
  (contDiff_const.mul Real.contDiff_sin).neg

@[powerlib_foundation] theorem contDiff_srfField (V Kp Ki δω : ℝ) :
    ContDiff ℝ 1 (srfField V Kp Ki δω) :=
  GFL.contDiff_piPLLField (contDiff_srfPD V)

/-- Jacobian of the SRF-PLL field at any state: `[[−K_p V cos θ̃, K_i], [−V cos θ̃, 0]]`. -/
@[powerlib_foundation] theorem fderiv_srfField (V Kp Ki δω : ℝ) (x : State 2) :
    fderiv ℝ (srfField V Kp Ki δω) x =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (piPLLJacobian Kp Ki (-(V * Real.cos (x 0)))) :=
  GFL.fderiv_piPLLField (hasDerivAt_srfPD V (x 0))

/-- At an in-phase point (`cos θ̃ = 1`) the Jacobian is the linear-model matrix `linA`. -/
@[powerlib_foundation] theorem piPLLJacobian_inPhase (V Kp Ki : ℝ) :
    piPLLJacobian Kp Ki (-(V * 1)) = linA V Kp Ki := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [piPLLJacobian, linA, mul_comm]

@[powerlib_foundation] private lemma cos_two_int_mul_pi (k : ℤ) :
    Real.cos (2 * k * Real.pi) = 1 := by
  rw [show 2 * (k : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_int_mul_two_pi k

@[powerlib_foundation] private lemma cos_odd_int_mul_pi (k : ℤ) :
    Real.cos ((2 * k + 1) * Real.pi) = -1 := by
  rw [show (2 * (k : ℝ) + 1) * Real.pi = (k : ℝ) * (2 * Real.pi) + Real.pi by ring,
    Real.cos_add_pi, Real.cos_int_mul_two_pi]

/-- Linearization chain: the Jacobian of the nonlinear SRF-PLL at any in-phase point
`(2kπ, η)` is `linA V K_p K_i`, the state matrix of `phaseModel`, `frequencyModel` and
`portModel`. -/
@[powerlib_foundation] theorem srf_fderiv_inPhase (V Kp Ki δω : ℝ) (k : ℤ) (η : ℝ) :
    fderiv ℝ (srfField V Kp Ki δω) (piPLLState (2 * k * Real.pi) η) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (linA V Kp Ki) := by
  rw [fderiv_srfField, GFL.piPLLState_apply_zero, cos_two_int_mul_pi, piPLLJacobian_inPhase]

/-! ## Equilibria -/

@[powerlib_foundation] theorem srfPD_eq_zero_iff {V : ℝ} (hV : V ≠ 0) (θ : ℝ) :
    srfPD V θ = 0 ↔ ∃ k : ℤ, θ = k * Real.pi := by
  rw [srfPD, neg_eq_zero, mul_eq_zero, or_iff_right hV, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

/-- Equilibria of the SRF-PLL (`V ≠ 0`, `K_i ≠ 0`): `θ̃ = kπ`, `η = δω / K_i`, for every
constant frequency offset `δω`. -/
@[powerlib_domain] theorem srfField_eq_zero_iff {V Kp Ki δω : ℝ} (hV : V ≠ 0) (hKi : Ki ≠ 0)
    (x : State 2) :
    srfField V Kp Ki δω x = 0 ↔ (∃ k : ℤ, x 0 = k * Real.pi) ∧ x 1 = δω / Ki := by
  rw [srfField, GFL.piPLLField_eq_zero_iff hKi, srfPD_eq_zero_iff hV]

/-- The equilibrium set is `{(kπ, δω / K_i) : k ∈ ℤ}`. -/
@[powerlib_domain] theorem srf_equilibria_eq {V Kp Ki δω : ℝ} (hV : V ≠ 0) (hKi : Ki ≠ 0) :
    {x : State 2 | srfField V Kp Ki δω x = 0} =
      Set.range (fun k : ℤ => piPLLState (k * Real.pi) (δω / Ki)) := by
  rw [srfField, GFL.piPLL_equilibria_eq hKi]
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, srfPD_eq_zero_iff hV]
  constructor
  · rintro ⟨θ, ⟨k, rfl⟩, rfl⟩; exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k * Real.pi, ⟨k, rfl⟩, rfl⟩

/-- An equilibrium exists for every constant frequency offset (integrator action). -/
@[powerlib_domain] theorem srf_exists_equilibrium (V Kp δω : ℝ) {Ki : ℝ} (hKi : Ki ≠ 0) :
    srfField V Kp Ki δω (piPLLState 0 (δω / Ki)) = 0 :=
  (GFL.piPLLField_eq_zero_iff hKi _).mpr ⟨by simp [srfPD], rfl⟩

/-! ## Local stability (instantiation of `GFL.PIPLL`) -/

/-- The Jacobian at an in-phase equilibrium is Hurwitz iff `V K_p > 0 ∧ V K_i > 0`. -/
@[powerlib_foundation] theorem srf_inPhase_jacobian_isHurwitz_iff (V Kp Ki : ℝ) :
    LinearSystems.IsHurwitz (piPLLJacobian Kp Ki (-(V * 1))) ↔ 0 < V * Kp ∧ 0 < V * Ki := by
  rw [piPLLJacobian_inPhase, isHurwitz_linA_iff]

/-- In-phase equilibria `(2kπ, δω/K_i)` are locally exponentially stable when
`V K_p > 0` and `V K_i > 0`, for every constant frequency offset `δω`. -/
@[powerlib_domain] theorem srf_locallyExponentiallyStable {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (δω : ℝ) (k : ℤ) :
    Dynamics.LocallyExponentiallyStable (srfField V Kp Ki δω)
      (piPLLState (2 * k * Real.pi) (δω / Ki)) := by
  have hd := hasDerivAt_srfPD V (2 * k * Real.pi)
  rw [cos_two_int_mul_pi] at hd
  refine GFL.piPLL_locallyExponentiallyStable_of_mul_neg (contDiff_srfPD V) ?_ hd ?_ ?_
  · simp [srfPD, Real.sin_eq_zero_iff]; exact Or.inr ⟨2 * k, by push_cast; ring⟩
  · nlinarith
  · nlinarith

/-- `V K_i < 0`: the in-phase equilibria are saddles, hence unstable. -/
@[powerlib_domain] theorem srf_unstable_inPhase_of_mul_neg {V Kp Ki : ℝ} (hVKi : V * Ki < 0)
    (δω : ℝ) (k : ℤ) :
    Dynamics.Unstable (srfField V Kp Ki δω) (piPLLState (2 * k * Real.pi) (δω / Ki)) := by
  have hd := hasDerivAt_srfPD V (2 * k * Real.pi)
  rw [cos_two_int_mul_pi] at hd
  refine GFL.piPLL_unstable_of_mul_pos (contDiff_srfPD V) ?_ hd ?_
  · simp [srfPD, Real.sin_eq_zero_iff]; exact Or.inr ⟨2 * k, by push_cast; ring⟩
  · nlinarith

/-- `V K_p < 0` (`K_i ≠ 0`): positive Jacobian trace at the in-phase equilibria, unstable. -/
@[powerlib_domain] theorem srf_unstable_inPhase_of_trace {V Kp Ki : ℝ} (hKi : Ki ≠ 0)
    (hVKp : V * Kp < 0) (δω : ℝ) (k : ℤ) :
    Dynamics.Unstable (srfField V Kp Ki δω) (piPLLState (2 * k * Real.pi) (δω / Ki)) := by
  have hd := hasDerivAt_srfPD V (2 * k * Real.pi)
  rw [cos_two_int_mul_pi] at hd
  refine GFL.piPLL_unstable_of_trace_pos (contDiff_srfPD V) ?_ hd hKi ?_
  · simp [srfPD, Real.sin_eq_zero_iff]; exact Or.inr ⟨2 * k, by push_cast; ring⟩
  · nlinarith

/-- `V K_i > 0`: the anti-phase equilibria `((2k+1)π, δω/K_i)` are saddles, hence unstable. -/
@[powerlib_domain] theorem srf_unstable_antiPhase {V Kp Ki : ℝ} (hVKi : 0 < V * Ki) (δω : ℝ)
    (k : ℤ) :
    Dynamics.Unstable (srfField V Kp Ki δω)
      (piPLLState ((2 * k + 1) * Real.pi) (δω / Ki)) := by
  have hd := hasDerivAt_srfPD V ((2 * k + 1) * Real.pi)
  rw [cos_odd_int_mul_pi] at hd
  refine GFL.piPLL_unstable_of_mul_pos (contDiff_srfPD V) ?_ hd ?_
  · simp [srfPD, Real.sin_eq_zero_iff]; exact Or.inr ⟨2 * k + 1, by push_cast; ring⟩
  · nlinarith

/-! ## Physical coordinates `(θ̂, η)` versus error coordinates `(θ̃, η)` -/

/-- Right-hand side of the physical SRF-PLL in state `(θ̂, η)` for grid angle `θ_g`:
`θ̂̇ = ω_s + K_p V_q + K_i η`, `η̇ = V_q`, with `V_q` the Park q voltage `phaseDetector`. -/
def physicalField (V Kp Ki ωs θg : ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![ωs + Kp * phaseDetector V θg (x 0) + Ki * x 1, phaseDetector V θg (x 0)]

/-- Phase-error coordinates `(θ̂, η) ↦ (θ̂ − θ_g, η)`. -/
def errorCoord (θg : ℝ) (x : State 2) : State 2 := x - piPLLState θg 0

@[powerlib_foundation] private lemma physicalField_sub (V Kp Ki ωs ωg θg : ℝ) (x : State 2) :
    physicalField V Kp Ki ωs θg x - piPLLState ωg 0 =
      srfField V Kp Ki (ωg - ωs) (errorCoord θg x) := by
  rw [GFL.state_two_ext_iff]
  simp [physicalField, errorCoord, srfField, srfPD, phaseDetector_eq, piPLLState]
  ring

/-- The physical SRF-PLL driven by the grid angle `θ_g(t) = θ₀ + ω_g t` and the autonomous
error field describe the same solutions: `x` solves the physical loop on `s` iff
`t ↦ (θ̂(t) − θ_g(t), η(t))` solves `srfField V K_p K_i (ω_g − ω_s)` on `s`. -/
@[powerlib_foundation] theorem physical_iff_error (V Kp Ki ωs θ₀ ωg : ℝ) (x : ℝ → State 2)
    (s : Set ℝ) :
    IsIntegralCurveOn x (fun t y => physicalField V Kp Ki ωs (θ₀ + ωg * t) y) s ↔
      IsIntegralCurveOn (fun t => errorCoord (θ₀ + ωg * t) (x t))
        (fun _ y => srfField V Kp Ki (ωg - ωs) y) s := by
  have hc (t : ℝ) : HasDerivWithinAt (fun τ => piPLLState (θ₀ + ωg * τ) 0)
      (piPLLState ωg 0) s t := by
    have h1 : HasDerivAt (fun τ : ℝ => θ₀ + ωg * τ) ωg t := by
      simpa using ((hasDerivAt_id t).const_mul ωg).const_add θ₀
    have : (fun τ => piPLLState (θ₀ + ωg * τ) 0) =
        fun τ => (θ₀ + ωg * τ) • piPLLState 1 0 := by
      funext τ; rw [GFL.state_two_ext_iff]; simp [piPLLState]
    rw [this, show piPLLState ωg 0 = ωg • piPLLState 1 0 by
      rw [GFL.state_two_ext_iff]; simp [piPLLState]]
    exact (h1.smul_const (piPLLState 1 0)).hasDerivWithinAt
  constructor
  · intro hx t ht
    have := (hx t ht).sub (hc t)
    rw [physicalField_sub] at this
    exact this
  · intro hy t ht
    have := (hy t ht).add (hc t)
    have hxeq : ((fun t => errorCoord (θ₀ + ωg * t) (x t)) +
        fun τ => piPLLState (θ₀ + ωg * τ) 0) = x := by
      funext τ; simp [errorCoord]
    rw [hxeq] at this
    convert this using 1
    beta_reduce
    rw [← physicalField_sub V Kp Ki ωs ωg, sub_add_cancel]

/-! ## The `(θ_err, ξ)` coordinates and the gains `a = V K_p`, `b = V K_i` -/

/-- T-invariant-coordinates §1.2 / T-gfl-multiscale §1.3 field in `(θ_err, ξ)`:
`θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`, `Δω = ω_s − ω_g`. -/
def xiField (a b Δω : ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![Δω - a * Real.sin (x 0) + b * x 1, -Real.sin (x 0)]

/-- The `(θ_err, ξ)` field is the canonical field at unit amplitude with gains `a, b`. -/
@[powerlib_foundation] theorem xiField_eq_srfField (a b Δω : ℝ) :
    xiField a b Δω = srfField 1 a b (-Δω) := by
  funext x
  rw [GFL.state_two_ext_iff]
  simp [xiField]

/-- Diagonal rescaling `(θ, η) ↦ (θ, c η)` as a coordinate change (`c ≠ 0`). -/
def scaleSecond (c : ℝ) (hc : c ≠ 0) : State 2 ≃L[ℝ] State 2 :=
  ContinuousLinearEquiv.equivOfInverse
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (Matrix.diagonal ![1, c]))
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (Matrix.diagonal ![1, c⁻¹]))
    (fun x => by
      rw [GFL.state_two_ext_iff]
      simp [Matrix.mulVec_diagonal, hc])
    (fun x => by
      rw [GFL.state_two_ext_iff]
      simp [Matrix.mulVec_diagonal, hc])

@[simp, powerlib_foundation] theorem scaleSecond_apply (c : ℝ) (hc : c ≠ 0) (x : State 2) :
    scaleSecond c hc x = piPLLState (x 0) (c * x 1) := by
  rw [GFL.state_two_ext_iff]
  simp [scaleSecond, Matrix.mulVec_diagonal]

@[simp, powerlib_foundation] theorem scaleSecond_symm_apply (c : ℝ) (hc : c ≠ 0) (x : State 2) :
    (scaleSecond c hc).symm x = piPLLState (x 0) (c⁻¹ * x 1) := by
  rw [GFL.state_two_ext_iff]
  simp [scaleSecond, Matrix.mulVec_diagonal]

/-- Vector-field conjugacy `ξ = η / V`: the SRF-PLL of amplitude `V` and gains `(K_p, K_i)` is
the unit-amplitude PLL with loop gains `a = V K_p`, `b = V K_i`. -/
@[powerlib_foundation] theorem transport_scale_srfField {V : ℝ} (hV : V ≠ 0) (Kp Ki δω : ℝ) :
    Dynamics.transportField (scaleSecond V⁻¹ (inv_ne_zero hV)) 0 (srfField V Kp Ki δω) =
      srfField 1 (V * Kp) (V * Ki) δω := by
  funext y
  rw [GFL.state_two_ext_iff]
  simp [Dynamics.transportField, hV]
  field_simp

/-- Trajectory form of the same conjugacy (T-invariant-coordinates `ξ := ∫V_q / V_g`). -/
@[powerlib_foundation] theorem srf_iff_xi {V : ℝ} (hV : V ≠ 0) (Kp Ki δω : ℝ)
    (x : ℝ → State 2) (s : Set ℝ) :
    IsIntegralCurveOn x (fun _ y => srfField V Kp Ki δω y) s ↔
      IsIntegralCurveOn (fun t => piPLLState (x t 0) (x t 1 / V))
        (fun _ y => xiField (V * Kp) (V * Ki) (-δω) y) s := by
  rw [xiField_eq_srfField, neg_neg, ← transport_scale_srfField hV]
  have hrw : (fun t => piPLLState (x t 0) (x t 1 / V)) =
      fun t => Dynamics.affineCoord (scaleSecond V⁻¹ (inv_ne_zero hV)) 0 (x t) := by
    funext t; simp [Dynamics.affineCoord, div_eq_inv_mul]
  rw [hrw]
  constructor
  · exact fun h => Dynamics.isIntegralCurveOn_transport _ _ h
  · intro h
    have h' := Dynamics.isIntegralCurveOn_transport (scaleSecond V⁻¹ (inv_ne_zero hV)).symm
      (-((scaleSecond V⁻¹ (inv_ne_zero hV)).symm 0)) h
    rw [Dynamics.transportField_symm_transportField] at h'
    simp only [Dynamics.affineCoord_symm_affineCoord] at h'
    exact h'

/-! ## The `(e_θ, x_I)` coordinates of T-frequency-measurement §1.1 -/

/-- `ė_θ = K_p h(e_θ) + x_I − ω_g`, `ẋ_I = K_i h(e_θ)`; frequency estimate `ω̂ = K_p h + x_I`. -/
def measField (V Kp Ki ωg : ℝ) (y : State 2) : State 2 :=
  WithLp.toLp 2 ![Kp * srfPD V (y 0) + y 1 - ωg, Ki * srfPD V (y 0)]

/-- `x_I = ω_s + K_i η` is an affine conjugacy between the canonical field and `measField`. -/
@[powerlib_foundation] theorem transport_meas_srfField {Ki : ℝ} (hKi : Ki ≠ 0) (V Kp ωs ωg : ℝ) :
    Dynamics.transportField (scaleSecond Ki hKi) (piPLLState 0 ωs)
        (srfField V Kp Ki (ωg - ωs)) = measField V Kp Ki ωg := by
  funext y
  rw [GFL.state_two_ext_iff]
  simp [Dynamics.transportField, measField, srfField, piPLLState]
  field_simp
  ring

/-- Equilibria in the `(e_θ, x_I)` coordinates: `h(e_θ) = 0` and `x_I = ω_g`, i.e. the
frequency estimate `ω̂ = x_I` equals the grid frequency (zero steady-state frequency error). -/
@[powerlib_domain] theorem measField_eq_zero_iff {V Kp Ki ωg : ℝ} (hV : V ≠ 0) (hKi : Ki ≠ 0)
    (y : State 2) :
    measField V Kp Ki ωg y = 0 ↔ (∃ k : ℤ, y 0 = k * Real.pi) ∧ y 1 = ωg := by
  rw [GFL.state_two_ext_iff]
  simp only [measField, PiLp.zero_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← srfPD_eq_zero_iff hV]
  constructor
  · rintro ⟨h0, h1⟩
    have hz : srfPD V (y 0) = 0 := (mul_eq_zero.mp h1).resolve_left hKi
    refine ⟨hz, ?_⟩
    rw [hz, mul_zero, zero_add] at h0; linarith
  · rintro ⟨hz, h1⟩
    rw [hz, h1]; simp

end powerlib.PLL
