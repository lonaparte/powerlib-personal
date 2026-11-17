import theorem.GridTiedConverter.PLL.PIPLLFamily
import theorem.GridTiedConverter.PLL.Signals
import theorem.GridTiedConverter.PLL.Linear
import theorem.Dynamics.Transport

/-! # SRF-PLL: canonical nonlinear model, coordinate versions, equilibria, local stability

Model boundary.
* System: three-phase synchronous-reference-frame PLL on an ideal balanced sinusoidal grid of
  constant amplitude `V` and constant frequency `ω_g` (grid angle `θ_g(t) = θ₀ + ω_g t`).
  Phase detector = Park projection of the grid voltage on the PLL frame `θ̂`
  (`theorem/GridTiedConverter/PLL/Signals.lean`, Park convention
  `T(θ) = [[cos, sin], [−sin, cos]]`); loop filter = PI (`K_p`, `K_i`); VCO `θ̂̇ = ω̂`, free-running
  frequency `ω_s`. Physical state `(θ̂, η)`, `η = ∫ V_q dt` (raw integrator, V·s):
  `θ̂̇ = ω_s + K_p V_q + K_i η`, `η̇ = V_q`, `V_q = −V sin(θ̂ − θ_g)` (`physicalField`).
* Excluded: pre-filters (SOGI/DDSRF/MAF), sampling, delay, PWM, current loop, LCL filter,
  grid impedance, saturation, anti-windup, amplitude or frequency variations of the grid.
  Continuous time. Parameters are arbitrary reals unless a theorem states a sign condition.
* Canonical (error-coordinate) model: state `x = (θ̃, η)` in this order, `θ̃ = θ̂ − θ_g`
  (`conventions.md` §D5 swing sign), autonomous field
  `θ̃̇ = (ω_s − ω_g) − K_p V sin θ̃ + K_i η`, `η̇ = −V sin θ̃` (`srfField V K_p K_i δω`,
  `δω = ω_g − ω_s`). It is *literally* the general PI-PLL `PLL.piPLLField h K_p K_i δω` of
  `theorem/GridTiedConverter/PLL/PIPLL.lean` with `h = srfPD V = −V sin` (defined there); all
  equilibrium and linearization results below are instantiations of that module (not re-proved).
* Coordinate versions (vector-field conjugacies, domain):
  - physical `(θ̂, η)` ↔ error `(θ̃, η)` along trajectories (`physical_iff_error`):
    the non-autonomous physical loop becomes autonomous in error coordinates;
  - `(θ_err, ξ)`, `ξ = η / V` (T-invariant-coordinates §1.2, T-gfl-multiscale §1.3:
    `θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`, `a = V K_p`, `b = V K_i`, `Δω = ω_s − ω_g`):
    `xiField a b Δω = srfField 1 a b (−Δω)` and
    `transportField (scaleCoord V⁻¹) 0 (srfField V K_p K_i δω) = srfField 1 (V K_p) (V K_i) δω`;
  - `(e_θ, x_I)`, `x_I = ω_s + K_i η` (T-frequency-measurement §1.1: `ω̂ = K_p V_q + x_I`):
    `measField`, equilibrium `(0, ω_g)`;
  - the port-Hamiltonian coordinates of T-pll-ph are the canonical ones
    (`theorem/GridTiedConverter/PLL/PH.lean`).
* Level: equilibrium set (every constant `δω`) and local behaviour at an equilibrium via the
  Jacobian computed by `fderiv` from the field. The Jacobian at the in-phase equilibrium is
  `linA` of `theorem/GridTiedConverter/PLL/Linear.lean` (state matrix of the linear models there).

Source: work-sync `theory/T-pll-dynamics.md` §1.2–§1.4; `theory/T-invariant-coordinates.md`
§1.2; `theory/T-gfl-multiscale-modeling.md` §1.3, §1.8; `theory/T-frequency-measurement.md`
§1.1; `theory/T-pll-ph.md` §1.1.

Results.
* Equilibria (`V ≠ 0`, `K_i ≠ 0`): exactly `(kπ, δω / K_i)`, `k ∈ ℤ`, for every constant
  frequency offset (the integrator absorbs any offset; T-pll-dynamics §1.4).
* In-phase equilibria `(2kπ, δω/K_i)`: locally exponentially stable if `V K_p > 0 ∧ V K_i > 0`;
  unstable (saddle) if `V K_i < 0`; unstable if `V K_p < 0` (`K_i ≠ 0`). The Jacobian there is
  Hurwitz iff `V K_p > 0 ∧ V K_i > 0`.
* Anti-phase equilibria `((2k+1)π, δω/K_i)`: unstable (saddle) whenever `V K_i > 0`.
  (These local results are proved in `PIPLLFamily` on the SRF members; the Jacobian at the in-phase
  points is `linA`, `srf_fderiv_inPhase`.)

Family and connection conclusions.
No new family: the SRF-PLL read about a selected phase `θ*` is the member `PLL.PIPLL.srf V K_p K_i
δω θ*` of the PI-PLL family `PLL.PIPLL.family` (`theorem/GridTiedConverter/PLL/PIPLLFamily.lean`),
whose detector is `srfPD V` (by definition) and whose system map is `srfField V K_p K_i δω`
translated so that `(θ*, δω / K_i)` is the origin. The other coordinate versions are the same
models: the `(θ_err, ξ)` field with gains `(a, b)` and offset `Δω` is `srfField 1 a b (−Δω)`
(`xiField_eq_srfField`), i.e. the member `srf 1 a b (−Δω) θ*`, and the `(e_θ, x_I)` field is an
affine image of `srfField` (`transport_meas_srfField`). The four local-stability results of the SRF
members are proved with the family (`PIPLL.srf_mem_den_locallyExponentiallyStable_inPhase`,
`PIPLL.srf_mem_den_unstable_inPhase_of_mul_neg`, `PIPLL.srf_mem_den_unstable_inPhase_of_trace`,
`PIPLL.srf_mem_den_unstable_antiPhase`). Connection conclusion on the family's semantics connection
here: amplitude invariance of every flow sentence (`srf_mem_den_iff_unitAmplitude`: amplitude `V`
with gains `(K_p, K_i)` is the unit-amplitude loop with gains `(V K_p, V K_i)`). Scaffold of the
amplitude invariance: `theorem/GridTiedConverter/PLL/PLLAmplitude.agda`. The equilibrium sets
(`srfField_eq_zero_iff`: the equilibria are `{(kπ, δω / K_i) : k ∈ ℤ}`, `srf_exists_equilibrium`,
`measField_eq_zero_iff`) are static evidence on the model, not connection conclusions; the
coordinate conjugacies are domain model identities.

Sign note: `T-pll-dynamics` §1.3 writes the linearized error equation with
`Δθ̃̇ = −Δω_g − V(K_p Δθ̃ + K_i ξ)`, `ξ̇ = Δθ̃` (normalized integrator `ξ = −η / V`); this module
uses the raw integrator `η` of §1.2 (same closed loop). T-pll-ph's `δω_g` is this `δω`.
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.PLL.PIPLL (srf)

/-! ## The canonical model -/

/-- Canonical SRF-PLL error field in state `(θ̃, η)`:
`θ̃̇ = K_p h(θ̃) + K_i η − δω`, `η̇ = h(θ̃)`, `h = −V sin`, `δω = ω_g − ω_s`. -/
def srfField (V Kp Ki δω : ℝ) : State 2 → State 2 := piPLLField (srfPD V) Kp Ki δω

@[tmio M, simp, powerlib_domain] theorem srfField_apply_zero (V Kp Ki δω : ℝ) (x : State 2) :
    srfField V Kp Ki δω x 0 = -δω - Kp * V * Real.sin (x 0) + Ki * x 1 := by
  simp [srfField, srfPD]; ring

@[tmio M, simp, powerlib_domain] theorem srfField_apply_one (V Kp Ki δω : ℝ) (x : State 2) :
    srfField V Kp Ki δω x 1 = -(V * Real.sin (x 0)) := by
  simp [srfField, srfPD]

/-- The phase detector of `theorem/GridTiedConverter/PLL/Signals.lean` in error coordinates. -/
@[tmio M, powerlib_domain] theorem srfPD_sub (V θg θh : ℝ) :
    srfPD V (θh - θg) = phaseDetector V θg θh := by
  rw [phaseDetector_eq, srfPD]

@[tmio M, powerlib_domain] theorem contDiff_srfField (V Kp Ki δω : ℝ) :
    ContDiff ℝ 1 (srfField V Kp Ki δω) :=
  contDiff_piPLLField (contDiff_srfPD V)

/-- Jacobian of the SRF-PLL field at any state: `[[−K_p V cos θ̃, K_i], [−V cos θ̃, 0]]`. -/
@[tmio M, powerlib_domain] theorem fderiv_srfField (V Kp Ki δω : ℝ) (x : State 2) :
    fderiv ℝ (srfField V Kp Ki δω) x =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (piPLLJacobian Kp Ki (-(V * Real.cos (x 0)))) :=
  fderiv_piPLLField (hasDerivAt_srfPD V (x 0))

/-- At an in-phase point (`cos θ̃ = 1`) the Jacobian is the linear-model matrix `linA`. -/
@[tmio M, powerlib_domain] theorem piPLLJacobian_inPhase (V Kp Ki : ℝ) :
    piPLLJacobian Kp Ki (-(V * 1)) = linA V Kp Ki := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [piPLLJacobian, linA, mul_comm]

/-- Linearization chain: the Jacobian of the nonlinear SRF-PLL at any in-phase point
`(2kπ, η)` is `linA V K_p K_i`, the state matrix of `phaseModel`, `frequencyModel` and
`portModel`. -/
@[tmio M, powerlib_domain] theorem srf_fderiv_inPhase (V Kp Ki δω : ℝ) (k : ℤ) (η : ℝ) :
    fderiv ℝ (srfField V Kp Ki δω) (PhasePlane.mk (2 * k * Real.pi) η) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (linA V Kp Ki) := by
  rw [fderiv_srfField, PhasePlane.mk_apply_zero,
    show 2 * (k : ℝ) * Real.pi = k * (2 * Real.pi) by ring, Real.cos_int_mul_two_pi,
    piPLLJacobian_inPhase]

/-! ## Equilibria -/

@[tmio M, powerlib_domain] theorem srfPD_eq_zero_iff {V : ℝ} (hV : V ≠ 0) (θ : ℝ) :
    srfPD V θ = 0 ↔ ∃ k : ℤ, θ = k * Real.pi := by
  rw [srfPD, neg_eq_zero, mul_eq_zero, or_iff_right hV, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

/-- Equilibria of the SRF-PLL (`V ≠ 0`, `K_i ≠ 0`): `θ̃ = kπ`, `η = δω / K_i`, for every
constant frequency offset `δω`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem srfField_eq_zero_iff {V Kp Ki δω : ℝ} (hV : V ≠ 0) (hKi : Ki ≠ 0)
    (x : State 2) :
    srfField V Kp Ki δω x = 0 ↔ (∃ k : ℤ, x 0 = k * Real.pi) ∧ x 1 = δω / Ki := by
  rw [srfField, piPLLField_eq_zero_iff hKi, srfPD_eq_zero_iff hV]

/-- An equilibrium exists for every constant frequency offset (integrator action).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem srf_exists_equilibrium (V Kp δω : ℝ) {Ki : ℝ} (hKi : Ki ≠ 0) :
    srfField V Kp Ki δω (PhasePlane.mk 0 (δω / Ki)) = 0 :=
  (piPLLField_eq_zero_iff hKi _).mpr ⟨by simp [srfPD], rfl⟩

/-! ## Local stability (instantiation of `PLL.PIPLL`) -/

/-- The untranslated field of the SRF family member is the canonical SRF-PLL field. -/
@[tmio M, powerlib_domain] theorem srf_piPLLField (V Kp Ki δω θ : ℝ) :
    piPLLField (srf V Kp Ki δω θ).h Kp Ki δω = srfField V Kp Ki δω := rfl

/-! ## Physical coordinates `(θ̂, η)` versus error coordinates `(θ̃, η)` -/

/-- Right-hand side of the physical SRF-PLL in state `(θ̂, η)` for grid angle `θ_g`:
`θ̂̇ = ω_s + K_p V_q + K_i η`, `η̇ = V_q`, with `V_q` the Park q voltage `phaseDetector`. -/
def physicalField (V Kp Ki ωs θg : ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![ωs + Kp * phaseDetector V θg (x 0) + Ki * x 1, phaseDetector V θg (x 0)]

/-- Phase-error coordinates `(θ̂, η) ↦ (θ̂ − θ_g, η)`. -/
def errorCoord (θg : ℝ) (x : State 2) : State 2 := x - PhasePlane.mk θg 0

@[tmio M, powerlib_domain] private lemma physicalField_sub (V Kp Ki ωs ωg θg : ℝ) (x : State 2) :
    physicalField V Kp Ki ωs θg x - PhasePlane.mk ωg 0 =
      srfField V Kp Ki (ωg - ωs) (errorCoord θg x) := by
  rw [PhasePlane.ext_iff']
  simp [physicalField, errorCoord, srfField, srfPD, phaseDetector_eq, PhasePlane.mk]
  ring

/-- The physical SRF-PLL driven by the grid angle `θ_g(t) = θ₀ + ω_g t` and the autonomous
error field describe the same solutions: `x` solves the physical loop on `s` iff
`t ↦ (θ̂(t) − θ_g(t), η(t))` solves `srfField V K_p K_i (ω_g − ω_s)` on `s`. -/
@[tmio M, powerlib_domain] theorem physical_iff_error (V Kp Ki ωs θ₀ ωg : ℝ) (x : ℝ → State 2)
    (s : Set ℝ) :
    IsIntegralCurveOn x (fun t y => physicalField V Kp Ki ωs (θ₀ + ωg * t) y) s ↔
      IsIntegralCurveOn (fun t => errorCoord (θ₀ + ωg * t) (x t))
        (fun _ y => srfField V Kp Ki (ωg - ωs) y) s := by
  have hc (t : ℝ) : HasDerivWithinAt (fun τ => PhasePlane.mk (θ₀ + ωg * τ) 0)
      (PhasePlane.mk ωg 0) s t := by
    have h1 : HasDerivAt (fun τ : ℝ => θ₀ + ωg * τ) ωg t := by
      simpa using ((hasDerivAt_id t).const_mul ωg).const_add θ₀
    have : (fun τ => PhasePlane.mk (θ₀ + ωg * τ) 0) =
        fun τ => (θ₀ + ωg * τ) • PhasePlane.mk 1 0 := by
      funext τ; rw [PhasePlane.ext_iff']; simp [PhasePlane.mk]
    rw [this, show PhasePlane.mk ωg 0 = ωg • PhasePlane.mk 1 0 by
      rw [PhasePlane.ext_iff']; simp [PhasePlane.mk]]
    exact (h1.smul_const (PhasePlane.mk 1 0)).hasDerivWithinAt
  constructor
  · intro hx t ht
    have := (hx t ht).sub (hc t)
    rw [physicalField_sub] at this
    exact this
  · intro hy t ht
    have := (hy t ht).add (hc t)
    have hxeq : ((fun t => errorCoord (θ₀ + ωg * t) (x t)) +
        fun τ => PhasePlane.mk (θ₀ + ωg * τ) 0) = x := by
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
@[tmio M, powerlib_domain] theorem xiField_eq_srfField (a b Δω : ℝ) :
    xiField a b Δω = srfField 1 a b (-Δω) := by
  funext x
  rw [PhasePlane.ext_iff']
  simp [xiField]

/-- Vector-field conjugacy `ξ = η / V`: the SRF-PLL of amplitude `V` and gains `(K_p, K_i)` is
the unit-amplitude PLL with loop gains `a = V K_p`, `b = V K_i`. -/
@[tmio M, powerlib_domain] theorem transport_scale_srfField {V : ℝ} (hV : V ≠ 0) (Kp Ki δω : ℝ) :
    Dynamics.transportField (Dynamics.scaleCoord (inv_ne_zero hV)) 0 (srfField V Kp Ki δω) =
      srfField 1 (V * Kp) (V * Ki) δω := by
  funext y
  rw [PhasePlane.ext_iff']
  simp [Dynamics.transportField, hV]
  field_simp

/-- Trajectory form of the same conjugacy (T-invariant-coordinates `ξ := ∫V_q / V_g`). -/
@[tmio M, powerlib_domain] theorem srf_iff_xi {V : ℝ} (hV : V ≠ 0) (Kp Ki δω : ℝ)
    (x : ℝ → State 2) (s : Set ℝ) :
    IsIntegralCurveOn x (fun _ y => srfField V Kp Ki δω y) s ↔
      IsIntegralCurveOn (fun t => PhasePlane.mk (x t 0) (x t 1 / V))
        (fun _ y => xiField (V * Kp) (V * Ki) (-δω) y) s := by
  rw [xiField_eq_srfField, neg_neg, ← transport_scale_srfField hV]
  have hrw : (fun t => PhasePlane.mk (x t 0) (x t 1 / V)) =
      fun t => Dynamics.affineCoord (Dynamics.scaleCoord (inv_ne_zero hV)) 0 (x t) := by
    funext t; simp [Dynamics.affineCoord, div_eq_inv_mul]; rfl
  rw [hrw]
  constructor
  · exact fun h => Dynamics.isIntegralCurveOn_transport _ _ h
  · intro h
    have h' := Dynamics.isIntegralCurveOn_transport (Dynamics.scaleCoord (inv_ne_zero hV)).symm
      (-((Dynamics.scaleCoord (inv_ne_zero hV)).symm 0)) h
    rw [Dynamics.transportField_symm_transportField] at h'
    simp only [Dynamics.affineCoord_symm_affineCoord] at h'
    exact h'

/-- Amplitude invariance on the semantics connection (T-invariant-coordinates §1.2): for
`V ≠ 0`, every flow sentence holds for the SRF-PLL of amplitude `V` and gains `(K_p, K_i)` about
`θ*` exactly when it holds for the unit-amplitude SRF-PLL with loop gains `(V K_p, V K_i)` about
`θ*` (the conjugacy `ξ = η / V` maps the selected point `(θ*, δω / K_i)` to
`(θ*, δω / (V K_i))`). -/
@[tmio TM, powerlib_domain] theorem srf_mem_den_iff_unitAmplitude {V : ℝ} (hV : V ≠ 0)
    (Kp Ki δω θ : ℝ) (P : Flow.Property) :
    connection% (srf V Kp Ki δω θ ∈ PIPLL.family.den (.flow P) ↔
      srf 1 (V * Kp) (V * Ki) δω θ ∈ PIPLL.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hflow : ∀ m : PIPLL.Model, m ∈ PIPLL.family.den (.flow P) ↔
      P.holds (piPLLField m.h m.Kp m.Ki m.δω) m.point := fun _ =>
    Spectral.mem_den_flow_iff_shift (f := fun m : PIPLL.Model => piPLLField m.h m.Kp m.Ki m.δω)
      (pt := PIPLL.Model.point) PIPLL.family_isAutonomous
  rw [hflow, hflow]
  change P.holds (piPLLField (srf V Kp Ki δω θ).h Kp Ki δω) (PhasePlane.mk θ (δω / Ki)) ↔
    P.holds (piPLLField (srf 1 (V * Kp) (V * Ki) δω θ).h (V * Kp) (V * Ki) δω)
      (PhasePlane.mk θ (δω / (V * Ki)))
  rw [srf_piPLLField, srf_piPLLField, ← transport_scale_srfField hV,
    ← Dynamics.holds_transport_iff (Dynamics.scaleCoord (inv_ne_zero hV)) 0 P]
  have hpt : Dynamics.affineCoord (Dynamics.scaleCoord (inv_ne_zero hV)) 0
      (PhasePlane.mk θ (δω / Ki)) = PhasePlane.mk θ (δω / (V * Ki)) := by
    rw [PhasePlane.ext_iff']
    simp [Dynamics.affineCoord]
    field_simp
  rw [hpt]

/-! ## The `(e_θ, x_I)` coordinates of T-frequency-measurement §1.1 -/

/-- `ė_θ = K_p h(e_θ) + x_I − ω_g`, `ẋ_I = K_i h(e_θ)`; frequency estimate `ω̂ = K_p h + x_I`. -/
def measField (V Kp Ki ωg : ℝ) (y : State 2) : State 2 :=
  WithLp.toLp 2 ![Kp * srfPD V (y 0) + y 1 - ωg, Ki * srfPD V (y 0)]

/-- `x_I = ω_s + K_i η` is an affine conjugacy between the canonical field and `measField`. -/
@[tmio M, powerlib_domain] theorem transport_meas_srfField {Ki : ℝ} (hKi : Ki ≠ 0) (V Kp ωs ωg : ℝ) :
    Dynamics.transportField (Dynamics.scaleCoord hKi) (PhasePlane.mk 0 ωs)
        (srfField V Kp Ki (ωg - ωs)) = measField V Kp Ki ωg := by
  funext y
  rw [PhasePlane.ext_iff']
  simp [Dynamics.transportField, measField, srfField, PhasePlane.mk]
  field_simp
  ring

/-- Equilibria in the `(e_θ, x_I)` coordinates: `h(e_θ) = 0` and `x_I = ω_g`, i.e. the
frequency estimate `ω̂ = x_I` equals the grid frequency (zero steady-state frequency error).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem measField_eq_zero_iff {V Kp Ki ωg : ℝ} (hV : V ≠ 0) (hKi : Ki ≠ 0)
    (y : State 2) :
    measField V Kp Ki ωg y = 0 ↔ (∃ k : ℤ, y 0 = k * Real.pi) ∧ y 1 = ωg := by
  rw [PhasePlane.ext_iff']
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
