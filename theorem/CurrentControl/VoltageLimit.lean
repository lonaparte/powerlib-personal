import theorem.CurrentControl.PILoop
import theorem.Drives.Modulation
import theorem.Dynamics.Shift
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.PiecewiseAffine
import theorem.Stack.Implementation

/-! # PI current loop under the inverter's modulation voltage limit: an implementation layer

Model boundary.
* Implementation layer (I, `theorem/Stack/Implementation.lean`, `Layers.md`). A platform
  `LimitedPI` realizes its design, a single-axis PI current loop `PIParams` of the model layer
  `PIParams.family` (`theorem/CurrentControl/PILoop.lean`: perfect decoupling, ideal
  feedforward), under one realistic constraint the design did not intend: a two-level inverter
  applies only voltages of its linear modulation range, `|u| ≤ V_max = V_dc/√3` (`Vmax`), the
  radius of the largest circle in the voltage hexagon (`theorem/Drives/Modulation.lean`). The
  limit is hardware, not a designed limiter, so it belongs to I.
* State order `(i, ξ) ∈ ℝ² = EuclideanSpace ℝ (Fin 2)` as in the design: `i` the branch current,
  IN-positive (work-sync `conventions.md` §D1), in the PLL-aligned dq frame; `ξ = ∫ (i* − i) dt`.
* Platform field (`limitedField`): `L di/dt = −R i + sat_{V_max}(Kp (i* − i) + Ki ξ)`,
  `dξ/dt = i* − i`, with `sat_V(u) = max (−V) (min V u)` (`sat`) and the applied voltage
  `applied`. Continuous time, autonomous: the reference `i*` is a parameter of the platform, held
  constant (outer loops frozen), because whether the limit acts depends on the operating point.
  Any signs of `L, R, Kp, Ki, V_dc`; the engineering range is `L > 0`, `V_dc > 0`.
* Operating point `(i*, R i*/Ki)` (`point`, the design equilibrium `PIParams.equilibrium`), whose
  steady voltage is `R i*` (`control_point_of_ne`). A platform is read as its field translated so
  that the operating point is the origin (`field`, `Flow.Property.holds_shift_iff`); the design is
  read as the zero-input field of its linear plant (`Family.IsLinear`), its behaviour about every
  operating point.
* Single-axis idealization of the limit: the other axis carries no voltage, so the applied vector
  is `sat(u) e^{jθ}` in the stationary frame (`applied_synthesizable`); the joint dq limit
  `v_d² + v_q² ≤ V_max²` (T-field-oriented-control §1.7) and its priority rules between the axes
  are excluded.
* Excluded (as in the design): PLL dynamics, the other axis, feedforward dynamics, computation
  and PWM delay (`theorem/CurrentControl/LoopDelay.lean`, the delay tools), PWM switching and
  ripple, anti-windup, DC-link dynamics (`V_dc` constant).

Source: work-sync `theory/T-field-oriented-control.md` §1.5 (decoupled PI current loop), §1.7
(`V_max = V_dc/√3`, saturation of the current-loop PI and anti-windup),
`theory/T-scalar-vf-control.md` §1.8 (SVPWM linear range); powerlib
`theorem/Drives/Modulation.lean` (`linearRange_projection_le`, `svpwm_linearRange`,
`maxCircle_radius_le`: the tool module of the constraint), `theorem/CurrentControl/PILoop.lean`
(the design family), `theorem/Dynamics/Locality.lean` (local sentences depend only on the field
near the point), `theorem/Dynamics/PiecewiseAffine.lean` (a field decided near the point by one
affine piece), `theorem/Stack/Implementation.lean` (realization soundness, completeness,
exactness). Read only.

Results.
* Modulation (static): `circle_synthesizable_iff` — every vector of modulus `ρ ≥ 0` is produced
  by leg voltages in `[0, V_dc]` iff `ρ ≤ V_max`; `abs_applied_le`, `applied_synthesizable` —
  every voltage the platform applies, at every frame angle, is produced by the inverter.
* Saturation (static): `sat_of_abs_le`, `abs_sat_le`, `sat_eventually_eq` (constant near every
  command beyond the limit), `sat_ne_of_lt_abs`; `limitedField_eq_of_abs_le` (the platform field
  is the design field wherever the command is in range); `control_point`, `abs_control_point_le`;
  `contDiffAt_field` (with headroom the platform field is `C¹` near the operating point; used by
  its explicit Euler integration, `theorem/CurrentControl/Euler.lean`).
* Implementation evidence (private). With headroom the command at the operating point is in
  range, so near the point the platform field is the unsaturated design field
  (`field_eventuallyEq_design`), the design's linear zero-input field when `Ki ≠ 0`
  (`field_eventuallyEq_linear`). With overload the saturation is constant near the point and the
  point is not an equilibrium (`unstable_of_overload`). No platform is globally exponentially
  stable (`not_globallyExponentiallyStable`): from `(0, ξ₀)` the current stays below a bound `B`
  on `[0, T]` independent of `ξ₀` (Grönwall: the applied voltage is bounded), so the integrator
  moves by at most `B T`, while an exponential estimate halves `‖x‖` by a time `T` fixed by its
  constants; a large `ξ₀` contradicts both.

Family and connection conclusions.
* I: `family : Family LimitedPI LimitRequirement 2 0`. Requirements: the lifted design
  requirements `design q` (`PIParams.family.meets`) and the realistic constraints `inductance`
  (`0 < L`), `integral` (`Ki ≠ 0`), `dcLink` (`0 < V_dc`), `headroom` (`|R i*| < V_dc/√3`: the
  operating voltage strictly inside the linear range) and `overload` (`V_dc/√3 < |R i*|`). The
  local sentences translate into `{design stable, headroom}`, instability into
  `{design unstable, headroom}`, passivity into nothing, the remaining flow sentences into the
  whole, inconsistent, language (`realize_univ`).
  `chain_le_semantics`: every translation is sound. `exact_passive`. `exactUnder_attractive`:
  within `headroom` the local asymptotic and local exponential translations are exact
  (`mem_den_iff`: with `L > 0`, LAS / LES iff `R + Kp > 0 ∧ Ki > 0`). `exactUnder_unstable`:
  within `{inductance, integral, headroom}` instability is exact (a design that is not unstable,
  `(R + Kp)/L ≥ 0` and `Ki/L > 0`, is Lyapunov stable). `not_exactUnder_lyapunovStable`: Lyapunov
  stability is not exact within all realistic constraints (`center`, a lossless design
  `R + Kp = 0`). `exact_globallyExponentiallyStable`: no platform is globally exponentially
  stable (`not_mem_den_globallyExponentiallyStable`), so the whole-language translation is exact.
  `mem_den_unstable_of_overload`: with `L > 0`, `Ki ≠ 0`, `V_dc > 0` and overload the platform is
  unstable, whatever the design. Global asymptotic stability is not decided here.
* M–I: `implementation : Implementation PIParams Spectral.Requirement LimitedPI LimitRequirement
  2 1 2 0`, every platform realizing its design (`Implementation.ofDesign design`).
  `realizationExactUnder_local`: within `{integral, headroom}` Lyapunov stability, local
  asymptotic and local exponential stability and instability are realized exactly, for every
  sign of `L` (locality: the limit is inactive near the operating point).
  `realizationSoundUnder_attractive`: within `headroom` alone the local asymptotic and local
  exponential sentences are realized soundly, by the static reduction
  `Implementation.realizationSoundUnder_of_design` (the exact design translation
  `PIParams.exact`, the sound platform translation, and `design stable` with `headroom` meeting
  the platform translation).
  `not_realizationSoundUnder_lyapunovStable`, `not_realizationCompleteUnder_unstable`: without
  `integral` neither holds (`drifting`: design `L = R = 1`, `Kp = Ki = 0`, Lyapunov stable
  (`drifting_design_mem_den_lyapunovStable`); at `i* = 1`, `V_dc = 3` the operating point `(1, 0)`
  is not an equilibrium of the platform, which is unstable (`drifting_mem_den_unstable`)).
  `realizationSoundUnder_unstable_of_overload`,
  `not_realizationSoundUnder_locallyExponentiallyStable`: within
  `{inductance, integral, dcLink, overload}` instability is realized soundly and local exponential
  stability is not (`overloaded`: the nominal design `L = R = Kp = Ki = 1` (`nominal_mem_den`) at
  `i* = 1`, `V_dc = 1`, `overloaded_mem_den_unstable`).
  `not_realizationSoundUnder_globallyExponentiallyStable`: global exponential stability is not
  realized soundly within all realistic constraints including headroom (`unloaded`: the nominal
  design at `i* = 0`, `V_dc = 1`); `realizationCompleteUnder_globallyExponentiallyStable` holds
  vacuously. Scaffold: `theorem/VoltageLimit.agda`.

Complement (T-field-oriented-control §1.7, "当 |v_s*| 饱和后，PI 积分饱和需 anti-windup"): the
note treats integrator windup as a performance issue. Here, without anti-windup, the voltage limit
removes global exponential stability for every gain and every headroom, while every local
sentence of the design is inherited exactly once the operating voltage has headroom and the
integrator holds the operating point (`Ki ≠ 0`).
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter Linear LinearSystems TMIO Set
open scoped Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A PI current-loop axis driven through a two-level inverter: the design loop, the constant
current reference `i*` (the operating point) and the DC-link voltage `V_dc` that fixes the linear
modulation range. -/
structure LimitedPI where
  /-- The design loop (model layer). -/
  design : PIParams
  /-- The constant current reference `i*`. -/
  iref : ℝ
  /-- The DC-link voltage. -/
  Vdc : ℝ

namespace LimitedPI

/-! ## Saturation -/

/-- Saturation of a command `u` to `[−V, V]`. -/
def sat (V u : ℝ) : ℝ := max (-V) (min V u)

/-- A command in range passes unchanged. -/
@[tmio T, powerlib_foundation] theorem sat_of_abs_le {V u : ℝ} (h : |u| ≤ V) : sat V u = u := by
  rw [abs_le] at h
  simp [sat, min_eq_right h.2, max_eq_right h.1]

/-- The saturated command is bounded by the limit. -/
@[tmio T, powerlib_foundation] theorem abs_sat_le (V u : ℝ) : |sat V u| ≤ |V| := by
  unfold sat
  rcases le_total 0 V with hV | hV
  · rw [abs_of_nonneg hV, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · rw [max_eq_left ((min_le_left _ _).trans (by linarith)), abs_neg]

/-- Beyond the limit the saturation is constant near the command. -/
@[powerlib_foundation] theorem sat_eventually_eq {V u₀ : ℝ} (h : V < |u₀|) :
    ∀ᶠ u in 𝓝 u₀, sat V u = sat V u₀ := by
  rcases lt_abs.mp h with h | h
  · filter_upwards [eventually_gt_nhds h] with u hu
    simp [sat, min_eq_left hu.le, min_eq_left h.le]
  · have h' : u₀ < -V := by linarith
    have e : ∀ w, w < -V → sat V w = -V := fun w hw =>
      max_eq_left ((min_le_right _ _).trans hw.le)
    filter_upwards [eventually_lt_nhds h'] with u hu
    rw [e u hu, e u₀ h']

/-- With a nonnegative limit, a command beyond it is changed by the saturation. -/
@[powerlib_foundation] theorem sat_ne_of_lt_abs {V u : ℝ} (hV : 0 ≤ V) (h : V < |u|) :
    sat V u ≠ u := by
  rcases lt_abs.mp h with h | h
  · rw [show sat V u = V by simp [sat, min_eq_left h.le, max_eq_right (by linarith : -V ≤ V)]]
    exact h.ne
  · rw [show sat V u = -V from max_eq_left ((min_le_right _ _).trans (by linarith))]
    intro e
    linarith

/-! ## The platform -/

variable (y : LimitedPI)

/-- The modulation limit `V_max = V_dc/√3`. -/
def Vmax : ℝ := y.Vdc / Real.sqrt 3

/-- The voltage the inverter applies: the PI command saturated to the linear range. -/
def applied (x : ℝ²) : ℝ := sat y.Vmax (y.design.control y.iref x)

/-- The platform field `(di/dt, dξ/dt)` with `L di/dt = −R i + sat_{V_max}(Kp (i* − i) + Ki ξ)`,
`dξ/dt = i* − i`. -/
def limitedField (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![(-y.design.R * x 0 + y.applied x) / y.design.L, y.iref - x 0]

/-- The operating point `(i*, R i*/Ki)`, the design equilibrium. -/
def point : ℝ² := y.design.equilibrium y.iref

/-- The platform field translated so that the operating point is the origin. -/
def field (z : ℝ²) : ℝ² := y.limitedField (z + y.point)

@[simp, powerlib_foundation] theorem point_zero : y.point 0 = y.iref := by
  simp [point, PIParams.equilibrium]

@[simp, powerlib_foundation] theorem point_one :
    y.point 1 = y.design.R * y.iref / y.design.Ki := by
  simp [point, PIParams.equilibrium]

/-- The command at the operating point. Static evidence on the implementation. -/
@[powerlib_foundation] theorem control_point :
    y.design.control y.iref y.point = y.design.Ki * (y.design.R * y.iref / y.design.Ki) := by
  simp [PIParams.control]

/-- With integral action the command at the operating point is the steady voltage `R i*`. Static
evidence on the implementation. -/
@[powerlib_foundation] theorem control_point_of_ne (hKi : y.design.Ki ≠ 0) :
    y.design.control y.iref y.point = y.design.R * y.iref := by
  rw [control_point, mul_div_cancel₀ _ hKi]

@[powerlib_foundation] theorem abs_control_point_le :
    |y.design.control y.iref y.point| ≤ |y.design.R * y.iref| := by
  by_cases hKi : y.design.Ki = 0
  · rw [control_point, hKi, zero_mul, abs_zero]
    exact abs_nonneg _
  · rw [control_point_of_ne y hKi]

/-- Wherever the command is in range the platform field is the design field. Static evidence on
the implementation. -/
@[powerlib_foundation] theorem limitedField_eq_of_abs_le {x : ℝ²}
    (h : |y.design.control y.iref x| ≤ y.Vmax) :
    y.limitedField x = y.design.field y.iref x := by
  simp only [limitedField, applied, sat_of_abs_le h, PIParams.field]

@[powerlib_foundation] theorem continuous_control_shift :
    Continuous fun z : ℝ² => y.design.control y.iref (z + y.point) := by
  unfold PIParams.control
  fun_prop

/-- The unsaturated design field about the operating point is smooth. -/
@[powerlib_foundation] theorem contDiff_designField :
    ContDiff ℝ 1 (fun z => y.design.field y.iref (z + y.point)) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [PIParams.field, PIParams.control] <;> fun_prop

/-! ### The modulation range (static evidence) -/

/-- With `V_dc ≥ 0` the applied voltage lies in the linear range. -/
@[powerlib_foundation] theorem abs_applied_le (hV : 0 ≤ y.Vdc) (x : ℝ²) :
    |y.applied x| ≤ y.Vmax := by
  have h := abs_sat_le y.Vmax (y.design.control y.iref x)
  have hm : 0 ≤ y.Vmax := div_nonneg hV (Real.sqrt_nonneg 3)
  rwa [abs_of_nonneg hm] at h

/-- Every voltage the platform applies, as the space vector `sat(u) e^{jθ}` at any frame angle
`θ`, is produced by leg voltages in `[0, V_dc]` (`Drives.Modulation.svpwm_linearRange`). -/
@[powerlib_foundation] theorem applied_synthesizable (hV : 0 ≤ y.Vdc) (x : ℝ²) (θ : ℝ) :
    ∃ xa xb xc : ℝ, xa ∈ Icc 0 y.Vdc ∧ xb ∈ Icc 0 y.Vdc ∧ xc ∈ Icc 0 y.Vdc ∧
      Transform.SpaceVector.clarke xa xb xc =
        (y.applied x : ℂ) * Complex.exp (θ * Complex.I) := by
  apply Drives.Modulation.svpwm_linearRange
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact y.abs_applied_le hV x

/-- `V_max` is the largest synthesizable circle: every vector of modulus `ρ ≥ 0` is produced by leg
voltages in `[0, V_dc]` iff `ρ ≤ V_max` (`Drives.Modulation.maxCircle_radius_le`,
`Drives.Modulation.svpwm_linearRange`). -/
@[powerlib_foundation] theorem circle_synthesizable_iff {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ u : ℂ, ‖u‖ = ρ → ∃ xa xb xc : ℝ, xa ∈ Icc 0 y.Vdc ∧ xb ∈ Icc 0 y.Vdc ∧
      xc ∈ Icc 0 y.Vdc ∧ Transform.SpaceVector.clarke xa xb xc = u) ↔ ρ ≤ y.Vmax :=
  ⟨Drives.Modulation.maxCircle_radius_le _ ρ hρ,
    fun h u hu => Drives.Modulation.svpwm_linearRange _ u (hu ▸ h)⟩

/-! ### Implementation evidence (private) -/

/-- With headroom, near the operating point the limit is inactive. -/
private theorem field_eventuallyEq_design (hh : |y.design.R * y.iref| < y.Vmax) :
    y.field =ᶠ[𝓝 0] fun z => y.design.field y.iref (z + y.point) := by
  have hc := (continuous_abs.comp y.continuous_control_shift).tendsto 0
  have h0 : |y.design.control y.iref (0 + y.point)| < y.Vmax := by
    rw [zero_add]
    exact y.abs_control_point_le.trans_lt hh
  filter_upwards [hc.eventually (eventually_lt_nhds h0)] with z hz
  exact y.limitedField_eq_of_abs_le hz.le

/-- With headroom the platform field is `C¹` near the operating point, where it is the
unsaturated design field. Static evidence on the implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem contDiffAt_field (hh : |y.design.R * y.iref| < y.Vmax) :
    ContDiffAt ℝ 1 y.field 0 :=
  y.contDiff_designField.contDiffAt.congr_of_eventuallyEq (y.field_eventuallyEq_design hh)

/-- At an equilibrium the unsaturated design field about the operating point is the linear
zero-input field of the design plant. -/
private theorem designField_shift_of_zero (h0 : y.design.field y.iref y.point = 0) :
    (fun z => y.design.field y.iref (z + y.point)) =
      affineLinearVectorField y.design.model.A 0 := by
  have he : IsEquilibrium (y.design.model.inputField fun _ => y.iref) y.point := by
    rw [IsEquilibrium, PIParams.model_field]
    exact h0
  have h := LTI.inputField_shift y.design.model he
  funext z
  rw [← congrFun h z]
  exact (y.design.model_field _ _).symm

private theorem designField_shift (hKi : y.design.Ki ≠ 0) :
    (fun z => y.design.field y.iref (z + y.point)) =
      affineLinearVectorField y.design.model.A 0 := by
  refine y.designField_shift_of_zero ?_
  have h := y.design.isEquilibrium hKi y.iref
  rw [IsEquilibrium, PIParams.model_field] at h
  exact h

/-- With headroom and integral action, near the operating point the platform field is the design's
linear zero-input field. -/
private theorem field_eventuallyEq_linear (hKi : y.design.Ki ≠ 0)
    (hh : |y.design.R * y.iref| < y.Vmax) :
    y.field =ᶠ[𝓝 0] affineLinearVectorField y.design.model.A 0 := by
  rw [← y.designField_shift hKi]
  exact y.field_eventuallyEq_design hh

/-- A design loop with `(R + Kp)/L ≥ 0` and `Ki/L > 0` is Lyapunov stable: the energy
`i² + (Ki/L) ξ²` does not increase (`d/dt = −2 (R + Kp)/L · i²`). -/
@[tmio TM] private theorem lyapunovStable_of_nonneg (p : PIParams) (ha : 0 ≤ (p.R + p.Kp) / p.L)
    (hb : 0 < p.Ki / p.L) :
    connection% (p ∈ PIParams.family.den (.flow .lyapunovStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% PIParams.family_isLinear.mem_den_flow)]
  change LyapunovStable (affineLinearVectorField p.model.A 0) 0
  set s := Real.sqrt (p.Ki / p.L) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hb
  have hss : s * s = p.Ki / p.L := Real.mul_self_sqrt hb.le
  let T : ℝ² →L[ℝ] ℝ² := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 0; 0, s]
  have hT : ∀ x : ℝ², T x = WithLp.toLp 2 ![x 0, s * x 1] := by
    intro x
    ext i
    fin_cases i <;> simp [T, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  have hf : ∀ x : ℝ², affineLinearVectorField p.model.A 0 x =
      WithLp.toLp 2 ![-(p.R + p.Kp) / p.L * x 0 + p.Ki / p.L * x 1, -x 0] := by
    intro x
    ext i
    fin_cases i <;> simp [affineLinearVectorField, PIParams.model,
      Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine Dynamics.lyapunovStable_of_inner_nonpos (by norm_num) T ?_ ?_
  · intro x y hxy
    rw [hT, hT] at hxy
    have h0 := congrArg (fun z : ℝ² => z 0) hxy
    have h1 := congrArg (fun z : ℝ² => z 1) hxy
    simp at h0 h1
    ext i
    fin_cases i
    · exact h0
    · rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hs0.ne'
  · intro x
    rw [hf, hT, hT]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    have hprod : s * x 0 * (s * x 1) = p.Ki / p.L * x 0 * x 1 := by
      rw [show s * x 0 * (s * x 1) = (s * s) * x 0 * x 1 by ring, hss]
    have hneg : (-p.Kp + -p.R) / p.L = -((p.R + p.Kp) / p.L) := by ring
    rw [hneg, hprod]
    nlinarith [mul_nonneg ha (sq_nonneg (x 0))]

end LimitedPI

/-! ## The implementation family -/

/-- Requirements on a voltage-limited loop: the lifted design requirements and the realistic
constraints. -/
inductive LimitRequirement
  /-- The design loop meets `q` (`PIParams.family`). -/
  | design (q : Spectral.Requirement)
  /-- A positive inductance `0 < L`. -/
  | inductance
  /-- Integral action `Ki ≠ 0`: the integrator holds the operating point. -/
  | integral
  /-- A positive DC-link voltage `0 < V_dc`. -/
  | dcLink
  /-- Headroom: the operating voltage lies strictly inside the linear range, `|R i*| < V_dc/√3`. -/
  | headroom
  /-- Overload: the operating voltage lies beyond the linear range, `V_dc/√3 < |R i*|`. -/
  | overload

namespace LimitedPI

/-- Satisfaction of a platform requirement. -/
def Meets (y : LimitedPI) : LimitRequirement → Prop
  | .design q => PIParams.family.meets y.design q
  | .inductance => 0 < y.design.L
  | .integral => y.design.Ki ≠ 0
  | .dcLink => 0 < y.Vdc
  | .headroom => |y.design.R * y.iref| < y.Vmax
  | .overload => y.Vmax < |y.design.R * y.iref|

/-- The translation of the sentences into platform requirements: the local ones into a stable
design with headroom, instability into an unstable design with headroom, passivity into nothing,
the remaining sentences into the whole, inconsistent, language. -/
def translate : Sentence → Set LimitRequirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.design .stable, .headroom}
  | .flow .unstable => {.design .unstable, .headroom}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The voltage-limited platforms, each read as its field about the operating point. -/
def family : Family LimitedPI LimitRequirement 2 0 :=
  ⟨fun y => Port.System.autonomous y.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous field := fun _ => rfl

/-! ### Implementation evidence (private) -/

private theorem ki_ne_of_stable {p : PIParams} (h : PIParams.Stable p) : p.Ki ≠ 0 := by
  intro h0
  have := h.2
  rw [h0, zero_div] at this
  exact lt_irrefl _ this

/-- Within headroom a stable design makes the platform locally exponentially stable. -/
@[tmio MI] private theorem les_of_stable {y : LimitedPI} (hs : PIParams.Stable y.design)
    (hh : |y.design.R * y.iref| < y.Vmax) :
    connection% (y ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocallyExponentiallyStable y.field 0
  exact Dynamics.locallyExponentiallyStable_congr_nhds
    (y.field_eventuallyEq_linear (ki_ne_of_stable hs) hh)
    (holds_of_isHurwitz 0 (P := .locallyExponentiallyStable) trivial
      ((PIParams.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).mp ((PIParams.isHurwitz_iff_div y.design).mpr hs)))

/-- Within headroom an unstable design makes the platform unstable: near the operating point the
platform is the affine design field, unstable at a root in the right half plane or because the
point is not an equilibrium. -/
@[tmio MI] private theorem unstable_of_unstable {y : LimitedPI} (hu : PIParams.Unstable y.design)
    (hh : |y.design.R * y.iref| < y.Vmax) :
    connection% (y ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable y.field 0
  refine (Dynamics.unstable_congr_nhds (y.field_eventuallyEq_design hh)).mpr ?_
  by_cases h0 : y.design.field y.iref (0 + y.point) = 0
  · rw [zero_add] at h0
    rw [y.designField_shift_of_zero h0]
    obtain ⟨s, hs, hre⟩ := y.design.exists_root_of_unstable hu
    exact unstable_of_root 0 hs hre
  · exact Dynamics.unstable_of_ne_zero y.contDiff_designField h0

/-- Within headroom local asymptotic and local exponential stability of the platform hold exactly
for a stable design: near the operating point the platform is the design's affine loop, so these
sentences are decided by that affine piece (`Dynamics.holds_iff_of_eventuallyEq_inputField`). -/
@[tmio MI] private theorem mem_den_attractive_iff {y : LimitedPI} (hh : |y.design.R * y.iref| < y.Vmax)
    {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    connection% (y ∈ family.den (.flow P) ↔ PIParams.Stable y.design) := by
  change y ∈ family.den (.flow P) ↔ PIParams.Stable y.design
  have hd : y.field =ᶠ[𝓝 0]
      fun z => y.design.model.inputField (fun _ => y.iref) (z + y.point) := by
    simpa only [PIParams.model_field] using y.field_eventuallyEq_design hh
  rw [(connection_proof% family_isAutonomous.mem_den_flow), Dynamics.holds_iff_of_eventuallyEq_inputField _ _ hd hP,
    ← (connection_proof% PIParams.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)),
    (connection_proof% PIParams.isHurwitz_iff_div)]
  exact ⟨And.right, fun hs => ⟨y.design.isEquilibrium (ki_ne_of_stable hs) y.iref, hs⟩⟩

/-- With overload and integral action, near the operating point the saturation is constant. -/
private theorem field_eventuallyEq_overload (y : LimitedPI) (hKi : y.design.Ki ≠ 0)
    (ho : y.Vmax < |y.design.R * y.iref|) :
    y.field =ᶠ[𝓝 0] fun z => WithLp.toLp 2
      ![(-y.design.R * (z + y.point) 0 + sat y.Vmax (y.design.R * y.iref)) / y.design.L,
        y.iref - (z + y.point) 0] := by
  have hc := y.continuous_control_shift.tendsto 0
  rw [zero_add, y.control_point_of_ne hKi] at hc
  filter_upwards [hc.eventually (sat_eventually_eq ho)] with z hz
  simp only [field, limitedField, applied, hz]

/-- With overload the operating point is not an equilibrium: the platform is unstable. -/
@[tmio TM] private theorem unstable_of_overload (y : LimitedPI) (hL : y.design.L ≠ 0)
    (hKi : y.design.Ki ≠ 0) (hV : 0 < y.Vdc) (ho : y.Vmax < |y.design.R * y.iref|) :
    connection% (y ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable y.field 0
  refine (Dynamics.unstable_congr_nhds (y.field_eventuallyEq_overload hKi ho)).mpr
    (Dynamics.unstable_of_ne_zero ?_ ?_)
  · rw [contDiff_euclidean]
    intro i
    fin_cases i <;> simp <;> fun_prop
  · intro h
    have h0 := congrArg (fun z : ℝ² => z 0) h
    simp [hL] at h0
    have hVm : 0 ≤ y.Vmax := div_nonneg hV.le (Real.sqrt_nonneg 3)
    exact sat_ne_of_lt_abs hVm ho (by linarith)

/-- No platform is globally exponentially stable. From `(0, ξ₀)` the current obeys
`|di/dt| ≤ (|R|/|L|) |i − i*| + (|R i*| + |V_max|)/|L|` and stays below a bound `B` on `[0, T]`
(Grönwall), so the integrator moves by at most `B T`; an exponential estimate with constants
`C, a` halves the distance by `T = log (2C)/a`, which fails for `ξ₀ = 2 B T + 1`. -/
@[tmio TM] private theorem not_globallyExponentiallyStable (y : LimitedPI) :
    connection% (y ∉ family.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change ¬ Flow.GloballyExponentiallyStable y.field 0
  rintro ⟨-, hfc, C, a, hC, ha, hest⟩
  have hT : 0 ≤ Real.log (2 * C) / a := div_nonneg (Real.log_nonneg (by linarith)) ha.le
  set T := Real.log (2 * C) / a with hTdef
  have hCT : C * Real.exp (-a * T) = 1 / 2 := by
    have : -a * T = -Real.log (2 * C) := by
      rw [hTdef]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by linarith)]
    field_simp
  set K := |y.design.R| / |y.design.L| with hK
  set ε := (|y.design.R * y.iref| + |y.Vmax|) / |y.design.L| with hε
  have hgc : Continuous (gronwallBound 0 K ε) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gronwallBound 0 K ε x).continuousAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 T) hgc.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT⟩)
  obtain ⟨φ, hφ0, hφ⟩ := hfc 0 (WithLp.toLp 2 ![0, 2 * B * T + 1])
  have hd : ∀ t ∈ Ici (0 : ℝ), ∀ i : Fin 2,
      HasDerivWithinAt (fun s => φ s i) (y.field (φ t) i) (Ici 0) t :=
    fun t ht i => (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i).hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)
  have hf0 : ∀ z : ℝ², y.field z 0 =
      (-y.design.R * (z 0 + y.iref) + y.applied (z + y.point)) / y.design.L := by
    intro z
    simp [field, limitedField]
  have hf1 : ∀ z : ℝ², y.field z 1 = -z 0 := by
    intro z
    simp [field, limitedField]
  have hbound0 : ∀ z : ℝ², ‖y.field z 0‖ ≤ K * ‖z 0‖ + ε := by
    intro z
    rw [hf0, Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    have hs := abs_sat_le y.Vmax (y.design.control y.iref (z + y.point))
    have hn : |-y.design.R * (z 0 + y.iref) + y.applied (z + y.point)| ≤
        |y.design.R| * |z 0| + (|y.design.R * y.iref| + |y.Vmax|) := by
      have e : -y.design.R * (z 0 + y.iref) + y.applied (z + y.point) =
          -(y.design.R * z 0) + (-(y.design.R * y.iref) + y.applied (z + y.point)) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul]
      have := abs_add_le (-(y.design.R * y.iref)) (y.applied (z + y.point))
      rw [abs_neg] at this
      have hs' : |y.applied (z + y.point)| ≤ |y.Vmax| := hs
      linarith
    calc |-y.design.R * (z 0 + y.iref) + y.applied (z + y.point)| / |y.design.L|
        ≤ (|y.design.R| * |z 0| + (|y.design.R * y.iref| + |y.Vmax|)) / |y.design.L| :=
          div_le_div_of_nonneg_right hn (abs_nonneg _)
      _ = K * |z 0| + ε := by rw [hK, hε]; ring
  have hcont : ∀ i : Fin 2, ContinuousOn (fun s => φ s i) (Icc 0 T) := fun i t ht =>
    (hd t ht.1 i).continuousWithinAt.mono Icc_subset_Ici_self
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => φ s 0)
    (f' := fun s => y.field (φ s) 0) (δ := 0) (K := K) (ε := ε) (a := 0) (b := T) (hcont 0)
    (fun t ht => (hd t ht.1 0).mono (Ici_subset_Ici.mpr ht.1)) (by simp [hφ0])
    (fun t _ => hbound0 (φ t))
  have hb1 : ∀ t ∈ Ico (0 : ℝ) T, ‖y.field (φ t) 1‖ ≤ B := by
    intro t ht
    rw [hf1, norm_neg]
    have h1 := hg t (Ico_subset_Icc_self ht)
    rw [sub_zero] at h1
    exact h1.trans ((le_abs_self _).trans (hB t (Ico_subset_Icc_self ht)))
  have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun s => φ s 1)
    (f' := fun s => y.field (φ s) 1) (C := B) (hcont 1)
    (fun t ht => (hd t ht.1 1).mono (Ici_subset_Ici.mpr ht.1)) hb1 T ⟨hT, le_rfl⟩
  have he := hest 0 T φ (hφ.mono Icc_subset_Ici_self) T ⟨hT, le_rfl⟩
  simp only [sub_zero] at he
  rw [hCT, hφ0] at he
  have hn : ‖(WithLp.toLp 2 ![0, 2 * B * T + 1] : ℝ²)‖ = 2 * B * T + 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  rw [hn] at he
  have h1 : ‖φ T 1‖ ≤ ‖φ T‖ := PiLp.norm_apply_le _ _
  simp only [hφ0, sub_zero] at hmv
  have hξ : (![0, 2 * B * T + 1] : Fin 2 → ℝ) 1 = 2 * B * T + 1 := by simp
  rw [hξ, Real.norm_eq_abs] at hmv
  rw [Real.norm_eq_abs] at h1
  have := abs_sub_abs_le_abs_sub (2 * B * T + 1) (φ T 1)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * B * T + 1), abs_sub_comm] at this
  linarith

/-! ### Translation of the platform family (I) -/

/-- The whole platform requirement language is inconsistent: headroom and overload exclude each
other. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize family.meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.realize_univ_eq_empty_of .headroom .overload
    fun y (h1 : |y.design.R * y.iref| < y.Vmax) (h2 : y.Vmax < |y.design.R * y.iref|) => by
      linarith

/-- Every translation of the platform family is sound: with headroom a stable design gives local
exponential stability and an unstable design instability (locality of the local sentences), and
passivity holds without requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same (Rs := {.design .stable, .headroom})
    (Ru := {.design .unstable, .headroom}) (fun s => ?_) realize_univ (fun y hy => ?_)
    (fun y hy => ?_) family_isAutonomous.den_passive
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  · rw [(connection_proof% TMIO.mem_realize)] at hy
    exact family_isAutonomous.mem_den_flow.mpr ((family_isAutonomous.mem_den_flow.mp (les_of_stable (hy (.design .stable) (by simp))
      (hy .headroom (by simp)))))
  · rw [(connection_proof% TMIO.mem_realize)] at hy
    exact family_isAutonomous.mem_den_flow.mpr
      ((family_isAutonomous.mem_den_flow.mp (unstable_of_unstable (hy (.design .unstable) (by simp)) (hy .headroom (by simp)))))

/-- Passivity is translated exactly: a platform without ports is passive. -/
@[tmio TM, powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- Within headroom the local asymptotic and local exponential translations are exact: the
platform is locally asymptotically (exponentially) stable exactly when its design is stable,
`(R + Kp)/L > 0 ∧ Ki/L > 0`. The saturated field is not `C¹`, but near the operating point it is
the design's affine loop, which decides these sentences
(`Dynamics.holds_iff_of_eventuallyEq_inputField`). -/
@[tmio TM, powerlib_domain] theorem exactUnder_attractive {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    connection% (family.ExactUnder {.headroom} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have ht : family.translate (.flow P) = {.design .stable, .headroom} := by
    rcases hP with rfl | rfl <;> rfl
  refine Spectral.exactUnder_iff_forall.mpr fun y hΔ => ?_
  have hh : |y.design.R * y.iref| < y.Vmax := (TMIO.mem_realize _ _ _).mp hΔ .headroom rfl
  rw [ht, (connection_proof% mem_den_attractive_iff hh hP), (connection_proof% TMIO.mem_realize)]
  refine ⟨fun h => h (.design .stable) (by simp), fun hs => ?_⟩
  rintro q (rfl | rfl)
  · exact hs
  · exact hh

/-- With `L > 0` and headroom, a platform is locally asymptotically (exponentially) stable iff
`R + Kp > 0 ∧ Ki > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff (y : LimitedPI) (hL : 0 < y.design.L)
    (hh : |y.design.R * y.iref| < y.Vmax) {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    connection% (y ∈ family.den (.flow P) ↔
      y ∈ {y : LimitedPI | 0 < y.design.R + y.design.Kp ∧ 0 < y.design.Ki}) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_attractive_iff hh hP)]
  change PIParams.Stable y.design ↔ 0 < y.design.R + y.design.Kp ∧ 0 < y.design.Ki
  rw [PIParams.Stable, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]

/-- Within a positive inductance, integral action and headroom, instability is translated exactly:
a design that is not unstable, `(R + Kp)/L ≥ 0` and `Ki/L > 0`, is Lyapunov stable, and so is
the platform. -/
@[tmio TM, powerlib_domain] theorem exactUnder_unstable :
    connection% (family.ExactUnder {.inductance, .integral, .headroom} (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_iff_forall.mpr fun y hΔ => ⟨fun h => ?_, fun hd => ?_⟩
  · rw [(connection_proof% TMIO.mem_realize)] at h
    exact family_isAutonomous.mem_den_flow.mpr ((family_isAutonomous.mem_den_flow.mp (unstable_of_unstable
      (h (.design .unstable) (by simp [family, translate]))
      (h .headroom (by simp [family, translate])))))
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hL : 0 < y.design.L := hΔ .inductance (by simp)
  have hKi : y.design.Ki ≠ 0 := hΔ .integral (by simp)
  have hh : |y.design.R * y.iref| < y.Vmax := hΔ .headroom (by simp)
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl)
  · show PIParams.Unstable y.design
    by_contra hn
    simp only [PIParams.Unstable, not_or, not_lt] at hn
    have hb : 0 < y.design.Ki / y.design.L :=
      lt_of_le_of_ne hn.2 (Ne.symm (div_ne_zero hKi hL.ne'))
    rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hd
    exact hd (Dynamics.lyapunovStable_congr_nhds (y.field_eventuallyEq_linear hKi hh)
      ((PIParams.family_isLinear.mem_den_flow.mp (lyapunovStable_of_nonneg y.design hn.1 hb))))
  · exact hh

/-- A lossless platform: the design `L = R = Ki = 1`, `Kp = −1` (`R + Kp = 0`), at `i* = 0`,
`V_dc = 1`. -/
def center : LimitedPI := ⟨⟨1, 1, -1, 1⟩, 0, 1⟩

/-- The lossless platform is Lyapunov stable: its design is a centre and the limit is inactive near
the operating point. -/
@[tmio TM, powerlib_domain] theorem center_mem_den_lyapunovStable :
    connection% (center ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have hh : |center.design.R * center.iref| < center.Vmax := by
    simp only [Vmax, center, mul_zero, abs_zero]
    positivity
  exact Dynamics.lyapunovStable_congr_nhds
    (center.field_eventuallyEq_linear (by norm_num [center]) hh)
    ((PIParams.family_isLinear.mem_den_flow.mp (lyapunovStable_of_nonneg center.design (by norm_num [center]) (by norm_num [center]))))

/-- Lyapunov stability is not translated exactly within all realistic constraints with headroom:
the lossless platform is Lyapunov stable while its design is not stable (`R + Kp = 0`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.inductance, .integral, .dcLink, .headroom}
      (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exactUnder_of_witness ?_ center_mem_den_lyapunovStable
    (q := .design .stable) (by simp [family, translate]) fun hs => ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · show (0 : ℝ) < 1; norm_num
    · show (1 : ℝ) ≠ 0; norm_num
    · show (0 : ℝ) < 1; norm_num
    · show |(1 : ℝ) * 0| < 1 / Real.sqrt 3
      rw [mul_zero, abs_zero]
      positivity
  · have := (hs : PIParams.Stable center.design).1
    norm_num [center] at this

/-- No platform is globally exponentially stable: the voltage limit bounds the rate at which a
large integrator state unwinds. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyExponentiallyStable (y : LimitedPI) :
    connection% (y ∉ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  exact (fun hFlowConnection => (not_globallyExponentiallyStable y) (family_isAutonomous.mem_den_flow.mpr hFlowConnection))

/-- Global exponential stability is translated exactly into the whole, inconsistent, language:
no platform satisfies it. -/
@[tmio TM, powerlib_domain] theorem exact_globallyExponentiallyStable :
    connection% (family.Exact (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_univ realize_univ rfl
    (Set.eq_empty_iff_forall_notMem.mpr not_mem_den_globallyExponentiallyStable)

/-- With a positive inductance, integral action, a positive DC link and overload, the platform is
unstable whatever the design: the operating point is not an equilibrium. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_overload (y : LimitedPI) (hL : 0 < y.design.L)
    (hKi : y.design.Ki ≠ 0) (hV : 0 < y.Vdc) (ho : y.Vmax < |y.design.R * y.iref|) :
    connection% (y ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr ((family_isAutonomous.mem_den_flow.mp (y.unstable_of_overload hL.ne' hKi hV ho)))

/-! ## The implementation over the PI design (M–I) -/

/-- The voltage-limited platforms as an implementation of the single-axis PI design
`PIParams.family`: the modulation limit is a hardware constraint, and each platform realizes its
design. -/
def implementation :
    Implementation PIParams Spectral.Requirement LimitedPI LimitRequirement 2 1 2 0 :=
  { model := PIParams.family, impl := family, realizes := Implementation.ofDesign design }

private theorem implementation_model : implementation.model = PIParams.family := rfl

private theorem implementation_impl : implementation.impl = family := rfl

/-- Within integral action and headroom, Lyapunov stability, local asymptotic and local
exponential stability and instability are realized exactly, for every sign of `L`: near the
operating point the limit is inactive and the platform is the design's linear loop. -/
@[tmio MI, powerlib_domain] theorem realizationExactUnder_local {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable ∨ P = .unstable) :
    connection% (implementation.RealizationExactUnder {.integral, .headroom} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  refine Implementation.realizationExactUnder_of_design (I := implementation) rfl ?_
  rw [implementation_model, implementation_impl]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  refine and_congr_left fun hΔ => ?_
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hKi : y.design.Ki ≠ 0 := hΔ .integral (by simp)
  have hh : |y.design.R * y.iref| < y.Vmax := hΔ .headroom (by simp)
  rw [(connection_proof% PIParams.family_isLinear.mem_den_flow), (connection_proof% family_isAutonomous.mem_den_flow)]
  exact Dynamics.holds_congr_nhds (y.field_eventuallyEq_linear hKi hh) hP

/-- Within headroom alone, local asymptotic and local exponential stability are realized soundly,
by the static reduction `Implementation.realizationSoundUnder_of_design`: the exact design
translation (`PIParams.exact`), the sound platform translation (`chain_le_semantics`), and a
stable design with headroom meeting the platform translation. -/
@[tmio MI, powerlib_domain] theorem realizationSoundUnder_attractive {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    connection% (implementation.RealizationSoundUnder {.headroom} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hPa : P.Attractive := by rcases hP with rfl | rfl <;> trivial
  have hM := PIParams.exact (Or.inl hPa)
  have hI := chain_le_semantics
  unfold powerlib.TMIO.Statement at hM hI
  have hMt : PIParams.family.translate (.flow P) = {.stable} := by
    rcases hP with rfl | rfl <;> rfl
  have hIt : family.translate (.flow P) = {.design .stable, .headroom} := by
    rcases hP with rfl | rfl <;> rfl
  refine Implementation.realizationSoundUnder_of_design (I := implementation) rfl (ΔM := ∅)
    (Family.exactUnder_empty_iff.mpr hM) (Family.chain_le_semantics_iff.mp hI _)
    (fun y _ => by rw [TMIO.realize_empty]; trivial) fun y hΔ hd => ?_
  rw [Set.union_empty, implementation_model, hMt, (connection_proof% TMIO.mem_realize)] at hd
  rw [implementation_impl, (connection_proof% TMIO.mem_realize)] at hΔ ⊢
  rw [hIt]
  intro q hq
  rcases hq with rfl | rfl
  · exact hd .stable rfl
  · exact hΔ .headroom rfl

/-- The nominal design `L = R = Kp = Ki = 1`. -/
def nominal : PIParams := ⟨1, 1, 1, 1⟩

/-- The nominal design satisfies every attractive sentence. -/
@[tmio TM, powerlib_domain] theorem nominal_mem_den {P : Flow.Property} (hP : P.Attractive) :
    connection% (nominal ∈ PIParams.family.den (.flow P)) := by
  have h := PIParams.mem_den_iff nominal (by norm_num [nominal]) (Or.inl hP)
  unfold powerlib.TMIO.Statement at h ⊢
  exact h.mpr (by norm_num [nominal])

/-- An overloaded platform: the nominal design at `i* = 1` with `V_dc = 1`, so `R i* = 1` exceeds
`V_max = 1/√3`. -/
def overloaded : LimitedPI := ⟨nominal, 1, 1⟩

private theorem overloaded_overload :
    overloaded.Vmax < |overloaded.design.R * overloaded.iref| := by
  simp only [Vmax, overloaded, nominal, one_mul, abs_one]
  rw [div_lt_one (by positivity), Real.lt_sqrt (by norm_num)]
  norm_num

/-- The overloaded platform is unstable. -/
@[tmio TM, powerlib_domain] theorem overloaded_mem_den_unstable :
    connection% (overloaded ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_overload overloaded (by norm_num [overloaded, nominal])
    (by norm_num [overloaded, nominal]) (by norm_num [overloaded]) overloaded_overload

/-- Within overload (with a positive inductance, integral action and a positive DC link)
instability is realized soundly: every such platform is unstable. -/
@[tmio MI, powerlib_domain] theorem realizationSoundUnder_unstable_of_overload :
    connection% (implementation.RealizationSoundUnder {.inductance, .integral, .dcLink, .overload}
      (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement Implementation.RealizationSoundUnder
  rintro y ⟨-, hΔ⟩
  rw [implementation_impl, (connection_proof% TMIO.mem_realize)] at hΔ
  have h := mem_den_unstable_of_overload y (hΔ .inductance (by simp)) (hΔ .integral (by simp))
    (hΔ .dcLink (by simp)) (hΔ .overload (by simp))
  unfold powerlib.TMIO.Statement at h
  exact h

/-- Within overload local exponential stability is not realized soundly: the overloaded platform
has a locally exponentially stable design and is unstable. -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder_locallyExponentiallyStable :
    connection% (¬ implementation.RealizationSoundUnder {.inductance, .integral, .dcLink, .overload}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hd := nominal_mem_den (P := .locallyExponentiallyStable) trivial
  have hu := overloaded_mem_den_unstable
  unfold powerlib.TMIO.Statement at hd hu
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation) (y := overloaded)
    rfl hd ?_ fun hmem => ?_
  · rw [implementation_impl, (connection_proof% TMIO.mem_realize)]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · show (0 : ℝ) < 1; norm_num
    · show (1 : ℝ) ≠ 0; norm_num
    · show (0 : ℝ) < 1; norm_num
    · exact overloaded_overload
  rw [implementation_impl, (connection_proof% family_isAutonomous.mem_den_flow)] at hmem
  rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hu
  exact hu hmem.lyapunovStable

/-- An unloaded platform: the nominal design at `i* = 0` with `V_dc = 1`. -/
def unloaded : LimitedPI := ⟨nominal, 0, 1⟩

/-- Global exponential stability is not realized soundly within all realistic constraints with
headroom: the nominal design is globally exponentially stable, the unloaded platform is not. -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder_globallyExponentiallyStable :
    connection% (¬ implementation.RealizationSoundUnder {.inductance, .integral, .dcLink, .headroom}
      (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hd := nominal_mem_den (P := .globallyExponentiallyStable) trivial
  have hn := not_mem_den_globallyExponentiallyStable unloaded
  unfold powerlib.TMIO.Statement at hd hn
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation) (y := unloaded)
    rfl hd ?_ hn
  rw [implementation_impl, (connection_proof% TMIO.mem_realize)]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · show (0 : ℝ) < 1; norm_num
  · show (1 : ℝ) ≠ 0; norm_num
  · show (0 : ℝ) < 1; norm_num
  · show |(1 : ℝ) * 0| < 1 / Real.sqrt 3
    rw [mul_zero, abs_zero]
    positivity

/-- Global exponential stability is realized completely, without constraints, vacuously: no
platform satisfies it. -/
@[tmio MI, powerlib_domain] theorem realizationCompleteUnder_globallyExponentiallyStable :
    connection% (implementation.RealizationCompleteUnder ∅
      (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement Implementation.RealizationCompleteUnder
  rintro y ⟨hy, -⟩
  have hn := not_mem_den_globallyExponentiallyStable y
  unfold powerlib.TMIO.Statement at hn
  exact (hn hy).elim

/-- A drifting platform: the design `L = R = 1`, `Kp = Ki = 0` (no integral action) at `i* = 1`
with `V_dc = 3` (`|R i*| = 1 < √3 = V_max`). -/
def drifting : LimitedPI := ⟨⟨1, 1, 0, 0⟩, 1, 3⟩

private theorem drifting_headroom : |drifting.design.R * drifting.iref| < drifting.Vmax := by
  simp only [Vmax, drifting, one_mul, abs_one]
  rw [lt_div_iff₀ (by positivity), one_mul, Real.sqrt_lt' (by norm_num)]
  norm_num

/-- Without integral action the drifting design is Lyapunov stable: the current decays and the
integrator only drifts by a bounded amount (`i² + (ξ − i)²` does not increase). -/
@[tmio TM, powerlib_domain] theorem drifting_design_mem_den_lyapunovStable :
    connection% (drifting.design ∈ PIParams.family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% PIParams.family_isLinear.mem_den_flow)]
  let T : ℝ² →L[ℝ] ℝ² := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 0; -1, 1]
  have hT : ∀ x : ℝ², T x = WithLp.toLp 2 ![x 0, -x 0 + x 1] := by
    intro x
    ext i
    fin_cases i <;> simp [T, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  have hf : ∀ x : ℝ², affineLinearVectorField drifting.design.model.A 0 x =
      WithLp.toLp 2 ![-x 0, -x 0] := by
    intro x
    ext i
    fin_cases i <;> simp [affineLinearVectorField, PIParams.model, drifting,
      Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine Dynamics.lyapunovStable_of_inner_nonpos (by norm_num) T ?_ ?_
  · intro x y hxy
    rw [hT, hT] at hxy
    have h0 := congrArg (fun z : ℝ² => z 0) hxy
    have h1 := congrArg (fun z : ℝ² => z 1) hxy
    simp at h0 h1
    ext i
    fin_cases i
    · exact h0
    · simp; linarith
  · intro x
    rw [hf, hT, hT]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0)]

/-- The drifting platform is unstable: without integral action the operating point `(1, 0)` is not
an equilibrium (the steady voltage `R i* = 1` is never commanded). -/
@[tmio TM, powerlib_domain] theorem drifting_mem_den_unstable :
    connection% (drifting ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  refine (Dynamics.unstable_congr_nhds (drifting.field_eventuallyEq_design drifting_headroom)).mpr
    (Dynamics.unstable_of_ne_zero drifting.contDiff_designField ?_)
  intro h
  have h0 := congrArg (fun z : ℝ² => z 0) h
  simp [drifting, PIParams.field, PIParams.control, point, PIParams.equilibrium] at h0

@[tmio M] private theorem drifting_mem_context :
    connection% (drifting ∈ TMIO.realize implementation.impl.meets {.inductance, .dcLink, .headroom}) := by
  change drifting ∈ TMIO.realize implementation.impl.meets {.inductance, .dcLink, .headroom}
  rw [implementation_impl, (connection_proof% TMIO.mem_realize)]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · show (0 : ℝ) < 1; norm_num
  · show (0 : ℝ) < 3; norm_num
  · exact drifting_headroom

/-- Without integral action Lyapunov stability is not realized soundly, even with headroom: the
drifting platform has a Lyapunov stable design and is unstable. -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder_lyapunovStable :
    connection% (¬ implementation.RealizationSoundUnder {.inductance, .dcLink, .headroom}
      (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hd := drifting_design_mem_den_lyapunovStable
  have hu := drifting_mem_den_unstable
  unfold powerlib.TMIO.Statement at hd hu
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation) rfl hd
    drifting_mem_context fun hmem => ?_
  rw [implementation_impl, (connection_proof% family_isAutonomous.mem_den_flow)] at hmem
  rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hu
  exact hu hmem

/-- Without integral action instability is not realized completely, even with headroom: the
drifting platform is unstable while its design is Lyapunov stable. -/
@[tmio MI, powerlib_domain] theorem not_realizationCompleteUnder_unstable :
    connection% (¬ implementation.RealizationCompleteUnder {.inductance, .dcLink, .headroom}
      (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have hd := drifting_design_mem_den_lyapunovStable
  have hu := drifting_mem_den_unstable
  unfold powerlib.TMIO.Statement at hd hu
  refine Implementation.not_realizationCompleteUnder_of_design (I := implementation) rfl hu
    drifting_mem_context fun hmem => ?_
  rw [implementation_model, (connection_proof% PIParams.family_isLinear.mem_den_flow)] at hmem
  rw [(connection_proof% PIParams.family_isLinear.mem_den_flow)] at hd
  exact hmem hd

end LimitedPI

end powerlib.CurrentControl
