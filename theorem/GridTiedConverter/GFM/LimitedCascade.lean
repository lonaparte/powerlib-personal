import theorem.GridTiedConverter.GFM.InnerCascade
import theorem.GridTiedConverter.CurrentControl.VoltageLimit
import theorem.Drives.Modulation
import theorem.Dynamics.Shift
import theorem.Dynamics.PiecewiseAffine
import theorem.Stack.Implementation
import theorem.SpecialFunctions.Clamp

/-! # The grid-forming inner cascade under the modulation voltage limit: an implementation layer

Model boundary.
* Implementation layer (I, `theorem/Stack/Implementation.lean`). A platform `LimitedCascade`
  realizes its design, the single-axis grid-forming voltage/current cascade `InnerCascade` of the
  model layer `InnerCascade.family` (`theorem/GridTiedConverter/GFM/InnerCascade.lean`: LC filter,
  PI voltage loop on the capacitor, PI current loop on the inductor, ideal feed-forward and
  decoupling), under one realistic constraint the design did not intend: a two-level inverter
  applies only bridge voltages of its linear modulation range, `|e| ≤ V_max = V_dc/√3` (`Vmax`),
  the radius of the largest circle of the voltage hexagon (`theorem/Drives/Modulation.lean`).
* State order `(i, ξ, v, ζ) ∈ ℝ⁴` as in the design. The bridge command is the current-loop output
  plus the capacitor-voltage feed-forward, `e = K_pc (i* − i) + K_ic ξ + v` (`command`); the
  platform field (`limitedField`) is `L i̇ = −R i + sat_{V_max}(e) − v`, `ξ̇ = i* − i`, `C v̇ = i`,
  `ζ̇ = v* − v` with `sat_V(e) = max (−V) (min e V)` (`SpecialFunctions.clampSym`). Continuous
  time, autonomous: the voltage reference `v*` is a parameter of the platform, held constant,
  because whether the limit acts depends on the operating point; the load current is zero, as in
  the design.
* Operating point `(0, 0, v*, 0)` (`point`, the design equilibrium `InnerCascade.equilibrium`),
  whose steady bridge voltage is `v*` (`command_point`). A platform is read as its field translated
  so that the operating point is the origin (`field`); the design is read as the zero-input field
  of its linear plant, its behaviour about every operating point.
* Single-axis idealization of the limit: the other axis carries no voltage, so the applied vector
  is `sat(e) e^{jθ}` in the stationary frame (`applied_synthesizable`); the joint dq limit and its
  priority rules are excluded, as in `theorem/GridTiedConverter/CurrentControl/VoltageLimit.lean`.
* Parameters: any signs; the engineering range is `L, C > 0`, `V_dc > 0`.
* Excluded (as in the design): the line, the other axis, the synchronization and reactive-power
  loops, sampling and computation delay
  (`theorem/GridTiedConverter/GFM/DigitalCascade.lean`), PWM switching, anti-windup, DC-link
  dynamics (`V_dc` constant).

Source: work-sync `theory/T-gfm-control.md` §1.9 (the inner cascade), `theory/T-dc-voltage-gfm.md`
(the DC-link voltage as the modulation limit of a grid-forming converter),
`theory/T-field-oriented-control.md` §1.7 (`V_max = V_dc/√3`, saturation of the PI loops);
powerlib `theorem/GridTiedConverter/CurrentControl/VoltageLimit.lean`
(`CurrentControl.LimitedPI.circle_synthesizable_iff`), `theorem/Drives/Modulation.lean`
(`Drives.Modulation.svpwm_linearRange`,
`Drives.Modulation.maxCircle_radius_le`), `theorem/Dynamics/PiecewiseAffine.lean`
(`Dynamics.holds_congr_nhds`, `Dynamics.holds_iff_of_eventuallyEq_inputField`: a field decided
near the point by one affine piece), `theorem/Dynamics/Locality.lean`; the mirrored GFL platform
`theorem/GridTiedConverter/CurrentControl/VoltageLimit.lean`.

Results.
* Modulation (static): `abs_applied_le`, `applied_synthesizable` — every bridge voltage the
  platform applies, at every frame angle, is produced by the inverter; `circle_synthesizable_iff`
  — every vector of modulus `ρ ≥ 0` is produced iff `ρ ≤ V_max` (the statement of
  `CurrentControl.LimitedPI.circle_synthesizable_iff` at the same DC link).
* Saturation (static): `limitedField_eq_of_abs_le` (the platform field is the design field
  wherever the bridge command is in range), `command_point` (the steady bridge voltage is `v*`).
* Implementation evidence (private): with headroom `|v*| < V_max` the command at the operating
  point is in range, so near the point the platform field is the design's linear zero-input field
  (`field_eventuallyEq_linear`); with overload `V_max < |v*|` the saturation is constant near the
  point and the point is not an equilibrium (the proof of `mem_den_unstable_of_overload`); the
  bounded applied voltage bounds `(i, v)` on finite horizons whatever the integrators (the proof of
  `not_mem_den_globallyExponentiallyStable`).
* Anti-stable filter (static): `antiEnergy`, the energy
  `W = (L/2) i² + (1 + ρ² C/(2L)) (C/2) ṽ² − (ρ C/2) i ṽ` (`ρ = −R`, `ṽ = v − v*`), and
  `antiEnergy_rate`: `Ẇ = (ρ/2) i² + (ρ C/(2L)) ṽ² + (i − (ρ C/(2L)) ṽ) (sat(e) − v*)` along the
  platform (`L, C ≠ 0`).

Complement (T-gfm-control, the cascade without anti-windup): the modulation limit removes global
exponential stability for every gain and every headroom, while every local sentence of the design
is inherited exactly once the steady bridge voltage has headroom; global asymptotic stability
survives the limit on the Popov region (`theorem/GridTiedConverter/GFM/LimitedCascadeLure.lean`)
and fails for every negative filter resistance.

Family and connection conclusions.
* I: `family : Family LimitedCascade LimitRequirementGFM 4 0`. Requirements: the lifted design
  requirements `design q` (`InnerCascade.family.meets`) and the realistic constraints `physical`
  (`0 < L ∧ 0 < C`), `dcLink` (`0 < V_dc`), `headroom` (`|v*| < V_dc/√3`) and `overload`
  (`V_dc/√3 < |v*|`). The local sentences translate into `{design stable, headroom}`, instability
  into `{design unstable, headroom}`, passivity into nothing, the remaining flow sentences into the
  whole, inconsistent, language (`realize_univ`). `chain_le_semantics`: every translation is
  sound. `exactUnder_attractive`: within `headroom` the local asymptotic and local exponential
  translations are exact (`mem_den_attractive_iff`: with headroom, locally asymptotically
  (exponentially) stable iff the design is stable, `InnerCascade.Stable`); `mem_den_iff`: with
  `L, C > 0` and headroom a platform is locally asymptotically (exponentially) stable iff the
  explicit Routh conditions of `InnerCascade.mem_den_iff` hold. `mem_den_unstable_of_overload`:
  with `L ≠ 0`, `V_dc > 0` and overload the platform is unstable, whatever the design.
  `not_mem_den_globallyExponentiallyStable`: no platform is globally exponentially stable (from
  `(0, 0, 0, ζ₀)` the pair `(i, v − v*)` stays below a Grönwall bound `B` on `[0, T]` independent
  of `ζ₀`, the applied voltage being bounded, so the voltage integrator moves by at most `B T`,
  while an exponential estimate halves `‖x‖` by a time `T` fixed by its constants); hence
  `exact_globallyExponentiallyStable` (the whole-language translation is exact).
  `not_mem_den_globallyAsymptoticallyStable_of_R_neg`: with `L, C > 0` and a negative filter
  resistance `R < 0` no platform is globally asymptotically stable, whatever the design, the gains,
  the headroom and the DC link — the filter is open-loop anti-stable and the applied voltage
  bounded, so `antiEnergy` grows from every state where it is large
  (`Ẇ ≥ (ρ/4) i² + (ρ C/(4L)) ṽ² − B²/ρ − ρ C B²/(4L)`, `B = |V_max| + |v*|`) and the forward
  solution never converges. With `R ≥ 0` global asymptotic stability is proved on the Popov
  region in `theorem/GridTiedConverter/GFM/LimitedCascadeLure.lean`
  (`mem_den_globallyAsymptoticallyStable_of_popov`: `R > 0` and
  `(√K_pc − √(L n₀))² < R n₁`; `mem_den_globallyAsymptoticallyStable_of_lossless`: `R = 0`,
  `K_pc = L n₀`; `unloaded_mem_den_globallyAsymptoticallyStable`), where a Lur'e–Postnikov function
  with the saturation integral absorbs the windup of the two integrators. Outside that region it
  is not decided: a refutation needs an exact non-convergent solution of the saturated loop (a
  relay-type periodic orbit, or an unbounded solution of the LC resonance driven through the
  saturation when `R = 0`, `K_pc < L n₀`); none is given.
* M–I: `implementation : Implementation InnerCascade Spectral.Requirement LimitedCascade
  LimitRequirementGFM 4 1 4 0`, every platform realizing its design.
  `realizationExactUnder_local`: within `headroom` Lyapunov stability, local asymptotic and local
  exponential stability and instability are realized exactly, for every parameter sign (the limit
  is inactive near the operating point; unlike the GFL current loop no integral-action constraint
  is needed, the operating point is an equilibrium of every design).
  `realizationSoundUnder_unstable_of_overload`,
  `not_realizationSoundUnder_locallyExponentiallyStable`: within
  `{physical, dcLink, overload}` instability is realized soundly and local exponential stability
  is not (`overloaded`: the IMC design `L = R = C = ω_c = K_pv = 1`, `K_iv = 1/2`
  (`InnerCascade.imcTuned_mem_den_iff`) at `v* = 1`, `V_dc = 1`,
  `overloaded_mem_den_unstable`). `not_realizationSoundUnder_globallyExponentiallyStable`: global
  exponential stability is not realized soundly within all realistic constraints with headroom
  (`unloaded`: the same design at `v* = 0`, `V_dc = 1`);
  `realizationCompleteUnder_globallyExponentiallyStable` holds vacuously.
  `not_realizationSoundUnder_globallyAsymptoticallyStable`: global asymptotic stability is not
  realized soundly within all realistic constraints with headroom (`negResistance`: `L = C = 1`,
  `R = −1`, `K_pc = 3`, `K_ic = K_pv = 1`, `K_iv = 1/10`, a stable linear design, at `v* = 0`,
  `V_dc = 1`). Scaffold:
  `theorem/GridTiedConverter/GFM/LimitedCascade.agda`.
-/

noncomputable section
namespace powerlib.GFM
open Matrix Filter Linear LinearSystems TMIO Set
open scoped Topology

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- A grid-forming inner cascade driven through a two-level inverter: the design, the constant
voltage reference `v*` (the operating point) and the DC-link voltage `V_dc` that fixes the linear
modulation range. -/
structure LimitedCascade where
  /-- The design cascade (model layer). -/
  design : InnerCascade
  /-- The constant voltage reference `v*`. -/
  vref : ℝ
  /-- The DC-link voltage. -/
  Vdc : ℝ

namespace LimitedCascade

variable (y : LimitedCascade)

/-- The modulation limit `V_max = V_dc/√3`. -/
def Vmax : ℝ := y.Vdc / Real.sqrt 3

/-- The bridge command: the current-loop output plus the capacitor-voltage feed-forward. -/
def command (x : ℝ⁴) : ℝ := y.design.control y.vref x + x 2

/-- The bridge voltage the inverter applies: the command saturated to the linear range. -/
def applied (x : ℝ⁴) : ℝ := SpecialFunctions.clampSym y.Vmax (y.command x)

/-- The platform field: `L i̇ = −R i + sat(e) − v`, `ξ̇ = i* − i`, `C v̇ = i`, `ζ̇ = v* − v`. -/
def limitedField (x : ℝ⁴) : ℝ⁴ :=
  WithLp.toLp 2 ![(-y.design.R * x 0 + y.applied x - x 2) / y.design.L,
    y.design.currentRef y.vref x - x 0, x 0 / y.design.C, y.vref - x 2]

/-- The operating point `(0, 0, v*, 0)`, the design equilibrium. -/
def point : ℝ⁴ := InnerCascade.equilibrium y.vref

/-- The platform field translated so that the operating point is the origin. -/
def field (z : ℝ⁴) : ℝ⁴ := y.limitedField (z + y.point)

/-- The steady bridge voltage at the operating point is `v*`. Static evidence on the
implementation. -/
@[tmio M, powerlib_domain] theorem command_point : y.command y.point = y.vref := by
  simp [command, point, InnerCascade.equilibrium, InnerCascade.control, InnerCascade.currentRef]

/-- Wherever the bridge command is in range the platform field is the design field. Static
evidence on the implementation. -/
@[tmio M, powerlib_domain] theorem limitedField_eq_of_abs_le {x : ℝ⁴}
    (h : |y.command x| ≤ y.Vmax) : y.limitedField x = y.design.field y.vref x := by
  unfold limitedField applied
  rw [SpecialFunctions.clampSym_of_abs_le h]
  unfold command InnerCascade.field
  congr 3
  ring

@[tmio M, powerlib_domain] private theorem continuous_command_shift :
    Continuous fun z : ℝ⁴ => y.command (z + y.point) := by
  unfold command InnerCascade.control InnerCascade.currentRef
  fun_prop

/-! ### The modulation range (static evidence) -/

/-- With `V_dc ≥ 0` the applied bridge voltage lies in the linear range. -/
@[tmio M, powerlib_domain] theorem abs_applied_le (hV : 0 ≤ y.Vdc) (x : ℝ⁴) :
    |y.applied x| ≤ y.Vmax := by
  have h := SpecialFunctions.abs_clampSym_le y.Vmax (y.command x)
  have hm : 0 ≤ y.Vmax := div_nonneg hV (Real.sqrt_nonneg 3)
  rwa [abs_of_nonneg hm] at h

/-- Every bridge voltage the platform applies, as the space vector `sat(e) e^{jθ}` at any frame
angle `θ`, is produced by leg voltages in `[0, V_dc]` (`Drives.Modulation.svpwm_linearRange`). -/
@[tmio M, powerlib_domain] theorem applied_synthesizable (hV : 0 ≤ y.Vdc) (x : ℝ⁴) (θ : ℝ) :
    ∃ xa xb xc : ℝ, xa ∈ Icc 0 y.Vdc ∧ xb ∈ Icc 0 y.Vdc ∧ xc ∈ Icc 0 y.Vdc ∧
      Transform.SpaceVector.clarke xa xb xc =
        (y.applied x : ℂ) * Complex.exp (θ * Complex.I) := by
  apply Drives.Modulation.svpwm_linearRange
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact y.abs_applied_le hV x

/-- `V_max` is the largest synthesizable circle: every vector of modulus `ρ ≥ 0` is produced by leg
voltages in `[0, V_dc]` iff `ρ ≤ V_max`. The limit depends on the DC link alone: this is the
statement of the GFL current loop, `CurrentControl.LimitedPI.circle_synthesizable_iff`, read at
the same DC-link voltage. -/
@[tmio M, powerlib_domain] theorem circle_synthesizable_iff {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ u : ℂ, ‖u‖ = ρ → ∃ xa xb xc : ℝ, xa ∈ Icc 0 y.Vdc ∧ xb ∈ Icc 0 y.Vdc ∧
      xc ∈ Icc 0 y.Vdc ∧ Transform.SpaceVector.clarke xa xb xc = u) ↔ ρ ≤ y.Vmax :=
  CurrentControl.LimitedPI.circle_synthesizable_iff ⟨CurrentControl.LimitedPI.nominal, 0, y.Vdc⟩
    hρ

/-! ### Implementation evidence (private) -/

/-- With headroom, near the operating point the limit is inactive. -/
@[tmio M, powerlib_domain] private theorem field_eventuallyEq_design (hh : |y.vref| < y.Vmax) :
    y.field =ᶠ[𝓝 0] fun z => y.design.field y.vref (z + y.point) := by
  have hc := (continuous_abs.comp y.continuous_command_shift).tendsto 0
  have h0 : |y.command (0 + y.point)| < y.Vmax := by
    rw [zero_add, command_point]
    exact hh
  filter_upwards [hc.eventually (eventually_lt_nhds h0)] with z hz
  exact y.limitedField_eq_of_abs_le hz.le

/-- The design field about the operating point is the linear zero-input field of the design
plant (the operating point is an equilibrium of every design). -/
@[tmio M, powerlib_domain] private theorem designField_shift :
    (fun z => y.design.field y.vref (z + y.point)) =
      affineLinearVectorField y.design.model.A 0 := by
  have h := LTI.inputField_shift y.design.model (y.design.isEquilibrium y.vref)
  funext z
  rw [← congrFun h z]
  exact (y.design.model_field _ _).symm

/-- With headroom, near the operating point the platform field is the design's linear zero-input
field. -/
@[tmio M, powerlib_domain] private theorem field_eventuallyEq_linear (hh : |y.vref| < y.Vmax) :
    y.field =ᶠ[𝓝 0] affineLinearVectorField y.design.model.A 0 := by
  rw [← y.designField_shift]
  exact y.field_eventuallyEq_design hh

/-- With overload, near the operating point the saturation is constant. -/
@[tmio M, powerlib_domain] private theorem field_eventuallyEq_overload (ho : y.Vmax < |y.vref|) :
    y.field =ᶠ[𝓝 0] fun z => WithLp.toLp 2
      ![(-y.design.R * (z + y.point) 0 + SpecialFunctions.clampSym y.Vmax y.vref -
          (z + y.point) 2) / y.design.L,
        y.design.currentRef y.vref (z + y.point) - (z + y.point) 0, (z + y.point) 0 / y.design.C,
        y.vref - (z + y.point) 2] := by
  have hc := y.continuous_command_shift.tendsto 0
  rw [zero_add, command_point] at hc
  filter_upwards [hc.eventually (SpecialFunctions.clampSym_eventually_eq ho)] with z hz
  simp only [field, limitedField, applied, hz]

end LimitedCascade

/-! ## The implementation family -/

/-- Requirements on a voltage-limited cascade: the lifted design requirements and the realistic
constraints. -/
inductive LimitRequirementGFM
  /-- The design cascade meets `q` (`InnerCascade.family`). -/
  | design (q : Spectral.Requirement)
  /-- Positive filter inductance and capacitance. -/
  | physical
  /-- A positive DC-link voltage `0 < V_dc`. -/
  | dcLink
  /-- Headroom: the steady bridge voltage lies strictly inside the linear range,
  `|v*| < V_dc/√3`. -/
  | headroom
  /-- Overload: the steady bridge voltage lies beyond the linear range, `V_dc/√3 < |v*|`. -/
  | overload

namespace LimitedCascade

/-- Satisfaction of a platform requirement. -/
def Meets (y : LimitedCascade) : LimitRequirementGFM → Prop
  | .design q => InnerCascade.family.meets y.design q
  | .physical => 0 < y.design.L ∧ 0 < y.design.C
  | .dcLink => 0 < y.Vdc
  | .headroom => |y.vref| < y.Vmax
  | .overload => y.Vmax < |y.vref|

/-- The translation of the sentences into platform requirements: the local ones into a stable
design with headroom, instability into an unstable design with headroom, passivity into nothing,
the remaining sentences into the whole, inconsistent, language. -/
def translate : Sentence → Set LimitRequirementGFM
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.design .stable, .headroom}
  | .flow .unstable => {.design .unstable, .headroom}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The voltage-limited cascades, each read as its field about the operating point. -/
def family : Family LimitedCascade LimitRequirementGFM 4 0 :=
  ⟨fun y => Port.System.autonomous y.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous field :=
  fun _ => rfl

/-- Within headroom the local sentences of the platform are those of its design: near the
operating point the platform is the design's linear loop. -/
@[tmio TM, powerlib_domain] private theorem mem_den_iff_design {y : LimitedCascade}
    (hh : |y.vref| < y.Vmax) {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable ∨ P = .unstable) :
    connection% (y ∈ family.den (.flow P) ↔ y.design ∈ InnerCascade.family.den (.flow P)) := by
  unfold TMIO.Statement
  rw [(connection_proof% InnerCascade.family_isLinear.mem_den_flow),
    (connection_proof% family_isAutonomous.mem_den_flow)]
  exact Dynamics.holds_congr_nhds (y.field_eventuallyEq_linear hh) hP

/-- The whole platform requirement language is inconsistent: headroom and overload exclude each
other. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize family.meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.realize_univ_eq_empty_of .headroom .overload
    fun y (h1 : |y.vref| < y.Vmax) (h2 : y.Vmax < |y.vref|) => by linarith

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
    have hd := InnerCascade.chain_le_semantics
    unfold powerlib.TMIO.Statement at hd
    have hs : y.design ∈ InnerCascade.family.den (.flow .locallyExponentiallyStable) :=
      Family.chain_le_semantics_iff.mp hd (.flow .locallyExponentiallyStable)
        ((TMIO.mem_realize _ _ _).mpr fun q hq => by
          have : q = .stable := by simpa [InnerCascade.family, Spectral.linearFamily,
            Spectral.linearTranslate, Spectral.table] using hq
          subst this
          exact hy (.design .stable) (by simp))
    exact (connection_proof% mem_den_iff_design (hy .headroom (by simp))
      (P := .locallyExponentiallyStable) (by simp)).mpr hs
  · rw [(connection_proof% TMIO.mem_realize)] at hy
    have hd := InnerCascade.chain_le_semantics
    unfold powerlib.TMIO.Statement at hd
    have hs : y.design ∈ InnerCascade.family.den (.flow .unstable) :=
      Family.chain_le_semantics_iff.mp hd (.flow .unstable)
        ((TMIO.mem_realize _ _ _).mpr fun q hq => by
          have : q = .unstable := by simpa [InnerCascade.family, Spectral.linearFamily,
            Spectral.linearTranslate, Spectral.table] using hq
          subst this
          exact hy (.design .unstable) (by simp))
    exact (connection_proof% mem_den_iff_design (hy .headroom (by simp))
      (P := .unstable) (by simp)).mpr hs

/-- **With headroom, exactly**: a platform is locally asymptotically (exponentially) stable iff its
design is stable (the quartic Routh conditions `InnerCascade.Stable`). -/
@[tmio TM, powerlib_domain] theorem mem_den_attractive_iff {y : LimitedCascade}
    (hh : |y.vref| < y.Vmax) {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    connection% (y ∈ family.den (.flow P) ↔ y ∈ {y : LimitedCascade | y.design.Stable}) := by
  have hPa : P.Attractive := by rcases hP with rfl | rfl <;> trivial
  have h1 := mem_den_iff_design hh (P := P) (by rcases hP with rfl | rfl <;> simp)
  have h2 := InnerCascade.mem_den_iff_stable y.design (Or.inl hPa)
  unfold TMIO.Statement at h1 h2 ⊢
  exact h1.trans h2

/-- Within headroom the local asymptotic and local exponential translations are exact. -/
@[tmio TM, powerlib_domain] theorem exactUnder_attractive {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    connection% (family.ExactUnder {.headroom} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have ht : family.translate (.flow P) = {.design .stable, .headroom} := by
    rcases hP with rfl | rfl <;> rfl
  refine Spectral.exactUnder_iff_forall.mpr fun y hΔ => ?_
  have hh : |y.vref| < y.Vmax := (TMIO.mem_realize _ _ _).mp hΔ .headroom rfl
  rw [ht, (connection_proof% mem_den_attractive_iff hh hP), (connection_proof% TMIO.mem_realize)]
  refine ⟨fun h => h (.design .stable) (by simp), fun hs => ?_⟩
  rintro q (rfl | rfl)
  · exact hs
  · exact hh

/-- With `L, C > 0` and headroom a platform is locally asymptotically (exponentially) stable iff
the explicit Routh conditions of its design hold (`InnerCascade.mem_den_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_iff (y : LimitedCascade) (hL : 0 < y.design.L)
    (hC : 0 < y.design.C) (hh : |y.vref| < y.Vmax) {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    connection% (y ∈ family.den (.flow P) ↔ y.design ∈ {c : InnerCascade | 0 < c.R + c.Kpc ∧
      0 < c.Kic * c.Kpv + c.Kiv * c.Kpc ∧ 0 < c.Kic * c.Kiv ∧
      c.C * c.L * (c.Kic * c.Kpv + c.Kiv * c.Kpc) ^ 2 +
          c.C ^ 2 * (c.R + c.Kpc) ^ 2 * (c.Kic * c.Kiv) <
        c.C * (c.R + c.Kpc) * (c.C * c.Kic + c.Kpc * c.Kpv) *
          (c.Kic * c.Kpv + c.Kiv * c.Kpc)}) := by
  have hPa : P.Attractive := by rcases hP with rfl | rfl <;> trivial
  have h1 := mem_den_iff_design hh (P := P) (by rcases hP with rfl | rfl <;> simp)
  have h2 := InnerCascade.mem_den_iff y.design hL hC (Or.inl hPa)
  unfold TMIO.Statement at h1 h2 ⊢
  exact h1.trans h2

/-- **Overload makes the platform unstable, whatever the design**: with `L ≠ 0`, `V_dc > 0` and
`V_max < |v*|` the saturation is constant near the operating point, which is not an equilibrium
(`sat(v*) ≠ v*`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_overload (y : LimitedCascade)
    (hL : y.design.L ≠ 0) (hV : 0 < y.Vdc) (ho : y.Vmax < |y.vref|) :
    connection% (y ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable y.field 0
  refine (Dynamics.unstable_congr_nhds (y.field_eventuallyEq_overload ho)).mpr
    (Dynamics.unstable_of_ne_zero ?_ ?_)
  · rw [contDiff_euclidean]
    intro i
    fin_cases i <;> simp [InnerCascade.currentRef] <;> fun_prop
  · intro h
    have h0 := congrArg (fun z : ℝ⁴ => z 0) h
    simp [point, InnerCascade.equilibrium, hL] at h0
    have hVm : 0 ≤ y.Vmax := div_nonneg hV.le (Real.sqrt_nonneg 3)
    exact SpecialFunctions.clampSym_ne_of_lt_abs hVm ho (by linarith)

/-- **No platform is globally exponentially stable.** From `(0, 0, 0, ζ₀)` (about the operating
point) the pair `(i, v − v*)` obeys `‖(i̇, v̇)‖ ≤ K ‖(i, v − v*)‖ + ε` with
`K = (|R| + 1)/|L| + 1/|C|`, `ε = (|V_max| + |v*|)/|L|` (the applied voltage is bounded) and stays
below a bound `B` on `[0, T]` (Grönwall), whatever `ζ₀`, so the voltage integrator moves by at most
`B T`; an exponential estimate with constants `C, a` halves the distance by `T = log (2C)/a`,
which fails for `ζ₀ = 2 B T + 1`. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyExponentiallyStable
    (y : LimitedCascade) :
    connection% (y ∉ family.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change ¬ Flow.GloballyExponentiallyStable y.field 0
  intro hges
  obtain ⟨C, a, hC, ha, hest⟩ := hges.exists_constant
  have hfc := hges.2.1
  have hT : 0 ≤ Real.log (2 * C) / a := div_nonneg (Real.log_nonneg (by linarith)) ha.le
  set T := Real.log (2 * C) / a with hTdef
  have hCT : C * Real.exp (-a * T) = 1 / 2 := by
    have : -a * T = -Real.log (2 * C) := by
      rw [hTdef]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by linarith)]
    field_simp
  set K := (|y.design.R| + 1) / |y.design.L| + 1 / |y.design.C| with hK
  set ε := (|y.Vmax| + |y.vref|) / |y.design.L| with hε
  have hK0 : 0 ≤ K := by positivity
  have hgc : Continuous (gronwallBound 0 K ε) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gronwallBound 0 K ε x).continuousAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 T) hgc.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT⟩)
  obtain ⟨φ, hφ0, hφ⟩ := hfc 0 (WithLp.toLp 2 ![0, 0, 0, 2 * B * T + 1])
  have hd : ∀ t ∈ Ici (0 : ℝ), ∀ i : Fin 4,
      HasDerivWithinAt (fun s => φ s i) (y.field (φ t) i) (Ici 0) t :=
    fun t ht i => (PiLp.proj 2 (fun _ : Fin 4 => ℝ) i).hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)
  have hf0 : ∀ z : ℝ⁴, y.field z 0 =
      (-y.design.R * z 0 + y.applied (z + y.point) - (z 2 + y.vref)) / y.design.L := by
    intro z
    simp [field, limitedField, point, InnerCascade.equilibrium]
  have hf2 : ∀ z : ℝ⁴, y.field z 2 = z 0 / y.design.C := by
    intro z
    simp [field, limitedField, point, InnerCascade.equilibrium]
  have hf3 : ∀ z : ℝ⁴, y.field z 3 = -z 2 := by
    intro z
    simp [field, limitedField, point, InnerCascade.equilibrium]
  -- the pair `(i, v − v*)` and its derivative
  have hbound : ∀ z : ℝ⁴, ‖((y.field z 0, y.field z 2) : ℝ × ℝ)‖ ≤
      K * ‖((z 0, z 2) : ℝ × ℝ)‖ + ε := by
    intro z
    set m := ‖((z 0, z 2) : ℝ × ℝ)‖ with hm
    have h0 : |z 0| ≤ m := norm_fst_le ((z 0, z 2) : ℝ × ℝ)
    have h2 : |z 2| ≤ m := norm_snd_le ((z 0, z 2) : ℝ × ℝ)
    have hm0 : 0 ≤ m := norm_nonneg _
    have hs : |y.applied (z + y.point)| ≤ |y.Vmax| := by
      have := SpecialFunctions.abs_clampSym_le y.Vmax (y.command (z + y.point))
      exact this
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · rw [hf0, Real.norm_eq_abs, abs_div]
      have hn : |-y.design.R * z 0 + y.applied (z + y.point) - (z 2 + y.vref)| ≤
          (|y.design.R| + 1) * m + (|y.Vmax| + |y.vref|) := by
        have e1 := abs_add_le (-y.design.R * z 0 + y.applied (z + y.point)) (-(z 2 + y.vref))
        have e2 := abs_add_le (-y.design.R * z 0) (y.applied (z + y.point))
        have e3 := abs_add_le (z 2) y.vref
        rw [abs_neg] at e1
        rw [abs_mul, abs_neg] at e2
        have := mul_le_mul_of_nonneg_left h0 (abs_nonneg y.design.R)
        rw [sub_eq_add_neg]
        nlinarith
      rcases eq_or_ne y.design.L 0 with hL | hL
      · simp only [hL, abs_zero, div_zero]
        positivity
      have hLp : 0 < |y.design.L| := abs_pos.mpr hL
      calc |-y.design.R * z 0 + y.applied (z + y.point) - (z 2 + y.vref)| / |y.design.L|
          ≤ ((|y.design.R| + 1) * m + (|y.Vmax| + |y.vref|)) / |y.design.L| :=
            div_le_div_of_nonneg_right hn hLp.le
        _ = (|y.design.R| + 1) / |y.design.L| * m + ε := by rw [hε]; ring
        _ ≤ K * m + ε := by
            have : 0 ≤ 1 / |y.design.C| * m := by positivity
            rw [hK]; nlinarith
    · rw [hf2, Real.norm_eq_abs, abs_div]
      calc |z 0| / |y.design.C| ≤ m / |y.design.C| :=
            div_le_div_of_nonneg_right h0 (abs_nonneg _)
        _ = 1 / |y.design.C| * m := by ring
        _ ≤ K * m + ε := by
            have : 0 ≤ (|y.design.R| + 1) / |y.design.L| * m := by positivity
            have : 0 ≤ ε := by positivity
            rw [hK]; nlinarith
  have hcont : ∀ i : Fin 4, ContinuousOn (fun s => φ s i) (Icc 0 T) := fun i t ht =>
    (hd t ht.1 i).continuousWithinAt.mono Icc_subset_Ici_self
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s => ((φ s 0, φ s 2) : ℝ × ℝ))
    (f' := fun s => ((y.field (φ s) 0, y.field (φ s) 2) : ℝ × ℝ)) (δ := 0) (K := K) (ε := ε)
    (a := 0) (b := T) ((hcont 0).prodMk (hcont 2))
    (fun t ht => ((hd t ht.1 0).prodMk (hd t ht.1 2)).mono (Ici_subset_Ici.mpr ht.1))
    (by simp [hφ0]) (fun t _ => hbound (φ t))
  have hb3 : ∀ t ∈ Ico (0 : ℝ) T, ‖y.field (φ t) 3‖ ≤ B := by
    intro t ht
    rw [hf3, norm_neg]
    have h1 := hg t (Ico_subset_Icc_self ht)
    rw [sub_zero] at h1
    have h2 : ‖φ t 2‖ ≤ ‖((φ t 0, φ t 2) : ℝ × ℝ)‖ := norm_snd_le ((φ t 0, φ t 2) : ℝ × ℝ)
    exact h2.trans (h1.trans ((le_abs_self _).trans (hB t (Ico_subset_Icc_self ht))))
  have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun s => φ s 3)
    (f' := fun s => y.field (φ s) 3) (C := B) (hcont 3)
    (fun t ht => (hd t ht.1 3).mono (Ici_subset_Ici.mpr ht.1)) hb3 T ⟨hT, le_rfl⟩
  have he := hest 0 T φ (hφ.mono Icc_subset_Ici_self) T ⟨hT, le_rfl⟩
  simp only [sub_zero] at he
  rw [hCT, hφ0] at he
  have hn : ‖(WithLp.toLp 2 ![0, 0, 0, 2 * B * T + 1] : ℝ⁴)‖ = 2 * B * T + 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_four]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  rw [hn] at he
  have h1 : ‖φ T 3‖ ≤ ‖φ T‖ := PiLp.norm_apply_le _ _
  simp only [hφ0, sub_zero] at hmv
  have hξ : (![0, 0, 0, 2 * B * T + 1] : Fin 4 → ℝ) 3 = 2 * B * T + 1 := by simp
  rw [hξ, Real.norm_eq_abs] at hmv
  rw [Real.norm_eq_abs] at h1
  have := abs_sub_abs_le_abs_sub (2 * B * T + 1) (φ T 3)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * B * T + 1), abs_sub_comm] at this
  linarith

/-- Global exponential stability is translated exactly into the whole, inconsistent, language:
no platform satisfies it. -/
@[tmio TM, powerlib_domain] theorem exact_globallyExponentiallyStable :
    connection% (family.Exact (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_univ realize_univ rfl
    (Set.eq_empty_iff_forall_notMem.mpr not_mem_den_globallyExponentiallyStable)

/-! ## Global asymptotic stability with an anti-stable filter -/

/-- **The anti-Lyapunov energy of the filter** (in the coordinates about the operating point,
`ρ = −R`, `ṽ = v − v*`): `W = (L/2) i² + (1 + ρ² C/(2L)) (C/2) ṽ² − (ρ C/2) i ṽ`. -/
def antiEnergy (y : LimitedCascade) (z : ℝ⁴) : ℝ :=
  y.design.L / 2 * z 0 ^ 2 +
    (1 + (-y.design.R) ^ 2 * y.design.C / (2 * y.design.L)) * y.design.C / 2 * z 2 ^ 2 -
      -y.design.R * y.design.C / 2 * (z 0 * z 2)

@[tmio M, powerlib_domain] private theorem hasFDerivAt_antiEnergy (y : LimitedCascade)
    (z : ℝ⁴) : ∃ W' : ℝ⁴ →L[ℝ] ℝ, HasFDerivAt y.antiEnergy W' z ∧ ∀ v : ℝ⁴,
      W' v = y.design.L * z 0 * v 0 +
        (1 + (-y.design.R) ^ 2 * y.design.C / (2 * y.design.L)) * y.design.C * z 2 * v 2 -
          -y.design.R * y.design.C / 2 * (z 0 * v 2 + z 2 * v 0) := by
  have h0 : HasFDerivAt (fun w : ℝ⁴ => w 0) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4)) z :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) : ℝ⁴ →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun w : ℝ⁴ => w 2) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4)) z :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) : ℝ⁴ →L[ℝ] ℝ).hasFDerivAt
  have hW := (((h0.pow 2).const_mul (y.design.L / 2)).add
    ((h2.pow 2).const_mul ((1 + (-y.design.R) ^ 2 * y.design.C / (2 * y.design.L)) *
      y.design.C / 2))).sub ((h0.mul h2).const_mul (-y.design.R * y.design.C / 2))
  refine ⟨_, hW, fun v => ?_⟩
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, PiLp.proj_apply, smul_eq_mul]
  simp
  ring

/-- **The rate of the anti-Lyapunov energy** along the platform: with `u = sat(e) − v*` the
applied voltage about its steady value,
`Ẇ = (ρ/2) i² + (ρ C/(2L)) ṽ² + (i − (ρ C/(2L)) ṽ) u` (`ρ = −R`; `L, C ≠ 0`). Static evidence on
the implementation. -/
@[tmio M, powerlib_domain] theorem antiEnergy_rate (y : LimitedCascade) (hL : y.design.L ≠ 0)
    (hC : y.design.C ≠ 0) (z : ℝ⁴) :
    fderiv ℝ y.antiEnergy z (y.field z) =
      -y.design.R / 2 * z 0 ^ 2 + -y.design.R * y.design.C / (2 * y.design.L) * z 2 ^ 2 +
        (z 0 - -y.design.R * y.design.C / (2 * y.design.L) * z 2) *
          (y.applied (z + y.point) - y.vref) := by
  obtain ⟨W', hW, hW'⟩ := y.hasFDerivAt_antiEnergy z
  rw [hW.fderiv, hW']
  have hf0 : y.field z 0 =
      (-y.design.R * z 0 + y.applied (z + y.point) - (z 2 + y.vref)) / y.design.L := by
    simp [field, limitedField, point, InnerCascade.equilibrium]
  have hf2 : y.field z 2 = z 0 / y.design.C := by
    simp [field, limitedField, point, InnerCascade.equilibrium]
  rw [hf0, hf2]
  field_simp
  ring

/-- **An anti-stable filter is never globally asymptotically stable.** With `L, C > 0` and a
negative resistance `R < 0` the filter `(i, v)` is open-loop anti-stable, and the applied voltage
is bounded by `V_max`: the anti-Lyapunov energy `antiEnergy` grows at the rate
`Ẇ ≥ (ρ/4) i² + (ρ C/(4L)) ṽ² − B²/ρ − ρ C B²/(4L)` (`ρ = −R`, `B = |V_max| + |v*|`), so from a
state of large `W` it never decreases, and the forward solution (which exists by global asymptotic
stability itself) cannot converge to the operating point — whatever the design, the gains, the
headroom and the DC link. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyAsymptoticallyStable_of_R_neg
    (y : LimitedCascade) (hL : 0 < y.design.L) (hC : 0 < y.design.C) (hR : y.design.R < 0) :
    connection% (y ∉ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change ¬ Flow.GloballyAsymptoticallyStable y.field 0
  rintro ⟨-, hfc, -, hconv⟩
  have hρ : 0 < -y.design.R := by linarith
  set B := |y.Vmax| + |y.vref| with hBdef
  have hB0 : 0 ≤ B := by positivity
  set c₁ := -y.design.R / 2 with hc₁def
  set c₂ := -y.design.R * y.design.C / (2 * y.design.L) with hc₂def
  have hc₁ : 0 < c₁ := by positivity
  have hc₂ : 0 < c₂ := by positivity
  set m := min c₁ c₂ with hmdef
  have hm : 0 < m := lt_min hc₁ hc₂
  set T := (B ^ 2 / c₁ + c₂ * B ^ 2) / m with hTdef
  have hT : 0 ≤ T := by positivity
  set a := (1 + (-y.design.R) ^ 2 * y.design.C / (2 * y.design.L)) * y.design.C / 2 with hadef
  have ha : 0 < a := by positivity
  set Λ := y.design.L / 2 + a + -y.design.R * y.design.C / 4 with hΛdef
  have hΛ : 0 < Λ := by positivity
  have hm0 : m ≠ 0 := hm.ne'
  have hc₁0 : c₁ ≠ 0 := hc₁.ne'
  clear_value B c₁ c₂ m T a Λ
  -- the energy is at most `Λ (i² + ṽ²)`
  have hWub : ∀ z : ℝ⁴, y.antiEnergy z ≤ Λ * (z 0 ^ 2 + z 2 ^ 2) := fun z => by
    have hz : -(z 0 * z 2) ≤ (z 0 ^ 2 + z 2 ^ 2) / 2 := by nlinarith [sq_nonneg (z 0 + z 2)]
    have hk : 0 < -y.design.R * y.design.C / 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hz hk.le
    have h2 : 0 ≤ y.design.L / 2 * z 2 ^ 2 := by positivity
    have h3 : 0 ≤ a * z 0 ^ 2 := by positivity
    simp only [antiEnergy, ← hadef]
    rw [hΛdef]
    nlinarith
  -- the rate is nonnegative once `i² + ṽ² ≥ T`
  have hrate : ∀ z : ℝ⁴, T ≤ z 0 ^ 2 + z 2 ^ 2 → 0 ≤ fderiv ℝ y.antiEnergy z (y.field z) :=
    fun z hz => by
      rw [y.antiEnergy_rate hL.ne' hC.ne', ← hc₁def, ← hc₂def]
      set u := y.applied (z + y.point) - y.vref with hu
      have hub : |u| ≤ B := by
        have h1 : |y.applied (z + y.point)| ≤ |y.Vmax| :=
          SpecialFunctions.abs_clampSym_le y.Vmax (y.command (z + y.point))
        calc |u| ≤ |y.applied (z + y.point)| + |y.vref| := abs_sub _ _
          _ ≤ B := by rw [hBdef]; exact add_le_add h1 le_rfl
      have e1 : -(c₁ / 2 * z 0 ^ 2 + B ^ 2 / (2 * c₁)) ≤ z 0 * u := by
        have h1 : -(|z 0| * B) ≤ z 0 * u := by
          have h := neg_abs_le (z 0 * u)
          rw [abs_mul] at h
          have h' := mul_le_mul_of_nonneg_left hub (abs_nonneg (z 0))
          linarith
        have key : 2 * c₁ * (|z 0| * B) ≤ c₁ ^ 2 * z 0 ^ 2 + B ^ 2 := by
          nlinarith [sq_nonneg (c₁ * |z 0| - B), sq_abs (z 0)]
        have eq : c₁ / 2 * z 0 ^ 2 + B ^ 2 / (2 * c₁) =
            (c₁ ^ 2 * z 0 ^ 2 + B ^ 2) / (2 * c₁) := by field_simp
        have h2 : |z 0| * B ≤ c₁ / 2 * z 0 ^ 2 + B ^ 2 / (2 * c₁) := by
          rw [eq, le_div_iff₀ (by positivity)]; linarith
        linarith
      have e2 : c₂ * z 2 * u ≤ c₂ * (z 2 ^ 2 / 2 + B ^ 2 / 2) := by
        have h1 : z 2 * u ≤ |z 2| * B := by
          have h := le_abs_self (z 2 * u)
          rw [abs_mul] at h
          have h' := mul_le_mul_of_nonneg_left hub (abs_nonneg (z 2))
          linarith
        have h2 : |z 2| * B ≤ z 2 ^ 2 / 2 + B ^ 2 / 2 := by
          nlinarith [sq_nonneg (|z 2| - B), sq_abs (z 2)]
        have := mul_le_mul_of_nonneg_left (h1.trans h2) hc₂.le
        linarith
      have e3 : m / 2 * (z 0 ^ 2 + z 2 ^ 2) ≤ c₁ / 2 * z 0 ^ 2 + c₂ / 2 * z 2 ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) (sq_nonneg (z 0))
        have h2 := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) (sq_nonneg (z 2))
        rw [← hmdef] at h1 h2
        nlinarith
      have e4 : m / 2 * T = B ^ 2 / (2 * c₁) + c₂ * B ^ 2 / 2 := by
        rw [hTdef]; field_simp
      have e5 : m / 2 * T ≤ m / 2 * (z 0 ^ 2 + z 2 ^ 2) :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      have e6 : (z 0 - c₂ * z 2) * u = z 0 * u - c₂ * z 2 * u := by ring
      rw [e6]
      linarith
  -- a state of large energy
  obtain ⟨X, hXdef⟩ : ∃ X, X = 2 * Λ * T / y.design.L := ⟨_, rfl⟩
  have hX : 0 ≤ X := by rw [hXdef]; positivity
  have hLX : y.design.L / 2 * X = Λ * T := by rw [hXdef]; field_simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ⁴, x₀ = WithLp.toLp 2 ![X + 1, 0, 0, 0] := ⟨_, rfl⟩
  have hWx₀ : y.antiEnergy x₀ = y.design.L / 2 * (X + 1) ^ 2 := by
    simp [antiEnergy, hx₀]
  have hbig : Λ * T < y.antiEnergy x₀ := by
    rw [hWx₀, ← hLX]
    have hs2 : X < (X + 1) ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_left hs2 (by positivity)
  -- the energy never decreases below its initial value
  have hWd : Differentiable ℝ y.antiEnergy := fun z =>
    (y.hasFDerivAt_antiEnergy z).choose_spec.1.differentiableAt
  have hWc : Continuous y.antiEnergy := hWd.continuous
  set U := {z : ℝ⁴ | Λ * T < y.antiEnergy z} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const hWc
  have hLie : ∀ z ∈ U, fderiv ℝ (fun w => -y.antiEnergy w) z (y.field z) ≤ 0 := fun z hz => by
    rw [fderiv_fun_neg, _root_.neg_apply, neg_nonpos]
    refine hrate z ?_
    have h1 := hWub z
    have h2 : Λ * T < Λ * (z 0 ^ 2 + z 2 ^ 2) := lt_of_lt_of_le hz h1
    exact (lt_of_mul_lt_mul_left h2 hΛ.le).le
  have hSeq : {z ∈ U | (fun w => -y.antiEnergy w) z ≤ -y.antiEnergy x₀} =
      {z | y.antiEnergy x₀ ≤ y.antiEnergy z} := by
    ext z
    simp only [hU, Set.mem_ofPred_eq, neg_le_neg_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨lt_of_lt_of_le hbig h, h⟩
  have hinv := Dynamics.LaSalle.isPositivelyInvariant_sublevel_of_isOpen
    (V := fun w => -y.antiEnergy w) (c := -y.antiEnergy x₀) hUo hWd.neg hLie
    (by rw [hSeq]; exact isClosed_le continuous_const hWc)
  obtain ⟨φ, hφ0, hφ⟩ := hfc 0 x₀
  have hstay : ∀ t, 0 ≤ t → y.antiEnergy x₀ ≤ y.antiEnergy (φ t) := fun t ht => by
    have h := hinv 0 t φ (hφ.mono Set.Icc_subset_Ici_self) (by
      rw [hφ0]; exact ⟨hbig, le_rfl⟩) t ⟨ht, le_rfl⟩
    exact neg_le_neg_iff.mp h.2
  have hlim : Tendsto (fun t => y.antiEnergy (φ t)) atTop (𝓝 (y.antiEnergy 0)) :=
    (hWc.tendsto 0).comp (hconv 0 φ hφ)
  have hW0 : y.antiEnergy 0 = 0 := by simp [antiEnergy]
  rw [hW0] at hlim
  have hle : y.antiEnergy x₀ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, fun t ht => hstay t ht⟩)
  have : 0 ≤ Λ * T := by positivity
  linarith

/-! ## The implementation over the cascade design (M–I) -/

/-- The voltage-limited cascades as an implementation of the cascade design
`InnerCascade.family`: each platform realizes its design. -/
def implementation :
    Implementation InnerCascade Spectral.Requirement LimitedCascade LimitRequirementGFM 4 1 4 0 :=
  { model := InnerCascade.family, impl := family, realizes := Implementation.ofDesign design }

/-- Within headroom, Lyapunov stability, local asymptotic and local exponential stability and
instability are realized exactly, for every parameter sign: near the operating point the limit is
inactive and the platform is the design's linear loop. -/
@[tmio MI, powerlib_domain] theorem realizationExactUnder_local {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable ∨ P = .unstable) :
    connection% (implementation.RealizationExactUnder {.headroom} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  refine Implementation.realizationExactUnder_of_design (I := implementation) rfl ?_
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  refine and_congr_left fun hΔ => ?_
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hh : |y.vref| < y.Vmax := hΔ .headroom (by simp)
  exact (connection_proof% mem_den_iff_design hh hP)

/-- An overloaded platform: the IMC design `L = R = C = ω_c = K_pv = 1`, `K_iv = 1/2` at `v* = 1`
with `V_dc = 1`, so `v* = 1` exceeds `V_max = 1/√3`. -/
def overloaded : LimitedCascade := ⟨InnerCascade.imcTuned 1 1 1 1 1 (1 / 2), 1, 1⟩

@[tmio M, powerlib_domain] private theorem overloaded_overload :
    overloaded.Vmax < |overloaded.vref| := by
  simp only [Vmax, overloaded, abs_one]
  rw [div_lt_one (by positivity), Real.lt_sqrt (by norm_num)]
  norm_num

/-- The overloaded platform is unstable. -/
@[tmio TM, powerlib_domain] theorem overloaded_mem_den_unstable :
    connection% (overloaded ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_overload overloaded (by norm_num [overloaded, InnerCascade.imcTuned])
    (by norm_num [overloaded]) overloaded_overload

/-- Within overload (with a positive filter and a positive DC link) instability is realized
soundly: every such platform is unstable. -/
@[tmio MI, powerlib_domain] theorem realizationSoundUnder_unstable_of_overload :
    connection% (implementation.RealizationSoundUnder {.physical, .dcLink, .overload}
      (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement Implementation.RealizationSoundUnder
  rintro y ⟨-, hΔ⟩
  rw [show implementation.impl = family from rfl, (connection_proof% TMIO.mem_realize)] at hΔ
  have hph : 0 < y.design.L ∧ 0 < y.design.C := hΔ .physical (by simp)
  have h := mem_den_unstable_of_overload y hph.1.ne' (hΔ .dcLink (by simp))
    (hΔ .overload (by simp))
  unfold powerlib.TMIO.Statement at h
  exact h

/-- Within overload local exponential stability is not realized soundly: the overloaded platform
has a locally exponentially stable design and is unstable. -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder_locallyExponentiallyStable :
    connection% (¬ implementation.RealizationSoundUnder {.physical, .dcLink, .overload}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hd := InnerCascade.imcTuned_mem_den_iff (L := 1) (R := 1) (C := 1) (ωc := 1) (Kpv := 1)
    (Kiv := 1 / 2) one_pos one_pos one_pos (P := .locallyExponentiallyStable) (Or.inl trivial)
  have hu := overloaded_mem_den_unstable
  unfold powerlib.TMIO.Statement at hd hu
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation) (y := overloaded)
    rfl (hd.mpr (by norm_num)) ?_ fun hmem => ?_
  · rw [show implementation.impl = family from rfl, (connection_proof% TMIO.mem_realize)]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · show 0 < overloaded.design.L ∧ 0 < overloaded.design.C
      norm_num [overloaded, InnerCascade.imcTuned]
    · show (0 : ℝ) < 1; norm_num
    · exact overloaded_overload
  rw [show implementation.impl = family from rfl,
    (connection_proof% family_isAutonomous.mem_den_flow)] at hmem
  rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hu
  exact hu hmem.lyapunovStable

/-- An unloaded platform: the IMC design `L = R = C = ω_c = K_pv = 1`, `K_iv = 1/2` at `v* = 0` with
`V_dc = 1` (headroom). -/
def unloaded : LimitedCascade := ⟨InnerCascade.imcTuned 1 1 1 1 1 (1 / 2), 0, 1⟩

/-- Global exponential stability is not realized soundly within all realistic constraints with
headroom: the unloaded platform has a globally exponentially stable design and is not globally
exponentially stable (`not_mem_den_globallyExponentiallyStable`). -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder_globallyExponentiallyStable :
    connection% (¬ implementation.RealizationSoundUnder {.physical, .dcLink, .headroom}
      (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hd := InnerCascade.imcTuned_mem_den_iff (L := 1) (R := 1) (C := 1) (ωc := 1) (Kpv := 1)
    (Kiv := 1 / 2) one_pos one_pos one_pos (P := .globallyExponentiallyStable) (Or.inl trivial)
  have hn := not_mem_den_globallyExponentiallyStable unloaded
  unfold powerlib.TMIO.Statement at hd hn
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation) (y := unloaded)
    rfl (hd.mpr (by norm_num)) ?_ hn
  rw [show implementation.impl = family from rfl, (connection_proof% TMIO.mem_realize)]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · show 0 < unloaded.design.L ∧ 0 < unloaded.design.C
    norm_num [unloaded, InnerCascade.imcTuned]
  · show (0 : ℝ) < 1; norm_num
  · show |(0 : ℝ)| < 1 / Real.sqrt 3
    rw [abs_zero]
    positivity

/-- A platform with an anti-stable filter and a stable design: `L = C = 1`, `R = −1`, `K_pc = 3`,
`K_ic = K_pv = 1`, `K_iv = 1/10` (the current loop's proportional gain overcomes the negative
resistance), at `v* = 0` with `V_dc = 1` (headroom). -/
def negResistance : LimitedCascade := ⟨⟨1, -1, 1, 3, 1, 1, 1 / 10⟩, 0, 1⟩

/-- Global asymptotic stability is not realized soundly within all realistic constraints with
headroom: the platform `negResistance` has a globally asymptotically stable (linear, Hurwitz)
design and is not globally asymptotically stable
(`not_mem_den_globallyAsymptoticallyStable_of_R_neg`). -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder_globallyAsymptoticallyStable :
    connection% (¬ implementation.RealizationSoundUnder {.physical, .dcLink, .headroom}
      (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hd := InnerCascade.mem_den_iff negResistance.design (by norm_num [negResistance])
    (by norm_num [negResistance]) (P := .globallyAsymptoticallyStable) (Or.inl trivial)
  have hn := not_mem_den_globallyAsymptoticallyStable_of_R_neg negResistance
    (by norm_num [negResistance]) (by norm_num [negResistance]) (by norm_num [negResistance])
  unfold powerlib.TMIO.Statement at hd hn
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation)
    (y := negResistance) rfl (hd.mpr (by norm_num [negResistance])) ?_ hn
  rw [show implementation.impl = family from rfl, (connection_proof% TMIO.mem_realize)]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · show 0 < negResistance.design.L ∧ 0 < negResistance.design.C
    norm_num [negResistance]
  · show (0 : ℝ) < 1; norm_num
  · show |(0 : ℝ)| < 1 / Real.sqrt 3
    rw [abs_zero]
    positivity

/-- Global exponential stability is realized completely, without constraints, vacuously: no
platform satisfies it. -/
@[tmio MI, powerlib_domain] theorem realizationCompleteUnder_globallyExponentiallyStable :
    connection% (implementation.RealizationCompleteUnder ∅
      (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Implementation.realizationCompleteUnder_of_forall_not_mem_den fun y => ?_
  have hn := not_mem_den_globallyExponentiallyStable y
  unfold powerlib.TMIO.Statement at hn
  exact hn

end LimitedCascade

end powerlib.GFM
