import theorem.GridTiedConverter.GFM.InnerCascade
import theorem.Delay.Pade
import theorem.Criteria.Routh5
import theorem.Stack.Implementation
import theorem.Spectral.LinearNamed

/-! # The grid-forming inner cascade with sampling and computation delay: an implementation layer

Model boundary.
* Implementation layer (I). A platform `DigitalCascade` realizes a design of the model layer (M),
  the single-axis grid-forming voltage/current cascade `InnerCascade.family` of
  `theorem/GridTiedConverter/GFM/InnerCascade.lean` (LC filter `L i̇ = −R i + u`, `C v̇ = i`, PI
  voltage loop `i* = K_pv (v* − v) + K_iv ζ`, PI current loop `u = K_pc (i* − i) + K_ic ξ`, ideal
  feed-forward and decoupling, GFM convention: current out of the converter positive), under one
  realistic constraint the design does not contain: the controller runs on a processor sampling
  with period `Tₛ`; one period of computation delay and the zero-order hold of the modulator make
  up the delay `τ = 3 Tₛ/2` (`DigitalCascade.τ`, as `CurrentControl.DigitalPI.τ`), taken as the
  Padé(1,1) block `Delay.pade11Model τ` between the current-loop output `u` and the voltage applied
  to the inductor: `ż = −(2/τ) z + u`, `w = (4/τ) z − u`, `L i̇ = −R i + w`
  (`DigitalCascade.field`, from the entries of `Delay.pade11Model`). The feed-forward and
  decoupling terms are applied without delay (part of the ideal design).
* State `(i, ξ, z, v, ζ) ∈ ℝ⁵ = EuclideanSpace ℝ (Fin 5)`, in this order: filter current,
  current-loop integrator, Padé state, capacitor voltage, voltage-loop integrator. Continuous
  time, linear. Input the voltage reference `v*`, output `v`; a flow sentence speaks about the
  zero-reference loop, which is the behaviour about the equilibrium of every constant reference.
* Parameters: the design `(L, R, C, K_pc, K_ic, K_pv, K_iv)` of any signs and the period `Tₛ`; the
  realistic range is `L, C > 0` (`physical`), `Tₛ > 0` (`sampling`).
* Excluded: the sampled-data dynamics themselves (only the Padé(1,1) equivalent of the delay is
  kept, accurate for `ω τ < 1/2`, `Delay.relPhaseError_pade11_lt`), the `sinc` magnitude of the
  hold, PWM ripple, quantization, the modulation limit
  (`theorem/GridTiedConverter/GFM/LimitedCascade.lean`), the line, the other axis, the
  synchronization and reactive-power loops.

Source: work-sync `theory/T-gfm-control.md` §1.9 (the inner cascade; a cascade at low switching
frequency can oscillate), `theory/T-control-delay.md`
§1.1 (the `1.5 Tₛ` total), §1.3 (Padé(1,1)), §1.6 (the bandwidth bound); the mirrored GFL
platform `theorem/GridTiedConverter/CurrentControl/DigitalPI.lean`; tools
`theorem/Delay/Pade.lean` (`Delay.pade11Model`, `Delay.pade11Num`, `Delay.pade11Den`),
`theorem/Criteria/Routh5.lean` (`Criteria.QuinticRouth`,
`Criteria.isHurwitz_iff_of_det_characteristicMatrix_quintic`), `theorem/Criteria/Routh4.lean`
(`Criteria.quartic_hurwitz_iff`), `theorem/Stack/Implementation.lean`. The witnesses were found by
an exact rational grid search (fractions) and are certified here.

Results.
* Static: `model_field` (the plant is the platform field), `isEquilibrium`,
  `equilibrium_voltage` (the delay keeps `v = v*` at every equilibrium).
* `det_characteristicMatrix` (`L, C, Tₛ ≠ 0`): `det (sI − A) = s⁵ + (b₄ s⁴ + b₃ s³ + b₂ s² + b₁ s
  + b₀)/b₅` with `b₅ = C L τ/2`, `b₄ = C (L + (R − K_pc) τ/2)`,
  `b₃ = C (R + K_pc − K_ic τ/2) − K_pc K_pv τ/2`,
  `b₂ = C K_ic + K_pc K_pv − (K_ic K_pv + K_iv K_pc) τ/2`,
  `b₁ = K_ic K_pv + K_iv K_pc − K_ic K_iv τ/2`, `b₀ = K_ic K_iv`; `charPoly_eq_pade`:
  `b₅ s⁵ + … + b₀ = C s² ((L s + R) s D(s) + (K_pc s + K_ic) N(s)) +
  (K_pv s + K_iv)(K_pc s + K_ic) N(s)` with the Padé numerator `N(s) = 1 − τ s/2` and denominator
  `D(s) = 1 + τ s/2` (`Delay.pade11Num`, `Delay.pade11Den`): the design cascade closed through the
  delay.
* `exists_root_of_lagged`: a strict violation of the quintic Routh conditions
  (`Criteria.QuinticRouthViolation` of `b₄/b₅, …, b₀/b₅`) gives a root in the open right half plane.
* IMC current tuning (`imcTuned`, `K_pc = L ω_c`, `K_ic = R ω_c`):
  `imcTuned_charPoly`, the platform polynomial is `(L s + R)` times
  `e₄ s⁴ + e₃ s³ + e₂ s² + e₁ s + e₀`, `e₄ = C τ/2`, `e₃ = C (1 − ω_c τ/2)`,
  `e₂ = ω_c (C − K_pv τ/2)`, `e₁ = ω_c (K_pv − K_iv τ/2)`, `e₀ = ω_c K_iv`.

Family and connection conclusions.
* I layer. `DigitalCascade.family : Family DigitalCascade CascadeRequirement 5 1`. Requirements:
  the lifted design requirements `design q`, `physical` (`0 < L ∧ 0 < C`), `sampling` (`0 < Tₛ`),
  `routh` (the quintic Routh conditions of the platform) and `lagged` (their strict violation).
  The attractive sentences, sampled contraction and Lyapunov stability translate into
  `{physical, sampling, routh}`, instability into `{physical, sampling, lagged}`, decay rates,
  conservation and passivity into the whole, inconsistent, language (`realize_univ`).
  `chain_le_semantics`: every translation is sound. `exactUnder`: within `{physical, sampling}` the
  attractive and contractive translations are exact. `mem_den_iff`: with `L, C, Tₛ > 0` an
  attractive sentence holds iff `Criteria.QuinticRouth (b₄/b₅) (b₃/b₅) (b₂/b₅) (b₁/b₅) (b₀/b₅)`.
  `imcTuned_mem_den_iff`: with `L, R, C, Tₛ > 0` the IMC-tuned platform satisfies an attractive
  sentence iff `0 < e₃`, `0 < e₁`, `0 < e₀` and `e₄ e₁² + e₃² e₀ < e₃ e₂ e₁` (the quartic Routh
  conditions of the factor; for `ω_c > 0`, in the units `x = ω_c τ`, `k_p = K_pv/(C ω_c)`,
  `k_i = K_iv/(C ω_c²)`: `x < 2`, `k_i x < 2 k_p`, `k_i > 0` and
  `8 k_p − 8 k_i − 4 k_p x + 4 k_i x − 8 k_p² x + 2 k_p² x² + 6 k_i k_p x² − k_i k_p x³ −
  k_i² x³ > 0`; at `x = 0` the design condition `k_i < k_p` of
  `InnerCascade.imcTuned_mem_den_iff`). `tuned_mem_den_iff`: with the voltage gains
  `K_pv = C ω_v`, `K_iv = C ω_v²/4` and `ω_c, ω_v > 0`, an attractive sentence holds iff, with
  `a = ω_c τ`, `b = ω_v τ`: `a < 2`, `b < 8` and
  `0 < 128 a − 64 a² − 32 b − 112 a b + 32 a² b + 24 a b² − 4 a² b² − a b³` (an explicit
  boundary in the plane of the two delay-scaled bandwidths).
* M–I. `implementation : Implementation InnerCascade Spectral.Requirement DigitalCascade
  CascadeRequirement 4 1 5 1`, every platform realizing its design (`Implementation.ofDesign`).
  `not_realizationSoundUnder`: within `{physical, sampling}` the attractive sentences are not
  realized soundly — `slowCascade` (IMC design `L = R = C = ω_c = 1`, `K_pv = 1`, `K_iv = 1/2`,
  stable by `InnerCascade.imcTuned_mem_den_iff`; `Tₛ = 2`, `b₃ = −1 < 0`) is unstable
  (`slowCascade_design_mem_den`, `slowCascade_mem_den_unstable`).
  `not_realizationCompleteUnder`: nor completely — unlike the GFL current loop
  (`CurrentControl.DigitalPI.realizationCompleteUnder`: the delay never stabilizes), the delay can
  stabilize the cascade: `delayStabilized` (design `L = C = 1`, `R = 1/20`, `K_pc = 3`, `K_ic = 4`,
  `K_pv = 1/2`, `K_iv = 2`, Routh determinant `a₃ a₂ a₁ − a₁² − a₃² a₀ < 0`, unstable,
  `delayStabilized_design_mem_den_unstable`; period `Tₛ = 1/6`, quintic Routh conditions hold,
  `delayStabilized_mem_den`). So the delay changes the attractive sentences of the cascade in both
  directions, and only the exact platform conditions `mem_den_iff` decide them. Scaffold:
  `theorem/GridTiedConverter/GFM/DigitalCascade.agda`.

Scope (the Padé platform versus the pure delay): as for `CurrentControl.DigitalPI`, every
conclusion is about the Padé(1,1) platform, not the transcendental delay loop.
-/

noncomputable section
namespace powerlib.GFM
open Matrix Linear LinearSystems TMIO

local notation "ℝ⁵" => EuclideanSpace ℝ (Fin 5)

/-- A digital implementation of the grid-forming inner cascade: the cascade design and the
sampling period `Tₛ`. -/
@[ext] structure DigitalCascade where
  /-- The cascade design, a member of `InnerCascade.family`. -/
  design : InnerCascade
  /-- The sampling period `Tₛ`. -/
  Ts : ℝ

namespace DigitalCascade

variable (y : DigitalCascade)

/-- The total equivalent delay `τ = 3 Tₛ/2`: one period of computation delay and half a period of
zero-order hold. -/
def τ : ℝ := 3 * y.Ts / 2

/-- The current reference of the voltage loop, `i* = K_pv (v* − v) + K_iv ζ`. -/
def currentRef (vref : ℝ) (x : ℝ⁵) : ℝ := y.design.Kpv * (vref - x 3) + y.design.Kiv * x 4

/-- The current-loop output `u = K_pc (i* − i) + K_ic ξ`. -/
def control (vref : ℝ) (x : ℝ⁵) : ℝ :=
  y.design.Kpc * (y.currentRef vref x - x 0) + y.design.Kic * x 1

/-- The voltage applied to the inductor: the output of the Padé(1,1) block `Delay.pade11Model τ`
with state `z = x 2`, driven by the current-loop output. -/
def applied (vref : ℝ) (x : ℝ⁵) : ℝ :=
  (Delay.pade11Model y.τ).C 0 0 * x 2 + (Delay.pade11Model y.τ).D 0 0 * y.control vref x

/-- The platform field `(i̇, ξ̇, ż, v̇, ζ̇)`: `L i̇ = −R i + w`, `ξ̇ = i* − i`, the Padé state
equation driven by `u`, `C v̇ = i`, `ζ̇ = v* − v`. -/
def field (vref : ℝ) (x : ℝ⁵) : ℝ⁵ :=
  WithLp.toLp 2 ![(-y.design.R * x 0 + y.applied vref x) / y.design.L, y.currentRef vref x - x 0,
    (Delay.pade11Model y.τ).A 0 0 * x 2 + (Delay.pade11Model y.τ).B 0 0 * y.control vref x,
    x 0 / y.design.C, vref - x 3]

/-- The platform as a linear plant: input `v*`, output `v`. -/
def model : Plant 5 1 :=
  ⟨!![(y.design.Kpc - y.design.R) / y.design.L, -y.design.Kic / y.design.L,
      4 / (y.τ * y.design.L), y.design.Kpc * y.design.Kpv / y.design.L,
      -(y.design.Kpc * y.design.Kiv) / y.design.L;
    -1, 0, 0, -y.design.Kpv, y.design.Kiv;
    -y.design.Kpc, y.design.Kic, -2 / y.τ, -(y.design.Kpc * y.design.Kpv),
      y.design.Kpc * y.design.Kiv;
    1 / y.design.C, 0, 0, 0, 0;
    0, 0, 0, -1, 0],
    !![-(y.design.Kpc * y.design.Kpv) / y.design.L; y.design.Kpv; y.design.Kpc * y.design.Kpv;
      0; 1], !![0, 0, 0, 1, 0], !![0]⟩

/-- The plant is exactly the platform field. -/
@[tmio M, powerlib_domain] theorem model_field (vref : ℝ) (x : ℝ⁵) :
    y.model.inputField (fun _ => vref) x = y.field vref x := by
  ext j
  fin_cases j <;>
    simp [Plant.inputField, model, field, applied, control, currentRef, Delay.pade11Model, op,
      Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> ring

/-- The equilibrium for a constant reference: `i = ξ = z = 0`, `v = v*`, `ζ = 0`. -/
def equilibrium (vref : ℝ) : ℝ⁵ := WithLp.toLp 2 ![0, 0, 0, vref, 0]

@[tmio M, powerlib_domain] theorem isEquilibrium (vref : ℝ) :
    IsEquilibrium (y.model.inputField fun _ => vref) (equilibrium vref) := by
  rw [IsEquilibrium, model_field]
  ext j
  fin_cases j <;> simp [field, applied, control, currentRef, equilibrium]

/-- Every equilibrium of the platform has zero voltage error `v = v*`. Static evidence on the
implementation, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_voltage {vref : ℝ} {e : ℝ⁵}
    (he : IsEquilibrium (y.model.inputField fun _ => vref) e) : e 3 = vref := by
  rw [IsEquilibrium, model_field] at he
  have h := congrArg (fun z : ℝ⁵ => z 4) he
  simp [field] at h
  linarith

/-! ### The characteristic polynomial -/

/-- `b₅ = C L τ/2`. -/
def b5 : ℝ := y.design.C * y.design.L * y.τ / 2

/-- `b₄ = C (L + (R − K_pc) τ/2)`. -/
def b4 : ℝ := y.design.C * (y.design.L + (y.design.R - y.design.Kpc) * y.τ / 2)

/-- `b₃ = C (R + K_pc − K_ic τ/2) − K_pc K_pv τ/2`. -/
def b3 : ℝ := y.design.C * (y.design.R + y.design.Kpc - y.design.Kic * y.τ / 2) -
  y.design.Kpc * y.design.Kpv * y.τ / 2

/-- `b₂ = C K_ic + K_pc K_pv − (K_ic K_pv + K_iv K_pc) τ/2`. -/
def b2 : ℝ := y.design.C * y.design.Kic + y.design.Kpc * y.design.Kpv -
  (y.design.Kic * y.design.Kpv + y.design.Kiv * y.design.Kpc) * y.τ / 2

/-- `b₁ = K_ic K_pv + K_iv K_pc − K_ic K_iv τ/2`. -/
def b1 : ℝ := y.design.Kic * y.design.Kpv + y.design.Kiv * y.design.Kpc -
  y.design.Kic * y.design.Kiv * y.τ / 2

/-- `b₀ = K_ic K_iv`. -/
def b0 : ℝ := y.design.Kic * y.design.Kiv

/-- The characteristic polynomial of the platform:
`det (sI − A) = s⁵ + (b₄/b₅) s⁴ + (b₃/b₅) s³ + (b₂/b₅) s² + (b₁/b₅) s + b₀/b₅`. Static evidence on
the implementation. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix (hL : y.design.L ≠ 0)
    (hC : y.design.C ≠ 0) (hT : y.Ts ≠ 0) (s : ℂ) :
    (characteristicMatrix y.model.A s).det =
      s ^ 5 + ((y.b4 / y.b5 : ℝ) : ℂ) * s ^ 4 + ((y.b3 / y.b5 : ℝ) : ℂ) * s ^ 3 +
        ((y.b2 / y.b5 : ℝ) : ℂ) * s ^ 2 + ((y.b1 / y.b5 : ℝ) : ℂ) * s +
          ((y.b0 / y.b5 : ℝ) : ℂ) := by
  have hτ : y.τ ≠ 0 := by unfold τ; intro h; apply hT; linarith
  have hL' : (y.design.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hC' : (y.design.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hτ' : (y.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  simp only [characteristicMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  simp [model, complexify, Fin.succAbove, Fin.lt_def, b5, b4, b3, b2, b1, b0]
  field_simp
  ring

/-- The platform polynomial is the design cascade closed through the Padé(1,1) delay:
`b₅ s⁵ + … + b₀ = C s² ((L s + R) s D(s) + (K_pc s + K_ic) N(s)) + (K_pv s + K_iv)(K_pc s + K_ic)
N(s)`. Static evidence on the implementation. -/
@[tmio M, powerlib_domain] theorem charPoly_eq_pade (s : ℂ) :
    (y.b5 : ℂ) * s ^ 5 + y.b4 * s ^ 4 + y.b3 * s ^ 3 + y.b2 * s ^ 2 + y.b1 * s + y.b0 =
      (y.design.C : ℂ) * s ^ 2 * (((y.design.L : ℂ) * s + y.design.R) * s *
          Delay.pade11Den y.τ s + ((y.design.Kpc : ℂ) * s + y.design.Kic) *
          Delay.pade11Num y.τ s) +
        ((y.design.Kpv : ℂ) * s + y.design.Kiv) * ((y.design.Kpc : ℂ) * s + y.design.Kic) *
          Delay.pade11Num y.τ s := by
  simp only [b5, b4, b3, b2, b1, b0, Delay.pade11Den, Delay.pade11Num]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem b5_pos {y : DigitalCascade} (hL : 0 < y.design.L)
    (hC : 0 < y.design.C) (hT : 0 < y.Ts) : 0 < y.b5 := by
  unfold b5 τ
  positivity

/-- The platform Routh conditions: the quintic Hurwitz determinants of the monic characteristic
polynomial are positive. -/
abbrev Routh : Prop :=
  Criteria.QuinticRouth (y.b4 / y.b5) (y.b3 / y.b5) (y.b2 / y.b5) (y.b1 / y.b5) (y.b0 / y.b5)

/-- A strict violation of the platform Routh conditions. -/
abbrev Lagged : Prop :=
  Criteria.QuinticRouthViolation (y.b4 / y.b5) (y.b3 / y.b5) (y.b2 / y.b5) (y.b1 / y.b5)
    (y.b0 / y.b5)

/-- A strict violation of the platform Routh conditions gives a characteristic root in the open
right half plane. Static evidence on the implementation. -/
@[tmio M, powerlib_domain] theorem exists_root_of_lagged {y : DigitalCascade}
    (hL : 0 < y.design.L) (hC : 0 < y.design.C) (hT : 0 < y.Ts) (h : y.Lagged) :
    ∃ s : ℂ, (characteristicMatrix y.model.A s).det = 0 ∧ 0 < s.re := by
  obtain ⟨s, hs, hre⟩ := Criteria.exists_quintic_root_re_pos_of_violation h
  exact ⟨s, by rw [det_characteristicMatrix y hL.ne' hC.ne' hT.ne']; exact hs, hre⟩

end DigitalCascade

/-! ## The implementation family -/

/-- Requirements on digital cascade platforms: the lifted design requirements and the realistic
constraints. -/
inductive CascadeRequirement
  /-- The cascade design meets the requirement `q` of `InnerCascade.family`. -/
  | design (q : Spectral.Requirement)
  /-- Positive filter inductance and capacitance `0 < L`, `0 < C`. -/
  | physical
  /-- A positive sampling period `0 < Tₛ`. -/
  | sampling
  /-- The quintic Routh conditions of the platform. -/
  | routh
  /-- A strict violation of the quintic Routh conditions of the platform. -/
  | lagged

namespace DigitalCascade

/-- Satisfaction of a platform requirement. -/
def Meets (y : DigitalCascade) : CascadeRequirement → Prop
  | .design q => InnerCascade.family.meets y.design q
  | .physical => 0 < y.design.L ∧ 0 < y.design.C
  | .sampling => 0 < y.Ts
  | .routh => y.Routh
  | .lagged => y.Lagged

/-- The translation of the sentences into platform requirements: the attractive sentences,
sampled contraction and Lyapunov stability into the physical range and the Routh conditions;
instability into the physical range and a strict violation; decay rates, conservation and
passivity into the whole, inconsistent, language. -/
def translate : Sentence → Set CascadeRequirement
  | .flow .unstable => {.physical, .sampling, .lagged}
  | .flow (.decay _) | .flow .conservative | .passive => Set.univ
  | .flow _ => {.physical, .sampling, .routh}
  | .envelope _ => ∅

/-- The digital cascade platforms, each read as the port system of its plant (input `v*`, output
`v`). -/
def family : Family DigitalCascade CascadeRequirement 5 1 :=
  ⟨fun y => y.model.system, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isLinear : family.IsLinear model := fun _ => rfl

/-- **The platform, exactly**: with `L, C, Tₛ > 0` an attractive sentence (in particular global
exponential stability) or sampled contraction holds iff the quintic Routh conditions of the
platform hold. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff (y : DigitalCascade) (hL : 0 < y.design.L)
    (hC : 0 < y.design.C) (hT : 0 < y.Ts) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (y ∈ family.den (.flow P) ↔ y ∈ {y : DigitalCascade | y.Routh}) := by
  unfold TMIO.Statement
  rw [(connection_proof% (family_isLinear.mem_den_hurwitz hP))]
  exact Criteria.isHurwitz_iff_of_det_characteristicMatrix_quintic _
    (det_characteristicMatrix y hL.ne' hC.ne' hT.ne')

/-- The whole platform requirement language is inconsistent: the Routh conditions exclude every
strict violation. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize family.meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun y h => ?_
  exact Criteria.not_quinticRouthViolation_of_quinticRouth (h .routh) (h .lagged)

/-- The platform translation is the linear table of `theorem/Spectral/LinearNamed.lean`. -/
@[tmio TM, powerlib_domain] private theorem translate_eq_linearTable (s : Sentence) :
    connection% (generate (cover (table translate)) {s} =
      Spectral.linearTable {.physical, .sampling, .routh}
      {.physical, .sampling, .lagged} Set.univ Set.univ (fun _ => Set.univ) s) := by
  unfold TMIO.Statement
  rw [TMIO.image_table_singleton]
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- Every translation of the platform family is sound: the Routh conditions give a Hurwitz plant,
a strict violation a characteristic root in the open right half plane. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_linearTable_univ (F := family) family_isLinear
    (fun s => (connection_proof% TMIO.image_table_singleton translate s).symm.trans
      (connection_proof% translate_eq_linearTable s)) (fun y hy => ?_) (fun y hy => ?_)
    fun _ => Spectral.realize_univ_subset_of_eq_empty realize_univ _
  · rw [(connection_proof% TMIO.mem_realize)] at hy
    have hph : 0 < y.design.L ∧ 0 < y.design.C := hy .physical (by simp)
    exact (family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).mp
      ((mem_den_iff y hph.1 hph.2 (hy .sampling (by simp))
        (P := .globallyExponentiallyStable) (Or.inl trivial)).mpr (hy .routh (by simp)))
  · rw [(connection_proof% TMIO.mem_realize)] at hy
    have hph : 0 < y.design.L ∧ 0 < y.design.C := hy .physical (by simp)
    exact exists_root_of_lagged hph.1 hph.2 (hy .sampling (by simp)) (hy .lagged (by simp))

/-- Within the physical range and a positive period, the attractive sentences and sampled
contraction of the platform are translated exactly. -/
@[tmio TM, powerlib_domain] theorem exactUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.ExactUnder {.physical, .sampling} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_of_linearTable (F := family) family_isLinear
    (fun s => (connection_proof% TMIO.image_table_singleton translate s).symm.trans
      (connection_proof% translate_eq_linearTable s)) _ (fun y hΔ => ?_) hP
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hph : 0 < y.design.L ∧ 0 < y.design.C := hΔ .physical (by simp)
  have hT : 0 < y.Ts := hΔ .sampling (by simp)
  rw [((family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable)
      (Or.inl trivial)).symm.trans
    (mem_den_iff y hph.1 hph.2 hT (P := .globallyExponentiallyStable) (Or.inl trivial))),
    (connection_proof% TMIO.mem_realize)]
  refine ⟨fun h => h .routh (by simp), fun h q hq => ?_⟩
  rcases hq with rfl | rfl | rfl
  exacts [hph, hT, h]

/-! ## IMC tuning of the current loop -/

/-- The platform of the IMC-tuned cascade `InnerCascade.imcTuned L R C ω_c K_pv K_iv`
(`K_pc = L ω_c`, `K_ic = R ω_c`) sampled with period `Tₛ`. -/
def imcTuned (L R C ωc Kpv Kiv Ts : ℝ) : DigitalCascade :=
  ⟨InnerCascade.imcTuned L R C ωc Kpv Kiv, Ts⟩

/-- **The IMC platform polynomial factors**: `b₅ s⁵ + … + b₀ = (L s + R)(e₄ s⁴ + e₃ s³ + e₂ s² +
e₁ s + e₀)` with `e₄ = C τ/2`, `e₃ = C (1 − ω_c τ/2)`, `e₂ = ω_c (C − K_pv τ/2)`,
`e₁ = ω_c (K_pv − K_iv τ/2)`, `e₀ = ω_c K_iv`. Static evidence on the implementation. -/
@[tmio M, powerlib_domain] theorem imcTuned_charPoly (L R C ωc Kpv Kiv Ts : ℝ) (s : ℂ) :
    let y := imcTuned L R C ωc Kpv Kiv Ts
    (y.b5 : ℂ) * s ^ 5 + y.b4 * s ^ 4 + y.b3 * s ^ 3 + y.b2 * s ^ 2 + y.b1 * s + y.b0 =
      ((L : ℂ) * s + R) * (((C * y.τ / 2 : ℝ) : ℂ) * s ^ 4 + ((C * (1 - ωc * y.τ / 2) : ℝ) : ℂ) *
        s ^ 3 + ((ωc * (C - Kpv * y.τ / 2) : ℝ) : ℂ) * s ^ 2 +
          ((ωc * (Kpv - Kiv * y.τ / 2) : ℝ) : ℂ) * s + ((ωc * Kiv : ℝ) : ℂ)) := by
  simp only [imcTuned, InnerCascade.imcTuned, b5, b4, b3, b2, b1, b0]
  push_cast
  ring

/-- **The IMC platform, exactly**: with `L, R, C, Tₛ > 0` the IMC-tuned platform satisfies an
attractive sentence (or sampled contraction) iff the quartic factor is Hurwitz, `0 < e₃`,
`0 < e₁`, `0 < e₀` and `e₄ e₁² + e₃² e₀ < e₃ e₂ e₁` (`Criteria.quartic_hurwitz_iff`; the factor
`L s + R` has its root at `−R/L < 0`). -/
@[tmio TM, powerlib_domain] theorem imcTuned_mem_den_iff {L R C ωc Kpv Kiv Ts : ℝ} (hL : 0 < L)
    (hR : 0 < R) (hC : 0 < C) (hT : 0 < Ts) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (imcTuned L R C ωc Kpv Kiv Ts ∈ family.den (.flow P) ↔
      imcTuned L R C ωc Kpv Kiv Ts ∈ {y : DigitalCascade |
        0 < C * (1 - ωc * y.τ / 2) ∧ 0 < ωc * (Kpv - Kiv * y.τ / 2) ∧ 0 < ωc * Kiv ∧
        C * y.τ / 2 * (ωc * (Kpv - Kiv * y.τ / 2)) ^ 2 + (C * (1 - ωc * y.τ / 2)) ^ 2 *
            (ωc * Kiv) <
          C * (1 - ωc * y.τ / 2) * (ωc * (C - Kpv * y.τ / 2)) * (ωc * (Kpv - Kiv * y.τ / 2))}) := by
  unfold TMIO.Statement
  set y := imcTuned L R C ωc Kpv Kiv Ts with hy
  have hyL : 0 < y.design.L := hL
  have hyC : 0 < y.design.C := hC
  have hyT : 0 < y.Ts := hT
  have hτ : 0 < y.τ := by unfold τ; positivity
  set e4 := C * y.τ / 2 with he4
  set e3 := C * (1 - ωc * y.τ / 2) with he3
  set e2 := ωc * (C - Kpv * y.τ / 2) with he2
  set e1 := ωc * (Kpv - Kiv * y.τ / 2) with he1
  set e0 := ωc * Kiv with he0
  have h4 : 0 < e4 := by rw [he4]; positivity
  have hb5 := b5_pos hyL hyC hyT
  rw [(connection_proof% (family_isLinear.mem_den_hurwitz hP)),
    ← spectrallyStable_iff_isHurwitz]
  simp only [Set.mem_ofPred_eq]
  -- the roots of the characteristic determinant are those of `(L s + R) Q(s)`
  have hroot : ∀ s : ℂ, (characteristicMatrix y.model.A s).det = 0 ↔
      s ^ 4 + ((e3 / e4 : ℝ) : ℂ) * s ^ 3 + ((e2 / e4 : ℝ) : ℂ) * s ^ 2 +
        ((e1 / e4 : ℝ) : ℂ) * s + ((e0 / e4 : ℝ) : ℂ) = 0 ∨ s = ((-R / L : ℝ) : ℂ) := by
    intro s
    have hb5' : (y.b5 : ℂ) ≠ 0 := by exact_mod_cast hb5.ne'
    have h4' : (e4 : ℂ) ≠ 0 := by exact_mod_cast h4.ne'
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hcp := imcTuned_charPoly L R C ωc Kpv Kiv Ts s
    rw [det_characteristicMatrix y hyL.ne' hyC.ne' hyT.ne']
    have e : s ^ 5 + ((y.b4 / y.b5 : ℝ) : ℂ) * s ^ 4 + ((y.b3 / y.b5 : ℝ) : ℂ) * s ^ 3 +
        ((y.b2 / y.b5 : ℝ) : ℂ) * s ^ 2 + ((y.b1 / y.b5 : ℝ) : ℂ) * s + ((y.b0 / y.b5 : ℝ) : ℂ) =
        (e4 : ℂ) / y.b5 * (((L : ℂ) * s + R) * (s ^ 4 + ((e3 / e4 : ℝ) : ℂ) * s ^ 3 +
          ((e2 / e4 : ℝ) : ℂ) * s ^ 2 + ((e1 / e4 : ℝ) : ℂ) * s + ((e0 / e4 : ℝ) : ℂ))) := by
      have hcp' : (y.b5 : ℂ) * s ^ 5 + y.b4 * s ^ 4 + y.b3 * s ^ 3 + y.b2 * s ^ 2 + y.b1 * s +
          y.b0 =
            ((L : ℂ) * s + R) * ((e4 : ℂ) * s ^ 4 + e3 * s ^ 3 + e2 * s ^ 2 + e1 * s + e0) := by
        rw [hcp]
      push_cast
      field_simp
      linear_combination hcp'
    rw [e, mul_eq_zero, mul_eq_zero, or_iff_right (div_ne_zero h4' hb5'), or_comm]
    refine or_congr_right ?_
    constructor
    · intro h; push_cast; field_simp; linear_combination h
    · intro h; rw [h]; push_cast; field_simp; ring
  constructor
  · intro hS
    have hQ : ∀ s : ℂ, s ^ 4 + ((e3 / e4 : ℝ) : ℂ) * s ^ 3 + ((e2 / e4 : ℝ) : ℂ) * s ^ 2 +
        ((e1 / e4 : ℝ) : ℂ) * s + ((e0 / e4 : ℝ) : ℂ) = 0 → s.re < 0 :=
      fun s hs => hS s ((hroot s).mpr (Or.inl hs))
    obtain ⟨g3, g1, g0, gg⟩ := (Criteria.quartic_hurwitz_iff _ _ _ _).mp hQ
    refine ⟨(div_pos_iff_of_pos_right h4).mp g3, (div_pos_iff_of_pos_right h4).mp g1,
      (div_pos_iff_of_pos_right h4).mp g0, ?_⟩
    have k1 : e4 ^ 3 * ((e1 / e4) ^ 2 + (e3 / e4) ^ 2 * (e0 / e4)) = e4 * e1 ^ 2 + e3 ^ 2 * e0 := by
      field_simp
    have k2 : e4 ^ 3 * (e3 / e4 * (e2 / e4) * (e1 / e4)) = e3 * e2 * e1 := by
      field_simp
    have := mul_lt_mul_of_pos_left gg (pow_pos h4 3)
    rwa [k1, k2] at this
  · rintro ⟨g3, g1, g0, gg⟩ s hs
    rcases (hroot s).mp hs with hq | rfl
    · refine (Criteria.quartic_hurwitz_iff _ _ _ _).mpr ⟨div_pos g3 h4, div_pos g1 h4,
        div_pos g0 h4, ?_⟩ s hq
      have k1 : e4 ^ 3 * ((e1 / e4) ^ 2 + (e3 / e4) ^ 2 * (e0 / e4)) =
          e4 * e1 ^ 2 + e3 ^ 2 * e0 := by
        field_simp
      have k2 : e4 ^ 3 * (e3 / e4 * (e2 / e4) * (e1 / e4)) = e3 * e2 * e1 := by
        field_simp
      refine (mul_lt_mul_iff_of_pos_left (pow_pos h4 3)).mp ?_
      rw [k1, k2]
      exact gg
    · rw [Complex.ofReal_re]
      exact div_neg_of_neg_of_pos (by linarith) hL

/-- **The doubly tuned platform, an explicit boundary**: the IMC current loop with the voltage
gains `K_pv = C ω_v`, `K_iv = C ω_v²/4` (the design voltage loop `C (s + ω_v/2)²`), with
`L, R, C, Tₛ, ω_c, ω_v > 0`, satisfies an attractive sentence iff, with `a = ω_c τ`, `b = ω_v τ`,
`a < 2`, `b < 8` and `0 < 128 a − 64 a² − 32 b − 112 a b + 32 a² b + 24 a b² − 4 a² b² − a b³`
(the Routh determinant of the quartic factor is `C³ ω_c ω_v` times this polynomial over `128 τ`;
for `a → 0` with `b/a = ω_v/ω_c` fixed it tends to the design condition `ω_v < 4 ω_c`). -/
@[tmio TM, powerlib_domain] theorem tuned_mem_den_iff {L R C ωc ωv Ts : ℝ} (hL : 0 < L)
    (hR : 0 < R) (hC : 0 < C) (hT : 0 < Ts) (hωc : 0 < ωc) (hωv : 0 < ωv) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (imcTuned L R C ωc (C * ωv) (C * ωv ^ 2 / 4) Ts ∈ family.den (.flow P) ↔
      imcTuned L R C ωc (C * ωv) (C * ωv ^ 2 / 4) Ts ∈ {y : DigitalCascade |
        ωc * y.τ < 2 ∧ ωv * y.τ < 8 ∧
        0 < 128 * (ωc * y.τ) - 64 * (ωc * y.τ) ^ 2 - 32 * (ωv * y.τ) -
          112 * (ωc * y.τ) * (ωv * y.τ) + 32 * (ωc * y.τ) ^ 2 * (ωv * y.τ) +
          24 * (ωc * y.τ) * (ωv * y.τ) ^ 2 - 4 * (ωc * y.τ) ^ 2 * (ωv * y.τ) ^ 2 -
          (ωc * y.τ) * (ωv * y.τ) ^ 3}) := by
  have h := imcTuned_mem_den_iff (L := L) (R := R) (C := C) (ωc := ωc) (Kpv := C * ωv)
    (Kiv := C * ωv ^ 2 / 4) hL hR hC hT hP
  unfold TMIO.Statement at h ⊢
  rw [h]
  simp only [Set.mem_ofPred_eq]
  set τ := (imcTuned L R C ωc (C * ωv) (C * ωv ^ 2 / 4) Ts).τ with hτdef
  have hτ : 0 < τ := by rw [hτdef]; unfold DigitalCascade.τ imcTuned; positivity
  have hD : C * (1 - ωc * τ / 2) * (ωc * (C - C * ωv * τ / 2)) *
        (ωc * (C * ωv - C * ωv ^ 2 / 4 * τ / 2)) -
      (C * τ / 2 * (ωc * (C * ωv - C * ωv ^ 2 / 4 * τ / 2)) ^ 2 +
        (C * (1 - ωc * τ / 2)) ^ 2 * (ωc * (C * ωv ^ 2 / 4))) =
      C ^ 3 * ωc * ωv / (128 * τ) * (128 * (ωc * τ) - 64 * (ωc * τ) ^ 2 - 32 * (ωv * τ) -
        112 * (ωc * τ) * (ωv * τ) + 32 * (ωc * τ) ^ 2 * (ωv * τ) +
        24 * (ωc * τ) * (ωv * τ) ^ 2 - 4 * (ωc * τ) ^ 2 * (ωv * τ) ^ 2 -
        (ωc * τ) * (ωv * τ) ^ 3) := by
    field_simp
    ring
  have hk : 0 < C ^ 3 * ωc * ωv / (128 * τ) := by positivity
  have e1 : ωc * (C * ωv - C * ωv ^ 2 / 4 * τ / 2) = ωc * C * ωv * (1 - ωv * τ / 8) := by ring
  constructor
  · rintro ⟨g3, g1, -, gg⟩
    refine ⟨?_, ?_, ?_⟩
    · have := (mul_pos_iff_of_pos_left hC).mp g3
      linarith
    · rw [e1] at g1
      have := (mul_pos_iff_of_pos_left (by positivity : 0 < ωc * C * ωv)).mp g1
      linarith
    · have := sub_pos.mpr gg
      rw [hD] at this
      exact (mul_pos_iff_of_pos_left hk).mp this
  · rintro ⟨g3, g1, gg⟩
    refine ⟨mul_pos hC (by linarith), ?_, by positivity, ?_⟩
    · rw [e1]
      exact mul_pos (by positivity) (by linarith)
    · rw [← sub_pos, hD]
      exact mul_pos hk gg

/-! ## The digital cascade as an implementation of the cascade design (M–I) -/

/-- The digital cascade platforms as an implementation layer over the cascade design family: each
platform realizes its design. -/
def implementation :
    Implementation InnerCascade Spectral.Requirement DigitalCascade CascadeRequirement 4 1 5 1 :=
  { model := InnerCascade.family, impl := family, realizes := Implementation.ofDesign design }

/-- A slowly sampled IMC cascade: `L = R = C = ω_c = 1`, `K_pv = 1`, `K_iv = 1/2`, `Tₛ = 2`. -/
def slowCascade : DigitalCascade := ⟨InnerCascade.imcTuned 1 1 1 1 1 (1 / 2), 2⟩

/-- The design of the slow platform satisfies every attractive sentence (`0 < K_iv < ω_c K_pv`,
`InnerCascade.imcTuned_mem_den_iff`). -/
@[tmio TM, powerlib_domain] theorem slowCascade_design_mem_den {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (slowCascade.design ∈ InnerCascade.family.den (.flow P)) := by
  have h := InnerCascade.imcTuned_mem_den_iff (L := 1) (R := 1) (C := 1) (ωc := 1) (Kpv := 1)
    (Kiv := 1 / 2) one_pos one_pos one_pos hP
  unfold powerlib.TMIO.Statement at h ⊢
  exact h.mpr (by norm_num)

/-- The slow platform is unstable: `b₃ = −1 < 0`. -/
@[tmio TM, powerlib_domain] theorem slowCascade_mem_den_unstable :
    connection% (slowCascade ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isLinear.mem_den_flow)]
  obtain ⟨s, hs, hre⟩ := exists_root_of_lagged (y := slowCascade)
    (by norm_num [slowCascade, InnerCascade.imcTuned])
    (by norm_num [slowCascade, InnerCascade.imcTuned]) (by norm_num [slowCascade])
    (Or.inr (Or.inl (by
      norm_num [slowCascade, InnerCascade.imcTuned, b5, b3, τ])))
  exact unstable_of_root 0 hs hre

/-- **The attractive sentences are not realized soundly within the physical range and a positive
period**: the slow platform has a stable design and is unstable. -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (¬ implementation.RealizationSoundUnder {.physical, .sampling} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hd := slowCascade_design_mem_den hP
  have hu := slowCascade_mem_den_unstable
  unfold powerlib.TMIO.Statement at hd hu
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation) rfl hd ?_
    fun hmem => ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · show 0 < slowCascade.design.L ∧ 0 < slowCascade.design.C
      norm_num [slowCascade, InnerCascade.imcTuned]
    · show 0 < slowCascade.Ts
      norm_num [slowCascade]
  rw [show implementation.impl = family from rfl, family_isLinear.den_hurwitz hP] at hmem
  rw [(connection_proof% family_isLinear.mem_den_flow)] at hu
  exact hu (holds_of_isHurwitz 0 (P := .locallyExponentiallyStable) trivial hmem).lyapunovStable

/-- A platform stabilized by its delay: design `L = C = 1`, `R = 1/20`, `K_pc = 3`, `K_ic = 4`,
`K_pv = 1/2`, `K_iv = 2`, period `Tₛ = 1/6` (`τ = 1/4`). -/
def delayStabilized : DigitalCascade := ⟨⟨1, 1 / 20, 1, 3, 4, 1 / 2, 2⟩, 1 / 6⟩

/-- The design of `delayStabilized` is unstable: `a₃ a₂ a₁ < a₁² + a₃² a₀`
(`InnerCascade.exists_root_of_unstable`). -/
@[tmio TM, powerlib_domain] theorem delayStabilized_design_mem_den_unstable :
    connection% (delayStabilized.design ∈ InnerCascade.family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% InnerCascade.family_isLinear.mem_den_flow)]
  obtain ⟨s, hs, hre⟩ := InnerCascade.exists_root_of_unstable delayStabilized.design
    (Or.inr (Or.inr (Or.inr (Or.inr (by
      norm_num [delayStabilized, InnerCascade.a3, InnerCascade.a2, InnerCascade.a1,
        InnerCascade.a0])))))
  exact unstable_of_root 0 hs hre

/-- The platform `delayStabilized` satisfies every attractive sentence: its quintic Routh
conditions hold (exact rational arithmetic). -/
@[tmio TM, powerlib_domain] theorem delayStabilized_mem_den {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (delayStabilized ∈ family.den (.flow P)) := by
  have h := mem_den_iff delayStabilized (by norm_num [delayStabilized])
    (by norm_num [delayStabilized]) (by norm_num [delayStabilized]) hP
  unfold powerlib.TMIO.Statement at h ⊢
  refine h.mpr ?_
  show Criteria.QuinticRouth _ _ _ _ _
  norm_num [Criteria.QuinticRouth, Criteria.quinticHurwitzDet2, Criteria.quinticHurwitzDet3,
    Criteria.quinticHurwitzDet4, Criteria.quinticHurwitzDet5, delayStabilized, b5, b4, b3, b2, b1,
    b0, τ]

/-- **The attractive sentences are not realized completely within the physical range and a
positive period**: the delay stabilizes `delayStabilized`, whose design is unstable. -/
@[tmio MI, powerlib_domain] theorem not_realizationCompleteUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (¬ implementation.RealizationCompleteUnder {.physical, .sampling} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hm := delayStabilized_mem_den hP
  have hu := delayStabilized_design_mem_den_unstable
  unfold powerlib.TMIO.Statement at hm hu
  refine Implementation.not_realizationCompleteUnder_of_design (I := implementation) rfl hm ?_
    fun hd => ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · show 0 < delayStabilized.design.L ∧ 0 < delayStabilized.design.C
      norm_num [delayStabilized]
    · show 0 < delayStabilized.Ts
      norm_num [delayStabilized]
  rw [show implementation.model = InnerCascade.family from rfl,
    InnerCascade.family_isLinear.den_hurwitz hP] at hd
  rw [(connection_proof% InnerCascade.family_isLinear.mem_den_flow)] at hu
  exact hu (holds_of_isHurwitz 0 (P := .locallyExponentiallyStable) trivial hd).lyapunovStable

end DigitalCascade

end powerlib.GFM
