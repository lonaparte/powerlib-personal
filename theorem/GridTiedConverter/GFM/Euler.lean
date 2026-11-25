import theorem.GridTiedConverter.GFM.PSC
import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.GridTiedConverter.GFM.VSMLPFRig
import theorem.GridTiedConverter.GFM.VOC
import theorem.GridTiedConverter.GFM.DroopVSM
import theorem.GridTiedConverter.GFM.VSMLPFLossy
import theorem.GridTiedConverter.GFM.QVDroop
import theorem.GridTiedConverter.GFM.DCLink.VSMDC
import theorem.GridTiedConverter.GFM.Line.VSM
import theorem.GridTiedConverter.GFM.Line.VSMLPF
import theorem.GridTiedConverter.GFM.Line.PSC
import theorem.GridTiedConverter.GFM.FullModel.DCWitness
import theorem.PowerSystem.Synchronous.SwingEuler
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the grid-forming families: realizations

The grid-forming families of autonomous fields integrated by the explicit Euler method with a
fixed step `h > 0`: each integration realizes the model it integrates. A locally exponentially
stable model whose field is `C¹` near its point has a step `h₀ > 0` below which its Euler
integration is locally exponentially stable, and without a step constraint the realization is not
sound; instances of the generic template `theorem/Numerics/EulerRealization.lean`, in the pattern
of `theorem/PowerSystem/Synchronous/SwingEuler.lean`. For the open-loop VSM–DC family the
smoothness hypothesis is exact: among its locally exponentially stable models exactly those with
`V* ≠ 0` have a stable step; the collapsing points of its singular plane have none. Scaffold:
`theorem/Numerics/EulerDiscretization.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module, read about its selected
  point (continuous time, autonomous, no input): `GFM.PSC.family` (quasi-static PSC, state `δ`,
  `theorem/GridTiedConverter/GFM/PSC.lean`); `GFM.VSMLPF.family` (VSM + power filter, state
  `(δ, ω, P_f)`) and `GFM.DroopLPF.family` (droop + power filter, state `(δ, P_f)`),
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`; `GFM.VSMLPF.rigFamily` (the VSM + power-filter
  platform with an execution delay, state `(δ, ω, P_f, θ)`,
  `theorem/GridTiedConverter/GFM/VSMLPFRig.lean`, here the model its integration realizes);
  `GFM.AHO.family` (the Andronov–Hopf virtual oscillator about the origin,
  `theorem/GridTiedConverter/GFM/VOC.lean`); `GFM.DroopVSM.vsmFamily` (VSM with an arbitrary power
  map `P`, state `(θ, ω)`) and `GFM.DroopVSM.droopFamily` (droop + LPF with an arbitrary power map,
  state `(θ, P_f)`), `theorem/GridTiedConverter/GFM/DroopVSM.lean`; `GFM.VSMLPFLossy.family`
  (VSM + power filter on a lossy quasi-static line, state `(δ, ω, P_f)`,
  `theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`); `GFM.QVDroop.family` (Q–V droop on a
  quasi-static line, state `(δ, Δω, Q_f)`, `theorem/GridTiedConverter/GFM/QVDroop.lean`);
  `GFM.DCLink.OpenLoop.family` (VSM with a DC link, DC-voltage loop open, state `(δ, ω, V)`,
  `theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean`) and `GFM.DCLink.VSMDC.family` (with the
  DC-voltage PI loop, state `(δ, ω, V, ζ)`, `theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`);
  `GFM.Line.VSM.family`, `GFM.Line.VSMLPF.family`, `GFM.Line.PSC.family` (the source on a dynamic
  R–L line, four, five and three states, `theorem/GridTiedConverter/GFM/Line/VSM.lean`,
  `VSMLPF.lean`, `PSC.lean`); `GFM.FullModel.family` (the 13-state converter with LC filter, line,
  cascaded voltage and current PI loops, VSM and Q–V droop,
  `theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`) and `GFM.FullModel.dcFamily` (its
  16-state DC variant, `theorem/GridTiedConverter/GFM/FullModel/DCSaddle.lean`).
* Implementation layer (I). For each family the integrations `Numerics.EulerStep` of its model type
  (`Euler`; for the platform `RigEuler`, for the DroopVSM families `VSMEuler` and `DroopEuler`,
  for the DC variant `FullModel.DCEuler`): a model and a step `h > 0`; the system is the explicit
  Euler map `z ↦ z + h f(z)` of the model's (translated) field (the DC-link fields with their
  `1/V` term read with Lean's `x / 0 = 0`), with step length `h`, discrete time, exact arithmetic
  (no round-off), fixed step. Excluded: step-size control, implicit or higher-order schemes, the
  integration error against the continuous trajectory.
* Smoothness: the fields of `PSC`, `VSMLPF`, `DroopLPF`, `AHO`, the platform, `VSMLPFLossy`,
  `QVDroop`, the three line models and the 13-state model are `C¹` everywhere (the global laws of
  the template). The DroopVSM families have an arbitrary power map `P`, so their laws carry the
  hypothesis that `P` is `C¹` near the selected angle (`ContDiffAt ℝ 1 P θ*`, the local laws of
  the template; weaker than the requirement `smooth`). The DC-link fields divide by the DC
  voltage and are `C¹` near the selected point when `V* ≠ 0` (`OpenLoop`), `V_dc* ≠ 0` (`VSMDC`),
  `C_dc ≠ 0` and `v_ref ≠ 0` (the DC variant): the local laws, with these hypotheses. The open
  loop has locally exponentially stable selected points on the singular plane `V* = 0`
  (`DCLink.OpenLoop.mem_den_locallyExponentiallyStable_of_collapse`, an estimate that holds
  because solutions reach the plane in finite time), where no Jacobian exists.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`not_eulerStep_realizationSoundUnder` and their `_local` forms, `contDiffAt_shift`,
`contDiff_shift`) and the family modules (autonomy, `C¹` fields, members of local exponential
stability): for the DC link `theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean`
(`Plant.openField_contDiffOn`, `Plant.openField_two_eq_planeQ_div`,
`mem_den_locallyExponentiallyStable_iff_of_V_eq_zero`,
`mem_den_locallyExponentiallyStable_iff_of_invariant`) and
`theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean` (`Params.field_contDiffOn`); for the full
model `theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean`
(`exists_epsStar_mem_den_LES_of_qvDroop`), `Counterexample.lean` (`witness_reduced_mem_den_LES`,
`witness_fastBlock_spectrallyStable`), `DCWitness.lean` (`dcWitness_exists_epsStar_mem_den_LES`)
and `DCSaddle.lean` (`DCParams.contDiffOn_field`); work-sync `theory/T-numerical-integration.md`
§1.2, §2.7.

Results.
* The smoothness hypotheses of the generic laws: for `PSC`, `VSMLPF`, the platform and `DroopLPF`
  the translated fields are `C¹` by `Numerics.contDiff_shift` at the families' `C¹` fields
  (`NormalForm.lift_contDiff`, `VSMLPF.contDiff_field`, `VSMLPF.contDiff_rigField`,
  `DroopLPF.contDiff_field`); for the oscillator the Hopf normal form's
  `NormalForm.Hopf.field_contDiff` at `AHO.toHopf`, `theorem/GridTiedConverter/GFM/VOC.lean`;
  `DroopVSM.vsm_contDiffAt_field`, `DroopVSM.droop_contDiffAt_field` (the translated fields are
  `C¹` near the origin when the power map is `C¹` near the selected angle); for `VSMLPFLossy`,
  `QVDroop` and the 13-state model `Numerics.contDiff_shift` at `VSMLPFLossy.contDiff_field`,
  `QVDroop.contDiff_field`, `FullModel.Params.contDiff_field`; the line models' translated fields
  are `C¹` (`Line.VSM.Model.contDiff_field`, `Line.VSMLPF.Model.contDiff_field`,
  `Line.PSC.Model.contDiff_field`); `DCLink.OpenLoop.contDiffAt_field` (`V* ≠ 0`),
  `DCLink.VSMDC.contDiffAt_field` (`V_dc* ≠ 0`), `FullModel.DCModel.contDiffAt_field`
  (`C_dc ≠ 0`, `v_ref ≠ 0`): the translated field is `C¹` near the origin.

Family and connection conclusions.
* For each family `F` above (`F = PSC, VSMLPF, DroopLPF, AHO, VSMLPFLossy, QVDroop,
  DCLink.OpenLoop, DCLink.VSMDC, Line.VSM, Line.VSMLPF, Line.PSC, FullModel`): `F.eulerFamily`
  (for the platform `VSMLPF.rigEulerFamily`, for the DroopVSM families `DroopVSM.vsmEulerFamily`
  and `DroopVSM.droopEulerFamily`, for the DC variant `FullModel.dcEulerFamily`), every
  integration read as its Euler map, with the requirements and translation of its model read
  through the design; `F.euler` (`VSMLPF.rigEuler`, `DroopVSM.vsmEuler`, `DroopVSM.droopEuler`,
  `FullModel.dcEuler`), every integration realizing its model (`Implementation.ofDesign`).
* M–I (realization), for each family. The small-step laws are the generic connection laws applied
  to the family, with its autonomy (`F.family_isAutonomous`, for the platform
  `VSMLPF.rigFamily_isAutonomous`, for the local spectral families `OpenLoop`, `VSMDC`,
  `FullModel.family` and `FullModel.dcFamily` `Spectral.localFamily_isAutonomous`) and its
  smoothness above: `Numerics.euler_sound_small_step_local` (scaffold `sound-small-step`: a
  locally exponentially stable model has a step `h₀ > 0` such that every Euler integration with a
  step `h ≤ h₀` is locally exponentially stable) and `Numerics.euler_sound_small_step_local`
  (scaffold `certified-small-step`). `F.not_euler_realizationSoundUnder` (scaffold
  `not-sound-large-step`): without a step constraint the realization is not sound — a locally
  exponentially stable member (`PSC.locallyExponentiallyStable`,
  `VSMLPF.mem_den_locallyExponentiallyStable`, `DroopLPF.locallyExponentiallyStable`,
  `AHO.mem_den_locallyExponentiallyStable`, for the platform `VSMLPF.rig_chain_le_semantics` at
  `M = D = ω_c = K₀ = 1`, `τ = 1/2`, `H = 1/2`; `VSMLPFLossy.den_eq_preimage` at the lossless
  member `M = D = ω_c = A = 1`, `P_ref = c₀ = α = 0`; `FullModel.witness_reduced_mem_den_LES` for
  `QVDroop`; the rectifying open loop `M = D = C = A = 1`, `c₀ = P_ff = −1`, `I_s = −1`, `P_s = 0`
  at `(0, 0, 1)`; the exporting `VSMDC` model `M = 1/4`, `D = 1/2`,
  `C = V* = c₀ = A = P_ff = I_s = 1`, `P_s = 0`, `K_p = 5/4`, `K_i = 1/8`, whose plant without the
  DC loop is the unstable export case of `DCLink.OpenLoop.mem_den_unstable_of_export`;
  `Line.VSM.highDamping_stable`,
  `Line.VSMLPF.highDamping_stable`, `Line.PSC.lowGain_stable`; the time-scaled 13-state witness
  at `ε = ε*/2` of `exists_epsStar_mem_den_LES_of_qvDroop`, and for the DC variant
  `FullModel.dc_not_euler_realizationSoundUnder` with the time-scaled DC witness of
  `FullModel.dcWitness_exists_epsStar_mem_den_LES`) has Euler integrations with every multiplier
  outside the unit disk. The platform's statements carry the prefix `rig_`.
* M–I for the DroopVSM families, with a power map `C¹` near the selected angle: the small-step
  laws are the local generic laws `Numerics.euler_sound_small_step_local` applied with
  `DroopVSM.vsmFamily_isAutonomous`, `DroopVSM.droopFamily_isAutonomous` and the smoothness lemmas
  `DroopVSM.vsm_contDiffAt_field`, `DroopVSM.droop_contDiffAt_field`;
  `DroopVSM.vsm_not_euler_realizationSoundUnder` (witness `vsm_mem_den_locallyExponentiallyStable`
  with `P(θ) = θ`, `M = D = 1`, `P_ref = ω_s = 0` at the origin) and
  `DroopVSM.droop_not_euler_realizationSoundUnder` (witness
  `infiniteBus_locallyExponentiallyStable` with `P = sin`, `K_R = τ_p = 1`, `P_ref = ω_s = 0` at
  the origin).
* The open-loop VSM–DC family on its singular plane:
  `DCLink.OpenLoop.euler_not_mem_den_locallyExponentiallyStable_of_V_eq_zero` — at a selected
  point with `V* = 0` and `a = (P_s − P_e(δ*))/C ≠ 0` no Euler integration, at any step `h > 0`, is
  locally exponentially stable: one step from `(δ*, 0, v)` lands at
  `v + h (I_s/C + a/v)` (`Plant.openField_two_eq_planeQ_div`), unbounded as `v → 0`, while the
  exponential estimate bounds it by a multiple of `|v|`.
  `DCLink.OpenLoop.euler_sound_small_step_iff` — a locally exponentially stable model has a step
  `h₀ > 0` below which its integrations are locally exponentially stable iff `V* ≠ 0`: for
  `V* ≠ 0` the small-step law, for `V* = 0` local exponential stability forces `a < 0`
  (`mem_den_locallyExponentiallyStable_iff_of_V_eq_zero`,
  `mem_den_locallyExponentiallyStable_iff_of_invariant`) and no step is stable. The smoothness
  hypothesis of the small-step law is thus exact for this family: the collapsing points
  (`mem_den_locallyExponentiallyStable_of_collapse`) are locally exponentially stable models whose
  realization fails at every step.
-/

noncomputable section

namespace powerlib.GFM.PSC

/-- The explicit Euler integration of a PSC model about its selected angle with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 1 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its PSC model. -/
def euler : Implementation Model Requirement Euler Requirement 1 0 1 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the PSC models is not sound.** A locally
exponentially stable PSC model (`K_p = P_max = 1`, `P* = 0` at `δ* = 0`) integrated with a large
enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := PSC.locallyExponentiallyStable ⟨1, 0, 1⟩ one_pos one_pos (δ₀ := 0) (by simp) (by simp)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift (NormalForm.lift_contDiff m.c.rhs_contDiff)) (by norm_num) hm

end powerlib.GFM.PSC

namespace powerlib.GFM.VSMLPF

/-- The explicit Euler integration of a VSM + power-filter model about its selected point with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 3 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its VSM + power-filter model. -/
def euler : Implementation Model Requirement Euler Requirement 3 0 3 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the VSM + power-filter models is not
sound.** A locally exponentially stable model (`M = D = ω_c = K₀ = 1`, `P₀ = 0` at `δ* = 0`:
`K = 1 < D ω_c + D²/M = 2`) integrated with a large enough step is not locally exponentially stable:
every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨⟨1, 1, 1, 0, 1⟩, 0⟩ one_pos one_pos one_pos
      (by simp) (by norm_num [Model.K]) (by norm_num [Model.K])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift m.g.contDiff_field) (by norm_num) hm

/-- The explicit Euler integration of a platform model about its operating point with step
`h > 0`. -/
abbrev RigEuler := Numerics.EulerStep Rig

/-- The Euler integration family: every integration read as the Euler map of its model's translated
platform field, with step length its step. -/
def rigEulerFamily : Family RigEuler RigRequirement 4 0 :=
  Numerics.eulerFamily rigFamily Rig.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its platform model. -/
def rigEuler : Implementation Rig RigRequirement RigEuler RigRequirement 4 0 4 0 :=
  Numerics.euler rigFamily Rig.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the platform models is not sound.** A
locally exponentially stable platform (design `M = D = ω_c = K₀ = 1`, `P₀ = δ* = 0`, delay
`τ = 1/2`, so `H = 1/2 > 0`) integrated with a large enough step is not locally exponentially
stable: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem rig_not_euler_realizationSoundUnder :
    connection% (¬ rigEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hc := rig_chain_le_semantics
  unfold powerlib.TMIO.Statement at hc
  have hm : (⟨⟨⟨1, 1, 1, 0, 1⟩, 0⟩, 1 / 2⟩ : Rig) ∈
      rigFamily.den (.flow .locallyExponentiallyStable) := by
    refine Family.chain_le_semantics_iff.mp hc _ ((TMIO.mem_realize _ _ _).mpr ?_)
    simp only [rigFamily, rigTranslate, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro q (rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [RigMeets, Meets, Rig.H, Rig.b, Rig.c, Model.K]
  exact Numerics.not_eulerStep_realizationSoundUnder rigFamily_isAutonomous
    (fun m => Numerics.contDiff_shift (contDiff_rigField m)) (by norm_num) hm

end powerlib.GFM.VSMLPF

namespace powerlib.GFM.DroopLPF

/-- The explicit Euler integration of a droop + LPF model about its selected point with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its droop + LPF model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the droop + LPF models is not sound.** A
locally exponentially stable model (`D = ω_c = K₀ = 1`, `P₀ = 0` at its loading angle) integrated
with a large enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves
the unit disk (`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := DroopLPF.locallyExponentiallyStable ⟨1, 1, 0, 1⟩ one_pos one_pos one_pos (by norm_num)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift m.q.contDiff_field) (by norm_num) hm

end powerlib.GFM.DroopLPF

namespace powerlib.GFM.AHO

/-- The explicit Euler integration of a virtual-oscillator model about the origin with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep AHO

/-- The Euler integration family: every integration read as the Euler map of its model's field, with
step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family AHO.realField Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its virtual-oscillator model. -/
def euler : Implementation AHO Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family AHO.realField Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the virtual-oscillator models is not
sound.** A locally exponentially stable oscillator (`ω_s = σ = κ_v = 1`, `v* = 0`:
`c = κ_v v*² − σ < 0`) integrated with a large enough step is not locally exponentially stable:
every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨1, 1, 1, 0⟩ (by norm_num [AHO.c])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun a => NormalForm.Hopf.field_contDiff a.toHopf) (by norm_num) hm

end powerlib.GFM.AHO

namespace powerlib.GFM.DroopVSM

open powerlib.Dynamics (State)

/-- The explicit Euler integration of a VSM model about its selected state with step `h > 0`. -/
abbrev VSMEuler := Numerics.EulerStep VSMModel

/-- The Euler integration family of the VSM models: every integration read as the Euler map of its
model's translated field, with step length its step. -/
def vsmEulerFamily : Family VSMEuler VSMRequirement 2 0 :=
  Numerics.eulerFamily vsmFamily VSMModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization of the VSM models: every integration realizes its VSM model. -/
def vsmEuler : Implementation VSMModel VSMRequirement VSMEuler VSMRequirement 2 0 2 0 :=
  Numerics.euler vsmFamily VSMModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated VSM field is `C¹` near the origin when the power map is `C¹` near the selected
angle: the smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`); the field is its swing image's
(`VSMModel.field_eq_toSwing`, `Synchronous.GeneralSwing.contDiffAt_field`). -/
@[tmio M, powerlib_domain] theorem vsm_contDiffAt_field {m : VSMModel}
    (hs : ContDiffAt ℝ 1 m.P (m.point 0)) :
    ContDiffAt ℝ 1 m.field 0 := by
  rw [m.field_eq_toSwing]
  exact Synchronous.GeneralSwing.contDiffAt_field (hs.comp (m.point 0, m.point 1) contDiffAt_fst)

/-- **Without a step constraint the Euler realization of the VSM models is not sound.** A locally
exponentially stable VSM model (`P(θ) = θ`, `M = D = 1`, `P_ref = ω_s = 0` at the origin)
integrated with a large enough step is not locally exponentially stable: every Euler multiplier
`1 + hλ` leaves the unit disk (`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem vsm_not_euler_realizationSoundUnder :
    connection% (¬ vsmEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := vsm_mem_den_locallyExponentiallyStable ⟨1, 1, 0, 0, fun θ => θ, 0⟩ contDiff_id
    (by simp) (by simp) one_pos one_pos (by simp)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder_local vsmFamily_isAutonomous
    (by norm_num) (vsm_contDiffAt_field contDiff_id.contDiffAt) hm

/-- The explicit Euler integration of a droop + LPF model about its selected state with step
`h > 0`. -/
abbrev DroopEuler := Numerics.EulerStep DroopModel

/-- The Euler integration family of the droop + LPF models: every integration read as the Euler
map of its model's translated field, with step length its step. -/
def droopEulerFamily : Family DroopEuler VSMRequirement 2 0 :=
  Numerics.eulerFamily droopFamily DroopModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization of the droop + LPF models: every integration realizes its model. -/
def droopEuler : Implementation DroopModel VSMRequirement DroopEuler VSMRequirement 2 0 2 0 :=
  Numerics.euler droopFamily DroopModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated droop + LPF field is `C¹` near the origin when the power map is `C¹` near the
selected angle: the smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem droop_contDiffAt_field {m : DroopModel}
    (hs : ContDiffAt ℝ 1 m.d.P (m.point 0)) :
    ContDiffAt ℝ 1 m.field 0 := by
  refine Numerics.contDiffAt_shift (g := m.d.droopField) (x₀ := m.point) ?_
  have hP : ContDiffAt ℝ 1 (fun x : State 2 => m.d.P (x 0)) m.point :=
    hs.comp (f := fun x : State 2 => x 0) m.point (Dynamics.contDiff_coord 0).contDiffAt
  rw [contDiffAt_euclidean]
  intro i
  fin_cases i
  · simp only [droopField, Fin.zero_eta, Fin.isValue, PhasePlane.mk_apply_zero]
    exact contDiffAt_const.sub
      (((Dynamics.contDiff_coord 1).contDiffAt.sub contDiffAt_const).div_const _)
  · simp only [droopField, Fin.mk_one, Fin.isValue, PhasePlane.mk_apply_one]
    exact (hP.sub (Dynamics.contDiff_coord 1).contDiffAt).div_const _

/-- **Without a step constraint the Euler realization of the droop + LPF models is not sound.** A
locally exponentially stable model on an infinite bus (`P = sin`, `K_R = τ_p = 1`,
`P_ref = ω_s = 0` at the origin, `infiniteBus_locallyExponentiallyStable`) integrated with a large
enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem droop_not_euler_realizationSoundUnder :
    connection% (¬ droopEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := infiniteBus_locallyExponentiallyStable
    ⟨⟨1, 1, 0, 0, fun θ => 1 * Real.sin θ⟩, one_ne_zero, one_ne_zero, 0⟩ 1 rfl one_pos one_pos
    (by simp [droopField]) (by simp)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder_local droopFamily_isAutonomous
    (by norm_num) (droop_contDiffAt_field (contDiff_const.mul Real.contDiff_sin).contDiffAt) hm

end powerlib.GFM.DroopVSM

namespace powerlib.GFM.VSMLPFLossy

/-- The explicit Euler integration of a VSM + power-filter model on a lossy line about its
selected point with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler VSMLPF.Requirement 3 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its lossy VSM + power-filter model. -/
def euler : Implementation Model VSMLPF.Requirement Euler VSMLPF.Requirement 3 0 3 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the lossy VSM + power-filter models is
not sound.** The lossy model with `M = D = ω_c = A = 1`, `P_ref = c₀ = α = 0` at `δ* = 0` reads as
the locally exponentially stable lossless model `M = D = ω_c = K₀ = 1`, `P₀ = 0`
(`den_eq_preimage`); integrated with a large enough step it is not locally exponentially stable:
every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hv := VSMLPF.mem_den_locallyExponentiallyStable ⟨⟨1, 1, 1, 0, 1⟩, 0⟩ one_pos one_pos
    one_pos (by simp) (by norm_num [VSMLPF.Model.K]) (by norm_num [VSMLPF.Model.K])
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hv hd
  have hm : (⟨⟨1, 1, 1, 0, 0, 1, 0⟩, 0⟩ : Model) ∈
      family.den (.flow .locallyExponentiallyStable) := by
    rw [hd, Set.mem_preimage]
    convert hv using 1
    simp [Model.toVSMLPF, toVSMLPF]
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift m.p.contDiff_field) (by norm_num) hm

end powerlib.GFM.VSMLPFLossy

namespace powerlib.GFM.QVDroop

/-- The explicit Euler integration of a Q–V droop model about its selected point with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 3 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its Q–V droop model. -/
def euler : Implementation Model Spectral.Requirement Euler Spectral.Requirement 3 0 3 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the Q–V droop models is not sound.** The
reduced Q–V droop model of the 13-state witness (`M = D = 1/10`, `ω_q = 1`, `E₀ = 2`, no droop, at
`(0, 0, 2)`, `FullModel.witness_reduced_mem_den_LES`) is locally exponentially stable; integrated
with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := FullModel.witness_reduced_mem_den_LES
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift m.q.contDiff_field) (by norm_num) hm

end powerlib.GFM.QVDroop

namespace powerlib.GFM.DCLink.OpenLoop

open powerlib.Dynamics (mk3)

/-- The explicit Euler integration of an open-loop VSM–DC model about its selected point with
step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field (with its `1/V` term), with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 3 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its open-loop VSM–DC model. -/
def euler : Implementation Model Spectral.Requirement Euler Spectral.Requirement 3 0 3 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated field is `C¹` near the origin when the selected DC voltage is nonzero: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_field {m : Model} (hV : m.V ≠ 0) :
    ContDiffAt ℝ 1 m.field 0 :=
  Numerics.contDiffAt_shift (g := m.q.openField) (x₀ := m.point)
    (m.q.openField_contDiffOn.contDiffAt
      ((isOpen_nonzeroDC 2).mem_nhds (by simpa [Model.point, nonzeroDC] using hV)))

/-- **Without a step constraint the Euler realization of the open-loop VSM–DC models is not
sound.** A rectifying converter (`M = D = C = A = 1`, `c₀ = P_ff = −1`, a constant-current DC
load `P_s = 0`, `I_s = −1`, at `(δ*, V*) = (0, 1)`: `P_e(0) = −1` imported, DC pole `b = −1`) is
locally exponentially stable; integrated with a large enough step it is not: every Euler
multiplier `1 + hλ` leaves the unit disk (`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨⟨1, 1, 1, -1, -1, 1, 0, 0, -1⟩, 0, 1⟩
    ⟨one_ne_zero, ⟨by norm_num [Plant.Pe], by norm_num [Plant.Psrc, Plant.Pe]⟩, by norm_num,
      by norm_num [Plant.k], by norm_num [Model.b]⟩
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder_local
    (Spectral.localFamily_isAutonomous _ _ _ : family.IsAutonomous Model.field)
    (by norm_num) (contDiffAt_field one_ne_zero) hm

/-- One Euler step from `(δ*, 0, v)` of a model read on the singular plane: its DC coordinate is
`v + h (I_s/C + (P_s − P_e(δ*))/(C v))` (`Plant.openField_two_eq_planeQ_div`). -/
@[tmio M, powerlib_domain] private theorem eulerMap_two {m : Model} (hV : m.V = 0) (h : ℝ)
    {v : ℝ} (hv : v ≠ 0) :
    Numerics.eulerMap m.field h (EuclideanSpace.single 2 v) 2 =
      v + h * (m.q.Is / m.q.C + (m.q.Ps - m.q.Pe m.δ) / m.q.C / v) := by
  have hy : EuclideanSpace.single (2 : Fin 3) v + m.point = mk3 m.δ 0 v := by
    apply Dynamics.state3_ext <;> simp [Model.point, hV]
  simp only [Numerics.eulerMap, Model.field, hy, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [m.q.openField_two_eq_planeQ_div (by simpa using hv)]
  simp only [Plant.planeQ, Dynamics.mk3_zero, Dynamics.mk3_two]
  rw [show (EuclideanSpace.single (2 : Fin 3) v).ofLp 2 = v by simp]
  by_cases hC : m.q.C = 0
  · simp [hC]
  · field_simp
    ring

/-- **On the singular plane no Euler step is stable.** At a selected point with `V* = 0` and a
nonzero power term `a = (P_s − P_e(δ*))/C ≠ 0`, no Euler integration, whatever its step `h > 0`, is
locally exponentially stable: one step from `(δ*, 0, v)` lands at `v + h (I_s/C + a/v)`, whose
size `≥ h |a|/v − v − h |I_s/C|` is unbounded as `v → 0`, while the exponential estimate bounds it
by a multiple of `v`. -/
@[tmio TM, powerlib_domain] theorem euler_not_mem_den_locallyExponentiallyStable_of_V_eq_zero
    {m : Model} (hV : m.V = 0) (ha : (m.q.Ps - m.q.Pe m.δ) / m.q.C ≠ 0) (y : Euler)
    (hy : y.design = m) :
    connection% (y ∉ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro hmem
  have hmap := (connection_proof% (Numerics.eulerFamily_isAutonomousMap family Model.field
    Numerics.EulerStep.design Numerics.EulerStep.h).mem_den_flow).mp hmem
  rw [hy] at hmap
  obtain ⟨r, K, ρ, hr, hK, hρ0, hρ1, hb⟩ := hmap
  set a := (m.q.Ps - m.q.Pe m.δ) / m.q.C
  set b := m.q.Is / m.q.C
  have hh : 0 < y.h := y.pos
  have hapos : 0 < |a| := abs_pos.mpr ha
  set L := K + 1 + y.h * |b|
  have hL1 : 1 ≤ L := by have := abs_nonneg b; nlinarith
  set v := min (r / 2) (min 1 (y.h * |a| / (2 * L)))
  have hv0 : 0 < v := lt_min (half_pos hr) (lt_min one_pos (by positivity))
  have hvr : v < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  have hv1 : v ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hva : v ≤ y.h * |a| / (2 * L) := le_trans (min_le_right _ _) (min_le_right _ _)
  have key := hb (EuclideanSpace.single 2 v) (by simpa [abs_of_pos hv0] using hvr) 1
  simp only [Function.iterate_one, sub_zero, pow_one] at key
  have hcomp := PiLp.norm_apply_le (Numerics.eulerMap m.field y.h (EuclideanSpace.single 2 v)) 2
  rw [eulerMap_two hV y.h hv0.ne'] at hcomp
  have hnorm : ‖EuclideanSpace.single (2 : Fin 3) v‖ = v := by simp [abs_of_pos hv0]
  rw [hnorm] at key
  have hw : |v + y.h * (b + a / v)| ≤ K := by
    have h1 : K * ρ * v ≤ K := by
      have : ρ * v ≤ 1 := by nlinarith
      nlinarith
    rw [← Real.norm_eq_abs]
    linarith
  have hav : |y.h * (a / v)| = y.h * |a| / v := by
    rw [abs_mul, abs_div, abs_of_pos hh, abs_of_pos hv0, mul_div_assoc]
  have htri : |y.h * (a / v)| ≤ |v + y.h * (b + a / v)| + v + y.h * |b| := by
    have e : y.h * (a / v) = (v + y.h * (b + a / v)) - v - y.h * b := by ring
    rw [e]
    calc |(v + y.h * (b + a / v)) - v - y.h * b|
        ≤ |(v + y.h * (b + a / v)) - v| + |y.h * b| := abs_sub _ _
      _ ≤ |v + y.h * (b + a / v)| + |v| + |y.h * b| := by gcongr; exact abs_sub _ _
      _ = |v + y.h * (b + a / v)| + v + y.h * |b| := by
          rw [abs_of_pos hv0, abs_mul, abs_of_pos hh]
  have hbig : 2 * L ≤ y.h * |a| / v := by
    rw [le_div_iff₀ hv0]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mp hva
    linarith
  have : y.h * |a| / v ≤ L := by
    rw [← hav]
    linarith
  linarith

/-- **The small-step realization of the open loop holds exactly off the singular plane.** A
locally exponentially stable open-loop model has a step `h₀ > 0` below which every Euler
integration of it is locally exponentially stable iff `V* ≠ 0`. For `V* ≠ 0` this is the
small-step law `Numerics.euler_sound_small_step_local` with `contDiffAt_field`; for `V* = 0`
local exponential stability forces `(P_s − P_e(δ*))/C < 0`
(`mem_den_locallyExponentiallyStable_iff_of_V_eq_zero`,
`mem_den_locallyExponentiallyStable_iff_of_invariant`), and then no step is stable
(`euler_not_mem_den_locallyExponentiallyStable_of_V_eq_zero`). -/
@[tmio MI, powerlib_domain] theorem euler_sound_small_step_iff {m : Model}
    (hm : m ∈ family.den (.flow .locallyExponentiallyStable)) :
    connection% ((∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y : Euler, y.design = m → y.h ∈ Set.Ioc (0 : ℝ) h₀ →
      y ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) ↔ m.V ≠ 0) := by
  unfold powerlib.TMIO.Statement
  constructor
  · rintro ⟨h₀, hh₀, hS⟩ hV
    have ha : (m.q.Ps - m.q.Pe m.δ) / m.q.C < 0 := by
      by_cases hI : m.q.Is / m.q.C = 0
      · have h := mem_den_locallyExponentiallyStable_iff_of_invariant m hV hI
        unfold powerlib.TMIO.Statement at h
        exact (h.mp hm).1
      · have h := mem_den_locallyExponentiallyStable_iff_of_V_eq_zero m hV hI
        unfold powerlib.TMIO.Statement at h
        exact h.mp hm
    have hn := euler_not_mem_den_locallyExponentiallyStable_of_V_eq_zero hV ha.ne ⟨m, h₀, hh₀⟩ rfl
    unfold powerlib.TMIO.Statement at hn
    exact hn (hS _ rfl ⟨hh₀, le_rfl⟩)
  · intro hV
    have h := Numerics.euler_sound_small_step_local (design := Numerics.EulerStep.design)
      (step := Numerics.EulerStep.h)
      (Spectral.localFamily_isAutonomous _ _ _ : family.IsAutonomous Model.field)
      (contDiffAt_field hV) hm
    unfold powerlib.TMIO.Statement at h
    exact h

end powerlib.GFM.DCLink.OpenLoop

namespace powerlib.GFM.DCLink.VSMDC

/-- The explicit Euler integration of a VSM–DC model with its DC-voltage loop about its selected
point with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field (with its `1/V` term), with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 4 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its VSM–DC model. -/
def euler : Implementation Model Spectral.Requirement Euler Spectral.Requirement 4 0 4 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated field is `C¹` near the origin when the DC-voltage reference is nonzero: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_field {m : Model} (hV : m.p.Vref ≠ 0) :
    ContDiffAt ℝ 1 m.field 0 :=
  Numerics.contDiffAt_shift (g := m.p.field) (x₀ := m.point)
    (m.p.field_contDiffOn.contDiffAt
      ((isOpen_nonzeroDC 2).mem_nhds (by simpa [Model.point, nonzeroDC] using hV)))

/-- **Without a step constraint the Euler realization of the VSM–DC models is not sound.** An
exporting converter on a constant-current source (`M = 1/4`, `D = 1/2`,
`C = V* = c₀ = A = P_ff = I_s = 1`, `P_s = 0`, at `δ* = ζ* = 0`: `P_e = 1`, DC pole `b = 1`, the
unstable export case of `DCLink.OpenLoop.mem_den_unstable_of_export` without the DC loop) with
the gains `K_p = 5/4`, `K_i = 1/8` (`a₃ = a₁ = 1`, `a₂ = 2`,
`a₀ = 1/2`) is locally exponentially stable; integrated with a large enough step it is not: every
Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable
    ⟨⟨⟨1 / 4, 1 / 2, 1, 1, 1, 1, 0, 0, 1⟩, 1, 5 / 4, 1 / 8⟩, 0, 0⟩
    ⟨one_ne_zero, ⟨by norm_num [Plant.Pe], by norm_num [Plant.Psrc, Plant.Pe]⟩,
      by norm_num [Model.a3, Model.b],
      by norm_num [Model.a1, Model.b, Model.k, Plant.k],
      by norm_num [Model.a0, Model.k, Plant.k],
      by norm_num [Model.a0, Model.a1, Model.a2, Model.a3, Model.b, Model.k, Plant.k]⟩
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder_local
    (Spectral.localFamily_isAutonomous _ _ _ : family.IsAutonomous Model.field)
    (by norm_num) (contDiffAt_field one_ne_zero) hm

end powerlib.GFM.DCLink.VSMDC

namespace powerlib.GFM.Line.VSM

/-- The explicit Euler integration of a VSM on the dynamic line about its operating point with
step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its VSM-on-line model. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the VSM-on-line models is not sound.**
The lossy witness at `D = 1` (`highDamping_stable`) is locally exponentially stable; integrated
with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := highDamping_stable
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous Model.contDiff_field
    (by norm_num) hm

end powerlib.GFM.Line.VSM

namespace powerlib.GFM.Line.VSMLPF

/-- The explicit Euler integration of a VSM + power filter on the dynamic line about its operating
point with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 5 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its model. -/
def euler : Implementation Model Requirement Euler Requirement 5 0 5 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the VSM + power-filter models on the line
is not sound.** The lossy witness at `D = ω_c = 1` (`highDamping_stable`) is locally exponentially
stable; integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the
unit disk (`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := highDamping_stable
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous Model.contDiff_field
    (by norm_num) hm

end powerlib.GFM.Line.VSMLPF

namespace powerlib.GFM.Line.PSC

/-- The explicit Euler integration of power-synchronization control on the dynamic line about its
operating point with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 3 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its PSC-on-line model. -/
def euler : Implementation Model Requirement Euler Requirement 3 0 3 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the PSC-on-line models is not sound.** The
lossy witness at `K_p = 1` below the critical gain (`lowGain_stable`) is locally exponentially
stable; integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the
unit disk (`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := lowGain_stable
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous Model.contDiff_field
    (by norm_num) hm

end powerlib.GFM.Line.PSC

namespace powerlib.GFM.FullModel

open powerlib.Dynamics (State)

/-- The explicit Euler integration of a 13-state model about its selected quasi-steady point with
step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 13 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its 13-state model. -/
def euler : Implementation Model Spectral.Requirement Euler Spectral.Requirement 13 0 13 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the 13-state models is not sound.** The
13-state witness time-scaled by `ε = ε*/2` (`exists_epsStar_mem_den_LES_of_qvDroop`: its reduced
Q–V droop model and its boundary layer are stable, `witness_reduced_mem_den_LES`,
`witness_fastBlock_spectrallyStable`) is locally exponentially stable; integrated with a large
enough step it is not: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := exists_epsStar_mem_den_LES_of_qvDroop witnessModel
    (by norm_num [witnessModel, witness]) (by norm_num [witnessModel, witness])
    (by norm_num [witnessModel, witness]) (by norm_num [witnessModel, witness])
    (by norm_num [witnessModel, witness]) witness_Zv
    (by rw [show witnessModel.p.Zg = witness.Zg from rfl, witness_Zg]; exact Complex.I_ne_zero)
    (by norm_num [witnessModel, witness]) (by norm_num [witnessModel, witness])
    witness_reduced_mem_den_LES witness_fastBlock_spectrallyStable
  unfold powerlib.TMIO.Statement at h
  obtain ⟨εs, hεs, hε⟩ := h
  exact Numerics.not_eulerStep_realizationSoundUnder
    (Spectral.localFamily_isAutonomous _ _ _ : family.IsAutonomous Model.field)
    (fun m => Numerics.contDiff_shift m.p.contDiff_field) (by norm_num)
    (hε _ (half_pos hεs) (half_lt_self hεs))

/-- The explicit Euler integration of a 16-state DC-variant model about its selected quasi-steady
point with step `h > 0`. -/
abbrev DCEuler := Numerics.EulerStep DCModel

/-- The Euler integration family of the DC variant: every integration read as the Euler map of its
model's translated field (with its `1/v_dc` term), with step length its step. -/
def dcEulerFamily : Family DCEuler Spectral.Requirement 16 0 :=
  Numerics.eulerFamily dcFamily DCModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization of the DC variant: every integration realizes its model. -/
def dcEuler : Implementation DCModel Spectral.Requirement DCEuler Spectral.Requirement 16 0 16 0 :=
  Numerics.euler dcFamily DCModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated DC-variant field is `C¹` near the origin when `C_dc ≠ 0` and `v_ref ≠ 0` (the
selected point has `v_dc = v_ref`, `DCParams.contDiffOn_field`): the smoothness hypothesis of the
local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem DCModel.contDiffAt_field {m : DCModel} (hC : m.q.Cdc ≠ 0)
    (hv : m.q.vref ≠ 0) : ContDiffAt ℝ 1 m.field 0 := by
  have hU : IsOpen {x : State 16 | x 13 ≠ 0} :=
    isOpen_ne_fun (Dynamics.contDiff_coord (k := 1) 13).continuous continuous_const
  refine Numerics.contDiffAt_shift (g := m.q.field) (x₀ := m.point)
    ((m.q.contDiffOn_field hC).contDiffAt (hU.mem_nhds ?_))
  show m.q.graph _ 13 ≠ 0
  rw [DCParams.graph_13]
  simpa [DCParams.slowPoint] using hv

/-- **Without a step constraint the Euler realization of the DC variant is not sound.** The DC
witness time-scaled by `ε = ε*/2` (`dcWitness_exists_epsStar_mem_den_LES`, `C_dc = v_ref = 1`) is
locally exponentially stable; integrated with a large enough step it is not: every Euler
multiplier `1 + hλ` leaves the unit disk (`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem dc_not_euler_realizationSoundUnder :
    connection% (¬ dcEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := dcWitness_exists_epsStar_mem_den_LES
  unfold powerlib.TMIO.Statement at h
  obtain ⟨εs, hεs, hε⟩ := h
  exact Numerics.not_eulerStep_realizationSoundUnder_local
    (Spectral.localFamily_isAutonomous _ _ _ : dcFamily.IsAutonomous DCModel.field) (by norm_num)
    (DCModel.contDiffAt_field (m := dcWitnessModel.timeScaled (εs / 2))
      (by norm_num [DCModel.timeScaled, DCParams.timeScaled, dcWitnessModel, dcWitness])
      (by norm_num [DCModel.timeScaled, DCParams.timeScaled, dcWitnessModel, dcWitness]))
    (hε _ (half_pos hεs) (half_lt_self hεs))

end powerlib.GFM.FullModel
