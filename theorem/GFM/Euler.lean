import theorem.GFM.PSC
import theorem.GFM.VSMLPF
import theorem.GFM.VSMLPFRig
import theorem.GFM.VOC
import theorem.GFM.DroopVSM
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the grid-forming families: realizations

The grid-forming families of autonomous fields integrated by the explicit Euler method with a
fixed step `h > 0`: each integration realizes the model it integrates. A locally exponentially
stable model whose field is `C¹` near its point has a step `h₀ > 0` below which its Euler
integration is locally exponentially stable, and without a step constraint the realization is not
sound; instances of the generic template `theorem/Numerics/EulerRealization.lean`, in the pattern
of `theorem/Synchronous/SwingEuler.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module, read about its selected
  point (continuous time, autonomous, no input): `GFM.PSC.family` (quasi-static PSC, state `δ`,
  `theorem/GFM/PSC.lean`); `GFM.VSMLPF.family` (VSM + power filter, state `(δ, ω, P_f)`) and
  `GFM.DroopLPF.family` (droop + power filter, state `(δ, P_f)`), `theorem/GFM/VSMLPF.lean`;
  `GFM.VSMLPF.rigFamily` (the VSM + power-filter platform with an execution delay, state
  `(δ, ω, P_f, θ)`, `theorem/GFM/VSMLPFRig.lean`, here the model its integration realizes);
  `GFM.AHO.family` (the Andronov–Hopf virtual oscillator about the origin, `theorem/GFM/VOC.lean`);
  `GFM.DroopVSM.vsmFamily` (VSM with an arbitrary power map `P`, state `(θ, ω)`) and
  `GFM.DroopVSM.droopFamily` (droop + LPF with an arbitrary power map, state `(θ, P_f)`),
  `theorem/GFM/DroopVSM.lean`.
* Implementation layer (I). For each family a structure (`Euler`; for the platform `RigEuler`,
  for the DroopVSM families `VSMEuler` and `DroopEuler`) of a model and a step `h > 0`; the system
  is the explicit Euler map `z ↦ z + h f(z)` of the model's (translated) field, with step length
  `h`, discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control,
  implicit or higher-order schemes, the integration error against the continuous trajectory.
* Smoothness: the fields of `PSC`, `VSMLPF`, `DroopLPF`, `AHO` and the platform are `C¹`
  everywhere (the global laws of the template). The DroopVSM families have an arbitrary power map
  `P`, so their laws carry the hypothesis that `P` is `C¹` near the selected angle
  (`ContDiffAt ℝ 1 P θ*`, the local laws of the template; weaker than the requirement `smooth`).
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step` and their `_local`
forms, `contDiffAt_shift`) and the family modules (autonomy, `C¹` fields, members of local
exponential stability); work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* The smoothness hypotheses of the generic laws, one per family: `PSC.contDiff_modelField`,
  `VSMLPF.contDiff_modelField`, `VSMLPF.rig_contDiff_field`, `DroopLPF.contDiff_modelField` (the
  translated fields are `C¹`; `AHO.contDiff_realField` of `theorem/GFM/VOC.lean` for the
  oscillator), `DroopVSM.vsm_contDiffAt_field`, `DroopVSM.droop_contDiffAt_field` (the translated
  fields are `C¹` near the origin when the power map is `C¹` near the selected angle).

Family and connection conclusions.
* For each family `F` above (`F = PSC, VSMLPF, DroopLPF, AHO`): `F.eulerFamily` (for the platform
  `VSMLPF.rigEulerFamily`, for the DroopVSM families `DroopVSM.vsmEulerFamily` and
  `DroopVSM.droopEulerFamily`), every integration read as its Euler map, with the requirements and
  translation of its model read through the design; `F.euler` (`VSMLPF.rigEuler`,
  `DroopVSM.vsmEuler`, `DroopVSM.droopEuler`), every integration realizing its model
  (`Implementation.ofDesign`).
* M–I (realization), for each family. The small-step laws are the generic connection laws applied
  to the family, with its autonomy (`F.family_isAutonomous`, for the platform
  `VSMLPF.rigFamily_isAutonomous`) and its public smoothness lemma above:
  `Numerics.euler_sound_small_step` (scaffold `sound-small-step`: a locally exponentially stable
  model has a step `h₀ > 0` such that every Euler integration with a step `h ≤ h₀` is locally
  exponentially stable) and `Numerics.euler_certified_small_step` (scaffold
  `certified-small-step`). `F.not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — a locally exponentially stable member
  (`PSC.locallyExponentiallyStable`, `VSMLPF.mem_den_locallyExponentiallyStable`,
  `DroopLPF.locallyExponentiallyStable`, `AHO.mem_den_locallyExponentiallyStable`, for the
  platform `VSMLPF.rig_chain_le_semantics` at `M = D = ω_c = K₀ = 1`, `τ = 1/2`, `H = 1/2`) has
  Euler integrations with every multiplier outside the unit disk. The platform's statements carry
  the prefix `rig_`.
* M–I for the DroopVSM families, with a power map `C¹` near the selected angle: the small-step
  laws are the local generic laws `Numerics.euler_sound_small_step_local` and
  `Numerics.euler_certified_small_step_local` applied with `DroopVSM.vsmFamily_isAutonomous`,
  `DroopVSM.droopFamily_isAutonomous` and the smoothness lemmas `DroopVSM.vsm_contDiffAt_field`,
  `DroopVSM.droop_contDiffAt_field`; `DroopVSM.vsm_not_euler_realizationSoundUnder` (witness
  `vsm_mem_den_locallyExponentiallyStable` with `P(θ) = θ`, `M = D = 1`, `P_ref = ω_s = 0` at the
  origin) and `DroopVSM.droop_not_euler_realizationSoundUnder` (witness
  `infiniteBus_locallyExponentiallyStable` with `P = sin`, `K_R = τ_p = 1`, `P_ref = ω_s = 0` at the
  origin).
-/

noncomputable section

namespace powerlib.GFM.PSC

/-- The explicit Euler integration of a PSC model about its selected angle with step `h > 0`. -/
structure Euler where
  /-- The integrated PSC model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 1 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its PSC model. -/
def euler : Implementation Model Requirement Euler Requirement 1 0 1 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated field is `C¹`: the smoothness hypothesis of the generic Euler laws
(`Numerics.euler_sound_small_step`). -/
@[powerlib_foundation] theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  (NormalForm.lift_contDiff m.c.rhs_contDiff).comp (contDiff_id.add contDiff_const)

/-- **Without a step constraint the Euler realization of the PSC models is not sound.** A locally
exponentially stable PSC model (`K_p = P_max = 1`, `P* = 0` at `δ* = 0`) integrated with a large
enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := PSC.locallyExponentiallyStable ⟨1, 0, 1⟩ one_pos one_pos (δ₀ := 0) (by simp) (by simp)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_modelField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.PSC

namespace powerlib.GFM.VSMLPF

/-- The explicit Euler integration of a VSM + power-filter model about its selected point with step
`h > 0`. -/
structure Euler where
  /-- The integrated VSM + power-filter model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 3 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its VSM + power-filter model. -/
def euler : Implementation Model Requirement Euler Requirement 3 0 3 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated field is `C¹`: the smoothness hypothesis of the generic Euler laws
(`Numerics.euler_sound_small_step`). -/
@[powerlib_foundation] theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  m.g.contDiff_field.comp (contDiff_id.add contDiff_const)

/-- **Without a step constraint the Euler realization of the VSM + power-filter models is not
sound.** A locally exponentially stable model (`M = D = ω_c = K₀ = 1`, `P₀ = 0` at `δ* = 0`:
`K = 1 < D ω_c + D²/M = 2`) integrated with a large enough step is not locally exponentially stable:
every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨⟨1, 1, 1, 0, 1⟩, 0⟩ one_pos one_pos one_pos
      (by simp) (by norm_num [Model.K]) (by norm_num [Model.K])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_modelField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- The explicit Euler integration of a platform model about its operating point with step
`h > 0`. -/
structure RigEuler where
  /-- The integrated platform model. -/
  design : Rig
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
platform field, with step length its step. -/
def rigEulerFamily : Family RigEuler RigRequirement 4 0 :=
  Numerics.eulerFamily rigFamily Rig.field RigEuler.design RigEuler.h

/-- The Euler realization: every integration realizes its platform model. -/
def rigEuler : Implementation Rig RigRequirement RigEuler RigRequirement 4 0 4 0 :=
  Numerics.euler rigFamily Rig.field RigEuler.design RigEuler.h

/-- The translated platform field is `C¹`: the smoothness hypothesis of the generic Euler laws
(`Numerics.euler_sound_small_step`). -/
@[powerlib_foundation] theorem rig_contDiff_field (m : Rig) : ContDiff ℝ 1 (Rig.field m) :=
  (contDiff_rigField m).comp (contDiff_id.add contDiff_const)

/-- **Without a step constraint the Euler realization of the platform models is not sound.** A
locally exponentially stable platform (design `M = D = ω_c = K₀ = 1`, `P₀ = δ* = 0`, delay
`τ = 1/2`, so `H = 1/2 > 0`) integrated with a large enough step is not locally exponentially
stable: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem rig_not_euler_realizationSoundUnder :
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
  exact Numerics.not_euler_realizationSoundUnder_of_large_step rigFamily_isAutonomous
    rig_contDiff_field (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.VSMLPF

namespace powerlib.GFM.DroopLPF

/-- The explicit Euler integration of a droop + LPF model about its selected point with step
`h > 0`. -/
structure Euler where
  /-- The integrated droop + LPF model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its droop + LPF model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated field is `C¹`: the smoothness hypothesis of the generic Euler laws
(`Numerics.euler_sound_small_step`). -/
@[powerlib_foundation] theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  m.q.contDiff_field.comp (contDiff_id.add contDiff_const)

/-- **Without a step constraint the Euler realization of the droop + LPF models is not sound.** A
locally exponentially stable model (`D = ω_c = K₀ = 1`, `P₀ = 0` at its loading angle) integrated
with a large enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves
the unit disk (`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := DroopLPF.locallyExponentiallyStable ⟨1, 1, 0, 1⟩ one_pos one_pos one_pos (by norm_num)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_modelField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.DroopLPF

namespace powerlib.GFM.AHO

/-- The explicit Euler integration of a virtual-oscillator model about the origin with step
`h > 0`. -/
structure Euler where
  /-- The integrated virtual-oscillator model. -/
  design : AHO
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's field, with
step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family AHO.realField Euler.design Euler.h

/-- The Euler realization: every integration realizes its virtual-oscillator model. -/
def euler : Implementation AHO Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family AHO.realField Euler.design Euler.h

/-- **Without a step constraint the Euler realization of the virtual-oscillator models is not
sound.** A locally exponentially stable oscillator (`ω_s = σ = κ_v = 1`, `v* = 0`:
`c = κ_v v*² − σ < 0`) integrated with a large enough step is not locally exponentially stable:
every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨1, 1, 1, 0⟩ (by norm_num [AHO.c])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    AHO.contDiff_realField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.AHO

namespace powerlib.GFM.DroopVSM

open powerlib.Dynamics (State)

/-- The explicit Euler integration of a VSM model about its selected state with step `h > 0`. -/
structure VSMEuler where
  /-- The integrated VSM model. -/
  design : VSMModel
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family of the VSM models: every integration read as the Euler map of its
model's translated field, with step length its step. -/
def vsmEulerFamily : Family VSMEuler VSMRequirement 2 0 :=
  Numerics.eulerFamily vsmFamily VSMModel.field VSMEuler.design VSMEuler.h

/-- The Euler realization of the VSM models: every integration realizes its VSM model. -/
def vsmEuler : Implementation VSMModel VSMRequirement VSMEuler VSMRequirement 2 0 2 0 :=
  Numerics.euler vsmFamily VSMModel.field VSMEuler.design VSMEuler.h

/-- The translated VSM field is `C¹` near the origin when the power map is `C¹` near the selected
angle: the smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem vsm_contDiffAt_field {m : VSMModel}
    (hs : ContDiffAt ℝ 1 m.P (m.point 0)) :
    ContDiffAt ℝ 1 m.field 0 := by
  refine Numerics.contDiffAt_shift (g := m.vector) (x₀ := m.point) ?_
  have hP : ContDiffAt ℝ 1 (fun x : State 2 => m.P (x 0)) m.point :=
    hs.comp (f := fun x : State 2 => x 0) m.point (Dynamics.contDiff_coord 0).contDiffAt
  rw [contDiffAt_euclidean]
  intro i
  fin_cases i
  · simpa [VSMModel.vector] using (Dynamics.contDiff_coord (k := 1) 1).contDiffAt (x := m.point)
  · simp only [VSMModel.vector, Fin.mk_one, Fin.isValue, PhasePlane.mk_apply_one]
    exact ((contDiffAt_const.sub hP).sub (contDiffAt_const.mul
      ((Dynamics.contDiff_coord 1).contDiffAt.sub contDiffAt_const))).div_const _

/-- **Without a step constraint the Euler realization of the VSM models is not sound.** A locally
exponentially stable VSM model (`P(θ) = θ`, `M = D = 1`, `P_ref = ω_s = 0` at the origin)
integrated with a large enough step is not locally exponentially stable: every Euler multiplier
`1 + hλ` leaves the unit disk (`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[powerlib_domain] theorem vsm_not_euler_realizationSoundUnder :
    connection% (¬ vsmEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := vsm_mem_den_locallyExponentiallyStable ⟨1, 1, 0, 0, fun θ => θ, 0⟩ contDiff_id
    (by simp) (by simp) one_pos one_pos (by simp)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local vsmFamily_isAutonomous
    (by norm_num) (vsm_contDiffAt_field contDiff_id.contDiffAt) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- The explicit Euler integration of a droop + LPF model about its selected state with step
`h > 0`. -/
structure DroopEuler where
  /-- The integrated droop + LPF model. -/
  design : DroopModel
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family of the droop + LPF models: every integration read as the Euler
map of its model's translated field, with step length its step. -/
def droopEulerFamily : Family DroopEuler VSMRequirement 2 0 :=
  Numerics.eulerFamily droopFamily DroopModel.field DroopEuler.design DroopEuler.h

/-- The Euler realization of the droop + LPF models: every integration realizes its model. -/
def droopEuler : Implementation DroopModel VSMRequirement DroopEuler VSMRequirement 2 0 2 0 :=
  Numerics.euler droopFamily DroopModel.field DroopEuler.design DroopEuler.h

/-- The translated droop + LPF field is `C¹` near the origin when the power map is `C¹` near the
selected angle: the smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem droop_contDiffAt_field {m : DroopModel}
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
disk (`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[powerlib_domain] theorem droop_not_euler_realizationSoundUnder :
    connection% (¬ droopEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := infiniteBus_locallyExponentiallyStable
    ⟨⟨1, 1, 0, 0, fun θ => 1 * Real.sin θ⟩, one_ne_zero, one_ne_zero, 0⟩ 1 rfl one_pos one_pos
    (by simp [droopField]) (by simp)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local droopFamily_isAutonomous
    (by norm_num) (droop_contDiffAt_field (contDiff_const.mul Real.contDiff_sin).contDiffAt) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.DroopVSM
