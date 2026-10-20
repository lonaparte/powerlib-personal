import theorem.GFM.PSC
import theorem.GFM.VSMLPF
import theorem.GFM.VSMLPFRig
import theorem.GFM.VOC
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the grid-forming families: realizations

The grid-forming families of autonomous `C¹` fields integrated by the explicit Euler method with a
fixed step `h > 0`: each integration realizes the model it integrates. A locally exponentially
stable model has a step `h₀ > 0` below which its Euler integration is locally exponentially
stable, and without a step constraint the realization is not sound; instances of the generic
template `theorem/Numerics/EulerRealization.lean`, in the pattern of
`theorem/Synchronous/SwingEuler.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module, read about its selected
  point (continuous time, autonomous, no input): `GFM.PSC.family` (quasi-static PSC, state `δ`,
  `theorem/GFM/PSC.lean`); `GFM.VSMLPF.family` (VSM + power filter, state `(δ, ω, P_f)`) and
  `GFM.DroopLPF.family` (droop + power filter, state `(δ, P_f)`), `theorem/GFM/VSMLPF.lean`;
  `GFM.VSMLPF.rigFamily` (the VSM + power-filter platform with an execution delay, state
  `(δ, ω, P_f, θ)`, `theorem/GFM/VSMLPFRig.lean`, here the model its integration realizes);
  `GFM.AHO.family` (the Andronov–Hopf virtual oscillator about the origin, `theorem/GFM/VOC.lean`).
* Implementation layer (I). For each family a structure (`Euler`, for the platform `RigEuler`) of
  a model and a step `h > 0`; the system is the explicit Euler map `z ↦ z + h f(z)` of the model's
  (translated) field, with step length `h`, discrete time, exact arithmetic (no round-off), fixed
  step. Excluded: step-size control, implicit or higher-order schemes, the integration error
  against the continuous trajectory.
* Not instantiated here: `GFM.DroopVSM.vsmFamily` and `droopFamily` (an arbitrary power map, so
  the fields are `C¹` only under the requirement `smooth`).
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`) and the family
modules (autonomy, `C¹` fields, members of local exponential stability); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* For each family `F` above (`F = PSC, VSMLPF, DroopLPF, AHO`): `F.eulerFamily` (for the platform
  `VSMLPF.rigEulerFamily`), every integration read as its Euler map, with the requirements and
  translation of its model read through the design; `F.euler` (`VSMLPF.rigEuler`), every
  integration realizing its model (`Implementation.ofDesign`).
* M–I (realization), for each family: `F.euler_sound_small_step` (scaffold `sound-small-step`): a
  locally exponentially stable model has a step `h₀ > 0` such that every Euler integration with a
  step `h ≤ h₀` is locally exponentially stable. `F.euler_certified_small_step` (scaffold
  `certified-small-step`): the same for the design of an integration certified for local
  exponential stability. `F.not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — a locally exponentially stable member
  (`PSC.locallyExponentiallyStable`, `VSMLPF.mem_den_locallyExponentiallyStable`,
  `DroopLPF.locallyExponentiallyStable`, `AHO.mem_den_locallyExponentiallyStable`, for the
  platform `VSMLPF.rig_chain_le_semantics` at `M = D = ω_c = K₀ = 1`, `τ = 1/2`, `H = 1/2`) has
  Euler integrations with every multiplier outside the unit disk. The platform's statements carry
  the prefix `rig_`.
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

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  (NormalForm.lift_contDiff m.c.rhs_contDiff).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the PSC models.** A locally exponentially
stable PSC model has a step `h₀ > 0` such that its explicit Euler integration with every step
`h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its PSC model is locally exponentially stable), every Euler integration of
its PSC model with a step below a threshold is locally exponentially stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

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

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  m.g.contDiff_field.comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the VSM + power-filter models.** A locally
exponentially stable VSM + power-filter model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its VSM + power-filter model is locally exponentially stable), every Euler
integration of its VSM + power-filter model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

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

/-- The translated platform field is `C¹`. -/
private theorem rig_contDiff_field (m : Rig) : ContDiff ℝ 1 (Rig.field m) :=
  (contDiff_rigField m).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the platform models.** A locally
exponentially stable platform model has a step `h₀ > 0` such that its explicit Euler integration
with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem rig_euler_sound_small_step :
    connection% (∀ m : Rig, m ∈ rigFamily.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : RigEuler) ∈ rigEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := RigEuler.design)
    (step := RigEuler.h) rigFamily_isAutonomous rig_contDiff_field hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its platform model is locally exponentially stable), every Euler integration
of its platform model with a step below a threshold is locally exponentially stable. -/
@[powerlib_domain] theorem rig_euler_certified_small_step :
    connection% (∀ y : RigEuler,
      y ∈ TMIO.certify rigEuler.realizes (rigEuler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : RigEuler) ∈
            rigEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step rigFamily_isAutonomous
    rig_contDiff_field hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

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

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  m.q.contDiff_field.comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the droop + LPF models.** A locally
exponentially stable droop + LPF model has a step `h₀ > 0` such that its explicit Euler integration
with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its droop + LPF model is locally exponentially stable), every Euler
integration of its droop + LPF model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

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

/-- **Small steps realize local exponential stability of the virtual-oscillator models.** A locally
exponentially stable virtual-oscillator model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : AHO, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous AHO.contDiff_realField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its virtual-oscillator model is locally exponentially stable), every Euler
integration of its virtual-oscillator model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    AHO.contDiff_realField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

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
