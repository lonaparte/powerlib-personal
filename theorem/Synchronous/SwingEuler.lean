import theorem.Synchronous.Swing
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the swing equation: a realization

The swing family (`Swing.family`, `theorem/Synchronous/Swing.lean`) integrated by the explicit
Euler method with a fixed step `h > 0` is an implementation layer over it: each integration
realizes the swing model it integrates. A locally exponentially stable swing model has a step
`h₀ > 0` below which its Euler integration is locally exponentially stable, and without a step
constraint the realization is not sound; the instance of the generic template
`theorem/Numerics/EulerRealization.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `Swing.family`, the swing model `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))` read
  about its selected point `(δ*, 0)` (state `z = (δ − δ*, ω)`, continuous time, autonomous, no
  input), with the model boundary of `theorem/Synchronous/Swing.lean`.
* Implementation layer (I). `Swing.Euler`: a swing model and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated swing field (the Euler integration of the
  swing equation from `(δ, ω)`, read about `(δ*, 0)`), with step length `h`, discrete time, exact
  arithmetic (no round-off), fixed step. Excluded: step-size control, implicit or higher-order
  schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`), `theorem/Synchronous/Swing.lean` (`family_isAutonomous`,
`SwingParams.contDiff_field`); work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions; the witness `overstep` and the left inverse of
  its Euler Jacobian are private evidence.

Family and connection conclusions.
* `Swing.eulerFamily : Family Swing.Euler Requirement 2 0`: every integration read as its Euler
  map; requirements and translation are those of its swing model, read through the design
  (`meets y = Swing.Meets y.design`). `Swing.euler`: the implementation layer, every integration
  realizing its swing model (`Implementation.ofDesign Euler.design`).
* M–I (realization). `euler_sound_small_step` (scaffold `sound-small-step`): a locally
  exponentially stable swing model (for instance a balanced angle with positive inertia, damping
  and synchronizing coefficient, `Swing.mem_den_locallyExponentiallyStable`) has a step `h₀ > 0`
  such that every Euler integration with a step `h ≤ h₀` is locally exponentially stable.
  `euler_certified_small_step` (scaffold `certified-small-step`): the same for the design of an
  integration certified for local exponential stability. `not_euler_realizationSoundUnder`:
  without a step constraint the realization is not sound — `M = 1`, `D = 4`, `K = 4` at a balanced
  angle with step `h = 3` has both Euler multipliers at `−5` (the generic witness
  `Numerics.not_euler_realizationSoundUnder`).
-/

noncomputable section

namespace powerlib.Synchronous.Swing

/-- The explicit Euler integration of a swing model about its selected point with step `h > 0`. -/
structure Euler where
  /-- The integrated swing model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's
translated field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its swing model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated swing field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 m.field :=
  (m.p.contDiff_field (k := 1)).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the swing model.** A locally
exponentially stable swing model has a step `h₀ > 0` such that its explicit Euler integration with
every step `h ∈ (0, h₀]` is locally exponentially stable. -/
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
exponential stability (its swing model is locally exponentially stable), every Euler integration
of its swing model with a step below a threshold is locally exponentially stable. -/
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

/-- The overstepped integration: `M = 1`, `D = 4`, `P_m = k₁ = k₃ = 0`, `k₂ = 4`, `δ* = 0`
(Jacobian `[[0, 1], [−4, −4]]`, eigenvalue `−2` twice), step `h = 3` (Euler multiplier
`1 + 3 (−2) = −5` twice). -/
private def overstep : Euler := ⟨⟨⟨1, 4, 0, 0, 4, 0⟩, 0⟩, 3, by norm_num⟩

/-- The left inverse `(I + 3 J)⁻¹ = [[−11, −3], [12, 1]] / 25` of the overstepped Euler
Jacobian. -/
private def overstepInverse : Matrix (Fin 2) (Fin 2) ℝ := (1 / 25 : ℝ) • !![-11, -3; 12, 1]

/-- **Without a step constraint the Euler realization of the swing family is not sound.** The
overstepped integration (`M = 1`, `D = 4`, `K = 4` at a balanced angle, step `h = 3`) is not
locally exponentially stable although its swing model is: both Euler multipliers are `−5`. -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  set J := overstep.design.p.jacobian 0 with hJdef
  have hJ : fderiv ℝ overstep.design.field 0 = Map.op J := by
    change fderiv ℝ (fun z => overstep.design.p.field (z + overstep.design.point)) 0 = _
    rw [fderiv_comp_add_right, zero_add, Model.fderiv_point]
    rfl
  have h0 : overstep.design.field 0 = 0 := by
    change overstep.design.p.field (0 + overstep.design.point) = 0
    rw [zero_add, SwingParams.field_eq_zero_iff _ (by norm_num [overstep])]
    simp [overstep, Model.point, SwingParams.Pe]
  have hA : LinearSystems.IsHurwitz J :=
    (SwingParams.isHurwitz_jacobian_iff _ (by norm_num [overstep]) 0).mpr
      ⟨by norm_num [overstep], by norm_num [overstep, SwingParams.syncCoeff]⟩
  have hB : overstepInverse * Numerics.forwardEulerMatrix overstep.h J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [overstepInverse, Numerics.forwardEulerMatrix, hJdef, overstep, SwingParams.jacobian,
        SwingParams.syncCoeff, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hS : LTI.SchurStable overstepInverse := by
    intro μ v hv heig
    have hdet := Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _ hv heig
    rw [Criteria.det_characteristicMatrix_fin_two] at hdet
    have htr : overstepInverse.trace = -2 / 5 := by
      simp [overstepInverse, Matrix.trace_fin_two]
      norm_num
    have hdt : overstepInverse.det = 1 / 25 := by
      simp [overstepInverse, Matrix.det_fin_two]
      norm_num
    rw [htr, hdt] at hdet
    have hsq : (μ + 1 / 5) ^ 2 = 0 := by
      push_cast at hdet
      linear_combination hdet
    have hμ : μ = -1 / 5 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
      linear_combination this
    rw [hμ]
    norm_num
  exact Numerics.not_euler_realizationSoundUnder family_isAutonomous contDiff_modelField
    (by norm_num) overstep J overstepInverse hJ h0 hA hB hS

end powerlib.Synchronous.Swing
