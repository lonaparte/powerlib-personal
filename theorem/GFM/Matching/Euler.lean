import theorem.GFM.Matching.StiffGrid
import theorem.GFM.Matching.ClosedLoop
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the matching-control families: realizations

The matching-control families of `theorem/GFM/Matching/` integrated by the explicit Euler method
with a fixed step `h > 0`: each integration realizes the model it integrates. A locally
exponentially stable model whose field is `C¹` near its point has a step `h₀ > 0` below which its
Euler integration is locally exponentially stable, and without a step constraint the realization
is not sound — except for the stationary-frame family, which has no locally exponentially stable
member, so that its realization is sound without a step constraint, vacuously; instances of the
generic template `theorem/Numerics/EulerRealization.lean`, in the pattern of
`theorem/Synchronous/SwingEuler.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module, read about its selected
  point (continuous time, autonomous, no input): `MatchingStiffGrid.family`, the matching closed
  loop on a stiff grid, state `(θ_dq, u_dc, i_d, i_q)`, about its operating point
  (`Model.translated`, `theorem/GFM/Matching/StiffGrid.lean`); `Matching.matchingFamily` (matching
  control with an arbitrary load-current law `i_x(θ, v)`, state `(θ, v)`) and
  `Matching.swingFamily` (swing model with an arbitrary power law `P_e(θ, ω)`, state `(θ, ω)`),
  `theorem/GFM/Matching/Matching.lean`; `MatchingClosedLoop.fullFamily` (the stationary-frame
  closed loop with the load oscillator, state `(θ, v_dc, i_αβ, v_αβ, s_αβ)`,
  `theorem/GFM/Matching/ClosedLoop.lean`).
* Implementation layer (I). For each family a structure (`MatchingStiffGrid.Euler`,
  `Matching.MatchingEuler`, `Matching.SwingEuler`, `MatchingClosedLoop.FullEuler`) of a model and a
  step `h > 0`; the system is the explicit Euler map `z ↦ z + h f(z)` of the translated field,
  with step length `h`, discrete time, exact arithmetic (no round-off), fixed step. Excluded:
  step-size control, implicit or higher-order schemes, the integration error against the
  continuous trajectory.
* Smoothness: the stiff-grid and stationary-frame fields are `C¹` everywhere (`field_contDiff`,
  `MatchingClosedLoop.abField_smooth`; the global laws of the template). The laws of
  `matchingFamily` and `swingFamily` carry the hypothesis that the law is `C¹` near the selected
  point (`ContDiffAt ℝ 1 (Function.uncurry i_x) (θ*, v*)`, resp. `P_e` at `(θ*, ω*)`; the local
  laws of the template).
* `MatchingClosedLoop.fullFamily`: no member is locally exponentially stable
  (`MatchingClosedLoop.full_not_mem_den_locallyExponentiallyStable`: every equilibrium has
  `η v* = 0` and a singular Jacobian), so its Euler realization is sound without a step
  constraint, vacuously, and the family has no step threshold to state; its small-step laws hold
  vacuously.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step` and their `_local`
forms, `contDiffAt_shift`), `theorem/GFM/Matching/StiffGrid.lean` (`field_contDiff`,
`mem_den_locallyExponentiallyStable`), `theorem/GFM/Matching/Matching.lean` (`matching_den_eq`,
`swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid`),
`theorem/GFM/Matching/ClosedLoop.lean` (`abField_smooth`,
`full_not_mem_den_locallyExponentiallyStable`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `MatchingStiffGrid.eulerFamily : Family MatchingStiffGrid.Euler Requirement 4 0`: every
  integration read as its Euler map; requirements and translation are those of its model, read
  through the design. `MatchingStiffGrid.euler`: the implementation layer, every integration
  realizing its model (`Implementation.ofDesign Euler.design`).
* M–I (realization) on the stiff grid. `MatchingStiffGrid.euler_sound_small_step` (scaffold
  `sound-small-step`): a locally exponentially stable model has a step `h₀ > 0` such that every
  Euler integration with a step `h ≤ h₀` is locally exponentially stable.
  `MatchingStiffGrid.euler_certified_small_step` (scaffold `certified-small-step`): the same for
  the design of an integration certified for local exponential stability.
  `MatchingStiffGrid.not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — the locally exponentially stable model
  with unit parameters and `K_p = 0` (`margin = 7/8`) has Euler integrations with every multiplier
  outside the unit disk.
* The same laws for `Matching.matchingFamily` (`Matching.matchingEulerFamily`,
  `Matching.matchingEuler`; `matching_euler_sound_small_step`,
  `matching_euler_certified_small_step`, with a load law `C¹` near `(θ*, v*)`;
  `matching_not_euler_realizationSoundUnder`, witness `C = G = η = 1`, `i_dc = 0`,
  `i_x(θ, v) = sin θ` at the origin, through `matching_den_eq`) and `Matching.swingFamily`
  (`Matching.swingEulerFamily`, `Matching.swingEuler`; `swing_euler_sound_small_step`,
  `swing_euler_certified_small_step`, with a power law `C¹` near `(θ*, ω*)`;
  `swing_not_euler_realizationSoundUnder`, witness `M = D = 1`, `τ = 0`, `P_e = sin θ` at the
  origin).
* `MatchingClosedLoop.fullFamily`: `MatchingClosedLoop.fullEulerFamily`,
  `MatchingClosedLoop.fullEuler`; `full_euler_sound_small_step`, `full_euler_certified_small_step`
  (both vacuous: no model is locally exponentially stable) and
  `full_euler_realizationSoundUnder`: the realization is sound without a step constraint
  (`RealizationSoundUnder ∅`), vacuously, so the family has no step threshold to state.
-/

noncomputable section

namespace powerlib.GFM.Matching.MatchingStiffGrid

/-- The explicit Euler integration of a stiff-grid matching model about its operating point with
step `h > 0`. -/
structure Euler where
  /-- The integrated stiff-grid matching model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.translated Euler.design Euler.h

/-- The Euler realization: every integration realizes its stiff-grid matching model. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.translated Euler.design Euler.h

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.translated m) :=
  (field_contDiff m).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the stiff-grid matching models.** A locally
exponentially stable stiff-grid matching model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) (fun _ => rfl : family.IsAutonomous Model.translated) contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its stiff-grid matching model is locally exponentially stable), every Euler
integration of its stiff-grid matching model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step (fun _ => rfl : family.IsAutonomous
    Model.translated) contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the stiff-grid matching models is not
sound.** A locally exponentially stable model (`C_dc = G_dc = η = μ = u*_dc = v₀ = R_s = L_s = 1`,
`K_p = 0`: `margin = 7/8 > 0`) integrated with a large enough step is not locally exponentially
stable: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨1, 1, 0, 1, 1, 1, 1, 1, 1⟩ one_pos one_pos one_pos
    (by norm_num) one_ne_zero (by norm_num [Model.margin, Model.ω0, Model.N])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step
    (fun _ => rfl : family.IsAutonomous Model.translated)
    contDiff_modelField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.Matching.MatchingStiffGrid

namespace powerlib.GFM.Matching

open powerlib.Dynamics (State)

/-- The explicit Euler integration of a matching-control model about its selected point with step
`h > 0`. -/
structure MatchingEuler where
  /-- The integrated matching-control model. -/
  design : MatchingModel
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family of the matching-control models: every integration read as the
Euler map of its model's translated field, with step length its step. -/
def matchingEulerFamily : Family MatchingEuler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily matchingFamily MatchingModel.field MatchingEuler.design MatchingEuler.h

/-- The Euler realization of the matching-control models: every integration realizes its model. -/
def matchingEuler :
    Implementation MatchingModel Spectral.Requirement MatchingEuler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler matchingFamily MatchingModel.field MatchingEuler.design MatchingEuler.h

/-- The translated matching field is `C¹` near the origin when the load law is `C¹` near the
selected point. -/
private theorem matching_contDiffAt_field {m : MatchingModel}
    (hs : ContDiffAt ℝ 1 (Function.uncurry m.ix) (m.θ, m.v)) : ContDiffAt ℝ 1 m.field 0 := by
  refine Numerics.contDiffAt_shift (g := matchingField m.C m.G m.η m.idc m.ix) (x₀ := m.point) ?_
  have hpt : (m.point 0, m.point 1) = (m.θ, m.v) := by simp [MatchingModel.point]
  have hx : ContDiffAt ℝ 1 (fun x : State 2 => m.ix (x 0) (x 1)) m.point :=
    ContDiffAt.comp (g := Function.uncurry m.ix) (f := fun x : State 2 => (x 0, x 1)) m.point
      (by beta_reduce; rw [hpt]; exact hs)
      ((Dynamics.contDiff_coord 0).prodMk (Dynamics.contDiff_coord 1)).contDiffAt
  rw [contDiffAt_euclidean]
  intro i
  fin_cases i
  · simp only [matchingField, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
    exact contDiffAt_const.mul (Dynamics.contDiff_coord 1).contDiffAt
  · simp only [matchingField, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact ((contDiffAt_const.sub hx).sub
      (contDiffAt_const.mul (Dynamics.contDiff_coord 1).contDiffAt)).div_const _

/-- **Small steps realize local exponential stability of the matching-control models.** A locally
exponentially stable matching-control model whose load law is `C¹` near the selected point has a
step `h₀ > 0` such that its explicit Euler integration with every step `h ∈ (0, h₀]` is locally
exponentially stable. -/
@[powerlib_domain] theorem matching_euler_sound_small_step :
    connection% (∀ m : MatchingModel, ContDiffAt ℝ 1 (Function.uncurry m.ix) (m.θ, m.v) →
      m ∈ matchingFamily.den (.flow .locallyExponentiallyStable) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨m, h, hh⟩ : MatchingEuler) ∈
            matchingEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hs hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step_local (design := MatchingEuler.design)
    (step := MatchingEuler.h)
    (Spectral.localFamily_isAutonomous _ _ _ : matchingFamily.IsAutonomous MatchingModel.field)
    (matching_contDiffAt_field hs) hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its matching-control model is locally exponentially stable) whose load law
is `C¹` near the selected point, every Euler integration of its model with a step below a threshold
is locally exponentially stable. -/
@[powerlib_domain] theorem matching_euler_certified_small_step :
    connection% (∀ y : MatchingEuler,
      ContDiffAt ℝ 1 (Function.uncurry y.design.ix) (y.design.θ, y.design.v) →
      y ∈ TMIO.certify matchingEuler.realizes
        (matchingEuler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : MatchingEuler) ∈
            matchingEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hs hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step_local
    (Spectral.localFamily_isAutonomous _ _ _ : matchingFamily.IsAutonomous MatchingModel.field)
    (matching_contDiffAt_field hs) hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the matching-control models is not
sound.** The model `C = G = η = 1`, `i_dc = 0`, `i_x(θ, v) = sin θ` at the origin is locally
exponentially stable (its matched swing model `M = D = 1`, `τ = 0`, `P_e = sin θ` is,
`matching_den_eq`); integrated with a large enough step it is not: every Euler multiplier
`1 + hλ` leaves the unit disk (`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[powerlib_domain] theorem matching_not_euler_realizationSoundUnder :
    connection% (¬ matchingEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  set m : MatchingModel := ⟨1, 1, 1, 0, fun θ _ => Real.sin θ, 0, 0, one_ne_zero, one_ne_zero⟩
  have hd := matching_den_eq .locallyExponentiallyStable
  have hs := swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid m.toSwing 0 1 0
    (by funext θ ω; simp [m, MatchingModel.toSwing]) (by simp [m, MatchingModel.toSwing])
    (by norm_num [m, MatchingModel.toSwing])
  unfold powerlib.TMIO.Statement at hd hs
  have hm : m ∈ matchingFamily.den (.flow .locallyExponentiallyStable) := by
    rw [hd, Set.mem_preimage, hs]
    norm_num [m, MatchingModel.toSwing]
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local
    (Spectral.localFamily_isAutonomous _ _ _ : matchingFamily.IsAutonomous MatchingModel.field)
    (by norm_num) (matching_contDiffAt_field (m := m)
      (show ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Real.sin p.1) (0, 0) by fun_prop)) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- The explicit Euler integration of a swing model with an arbitrary power law about its selected
point with step `h > 0`. -/
structure SwingEuler where
  /-- The integrated swing model. -/
  design : SwingModel
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family of the swing models: every integration read as the Euler map of
its model's translated field, with step length its step. -/
def swingEulerFamily : Family SwingEuler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily swingFamily SwingModel.field SwingEuler.design SwingEuler.h

/-- The Euler realization of the swing models: every integration realizes its model. -/
def swingEuler :
    Implementation SwingModel Spectral.Requirement SwingEuler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler swingFamily SwingModel.field SwingEuler.design SwingEuler.h

/-- The translated swing field is `C¹` near the origin when the power law is `C¹` near the
selected point. -/
private theorem swing_contDiffAt_field {m : SwingModel}
    (hs : ContDiffAt ℝ 1 (Function.uncurry m.Pe) (m.θ, m.ω)) : ContDiffAt ℝ 1 m.field 0 := by
  refine Numerics.contDiffAt_shift (g := swingField m.M m.D m.τ m.Pe) (x₀ := m.point) ?_
  have hpt : (m.point 0, m.point 1) = (m.θ, m.ω) := by simp [SwingModel.point]
  have hx : ContDiffAt ℝ 1 (fun x : State 2 => m.Pe (x 0) (x 1)) m.point :=
    ContDiffAt.comp (g := Function.uncurry m.Pe) (f := fun x : State 2 => (x 0, x 1)) m.point
      (by beta_reduce; rw [hpt]; exact hs)
      ((Dynamics.contDiff_coord 0).prodMk (Dynamics.contDiff_coord 1)).contDiffAt
  rw [contDiffAt_euclidean]
  intro i
  fin_cases i
  · simp only [swingField, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
    exact (Dynamics.contDiff_coord 1).contDiffAt
  · simp only [swingField, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact ((contDiffAt_const.sub hx).sub
      (contDiffAt_const.mul (Dynamics.contDiff_coord 1).contDiffAt)).div_const _

/-- **Small steps realize local exponential stability of the swing models.** A locally
exponentially stable swing model whose power law is `C¹` near the selected point has a step
`h₀ > 0` such that its explicit Euler integration with every step `h ∈ (0, h₀]` is locally
exponentially stable. -/
@[powerlib_domain] theorem swing_euler_sound_small_step :
    connection% (∀ m : SwingModel, ContDiffAt ℝ 1 (Function.uncurry m.Pe) (m.θ, m.ω) →
      m ∈ swingFamily.den (.flow .locallyExponentiallyStable) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨m, h, hh⟩ : SwingEuler) ∈
            swingEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hs hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step_local (design := SwingEuler.design)
    (step := SwingEuler.h)
    (Spectral.localFamily_isAutonomous _ _ _ : swingFamily.IsAutonomous SwingModel.field)
    (swing_contDiffAt_field hs) hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its swing model is locally exponentially stable) whose power law is `C¹`
near the selected point, every Euler integration of its model with a step below a threshold is
locally exponentially stable. -/
@[powerlib_domain] theorem swing_euler_certified_small_step :
    connection% (∀ y : SwingEuler,
      ContDiffAt ℝ 1 (Function.uncurry y.design.Pe) (y.design.θ, y.design.ω) →
      y ∈ TMIO.certify swingEuler.realizes
        (swingEuler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : SwingEuler) ∈
            swingEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hs hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step_local
    (Spectral.localFamily_isAutonomous _ _ _ : swingFamily.IsAutonomous SwingModel.field)
    (swing_contDiffAt_field hs) hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the swing models is not sound.** The
swing model `M = D = 1`, `τ = 0`, `P_e(θ, ω) = sin θ` at the origin is locally exponentially
stable (`swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid`); integrated with a large
enough step it is not: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[powerlib_domain] theorem swing_not_euler_realizationSoundUnder :
    connection% (¬ swingEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  set m : SwingModel := ⟨1, 1, 0, fun θ _ => 0 + 1 * Real.sin (θ - 0), 0, 0⟩
  have hs := swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid m 0 1 0 rfl rfl one_pos
  unfold powerlib.TMIO.Statement at hs
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local
    (Spectral.localFamily_isAutonomous _ _ _ : swingFamily.IsAutonomous SwingModel.field)
    (by norm_num) (swing_contDiffAt_field (m := m)
      (show ContDiffAt ℝ 1 (fun p : ℝ × ℝ => 0 + 1 * Real.sin (p.1 - 0)) (0, 0) by fun_prop))
    (hs.mpr (by norm_num [m]))
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.Matching

namespace powerlib.GFM.Matching.MatchingClosedLoop

/-- The explicit Euler integration of a stationary-frame matching model about its selected point
with step `h > 0`. -/
structure FullEuler where
  /-- The integrated stationary-frame model. -/
  design : FullModel
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family of the stationary-frame models: every integration read as the
Euler map of its model's translated field, with step length its step. -/
def fullEulerFamily : Family FullEuler Spectral.Requirement 8 0 :=
  Numerics.eulerFamily fullFamily FullModel.field FullEuler.design FullEuler.h

/-- The Euler realization of the stationary-frame models: every integration realizes its model. -/
def fullEuler :
    Implementation FullModel Spectral.Requirement FullEuler Spectral.Requirement 8 0 8 0 :=
  Numerics.euler fullFamily FullModel.field FullEuler.design FullEuler.h

/-- The translated stationary-frame field is `C¹`. -/
private theorem full_contDiff_field (M : FullModel) : ContDiff ℝ 1 M.field :=
  (abField_smooth M.p).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the stationary-frame models.** A locally
exponentially stable stationary-frame model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem full_euler_sound_small_step :
    connection% (∀ M : FullModel, M ∈ fullFamily.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨M, h, hh⟩ : FullEuler) ∈ fullEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro M hM
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := FullEuler.design)
    (step := FullEuler.h)
    (Spectral.localFamily_isAutonomous _ _ _ : fullFamily.IsAutonomous FullModel.field)
    full_contDiff_field hM
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨M, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its stationary-frame model is locally exponentially stable), every Euler
integration of its model with a step below a threshold is locally exponentially stable. -/
@[powerlib_domain] theorem full_euler_certified_small_step :
    connection% (∀ y : FullEuler,
      y ∈ TMIO.certify fullEuler.realizes
        (fullEuler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : FullEuler) ∈
            fullEulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step
    (Spectral.localFamily_isAutonomous _ _ _ : fullFamily.IsAutonomous FullModel.field)
    full_contDiff_field hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **The Euler realization of the stationary-frame models is sound without a step constraint,
vacuously.** No stationary-frame model is locally exponentially stable
(`full_not_mem_den_locallyExponentiallyStable`: every equilibrium has a singular Jacobian), so
no integration is certified for local exponential stability, whatever its step; the family has
no step threshold to state. -/
@[powerlib_domain] theorem full_euler_realizationSoundUnder :
    connection% (fullEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rintro y ⟨hy, -⟩
  rw [Implementation.certify_realizes_of_design (I := fullEuler) rfl] at hy
  have hn := full_not_mem_den_locallyExponentiallyStable y.design
  unfold powerlib.TMIO.Statement at hn
  exact absurd hy hn

end powerlib.GFM.Matching.MatchingClosedLoop
