import theorem.GridTiedConverter.GFM.Matching.StiffGrid
import theorem.GridTiedConverter.GFM.Matching.ClosedLoop
import theorem.Numerics.EulerRealization
import theorem.Numerics.EulerPorts

/-! # The explicit Euler integration of the matching-control families: realizations

The matching-control families of `theorem/GridTiedConverter/GFM/Matching/` integrated by the
explicit Euler method with a fixed step `h > 0`: each integration realizes the model it integrates.
A locally exponentially stable model whose field is `C¹` near its point has a step `h₀ > 0` below
which its Euler integration is locally exponentially stable, and without a step constraint the
realization is not sound — except for the stationary-frame family, which has no locally
exponentially stable member, so that its realization is sound without a step constraint, vacuously;
instances of the generic template `theorem/Numerics/EulerRealization.lean`, in the pattern of
`theorem/PowerSystem/Synchronous/SwingEuler.lean`. The reduced closed loop is a family of port
systems (input the DC and load current perturbations, output the conjugate voltages): its Euler
discretization, with the input held over the step, realizes local exponential stability for
small steps and not without a step constraint, and it never realizes passivity (template
`theorem/Numerics/EulerPorts.lean`, in the pattern of
`theorem/GridTiedConverter/PLL/PortEuler.lean`). Scaffolds:
`theorem/Numerics/EulerDiscretization.agda`, `theorem/Numerics/EulerPorts.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module, read about its selected
  point (continuous time, autonomous, no input): `MatchingStiffGrid.family`, the matching closed
  loop on a stiff grid, state `(θ_dq, u_dc, i_d, i_q)`, about its operating point
  (`Model.translated`, `theorem/GridTiedConverter/GFM/Matching/StiffGrid.lean`);
  `Matching.matchingFamily` (matching control with an arbitrary load-current law `i_x(θ, v)`,
  state `(θ, v)`), `theorem/GridTiedConverter/GFM/Matching/Matching.lean`;
  `MatchingClosedLoop.fullFamily` (the stationary-frame closed loop with the load oscillator,
  state `(θ, v_dc, i_αβ, v_αβ, s_αβ)`, `theorem/GridTiedConverter/GFM/Matching/ClosedLoop.lean`);
  `MatchingClosedLoop.family` (the reduced closed loop in the frame of `θ`, state
  `(v_dc, i_d, i_q, v_d, v_q)` about its selected point, a port system with input
  `w = (ĩ_dc, −ĩ_l,d, −ĩ_l,q)` and conjugate output `(ṽ_dc, ṽ_d, ṽ_q)`, same module).
* Implementation layer (I). For each family the integrations `Numerics.EulerStep` of its model type
  (`MatchingStiffGrid.Euler`, `Matching.MatchingEuler`, `MatchingClosedLoop.FullEuler`,
  `MatchingClosedLoop.Euler`): a model and a step `h > 0`; the system is the explicit Euler map
  `z ↦ z + h f(z)` of the translated field, with step length `h`, discrete time, exact arithmetic
  (no round-off), fixed step; for the reduced port family the Euler discretization
  `z⁺ = z + h f(z, w)` with the input held over the step and the same output
  (`Numerics.eulerSystem`). Excluded: step-size control, implicit or higher-order schemes, the
  integration error against the continuous trajectory.
* Smoothness: the stiff-grid and stationary-frame fields are `C¹` everywhere (`field_contDiff`,
  `MatchingClosedLoop.abField_smooth`; the global laws of the template), and so is the reduced
  field at every input (`MatchingClosedLoop.field_smooth`). The laws of
  `matchingFamily` carry the hypothesis that the load law is `C¹` near the selected point
  (`ContDiffAt ℝ 1 (Function.uncurry i_x) (θ*, v*)`; the local laws of the template).
* `MatchingClosedLoop.fullFamily`: no member is locally exponentially stable
  (`MatchingClosedLoop.full_not_mem_den_locallyExponentiallyStable`: every equilibrium has
  `η v* = 0` and a singular Jacobian), so its Euler realization is sound without a step
  constraint, vacuously, and the family has no step threshold to state; its small-step laws hold
  vacuously.
* Level: local exponential stability of the selected point; passivity of the discretized port
  system (reduced family).

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`not_eulerStep_realizationSoundUnder` and their `_local` forms, `contDiffAt_shift`,
`contDiff_shift`), `theorem/GridTiedConverter/GFM/Matching/StiffGrid.lean` (`field_contDiff`,
`mem_den_locallyExponentiallyStable`),
`theorem/GridTiedConverter/GFM/Matching/Matching.lean` (`matching_den_eq`),
`theorem/PowerSystem/Synchronous/GeneralSwing.lean`
(`mem_den_locallyExponentiallyStable_iff_of_sinusoid`),
`theorem/GridTiedConverter/GFM/Matching/ClosedLoop.lean` (`abField_smooth`,
`full_not_mem_den_locallyExponentiallyStable`, `field_smooth`, `example1_mem_den`,
`mem_den_passive`), `theorem/Numerics/EulerPorts.lean`
(`not_eulerStepPorts_realizationSoundUnder_local`, `eulerPortFamily_not_mem_den_passive`,
`not_eulerPorts_realizationSoundUnder_passive`, `eulerPorts_sound_small_step_local`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* The smoothness hypotheses of the generic laws: the translated stiff-grid and stationary-frame
  fields are `C¹` (`Numerics.contDiff_shift` at `MatchingStiffGrid.field_contDiff`,
  `MatchingClosedLoop.abField_smooth`); `Matching.matching_contDiffAt_field` (the translated
  field is `C¹` near the origin when the load law is `C¹` near the selected point);
  `MatchingClosedLoop.contDiffAt_zeroInput` (the zero-input field of the reduced port system is
  `C¹` near the origin).

Family and connection conclusions.
* `MatchingStiffGrid.eulerFamily : Family MatchingStiffGrid.Euler Requirement 4 0`: every
  integration read as its Euler map; requirements and translation are those of its model, read
  through the design. `MatchingStiffGrid.euler`: the implementation layer, every integration
  realizing its model (`Implementation.ofDesign Numerics.EulerStep.design`).
* M–I (realization) on the stiff grid. The small-step laws are the generic connection laws
  applied to the family, with its autonomy `MatchingStiffGrid.family_isAutonomous` and the
  smoothness above: `Numerics.euler_sound_small_step_local`
  (scaffold `sound-small-step`: a locally exponentially stable model has a step `h₀ > 0` such
  that every Euler integration with a step `h ≤ h₀` is locally exponentially stable) and
  `Numerics.euler_sound_small_step_local` (scaffold `certified-small-step`, read through
  certification). `MatchingStiffGrid.not_euler_realizationSoundUnder` (scaffold
  `not-sound-large-step`): without a step constraint the realization is not sound — the locally
  exponentially stable model with unit parameters and `K_p = 0` (`margin = 7/8`) has Euler
  integrations with every multiplier outside the unit disk.
* The same laws for `Matching.matchingFamily` (`Matching.matchingEulerFamily`,
  `Matching.matchingEuler`; the local generic laws `Numerics.euler_sound_small_step_local` applied
  with `Spectral.localFamily_isAutonomous` and `matching_contDiffAt_field`, for a load law `C¹`
  near `(θ*, v*)`; `matching_not_euler_realizationSoundUnder`, witness `C = G = η = 1`, `i_dc = 0`,
  `i_x(θ, v) = sin θ` at the origin, through `matching_den_eq` and the swing hub). The swing
  family with an arbitrary law that matching control reads through has its own Euler laws
  (`Synchronous.GeneralSwing.eulerFamily`, `theorem/PowerSystem/Synchronous/SwingEuler.lean`).
* `MatchingClosedLoop.fullFamily`: `MatchingClosedLoop.fullEulerFamily`,
  `MatchingClosedLoop.fullEuler`; the generic small-step laws, applied with the smoothness
  above, hold vacuously (no model is locally exponentially stable), and
  `full_euler_realizationSoundUnder`: the realization is sound without a step constraint
  (`RealizationSoundUnder ∅`), vacuously, so the family has no step threshold to state.
* `MatchingClosedLoop.family` (port family, `Family.IsPort` with `Model.system`):
  `MatchingClosedLoop.eulerFamily` (every discretization read as the Euler discretization of its
  model's port system, with the requirements and translation of its model read through the
  design) and `MatchingClosedLoop.euler` (`Implementation.ofDesign`). The small-step law is
  `Numerics.eulerPorts_sound_small_step_local` applied with the port structure and
  `MatchingClosedLoop.contDiffAt_zeroInput` (scaffold `sound-small-step`);
  `MatchingClosedLoop.not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`): the
  globally exponentially stable model `example1` (`example1_mem_den`) has discretizations with
  every multiplier outside the unit disk. Passivity:
  `MatchingClosedLoop.euler_not_mem_den_passive` — no discretization is passive, whatever its
  model and step (the output `(ṽ_dc, ṽ_d, ṽ_q)` does not see the input, and at `ṽ_dc = 1` one step
  with a large DC current draws energy without bound);
  `MatchingClosedLoop.not_euler_realizationSoundUnder_passive` — the passivity realization is not
  sound even within the requirements that make the model passive (`physical`, `equilibrium`,
  `damping`, met by `example1`, passive by `mem_den_passive`).
-/

noncomputable section

namespace powerlib.GFM.Matching.MatchingStiffGrid

/-- The explicit Euler integration of a stiff-grid matching model about its operating point with
step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.translated Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its stiff-grid matching model. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.translated Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the stiff-grid matching models is not
sound.** A locally exponentially stable model (`C_dc = G_dc = η = μ = u*_dc = v₀ = R_s = L_s = 1`,
`K_p = 0`: `margin = 7/8 > 0`) integrated with a large enough step is not locally exponentially
stable: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨⟨1, 1, 0⟩, 0, 1, 1, 1, 1,
    ⟨1, 1, 0⟩, rfl, rfl⟩ one_pos one_pos one_pos
    (by norm_num) one_ne_zero (by norm_num [Model.margin, Model.ω0, Model.N])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift (field_contDiff m)) (by norm_num) hm

end powerlib.GFM.Matching.MatchingStiffGrid

namespace powerlib.GFM.Matching

open powerlib.Dynamics (State)

/-- The explicit Euler integration of a matching-control model about its selected point with step
`h > 0`. -/
abbrev MatchingEuler := Numerics.EulerStep MatchingModel

/-- The Euler integration family of the matching-control models: every integration read as the
Euler map of its model's translated field, with step length its step. -/
def matchingEulerFamily : Family MatchingEuler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily matchingFamily MatchingModel.field
    Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization of the matching-control models: every integration realizes its model. -/
def matchingEuler :
    Implementation MatchingModel Spectral.Requirement MatchingEuler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler matchingFamily MatchingModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated matching field is `C¹` near the origin when the load law is `C¹` near the
selected point: the smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem matching_contDiffAt_field {m : MatchingModel}
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

/-- **Without a step constraint the Euler realization of the matching-control models is not
sound.** The model `C = G = η = 1`, `i_dc = 0`, `i_x(θ, v) = sin θ` at the origin is locally
exponentially stable (its matched swing model `M = D = 1`, `τ = 0`, `P_e = sin θ` is,
`matching_den_eq` and
`Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid`); integrated with a
large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem matching_not_euler_realizationSoundUnder :
    connection% (¬ matchingEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  set m : MatchingModel :=
    ⟨⟨1, 1, 0⟩, 1, 0, fun θ _ => Real.sin θ, 0, 0, one_ne_zero, one_ne_zero, rfl⟩
  have hd := matching_den_eq .locallyExponentiallyStable
  have hs := Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid m.toSwing
    0 1 0 (by funext θ ω; simp [m, MatchingModel.toSwing]) (by simp [m, MatchingModel.toSwing])
    (by norm_num [m, MatchingModel.toSwing])
  unfold powerlib.TMIO.Statement at hd hs
  have hm : m ∈ matchingFamily.den (.flow .locallyExponentiallyStable) := by
    rw [hd, Set.mem_preimage, hs]
    norm_num [m, MatchingModel.toSwing]
  exact Numerics.not_eulerStep_realizationSoundUnder_local
    (Spectral.localFamily_isAutonomous _ _ _ : matchingFamily.IsAutonomous MatchingModel.field)
    (by norm_num) (matching_contDiffAt_field (m := m)
      (show ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Real.sin p.1) (0, 0) by fun_prop)) hm

end powerlib.GFM.Matching

namespace powerlib.GFM.Matching.MatchingClosedLoop

/-- The explicit Euler integration of a stationary-frame matching model about its selected point
with step `h > 0`. -/
abbrev FullEuler := Numerics.EulerStep FullModel

/-- The Euler integration family of the stationary-frame models: every integration read as the
Euler map of its model's translated field, with step length its step. -/
def fullEulerFamily : Family FullEuler Spectral.Requirement 8 0 :=
  Numerics.eulerFamily fullFamily FullModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization of the stationary-frame models: every integration realizes its model. -/
def fullEuler :
    Implementation FullModel Spectral.Requirement FullEuler Spectral.Requirement 8 0 8 0 :=
  Numerics.euler fullFamily FullModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **The Euler realization of the stationary-frame models is sound without a step constraint,
vacuously.** No stationary-frame model is locally exponentially stable
(`full_not_mem_den_locallyExponentiallyStable`: every equilibrium has a singular Jacobian), so
no integration is certified for local exponential stability, whatever its step; the family has
no step threshold to state. -/
@[tmio MI, powerlib_domain] theorem full_euler_realizationSoundUnder :
    connection% (fullEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Implementation.realizationSoundUnder_of_forall_not_mem_den (I := fullEuler) rfl fun x => ?_
  have hn := full_not_mem_den_locallyExponentiallyStable x
  unfold powerlib.TMIO.Statement at hn
  exact hn

end powerlib.GFM.Matching.MatchingClosedLoop

namespace powerlib.GFM.Matching.MatchingClosedLoop

/-- The explicit Euler discretization of a reduced matching closed loop, a port system about its
selected point, with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler discretization family of the reduced closed loops: every discretization read as the
Euler discretization of its model's port system (the input held over the step, the same output),
with step length its step. -/
def eulerFamily : Family Euler Requirement 5 3 :=
  Numerics.eulerPortFamily family Model.system Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization of the reduced closed loops: every discretization realizes its model. -/
def euler : Implementation Model Requirement Euler Requirement 5 3 5 3 :=
  Numerics.eulerPorts family Model.system Numerics.EulerStep.design Numerics.EulerStep.h

/-- The zero-input field of the reduced port system is `C¹` near the origin: the smoothness
hypothesis of the generic Euler laws for port systems
(`Numerics.eulerPorts_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_zeroInput (m : Model) :
    ContDiffAt ℝ 1 m.system.zeroInput 0 :=
  ((field_smooth m 0).comp (contDiff_id.add contDiff_const)).contDiffAt

/-- At the unit DC-voltage deviation the output is `(1, 0, 0)`, whatever the input. -/
@[tmio M, powerlib_domain] private theorem output_single (m : Model) (u : Fin 3 → ℝ) :
    m.system.output (EuclideanSpace.single 0 1) u = ![1, 0, 0] := by
  ext i
  fin_cases i <;> simp [Model.system]

/-- **Without a step constraint the Euler realization of the reduced closed loops is not sound.**
The model `example1` is globally, hence locally, exponentially stable (`example1_mem_den`);
discretized with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_eulerStepPorts_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hg := example1_mem_den
  have hs := Spectral.den_globallyExponentiallyStable_subset_les (F := family)
  unfold powerlib.TMIO.Statement at hg hs
  exact Numerics.not_eulerStepPorts_realizationSoundUnder_local (fun _ => rfl) (by norm_num)
    (contDiffAt_zeroInput _) (hs hg)

/-- **No Euler discretization of a reduced closed loop is passive, whatever its step.** The output
`(ṽ_dc, ṽ_d, ṽ_q)` does not depend on the input; at the unit DC-voltage deviation it is
`(1, 0, 0)`, so one step with a large DC current perturbation draws energy without bound and no
nonnegative storage pays for it (`Numerics.eulerPortFamily_not_mem_den_passive`). -/
@[tmio TM, powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (m : Model) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro m h hh
  exact Numerics.eulerPortFamily_not_mem_den_passive (design := Numerics.EulerStep.design)
    (step := Numerics.EulerStep.h) (y := ⟨m, h, hh⟩) hh (output_single m) (by simp)

/-- **The passivity realization of explicit Euler is not sound for the reduced closed loops, even
within the requirements that make a model passive.** The model `example1` meets `physical`,
`equilibrium` and `damping` and is passive (`mem_den_passive`); its discretizations are not
(`Numerics.not_eulerPorts_realizationSoundUnder_passive`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder {.physical, .equilibrium, .damping} .passive) := by
  unfold powerlib.TMIO.Statement
  have he := example1_equilibrium
  unfold powerlib.TMIO.Statement at he
  have heq : example1.field example1.point 0 = 0 := by
    simpa only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets] using he
  have hm := mem_den_passive example1 (by norm_num [example1]) (by norm_num [example1])
    (by norm_num [example1]) (by norm_num [example1]) (by norm_num [example1]) heq
    (by rw [example1_margin]; norm_num)
  unfold powerlib.TMIO.Statement at hm
  refine Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨example1, 1, one_pos⟩) hm
    ?_ one_pos (output_single example1) (by simp)
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl | rfl)
  · exact ⟨by norm_num [example1], by norm_num [example1], by norm_num [example1],
      by norm_num [example1], by norm_num [example1]⟩
  · exact heq
  · show 0 < example1.margin
    rw [example1_margin]
    norm_num

end powerlib.GFM.Matching.MatchingClosedLoop
