import theorem.WPT.Bifurcation
import theorem.NormalForm.Scalar
import theorem.Spectral.Local
import theorem.TMIO.ClaimElab

/-! # Zero-phase-angle frequency tracking of the series–series link

A frequency controller that drives the operating frequency of the series–series link toward a
zero of the input phase: it integrates the output of a phase detector with the sign of the input
reactance, `ω̇ = −K N(ω)`, `N` the reactance numerator of `theorem/WPT/Bifurcation.lean`. The
design frequency `ω₀` of the tuned coil pair is always an equilibrium. It is locally exponentially
stable exactly when the slope `K N'(ω₀)` is positive, which for a positive gain and a positive
design frequency is the coupling condition `k² Q² < 1` (`ω₀² M² L₂ < (R₂ + R_L)² L₁`), and
unstable when `k² Q² > 1`: in the over-coupled regime the tracker does not lock at the resonant
frequency of the coils. Where it goes instead (for example to the split zero-phase-angle
frequencies of `theorem/WPT/Bifurcation.lean`) is not proved here.

Model boundary.
* Parameters (`Tracker`): the untuned coil pair `coils : Passive.Coupled`, tuned at the design
  frequency `ω₀` by `tunedCoils` (`theorem/WPT/Compensation.lean`), the load `R_L` and the tracking
  gain `K`. State: the operating angular frequency `ω` (`Dynamics.State 1`), continuous time, read
  about `ω₀`.
* Quasi-static: the electrical tank is in sinusoidal steady state at every instant (the phasor
  model of `theorem/WPT/Link.lean`); the frequency loop is much slower than the tank transients
  (`theorem/WPT/Resonator.lean`), which are not part of this model.
* The detector output is the reactance numerator
  `N(ω) = ω³((R₂ + R_L)² + X₂(ω)²) Im Z_in(jω)`, a polynomial with the sign of the input reactance
  at every positive frequency (`inputImpedance_im_pos_iff`); the conclusions are proved for this
  detector. No detector delay, filter, saturation, quantization, PWM or dead time.

Source: frequency tracking of the zero-phase-angle point and its instability under frequency
splitting in inductive power transfer (Wang, Covic and Stielau, *IEEE Trans. Ind. Electron.* 51
(2004) 148–157; Hui, Zhong and Lee, *IEEE Trans. Power Electron.* 29 (2014) 4500–4511); the
scalar linearization wrappers of `theorem/NormalForm/Scalar.lean` and the local spectral table of
`theorem/Spectral/Local.lean`, after the pattern of `theorem/GridTiedConverter/GFM/PSC.lean`.

Results.
* `Tracker`, `Tracker.rhs` (`−K N(ω)`), `Tracker.field`, `Tracker.slope`
  (`K · 2ω₀³((R₂ + R_L)² L₁ − ω₀² M² L₂)`), `rhs_contDiff`, `hasDerivAt_rhs`, `rhs_design`
  (the design frequency is an equilibrium).

Family and connection conclusions.
* `Tracking.family : Family Tracker Requirement 1 0` reads a tracker as its scalar field translated
  so that `ω₀` is the origin. Requirements: `lockSlope` (`0 < slope`) and `splitSlope`
  (`slope < 0`). Lyapunov stability and the local attractive sentences translate into
  `lockSlope`, instability into `splitSlope`, passivity into nothing, the global sentences, decay
  rates, sampled contraction, conservation and the envelope sentences into the whole, inconsistent,
  language (unavailable translation coverage).
* `chain_le_semantics`: every translation is sound (scalar linearization at `ω₀`);
  `exact_locallyExponentiallyStable`: the local exponential translation is exact (converse
  linearization).
* `locallyExponentiallyStable` (`K > 0`, `ω₀ > 0`, `k² Q² < 1`: the tracker locks at `ω₀`),
  `unstable` (`K > 0`, `ω₀ > 0`, `k² Q² > 1`: it leaves `ω₀`).
-/

noncomputable section

namespace powerlib.WPT

open Set
open powerlib.Dynamics (State)
open powerlib.NormalForm (lift embed)

/-- A zero-phase-angle frequency tracker: the coil pair (tuned at `ω₀`), the load, the design
frequency and the tracking gain. -/
structure Tracker where
  /-- The untuned coil pair. -/
  coils : Passive.Coupled
  /-- The load resistance. -/
  load : ℝ
  /-- The design frequency at which the coils are tuned. -/
  ω₀ : ℝ
  /-- The tracking gain `K`. -/
  gain : ℝ

namespace Tracker

variable (t : Tracker)

/-- The tracking law `ω̇ = −K N(ω)`. -/
def rhs (ω : ℝ) : ℝ := -(t.gain * reactanceNumerator t.coils t.load t.ω₀ ω)

/-- The tracking field on `State 1`. -/
def field : State 1 → State 1 := lift t.rhs

/-- The slope `K N'(ω₀) = K · 2ω₀³((R₂ + R_L)² L₁ − ω₀² M² L₂)`. -/
def slope : ℝ :=
  t.gain * (2 * t.ω₀ ^ 3 * ((t.coils.secondary.R + t.load) ^ 2 * t.coils.primary.L -
    t.ω₀ ^ 2 * t.coils.M ^ 2 * t.coils.secondary.L))

@[tmio M, powerlib_domain] theorem rhs_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k t.rhs := by
  unfold rhs reactanceNumerator
  fun_prop

@[tmio M, powerlib_domain] theorem hasDerivAt_rhs : HasDerivAt t.rhs (-t.slope) t.ω₀ := by
  have h := (hasDerivAt_reactanceNumerator t.coils t.load t.ω₀).const_mul t.gain |>.neg
  unfold rhs slope
  convert h using 1

/-- The design frequency is an equilibrium of the tracker. -/
@[tmio M, powerlib_domain] theorem rhs_design : t.rhs t.ω₀ = 0 := by
  simp [rhs, reactanceNumerator]

end Tracker

namespace Tracking

/-- The tracking field translated so that the design frequency is the origin. -/
def modelField (t : Tracker) (z : State 1) : State 1 := t.field (z + embed t.ω₀)

/-- Static requirements on trackers. -/
inductive Requirement
  /-- A positive slope `K N'(ω₀) > 0`: the field decreases through `ω₀`. -/
  | lockSlope
  /-- A negative slope `K N'(ω₀) < 0`: the field increases through `ω₀`. -/
  | splitSlope

/-- Satisfaction of a requirement by a tracker. -/
def Meets (t : Tracker) : Requirement → Prop
  | .lockSlope => 0 < t.slope
  | .splitSlope => t.slope < 0

/-- The local table: Lyapunov stability and the local attractive sentences to `lockSlope`,
instability to `splitSlope`, passivity to nothing, every other sentence to the whole language. -/
def translate : Sentence → Set Requirement :=
  Spectral.localTable {.lockSlope} {.lockSlope} {.splitSlope} ∅

/-- The frequency-tracking family. -/
def family : Family Tracker Requirement 1 0 :=
  ⟨fun t => Port.System.autonomous (modelField t), Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous modelField :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {t : Tracker} {P : Flow.Property} :
    t ∈ family.den (.flow P) ↔ P.holds t.field (embed t.ω₀) :=
  Spectral.mem_den_flow_iff_shift (f := fun t : Tracker => t.field) (pt := fun t => embed t.ω₀)
    family_isAutonomous

@[tmio TM, powerlib_domain] private theorem les_of {t : Tracker} (hs : Meets t .lockSlope) :
    connection% (t ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hs' : 0 < t.slope := hs
  apply NormalForm.lift_locallyExponentiallyStable t.rhs_contDiff t.rhs_design
  rw [t.hasDerivAt_rhs.deriv]
  linarith

@[tmio TM, powerlib_domain] private theorem unstable_of {t : Tracker} (hs : Meets t .splitSlope) :
    connection% (t ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hs' : t.slope < 0 := hs
  apply NormalForm.lift_unstable t.rhs_contDiff t.rhs_design
  rw [t.hasDerivAt_rhs.deriv]
  linarith

/-- The whole requirement language is inconsistent: the slope cannot be both positive and
negative. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .lockSlope .splitSlope fun t h1 h2 => ?_
  have h1 : 0 < t.slope := h1
  have h2 : t.slope < 0 := h2
  linarith

/-- Every translation of the tracking family is sound: the scalar linearization at `ω₀` proves the
local sentences and instability, and passivity holds without requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same (Rs := {.lockSlope})
    (Ru := {.splitSlope}) (fun _ => rfl) realize_univ (fun t ht => ?_) (fun t ht => ?_)
    family_isAutonomous.den_passive
  · rw [(connection_proof% TMIO.mem_realize)] at ht
    exact mem_den_flow_iff.mpr (mem_den_flow_iff.mp (les_of (ht .lockSlope (by simp))))
  · rw [(connection_proof% TMIO.mem_realize)] at ht
    exact mem_den_flow_iff.mpr (mem_den_flow_iff.mp (unstable_of (ht .splitSlope (by simp))))

/-- The local exponential translation is exact: a tracker locks at `ω₀`, locally exponentially,
exactly when its slope `K N'(ω₀)` is positive (converse linearization of the scalar field). -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exact_of_exactUnder_empty (Spectral.exactUnder_les_of_jacobian
    (fun t P => mem_den_flow_iff) ∅ (fun t => !![-t.slope])
    (fun t _ ht => ?_) (fun t _ => NormalForm.lift_contDiff t.rhs_contDiff)
    (fun t _ => (NormalForm.hasFDerivAt_lift (by simpa using t.hasDerivAt_rhs)).fderiv)
    fun t _ _ hH => ?_)
  · rw [(connection_proof% TMIO.mem_realize)] at ht
    exact mem_den_flow_iff.mpr (mem_den_flow_iff.mp (les_of (ht .lockSlope
      (by exact Set.mem_singleton _))))
  rw [Linear.isHurwitz_one_iff, neg_lt_zero] at hH
  rw [(connection_proof% TMIO.mem_realize)]
  intro q hq
  have hq' : q ∈ ({.lockSlope} : Set Requirement) := hq
  rw [Set.mem_singleton_iff] at hq'
  subst hq'
  exact hH

/-- Under-coupled tracking locks at the design frequency: with a positive gain and design
frequency and `k² Q² < 1` (`ω₀² M² L₂ < (R₂ + R_L)² L₁`), `ω₀` is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem locallyExponentiallyStable (t : Tracker) (hK : 0 < t.gain)
    (hω₀ : 0 < t.ω₀)
    (h : t.ω₀ ^ 2 * t.coils.M ^ 2 * t.coils.secondary.L <
      (t.coils.secondary.R + t.load) ^ 2 * t.coils.primary.L) :
    connection% (t ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (mem_den_flow_iff.mp (les_of ?_))
  show 0 < t.slope
  unfold Tracker.slope
  have : 0 < (t.coils.secondary.R + t.load) ^ 2 * t.coils.primary.L -
      t.ω₀ ^ 2 * t.coils.M ^ 2 * t.coils.secondary.L := by linarith
  positivity

/-- Over-coupled tracking leaves the design frequency: with a positive gain and design frequency
and `k² Q² > 1` (`(R₂ + R_L)² L₁ < ω₀² M² L₂`), `ω₀` is unstable. -/
@[tmio TM, powerlib_domain] theorem unstable (t : Tracker) (hK : 0 < t.gain) (hω₀ : 0 < t.ω₀)
    (h : (t.coils.secondary.R + t.load) ^ 2 * t.coils.primary.L <
      t.ω₀ ^ 2 * t.coils.M ^ 2 * t.coils.secondary.L) :
    connection% (t ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (mem_den_flow_iff.mp (unstable_of ?_))
  show t.slope < 0
  unfold Tracker.slope
  have h1 : (t.coils.secondary.R + t.load) ^ 2 * t.coils.primary.L -
      t.ω₀ ^ 2 * t.coils.M ^ 2 * t.coils.secondary.L < 0 := by linarith
  have h2 : 0 < t.gain * (2 * t.ω₀ ^ 3) := by positivity
  nlinarith

end Tracking

end powerlib.WPT
