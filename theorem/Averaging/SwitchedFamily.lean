import theorem.Averaging.SwitchedStability
import theorem.LTI.ExactSampling

/-! # The switched implementation of an averaged linear model: a realization (foundation)

A switched linear system that alternates between `ẋ = A₁ x` (for `d T`) and `ẋ = A₂ x` (for
`(1 − d) T`), read stroboscopically at the switching instants `t = k T` (the period map
`M_T = e^{(1−d) T A₂} e^{d T A₁}` as a discrete system of step length `T`), realizes the averaged
model `ẋ = Ā x`, `Ā = d A₁ + (1 − d) A₂`, it is designed from (`Implementation.ofDesign`, design
map `(d, T, A₁, A₂) ↦ Ā`). The realization holds only under a constraint, fast switching: an
averaged model satisfying an attractive sentence gives a switching period below which the
switched system satisfies it (`Averaging.periodMap_schurStable_of_isHurwitz` read through the
continuous and discrete linear readings), and without a constraint on the switching period the
realization is not sound — slow switching between two Hurwitz matrices with a Hurwitz average
gives a period map with a multiplier below `−1` (`Averaging.slowSwitching_counterexample`, a
period-doubling instability). Scaffold: `theorem/SwitchedAveraging.agda`.

Scope.
* Model layer (M): the continuous linear family `LTI.continuousFamily`
  (`theorem/LTI/ExactSampling.lean`): `ẋ = Ā x` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, no ports.
* Implementation layer (I). `Averaging.Switched n`: duty `d ∈ [0, 1]`, switching period `T > 0`,
  topologies `A₁`, `A₂` (any real square matrices); the ideal two-topology switched linear system
  of `theorem/Averaging/SwitchedStability.lean` (ideal instantaneous switches, fixed duty ratio,
  no input, no PWM carrier or modulator dynamics, no control loop, no delay, no discontinuous
  conduction), discrete time: the period map with step length `T`. The ripple between switching
  instants is not read.
* Generic: the families range over all real square matrices; no engineering model.
* Matrix norms: the `L∞` operator norm (`Matrix.Norms.Operator`), the convention of
  `avgMatrix` and `periodMap`; no statement depends on it.

Source: `theorem/Averaging/SwitchedStability.lean` (`periodMap_schurStable_of_isHurwitz`,
`slowSwitching_counterexample`), `theorem/Averaging/StateSpaceAveraging.lean` (`avgMatrix`,
`periodMap`), `theorem/Map/LinearReading.lean`, `theorem/LTI/ExactSampling.lean`,
`theorem/Stack/Implementation.lean`; work-sync `theory/T-averaging-method.md` §1.5, §1.8, §2.4.

Results.
* Static: `switchedFamily_isAutonomousMap`.

Family and connection conclusions.
* `Averaging.switchedFamily : Family (Switched n) Spectral.Requirement n 0`: every switched system
  read as the map of its period map; requirements and translation are those of its averaged
  model, read through the design (`meets y = LTI.continuousFamily.meets y.average`).
* M–I (realization). `Averaging.switching`, every switched system realizing its averaged model
  (`Implementation.ofDesign Switched.average`).
  `switching_sound_fast` (scaffold `sound-fast`): for every attractive sentence (and sampled
  contraction), every duty `d ∈ [0, 1]` and topologies `A₁`, `A₂` whose averaged model satisfies
  it, there is `T₀ > 0` such that every switched system with switching period `T ≤ T₀` satisfies
  it. `not_switching_realizationSoundUnder` (scaffold `not-sound-slow`): without a constraint the
  realization is not sound for any attractive sentence (nor sampled contraction), witnessed in
  `ℝ²` by `d = 1/2`, `T = 5`, `A₁ = [[−1/10, 1], [0, −1/10]]`, `A₂ = [[−1/10, 0], [−1, −1/10]]`.
-/

noncomputable section

namespace powerlib.Averaging

open Matrix LinearSystems
open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- A switched implementation of an averaged linear model: duty `d ∈ [0, 1]`, switching period
`T > 0`, topology `A₁` on `[kT, kT + dT]` and `A₂` on `[kT + dT, (k + 1)T]`. -/
structure Switched (n : ℕ) where
  /-- The duty ratio. -/
  d : ℝ
  /-- The switching period. -/
  T : ℝ
  /-- The state matrix of the first topology. -/
  A₁ : Matrix (Fin n) (Fin n) ℝ
  /-- The state matrix of the second topology. -/
  A₂ : Matrix (Fin n) (Fin n) ℝ
  /-- The duty ratio lies in `[0, 1]`. -/
  duty : d ∈ Set.Icc (0 : ℝ) 1
  /-- Switching periods are positive. -/
  pos : 0 < T

namespace Switched

/-- The design: the averaged model `ẋ = Ā x`, `Ā = d A₁ + (1 − d) A₂`. -/
def average (y : Switched n) : LTI.ContinuousModel n := ⟨avgMatrix y.d y.A₁ y.A₂⟩

/-- The step matrix: the period map `e^{(1−d) T A₂} e^{d T A₁}`. -/
def step (y : Switched n) : Matrix (Fin n) (Fin n) ℝ := periodMap y.d y.T y.A₁ y.A₂

end Switched

/-- The switched implementation family, read stroboscopically: every switched system read as the
map of its period map, with step length its switching period; requirements and translation are
those of its averaged model. -/
def switchedFamily : Family (Switched n) Spectral.Requirement n 0 where
  system y := .discrete (Map.System.autonomous y.T (Map.op y.step))
  meets y := LTI.continuousFamily.meets y.average
  translate := (LTI.continuousFamily (n := n)).translate

@[powerlib_foundation] theorem switchedFamily_isAutonomousMap :
    (switchedFamily (n := n)).IsAutonomousMap Switched.T fun y => Map.op y.step :=
  fun _ => rfl

/-- The switched realization: every switched system realizes its averaged model. -/
def switching :
    Implementation (LTI.ContinuousModel n) Spectral.Requirement (Switched n) Spectral.Requirement
      n 0 n 0 :=
  { model := LTI.continuousFamily, impl := switchedFamily,
    realizes := Implementation.ofDesign Switched.average }

/-- **Fast switching realizes the averaged model.** For an attractive sentence (or sampled
contraction), a duty `d ∈ [0, 1]` and topologies `A₁`, `A₂` whose averaged model satisfies it,
there is a switching period `T₀ > 0` below which every switched system satisfies it. -/
@[powerlib_domain] theorem switching_sound_fast {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (∀ (d : ℝ) (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) (hd : d ∈ Set.Icc (0 : ℝ) 1),
      (⟨avgMatrix d A₁ A₂⟩ : LTI.ContinuousModel n) ∈ LTI.continuousFamily.den (.flow P) →
        ∃ T₀ : {T : ℝ // 0 < T}, ∀ (T : ℝ) (hT : 0 < T), T ≤ T₀.1 →
          (⟨d, T, A₁, A₂, hd, hT⟩ : Switched n) ∈ switchedFamily.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  intro d A₁ A₂ hd h
  rw [LTI.continuousFamily_isLinear.den_hurwitz hP] at h
  obtain ⟨T₀, hT₀, hS⟩ := periodMap_schurStable_of_isHurwitz hd.1 hd.2 A₁ A₂ h
  refine ⟨⟨T₀, hT₀⟩, fun T hT hle => ?_⟩
  rw [switchedFamily_isAutonomousMap.den_schurStable hP]
  exact (hS T ⟨hT, hle⟩).1

/-- The slow-switching witness: `d = 1/2`, `T = 5`, two Hurwitz topologies with a Hurwitz
average. -/
private def slow : Switched 2 :=
  ⟨1 / 2, 5, !![-1 / 10, 1; 0, -1 / 10], !![-1 / 10, 0; -1, -1 / 10],
    ⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- **Without a constraint the switched realization is not sound.** For every attractive sentence
(and sampled contraction), slow switching between two Hurwitz topologies with a Hurwitz average
gives a switched system outside the sentence whose averaged model satisfies it. -/
@[powerlib_domain] theorem not_switching_realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (¬ (switching (n := 2)).RealizationSoundUnder ∅ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨-, -, havg, -, hnot⟩ := slowSwitching_counterexample
  refine Implementation.not_realizationSoundUnder_of_design (I := switching) (y := slow) rfl
    ?_ ?_ ?_
  · change slow.average ∈ LTI.continuousFamily.den (.flow P)
    rw [LTI.continuousFamily_isLinear.den_hurwitz hP]
    exact havg
  · rw [TMIO.realize_empty]
    exact Set.mem_univ _
  · change slow ∉ switchedFamily.den (.flow P)
    rw [switchedFamily_isAutonomousMap.den_schurStable hP]
    exact hnot

end powerlib.Averaging
