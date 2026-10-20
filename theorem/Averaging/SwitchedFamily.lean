import theorem.Averaging.SwitchedStability
import theorem.LTI.ExactSampling

/-! # The switched implementation of an averaged linear model: a realization (foundation)

A switched linear system that alternates between `ẋ = A₁ x` (for `d T`) and `ẋ = A₂ x` (for
`(1 − d) T`), read stroboscopically at the switching instants `t = k T` (the period map
`M_T = e^{(1−d) T A₂} e^{d T A₁}` as a discrete system of step length `T`), realizes the averaged
model `ẋ = Ā x`, `Ā = d A₁ + (1 − d) A₂`, it is designed from (`Implementation.ofDesign`, design
map `(d, T, A₁, A₂) ↦ Ā`). The realization holds only under a constraint. Fast switching: an
averaged model satisfying an attractive sentence gives a switching period below which the
switched system satisfies it (`Averaging.periodMap_schurStable_of_isHurwitz` read through the
continuous and discrete linear readings). Commuting topologies: if `A₁ A₂ = A₂ A₁`, the period map
is `e^{TĀ}` (`Averaging.periodMap_eq_exp_of_commute`), so the switched system is the exact
sampling of its averaged model with the switching period, and the realization is exact at every
sentence and every period, as exact sampling is (`LTI.sampled_reading`,
`theorem/LTI/ExactSampling.lean`); in dimension `n ≤ 1` every two topologies commute, so averaging
never fails for scalar systems. Without a constraint the realization is not sound in any
dimension `n ≥ 2`: slow switching between two Hurwitz topologies with a Hurwitz average gives a
period map with a multiplier below `−1` (`Averaging.slowSwitching_counterexample_of_two_le`, the
`ℝ²` example `Averaging.slowSwitching_counterexample` embedded block-diagonally; a
period-doubling instability). The dimension boundary is exact: without a constraint the
realization is sound for the attractive sentences (and sampled contraction) exactly when `n ≤ 1`.
Scaffold: `theorem/SwitchedAveraging.agda`.

Scope.
* Model layer (M): the continuous linear family `LTI.continuousFamily`
  (`theorem/LTI/ExactSampling.lean`): `ẋ = Ā x` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, no ports.
* Implementation layer (I). `Averaging.Switched n`: duty `d ∈ [0, 1]`, switching period `T > 0`,
  topologies `A₁`, `A₂` (any real square matrices); the ideal two-topology switched linear system
  of `theorem/Averaging/SwitchedStability.lean` (ideal instantaneous switches, fixed duty ratio,
  no input, no PWM carrier or modulator dynamics, no control loop, no delay, no discontinuous
  conduction), discrete time: the period map with step length `T`. The ripple between switching
  instants is not read. Realistic constraint: the two topologies commute (`commuting`); the
  fast-switching threshold depends on the topologies and is a quantifier of `switching_sound_fast`,
  not a requirement.
* Generic: the families range over all real square matrices; no engineering model.
* Matrix norms: the `L∞` operator norm (`Matrix.Norms.Operator`), the convention of
  `avgMatrix` and `periodMap`; no statement depends on it.

Source: `theorem/Averaging/SwitchedStability.lean` (`periodMap_schurStable_of_isHurwitz`,
`periodMap_eq_exp_of_commute`, `slowSwitching_counterexample_of_two_le`),
`theorem/Averaging/StateSpaceAveraging.lean` (`avgMatrix`, `periodMap`),
`theorem/Map/LinearReading.lean`, `theorem/LTI/ExactSampling.lean` (`sampledFamily`,
`sampled_reading`), `theorem/Stack/Implementation.lean`; work-sync
`theory/T-averaging-method.md` §1.5, §1.8, §2.4.

Results.
* Static: `switchedFamily_isAutonomousMap`.

Family and connection conclusions.
* `Averaging.switchedFamily : Family (Switched n) Switched.Requirement n 0`: every switched system
  read as the map of its period map; requirements `design q` (its averaged model meets the
  requirement `q` of `LTI.continuousFamily`) and `commuting` (`A₁ A₂ = A₂ A₁`); a sentence
  translates into the averaged model's requirements (`design '' continuousFamily.translate s`).
* M–I (realization). `Averaging.switching`, every switched system realizing its averaged model
  (`Implementation.ofDesign Switched.average`).
  `switching_sound_fast` (scaffold `sound-fast`): for every attractive sentence (and sampled
  contraction), every duty `d ∈ [0, 1]` and topologies `A₁`, `A₂` whose averaged model satisfies
  it, there is `T₀ > 0` such that every switched system with switching period `T ≤ T₀` satisfies
  it.
  `switching_realizationExactUnder_commuting` (scaffold `commuting-exact`): within the constraint
  `commuting`, every sentence is realized exactly, at every switching period and duty.
  `switching_realizationExactUnder_of_le_one` (scaffold `dimension-one`): in dimension `n ≤ 1`
  every sentence is realized exactly without constraint.
  `not_switching_realizationSoundUnder` (scaffold `not-sound-slow`): in every dimension `n ≥ 2`,
  without a constraint the realization is not sound for any attractive sentence (nor sampled
  contraction), witnessed by `d = 1/2`, `T = 5` and the topologies
  `[[−1/10, 1], [0, −1/10]] ⊕ (−I)`, `[[−1/10, 0], [−1, −1/10]] ⊕ (−I)`.
  `switching_realizationSoundUnder_iff` (the dimension boundary, from the last two): for the
  attractive sentences and sampled contraction the realization is sound without constraint iff
  `n ≤ 1`.
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

/-- The requirement language of the switched implementations: the requirements of the averaged
model, read through the design, and the constraint that the two topologies commute. -/
inductive Requirement
  /-- The averaged model meets the requirement `q` of `LTI.continuousFamily`. -/
  | design (q : Spectral.Requirement)
  /-- The two topologies commute: `A₁ A₂ = A₂ A₁`. -/
  | commuting

/-- Satisfaction of a switched requirement. -/
def Meets (y : Switched n) : Requirement → Prop
  | .design q => LTI.continuousFamily.meets y.average q
  | .commuting => Commute y.A₁ y.A₂

end Switched

/-- The switched implementation family, read stroboscopically: every switched system read as the
map of its period map, with step length its switching period; the requirements of its averaged
model, read through the design, and the commuting constraint; sentences translate into the
averaged model's requirements. -/
def switchedFamily : Family (Switched n) Switched.Requirement n 0 where
  system y := .discrete (Map.System.autonomous y.T (Map.op y.step))
  meets := Switched.Meets
  translate s := Switched.Requirement.design '' (LTI.continuousFamily (n := n)).translate s

@[powerlib_foundation] theorem switchedFamily_isAutonomousMap :
    (switchedFamily (n := n)).IsAutonomousMap Switched.T fun y => Map.op y.step :=
  fun _ => rfl

/-- The switched realization: every switched system realizes its averaged model. -/
def switching :
    Implementation (LTI.ContinuousModel n) Spectral.Requirement (Switched n) Switched.Requirement
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

/-- Commuting topologies: the switched system is the exact sampling of its averaged model with the
switching period. -/
private theorem system_eq_sampled {y : Switched n} (h : Commute y.A₁ y.A₂) :
    switchedFamily.system y = LTI.sampledFamily.system ⟨y.average, y.T, y.pos⟩ := by
  simp only [switchedFamily, LTI.sampledFamily, Switched.step, LTI.Sampled.step,
    periodMap_eq_exp_of_commute _ _ h]
  rfl

/-- **Commuting topologies are exact at every period.** Within the constraint that the two
topologies commute, at every switching period and duty, a switched system satisfies a sentence
exactly when its averaged model does: the period map is then `e^{TĀ}`
(`periodMap_eq_exp_of_commute`), so the switched system is the exact sampling of its averaged model
with the switching period, read through its design at every sentence (`LTI.sampled_reading`). -/
@[powerlib_domain] theorem switching_realizationExactUnder_commuting (s : Sentence) :
    connection% ((switching (n := n)).RealizationExactUnder {.commuting} s) := by
  unfold powerlib.TMIO.Statement
  have hs := LTI.sampled_reading (n := n) s
  unfold powerlib.TMIO.Statement at hs
  refine Implementation.realizationExactUnder_of_design (I := switching) rfl ?_
  ext y
  refine and_congr_left fun hy => ?_
  have hc : Commute y.A₁ y.A₂ := (TMIO.mem_realize _ _ _).mp hy .commuting rfl
  have h : (⟨y.average, y.T, y.pos⟩ : LTI.Sampled n) ∈ LTI.sampledFamily.den s ↔
      y.average ∈ LTI.continuousFamily.den s := by
    rw [hs]
    rfl
  change y ∈ switchedFamily.den s ↔ y.average ∈ LTI.continuousFamily.den s
  rw [← h, Family.mem_den, Family.mem_den, system_eq_sampled hc]

/-- Square matrices of size at most one commute. -/
private theorem commute_of_le_one (hn : n ≤ 1) (A B : Matrix (Fin n) (Fin n) ℝ) :
    Commute A B := by
  have := Fin.subsingleton_iff_le_one.mpr hn
  show A * B = B * A
  ext i j
  simp only [mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Subsingleton.elim i k, Subsingleton.elim j k, mul_comm]

/-- **Scalar systems: averaging never fails.** In dimension `n ≤ 1` every two topologies commute,
so without a constraint, at every switching period and duty, a switched system satisfies a
sentence exactly when its averaged model does (`switching_realizationExactUnder_commuting`). -/
@[powerlib_domain] theorem switching_realizationExactUnder_of_le_one (hn : n ≤ 1) (s : Sentence) :
    connection% ((switching (n := n)).RealizationExactUnder ∅ s) := by
  have h := switching_realizationExactUnder_commuting (n := n) s
  unfold powerlib.TMIO.Statement Implementation.RealizationExactUnder at h ⊢
  have hΔ : TMIO.realize (switching (n := n)).impl.meets {.commuting} =
      TMIO.realize (switching (n := n)).impl.meets ∅ := by
    rw [TMIO.realize_empty, Set.eq_univ_iff_forall]
    intro y
    rw [TMIO.mem_realize]
    rintro q rfl
    exact commute_of_le_one hn y.A₁ y.A₂
  rwa [← hΔ]

/-- **Without a constraint the switched realization is not sound, in every dimension `n ≥ 2`.**
For every attractive sentence (and sampled contraction), slow switching between two Hurwitz
topologies with a Hurwitz average gives a switched system outside the sentence whose averaged
model satisfies it (`slowSwitching_counterexample_of_two_le`, `d = 1/2`, `T = 5`). -/
@[powerlib_domain] theorem not_switching_realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) (hn : 2 ≤ n) :
    connection% (¬ (switching (n := n)).RealizationSoundUnder ∅ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨A₁, A₂, -, -, havg, hnot⟩ := slowSwitching_counterexample_of_two_le hn
  refine Implementation.not_realizationSoundUnder_of_design (I := switching)
    (y := ⟨1 / 2, 5, A₁, A₂, ⟨by norm_num, by norm_num⟩, by norm_num⟩) rfl ?_ ?_ ?_
  · change (⟨avgMatrix (1 / 2) A₁ A₂⟩ : LTI.ContinuousModel n) ∈ LTI.continuousFamily.den (.flow P)
    rw [LTI.continuousFamily_isLinear.den_hurwitz hP]
    exact havg
  · rw [TMIO.realize_empty]
    exact Set.mem_univ _
  · change (⟨1 / 2, 5, A₁, A₂, _, _⟩ : Switched n) ∉ switchedFamily.den (.flow P)
    rw [switchedFamily_isAutonomousMap.den_schurStable hP]
    exact hnot

/-- **The dimension boundary of averaging.** For an attractive sentence (or sampled contraction),
the switched realization is sound without a constraint exactly in dimension `n ≤ 1`: in
dimension at most one it is exact (`switching_realizationExactUnder_of_le_one`), in every
dimension `n ≥ 2` slow switching refutes it (`not_switching_realizationSoundUnder`). -/
@[powerlib_domain] theorem switching_realizationSoundUnder_iff {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((switching (n := n)).RealizationSoundUnder ∅ (.flow P) ↔ n ≤ 1) := by
  unfold powerlib.TMIO.Statement
  constructor
  · intro h
    by_contra hn
    have hnot := not_switching_realizationSoundUnder hP (by omega : 2 ≤ n)
    unfold powerlib.TMIO.Statement at hnot
    exact hnot h
  · intro hn
    have h := switching_realizationExactUnder_of_le_one hn (.flow P)
    unfold powerlib.TMIO.Statement at h
    exact h.soundUnder

end powerlib.Averaging
