import theorem.LTI.SampledFlow
import theorem.Spectral.Family
import theorem.Stack.Implementation

/-! # Exact sampling of continuous linear models: a realization (foundation)

A continuous-time linear model `ẋ = A x` and its implementation by exact sampling with period
`T > 0`, read at the sampling instants: the discrete system `x_{k+1} = e^{TA} x_k`. The sampled
system realizes the model it is designed from (`Implementation.ofDesign`, design map
`(A, T) ↦ A`), and the realization is exact for every sentence, at every sampling period: the
linear flow of `A` and the linear map `e^{TA}` satisfy the same sentences at the origin
(`LTI.holds_iff_holdsMap_exp`, `theorem/LTI/SampledFlow.lean`: the attractive sentences and
sampled contraction are the Hurwitz property of `A` and the Schur property of `e^{TA}`; Lyapunov
stability, instability, decay rates and conservation are read through the samples of the
solutions and the flow over one period), and neither system has a port, so both are passive. The
sampled family translates as its design model, so its translations are as sound and as exact as
the model's. Scaffold: `theorem/ExactSampling.agda`.

Scope.
* Model layer (M). `LTI.ContinuousModel n`: a continuous-time autonomous linear model `ẋ = A x`
  on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, no ports, any real square matrix `A`; read as the port
  system of the plant `(A, 0, 0, 0)` (`Family.IsLinear`).
* Implementation layer (I). `LTI.Sampled n`: a design model and a sampling period `T > 0`; the
  state is sampled exactly (ideal sampler, no quantization, no jitter, no computation delay) and
  the system has no input, so the zero-order hold is idle; the system is the map `e^{TA}` with
  step length `T` (`Map.System.autonomous`), discrete time. The intersample behaviour is not read.
* Generic: the families range over all real square matrices; no engineering model.

Source: `theorem/LTI/SampledFlow.lean` (`holds_iff_holdsMap_exp`), `theorem/LTI/Sampling.lean`
(`isHurwitz_iff_schurStable_exp`, `zoh_step`: the exact one-period step of `ẋ = A x` is `e^{TA}`),
`theorem/Map/LinearReading.lean`, `theorem/Linear/Family.lean`, `theorem/Spectral/Family.lean`
(`Spectral.linearFamily`), `theorem/Stack/Implementation.lean`; work-sync
`theory/T-control-delay.md` §1.4 (ZOH), `theory/T-numerical-integration.md` §2.7.

Results.
* Static: `continuousFamily_isLinear`, `sampledFamily_isAutonomousMap`.

Family and connection conclusions.
* `LTI.continuousFamily : Family (ContinuousModel n) Spectral.Requirement n 0`
  (`Spectral.linearFamily`): requirements `stable` (`A` Hurwitz) and `unstable` (a characteristic
  root in the open right half plane); the attractive sentences, sampled contraction and Lyapunov
  stability translate into `stable`, instability into `unstable`, decay rates, conservation and
  passivity into the whole, inconsistent, language. `continuous_chain_le_semantics`: every
  translation is sound; `continuous_exact`: the attractive and contractive translations are exact.
* `LTI.sampledFamily : Family (Sampled n) Spectral.Requirement n 0`: requirements and translation
  of the design model, read through the design (`meets y = continuousFamily.meets y.design`).
* `sampled_reading` (scaffold `reading`): every denotation of the sampled family is the model
  family's pulled back along the design map, at every period.
* `sampled_chain_le_semantics`: every translation of the sampled family is sound (the model
  family's soundness pulled back through the reading); `sampled_exact_iff`: a translation of the
  sampled family is exact exactly when the model family's is (the design map is onto); with
  `continuous_exact` the attractive and contractive translations are exact.
* M–I (realization). `LTI.exactSampling`, every sampled system realizing its design model
  (`Implementation.ofDesign Sampled.design`). `exactSampling_realizationExact` (scaffold `exact`):
  every sentence is realized exactly, without constraints
  (`Implementation.realizationExactUnder_of_den_eq_preimage`).
-/

noncomputable section

namespace powerlib.LTI

open Matrix LinearSystems Linear

variable {n : ℕ}

/-! ## The continuous model family -/

/-- A continuous-time autonomous linear model `ẋ = A x` on `ℝⁿ`. -/
structure ContinuousModel (n : ℕ) where
  /-- The state matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ

namespace ContinuousModel

/-- The plant of the model: no ports. -/
def plant (m : ContinuousModel n) : Linear.Plant n 0 := ⟨m.A, 0, 0, 0⟩

/-- The static stability condition: a Hurwitz state matrix. -/
def Stable (m : ContinuousModel n) : Prop := IsHurwitz m.A

/-- The static instability condition: a characteristic root in the open right half plane. -/
def Unstable (m : ContinuousModel n) : Prop :=
  ∃ s : ℂ, (characteristicMatrix m.A s).det = 0 ∧ 0 < s.re

end ContinuousModel

/-- The continuous linear model family: every model read as the port system of its plant. -/
def continuousFamily : Family (ContinuousModel n) Spectral.Requirement n 0 :=
  Spectral.linearFamily ContinuousModel.plant ContinuousModel.Stable ContinuousModel.Unstable

@[powerlib_foundation] theorem continuousFamily_isLinear :
    (continuousFamily (n := n)).IsLinear ContinuousModel.plant :=
  Spectral.linearFamily_isLinear _ _ _

/-- Every translation of the continuous linear family is sound. -/
@[tmio TM, powerlib_domain] theorem continuous_chain_le_semantics :
    connection% (∀ P, (continuousFamily (n := n)).chain P ≤ continuousFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics (fun _ h => h) (fun _ h => h)

/-- The attractive sentences and sampled contraction are translated exactly: into a Hurwitz state
matrix. -/
@[tmio TM, powerlib_domain] theorem continuous_exact {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((continuousFamily (n := n)).Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun _ => Iff.rfl) hP

/-! ## The sampled implementation family -/

/-- The exact sampling of a design model with period `T > 0`, read at the sampling instants: the
discrete system `x_{k+1} = e^{TA} x_k` with step length `T`. -/
structure Sampled (n : ℕ) where
  /-- The design model. -/
  design : ContinuousModel n
  /-- The sampling period. -/
  T : ℝ
  /-- Sampling periods are positive. -/
  pos : 0 < T

namespace Sampled

/-- The step matrix `e^{TA}`. -/
def step (y : Sampled n) : Matrix (Fin n) (Fin n) ℝ := NormedSpace.exp (y.T • y.design.A)

end Sampled

/-- The sampled implementation family: every sampled system read as the map of its step matrix,
with step length its period; requirements and translation are those of its design model. -/
def sampledFamily : Family (Sampled n) Spectral.Requirement n 0 where
  system y := .discrete (Map.System.autonomous y.T (Map.op y.step))
  meets y := continuousFamily.meets y.design
  translate := (continuousFamily (n := n)).translate

@[powerlib_foundation] theorem sampledFamily_isAutonomousMap :
    (sampledFamily (n := n)).IsAutonomousMap Sampled.T fun y => Map.op y.step :=
  fun _ => rfl

/-- **Reading of the sampled system through its design.** Every denotation of the sampled family
is that of the continuous family pulled back along the design map, at every sampling period: the
flow of the design and its sampled map satisfy the same flow sentences
(`holds_iff_holdsMap_exp`), and neither has a port, so both are passive. -/
@[tmio MI, powerlib_domain] theorem sampled_reading (s : Sentence) :
    connection% ((sampledFamily (n := n)).den s = Sampled.design ⁻¹' continuousFamily.den s) := by
  unfold powerlib.TMIO.Statement
  ext y
  rw [Set.mem_preimage]
  rcases s with P | _ | E
  · rw [sampledFamily_isAutonomousMap.mem_den_flow, continuousFamily_isLinear.mem_den_flow]
    exact (holds_iff_holdsMap_exp y.design.A y.pos P).symm
  · rw [Family.mem_den, Family.mem_den]
    exact iff_of_true (Map.System.autonomous_passive _ _) (Port.System.passive_of_noPorts _)
  · rw [sampledFamily_isAutonomousMap.den_envelope, continuousFamily_isLinear.den_envelope]
    exact iff_of_true trivial trivial

/-- The requirement spaces of the sampled family are those of the continuous family pulled back
along the design map. -/
private theorem sampled_realize (Γ : Set Spectral.Requirement) :
    TMIO.realize (sampledFamily (n := n)).meets Γ =
      Sampled.design ⁻¹' TMIO.realize continuousFamily.meets Γ :=
  TMIO.realize_comap continuousFamily.meets Sampled.design Γ

/-- Every translation of the sampled family is sound: a sampled system meeting the translation of
a sentence has a design meeting it, which satisfies the sentence (`continuous_chain_le_semantics`),
and so does the sampled system (`sampled_reading`). -/
@[tmio TM, powerlib_domain] theorem sampled_chain_le_semantics :
    connection% (∀ P, (sampledFamily (n := n)).chain P ≤ sampledFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hc := continuous_chain_le_semantics (n := n)
  unfold powerlib.TMIO.Statement at hc
  refine Family.chain_le_semantics_iff.mpr fun s => ?_
  have hr := sampled_reading (n := n) s
  unfold powerlib.TMIO.Statement at hr
  unfold Family.Sound
  rw [hr, show (sampledFamily (n := n)).translate s = continuousFamily.translate s from rfl,
    sampled_realize]
  exact Set.preimage_mono (Family.chain_le_semantics_iff.mp hc s)

/-- **Exactness of the sampled family is the model family's.** A translation of the sampled family
is exact exactly when the continuous family's is: both its requirement spaces and its denotations
are the model family's pulled back along the design map, which is onto. With `continuous_exact`
the attractive and contractive translations are exact. -/
@[tmio TM, powerlib_domain] theorem sampled_exact_iff (s : Sentence) :
    connection% ((sampledFamily (n := n)).Exact s ↔ (continuousFamily (n := n)).Exact s) := by
  unfold powerlib.TMIO.Statement
  have hr := sampled_reading (n := n) s
  unfold powerlib.TMIO.Statement at hr
  have hsurj : Function.Surjective (Sampled.design (n := n)) := fun m => ⟨⟨m, 1, one_pos⟩, rfl⟩
  unfold Family.Exact
  rw [hr, show (sampledFamily (n := n)).translate s = continuousFamily.translate s from rfl,
    sampled_realize]
  exact (Set.preimage_injective.mpr hsurj).eq_iff

/-! ## The realization -/

/-- Exact sampling as an implementation layer: every sampled system realizes its design model. -/
def exactSampling :
    Implementation (ContinuousModel n) Spectral.Requirement (Sampled n) Spectral.Requirement
      n 0 n 0 :=
  { model := continuousFamily, impl := sampledFamily,
    realizes := Implementation.ofDesign Sampled.design }

/-- **Exact sampling realizes every sentence exactly.** Without constraints, at every sampling
period, a sampled system satisfies a sentence exactly when its design model does. -/
@[tmio MI, powerlib_domain] theorem exactSampling_realizationExact (s : Sentence) :
    connection% ((exactSampling (n := n)).RealizationExactUnder ∅ s) := by
  unfold powerlib.TMIO.Statement
  have h := sampled_reading (n := n) s
  unfold powerlib.TMIO.Statement at h
  exact Implementation.realizationExactUnder_of_den_eq_preimage rfl h

end powerlib.LTI
