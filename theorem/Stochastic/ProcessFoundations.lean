import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Adapted, progressive and predictable processes; finite-dimensional laws

The measurability classes of stochastic processes and the determination of a process law by its
finite-dimensional distributions, as thin wrappers of Mathlib.

Scope.
* Probability theory, not an engineering result.
* Every result is a thin Mathlib wrapper (the Mathlib declaration is given in brackets).

Source: work-sync theory/T-process-foundations-stochastic.md §1.1 (filtrations, natural
filtration), §1.2 (measurability classes of processes: predictable ⇒ progressive ⇒ adapted;
continuous adapted ⇒ progressive), §1.3 (the law of a process is determined by its
finite-dimensional distributions; modifications have the same law).

Results.
* `progressive_adapted` [`MeasureTheory.IsProgressive.adapted`].
* `stronglyProgressive_stronglyAdapted` [`MeasureTheory.IsStronglyProgressive.stronglyAdapted`].
* `predictable_progressive` [`MeasureTheory.IsStronglyPredictable.isStronglyProgressive`].
* `predictable_adapted` — a predictable real process is adapted in the measurable sense (from
  the previous two and `StronglyAdapted.adapted`).
* `predictable_discrete_previsible` [`IsStronglyPredictable.measurable_add_one`] — in discrete
  time `u (n + 1)` is `𝓕 n`-measurable.
* `continuous_adapted_progressive`
  [`MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous`].
* `discrete_adapted_progressive` [`StronglyAdapted.isStronglyProgressive_of_discrete`].
* `natural_adapted` [`MeasureTheory.Filtration.stronglyAdapted_natural`].
* `law_eq_iff_fdd_eq` [`ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq`].
* `law_eq_of_modification` [`ProbabilityTheory.map_eq_of_forall_ae_eq`].
-/

noncomputable section
namespace powerlib.Stochastic.Found

open MeasureTheory ProbabilityTheory

variable {Ω ι β : Type*} {m : MeasurableSpace Ω}

/-- A progressively measurable process is adapted. -/
@[tmio T, powerlib_foundation] theorem progressive_adapted [Preorder ι] [MeasurableSpace ι]
    [MeasurableSpace β] {f : Filtration ι m} {u : ι → Ω → β} (h : IsProgressive f u) :
    Adapted f u :=
  h.adapted

/-- A strongly progressive process is strongly adapted. -/
@[powerlib_foundation] theorem stronglyProgressive_stronglyAdapted [Preorder ι]
    [MeasurableSpace ι] [TopologicalSpace β] {f : Filtration ι m} {u : ι → Ω → β}
    (h : IsStronglyProgressive f u) : StronglyAdapted f u :=
  h.stronglyAdapted

/-- A predictable process is progressive. -/
@[powerlib_foundation] theorem predictable_progressive [LinearOrder ι] [OrderBot ι]
    [MeasurableSpace ι] [TopologicalSpace ι] [OpensMeasurableSpace ι] [OrderClosedTopology ι]
    [TopologicalSpace β] {f : Filtration ι m} {u : ι → Ω → β} (h : IsStronglyPredictable f u) :
    IsStronglyProgressive f u :=
  h.isStronglyProgressive

/-- A predictable real process is adapted (each `u i` is `f i`-measurable). -/
@[powerlib_foundation] theorem predictable_adapted [LinearOrder ι] [OrderBot ι]
    [MeasurableSpace ι] [TopologicalSpace ι] [OpensMeasurableSpace ι] [OrderClosedTopology ι]
    {f : Filtration ι m} {u : ι → Ω → ℝ} (h : IsStronglyPredictable f u) : Adapted f u :=
  h.stronglyAdapted.adapted

/-- Discrete-time predictable processes are previsible: `u (n + 1)` is `𝓕 n`-measurable. -/
@[powerlib_foundation] theorem predictable_discrete_previsible [TopologicalSpace β]
    {f : Filtration ℕ m} {u : ℕ → Ω → β} (h : IsStronglyPredictable f u) (n : ℕ) :
    StronglyMeasurable[f n] (u (n + 1)) :=
  h.measurable_add_one n

/-- An adapted process with continuous paths is progressive. -/
@[powerlib_foundation] theorem continuous_adapted_progressive [Preorder ι] [TopologicalSpace ι]
    [TopologicalSpace.MetrizableSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [OpensMeasurableSpace ι] [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    {f : Filtration ι m} {u : ι → Ω → β} (h : StronglyAdapted f u)
    (hc : ∀ ω, Continuous fun i => u i ω) : IsStronglyProgressive f u :=
  h.isStronglyProgressive_of_continuous hc

/-- In discrete time adapted and progressive coincide. -/
@[powerlib_foundation] theorem discrete_adapted_progressive [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] {f : Filtration ℕ m} {u : ℕ → Ω → β}
    (h : StronglyAdapted f u) : IsStronglyProgressive f u :=
  h.isStronglyProgressive_of_discrete

/-- A process is adapted to its natural filtration. -/
@[powerlib_foundation] theorem natural_adapted [Preorder ι] [TopologicalSpace β]
    [TopologicalSpace.MetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {u : ι → Ω → β}
    (hu : ∀ i, StronglyMeasurable (u i)) :
    StronglyAdapted (Filtration.natural u hu) u :=
  Filtration.stronglyAdapted_natural hu

/-- The law of a process is determined by its finite-dimensional distributions. -/
@[powerlib_foundation] theorem law_eq_iff_fdd_eq {T : Type*} {𝓧 : T → Type*}
    [∀ t, MeasurableSpace (𝓧 t)] {X Y : (t : T) → Ω → 𝓧 t} {P : Measure Ω} [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω => (X · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P) :
    P.map (fun ω => (X · ω)) = P.map (fun ω => (Y · ω)) ↔
      ∀ I : Finset T, P.map (fun ω => I.restrict (X · ω)) = P.map (fun ω => I.restrict (Y · ω)) :=
  map_eq_iff_forall_finset_map_restrict_eq hX hY

/-- Modifications (`X t = Y t` a.s. for every `t`) have the same law. -/
@[powerlib_foundation] theorem law_eq_of_modification {T : Type*} {𝓧 : T → Type*}
    [∀ t, MeasurableSpace (𝓧 t)] {X Y : (t : T) → Ω → 𝓧 t} {P : Measure Ω} [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω => (X · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    P.map (fun ω => (X · ω)) = P.map (fun ω => (Y · ω)) :=
  map_eq_of_forall_ae_eq hX hY h

end powerlib.Stochastic.Found
