import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Adapted, progressive and predictable processes; finite-dimensional laws

The measurability classes of stochastic processes and the determination of a process law by its
finite-dimensional distributions. Mathlib proves them in the generality the library needs; this
module declares nothing and records the Mathlib theorems that are applied directly.

Scope.
* Probability theory, not an engineering result.
* No declarations of its own: every result below is a Mathlib theorem, used under its own name.

Source: work-sync theory/T-process-foundations-stochastic.md §1.1 (filtrations, natural
filtration), §1.2 (measurability classes of processes: predictable ⇒ progressive ⇒ adapted;
continuous adapted ⇒ progressive), §1.3 (the law of a process is determined by its
finite-dimensional distributions; modifications have the same law).

Results (Mathlib, namespace `MeasureTheory` unless stated).
* Progressive ⇒ adapted: `IsProgressive.adapted`, `IsStronglyProgressive.stronglyAdapted`.
* Predictable ⇒ progressive ⇒ adapted: `IsStronglyPredictable.isStronglyProgressive`,
  `IsStronglyPredictable.stronglyAdapted`, then `StronglyAdapted.adapted` for the measurable
  sense; in discrete time `u (n + 1)` is `𝓕 n`-measurable:
  `IsStronglyPredictable.measurable_add_one`.
* Adapted ⇒ progressive: `StronglyAdapted.isStronglyProgressive_of_continuous` (continuous
  paths), `StronglyAdapted.isStronglyProgressive_of_discrete` (discrete time).
* The natural filtration: `Filtration.stronglyAdapted_natural`.
* Finite-dimensional laws: `ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq` (the law
  is determined by the finite-dimensional distributions), `ProbabilityTheory.map_eq_of_forall_ae_eq`
  (modifications have the same law).
-/
