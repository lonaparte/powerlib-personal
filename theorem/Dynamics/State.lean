import theorem.Flow.Defs

/-! # State space notation

The state space of the Flow semantics, as reducible notation.

Scope.
* Reducible notation only: it introduces no structure, definition of behaviour or semantics.

Source: library infrastructure (no work-sync note).

Results.
* `State n` — abbreviates the state space `ℝⁿ = EuclideanSpace ℝ (Fin n)` of the Flow semantics.
-/

namespace powerlib.Dynamics

/-- The state space `ℝⁿ` of the Flow semantics. -/
abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

end powerlib.Dynamics
