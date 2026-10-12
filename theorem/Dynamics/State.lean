import theorem.Flow.Defs

/-! # State space notation

`State n` abbreviates the state space `ℝⁿ = EuclideanSpace ℝ (Fin n)` of the Flow semantics. It is
reducible notation only: it introduces no structure, definition of behaviour or semantics. -/

namespace powerlib.Dynamics

/-- The state space `ℝⁿ` of the Flow semantics. -/
abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

end powerlib.Dynamics
