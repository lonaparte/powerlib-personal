import theorem.Flow.Defs

/-! # Map semantics

The single definition of the behaviour of discrete-time systems: digital controllers, sampled-data
loops read at their sampling instants, period maps of switched systems, numerical integration
schemes. Every model family whose complete systems evolve in discrete steps is read through these
definitions and nothing else.

A discrete-time system is a map `F : ℝⁿ → ℝⁿ` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, the state update
over one step, after inputs are fixed and feedback is closed. Its behaviour from a state `y` is the
orbit of iterates `F^[k] y`, `k : ℕ`. Orbits exist and are unique for all forward steps, so no
notion needs a solution concept or a completeness clause.

Every notion is written with iterates and one-step inequalities; none quantifies a sequence of
states or inputs. The step counter is therefore a quantified instant and never the domain of a
quantified function, and the semantic layer keeps the single time axis of the flow semantics. The
admission audit recognizes iteration of a state map as discrete behaviour (`theorem/Architecture.lean`).

The notions are the discrete counterparts of the flow notions: Lyapunov stability, local
asymptotic and local exponential (geometric) stability, their global versions, instability,
decay at a rate per step, contraction over some number of steps, and conservation of an energy
with a strict minimum. A system with ports has a one-step update and a conjugate output; its step
length `T` converts rates per step into rates per unit time and scales the supplied energy, so the
sentences mean the same in both kinds. Passivity is the one-step dissipation inequality, the
discrete counterpart of the integral dissipation inequality. -/

noncomputable section

namespace powerlib

namespace Map

open Filter Topology

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Lyapunov stability of `x` under the map `F`: orbits starting close stay close. -/
def LyapunovStable (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ∀ k : ℕ, ‖F^[k] y - x‖ < ε

/-- Local asymptotic stability: Lyapunov stable, and the orbits starting within `c` converge. -/
def LocalAsymptoticStable (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop :=
  LyapunovStable F x ∧
    ∃ c > 0, ∀ y, ‖y - x‖ < c → Tendsto (fun k : ℕ => F^[k] y) atTop (𝓝 x)

/-- Local exponential (geometric) stability: `‖F^[k] y - x‖ ≤ C ρ^k ‖y - x‖` near `x`, with
`ρ < 1`. -/
def LocallyExponentiallyStable (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop :=
  ∃ r C ρ : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ y, ‖y - x‖ < r → ∀ k : ℕ, ‖F^[k] y - x‖ ≤ C * ρ ^ k * ‖y - x‖

/-- Global asymptotic stability: a fixed point, Lyapunov stable, every orbit converges. -/
def GloballyAsymptoticallyStable (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop :=
  F x = x ∧ LyapunovStable F x ∧ ∀ y, Tendsto (fun k : ℕ => F^[k] y) atTop (𝓝 x)

/-- Global exponential stability: a fixed point and one geometric estimate on every orbit. -/
def GloballyExponentiallyStable (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop :=
  F x = x ∧ ∃ C ρ : ℝ, 1 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ y (k : ℕ), ‖F^[k] y - x‖ ≤ C * ρ ^ k * ‖y - x‖

/-- Instability is the failure of Lyapunov stability. -/
def Unstable (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop := ¬ LyapunovStable F x

/-- Decay at the rate `a` per step: one constant `C` bounds every orbit by `C e^{-a k}` times its
initial distance to `x`. A negative rate bounds the growth. -/
def Decay (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) (a : ℝ) : Prop :=
  ∃ C : ℝ, ∀ y (k : ℕ), ‖F^[k] y - x‖ ≤ C * Real.exp (-a * k) * ‖y - x‖

/-- Sampled contraction: over some positive number of steps every state ends closer to `x` by a
fixed factor below one. -/
def SampledContraction (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ c < 1, ∀ y, ‖F^[k] y - x‖ ≤ c * ‖y - x‖

/-- Conservation: a continuous energy with a strict minimum at `x` is constant along every
orbit. -/
def Conservative (F : ℝⁿ → ℝⁿ) (x : ℝⁿ) : Prop :=
  ∃ V : ℝⁿ → ℝ, Continuous V ∧ (∀ y, y ≠ x → V x < V y) ∧ ∀ y (k : ℕ), V (F^[k] y) = V y

/-- A discrete-time system with `n` states, `p` ports and step length `period`. -/
structure System (n p : ℕ) where
  /-- The state update over one step, the port input held during the step. -/
  step : EuclideanSpace ℝ (Fin n) → (Fin p → ℝ) → EuclideanSpace ℝ (Fin n)
  /-- The conjugate port output. -/
  output : EuclideanSpace ℝ (Fin n) → (Fin p → ℝ) → (Fin p → ℝ)
  /-- The length of one step in units of time (sampling or integration period). -/
  period : ℝ

/-- The energy supplied through the ports over one step. -/
def System.supply (s : System n p) (x : ℝⁿ) (u : Fin p → ℝ) : ℝ :=
  s.period * (u ⬝ᵥ s.output x u)

/-- The autonomous map with the ports held at zero. -/
def System.zeroInput (s : System n p) : ℝⁿ → ℝⁿ := fun x => s.step x 0

/-- Passivity with the storage `V`: a nonnegative storage whose increase over every step is
bounded by the energy supplied through the ports. -/
def System.PassiveWith (s : System n p) (V : ℝⁿ → ℝ) : Prop :=
  (∀ x, 0 ≤ V x) ∧ ∀ x u, V (s.step x u) - V x ≤ s.supply x u

/-- Passivity with some storage. -/
def System.Passive (s : System n p) : Prop := ∃ V, s.PassiveWith V

/-- The system of an autonomous map with step length `T`: no ports. -/
def System.autonomous (T : ℝ) (F : ℝⁿ → ℝⁿ) : System n 0 := ⟨fun x _ => F x, fun _ _ => 0, T⟩

end Map

/-- The interpretation of every sentence on a map with step length `T`, fixed once. Decay rates are
per unit time: `decay a` asks for the factor `e^{-a T}` per step. -/
def Flow.Property.holdsMap {n : ℕ} :
    Flow.Property → ℝ → (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) → Prop
  | .lyapunovStable, _ => Map.LyapunovStable
  | .locallyAsymptoticallyStable, _ => Map.LocalAsymptoticStable
  | .locallyExponentiallyStable, _ => Map.LocallyExponentiallyStable
  | .globallyAsymptoticallyStable, _ => Map.GloballyAsymptoticallyStable
  | .globallyExponentiallyStable, _ => Map.GloballyExponentiallyStable
  | .unstable, _ => Map.Unstable
  | .decay a, T => fun F x => Map.Decay F x (a * T)
  | .contractive, _ => Map.SampledContraction
  | .conservative, _ => Map.Conservative

end powerlib
