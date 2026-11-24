{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Numerics.EulerPorts where
-- Lean modules: theorem.Numerics.EulerPorts theorem.Passive.PortEuler theorem.GridTiedConverter.GFL.DCLink.PortEuler theorem.PowerSystem.Synchronous.PortEuler theorem.GridTiedConverter.PLL.PortEuler theorem.GridTiedConverter.GFM.Discrete.LinearPort

-- Scaffold of the explicit Euler implementation of models with ports: the model is a port system
-- `ẋ = f(x, u)`, `y = g(x, u)`; its implementation with step `h > 0` is the discrete port system
-- `x⁺ = x + h f(x, u)` with the same output, read with step length `h`, and realizes the model it
-- is designed from (`ofDesign`). Three readings carry it. The flow sentences read the zero-input
-- dynamics on both sides, and the zero-input map of the Euler system is the Euler map of the
-- zero-input field, so the implementation reads through the autonomous Euler implementation of the
-- zero-input family (`flow-reading`), and the small-step and large-step laws of
-- `theorem/Numerics/EulerDiscretization.agda` carry over. Passivity does not: when the output does
-- not depend on the input and is not zero at some state, one Euler step with a large input against
-- the output draws unbounded energy, so no storage makes the discrete system passive at any step;
-- a passive model of that kind (the integrator `ẋ = u`, `y = x`, an RL branch, a classical
-- machine) refutes realization soundness for passivity at every step (`not-sound-passive`). For a
-- strictly proper linear plant this holds exactly when the output map is not zero
-- (`StrictlyProper`, `not-den-passive`, `not-sound-passive-of`). For linear plants the zero-input
-- Euler map is `I + hA`, and a multiplier `1 + hλ` inside the unit disk forces `Re λ < 0`: an
-- implementation satisfying an attractive sentence at any step certifies its design model
-- (`complete-linear`), and with the small-step law the realization is exact below a threshold. The
-- contrast is the implicit midpoint (Tustin) implementation of a plant, `x⁺ − x = h (A x̄ + B u)`,
-- output at the midpoint `x̄ = (x + x⁺)/2`: with a KYP certificate of the design plant and a
-- well-posed step it is passive with the same storage at every step (`Midpoint`,
-- `passive-midpoint`). The Euler step commutes with linear changes of state coordinates, which
-- preserve passivity in continuous and in discrete time, so these passivity laws read through
-- such a change (as in `theorem/GridTiedConverter/GFM/Discrete/SwingPortMachine.agda`). Lean
-- (`theorem/Numerics/EulerPorts.lean`): `flow-reading` is
-- `Numerics.eulerPorts_realizationSoundUnder_flow_iff` (with `eulerPortFamily_den_flow`), the flow
-- laws `Numerics.eulerPorts_sound_small_step_local` and
-- `Numerics.not_eulerPorts_realizationSoundUnder_of_large_step_local`, `not-passive` is
-- `Numerics.not_passive_eulerSystem` (witness `not_passive_eulerSystem_integrator`),
-- `not-sound-passive` is `Numerics.not_eulerPorts_realizationSoundUnder_passive`,
-- `euler-not-passive` is `Numerics.not_passive_eulerSystem_plant_iff` (the family form
-- `Numerics.eulerPortFamily_not_mem_den_passive_linear`), `complete-linear` is
-- `Numerics.eulerPorts_realizationCompleteUnder_linear` (exactness
-- `eulerPorts_exact_small_step_linear`), `midpoint-passive` is
-- `Numerics.midpointSystem_passiveWith` and `passive-midpoint` is
-- `Numerics.midpointPortFamily_mem_den_passive` (the template `Numerics.midpointPortFamily`); the
-- commutation is `Numerics.eulerSystem_conjugate`, the
-- invariance `Map.System.passive_conjugate_iff`, `Port.System.passive_conjugate_iff`. The
-- discrete-gradient step, the scheme that keeps the energy balance of a pH system, is passive
-- (`Numerics.discreteGradient_passiveWith`), and a discrete system that draws unbounded energy
-- along a closed loop is not (`Map.System.not_passive_of_feedback_supply_unbounded`). These laws
-- are connection statements over arbitrary families with ports. The `PortEuler` modules of
-- `Passive` (RL, LCL), `GridTiedConverter/GFL/DCLink` (the linearized cascade),
-- `PowerSystem/Synchronous` (classical machine, seventh-order machine, SMIB) and
-- `GridTiedConverter/PLL` (port-Hamiltonian PLL) define each family's Euler implementation and
-- state what needs the family's own witness: the loss of passivity and the large-step instability.
-- `GridTiedConverter/GFM/Discrete/LinearPort` defines the Euler and midpoint implementations of the
-- linearized grid-forming port plants (swing, VSM + filter): no Euler implementation is passive
-- (`GFM.SwingPort.linearEuler_not_mem_den_passive`,
-- `GFM.FilterPort.linearEuler_not_mem_den_passive`) and the midpoint implementations of the
-- passive plants are passive (`GFM.SwingPort.linearMidpoint_mem_den_passive`,
-- `GFM.FilterPort.linearMidpoint_mem_den_passive`).
-- The nonlinear grid-forming swing port reads its Euler law from the classical machine's
-- (`theorem/GridTiedConverter/GFM/Discrete/SwingPortMachine.agda`), and its discrete-gradient
-- discretizations are passive exactly at the matched set-point (`GFM.SwingPort.dg_passive`,
-- `GFM.SwingPort.dg_not_passive`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading
open import theorem.Stack.Realization

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (Model Step : Type)
    (portSystem : Model → System) (eulerSystem : Step → Model → System)
    -- The autonomous Euler implementation of the zero-input family.
    (zeroEuler : Step → Model → System)
    (Flow Attractive : Sentence → Type) (passive : Sentence)
    -- What Lean proves.
    (flow-reading : (s : Sentence) → Flow s → (h : Step) (m : Model) →
      holds (eulerSystem h m) s ↔ holds (zeroEuler h m) s)
    (not-passive : Σ[ m ∈ Model ] holds (portSystem m) passive ×
      ((h : Step) → ¬ holds (eulerSystem h m) passive))
    (step : Step)
    where

    model : Family
    model = record
      { Model = Model ; Req = ⊥ ; system = portSystem ; meets = λ _ () ; translate = λ _ () }

    implementation : Family
    implementation = record
      { Model = Model × Step ; Req = ⊥ ; system = λ y → eulerSystem (snd y) (fst y)
      ; meets = λ _ () ; translate = λ _ () }

    zeroImplementation : Family
    zeroImplementation = record
      { Model = Model × Step ; Req = ⊥ ; system = λ y → zeroEuler (snd y) (fst y)
      ; meets = λ _ () ; translate = λ _ () }

    open Design model implementation fst

    -- The flow sentences of the implementation are those of the autonomous Euler implementation
    -- of the zero-input family.
    flow↔ : (s : Sentence) → Flow s → (y : Model × Step) →
      den implementation s y ↔ den zeroImplementation s y
    flow↔ s f (m , h) = flow-reading s f h m

    -- Passivity is not realized at any step.
    not-sound-passive : ¬ SoundUnder designed (λ _ → ⊥) passive
    not-sound-passive =
      let (m , hm , hn) = not-passive
      in not-sound-of-witness designed (m , step) (λ _ ())
        (snd (certified↔ passive (m , step)) hm) (hn step)

    -- Linear plants: an implementation satisfying an attractive sentence certifies its model.
    module Linear (linear : (s : Sentence) → Attractive s → (h : Step) (m : Model) →
        holds (eulerSystem h m) s → holds (portSystem m) s) where

      complete-linear : (s : Sentence) → Attractive s →
        CompleteUnder designed (λ _ → ⊥) s
      complete-linear s a (m , h) _ d = snd (certified↔ s (m , h)) (linear s a h m d)

    -- Strictly proper linear plants with a nonzero output map (`Observed`): no Euler
    -- implementation is passive, so a passive such model refutes realization soundness for
    -- passivity.
    module StrictlyProper (Observed : Model → Type)
      (euler-not-passive : (m : Model) → Observed m → (h : Step) →
        ¬ holds (eulerSystem h m) passive)
      where

      not-den-passive : (y : Model × Step) → Observed (fst y) → ¬ den implementation passive y
      not-den-passive (m , h) o = euler-not-passive m o h

      not-sound-passive-of : (m : Model) → Observed m → holds (portSystem m) passive →
        ¬ SoundUnder designed (λ _ → ⊥) passive
      not-sound-passive-of m o p = not-sound-of-witness designed (m , step) (λ _ ())
        (snd (certified↔ passive (m , step)) p) (euler-not-passive m o step)

    -- The contrast: the implicit midpoint implementation of the plants. A certificate of the
    -- design plant (a KYP storage) and a well-posed step make it passive.
    module Midpoint (midpointSystem : Step → Model → System)
      (Certificate : Model → Type) (WellPosed : Step → Model → Type)
      (midpoint-passive : (h : Step) (m : Model) → Certificate m → WellPosed h m →
        holds (midpointSystem h m) passive)
      where

      midpointImplementation : Family
      midpointImplementation = record
        { Model = Model × Step ; Req = ⊥ ; system = λ y → midpointSystem (snd y) (fst y)
        ; meets = λ _ () ; translate = λ _ () }

      -- A certified design and a well-posed step place the midpoint implementation in passivity,
      -- where its Euler implementation may be passive at no step (`not-sound-passive`).
      passive-midpoint : (y : Model × Step) → Certificate (fst y) → WellPosed (snd y) (fst y) →
        den midpointImplementation passive y
      passive-midpoint (m , h) c w = midpoint-passive h m c w
