{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.EulerPorts where

-- Scaffold of the explicit Euler implementation of models with ports: the model is a port system
-- `ẋ = f(x, u)`, `y = g(x, u)`; its implementation with step `h > 0` is the discrete port system
-- `x⁺ = x + h f(x, u)` with the same output, read with step length `h`, and realizes the model it
-- is designed from (`ofDesign`). Three readings carry it. The flow sentences read the zero-input
-- dynamics on both sides, and the zero-input map of the Euler system is the Euler map of the
-- zero-input field, so the implementation reads through the autonomous Euler implementation of the
-- zero-input family (`flow-reading`), and the small-step and large-step laws of
-- `theorem/EulerDiscretization.agda` carry over. Passivity does not: when the output does not
-- depend on the input and is not zero at some state, one Euler step with a large input against the
-- output draws unbounded energy, so no storage makes the discrete system passive at any step; a
-- passive model of that kind (the integrator `ẋ = u`, `y = x`, an RL branch, a classical machine)
-- refutes realization soundness for passivity at every step (`not-sound-passive`). For linear
-- plants the zero-input Euler map is `I + hA`, and a multiplier `1 + hλ` inside the unit disk
-- forces `Re λ < 0`: an implementation satisfying an attractive sentence at any step certifies its
-- design model (`complete-linear`), and with the small-step law the realization is exact below a
-- threshold. Lean (`theorem/Numerics/EulerPorts.lean`): `flow-reading` is
-- `Numerics.eulerPorts_realizationSoundUnder_flow_iff` (with `eulerPortFamily_den_flow`), the flow
-- laws `Numerics.eulerPorts_sound_small_step_local` and
-- `Numerics.not_eulerPorts_realizationSoundUnder_of_large_step_local`, `not-passive` is
-- `Numerics.not_passive_eulerSystem` (witness `not_passive_eulerSystem_integrator`),
-- `not-sound-passive` is `Numerics.not_eulerPorts_realizationSoundUnder_passive`, `complete-linear`
-- is `Numerics.eulerPorts_realizationCompleteUnder_linear` (exactness
-- `eulerPorts_exact_small_step_linear`); the passivity of the discrete-gradient step, the scheme
-- that does keep the energy balance, is `Numerics.discreteGradient_passiveWith`. These laws are
-- connection statements over arbitrary families with ports. The `PortEuler` modules of `Circuits`
-- (RL, LCL), `GFL/DCLink` (the linearized cascade), `Synchronous` (classical machine, seventh-order
-- machine, SMIB) and `PLL` (port-Hamiltonian PLL) define each family's Euler implementation and
-- state what needs the family's own witness: the loss of passivity and the large-step instability.
-- Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.Realization

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
