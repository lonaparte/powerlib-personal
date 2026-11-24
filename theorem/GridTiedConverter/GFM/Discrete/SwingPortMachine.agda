{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.Discrete.SwingPortMachine where
-- Lean modules: theorem.GridTiedConverter.GFM.Discrete.SwingPort

-- Scaffold of the reading of the grid-forming swing synchronization with a power port
-- (`GFM.SwingPort.family` of `theorem/GridTiedConverter/GFM/Discrete/SwingPort.lean`) through the
-- classical machine on an infinite bus (`Synchronous.ClassicalSM.family`), and of their explicit
-- Euler discretizations. The GFM model `δ̇ = Δω`, `M Δω̇ = P_ref + u − c₀ − A sin(δ − α) − D Δω`,
-- output `Δω`, at `(δ*, 0)` is the machine `⟨M, D, A, P_ref − c₀⟩` at the angle `δ* − α` in the
-- momentum coordinate `p = M Δω`: its port system is the machine's conjugated by that change of
-- coordinates, with the same input and output. Satisfaction of every sentence — the flow
-- sentences and passivity — is invariant under the conjugation, so the reading is a hub for every
-- sentence (`viaConjugacy`). The spoke keeps the hub's requirement language (read through the map
-- of models), so soundness and exactness pass sentence by sentence. The explicit Euler step
-- commutes with the change of coordinates, so the Euler discretizations with the same step read
-- through each other as well, and the machine's law that no discretization is passive carries
-- over. Lean proves the conjugacy (`GFM.SwingPort.system_eq_conjugate`), the reading
-- (`GFM.SwingPort.mem_den_iff_classicalSM`, through `Spectral.mem_den_flow_iff_of_transport` and
-- `Port.System.passive_conjugate_iff`), the transfers (`GFM.SwingPort.chain_le_semantics`,
-- `GFM.SwingPort.exact_passive`, `GFM.SwingPort.mem_den_passive_iff`), the commutation
-- (`Numerics.eulerSystem_conjugate`, `Map.System.passive_conjugate_iff`), the Euler reading
-- (`GFM.SwingPort.euler_mem_den_passive_iff_classicalSM`) and the transferred law
-- (`GFM.SwingPort.euler_not_mem_den_passive`, from
-- `Synchronous.ClassicalSM.euler_not_mem_den_passive`; the realization conclusion
-- `GFM.SwingPort.not_euler_realizationSoundUnder_passive`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading

module _ (S : Semantics) where
  open Semantics S
  open Readings S

  module _ (SwingModel MachineModel Step Coord Req : Type)
    -- The map of models and the momentum coordinates of a model.
    (toMachine : SwingModel → MachineModel) (momentum : SwingModel → Coord)
    -- Transport of a system through a change of coordinates, and the satisfaction it preserves.
    (transport : Coord → System → System)
    (invariant : (c : Coord) (a : System) (s : Sentence) → holds (transport c a) s ≃ holds a s)
    -- The two port systems, the Euler discretization with a step, the machine's language.
    (swingSystem : SwingModel → System) (machineSystem : MachineModel → System)
    (euler : Step → System → System)
    (machineMeets : MachineModel → Req → Type) (translate : Sentence → Req → Type)
    -- What Lean proves.
    (conjugate : (m : SwingModel) →
      swingSystem m ≡ transport (momentum m) (machineSystem (toMachine m)))
    (commutes : (h : Step) (c : Coord) (a : System) →
      euler h (transport c a) ≡ transport c (euler h a))
    where

    invariance : Invariance
    invariance = record { Conj = Coord ; act = transport ; invariant = invariant }

    machineFamily : Family
    machineFamily = record
      { Model = MachineModel ; Req = Req ; system = machineSystem ; meets = machineMeets
      ; translate = translate }

    -- The spoke keeps the machine's language, read through the map of models.
    swingFamily : Family
    swingFamily = record
      { Model = SwingModel ; Req = Req ; system = swingSystem
      ; meets = λ m → machineMeets (toMachine m) ; translate = translate }

    reading : Hub swingFamily machineFamily
    reading = viaConjugacy invariance toMachine momentum conjugate

    -- Soundness and exactness pass sentence by sentence (Lean
    -- `GFM.SwingPort.chain_le_semantics`, `GFM.SwingPort.exact_passive`).
    sound : (s : Sentence) → Sound machineFamily s → Sound swingFamily s
    sound s = sound-pullback reading (λ x hx → hx)

    exact : (s : Sentence) → Exact machineFamily s → Exact swingFamily s
    exact s h x = ↔-trans (h (toMachine x)) (↔-of-≃ (invEquiv (Hub.read reading x s)))

    -- The Euler discretizations, a model and a step, with the language of their model.
    swingEuler machineEuler : Family
    swingEuler = record
      { Model = SwingModel × Step ; Req = Req ; system = λ y → euler (snd y) (swingSystem (fst y))
      ; meets = λ y → machineMeets (toMachine (fst y)) ; translate = translate }
    machineEuler = record
      { Model = MachineModel × Step ; Req = Req
      ; system = λ y → euler (snd y) (machineSystem (fst y))
      ; meets = λ y → machineMeets (fst y) ; translate = translate }

    eulerConjugate : (y : SwingModel × Step) →
      euler (snd y) (swingSystem (fst y)) ≡
        transport (momentum (fst y)) (euler (snd y) (machineSystem (toMachine (fst y))))
    eulerConjugate y = cong (euler (snd y)) (conjugate (fst y)) ∙
      commutes (snd y) (momentum (fst y)) (machineSystem (toMachine (fst y)))

    -- Lean `GFM.SwingPort.euler_mem_den_passive_iff_classicalSM` (for every sentence here).
    eulerReading : Hub swingEuler machineEuler
    eulerReading = viaConjugacy invariance (λ y → toMachine (fst y) , snd y)
      (λ y → momentum (fst y)) eulerConjugate

    -- A sentence no machine discretization satisfies is satisfied by no GFM discretization
    -- (Lean `GFM.SwingPort.euler_not_mem_den_passive` for passivity).
    not-den : (s : Sentence) → ((y : MachineModel × Step) → ¬ den machineEuler s y) →
      (y : SwingModel × Step) → ¬ den swingEuler s y
    not-den s h y p = h (toMachine (fst y) , snd y) (equivFun (Hub.read eulerReading y s) p)
