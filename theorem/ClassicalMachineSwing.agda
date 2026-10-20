{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.ClassicalMachineSwing where

-- Scaffold of the reading of the classical synchronous machine through the swing hub
-- (`ClassicalSM.family` of `theorem/Synchronous/PH.lean` read through `Synchronous.Swing.family`).
-- The port-Hamiltonian machine `δ̇ = p/M`, `ṗ = P_m − b sin δ − D p/M (+ u)` at `(δ*, 0)` is, on
-- its zero-input field, the swing machine `⟨M, D, P_m, 0, b, 0⟩` in the momentum coordinate `p = M
-- ω`. Its parameters carry `M > 0`, `D ≥ 0`, `b > 0`, so every model maps into the swing context
-- `{inertia, curved}` and exactness, not only exactness within a context, passes. Only the flow
-- sentences are read: passivity is read on the machine's port, which the swing family does not
-- have, and stays a law of the machine (`ClassicalSM.exact_passive`). Lean proves the conjugacy
-- (`mem_den_flow_iff_swing`, through `Spectral.mem_den_flow_iff_of_transport` with `T = diag(1,
-- M)`), the requirement correspondence (`realize_translate_flow_eq_preimage`) and the transfer
-- (`Spectral.exact_of_hub`, `Spectral.sound_of_hub`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics
open import theorem.Swing

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  record MachineParams : Type where
    constructor machineParams
    field
      M D b Pm : ℝ
      M-pos : 0r < M
      D-nonneg : 0r ≤ D
      b-pos : 0r < b

  record MachineModel : Type where
    constructor machineModel
    field
      p : MachineParams
      δs : ℝ

  open MachineParams
  open MachineModel

  -- The zero-input field in the coordinates `(δ, p)` and the selected point `(δ*, 0)`.
  machineField : MachineParams → ℝ × ℝ → ℝ × ℝ
  machineField q (δ , π) = π / M q , ((Pm q - b q * sin δ) - D q * (π / M q))

  machineSystem : MachineModel → System (ℝ × ℝ)
  machineSystem m = machineField (p m) , (δs m , 0r)

  data MachineReq : Type where
    locked stableBranch damped' unstableBranch noPower : MachineReq

  machineMeets : MachineModel → MachineReq → Type
  machineMeets m locked = b (p m) * sin (δs m) ≡ Pm (p m)
  machineMeets m stableBranch = 0r < cos (δs m)
  machineMeets m damped' = (0r < D (p m)) × (0r < cos (δs m))
  machineMeets m unstableBranch = cos (δs m) < 0r
  machineMeets m noPower = Pm (p m) ≡ 0r

  machineLS machineLocal machineUnstable machinePassive : MachineReq → Type
  machineLS locked = Unit
  machineLS stableBranch = Unit
  machineLS _ = ⊥
  machineLocal locked = Unit
  machineLocal damped' = Unit
  machineLocal _ = ⊥
  machineUnstable locked = Unit
  machineUnstable unstableBranch = Unit
  machineUnstable _ = ⊥
  machinePassive noPower = Unit
  machinePassive _ = ⊥

  machineTranslate : Sentence → MachineReq → Type
  machineTranslate = localTable machineLS machineLocal machineUnstable machinePassive

  -- The map of models and the momentum coordinate `(δ, ω) ↦ (δ, M ω)`.
  toSwing : MachineModel → SwingModel
  toSwing m = swingModel (swingParams (M (p m)) (D (p m)) (Pm (p m)) 0r (b (p m)) 0r) (δs m)

  momentum : MachineModel → Affine (ℝ × ℝ)
  momentum m = record
    { point = λ { (δ , ω) → δ , (M (p m) * ω) }
    ; pointInv = λ { (δ , π) → δ , (π / M (p m)) }
    ; vector = λ { (a , c) → a , (M (p m) * c) } }

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    (laws : SwingFamily.SwingLaws holds invariant)
    where

    open SwingFamily holds invariant

    machineFamily : Family
    machineFamily = record
      { Model = MachineModel ; Req = MachineReq ; system = machineSystem ; meets = machineMeets
      ; translate = machineTranslate }

    -- What Lean proves by field arithmetic (with `M > 0`, `b > 0`).
    record Obligations : Type where
      field
        conjugate : (m : MachineModel) (s : Sentence) → Flow s →
          holds (machineSystem m) s ≃
            holds (transportSystem (momentum m) (swingSystem (toSwing m))) s
        inContext : (m : MachineModel) → realize swingFamily (both inertia curved) (toSwing m)
        local↔ : (m : MachineModel) →
          realize machineFamily machineLocal m ↔ realize swingFamily swingLocal (toSwing m)
        lyapunov↔ : (m : MachineModel) →
          realize machineFamily machineLS m ↔ realize swingFamily swingLS (toSwing m)

    module _ (ob : Obligations) where
      open Obligations ob

      reading : PartialHub Flow machineFamily swingFamily
      reading = partialConjugacy affine Flow toSwing momentum conjugate

      inertiaOf : (m : MachineModel) → realize swingFamily (only inertia) (toSwing m)
      inertiaOf m r e = inContext m r (inl e)

      -- Exactness of the local sentences for every machine (Lean
      -- `ClassicalSM.exact_locallyExponentiallyStable`, `exact_locallyAsymptoticallyStable`,
      -- `exact_lyapunovStable`).
      exact-les : Exact machineFamily locallyExponentiallyStable
      exact-les = exact-pullback reading tt inertiaOf local↔
        (SwingFamily.SwingLaws.exactUnder-les laws)

      exact-las : Exact machineFamily locallyAsymptoticallyStable
      exact-las = exact-pullback reading tt inertiaOf local↔
        (SwingFamily.SwingLaws.exactUnder-las laws)

      exact-ls : Exact machineFamily lyapunovStable
      exact-ls = exact-pullback reading tt inContext lyapunov↔
        (SwingFamily.SwingLaws.exactUnder-ls laws)
