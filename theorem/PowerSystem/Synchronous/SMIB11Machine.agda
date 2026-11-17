{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.PowerSystem.Synchronous.SMIB11Machine where
-- Lean modules: theorem.PowerSystem.Synchronous.SMIB11PH

-- Scaffold of the machine block of the 11-state single-machine system (`Synchronous.smib11` of
-- `theorem/PowerSystem/Synchronous/SMIB11PH.lean`) as the seven-state machine
-- (`Synchronous.syncMachine7`, `theorem/PowerSystem/Synchronous/PH.lean`). The parameters of the
-- 11-state system extend the machine's (`Synchronous.SMIB11Params` extends
-- `Synchronous.SyncMachine7Params`) with the node capacitor, the RL link and the frame speed; the
-- state of the machine is the block `(Ψ, p, δ)` of the 11-state state (`machineBlock`,
-- `Synchronous.smib11_machine`). On that block the 11-state field is the machine field driven by
-- the node voltage in the rotor frame, `R(δ)ᵀ (q_D, q_Q)/C`, the field voltage and the
-- mechanical torque (`machineInput`, `Synchronous.smib11_machineInput`; `machineField`), and the
-- 11-state storage is the machine storage at the block plus the node-capacitor and link energies
-- (`storage`). Both families are passivity-only (`Family.passiveOnly`) and prove passivity from a
-- lower bound of their storage; the 11-state bound is the machine's plus the nonnegative node and
-- link energies (`storage-nonneg`). Lean: `machineField` is `Synchronous.smib11_field_machine`,
-- `storage` is `Synchronous.smib11_H`, `machine-nonneg` is `Synchronous.syncMachine7_H_nonneg`,
-- `storage-nonneg` is `Synchronous.smib11_H_nonneg`; the passivity statements it bounds are
-- `Synchronous.SyncMachine7.mem_den_passive` and `Synchronous.SMIB11.mem_den_passive`. Nothing
-- here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import theorem.Flow.FlowSemantics

module _ (Sc : Scalars) where
  open Scalars Sc

  -- The seven-state machine: inverse inductance `Γ` (abstract), inertia, resistances, damping.
  record SyncMachine7Params (Mat₅ : Type) : Type where
    field
      Γ : Mat₅
      M rs rf rkd rkq D : ℝ

  -- The 11-state system extends the machine with the node, the link and the frame speed.
  record SMIB11Params (Mat₅ : Type) : Type where
    field
      machine : SyncMachine7Params Mat₅
      C Ll rl ωs : ℝ

  module Blocks (Mat₅ State₇ State₁₁ Input₇ Input₁₁ : Type)
    (machineBlock : State₁₁ → State₇)
    (machineInput : SMIB11Params Mat₅ → State₁₁ → Input₁₁ → Input₇)
    (field₇ : SyncMachine7Params Mat₅ → State₇ → Input₇ → State₇)
    (field₁₁ : SMIB11Params Mat₅ → State₁₁ → Input₁₁ → State₁₁)
    (H₇ : SyncMachine7Params Mat₅ → State₇ → ℝ)
    (H₁₁ node link : SMIB11Params Mat₅ → State₁₁ → ℝ)
    where

    open SMIB11Params

    -- What Lean proves by computation on the pH matrices.
    record Obligations : Type where
      field
        machineField : (p : SMIB11Params Mat₅) (x : State₁₁) (u : Input₁₁) →
          machineBlock (field₁₁ p x u) ≡ field₇ (machine p) (machineBlock x) (machineInput p x u)
        storage : (p : SMIB11Params Mat₅) (x : State₁₁) →
          H₁₁ p x ≡ (H₇ (machine p) (machineBlock x) + node p x) + link p x

    -- The lower bound of the 11-state storage from the machine's and the node and link energies
    -- (the scalar law `add-nonneg` is the one fact used).
    module _ (ob : Obligations) (add-nonneg : (a b : ℝ) → 0r ≤ a → 0r ≤ b → 0r ≤ a + b)
      (machine-nonneg : (q : SyncMachine7Params Mat₅) (y : State₇) → 0r ≤ H₇ q y)
      (node-nonneg : (p : SMIB11Params Mat₅) (x : State₁₁) → 0r ≤ node p x)
      (link-nonneg : (p : SMIB11Params Mat₅) (x : State₁₁) → 0r ≤ link p x)
      where

      storage-nonneg : (p : SMIB11Params Mat₅) (x : State₁₁) → 0r ≤ H₁₁ p x
      storage-nonneg p x = subst (0r ≤_) (sym (Obligations.storage ob p x))
        (add-nonneg _ _
          (add-nonneg _ _ (machine-nonneg (machine p) (machineBlock x)) (node-nonneg p x))
          (link-nonneg p x))
