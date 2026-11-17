{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Drives.IMCCurrentLoop where
-- Lean modules: theorem.Drives.CascadeControl

-- Scaffold of the machine-drive IMC current loop as a parameterization of the converter PI current
-- loop (`CurrentControl.PIParams.family` of `theorem/GridTiedConverter/CurrentControl/PILoop.lean`,
-- the hub). The drive loops of `theorem/Drives/CascadeControl.lean` (plant inductance `L`,
-- resistance `R`, bandwidth `α`) have no family of their own: the parameter map
-- `IMCLoop.toPIParams` sends a drive loop to the converter loop with the IMC tuning `K_p = L α`,
-- `K_i = R α` (`CurrentControl.imc`), and the drive loops read as the hub pulled back along it
-- (`comap`), so every hub result is a drive result at the image without restatement
-- (`CurrentControl.imc_mem_den_iff`). The physical drive loop `L di/dt = v − R i` closed by the
-- PI is a system only for `L ≠ 0`; there it is the hub plant of the image (`sameSystem`, Lean
-- `CurrentControl.PIParams.model_field`), so it satisfies exactly the sentences of the image
-- (`driveReading`). The slice `L = 0` is not a drive loop: the scaffold gives it no physical
-- system and the pull-back says nothing about it. The plants are taken abstractly. Nothing here
-- is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (Sc : Scalars) where
  open Scalars Sc

  record IMCLoop : Type where
    constructor imcLoop
    field
      L R α : ℝ

  record PIParams : Type where
    constructor piParams
    field
      L R Kp Ki : ℝ

  -- The parameter map: the IMC tuning of the converter PI loop (Lean `IMCLoop.toPIParams`).
  toPI : IMCLoop → PIParams
  toPI m =
    piParams (IMCLoop.L m) (IMCLoop.R m) (IMCLoop.L m * IMCLoop.α m) (IMCLoop.R m * IMCLoop.α m)

  NonzeroInductance : IMCLoop → Type
  NonzeroInductance m = ¬ (IMCLoop.L m ≡ 0r)

  -- The plants, abstractly, with their satisfaction of sentences; the hub with its requirement
  -- language; the physical drive loop, a system only for a nonzero inductance.
  module Reading (Plant : Type) (holds : Plant → Sentence → Type)
    (PReq : Type) (piPlant : PIParams → Plant) (piMeets : PIParams → PReq → Type)
    (piTranslate : Sentence → PReq → Type)
    (driveSystem : (m : IMCLoop) → NonzeroInductance m → Plant)
    where

    plantSemantics : Semantics
    plantSemantics = record { System = Plant ; Sentence = Sentence ; holds = holds }

    open Readings plantSemantics

    converterFamily : Family
    converterFamily = record
      { Model = PIParams ; Req = PReq ; system = piPlant ; meets = piMeets
      ; translate = piTranslate }

    -- The drive loops read as the converter loop: no semantics of their own.
    driveFamily : Family
    driveFamily = comap converterFamily toPI

    -- What Lean proves (`CurrentControl.PIParams.model_field`, by field arithmetic).
    record Obligations : Type where
      field
        sameSystem : (m : IMCLoop) (h : NonzeroInductance m) → driveSystem m h ≡ piPlant (toPI m)

    module _ (ob : Obligations) where
      open Obligations ob

      -- A physical drive loop satisfies exactly the sentences of its image in the hub.
      driveReading : (m : IMCLoop) (h : NonzeroInductance m) →
        (s : Sentence) → holds (driveSystem m h) s ≃ holds (piPlant (toPI m)) s
      driveReading m h s = pathToEquiv (cong (λ a → holds a s) (sameSystem m h))

      -- Members of the hub at the image pass to the physical loop (Lean: the attractive sentences
      -- from `CurrentControl.imc_mem_den_iff`).
      mem-den : (m : IMCLoop) (h : NonzeroInductance m) (s : Sentence) →
        den driveFamily s m → holds (driveSystem m h) s
      mem-den m h s d = invEq (driveReading m h s) d
