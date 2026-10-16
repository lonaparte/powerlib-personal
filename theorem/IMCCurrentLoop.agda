{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.IMCCurrentLoop where

-- Scaffold of the reading of the machine-drive IMC current loop through the converter PI current
-- loop (`Drives.CascadeControl.family` of `theorem/Drives/CascadeControl.lean` read through
-- `CurrentControl.PIParams.family` of `theorem/CurrentControl/PILoop.lean`). The drive loop with
-- plant inductance `L`, resistance `R` and bandwidth `α` is, for `L ≠ 0`, the same linear plant as
-- the converter PI loop with the IMC tuning `K_p = L α`, `K_i = R α` (`CurrentControl.imc`), so the
-- reading is an equality of systems on the models with `L ≠ 0`, a context on the parameters. Both
-- families keep the two-element language `{stable, unstable}`. The scaffold derives the reading of
-- every sentence and the transfer of members; the plants are taken abstractly. Lean proves the
-- equality of plants (`imcModel_eq`), the reading (`mem_den_iff_imc`) and the member transfer
-- (`mem_den` from `CurrentControl.imc_mem_den_iff`). The families' own soundness and exactness are
-- not transferred: a loop with `L = 0` has no reading. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics

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

  -- The IMC tuning of the converter PI loop (Lean `CurrentControl.imc`).
  imc : IMCLoop → PIParams
  imc m =
    piParams (IMCLoop.L m) (IMCLoop.R m) (IMCLoop.L m * IMCLoop.α m) (IMCLoop.R m * IMCLoop.α m)

  data LinearReq : Type where
    stable unstable' : LinearReq

  -- The table of `Spectral.linearFamily`: the attractive sentences to `stable`, instability to
  -- `unstable`.
  linearTranslate : Sentence → LinearReq → Type
  linearTranslate unstable unstable' = Unit
  linearTranslate unstable stable = ⊥
  linearTranslate passive _ = ⊥
  linearTranslate _ stable = Unit
  linearTranslate _ unstable' = ⊥

  -- The plants, abstractly, with their satisfaction of sentences.
  module Reading (Plant : Type) (holds : Plant → Sentence → Type)
    (imcPlant : IMCLoop → Plant) (piPlant : PIParams → Plant)
    (imcMeets : IMCLoop → LinearReq → Type) (piMeets : PIParams → LinearReq → Type)
    where

    linearSemantics : Semantics
    linearSemantics = record { System = Plant ; Sentence = Sentence ; holds = holds }

    open Readings linearSemantics

    driveFamily converterFamily : Family
    driveFamily = record
      { Model = IMCLoop ; Req = LinearReq ; system = imcPlant ; meets = imcMeets
      ; translate = linearTranslate }
    converterFamily = record
      { Model = PIParams ; Req = LinearReq ; system = piPlant ; meets = piMeets
      ; translate = linearTranslate }

    NonzeroInductance : IMCLoop → Type
    NonzeroInductance m = ¬ (IMCLoop.L m ≡ 0r)

    -- What Lean proves (`imcModel_eq`, by field arithmetic).
    module _ (samePlant : (m : IMCLoop) → NonzeroInductance m → imcPlant m ≡ piPlant (imc m)) where

      reading : Hub (restrictBy driveFamily NonzeroInductance) converterFamily
      reading = viaEquality (λ x → imc (fst x)) (λ x → samePlant (fst x) (snd x))

      -- Every sentence of a drive loop with `L ≠ 0` is the sentence of its converter form (Lean
      -- `mem_den_iff_imc`).
      den≃ : (m : IMCLoop) → NonzeroInductance m → (s : Sentence) →
        den driveFamily s m ≃ den converterFamily s (imc m)
      den≃ m h s = Hub.read reading (m , h) s

      -- Members pass back (Lean `mem_den` from `CurrentControl.imc_mem_den_iff`).
      mem-den : (m : IMCLoop) → NonzeroInductance m → (s : Sentence) →
        den converterFamily s (imc m) → den driveFamily s m
      mem-den m h s = invEq (den≃ m h s)
