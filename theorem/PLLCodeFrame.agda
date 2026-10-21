{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.PLLCodeFrame where

-- Scaffold of the reading of the reduced PLL loop in the project-code frame through the PI-PLL
-- family (`GFL.LCLine.codeFamily` of `theorem/GFL/LCLine/Reduced2D.lean` read through
-- `PLL.PIPLL.family` of `theorem/PLL/PIPLLFamily.lean`). The project code writes the reduced loop
-- with the angle of the opposite sign: its detector is `h_c(θ) = h(−θ)`, and its field is the
-- text-frame field transported by the reflection `(θ, η) ↦ (−θ, η)` (work-sync `decisions.md`
-- §D1.4, corrected). A code model, parameters and a selected code angle `θ_c*`, describes the
-- PI-PLL member at the text angle `−θ_c*` (`toText`); the reflection carries that member's system,
-- field and selected point, to the code system (`conjugate`). So the code family reads through
-- the PI-PLL family by conjugacy, on every sentence (`reading`): its semantics is the PI-PLL
-- semantics pulled back along `toText` (`semantics-path`), a sentence holds of a code model
-- exactly when it holds of its text member (`den↔`), and, the code family keeping the PI-PLL
-- requirement language pulled back along `toText`, every sound PI-PLL translation stays sound
-- (`sound`). This is a reflection of the angle, not the reversal of currents and powers of
-- `theorem/CurrentDirection.agda`. Lean: `member` is `PLL.PIPLL.Model.field` with
-- `GFL.LCLine.Params.pllModel_field` and `Flow.Property.holds_shift_iff`; `field-eq` is
-- `GFL.LCLine.Params.codeField_eq_transport` (from `GFL.LCLine.Params.hCode_eq`); `point-eq` is the
-- image of the selected point under the reflection (inside `GFL.LCLine.codeFamily_den`); the
-- invariance is `Dynamics.holds_transport_iff` on the flow sentences, and passivity holds of both
-- families, which are autonomous. `den↔` with `semantics-path` is `GFL.LCLine.codeFamily_den` and
-- `GFL.LCLine.code_mem_den_iff`; `sound` is `GFL.LCLine.codeFamily_chain_le_semantics`, from
-- `PLL.PIPLL.chain_le_semantics`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import theorem.FamilyReading
open import theorem.FlowSemantics

module _ (Sc : Scalars) where
  open Scalars Sc

  -- The reflection `(θ, η) ↦ (−θ, η)`, its own inverse (Lean `reflect`).
  reflect : Affine (ℝ × ℝ)
  reflect = record
    { point = λ x → - fst x , snd x
    ; pointInv = λ y → - fst y , snd y
    ; vector = λ w → - fst w , snd w }

  -- The parameters of the reduced loop, its text-frame field (Lean `Params.reducedField`) and its
  -- code-frame field, written by the code's own formulas (Lean `Params.codeField`).
  module _ (Params : Type) (textField codeField : Params → ℝ × ℝ → ℝ × ℝ) where

    -- A code model: parameters and a selected code angle (Lean `CodeModel`).
    record CodeModel : Type where
      constructor codeModel
      field
        params : Params
        θc : ℝ

    open CodeModel

    -- The code system: the code field at `(θ_c*, 0)` (Lean `CodeModel.field`).
    codeSystem : CodeModel → System (ℝ × ℝ)
    codeSystem m = codeField (params m) , (θc m , 0r)

    -- The text system of its PI-PLL member: the text field at `(−θ_c*, 0)`.
    textSystem : CodeModel → System (ℝ × ℝ)
    textSystem m = textField (params m) , (- θc m , 0r)

    module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
      (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
        holds (transportSystem A a) s ≃ holds a s)
      where

      open Flows (ℝ × ℝ) holds invariant

      -- The PI-PLL family, abstractly, and the text member of a code model (Lean
      -- `CodeModel.toText`).
      module _ (piPLL : Family) (toText : CodeModel → Family.Model piPLL) where

        -- The code family: the code systems, with the PI-PLL requirement language pulled back
        -- along `toText` (Lean `codeFamily`).
        codeFamily : Family
        codeFamily = record
          { Model = CodeModel ; Req = Family.Req piPLL ; system = codeSystem
          ; meets = λ m → Family.meets piPLL (toText m) ; translate = Family.translate piPLL }

        -- What Lean proves.
        record Obligations : Type where
          field
            -- The text member of a code model reads its sentences on the text system.
            member : (m : CodeModel) (s : Sentence) →
              holds (Family.system piPLL (toText m)) s ≃ holds (textSystem m) s
            -- The code field is the reflected text field, and the code point the reflected text
            -- point.
            field-eq : (p : Params) (y : ℝ × ℝ) →
              codeField p y ≡ Affine.vector reflect (textField p (Affine.pointInv reflect y))
            point-eq : (m : CodeModel) → (θc m , 0r) ≡ Affine.point reflect (- θc m , 0r)

        module _ (ob : Obligations) where
          open Obligations ob

          -- The code system is the reflected text system.
          conjugate : (m : CodeModel) → codeSystem m ≡ transportSystem reflect (textSystem m)
          conjugate m i = funExt (field-eq (params m)) i , point-eq m i

          -- The code family reads through the PI-PLL family, on every sentence.
          reading : Hub codeFamily piPLL
          reading = record
            { map = toText
            ; read = λ m s →
                compEquiv (conjugateReading affine reflect (conjugate m) s)
                  (invEquiv (member m s)) }

          -- Its semantics is the PI-PLL semantics pulled back along `toText`.
          semantics-path : semantics codeFamily ≡ pulledBack reading
          semantics-path = readPath reading

          -- A sentence holds of a code model exactly when it holds of its text member.
          den↔ : (m : CodeModel) (s : Sentence) → den codeFamily s m ↔ den piPLL s (toText m)
          den↔ m s = ↔-of-≃ (Hub.read reading m s)

          -- Every sound translation of the PI-PLL family stays sound.
          sound : (s : Sentence) → Sound piPLL s → Sound codeFamily s
          sound s = sound-pullback reading (λ m h → h)
