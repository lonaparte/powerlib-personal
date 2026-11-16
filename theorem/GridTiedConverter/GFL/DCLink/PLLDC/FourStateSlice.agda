{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFL.DCLink.PLLDC.FourStateSlice where
-- Lean modules: theorem.GridTiedConverter.GFL.DCLink.PLLDC.FourStateSlice

-- Scaffold of the four-state reading of the PLL–DC model inside its own family (`PLLDC.family` of
-- `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`), on the slice where a PLL–DC
-- system is a four-state GFL model: no line resistance, no reactive current, unit DC-voltage
-- reference, `V_dc* = 1` and `ω_s − ω_g + k_i x_pll* = 0` (every equilibrium of the parameter
-- slice has the last two, `PLLDC.Params.equilibrium_Vdc`, `PLLDC.Params.equilibrium_ki_xpll`).
-- The slice is a predicate on the parameters and the selected state, not a requirement of the
-- PLL–DC model. A model of the slice reads as a four-state model (`PLLDC.Model.toFourState`,
-- parameters `PLLDC.Params.fourStateParams` with the reference offset `i_d0 + k_iv ξ_v*`), and
-- that model reads back into the PLL–DC model (`FourState.Model.toPLLDC`, the parameterization of
-- `theorem/GridTiedConverter/GFL/DCLink/FourStatePLLDC.agda`) about the operating point
-- `(Δθ*, 0, 1, 0)`. The round trip is a change of representation inside the PLL–DC model: the
-- integrator states `x_pll*`, `ξ_v*` of the selected point become the frequency offset and the
-- reference offset, and the two systems are equal (`sameSystem`; Lean
-- `PLLDC.Params.field_eq_transport` with `FourState.field_eq_transport`), so the two models
-- satisfy the same sentences (`den↔`, Lean `PLLDC.mem_den_iff_fourState`). The basin-guard carrier
-- reads through this slice (`theorem/GridTiedConverter/GFL/DCLink/BasinGuardFourState.agda`).
-- Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (X : Type) (holds : System X → Sentence → Type)
  (invariant : (A : Affine X) (a : System X) (s : Sentence) →
    holds (transportSystem A a) s ≃ holds a s)
  where

  open Flows X holds invariant

  module _ (PModel FourModel PReq : Type)
    (pSystem : PModel → System X)
    (pMeets : PModel → PReq → Type) (pTranslate : Sentence → PReq → Type)
    -- The four-state reading of a PLL–DC system and the parameterization back into the PLL–DC
    -- model.
    (toFour : PModel → FourModel) (fourToP : FourModel → PModel)
    -- The slice with its point conditions.
    (Slice : PModel → Type)
    where

    pFamily : Family
    pFamily = record
      { Model = PModel ; Req = PReq ; system = pSystem ; meets = pMeets
      ; translate = pTranslate }

    -- The round trip through the four-state parameters.
    roundTrip : PModel → PModel
    roundTrip b = fourToP (toFour b)

    -- What Lean proves.
    record Obligations : Type where
      field
        sameSystem : (b : PModel) → Slice b → pSystem b ≡ pSystem (roundTrip b)

    module _ (ob : Obligations) where
      open Obligations ob

      reading : Hub (restrictBy pFamily Slice) pFamily
      reading = viaEquality (λ x → roundTrip (fst x)) (λ x → sameSystem (fst x) (snd x))

      -- On the slice a model and the image of its four-state reading agree on every sentence.
      den↔ : (b : PModel) → Slice b → (s : Sentence) → den pFamily s b ↔ den pFamily s (roundTrip b)
      den↔ b c s = ↔-of-≃ (Hub.read reading (b , c) s)
