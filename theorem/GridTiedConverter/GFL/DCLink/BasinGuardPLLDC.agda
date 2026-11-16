{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFL.DCLink.BasinGuardPLLDC where
-- Lean modules: theorem.GridTiedConverter.GFL.DCLink.BasinGuard

-- Scaffold of the basin-guard carrier as a parameterization of the PLL–DC model, the library's
-- single four-state DC-link model (`PLLDC.family` of
-- `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`). The carrier models of
-- `theorem/GridTiedConverter/GFL/DCLink/BasinGuard.lean` (parameters, a drop sign `s` and a
-- selected point) have no family of their own: the parameter map `CarrierParams.toPLLDC`
-- (`ω_s = ω_g = 1`, `V_dc* = 1`, gains `(K_p^pll, K_i^pll)`, `I₀ = I_dc`, `i_q0 = I_q*`, no
-- reference offset, line reactance `s X_g`) sends a carrier model to the PLL–DC system about the
-- same point (`BasinGuard.Model.toPLLDC`), and the sentences of a carrier model are those of its
-- image (`guardFamily` is the PLL–DC model pulled back along the map, `comap`). For every `I_q*`,
-- drop sign and point the carrier field is the PLL–DC field of the image, in the same coordinates
-- (`sameSystem`, Lean `CarrierParams.carrierField_eq_PLLDC_field`), so the carrier field about
-- its point satisfies exactly the sentences of the image (`carrierReading`); the PLL–DC model's
-- results hold for the carrier at its image without restatement: local exponential stability off
-- the singular plane (`PLLDC.mem_den_locallyExponentiallyStable_iff`), the collapse onto the plane
-- (`PLLDC.collapsePoint_mem_den_locallyExponentiallyStable`). The four-state reading of the
-- carrier is in `theorem/GridTiedConverter/GFL/DCLink/BasinGuardFourState.agda`, the mirror of
-- the two drop signs in `theorem/Transform/CurrentDirection.agda`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (X : Type) (holds : System X → Sentence → Type)
  (invariant : (A : Affine X) (a : System X) (s : Sentence) →
    holds (transportSystem A a) s ≃ holds a s)
  where

  open Flows X holds invariant

  module _ (GuardModel PModel PReq : Type)
    (pSystem : PModel → System X)
    (pMeets : PModel → PReq → Type) (pTranslate : Sentence → PReq → Type)
    -- The carrier field about the selected point.
    (carrierSystem : GuardModel → System X)
    -- The parameter map, about the same selected point.
    (toP : GuardModel → PModel)
    where

    pFamily : Family
    pFamily = record
      { Model = PModel ; Req = PReq ; system = pSystem ; meets = pMeets
      ; translate = pTranslate }

    -- The carrier models read as the PLL–DC model: no semantics of their own.
    guardFamily : Family
    guardFamily = comap pFamily toP

    -- What Lean proves.
    record Obligations : Type where
      field
        sameSystem : (m : GuardModel) → carrierSystem m ≡ pSystem (toP m)

    module _ (ob : Obligations) where
      open Obligations ob

      -- The carrier field about its point satisfies exactly the sentences of the image.
      carrierReading : (m : GuardModel) → Reading (carrierSystem m) (pSystem (toP m))
      carrierReading m s = pathToEquiv (cong (λ a → holds a s) (sameSystem m))
