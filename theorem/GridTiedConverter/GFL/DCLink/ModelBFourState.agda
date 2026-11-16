{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFL.DCLink.ModelBFourState where
-- Lean modules: theorem.GridTiedConverter.GFL.DCLink.ModelBFourState

-- Scaffold of the reading of the reduced-order model-B family through the four-state DC-link
-- family on the slice where they are the same plant (`ModelB.family` of
-- `theorem/GridTiedConverter/GFL/DCLink/ModelBStability.lean` read through `FourState.family` of
-- `theorem/GridTiedConverter/GFL/DCLink/FourState.lean`). The slice is a predicate on the
-- parameters and the selected state, not a requirement of model B: no line resistance, no
-- reactive current, unit DC-voltage reference, `V_dc* = 1` and `ω_s − ω_g + k_i x_pll* = 0`
-- (every equilibrium of the parameter slice has the last two, `ModelBParams.equilibrium_Vdc`,
-- `ModelBParams.equilibrium_ki_xpll`). There model B is the four-state field of
-- `ModelBParams.fourStateParams` written in other coordinates: the integrator sign flip
-- `diag(1, 1, 1, −1)` and the shift `(0, x_pll*, 0, ξ_v*)` (`conjugate`, Lean
-- `ModelBParams.field_eq_transport` read through `Spectral.mem_den_flow_iff_of_transport`), so the
-- two families agree on every flow sentence (`den↔`, a reading by conjugacy; Lean
-- `ModelB.mem_den_iff_fourState`, extended to every sentence by `Spectral.mem_den_iff_of_flow`,
-- both families being autonomous). Model B keeps its requirement language. The basin-guard
-- carrier reads through this slice
-- (`theorem/GridTiedConverter/GFL/DCLink/BasinGuardFourState.agda`). Nothing here is exported.

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

  module _ (BModel FourModel BReq FourReq : Type)
    (bSystem : BModel → System X) (fourSystem : FourModel → System X)
    (bMeets : BModel → BReq → Type) (bTranslate : Sentence → BReq → Type)
    (fourMeets : FourModel → FourReq → Type) (fourTranslate : Sentence → FourReq → Type)
    -- The map of models (`ModelB.Model.toFourState`) and the change of frame (integrator flip
    -- and shift).
    (toFour : BModel → FourModel) (frame : BModel → Affine X)
    -- The slice with its point conditions.
    (Slice : BModel → Type)
    where

    bFamily : Family
    bFamily = record
      { Model = BModel ; Req = BReq ; system = bSystem ; meets = bMeets
      ; translate = bTranslate }

    fourFamily : Family
    fourFamily = record
      { Model = FourModel ; Req = FourReq ; system = fourSystem ; meets = fourMeets
      ; translate = fourTranslate }

    -- What Lean proves.
    record Obligations : Type where
      field
        conjugate : (b : BModel) → Slice b → (s : Sentence) → Flow s →
          holds (bSystem b) s ≃ holds (transportSystem (frame b) (fourSystem (toFour b))) s

    module _ (ob : Obligations) where
      open Obligations ob

      onSlice : Family
      onSlice = restrictBy bFamily Slice

      reading : PartialHub Flow onSlice fourFamily
      reading = partialConjugacy affine Flow (λ x → toFour (fst x)) (λ x → frame (fst x))
        (λ x s p → conjugate (fst x) (snd x) s p)

      -- On the slice the two families agree on every flow sentence.
      den↔ : (b : BModel) → Slice b → (s : Sentence) → Flow s →
        den bFamily s b ↔ den fourFamily s (toFour b)
      den↔ b c s p = ↔-of-≃ (PartialHub.read reading (b , c) s p)
