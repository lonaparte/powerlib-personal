{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFL.DCLink.BasinGuardFourState where
-- Lean modules: theorem.GridTiedConverter.GFL.DCLink.BasinGuard

-- Scaffold of the reading of the basin-guard carrier family through the four-state DC-link
-- family (`BasinGuard.family` of `theorem/GridTiedConverter/GFL/DCLink/BasinGuard.lean` read
-- through `FourState.family` of `theorem/GridTiedConverter/GFL/DCLink/FourState.lean`), the
-- composite of two readings through the model-B hub. The carrier is model B for every model, an
-- equality of systems (`sameSystem`, scaffold
-- `theorem/GridTiedConverter/GFL/DCLink/BasinGuardModelB.agda`, Lean
-- `BasinGuard.Model.field_eq_modelB`). With no quadrature current reference (`I_q* = 0`), at a
-- point with `V_dc* = 1` and `K_i^pll x_p* = 0`, its model-B image lies on the slice of model B
-- (`onSlice`) where model B is the four-state field written in other coordinates: the integrator
-- sign flip `diag(1, 1, 1, −1)` and the shift `(0, x_p*, 0, ξ*)`, with the parameters mapped by
-- `V₀ = V`, `X_g ↦ s X_g`, `i_d0 = K_i^dvc ξ*` (`conjugate`, scaffold
-- `theorem/GridTiedConverter/GFL/DCLink/ModelBFourState.agda`, Lean
-- `ModelBParams.field_eq_transport` read through `Spectral.mem_den_flow_iff_of_transport`). So on
-- that context the carrier and its four-state image agree on every flow sentence (`den↔`, the
-- model-B reading followed by the reading by conjugacy; Lean `BasinGuard.mem_den_iff_fourState`
-- from `BasinGuard.mem_den_iff_modelB` and `ModelB.mem_den_iff_fourState`). A locally
-- exponentially stable point of the carrier with `V_dc* ≠ 0` is an equilibrium of model B, which
-- forces `V_dc* = 1` and `K_i^pll x_p* = 0` (`necessary`, Lean
-- `BasinGuard.mem_den_locallyExponentiallyStable_iff_modelB` with `ModelBParams.equilibrium_Vdc`
-- and `ModelBParams.equilibrium_ki_xpll`); with the four-state characterization (equilibrium and
-- the Routh conditions, by converse linearization, `four-les`, Lean
-- `FourState.exact_locallyExponentiallyStable`) this gives the characterization of local
-- exponential stability of the basin-guard models with `I_q* = 0` and `V_dc* ≠ 0` (`les↔`, Lean
-- `BasinGuard.mem_den_locallyExponentiallyStable_iff`). The family's requirement language speaks
-- of these conditions (`iqZero`, `vdcNonzero`, `fourStatePoint`, and `fourState r` for each
-- four-state requirement `r`, meaning `r` of the four-state reading), and translates local
-- exponential stability to `iqZero`, `fourStatePoint` and the four-state equilibrium and Routh
-- requirements, so the translation is exact within `{iqZero, vdcNonzero}` (`exact-les`, Lean
-- `BasinGuard.exactUnder_locallyExponentiallyStable`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (X : Type) (holds : System X → Sentence → Type)
  (invariant : (A : Affine X) (a : System X) (s : Sentence) →
    holds (transportSystem A a) s ≃ holds a s)
  where

  open Flows X holds invariant

  module _ (GuardModel BModel FourModel GuardReq BReq FourReq : Type)
    (guardSystem : GuardModel → System X) (bSystem : BModel → System X)
    (fourSystem : FourModel → System X)
    (guardMeets : GuardModel → GuardReq → Type) (guardTranslate : Sentence → GuardReq → Type)
    (bMeets : BModel → BReq → Type) (bTranslate : Sentence → BReq → Type)
    (fourMeets : FourModel → FourReq → Type) (fourTranslate : Sentence → FourReq → Type)
    -- The maps of models through the hub and the change of frame of model B (integrator flip and
    -- shift).
    (toB : GuardModel → BModel) (bToFour : BModel → FourModel) (frame : BModel → Affine X)
    -- `I_q* = 0` with `V_dc* ≠ 0` (the guard), the reading context `V_dc* = 1`,
    -- `K_i^pll x_p* = 0`, and the slice of model B.
    (Guard Context : GuardModel → Type) (Slice : BModel → Type)
    (Equilibrium Routh : FourModel → Type)
    -- `I_q* = 0` alone (part of the guard and of the translation).
    (IqZero : GuardModel → Type)
    where

    guardFamily : Family
    guardFamily = record
      { Model = GuardModel ; Req = GuardReq ; system = guardSystem ; meets = guardMeets
      ; translate = guardTranslate }

    bFamily : Family
    bFamily = record
      { Model = BModel ; Req = BReq ; system = bSystem ; meets = bMeets
      ; translate = bTranslate }

    fourFamily : Family
    fourFamily = record
      { Model = FourModel ; Req = FourReq ; system = fourSystem ; meets = fourMeets
      ; translate = fourTranslate }

    -- The four-state reading of a carrier is that of its model-B image.
    toFour : GuardModel → FourModel
    toFour m = bToFour (toB m)

    -- What Lean proves.
    record Obligations : Type where
      field
        sameSystem : (m : GuardModel) → guardSystem m ≡ bSystem (toB m)
        onSlice : (m : GuardModel) → Context m → Slice (toB m)
        conjugate : (b : BModel) → Slice b → (s : Sentence) → Flow s →
          holds (bSystem b) s ≃ holds (transportSystem (frame b) (fourSystem (bToFour b))) s
        necessary : (m : GuardModel) → Guard m → den guardFamily locallyExponentiallyStable m →
          Context m
        four-les : (f : FourModel) →
          den fourFamily locallyExponentiallyStable f ↔ (Equilibrium f × Routh f)

    module _ (ob : Obligations) where
      open Obligations ob

      toModelB : Hub guardFamily bFamily
      toModelB = viaEquality toB sameSystem

      sliceReading : PartialHub Flow (restrictBy bFamily Slice) fourFamily
      sliceReading = partialConjugacy affine Flow (λ x → bToFour (fst x)) (λ x → frame (fst x))
        (λ x s p → conjugate (fst x) (snd x) s p)

      -- The composite reading on the context: through model B, then through its slice.
      reading : PartialHub Flow (restrictBy guardFamily Context) fourFamily
      reading = record
        { map = λ x → toFour (fst x)
        ; read = λ x s p → compEquiv (Hub.read toModelB (fst x) s)
            (PartialHub.read sliceReading (toB (fst x) , onSlice (fst x) (snd x)) s p) }

      -- On the context the carrier and its four-state image agree on every flow sentence.
      den↔ : (m : GuardModel) → Context m → (s : Sentence) → Flow s →
        den guardFamily s m ↔ den fourFamily s (toFour m)
      den↔ m c s p = ↔-of-≃ (PartialHub.read reading (m , c) s p)

      -- Local exponential stability of the guarded models: the reading context and the
      -- four-state conditions.
      les↔ : (m : GuardModel) → Guard m → den guardFamily locallyExponentiallyStable m ↔
        (Context m × (Equilibrium (toFour m) × Routh (toFour m)))
      les↔ m g =
        (λ h → let c = necessary m g h
               in c , fst (four-les (toFour m)) (fst (den↔ m c locallyExponentiallyStable tt) h))
        , λ { (c , er) →
              snd (den↔ m c locallyExponentiallyStable tt) (snd (four-les (toFour m)) er) }


      -- The requirement language: the translation of local exponential stability says
      -- `I_q* = 0`, the reading context and the four-state conditions, and the guard is met by
      -- the requirements `iqZero`, `vdcNonzero`.
      module Exactness (Δ : GuardReq → Type)
        (translation↔ : (m : GuardModel) →
          realize guardFamily (guardTranslate locallyExponentiallyStable) m ↔
            (IqZero m × (Context m × (Equilibrium (toFour m) × Routh (toFour m)))))
        (guard-of : (m : GuardModel) → realize guardFamily Δ m → Guard m)
        (iq-of : (m : GuardModel) → Guard m → IqZero m)
        where

        exact-les : ExactUnder guardFamily Δ locallyExponentiallyStable
        exact-les m hΔ =
          let g = guard-of m hΔ
          in ↔-trans (translation↔ m)
               ((λ t → snd (les↔ m g) (snd t))
               , (λ d → iq-of m g , fst (les↔ m g) d))
