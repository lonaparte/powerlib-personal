{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFL.DCLink.BasinGuardModelB where
-- Lean modules: theorem.GridTiedConverter.GFL.DCLink.BasinGuard

-- Scaffold of the reading of the basin-guard carrier family through the reduced-order model-B
-- family (`BasinGuard.family` of `theorem/GridTiedConverter/GFL/DCLink/BasinGuard.lean` read
-- through `ModelB.family` of `theorem/GridTiedConverter/GFL/DCLink/ModelBStability.lean`). For
-- every quadrature current reference `I_q*`, drop sign `s` and selected point, the carrier field
-- is the model-B field under the parameter map `CarrierParams.toModelB` (`ω_s = ω_g = 1`,
-- `V_dc* = 1`, gains `(K_p^pll, K_i^pll)`, `I₀ = I_dc`, `i_q0 = I_q*`, line reactance `s X_g`),
-- in the same coordinates and about the same point. So the reading is an equality of systems for
-- every model (`sameSystem`, Lean `BasinGuard.Model.field_eq_modelB` from
-- `CarrierParams.carrierField_eq_modelB_field`), and the two families agree on every sentence
-- (`den↔`, Lean `BasinGuard.mem_den_iff_modelB`). The carrier keeps its own requirement language;
-- the model-B results are transported, not restated. Local exponential stability at `V_dc* ≠ 0`,
-- for every `I_q*`, is the model-B characterization (`b-les`, Lean
-- `ModelB.mem_den_locallyExponentiallyStable_iff`: an equilibrium whose Jacobian meets the 4×4
-- Routh conditions) read through the map (`les↔`, Lean
-- `BasinGuard.mem_den_locallyExponentiallyStable_iff_modelB`). A selected state of model B on the
-- singular plane `V_dc = 0` that the power term drives into the plane while the injection crosses
-- it is locally exponentially stable (`collapse`, Lean
-- `ModelB.mem_den_locallyExponentiallyStable_of_collapse`); the carrier `BasinGuard.collapsePoint`
-- (`I_q* = 0`, `V_dc* = 0`) reads as one, meets the context `iqZero` and misses the four-state
-- point of the translation, so the local exponential translation is not exact within `iqZero`
-- (`not-exact`, Lean `BasinGuard.collapsePoint_mem_den_locallyExponentiallyStable`,
-- `BasinGuard.not_exactUnder_iqZero_locallyExponentiallyStable`). The four-state reading of the
-- carrier composes this reading with the four-state reading of model B on its slice
-- (`theorem/GridTiedConverter/GFL/DCLink/BasinGuardFourState.agda`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (X : Type) (holds : System X → Sentence → Type)
  (invariant : (A : Affine X) (a : System X) (s : Sentence) →
    holds (transportSystem A a) s ≃ holds a s)
  where

  open Flows X holds invariant

  module _ (GuardModel BModel GuardReq BReq : Type)
    (guardSystem : GuardModel → System X) (bSystem : BModel → System X)
    (guardMeets : GuardModel → GuardReq → Type) (guardTranslate : Sentence → GuardReq → Type)
    (bMeets : BModel → BReq → Type) (bTranslate : Sentence → BReq → Type)
    -- The parameter map, about the same selected point.
    (toB : GuardModel → BModel)
    -- `V_dc* ≠ 0`, on either side.
    (GuardNonzero : GuardModel → Type) (BNonzero : BModel → Type)
    -- The model-B requirements of a locally exponentially stable state (equilibrium, Routh), and
    -- the states of the singular plane that collapse onto it.
    (bLes : BReq → Type) (Collapsing : BModel → Type)
    where

    guardFamily : Family
    guardFamily = record
      { Model = GuardModel ; Req = GuardReq ; system = guardSystem ; meets = guardMeets
      ; translate = guardTranslate }

    bFamily : Family
    bFamily = record
      { Model = BModel ; Req = BReq ; system = bSystem ; meets = bMeets
      ; translate = bTranslate }

    -- What Lean proves.
    record Obligations : Type where
      field
        sameSystem : (m : GuardModel) → guardSystem m ≡ bSystem (toB m)
        nonzero : (m : GuardModel) → GuardNonzero m → BNonzero (toB m)
        b-les : (b : BModel) → BNonzero b →
          den bFamily locallyExponentiallyStable b ↔ realize bFamily bLes b
        collapse : (b : BModel) → Collapsing b → den bFamily locallyExponentiallyStable b

    module _ (ob : Obligations) where
      open Obligations ob

      reading : Hub guardFamily bFamily
      reading = viaEquality toB sameSystem

      -- Every sentence, every model.
      den↔ : (m : GuardModel) (s : Sentence) → den guardFamily s m ↔ den bFamily s (toB m)
      den↔ m s = ↔-of-≃ (Hub.read reading m s)

      -- Local exponential stability at `V_dc* ≠ 0`, for every `I_q*`: the model-B requirements met
      -- by the image.
      les↔ : (m : GuardModel) → GuardNonzero m →
        den guardFamily locallyExponentiallyStable m ↔ realize bFamily bLes (toB m)
      les↔ m g = ↔-trans (den↔ m locallyExponentiallyStable) (b-les (toB m) (nonzero m g))

      -- A carrier whose image collapses onto the singular plane is locally exponentially stable;
      -- one that meets a context `Δ` and misses the translation refutes exactness within `Δ`.
      not-exact : (Δ : GuardReq → Type) (w : GuardModel) → realize guardFamily Δ w →
        Collapsing (toB w) →
        (realize guardFamily (guardTranslate locallyExponentiallyStable) w → ⊥) →
        ExactUnder guardFamily Δ locallyExponentiallyStable → ⊥
      not-exact Δ w hΔ c miss ex =
        miss (snd (ex w hΔ) (snd (den↔ w locallyExponentiallyStable) (collapse (toB w) c)))
