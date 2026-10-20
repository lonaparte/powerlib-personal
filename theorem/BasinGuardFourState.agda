{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.BasinGuardFourState where

-- Scaffold of the reading of the basin-guard carrier family through the four-state DC-link
-- family (`BasinGuard.family` of `theorem/GFL/DCLink/BasinGuard.lean` read through
-- `FourState.family` of `theorem/GFL/DCLink/FourState.lean`). With no quadrature current
-- reference (`I_q* = 0`), at a point with `V_dc* = 1` and `K_i^pll x_p* = 0`, the carrier field is
-- the four-state field written in other coordinates: the integrator sign flip `diag(1, 1, 1, −1)`
-- and the shift `(0, x_p*, 0, ξ*)`, with the parameters mapped by `V₀ = V`, `X_g ↦ s X_g`,
-- `i_d0 = K_i^dvc ξ*`. So on that context the two families agree on every flow sentence (`den↔`, a
-- reading by conjugacy). A locally exponentially stable point of the carrier field is an
-- equilibrium, which forces `V_dc* = 1` and `K_i^pll x_p* = 0` (`necessary`); with the four-state
-- characterization (equilibrium and the Routh conditions, by converse linearization) this gives
-- the characterization of local exponential stability of the basin-guard models with `I_q* = 0`
-- and `V_dc* ≠ 0` (`les↔`). Lean: `conjugate` is `CarrierParams.carrierField_eq_transport` read
-- through `Spectral.mem_den_flow_iff_of_transport`, `den↔` is `BasinGuard.mem_den_iff_fourState`,
-- `necessary` is `CarrierParams.equilibrium_Kip_xp` with
-- `Dynamics.isEquilibrium_of_lyapunovStable_local`, `four-les` is
-- `FourState.exact_locallyExponentiallyStable`, `les↔` is
-- `BasinGuard.mem_den_locallyExponentiallyStable_iff`. The family's requirement language speaks
-- of these conditions (`iqZero`, `vdcNonzero`, `fourStatePoint`, and `fourState r` for each
-- four-state requirement `r`, meaning `r` of the four-state reading), and translates local
-- exponential stability to `iqZero`, `fourStatePoint` and the four-state equilibrium and Routh
-- requirements, so the translation is exact within `{iqZero, vdcNonzero}` (`exact-les`, Lean
-- `BasinGuard.exactUnder_locallyExponentiallyStable`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import theorem.FamilyReading
open import theorem.FlowSemantics

module _ (X : Type) (holds : System X → Sentence → Type)
  (invariant : (A : Affine X) (a : System X) (s : Sentence) →
    holds (transportSystem A a) s ≃ holds a s)
  where

  open Flows X holds invariant

  module _ (GuardModel FourModel GuardReq FourReq : Type)
    (guardSystem : GuardModel → System X) (fourSystem : FourModel → System X)
    (guardMeets : GuardModel → GuardReq → Type) (guardTranslate : Sentence → GuardReq → Type)
    (fourMeets : FourModel → FourReq → Type) (fourTranslate : Sentence → FourReq → Type)
    -- The map of models and the change of frame (integrator flip and shift).
    (toFour : GuardModel → FourModel) (frame : GuardModel → Affine X)
    -- `I_q* = 0` with `V_dc* ≠ 0` (the guard), and the reading context `V_dc* = 1`,
    -- `K_i^pll x_p* = 0`.
    (Guard Context : GuardModel → Type)
    (Equilibrium Routh : FourModel → Type)
    -- `I_q* = 0` alone (part of the guard and of the translation).
    (IqZero : GuardModel → Type)
    where

    guardFamily : Family
    guardFamily = record
      { Model = GuardModel ; Req = GuardReq ; system = guardSystem ; meets = guardMeets
      ; translate = guardTranslate }

    fourFamily : Family
    fourFamily = record
      { Model = FourModel ; Req = FourReq ; system = fourSystem ; meets = fourMeets
      ; translate = fourTranslate }

    -- What Lean proves.
    record Obligations : Type where
      field
        conjugate : (m : GuardModel) → Context m → (s : Sentence) → Flow s →
          holds (guardSystem m) s ≃ holds (transportSystem (frame m) (fourSystem (toFour m))) s
        necessary : (m : GuardModel) → Guard m → den guardFamily locallyExponentiallyStable m →
          Context m
        four-les : (f : FourModel) →
          den fourFamily locallyExponentiallyStable f ↔ (Equilibrium f × Routh f)

    module _ (ob : Obligations) where
      open Obligations ob

      onContext : Family
      onContext = restrictBy guardFamily Context

      reading : PartialHub Flow onContext fourFamily
      reading = partialConjugacy affine Flow (λ x → toFour (fst x)) (λ x → frame (fst x))
        (λ x s p → conjugate (fst x) (snd x) s p)

      -- On the context the two families agree on every flow sentence.
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
