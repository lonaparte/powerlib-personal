{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFL.DCLink.BasinGuardFourState where
-- Lean modules: theorem.GridTiedConverter.GFL.DCLink.BasinGuard

-- Scaffold of the four-state reading of the basin-guard carrier inside the PLL–DC model
-- (`PLLDC.family` of `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`). A carrier
-- model reads as the PLL–DC model about the same point (`BasinGuard.Model.toPLLDC`, scaffold
-- `theorem/GridTiedConverter/GFL/DCLink/BasinGuardPLLDC.agda`). With no quadrature current
-- reference (`I_q* = 0`), at a point with `V_dc* = 1` and `K_i^pll x_p* = 0` (the context), its
-- image lies on the four-state slice of the PLL–DC model (`onSlice`), where a PLL–DC system and
-- the image of its four-state reading are the same system (`shift`, scaffold
-- `theorem/GridTiedConverter/GFL/DCLink/PLLDC/FourStateSlice.agda`, Lean
-- `PLLDC.mem_den_iff_fourState`). So on the context the carrier's image and the image of its
-- four-state reading `BasinGuard.Model.toFourState` agree on every sentence (`den↔`, Lean
-- `BasinGuard.mem_den_iff_fourState`). A locally exponentially stable carrier with `I_q* = 0` and
-- `V_dc* ≠ 0` (the guard) has an equilibrium image, which forces the context (`necessary`, Lean
-- `PLLDC.mem_den_locallyExponentiallyStable_iff` with `PLLDC.Params.equilibrium_Vdc` and
-- `PLLDC.Params.equilibrium_ki_xpll`); with the four-state characterization in the closed forms
-- of the four-state model (`four-les`, Lean `FourState.mem_den_locallyExponentiallyStable_iff`)
-- this characterizes local exponential stability of the guarded carriers (`les↔`, Lean
-- `BasinGuard.mem_den_locallyExponentiallyStable_iff`). Nothing here is exported.

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

  module _ (GuardModel PModel FourModel PReq : Type)
    (pSystem : PModel → System X)
    (pMeets : PModel → PReq → Type) (pTranslate : Sentence → PReq → Type)
    -- The parameter maps into the PLL–DC model and the four-state reading of the PLL–DC model.
    (toP : GuardModel → PModel) (fourToP : FourModel → PModel) (pToFour : PModel → FourModel)
    -- `I_q* = 0` with `V_dc* ≠ 0` (the guard), the reading context `V_dc* = 1`,
    -- `K_i^pll x_p* = 0`, the slice of the PLL–DC model, and the four-state closed forms.
    (Guard Context : GuardModel → Type) (Slice : PModel → Type)
    (Equilibrium Routh : FourModel → Type)
    where

    pFamily : Family
    pFamily = record
      { Model = PModel ; Req = PReq ; system = pSystem ; meets = pMeets
      ; translate = pTranslate }

    -- The four-state reading of a carrier is that of its PLL–DC image.
    toFour : GuardModel → FourModel
    toFour m = pToFour (toP m)

    -- What Lean proves.
    record Obligations : Type where
      field
        onSlice : (m : GuardModel) → Context m → Slice (toP m)
        shift : (b : PModel) → Slice b → pSystem b ≡ pSystem (fourToP (pToFour b))
        necessary : (m : GuardModel) → Guard m →
          den pFamily locallyExponentiallyStable (toP m) → Context m
        four-les : (f : FourModel) →
          den pFamily locallyExponentiallyStable (fourToP f) ↔ (Equilibrium f × Routh f)

    module _ (ob : Obligations) where
      open Obligations ob

      -- On the context the carrier's image and the image of its four-state reading agree on every
      -- sentence.
      den↔ : (m : GuardModel) → Context m → (s : Sentence) →
        den pFamily s (toP m) ↔ den pFamily s (fourToP (toFour m))
      den↔ m c s = ↔-of-≃ (pathToEquiv (cong (λ a → holds a s) (shift (toP m) (onSlice m c))))

      -- Local exponential stability of the guarded carriers: the reading context and the
      -- four-state conditions.
      les↔ : (m : GuardModel) → Guard m → den pFamily locallyExponentiallyStable (toP m) ↔
        (Context m × (Equilibrium (toFour m) × Routh (toFour m)))
      les↔ m g =
        (λ h → let c = necessary m g h
               in c , fst (four-les (toFour m)) (fst (den↔ m c locallyExponentiallyStable) h))
        , λ { (c , er) →
              snd (den↔ m c locallyExponentiallyStable) (snd (four-les (toFour m)) er) }
