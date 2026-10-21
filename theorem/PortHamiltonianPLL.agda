{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.PortHamiltonianPLL where

-- Scaffold of the reading of the port-Hamiltonian SRF-PLL through the PI-PLL hub
-- (`PLL.PLLPH.family` of `theorem/PLL/PH.lean` read through `PIPLL.family` of
-- `theorem/PLL/PIPLLFamily.lean`). The pH PLL with amplitude `V`, gains `K_p, K_i` and selected
-- point `(θ*, η*)` has, on its zero-input field, the field of the SRF member `srf V K_p K_i (K_i
-- η*) θ*` of the PI-PLL family (for `K_i = 0` both fields ignore `η`, so the reading holds for
-- every model). Only the flow sentences are read: the pH PLL has a port and its passivity stays its
-- own law. The hub's laws are taken abstractly here (the PI-PLL family has its own development);
-- the scaffold fixes the map, the context (`nonnegativeEnergy`: `V, K_i ≥ 0`) and the
-- correspondence, and derives exactness of local exponential stability within the context and
-- soundness of the local sentences. Lean proves the reading (`PLLPH.mem_den_flow_iff_srf`), the
-- correspondence (steps of the proofs of `PLLPH.exactUnder_locallyExponentiallyStable` and
-- `PLLPH.chain_le_semantics`) and the transfer (`Spectral.exactUnder_of_hub` with an empty hub
-- context, `Spectral.realize_subset_den_of_hub`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.FamilyReading
open import theorem.FlowSemantics
open import theorem.Swing using (only)

module _ (Sc : Scalars) where
  open Scalars Sc

  record PLLModel : Type where
    constructor pllModel
    field
      V Kp Ki ηs θ : ℝ

  open PLLModel

  data PLLReq : Type where
    nonnegativeEnergy wellBottom slopeStable saddle : PLLReq

  pllLS pllLocal pllUnstable pllPassive : PLLReq → Type
  pllLS wellBottom = Unit
  pllLS _ = ⊥
  pllLocal slopeStable = Unit
  pllLocal _ = ⊥
  pllUnstable saddle = Unit
  pllUnstable _ = ⊥
  pllPassive nonnegativeEnergy = Unit
  pllPassive _ = ⊥

  pllTranslate : Sentence → PLLReq → Type
  pllTranslate = localTable pllLS pllLocal pllUnstable pllPassive

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    where

    open Flows (ℝ × ℝ) holds invariant

    -- The hub, taken abstractly: the PI-PLL family, its SRF members and the laws it publishes
    -- (`PIPLL.exact_locallyExponentiallyStable`, `PIPLL.chain_le_semantics`).
    module _ (pi : Family) (srf : ℝ → ℝ → ℝ → ℝ → ℝ → Family.Model pi)
      (exact-les : Exact pi locallyExponentiallyStable)
      (sound : (s : Sentence) → Sound pi s)
      (pllSystem : PLLModel → System (ℝ × ℝ))
      (pllMeets : PLLModel → PLLReq → Type)
      where

      pllFamily : Family
      pllFamily = record
        { Model = PLLModel ; Req = PLLReq ; system = pllSystem ; meets = pllMeets
        ; translate = pllTranslate }

      -- The map of models: the SRF member with offset `K_i η*` about the same phase.
      toSRF : PLLModel → Family.Model pi
      toSRF m = srf (V m) (Kp m) (Ki m) (Ki m * ηs m) (θ m)

      NonnegativeEnergy : PLLModel → Type
      NonnegativeEnergy m = pllMeets m nonnegativeEnergy

      -- What Lean proves.
      record Obligations : Type where
        field
          sameFlow : (m : PLLModel) (s : Sentence) → Flow s →
            holds (pllSystem m) s ≃ holds (Family.system pi (toSRF m)) s
          local↔ : (m : PLLModel) → NonnegativeEnergy m →
            realize pllFamily pllLocal m ↔
              realize pi (Family.translate pi locallyExponentiallyStable) (toSRF m)
          local→ : (m : PLLModel) → realize pllFamily pllLocal m →
            realize pi (Family.translate pi locallyExponentiallyStable) (toSRF m)
          unstable→ : (m : PLLModel) → realize pllFamily pllUnstable m →
            realize pi (Family.translate pi unstable) (toSRF m)

      module _ (ob : Obligations) where
        open Obligations ob

        reading : PartialHub Flow pllFamily pi
        reading = record { map = toSRF ; read = sameFlow }

        energetic : Family
        energetic = restrict pllFamily (only nonnegativeEnergy)

        readingOn : PartialHub Flow energetic pi
        readingOn = record { map = λ x → toSRF (fst x) ; read = λ x → sameFlow (fst x) }

        -- Within nonnegative energy local exponential stability is translated exactly (Lean
        -- `PLLPH.exactUnder_locallyExponentiallyStable`); the hub context is empty.
        exactUnder-les : ExactUnder pllFamily (only nonnegativeEnergy) locallyExponentiallyStable
        exactUnder-les = exactUnder-restrict pllFamily (only nonnegativeEnergy) _
          (exact-pullback readingOn {ΔG = λ _ → ⊥} tt (λ x q ())
            (λ x → local↔ (fst x) (snd x nonnegativeEnergy refl))
            (λ y _ → exact-les y))

        -- Soundness of local exponential stability and instability from the hub (Lean
        -- `PLLPH.chain_le_semantics`).
        sound-les : Sound pllFamily locallyExponentiallyStable
        sound-les = sound-pullback-partial reading tt local→ (sound locallyExponentiallyStable)

        sound-unstable : Sound pllFamily unstable
        sound-unstable = sound-pullback-partial reading tt unstable→ (sound unstable)
