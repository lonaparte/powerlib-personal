{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.PLLAmplitude where

-- Scaffold of amplitude invariance of the SRF-PLL, a change of representation inside the PI-PLL
-- family (`PIPLL.family` of `theorem/PLL/PIPLLFamily.lean` on its SRF members `PIPLL.srf`;
-- `theorem/PLL/Model.lean`). The SRF member with amplitude `V`, gains `(K_p, K_i)`, offset `δω`
-- and selected phase `θ*` reads its flow sentences on the field
-- `θ̇ = −δω − K_p V sin θ + K_i η`, `η̇ = −V sin θ` at the point `(θ*, δω / K_i)`. For `V ≠ 0` the
-- rescaling `ξ = η / V` carries this system to that of the unit-amplitude member with the loop
-- gains `(V K_p, V K_i)`, whose point is `(θ*, δω / (V K_i))` (`conjugate`). So on the members
-- with `V ≠ 0` the PI-PLL family pulled back along `srf` reads through itself at unit amplitude
-- (`reading`, by conjugacy, on the flow sentences), and every flow sentence holds of the
-- amplitude-`V` member exactly when it holds of its unit-amplitude form (`den≃`). For `V = 0` the
-- rescaling is singular and nothing is read; passivity is not read (every member is autonomous
-- and passive). Lean: `member` is `srf_piPLLField` with `Spectral.mem_den_flow_iff_shift`,
-- `field-eq` is `transport_scale_srfField`, `point-eq` is the image
-- of the selected point under `scaleSecond V⁻¹` (inside `srf_mem_den_iff_unitAmplitude`), the
-- invariance is `Dynamics.holds_transport_iff`, and `den≃` is `srf_mem_den_iff_unitAmplitude`.
-- Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics

module _ (Sc : Scalars) (1r : Scalars.ℝ Sc) where
  open Scalars Sc

  -- An SRF member: amplitude, gains, frequency offset and selected phase.
  record SRFParams : Type where
    constructor srfParams
    field
      V Kp Ki δω θ : ℝ

  open SRFParams

  -- The SRF-PLL field in `(θ̃, η)` (Lean `srfField V K_p K_i δω`) and its selected point.
  srfField : SRFParams → ℝ × ℝ → ℝ × ℝ
  srfField m (φ , η) = (- δω m) - Kp m * V m * sin φ + Ki m * η , - (V m * sin φ)

  srfSystem : SRFParams → System (ℝ × ℝ)
  srfSystem m = srfField m , (θ m , δω m / Ki m)

  -- The unit-amplitude member with the loop gains `(V K_p, V K_i)`.
  unitAmplitude : SRFParams → SRFParams
  unitAmplitude m = srfParams 1r (V m * Kp m) (V m * Ki m) (δω m) (θ m)

  -- The rescaling `ξ = η / V` (Lean `scaleSecond V⁻¹`, no shift).
  rescale : SRFParams → Affine (ℝ × ℝ)
  rescale m = record
    { point = λ x → fst x , snd x / V m
    ; pointInv = λ y → fst y , V m * snd y
    ; vector = λ w → fst w , snd w / V m }

  NonzeroAmplitude : SRFParams → Type
  NonzeroAmplitude m = ¬ (V m ≡ 0r)

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    where

    open Flows (ℝ × ℝ) holds invariant

    -- The PI-PLL family, abstractly, and its SRF members.
    module _ (piPLL : Family) (srf : SRFParams → Family.Model piPLL) where

      -- The PI-PLL family read on its SRF members.
      srfFamily : Family
      srfFamily = comap piPLL srf

      -- What Lean proves.
      record Obligations : Type where
        field
          -- A member's flow sentences are those of the SRF field at its selected point.
          member : (m : SRFParams) (s : Sentence) → Flow s →
            holds (Family.system piPLL (srf m)) s ≃ holds (srfSystem m) s
          -- The rescaled field is the unit-amplitude field, and the selected point goes to the
          -- unit-amplitude point.
          field-eq : (m : SRFParams) → NonzeroAmplitude m → (y : ℝ × ℝ) →
            srfField (unitAmplitude m) y ≡
              Affine.vector (rescale m) (srfField m (Affine.pointInv (rescale m) y))
          point-eq : (m : SRFParams) → NonzeroAmplitude m →
            snd (srfSystem (unitAmplitude m)) ≡ Affine.point (rescale m) (snd (srfSystem m))

      module _ (ob : Obligations) where
        open Obligations ob

        -- The unit-amplitude system is the rescaled amplitude-`V` system.
        conjugate : (m : SRFParams) → NonzeroAmplitude m →
          srfSystem (unitAmplitude m) ≡ transportSystem (rescale m) (srfSystem m)
        conjugate m h i = funExt (field-eq m h) i , point-eq m h i

        -- On the members with `V ≠ 0`, the SRF members read through their unit-amplitude forms
        -- on the flow sentences.
        reading : PartialHub Flow (restrictBy srfFamily NonzeroAmplitude) srfFamily
        reading = record
          { map = λ x → unitAmplitude (fst x)
          ; read = λ x s f →
              compEquiv (member (fst x) s f)
                (compEquiv
                  (invEquiv
                    (conjugateReading affine (rescale (fst x)) (conjugate (fst x) (snd x)) s))
                  (invEquiv (member (unitAmplitude (fst x)) s f))) }

        -- Amplitude invariance of every flow sentence.
        den≃ : (m : SRFParams) → NonzeroAmplitude m → (s : Sentence) → Flow s →
          den piPLL s (srf m) ≃ den piPLL s (srf (unitAmplitude m))
        den≃ m h s f = PartialHub.read reading (m , h) s f
