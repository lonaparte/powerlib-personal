{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.Matching.ViSynCVSMLPF where
-- Lean modules: theorem.GridTiedConverter.GFM.Matching.ViSynC

-- Scaffold of the reading of ViSynC (virtual synchronous control through the DC-link capacitor)
-- through the VSM with a first-order power filter (`GFM.Matching.ViSynC.family` of
-- `theorem/GridTiedConverter/GFM/Matching/ViSynC.lean` read through `GFM.VSMLPF.family`, whose
-- content is fixed in `theorem/GridTiedConverter/GFM/VSMLPF.agda`). The loop `δ̇ = ω`,
-- `K_J ω̇ = −K_D ω + u`, `C u̇ = i₀ − K_p u − G (v* + u) − b sin δ` at `(δ*, 0, 0)` is the VSM
-- `⟨K_J, K_D, (G + K_p)/C, (i₀ − G v*)/(G + K_p), b/(G + K_p)⟩` at `(δ*, 0, P₀)` in the coordinates
-- `(δ, ω, P_f) = (δ, ω, P₀ − u)` (`visyncCoords`): the DC link is the power filter. The reading
-- is a conjugacy where `C ≠ 0` and `G + K_p ≠ 0` (the context `Readable`); within the physical
-- range the ViSynC stability condition is the hub's local translation (`stable↔`), so the hub's
-- exactness of local exponential stability within `physical` passes to ViSynC on that range
-- (`les↔`). Lean: `conjugate` is `GFM.Matching.ViSynC.Params.vsmlpf_field_eq_transport` with
-- `GFM.Matching.ViSynC.Model.point_eq` (read by `Dynamics.holds_transport_iff`), `den↔` is
-- `GFM.Matching.ViSynC.mem_den_iff_vsmlpf`, `stable↔` is `GFM.Matching.ViSynC.Model.stable_iff`,
-- the -- hub law is `VSMLPF.exactUnder_locallyExponentiallyStable`, and `les↔` is
-- `GFM.Matching.ViSynC.mem_den_locallyExponentiallyStable_iff`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing using (only)
open import theorem.GridTiedConverter.GFM.VSMLPF

module _ (Sc : Scalars) where
  open Scalars Sc
  open VSMLPFContent Sc

  record ViSynCParams : Type where
    constructor visyncParams
    field
      KJ KD C G Kp isrc vstar b : ℝ

  record ViSynCModel : Type where
    constructor visyncModel
    field
      vp : ViSynCParams
      vδ : ℝ

  open ViSynCParams
  open ViSynCModel

  Geff : ViSynCParams → ℝ
  Geff q = G q + Kp q

  visyncField : ViSynCParams → State3 → State3
  visyncField q (x , w , u) =
    w , ((- (KD q * w)) + u) / KJ q ,
    (((isrc q - Kp q * u) - G q * (vstar q + u)) - b q * sin x) / C q

  visyncSystem : ViSynCModel → System State3
  visyncSystem m = visyncField (vp m) , (vδ m , 0r , 0r)

  -- The map of models: the VSM with the DC link as its power filter, at the same angle.
  toVSMLPF : ViSynCModel → VSMModel
  toVSMLPF m = vsmModel (vsmParams (KJ q) (KD q) (Geff q / C q)
    ((isrc q - G q * vstar q) / Geff q) (b q / Geff q)) (vδ m)
    where q = vp m

  P0of : ViSynCModel → ℝ
  P0of m = (isrc (vp m) - G (vp m) * vstar (vp m)) / Geff (vp m)

  -- From ViSynC to VSM coordinates: `(δ, ω, u) ↦ (δ, ω, P₀ − u)`.
  visyncCoords : ViSynCModel → Affine State3
  visyncCoords m = record
    { point = λ { (x , w , u) → x , w , (P0of m - u) }
    ; pointInv = λ { (x , w , pf) → x , w , (P0of m - pf) }
    ; vector = λ { (x , w , u) → x , w , (- u) } }

  data ViSynCReq : Type where
    stable unstable : ViSynCReq

  visyncLocal visyncUnstable noReqV : ViSynCReq → Type
  visyncLocal unstable = ⊥
  visyncLocal stable = Unit
  visyncUnstable stable = ⊥
  visyncUnstable unstable = Unit
  noReqV _ = ⊥

  module Reading (holds : System State3 → Sentence → Type)
    (invariant : (Af : Affine State3) (a : System State3) (s : Sentence) →
      holds (transportSystem Af a) s ≃ holds a s)
    (visyncMeets : ViSynCModel → ViSynCReq → Type)
    -- The context of the reading (`C ≠ 0`, `G + K_p ≠ 0`) and the physical range.
    (Readable Physical : ViSynCModel → Type)
    (readable : (m : ViSynCModel) → Physical m → Readable m)
    where

    open VSMLPFFamily holds invariant

    visyncFamily : Family
    visyncFamily = record
      { Model = ViSynCModel ; Req = ViSynCReq ; system = visyncSystem ; meets = visyncMeets
      ; translate = localTable visyncLocal visyncLocal visyncUnstable noReqV }

    readableModels : Family
    readableModels = restrictBy visyncFamily Readable

    -- What Lean proves by field algebra, where the reading is defined.
    module _ (conjugate : (m : ViSynCModel) → Readable m →
               vsmSystem (toVSMLPF m) ≡ transportSystem (visyncCoords m) (visyncSystem m))
      where

      reading : Hub readableModels vsmFamily
      reading = record
        { map = λ x → toVSMLPF (fst x)
        ; read = λ x s →
            invEquiv (conjugateReading affine (visyncCoords (fst x))
              (conjugate (fst x) (snd x)) s) }

      -- Every sentence of a readable ViSynC model is the sentence of its VSM.
      den↔ : (m : ViSynCModel) (r : Readable m) (s : Sentence) →
        den visyncFamily s m ↔ den vsmFamily s (toVSMLPF m)
      den↔ m r s = ↔-of-≃ (Hub.read reading (m , r) s)

      -- Within the physical range the stability condition is the hub's local translation, so the
      -- hub's exactness within `physical` decides local exponential stability of ViSynC.
      module _ (stable↔ : (m : ViSynCModel) → Physical m →
                 realize visyncFamily visyncLocal m ↔ realize vsmFamily vsmLocal (toVSMLPF m))
        (physical→ : (m : ViSynCModel) → Physical m →
          realize vsmFamily (only physical) (toVSMLPF m))
        (laws : VSMLaws)
        where

        les↔ : (m : ViSynCModel) → Physical m →
          realize visyncFamily visyncLocal m ↔ den visyncFamily locallyExponentiallyStable m
        les↔ m h = ↔-trans (stable↔ m h)
          (↔-trans (VSMLaws.exactUnder-les laws (toVSMLPF m) (physical→ m h))
            (↔-of-≃ (invEquiv (Hub.read reading (m , readable m h) locallyExponentiallyStable))))
