{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.DroopSwing where

-- Scaffold of the reading of the droop loop with a first-order power filter through the swing hub
-- (`GFM.DroopLPF` of `theorem/GFM/VSMLPF.lean` read through `Synchronous.Swing.family`).
-- The loop `δ̇ = (P₀ − P_f)/D`, `Ṗ_f = ω_c (K₀ sin δ − P_f)` at `(δ*, P₀)` is the swing machine
-- `⟨D/ω_c, D, P₀, 0, K₀, 0⟩` at `(δ*, 0)` in the coordinates `P_f = P₀ − D ω`. The scaffold fixes
-- the map of models (`toSwing`), the change of coordinates (`droopCoords`), the context in which
-- the reading holds (`physical`: `D, ω_c > 0`) and the requirement correspondence there, and
-- derives the transfer of exactness and soundness of the local sentences. Lean proves the field
-- identity (`DroopLPF.field_eq_transport`), the invariance (`Dynamics.holds_transport_iff`), the
-- correspondence (steps of the proofs of `DroopLPF.chain_le_semantics` and
-- `DroopLPF.exactUnder_locallyExponentiallyStable`) and the transfer (`Spectral.exactUnder_of_hub`,
-- `Spectral.realize_subset_den_of_hub`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.FamilyReading
open import theorem.FlowSemantics
open import theorem.Swing

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  record DroopParams : Type where
    constructor droopParams
    field
      D ωc P0 K0 : ℝ

  record DroopModel : Type where
    constructor droopModel
    field
      q : DroopParams
      δ : ℝ

  open DroopParams
  open DroopModel

  -- The loop in the coordinates `(δ, P_f)` and the selected point `(δ*, P₀)`.
  droopField : DroopParams → ℝ × ℝ → ℝ × ℝ
  droopField q (δ , Pf) = (P0 q - Pf) / D q , ωc q * (K0 q * sin δ - Pf)

  droopSystem : DroopModel → System (ℝ × ℝ)
  droopSystem m = droopField (q m) , (δ m , P0 (q m))

  data DroopReq : Type where
    balanced physical synchronizing antiSynchronizing : DroopReq

  droopMeets : DroopModel → DroopReq → Type
  droopMeets m balanced = K0 (q m) * sin (δ m) ≡ P0 (q m)
  droopMeets m physical = (0r < D (q m)) × (0r < ωc (q m))
  droopMeets m synchronizing = 0r < K0 (q m) * cos (δ m)
  droopMeets m antiSynchronizing = K0 (q m) * cos (δ m) < 0r

  droopLocal droopUnstable noDroop : DroopReq → Type
  droopLocal antiSynchronizing = ⊥
  droopLocal _ = Unit
  droopUnstable synchronizing = ⊥
  droopUnstable _ = Unit
  noDroop _ = ⊥

  droopTranslate : Sentence → DroopReq → Type
  droopTranslate = localTable droopLocal droopLocal droopUnstable noDroop

  -- The map of models: the swing machine of the loop at the same angle.
  toSwing : DroopModel → SwingModel
  toSwing m = swingModel (swingParams (D (q m) / ωc (q m)) (D (q m)) (P0 (q m)) 0r (K0 (q m)) 0r)
    (δ m)

  -- From swing to droop coordinates: `(δ, ω) ↦ (δ, P₀ − D ω)`.
  droopCoords : DroopModel → Affine (ℝ × ℝ)
  droopCoords m = record
    { point = λ { (δ , ω) → δ , (P0 (q m) - D (q m) * ω) }
    ; pointInv = λ { (δ , Pf) → δ , ((P0 (q m) - Pf) / D (q m)) }
    ; vector = λ { (a , b) → a , - (D (q m) * b) } }

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    (laws : SwingFamily.SwingLaws holds invariant)
    where

    open SwingFamily holds invariant

    droopFamily : Family
    droopFamily = record
      { Model = DroopModel ; Req = DroopReq ; system = droopSystem ; meets = droopMeets
      ; translate = droopTranslate }

    Physical : DroopModel → Type
    Physical m = droopMeets m physical

    -- What Lean proves, by field arithmetic and the transport of flow sentences.
    record Obligations : Type where
      field
        conjugate : (m : DroopModel) → Physical m →
          droopSystem m ≡ transportSystem (droopCoords m) (swingSystem (toSwing m))
        hasInertia : (m : DroopModel) → Physical m → swingMeets (toSwing m) inertia
        local↔ : (m : DroopModel) → Physical m →
          realize droopFamily droopLocal m ↔ realize swingFamily swingLocal (toSwing m)
        lyapunov→ : (m : DroopModel) → realize droopFamily droopLocal m →
          realize swingFamily swingLS (toSwing m)
        unstable→ : (m : DroopModel) → realize droopFamily droopUnstable m →
          realize swingFamily swingUnstable (toSwing m)

    module _ (ob : Obligations) where
      open Obligations ob

      -- The models in the context and their reading as swing machines.
      physicalModels : Family
      physicalModels = restrict droopFamily (only physical)

      physicalOf : (x : Family.Model physicalModels) → Physical (fst x)
      physicalOf x = snd x physical refl

      reading : Hub physicalModels swingFamily
      reading = viaConjugacy affine (λ x → toSwing (fst x)) (λ x → droopCoords (fst x))
        (λ x → conjugate (fst x) (physicalOf x))

      inertiaOf : (x : Family.Model physicalModels) →
        realize swingFamily (only inertia) (toSwing (fst x))
      inertiaOf x r e =
        subst (swingMeets (toSwing (fst x))) (sym e) (hasInertia (fst x) (physicalOf x))

      -- Within `physical` local exponential and local asymptotic stability are translated exactly
      -- (Lean `DroopLPF.exactUnder_locallyExponentiallyStable`,
      -- `DroopLPF.exactUnder_locallyAsymptoticallyStable`).
      exactUnder-les : ExactUnder droopFamily (only physical) locallyExponentiallyStable
      exactUnder-les = exactUnder-restrict droopFamily (only physical) _
        (exact-pullback (partial Flow reading) tt inertiaOf
          (λ x → local↔ (fst x) (physicalOf x)) (SwingFamily.SwingLaws.exactUnder-les laws))

      exactUnder-las : ExactUnder droopFamily (only physical) locallyAsymptoticallyStable
      exactUnder-las = exactUnder-restrict droopFamily (only physical) _
        (exact-pullback (partial Flow reading) tt inertiaOf
          (λ x → local↔ (fst x) (physicalOf x)) (SwingFamily.SwingLaws.exactUnder-las laws))

      -- Every translated requirement set of a local sentence contains `physical`, so soundness
      -- passes from the hub (Lean `DroopLPF.chain_le_semantics`).
      sound-les : Sound droopFamily locallyExponentiallyStable
      sound-les = sound-restrict droopFamily (only physical) _
        (λ m hm r e → subst (droopMeets m) (sym e) (hm physical tt))
        (sound-pullback-partial (partial Flow reading) tt
          (λ x hx → fst (local↔ (fst x) (physicalOf x)) hx)
          (SwingFamily.SwingLaws.sound laws locallyExponentiallyStable))

      sound-ls : Sound droopFamily lyapunovStable
      sound-ls = sound-restrict droopFamily (only physical) _
        (λ m hm r e → subst (droopMeets m) (sym e) (hm physical tt))
        (sound-pullback-partial (partial Flow reading) tt (λ x hx → lyapunov→ (fst x) hx)
          (SwingFamily.SwingLaws.sound laws lyapunovStable))

      sound-unstable : Sound droopFamily unstable
      sound-unstable = sound-restrict droopFamily (only physical) _
        (λ m hm r e → subst (droopMeets m) (sym e) (hm physical tt))
        (sound-pullback-partial (partial Flow reading) tt (λ x hx → unstable→ (fst x) hx)
          (SwingFamily.SwingLaws.sound laws unstable))
