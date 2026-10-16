{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.SaturationSwing where

-- Scaffold of the reading of the current-saturated grid-forming converter through the swing hub
-- (`Limiting.family` of `theorem/Limiting/Saturation.lean` read through
-- `Synchronous.Swing.family`). The saturated model `M δ̈ + D δ̇ = P_ref − P_sat cos(δ − φ)` at
-- `(δ*, 0)` is the swing machine `⟨M, D, P_ref, 0, P_sat, φ − π/2⟩` at the same point: the same
-- field (`sin(x + π/2) = cos x`), so the reading is an equality of systems, for every model. The
-- family keeps the two-element language `{stable, unstable}` (`Spectral.localFamily`), which has no
-- requirement for positive inertia, so the context is a predicate on the parameters and the
-- results are member characterizations within it. Lean proves the field identity
-- (`satField_eq_swing`), the reading (`mem_den_flow_iff_swing`), the correspondence of `Stable`
-- with the swing requirements (`toSwing_mem_realize_iff`) and the characterizations
-- (`mem_den_locallyExponentiallyStable_iff`, `mem_den_locallyAsymptoticallyStable_iff`). Nothing
-- here is exported.

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

  record SatModel : Type where
    constructor satModel
    field
      M D Pref Psat φ δ : ℝ

  open SatModel

  satField : SatModel → ℝ × ℝ → ℝ × ℝ
  satField m (δ , ω) = ω , ((Pref m - Psat m * cos (δ - φ m)) - D m * ω) / M m

  satSystem : SatModel → System (ℝ × ℝ)
  satSystem m = satField m , (δ m , 0r)

  -- The two-element language of `Spectral.localFamily` and its conditions.
  data SatReq : Type where
    stable unstable' : SatReq

  satStable satUnstable : SatModel → Type
  satStable m = (Psat m * cos (δ m - φ m) ≡ Pref m) × (0r < M m) × (0r < D m)
    × (Psat m * sin (δ m - φ m) < 0r)
  satUnstable m = (Psat m * cos (δ m - φ m) ≡ Pref m) × (0r < M m)
    × (0r < Psat m * sin (δ m - φ m))

  satMeets : SatModel → SatReq → Type
  satMeets m stable = satStable m
  satMeets m unstable' = satUnstable m

  onlyStable onlyUnstable noSat : SatReq → Type
  onlyStable stable = Unit
  onlyStable unstable' = ⊥
  onlyUnstable stable = ⊥
  onlyUnstable unstable' = Unit
  noSat _ = ⊥

  satTranslate : Sentence → SatReq → Type
  satTranslate = localTable onlyStable onlyStable onlyUnstable noSat

  -- The map of models: the swing machine with the shifted curve.
  toSwing : SatModel → SwingModel
  toSwing m = swingModel (swingParams (M m) (D m) (Pref m) 0r (Psat m) (φ m - halfπ)) (δ m)

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    (laws : SwingFamily.SwingLaws holds invariant)
    where

    open SwingFamily holds invariant

    satFamily : Family
    satFamily = record
      { Model = SatModel ; Req = SatReq ; system = satSystem ; meets = satMeets
      ; translate = satTranslate }

    PositiveInertia : SatModel → Type
    PositiveInertia m = 0r < M m

    -- What Lean proves by trigonometry and order arithmetic.
    record Obligations : Type where
      field
        sameField : (m : SatModel) → satSystem m ≡ swingSystem (toSwing m)
        stable↔ : (m : SatModel) → PositiveInertia m →
          realize satFamily onlyStable m ↔ realize swingFamily swingLocal (toSwing m)

    module _ (ob : Obligations) where
      open Obligations ob

      positive : Family
      positive = restrictBy satFamily PositiveInertia

      reading : Hub positive swingFamily
      reading = viaEquality (λ x → toSwing (fst x)) (λ x → sameField (fst x))

      inertiaOf : (x : Family.Model positive) → realize swingFamily (only inertia) (toSwing (fst x))
      inertiaOf x r e = subst (swingMeets (toSwing (fst x))) (sym e) (snd x)

      -- Within positive inertia the stability condition is exactly local exponential and local
      -- asymptotic stability (Lean `mem_den_locallyExponentiallyStable_iff`,
      -- `mem_den_locallyAsymptoticallyStable_iff`).
      les↔ : (m : SatModel) → PositiveInertia m →
        realize satFamily onlyStable m ↔ den satFamily locallyExponentiallyStable m
      les↔ = den-of-restrictBy satFamily PositiveInertia _
        (exact-pullback (partial Flow reading) tt inertiaOf (λ x → stable↔ (fst x) (snd x))
          (SwingFamily.SwingLaws.exactUnder-les laws))

      las↔ : (m : SatModel) → PositiveInertia m →
        realize satFamily onlyStable m ↔ den satFamily locallyAsymptoticallyStable m
      las↔ = den-of-restrictBy satFamily PositiveInertia _
        (exact-pullback (partial Flow reading) tt inertiaOf (λ x → stable↔ (fst x) (snd x))
          (SwingFamily.SwingLaws.exactUnder-las laws))
