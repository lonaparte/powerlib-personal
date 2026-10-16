{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Swing where

-- Scaffold content of the swing hub (`Synchronous.Swing.family`,
-- `theorem/Synchronous/Swing.lean`): the swing machine `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`
-- read at a selected angle, its requirement language, its translation, and the laws it publishes
-- for its spokes. The readings through it are `theorem/DroopSwing.agda` (the droop loop with a
-- power filter), `theorem/SaturationSwing.agda` (the saturated converter) and
-- `theorem/ClassicalMachineSwing.agda` (the classical machine). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics

-- The singleton and the two-element contexts of a requirement language.
only : {Q : Type} → Q → Q → Type
only q r = r ≡ q

both : {Q : Type} → Q → Q → Q → Type
both q q' r = (r ≡ q) ⊎ (r ≡ q')

module SwingContent (Sc : Scalars) where
  open Scalars Sc

  record SwingParams : Type where
    constructor swingParams
    field
      M D Pm k₁ k₂ k₃ : ℝ

  record SwingModel : Type where
    constructor swingModel
    field
      p : SwingParams
      δ : ℝ

  open SwingParams
  open SwingModel

  Pe : SwingParams → ℝ → ℝ
  Pe q δ = k₁ q + k₂ q * sin (δ - k₃ q)

  syncCoeff : SwingParams → ℝ → ℝ
  syncCoeff q δ = k₂ q * cos (δ - k₃ q)

  -- The field in the coordinates `(δ, ω)` and the selected point `(δ*, 0)`.
  swingField : SwingParams → ℝ × ℝ → ℝ × ℝ
  swingField q (δ , ω) = ω , ((Pm q - Pe q δ) - D q * ω) / M q

  swingSystem : SwingModel → System (ℝ × ℝ)
  swingSystem m = swingField (p m) , (δ m , 0r)

  data SwingReq : Type where
    balanced inertia damped dampingNonneg undamped synchronizing destabilizing curved : SwingReq

  swingMeets : SwingModel → SwingReq → Type
  swingMeets m balanced = Pe (p m) (δ m) ≡ Pm (p m)
  swingMeets m inertia = 0r < M (p m)
  swingMeets m damped = 0r < D (p m)
  swingMeets m dampingNonneg = 0r ≤ D (p m)
  swingMeets m undamped = D (p m) ≡ 0r
  swingMeets m synchronizing = 0r < syncCoeff (p m) (δ m)
  swingMeets m destabilizing = (syncCoeff (p m) (δ m) < 0r) ⊎ (D (p m) < 0r)
  swingMeets m curved = ¬ (k₂ (p m) ≡ 0r)

  -- The requirement sets of the table (Lean `Swing.translate`).
  swingLS swingLocal swingUnstable none : SwingReq → Type
  swingLS balanced = Unit
  swingLS inertia = Unit
  swingLS dampingNonneg = Unit
  swingLS synchronizing = Unit
  swingLS _ = ⊥
  swingLocal balanced = Unit
  swingLocal inertia = Unit
  swingLocal damped = Unit
  swingLocal synchronizing = Unit
  swingLocal _ = ⊥
  swingUnstable balanced = Unit
  swingUnstable inertia = Unit
  swingUnstable destabilizing = Unit
  swingUnstable _ = ⊥
  none _ = ⊥

  swingTranslate : Sentence → SwingReq → Type
  swingTranslate = localTable swingLS swingLocal swingUnstable none

  -- The swing family on a semantic layer of planar fields.
  module SwingFamily (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    where

    open Flows (ℝ × ℝ) holds invariant public

    swingFamily : Family
    swingFamily = record
      { Model = SwingModel ; Req = SwingReq ; system = swingSystem ; meets = swingMeets
      ; translate = swingTranslate }

    -- The laws the hub publishes and its spokes read (Lean: `chain_le_semantics`,
    -- `exactUnder_locallyExponentiallyStable`, `exactUnder_locallyAsymptoticallyStable`,
    -- `exactUnder_lyapunovStable`, `mem_den_unstable_of_not_balanced`).
    record SwingLaws : Type where
      field
        sound : (s : Sentence) → Sound swingFamily s
        exactUnder-les : ExactUnder swingFamily (only inertia) locallyExponentiallyStable
        exactUnder-las : ExactUnder swingFamily (only inertia) locallyAsymptoticallyStable
        exactUnder-ls : ExactUnder swingFamily (both inertia curved) lyapunovStable
        unstable-of-not-balanced : (m : SwingModel) → ¬ (M (p m) ≡ 0r) →
          ¬ swingMeets m balanced → den swingFamily unstable m
