{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.SwitchedAveraging where

-- Scaffold of the switched implementation of an averaged model: the model is the averaged linear
-- system `ẋ = Ā x`, `Ā = d A₁ + (1 − d) A₂`; its implementation switches between `A₁` and `A₂` with
-- duty `d` and period `T`, read stroboscopically (the period map `M_T = e^{(1−d) T A₂} e^{d T A₁}`
-- as a discrete system of period `T`), and realizes the averaged model it is designed from
-- (`ofDesign`, design map `(d, T, A₁, A₂) ↦ Ā`). The realization is a relation that holds only
-- under a constraint: fast switching. If `Ā` is Hurwitz, every switching period below a threshold
-- gives a Schur period map, so the switched implementation satisfies every attractive sentence its
-- averaged model satisfies (`sound-fast`); without the constraint the realization is not sound —
-- slow switching between two Hurwitz matrices with a Hurwitz average can have a period map with a
-- multiplier below `−1` (`not-sound-slow`, a period-doubling instability). Lean
-- (`theorem/Averaging/SwitchedFamily.lean`): `fast` is
-- `Averaging.periodMap_schurStable_of_isHurwitz`, `slow` is
-- `Averaging.slowSwitching_counterexample` (in `ℝ²`), the readings are
-- `Family.IsLinear.den_hurwitz` and `Map.holdsMap_op_iff_schurStable`, `sound-fast` is
-- `Averaging.switching_sound_fast` and `not-sound-slow` is
-- `Averaging.not_switching_realizationSoundUnder`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.Realization

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (Mat Period Duty : Type) (_≤_ : Period → Period → Type)
    (avg : Duty → Mat → Mat → Mat) (periodMap : Duty → Period → Mat → Mat → Mat)
    (Hurwitz Schur : Mat → Type)
    (continuous : Mat → System) (discrete : Period → Mat → System)
    (Attractive : Sentence → Type)
    -- What Lean proves.
    (continuous-reading : (s : Sentence) → Attractive s → (A : Mat) →
      holds (continuous A) s ↔ Hurwitz A)
    (discrete-reading : (s : Sentence) → Attractive s → (T : Period) (Φ : Mat) →
      holds (discrete T Φ) s ↔ Schur Φ)
    (fast : (d : Duty) (A₁ A₂ : Mat) → Hurwitz (avg d A₁ A₂) →
      Σ[ T₀ ∈ Period ] ((T : Period) → T ≤ T₀ → Schur (periodMap d T A₁ A₂)))
    (slow : Σ[ d ∈ Duty ] Σ[ T ∈ Period ] Σ[ A₁ ∈ Mat ] Σ[ A₂ ∈ Mat ]
      Hurwitz (avg d A₁ A₂) × (¬ Schur (periodMap d T A₁ A₂)))
    where

    Switched : Type
    Switched = Duty × Period × Mat × Mat

    average : Switched → Mat
    average (d , T , A₁ , A₂) = avg d A₁ A₂

    model : Family
    model = record
      { Model = Mat ; Req = ⊥ ; system = continuous ; meets = λ _ () ; translate = λ _ () }

    switched : Family
    switched = record
      { Model = Switched ; Req = ⊥
      ; system = λ { (d , T , A₁ , A₂) → discrete T (periodMap d T A₁ A₂) }
      ; meets = λ _ () ; translate = λ _ () }

    open Design model switched average

    -- Fast switching: an implementation whose averaged model satisfies an attractive sentence
    -- satisfies it at every period below a threshold.
    sound-fast : (s : Sentence) → Attractive s → (d : Duty) (A₁ A₂ : Mat) →
      den model s (avg d A₁ A₂) →
      Σ[ T₀ ∈ Period ] ((T : Period) → T ≤ T₀ → den switched s (d , T , A₁ , A₂))
    sound-fast s a d A₁ A₂ h =
      let (T₀ , hT) = fast d A₁ A₂ (fst (continuous-reading s a (avg d A₁ A₂)) h)
      in T₀ , λ T hT₀ → snd (discrete-reading s a T (periodMap d T A₁ A₂)) (hT T hT₀)

    -- Without the constraint the realization is not sound.
    not-sound-slow : (s : Sentence) → Attractive s → ¬ SoundUnder designed (λ _ → ⊥) s
    not-sound-slow s a =
      let (d , T , A₁ , A₂ , hH , hS) = slow
      in not-sound-of-witness designed (d , T , A₁ , A₂) (λ _ ())
        (snd (certified↔ s (d , T , A₁ , A₂)) (snd (continuous-reading s a (avg d A₁ A₂)) hH))
        (λ h → hS (fst (discrete-reading s a T (periodMap d T A₁ A₂)) h))
