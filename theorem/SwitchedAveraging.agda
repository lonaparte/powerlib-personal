{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.SwitchedAveraging where

-- Scaffold of the switched implementation of an averaged model: the model is the averaged linear
-- system `ẋ = Ā x`, `Ā = d A₁ + (1 − d) A₂`; its implementation switches between `A₁` and `A₂` with
-- duty `d` and period `T`, read stroboscopically (the period map `M_T = e^{(1−d) T A₂} e^{d T A₁}`
-- as a discrete system of period `T`), and realizes the averaged model it is designed from
-- (`ofDesign`, design map `(d, T, A₁, A₂) ↦ Ā`). The realization holds under constraints. Fast
-- switching: if `Ā` is Hurwitz, every switching period below a threshold gives a Schur period map,
-- so the switched implementation satisfies every attractive sentence its averaged model satisfies
-- (`sound-fast`). Commuting topologies: then `M_T = e^{T Ā}`, the switched system is the exact
-- sampling of its average, and the realization is exact for every sentence at every period
-- (`commuting-exact`, through the exact-sampling reading of `theorem/ExactSampling.agda`); in
-- dimension one every pair commutes, so there the realization is exact without constraint
-- (`dimension-one`). Without a constraint, in dimension two and above, the realization is not sound
-- — slow switching between two Hurwitz matrices with a Hurwitz average can have a period map with
-- a multiplier below `−1` (`not-sound-slow`, a period-doubling instability). Lean
-- (`theorem/Averaging/SwitchedStability.lean`, `theorem/Averaging/SwitchedFamily.lean`): `fast` is
-- `Averaging.periodMap_schurStable_of_isHurwitz`, `slow` is
-- `Averaging.slowSwitching_counterexample_of_two_le` (every `n ≥ 2`, the `ℝ²` example embedded
-- block-diagonally), `commute` is `Averaging.periodMap_eq_exp_of_commute`, `sampling` is
-- `LTI.holds_iff_holdsMap_exp` (read as `LTI.sampled_reading`), `sound-fast` is
-- `Averaging.switching_sound_fast`, `not-sound-slow` is
-- `Averaging.not_switching_realizationSoundUnder`, `commuting-exact` is
-- `Averaging.switching_realizationExactUnder_commuting`, `dimension-one` is
-- `Averaging.switching_realizationExactUnder_of_le_one`, `sound-iff` (the dimension boundary) is
-- `Averaging.switching_realizationSoundUnder_iff`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥) renaming (elim to ⊥-elim)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

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
    (exp : Period → Mat → Mat) (Commute : Mat → Mat → Type)
    -- The dimension is at most one (decidable).
    (Dim1 : Type) (dim1? : Dec Dim1)
    -- What Lean proves.
    (continuous-reading : (s : Sentence) → Attractive s → (A : Mat) →
      holds (continuous A) s ↔ Hurwitz A)
    (discrete-reading : (s : Sentence) → Attractive s → (T : Period) (Φ : Mat) →
      holds (discrete T Φ) s ↔ Schur Φ)
    (fast : (d : Duty) (A₁ A₂ : Mat) → Hurwitz (avg d A₁ A₂) →
      Σ[ T₀ ∈ Period ] ((T : Period) → T ≤ T₀ → Schur (periodMap d T A₁ A₂)))
    (slow : ¬ Dim1 → Σ[ d ∈ Duty ] Σ[ T ∈ Period ] Σ[ A₁ ∈ Mat ] Σ[ A₂ ∈ Mat ]
      Hurwitz (avg d A₁ A₂) × (¬ Schur (periodMap d T A₁ A₂)))
    (scalars-commute : Dim1 → (A₁ A₂ : Mat) → Commute A₁ A₂)
    (commute : (d : Duty) (T : Period) (A₁ A₂ : Mat) → Commute A₁ A₂ →
      periodMap d T A₁ A₂ ≡ exp T (avg d A₁ A₂))
    (sampling : (T : Period) (A : Mat) (s : Sentence) →
      holds (discrete T (exp T A)) s ↔ holds (continuous A) s)
    where

    Switched : Type
    Switched = Duty × Period × Mat × Mat

    average : Switched → Mat
    average (d , T , A₁ , A₂) = avg d A₁ A₂

    model : Family
    model = record
      { Model = Mat ; Req = ⊥ ; system = continuous ; meets = λ _ () ; translate = λ _ () }

    -- The realistic constraint the switched family can state about itself.
    data Constraint : Type where
      commuting : Constraint

    switched : Family
    switched = record
      { Model = Switched ; Req = Constraint
      ; system = λ { (d , T , A₁ , A₂) → discrete T (periodMap d T A₁ A₂) }
      ; meets = λ { (d , T , A₁ , A₂) commuting → Commute A₁ A₂ } ; translate = λ _ _ → ⊥ }

    open Design model switched average

    -- Fast switching: an implementation whose averaged model satisfies an attractive sentence
    -- satisfies it at every period below a threshold.
    sound-fast : (s : Sentence) → Attractive s → (d : Duty) (A₁ A₂ : Mat) →
      den model s (avg d A₁ A₂) →
      Σ[ T₀ ∈ Period ] ((T : Period) → T ≤ T₀ → den switched s (d , T , A₁ , A₂))
    sound-fast s a d A₁ A₂ h =
      let (T₀ , hT) = fast d A₁ A₂ (fst (continuous-reading s a (avg d A₁ A₂)) h)
      in T₀ , λ T hT₀ → snd (discrete-reading s a T (periodMap d T A₁ A₂)) (hT T hT₀)

    -- Without the constraint, in dimension two and above, the realization is not sound.
    not-sound-slow : ¬ Dim1 → (s : Sentence) → Attractive s → ¬ SoundUnder designed (λ _ → ⊥) s
    not-sound-slow nd s a =
      let (d , T , A₁ , A₂ , hH , hS) = slow nd
      in not-sound-of-witness designed (d , T , A₁ , A₂) (λ _ ())
        (snd (certified↔ s (d , T , A₁ , A₂)) (snd (continuous-reading s a (avg d A₁ A₂)) hH))
        (λ h → hS (fst (discrete-reading s a T (periodMap d T A₁ A₂)) h))

    -- Commuting topologies: the switched system is the exact sampling of its average, so the
    -- realization is exact for every sentence at every period.
    commuting-exact : (s : Sentence) → ExactUnder' designed (λ r → r ≡ commuting) s
    commuting-exact s (d , T , A₁ , A₂) r =
      let p = commute d T A₁ A₂ (r commuting refl)
          toModel : den switched s (d , T , A₁ , A₂) → den model s (avg d A₁ A₂)
          toModel h = fst (sampling T (avg d A₁ A₂) s) (subst (λ M → holds (discrete T M) s) p h)
          fromModel : den model s (avg d A₁ A₂) → den switched s (d , T , A₁ , A₂)
          fromModel h =
            subst (λ M → holds (discrete T M) s) (sym p) (snd (sampling T (avg d A₁ A₂) s) h)
      in ↔-trans (certified↔ s (d , T , A₁ , A₂)) (fromModel , toModel)

    -- Where every pair of matrices commutes (dimension one), the realization is exact without
    -- constraint.
    dimension-one : ((A₁ A₂ : Mat) → Commute A₁ A₂) → (s : Sentence) →
      ExactUnder' designed (λ _ → ⊥) s
    dimension-one all s (d , T , A₁ , A₂) _ =
      commuting-exact s (d , T , A₁ , A₂) (λ { commuting _ → all A₁ A₂ })

    -- The dimension boundary: the realization is sound without constraint exactly in dimension
    -- at most one.
    sound-iff : (s : Sentence) → Attractive s → SoundUnder designed (λ _ → ⊥) s ↔ Dim1
    sound-iff s a = forward dim1? , backward
      where
        forward : Dec Dim1 → SoundUnder designed (λ _ → ⊥) s → Dim1
        forward (yes d) _ = d
        forward (no nd) h = ⊥-elim (not-sound-slow nd s a h)
        backward : Dim1 → SoundUnder designed (λ _ → ⊥) s
        backward d y r c = fst (dimension-one (scalars-commute d) s y r) c
