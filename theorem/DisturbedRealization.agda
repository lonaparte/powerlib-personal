{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.DisturbedRealization where

-- Scaffold of the disturbed implementation of a deterministic design: the model is a design read
-- with its operating envelope and no disturbance; its implementation adds a random perturbation of
-- intensity `σ` to the field and is judged on its own safe set, which contains every state within
-- a margin of the design's. The implementation realizes the design it is built from (`ofDesign`,
-- design map `y ↦ design y`). The sentences are safety over a horizon `T` at a level `ε`.
--
-- Over a finite horizon the realization holds under constraints: a Lipschitz design whose initial
-- states start solutions, the margin, an intensity whose Grönwall bound at the horizon is at most
-- the margin, a perturbation bounded with probability `1 − ε` (`finite-sound`). Over the infinite
-- horizon it does not hold under any intensity bound: a design safe over every horizon has, for
-- every positive intensity, an implementation that is not (`infinite-not-sound`). For the witness
-- design every finite horizon has an intensity threshold (`finite-small`) and no nonzero intensity
-- is safe over the infinite horizon (`infinite-unsafe`), so the two limits do not commute: no
-- positive threshold serves every horizon (`non-commuting`).
--
-- Lean (`theorem/Envelope/Disturbed.lean`): `gronwall` is `Envelope.holds_safe_of_margin` with
-- `Envelope.IsDesign.mem_den_safe_iff`; `finite-sound` is
-- `Envelope.noisy_realizationSoundUnder_safe`; `small` is `Envelope.noisyDrift_mem_den_finite`;
-- `unsafe` is `Envelope.noisyDrift_not_mem_den_top`, `infinite-not-sound` is
-- `Envelope.not_driftImpl_realizationSoundUnder_top`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.Realization

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  -- Designs and their disturbed implementations (Lean `Envelope.Noisy`), with the intensity of an
  -- implementation, horizons with the infinite one, and safety over a horizon at a fixed level.
  module _ (Plan Impl Intensity Horizon : Type)
    (design : Impl → Plan) (intensity : Impl → Intensity)
    (_≤_ : Intensity → Intensity → Type) (zero : Intensity) (_<_ : Intensity → Intensity → Type)
    (∞ : Horizon) (Finite : Horizon → Type)
    (nominal : Plan → System) (disturbed : Impl → System) (safe : Horizon → Sentence)
    -- The constraints of a horizon (Lipschitz and solvable design, margin, small intensity,
    -- bounded perturbation), Lean's `NoiseRequirement`.
    (Constrained : Horizon → Impl → Type)
    -- What Lean proves.
    (gronwall : (T : Horizon) → Finite T → (y : Impl) → Constrained T y →
      holds (nominal (design y)) (safe T) → holds (disturbed y) (safe T))
    (witness : Plan) (copy : Intensity → Impl)
    (copy-design : (σ : Intensity) → design (copy σ) ≡ witness)
    (copy-intensity : (σ : Intensity) → intensity (copy σ) ≡ σ)
    (design-safe : (T : Horizon) → holds (nominal witness) (safe T))
    (small : (T : Horizon) → Finite T →
      Σ[ σ₀ ∈ Intensity ] (zero < σ₀) ×
        ((σ : Intensity) → σ ≤ σ₀ → holds (disturbed (copy σ)) (safe T)))
    (unsafe : (σ : Intensity) → zero < σ → ¬ holds (disturbed (copy σ)) (safe ∞))
    (≤-refl : (σ₀ : Intensity) → σ₀ ≤ σ₀)
    where

    model : Family
    model = record
      { Model = Plan ; Req = ⊥ ; system = nominal ; meets = λ _ () ; translate = λ _ () }

    implementation : Family
    implementation = record
      { Model = Impl ; Req = ⊥ ; system = disturbed ; meets = λ _ () ; translate = λ _ () }

    open Design model implementation design

    -- Finite horizons: within the constraints, certified implementations are safe.
    finite-sound : (T : Horizon) → Finite T → (y : Impl) → Constrained T y →
      Certified designed (safe T) y → den implementation (safe T) y
    finite-sound T hT y hc c = gronwall T hT y hc (fst (certified↔ (safe T) y) c)

    -- The infinite horizon: within an intensity bound `σ₀ > 0`, the implementation of the witness
    -- design with intensity `σ₀` is certified and not safe.
    infinite-not-sound : (σ₀ : Intensity) → zero < σ₀ →
      ¬ ((y : Impl) → intensity y ≤ σ₀ → Certified designed (safe ∞) y →
        den implementation (safe ∞) y)
    infinite-not-sound σ₀ h sound =
      unsafe σ₀ h (sound (copy σ₀) (subst (_≤ σ₀) (sym (copy-intensity σ₀)) (≤-refl σ₀))
        (snd (certified↔ (safe ∞) (copy σ₀))
          (subst (λ d → holds (nominal d) (safe ∞)) (sym (copy-design σ₀)) (design-safe ∞))))

    -- The two limits do not commute: every finite horizon has a threshold, no positive threshold
    -- serves every horizon.
    non-commuting : ((T : Horizon) → Finite T → Σ[ σ₀ ∈ Intensity ] (zero < σ₀) ×
        ((σ : Intensity) → σ ≤ σ₀ → den implementation (safe T) (copy σ))) ×
      (¬ (Σ[ σ₀ ∈ Intensity ] (zero < σ₀) ×
        ((σ : Intensity) → σ ≤ σ₀ → (T : Horizon) → den implementation (safe T) (copy σ))))
    non-commuting = small , λ (σ₀ , h , all) → unsafe σ₀ h (all σ₀ (≤-refl σ₀) ∞)
