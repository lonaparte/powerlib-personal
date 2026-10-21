{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GovernorReduction where

-- Scaffold of the reduction `T_g → 0` of the swing + governor family to the first-order swing
-- family (`Frequency.SwingGovernor.family` and `Frequency.SwingGovernor.reducedFamily` of
-- `theorem/Frequency/SwingGovernor.lean`). A swing + governor model `M Δω̇ = ΔP_m − ΔP_L − D Δω`,
-- `T_g ΔṖ_m = −ΔP_m − K_R Δω` (`M, T_g > 0`) reduces (`reduce`: forget `T_g`) to the first-order
-- swing with static droop `M Δω̇ = −(K_R + D) Δω − ΔP_L`. The two are linear plants of different
-- dimension, so the connection is not a reading of systems: it compares the denotations, sentence
-- by sentence, under conditions. The attractive sentences and sampled contraction (`Hurwitzian`,
-- read on the Hurwitz property of the state matrix) transfer exactly whenever `0 < M + D T_g`
-- (`den↔`), so for every `T_g` with nonnegative damping (`den↔-nonneg`); not without that
-- condition: with negative damping a large `T_g` breaks it, a model being unstable while its
-- reduction is globally exponentially stable (`boundary`: `M = 1`, `D = −1`, `K_R = 2`,
-- `T_g = 2`), so the Hurwitzian sentences do not transfer on the whole family (`no-transfer`).
-- Decay rates transfer only in the limit and off the first-order pole: for a first-order model `r`
-- and a rate `a` with `a M ≠ K_R + D` there is a threshold `τ > 0` below which every swing +
-- governor model reducing to `r` (Lean: with the parameters of `r`) decays at the rate `a` exactly
-- when `r` does (`decay-threshold`: below the pole the full model has the rate margin, above it
-- its slow root bounds the rate; at the pole the full model is not decided). Instability,
-- Lyapunov stability, conservation and passivity are not compared; each family keeps its own
-- translation and laws (the requirement languages take no part and are left empty here), and the
-- finite-horizon trajectory estimate of the limit is implementation evidence outside the
-- sentences. Lean: `full-hurwitz`, `red-hurwitz` are `Family.IsLinear.den_hurwitz`
-- (`SwingGovernor.family_isLinear`, `SwingGovernor.reducedFamily_isLinear`), `hurwitz-reduce` is
-- `SwingGovernor.isHurwitz_iff_reduced`, `den↔` is `SwingGovernor.mem_den_iff_reduce`,
-- `den↔-nonneg` is `SwingGovernor.mem_den_iff_reduce_of_nonneg` (`damped-of-nonneg` its
-- arithmetic), `boundary` is `SwingGovernor.exists_unstable_reduce_globallyExponentiallyStable`
-- (`no-transfer` is its reading, with `unstable-excludes` from
-- `GloballyExponentiallyStable.lyapunovStable`); `threshold` gathers the eventual spectral facts
-- of the proof of `SwingGovernor.exists_threshold_mem_den_decay_iff_reduce`
-- (`SwingGovernor.eventually_rateMargin_iff_reduced`, `SwingGovernor.reduced_rateMargin_iff`,
-- `SwingGovernor.tendsto_slowEig`, `SwingGovernor.eventually_eigDisc_pos`,
-- `SwingGovernor.eventually_rootSum_pos`), `decay-of-margin` is
-- `Family.IsLinear.mem_den_decay_of_rateMargin`, `not-decay-of-slow` is
-- `SwingGovernor.not_mem_den_decay_of_slowEig`, `red-decay` is `SwingGovernor.reduced_exact_decay`,
-- and `decay-threshold` is `SwingGovernor.exists_threshold_mem_den_decay_iff_reduce`. Nothing here
-- is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (elim to ⊥-elim)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics using (Scalars)

module _ (Sc : Scalars) where
  open Scalars Sc

  -- A swing + governor model: `M`, `D`, `K_R`, `T_g`, with `M, T_g > 0`.
  record Model : Type where
    constructor model
    field
      M D K Tg : ℝ
      M-pos : 0r < M
      Tg-pos : 0r < Tg

  -- A first-order swing model: `M`, `D`, `K_R`, with `M > 0`.
  record ReducedModel : Type where
    constructor reducedModel
    field
      M D K : ℝ
      M-pos : 0r < M

  -- The reduction `T_g → 0`: forget `T_g`.
  reduce : Model → ReducedModel
  reduce m = reducedModel (Model.M m) (Model.D m) (Model.K m) (Model.M-pos m)

  -- The condition of the Hurwitz transfer: `0 < M + D T_g`.
  Damped : Model → Type
  Damped m = 0r < Model.M m + Model.D m * Model.Tg m

  -- A rate `a` against the first-order pole: `a M` and `K_R + D`.
  rateOf poleOf : ReducedModel → ℝ → ℝ
  rateOf r a = a * ReducedModel.M r
  poleOf r a = ReducedModel.K r + ReducedModel.D r

  module _ (S : Semantics) where
    open Semantics S
    open Readings S

    module _
      -- The attractive sentences and sampled contraction, global exponential stability,
      -- instability and the decay rates.
      (Hurwitzian : Sentence → Type) (ges unstable : Sentence) (decay : ℝ → Sentence)
      -- The port systems of the two plants (load in, frequency out).
      (fullSystem : Model → System) (reducedSystem : ReducedModel → System)
      -- Hurwitz state matrices, the rate margin `a` of the full model, and its slow root above
      -- `−a` (real roots).
      (HurwitzFull : Model → Type) (HurwitzRed : ReducedModel → Type)
      (Margin SlowRoot : Model → ℝ → Type)
      where

      full reduced : Family
      full = record
        { Model = Model ; Req = ⊥ ; system = fullSystem ; meets = λ _ () ; translate = λ _ () }
      reduced = record
        { Model = ReducedModel ; Req = ⊥ ; system = reducedSystem ; meets = λ _ ()
        ; translate = λ _ () }

      -- What Lean proves.
      record Obligations : Type where
        field
          -- The order of ℝ.
          split : {x y : ℝ} → ¬ (x ≡ y) → (x < y) ⊎ (y < x)
          lt→le : {x y : ℝ} → x < y → x ≤ y
          lt→not-le : {x y : ℝ} → y < x → ¬ (x ≤ y)
          damped-of-nonneg : (m : Model) → 0r ≤ Model.D m → Damped m
          -- The Hurwitzian sentences.
          full-hurwitz : (s : Sentence) → Hurwitzian s → (m : Model) →
            den full s m ↔ HurwitzFull m
          red-hurwitz : (s : Sentence) → Hurwitzian s → (r : ReducedModel) →
            den reduced s r ↔ HurwitzRed r
          hurwitz-reduce : (m : Model) → Damped m → HurwitzFull m ↔ HurwitzRed (reduce m)
          -- The boundary.
          ges-hurwitzian : Hurwitzian ges
          unstable-excludes : (x : System) → holds x unstable → ¬ holds x ges
          boundary : Σ[ m ∈ Model ] den full unstable m × den reduced ges (reduce m)
          -- The decay rates.
          decay-of-margin : (m : Model) (a : ℝ) → Margin m a → den full (decay a) m
          not-decay-of-slow : (m : Model) (a : ℝ) → SlowRoot m a → ¬ den full (decay a) m
          red-decay : (a : ℝ) (r : ReducedModel) →
            den reduced (decay a) r ↔ (rateOf r a ≤ poleOf r a)
          threshold : (r : ReducedModel) (a : ℝ) → ¬ (rateOf r a ≡ poleOf r a) →
            Σ[ τ ∈ ℝ ] (0r < τ) × ((m : Model) → reduce m ≡ r → Model.Tg m < τ →
              (rateOf r a < poleOf r a → Margin m a) × (poleOf r a < rateOf r a → SlowRoot m a))

      module _ (ob : Obligations) where
        open Obligations ob

        ↔-sym : {A B : Type} → A ↔ B → B ↔ A
        ↔-sym (f , g) = g , f

        -- The Hurwitzian sentences transfer whenever `0 < M + D T_g`.
        den↔ : (s : Sentence) → Hurwitzian s → (m : Model) → Damped m →
          den full s m ↔ den reduced s (reduce m)
        den↔ s h m d = ↔-trans (full-hurwitz s h m)
          (↔-trans (hurwitz-reduce m d) (↔-sym (red-hurwitz s h (reduce m))))

        -- With nonnegative damping, for every `T_g`.
        den↔-nonneg : (s : Sentence) → Hurwitzian s → (m : Model) → 0r ≤ Model.D m →
          den full s m ↔ den reduced s (reduce m)
        den↔-nonneg s h m d = den↔ s h m (damped-of-nonneg m d)

        -- Not on the whole family.
        no-transfer : ¬ ((s : Sentence) → Hurwitzian s → (m : Model) →
          den full s m ↔ den reduced s (reduce m))
        no-transfer h =
          let (m , u , g) = boundary
          in unstable-excludes (fullSystem m) u (snd (h ges ges-hurwitzian m) g)

        -- Below the threshold the rate is decided on the side of the pole it lies on.
        decide : (r : ReducedModel) (a : ℝ) (m : Model) → reduce m ≡ r →
          (rateOf r a < poleOf r a → Margin m a) × (poleOf r a < rateOf r a → SlowRoot m a) →
          (rateOf r a < poleOf r a) ⊎ (poleOf r a < rateOf r a) →
          den full (decay a) m ↔ den reduced (decay a) (reduce m)
        decide r a m p below (inl fast) =
          (λ _ → subst (den reduced (decay a)) (sym p) (snd (red-decay a r) (lt→le fast)))
          , (λ _ → decay-of-margin m a (fst below fast))
        decide r a m p below (inr slow) =
          (λ d → ⊥-elim (not-decay-of-slow m a (snd below slow) d))
          , (λ d → ⊥-elim (lt→not-le slow
              (fst (red-decay a r) (subst (den reduced (decay a)) p d))))

        -- Decay rates off the pole transfer below a threshold.
        decay-threshold : (r : ReducedModel) (a : ℝ) → ¬ (rateOf r a ≡ poleOf r a) →
          Σ[ τ ∈ ℝ ] (0r < τ) × ((m : Model) → reduce m ≡ r → Model.Tg m < τ →
            den full (decay a) m ↔ den reduced (decay a) (reduce m))
        decay-threshold r a off =
          let (τ , hτ , below) = threshold r a off
          in τ , hτ , λ m p t → decide r a m p (below m p t) (split off)
