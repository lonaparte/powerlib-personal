{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.DigitalCascade where
-- Lean modules: theorem.GridTiedConverter.GFM.DigitalCascade

-- Scaffold of the digital realization of the grid-forming inner cascade: the model is the
-- single-axis voltage/current cascade (`GFM.InnerCascade.family`: LC filter, PI voltage loop,
-- PI current loop, ideal feed-forward and decoupling); its implementation `GFM.DigitalCascade`
-- runs the same design on a processor with sampling period `Tₛ` — one period of computation
-- delay and the zero-order hold, a total delay `τ = 3 Tₛ/2` taken as the Padé(1,1) block between
-- the current-loop output and the voltage applied to the inductor — and realizes the design it
-- carries (`ofDesign`, design map `(design, Tₛ) ↦ design`). The attractive sentences and sampled
-- contraction (`Attractive`) of both are read through their plants: the design satisfies them
-- exactly when it is stable (the quartic Routh conditions), the platform exactly when its
-- fifth-order plant is Hurwitz, which with `L, C, Tₛ > 0` is the quintic Routh condition of the
-- platform. Unlike the GFL current loop (`theorem/GridTiedConverter/CurrentControl/
-- DigitalCurrentLoop.agda`, where the delay never stabilizes), the realization of the cascade is
-- neither sound nor complete within the physical range `{physical, sampling}`: the slowly sampled
-- IMC cascade `slowCascade` has a stable design and an unstable platform (`not-sound`), and the
-- platform `delayStabilized` is stable while its design is unstable (`not-complete`): the delay
-- changes the attractive sentences in both directions, and only the platform Routh condition
-- decides them (`routh-iff`). Every law is about the Padé platform, not the transcendental delay
-- loop. Lean (`theorem/GridTiedConverter/GFM/DigitalCascade.lean`): `design-reading` is
-- `GFM.InnerCascade.mem_den_iff_stable`, `platform-reading` is `GFM.DigitalCascade.family_isLinear`
-- read by `Family.IsLinear.den_hurwitz`, `routh-iff` is `GFM.DigitalCascade.mem_den_iff`,
-- `hurwitz-not-unstable` and `stable-not-unstable` are `Linear.holds_of_isHurwitz` (a Hurwitz
-- plant is Lyapunov stable) for the platform and for the design,
-- `slow-design` and `slow-unstable` are `GFM.DigitalCascade.slowCascade_design_mem_den` and
-- `GFM.DigitalCascade.slowCascade_mem_den_unstable`, `stabilized-platform` and
-- `stabilized-design` are `GFM.DigitalCascade.delayStabilized_mem_den` and
-- `GFM.DigitalCascade.delayStabilized_design_mem_den_unstable`. The laws: `not-sound` is
-- `GFM.DigitalCascade.not_realizationSoundUnder`, `not-complete` is
-- `GFM.DigitalCascade.not_realizationCompleteUnder`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading
open import theorem.Stack.Realization

-- The requirement language of the cascade design family (`Spectral.Requirement`).
data LinearReq : Type where
  stable unstable' : LinearReq

-- The platform requirements (Lean `CascadeRequirement`): the lifted design requirements, the
-- physical range `L, C > 0`, a positive period, the platform Routh conditions and their strict
-- violation.
data CascadeReq : Type where
  design : LinearReq → CascadeReq
  physical sampling routh lagged : CascadeReq

-- The context of the connection: the physical range and a positive period.
positive : CascadeReq → Type
positive physical = Unit
positive sampling = Unit
positive _ = ⊥

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (Cascade Period : Type)
    (designSystem : Cascade → System) (platformSystem : Cascade → Period → System)
    (Attractive : Sentence → Type) (unstable : Sentence)
    -- Designs: stable, unstable, the physical range; periods: positive; platforms: a Hurwitz
    -- plant, the Routh conditions, a strict violation.
    (Stable Unstable Physical : Cascade → Type) (Sampling : Period → Type)
    (Hurwitz Routh Lagged : Cascade → Period → Type)
    -- What Lean proves.
    (design-reading : (s : Sentence) → Attractive s → (c : Cascade) →
      holds (designSystem c) s ↔ Stable c)
    (platform-reading : (s : Sentence) → Attractive s → (c : Cascade) (T : Period) →
      holds (platformSystem c T) s ↔ Hurwitz c T)
    (routh-iff : (c : Cascade) (T : Period) → Physical c → Sampling T →
      Hurwitz c T ↔ Routh c T)
    (hurwitz-not-unstable : (c : Cascade) (T : Period) → Hurwitz c T →
      ¬ holds (platformSystem c T) unstable)
    (stable-not-unstable : (c : Cascade) → Stable c → ¬ holds (designSystem c) unstable)
    -- The slowly sampled IMC cascade `slowCascade`.
    (slowDesign : Cascade) (slowPeriod : Period)
    (slow-physical : Physical slowDesign) (slow-sampling : Sampling slowPeriod)
    (slow-design : (s : Sentence) → Attractive s → holds (designSystem slowDesign) s)
    (slow-unstable : holds (platformSystem slowDesign slowPeriod) unstable)
    -- The platform stabilized by its delay, `delayStabilized`.
    (stabDesign : Cascade) (stabPeriod : Period)
    (stab-physical : Physical stabDesign) (stab-sampling : Sampling stabPeriod)
    (stabilized-platform : (s : Sentence) → Attractive s →
      holds (platformSystem stabDesign stabPeriod) s)
    (stabilized-design : holds (designSystem stabDesign) unstable)
    where

    Platform : Type
    Platform = Cascade × Period

    designMeets : Cascade → LinearReq → Type
    designMeets c stable = Stable c
    designMeets c unstable' = Unstable c

    platformMeets : Platform → CascadeReq → Type
    platformMeets (c , T) (design q) = designMeets c q
    platformMeets (c , T) physical = Physical c
    platformMeets (c , T) sampling = Sampling T
    platformMeets (c , T) routh = Routh c T
    platformMeets (c , T) lagged = Lagged c T

    -- The two families; their translations are their own and do not enter the realization laws.
    designFamily : Family
    designFamily = record
      { Model = Cascade ; Req = LinearReq ; system = designSystem ; meets = designMeets
      ; translate = λ _ _ → ⊥ }

    platform : Family
    platform = record
      { Model = Platform ; Req = CascadeReq ; system = λ y → platformSystem (fst y) (snd y)
      ; meets = platformMeets ; translate = λ _ _ → ⊥ }

    open Design designFamily platform fst

    -- Within the physical range, a platform satisfies an attractive sentence exactly when its
    -- Routh conditions hold.
    platform-exact : (s : Sentence) → Attractive s → (y : Platform) → realize platform positive y →
      holds (platformSystem (fst y) (snd y)) s ↔ Routh (fst y) (snd y)
    platform-exact s a (c , T) hΔ =
      ↔-trans (platform-reading s a c T) (routh-iff c T (hΔ physical tt) (hΔ sampling tt))

    -- Without a condition on the period the realization is not sound.
    not-sound : (s : Sentence) → Attractive s → ¬ SoundUnder designed positive s
    not-sound s a = not-sound-of-witness designed (slowDesign , slowPeriod) context
      (snd (certified↔ s (slowDesign , slowPeriod)) (slow-design s a))
      (λ h → hurwitz-not-unstable slowDesign slowPeriod
        (fst (platform-reading s a slowDesign slowPeriod) h) slow-unstable)
      where
        context : realize platform positive (slowDesign , slowPeriod)
        context physical _ = slow-physical
        context sampling _ = slow-sampling
        context (design _) ()
        context routh ()
        context lagged ()

    -- Nor complete: the delay stabilizes a platform whose design is unstable.
    not-complete : (s : Sentence) → Attractive s → ¬ CompleteUnder designed positive s
    not-complete s a h =
      stable-not-unstable stabDesign
        (fst (design-reading s a stabDesign)
          (fst (certified↔ s (stabDesign , stabPeriod))
            (h (stabDesign , stabPeriod) context (stabilized-platform s a))))
        stabilized-design
      where
        context : realize platform positive (stabDesign , stabPeriod)
        context physical _ = stab-physical
        context sampling _ = stab-sampling
        context (design _) ()
        context routh ()
        context lagged ()
