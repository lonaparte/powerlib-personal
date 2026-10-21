{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.DigitalCurrentLoop where

-- Scaffold of the digital realization of the PI current loop: the model is the single-axis PI
-- current loop (`CurrentControl.PIParams.family`: R–L branch `L di/dt = −R i + v`, PI law
-- `u = K_p (i* − i) + K_i ξ`); its implementation `CurrentControl.DigitalPI` runs the same design
-- on a processor with sampling period `Tₛ` — one period of computation delay and the zero-order
-- hold, a total delay `τ = 3 Tₛ/2` taken as the Padé(1,1) block between `u` and the applied
-- voltage — and realizes the design it carries (`ofDesign`, design map `(design, Tₛ) ↦ design`).
-- The attractive sentences and sampled contraction (`Attractive`) of both are read through their
-- plants: the design satisfies them exactly when it is stable (`(R + K_p)/L > 0`, `K_i/L > 0`),
-- the platform exactly when its third-order plant is Hurwitz, which with `L, Tₛ > 0` is the
-- platform Routh condition `0 < a₂, 0 < a₀, a₃ a₀ < a₂ a₁`. The realization holds under step
-- constraints. It is sound within `{physical, sampling, fastSampling}` (`L > 0`, `Tₛ > 0`,
-- `3 K_p Tₛ ≤ L`, `3 K_i Tₛ ≤ R + K_p`): fast sampling against a stable design gives the Routh
-- condition (`sound`). It is complete within `{sampling}` alone, for every period and every
-- inductance: a Hurwitz platform has a stable design, the delay never stabilizes (`complete`);
-- so it is exact within the step constraints (`exact`). It is not sound without `fastSampling`:
-- the slowly sampled IMC design `L = R = ω_b = 1`, `Tₛ = 2` is stable and its platform unstable
-- (`not-sound`). Instability is realized soundly within `{physical, sampling, design unstable}`:
-- an unstable design violates the Routh condition strictly at every period, which gives a root
-- in the open right half plane (`sound-unstable`). Every law is about the Padé platform, not the
-- transcendental delay loop. Lean (`theorem/CurrentControl/DigitalPI.lean`): `design-reading` is
-- `CurrentControl.PIParams.family_isLinear` read by `Family.IsLinear.den_hurwitz` with
-- `CurrentControl.PIParams.isHurwitz_iff_div`, `platform-reading` is
-- `CurrentControl.DigitalPI.family_isLinear` read by `Family.IsLinear.den_hurwitz`, `routh-iff` is
-- `CurrentControl.DigitalPI.isHurwitz_iff`, `fast` is
-- `CurrentControl.DigitalPI.routh_of_fastSampling`, `delay` is
-- `CurrentControl.DigitalPI.design_stable_of_isHurwitz`, `strict` is
-- `CurrentControl.DigitalPI.lagged_of_unstable`, `root` is
-- `CurrentControl.DigitalPI.exists_root_of_lagged` with `Linear.unstable_of_root`,
-- `hurwitz-not-unstable` is `Linear.holds_of_isHurwitz` (a Hurwitz plant is Lyapunov stable),
-- `slow-design` and `slow-unstable` are `CurrentControl.DigitalPI.slowIMC_design_mem_den` and
-- `CurrentControl.DigitalPI.slowIMC_mem_den_unstable`. The laws: `sound` is
-- `CurrentControl.DigitalPI.realizationSoundUnder` (Lean reduces it statically,
-- `Implementation.realizationSoundUnder_of_design`, through the exact design translation and the
-- sound platform translation `CurrentControl.DigitalPI.chain_le_semantics`; the scaffold reads
-- both through the plants), `complete` is `CurrentControl.DigitalPI.realizationCompleteUnder`,
-- `exact` is `CurrentControl.DigitalPI.realizationExactUnder`, `not-sound` is
-- `CurrentControl.DigitalPI.not_realizationSoundUnder`, `sound-unstable` is
-- `CurrentControl.DigitalPI.realizationSoundUnder_unstable`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.Realization

-- The requirement language of the PI design family (`Spectral.Requirement`).
data LinearReq : Type where
  stable unstable' : LinearReq

-- The platform requirements (Lean `DigitalRequirement`): the lifted design requirements, a
-- positive inductance and period, the platform Routh conditions, a strict violation of them, and
-- fast sampling against the design.
data DigitalReq : Type where
  design : LinearReq → DigitalReq
  physical sampling routh lagged fastSampling : DigitalReq

-- The contexts of the connection: the step constraints `{physical, sampling, fastSampling}`, the
-- positive parameters `{physical, sampling}`, a positive period `{sampling}`, and an unstable
-- design `{physical, sampling, design unstable}`.
stepConstraints positive periodOnly unstableDesign : DigitalReq → Type
stepConstraints physical = Unit
stepConstraints sampling = Unit
stepConstraints fastSampling = Unit
stepConstraints _ = ⊥
positive physical = Unit
positive sampling = Unit
positive _ = ⊥
periodOnly sampling = Unit
periodOnly _ = ⊥
unstableDesign physical = Unit
unstableDesign sampling = Unit
unstableDesign (design unstable') = Unit
unstableDesign _ = ⊥

-- A positive period is one of the step constraints.
period-of-step : (q : DigitalReq) → periodOnly q → stepConstraints q
period-of-step sampling _ = tt
period-of-step (design _) ()
period-of-step physical ()
period-of-step routh ()
period-of-step lagged ()
period-of-step fastSampling ()

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (PIParams Period : Type)
    (designSystem : PIParams → System) (platformSystem : PIParams → Period → System)
    (Attractive : Sentence → Type) (unstable : Sentence)
    -- Designs: stable, unstable (`(R + K_p)/L < 0` or `K_i/L < 0`), a positive inductance;
    -- periods: positive; platforms: a Hurwitz plant, the Routh conditions, a strict violation,
    -- fast sampling.
    (Stable Unstable Physical : PIParams → Type) (Sampling : Period → Type)
    (Hurwitz Routh Lagged FastSampling : PIParams → Period → Type)
    -- What Lean proves.
    (design-reading : (s : Sentence) → Attractive s → (p : PIParams) →
      holds (designSystem p) s ↔ Stable p)
    (platform-reading : (s : Sentence) → Attractive s → (p : PIParams) (T : Period) →
      holds (platformSystem p T) s ↔ Hurwitz p T)
    (routh-iff : (p : PIParams) (T : Period) → Physical p → Sampling T →
      Hurwitz p T ↔ Routh p T)
    (fast : (p : PIParams) (T : Period) → Physical p → Sampling T → Stable p →
      FastSampling p T → Routh p T)
    (delay : (p : PIParams) (T : Period) → Sampling T → Hurwitz p T → Stable p)
    (strict : (p : PIParams) (T : Period) → Physical p → Sampling T → Unstable p → Lagged p T)
    (root : (p : PIParams) (T : Period) → Physical p → Sampling T → Lagged p T →
      holds (platformSystem p T) unstable)
    (hurwitz-not-unstable : (p : PIParams) (T : Period) → Hurwitz p T →
      ¬ holds (platformSystem p T) unstable)
    -- The slowly sampled IMC platform `slowIMC`.
    (slowDesign : PIParams) (slowPeriod : Period)
    (slow-physical : Physical slowDesign) (slow-sampling : Sampling slowPeriod)
    (slow-design : (s : Sentence) → Attractive s → holds (designSystem slowDesign) s)
    (slow-unstable : holds (platformSystem slowDesign slowPeriod) unstable)
    where

    Platform : Type
    Platform = PIParams × Period

    designMeets : PIParams → LinearReq → Type
    designMeets p stable = Stable p
    designMeets p unstable' = Unstable p

    platformMeets : Platform → DigitalReq → Type
    platformMeets (p , T) (design q) = designMeets p q
    platformMeets (p , T) physical = Physical p
    platformMeets (p , T) sampling = Sampling T
    platformMeets (p , T) routh = Routh p T
    platformMeets (p , T) lagged = Lagged p T
    platformMeets (p , T) fastSampling = FastSampling p T

    -- The two families; their translations are their own and do not enter the realization laws.
    designFamily : Family
    designFamily = record
      { Model = PIParams ; Req = LinearReq ; system = designSystem ; meets = designMeets
      ; translate = λ _ _ → ⊥ }

    platform : Family
    platform = record
      { Model = Platform ; Req = DigitalReq ; system = λ y → platformSystem (fst y) (snd y)
      ; meets = platformMeets ; translate = λ _ _ → ⊥ }

    open Design designFamily platform fst

    -- Within the step constraints, a platform whose design satisfies an attractive sentence
    -- satisfies it.
    sound : (s : Sentence) → Attractive s → SoundUnder designed stepConstraints s
    sound s a (p , T) hΔ c =
      let ph = hΔ physical tt
          sa = hΔ sampling tt
          st = fst (design-reading s a p) (fst (certified↔ s (p , T)) c)
      in snd (platform-reading s a p T)
           (snd (routh-iff p T ph sa) (fast p T ph sa st (hΔ fastSampling tt)))

    -- Within a positive period alone, for every inductance, a platform satisfying an attractive
    -- sentence realizes a design satisfying it: the delay never stabilizes.
    complete : (s : Sentence) → Attractive s → CompleteUnder designed periodOnly s
    complete s a (p , T) hΔ h =
      snd (certified↔ s (p , T))
        (snd (design-reading s a p) (delay p T (hΔ sampling tt) (fst (platform-reading s a p T) h)))

    exact : (s : Sentence) → Attractive s → ExactUnder' designed stepConstraints s
    exact s a y hΔ = sound s a y hΔ , complete s a y (λ q h → hΔ q (period-of-step q h))

    -- Without fast sampling the realization is not sound.
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
        context fastSampling ()

    -- Instability is realized soundly for unstable designs, at every positive period.
    sound-unstable : SoundUnder designed unstableDesign unstable
    sound-unstable (p , T) hΔ _ =
      let ph = hΔ physical tt
          sa = hΔ sampling tt
      in root p T ph sa (strict p T ph sa (hΔ (design unstable') tt))
