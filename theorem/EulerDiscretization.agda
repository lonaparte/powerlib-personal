{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.EulerDiscretization where

-- Scaffold of the explicit Euler implementation of a model: the model is a field `f` with a
-- selected point `x*`; its implementation with step `h > 0` is the discrete system `x_{k+1} = x_k +
-- h f(x_k)` (period `h`), which realizes the model it is designed from (`ofDesign`, design map `(m,
-- h) ↦ m`). The realization holds under a constraint, a small step: at an equilibrium with a
-- Hurwitz Jacobian (local exponential stability of a `C¹` field, by converse linearization) the
-- Euler Jacobian `I + h Df(x*)` is Schur for every step below a threshold, and a fixed point with a
-- Schur Jacobian is locally exponentially stable for the map (discrete linearization), so the
-- implementation is locally exponentially stable for every small step (`sound-small-step`). Without
-- the constraint the realization is not sound: at every locally exponentially stable model the
-- Jacobian is Hurwitz, and for every large enough step all multipliers `1 + hλ` of the Euler map
-- lie outside the unit disk, so the Euler implementation is unstable there
-- (`not-sound-large-step`). Lean: `converse` is
-- `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`, `threshold` is
-- `Numerics.exists_forwardEuler_schurStable` (from the forward Euler stability region), `discrete`
-- is `Map.locallyExponentiallyStable_of_schurStable` with `Numerics.hasFDerivAt_eulerMap`, `large`
-- comes from `Numerics.exists_forwardEuler_inverse_schurStable`; the template laws
-- `Numerics.euler_sound_small_step`, `Numerics.euler_certified_small_step` and
-- `Numerics.not_euler_realizationSoundUnder_of_large_step`
-- (`theorem/Numerics/EulerRealization.lean`, for autonomous families with `C¹` fields) are
-- published as connection statements (`euler_sound_small_step`, `euler_certified_small_step`,
-- `not_euler_realizationSoundUnder`) for the swing family (`theorem/Synchronous/SwingEuler.lean`)
-- and for the families of the `Euler` modules of `GFM`, `GFM/Matching`, `GFL`, `GFL/PowerLoop`,
-- `GFL/LCLine`, `Network/Swing`, `Drives`, `PLL` and `Limiting`. Nothing here is exported.

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

  module _ (Model Step : Type) (_≤_ : Step → Step → Type)
    (continuous : Model → System) (euler : Step → Model → System)
    (les : Sentence)
    (HurwitzAt : Model → Type) (SchurAt : Step → Model → Type)
    -- What Lean proves.
    (converse : (m : Model) → holds (continuous m) les → HurwitzAt m)
    (threshold : (m : Model) → HurwitzAt m →
      Σ[ h₀ ∈ Step ] ((h : Step) → h ≤ h₀ → SchurAt h m))
    (discrete : (h : Step) (m : Model) → SchurAt h m → holds (euler h m) les)
    (large : Σ[ m ∈ Model ] Σ[ h ∈ Step ] holds (continuous m) les × (¬ holds (euler h m) les))
    where

    model : Family
    model = record
      { Model = Model ; Req = ⊥ ; system = continuous ; meets = λ _ () ; translate = λ _ () }

    implementation : Family
    implementation = record
      { Model = Model × Step ; Req = ⊥ ; system = λ y → euler (snd y) (fst y)
      ; meets = λ _ () ; translate = λ _ () }

    open Design model implementation fst

    -- Small steps: a locally exponentially stable model has a step threshold below which its
    -- Euler implementation is locally exponentially stable.
    sound-small-step : (m : Model) → den model les m →
      Σ[ h₀ ∈ Step ] ((h : Step) → h ≤ h₀ → den implementation les (m , h))
    sound-small-step m hm =
      let (h₀ , hS) = threshold m (converse m hm)
      in h₀ , λ h hh → discrete h m (hS h hh)

    -- The same, as certification: certified implementations with a small enough step satisfy
    -- local exponential stability.
    certified-small-step : (y : Model × Step) → Certified designed les y →
      Σ[ h₀ ∈ Step ] ((h : Step) → h ≤ h₀ → den implementation les (fst y , h))
    certified-small-step y c = sound-small-step (fst y) (fst (certified↔ les y) c)

    -- Without a step constraint the realization is not sound.
    not-sound-large-step : ¬ SoundUnder designed (λ _ → ⊥) les
    not-sound-large-step =
      let (m , h , hm , hn) = large
      in not-sound-of-witness designed (m , h) (λ _ ()) (snd (certified↔ les (m , h)) hm) hn
