{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.EulerDiscretization where

-- Scaffold of the explicit Euler implementation of a model: the model is a field `f` with a
-- selected point `x*`; its implementation with step `h > 0` is the discrete system
-- `x_{k+1} = x_k + h f(x_k)` (period `h`), which realizes the model it is designed from
-- (`ofDesign`, design map `(m, h) ↦ m`). The realization holds under a constraint, a small step:
-- at an equilibrium with a Hurwitz Jacobian (local exponential stability of a `C¹` field, by
-- converse linearization) the Euler Jacobian `I + h Df(x*)` is Schur for every step below a
-- threshold, and a fixed point with a Schur Jacobian is locally exponentially stable for the map
-- (discrete linearization), so the implementation is locally exponentially stable for every small
-- step (`sound-small-step`). Lean proves converse linearization
-- (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`), discrete linearization
-- (`Map.locallyExponentiallyStable_of_schurStable`), the step threshold (from the forward Euler
-- stability region, `Numerics.forwardEuler_schurStable_iff`) and the realization, generically for
-- autonomous families with `C¹` fields and for the swing family, in
-- `theorem/Numerics/EulerRealization.lean`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

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
