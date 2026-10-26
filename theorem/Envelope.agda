{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Envelope where

-- Scaffold of the parameters of the envelope sentences: safety over a horizon `T` at a level `ε`,
-- with a safe set `A` in the system. The denotation of safety sends the supremum of a set of
-- horizons to the intersection of the denotations (`sup-meet`) and is antitone in the horizon;
-- then the longest horizon certified for a set of models, the supremum of the horizons whose
-- denotation contains it, is the upper adjoint of the denotation (`galois`): a horizon is
-- certified exactly when it is at most the certified horizon. The level enters the same way, with
-- the worst exceedance probability of a set of models as the upper adjoint. The safe set enters
-- through meets only almost surely; at a positive level two certified safe sets can have an
-- uncertified intersection, and then no certified safe set is least (`no-least`).
--
-- Lean (`theorem/Envelope/Basic.lean`): `sup-meet` is `Envelope.den_safe_sSup`, `antitone` is
-- `Envelope.den_safe_antitone`, `galois` is `Envelope.le_certifiedHorizon_iff` with the generated
-- adjoint `Envelope.generate_certifiedHorizon`; the level is `Envelope.den_safe_iInf`,
-- `Envelope.gc_worstExceedance`, `Envelope.generate_worstExceedance`; `no-least` is
-- `Envelope.not_isLeast_safe` with the witness `Envelope.not_holds_safe_inter`, and the almost
-- sure meets are `Envelope.holds_safe_iInter_null`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading

-- Inclusion of predicates.
_⊆_ : {M : Type} → (M → Type) → (M → Type) → Type
D ⊆ E = ∀ x → D x → E x

module Horizons (Model Horizon : Type) (_≤_ : Horizon → Horizon → Type)
  (sup : (Horizon → Type) → Horizon)
  (den : Horizon → Model → Type)
  -- What Lean proves.
  (sup-meet : (H : Horizon → Type) (D : Model → Type) →
    (D ⊆ den (sup H)) ↔ ((T : Horizon) → H T → D ⊆ den T))
  (le-sup : (H : Horizon → Type) (T : Horizon) → H T → T ≤ sup H)
  (antitone : (T T' : Horizon) → T ≤ T' → den T' ⊆ den T)
  where

  -- The longest horizon certified for a set of models.
  certified : (Model → Type) → Horizon
  certified D = sup (λ T → D ⊆ den T)

  -- The Galois law: a horizon is certified exactly when it is at most the certified horizon.
  galois : (D : Model → Type) (T : Horizon) → (T ≤ certified D) ↔ (D ⊆ den T)
  galois D T =
    (λ h x hx → antitone T (certified D) h x
      (snd (sup-meet (λ T → D ⊆ den T) D) (λ _ c → c) x hx)) ,
    le-sup (λ T → D ⊆ den T) T

module SafeSets (Safe : Type) (_⊆'_ : Safe → Safe → Type) (_∩_ : Safe → Safe → Safe)
  (∩-l : (A B : Safe) → (A ∩ B) ⊆' A) (∩-r : (A B : Safe) → (A ∩ B) ⊆' B)
  (∩-glb : (L A B : Safe) → L ⊆' A → L ⊆' B → L ⊆' (A ∩ B))
  (Certified : Safe → Type)
  -- What Lean proves.
  (upward : (A A' : Safe) → A ⊆' A' → Certified A → Certified A')
  (A₁ A₂ : Safe) (c₁ : Certified A₁) (c₂ : Certified A₂) (not-inter : ¬ Certified (A₁ ∩ A₂))
  where

  -- A least certified safe set.
  Least : Safe → Type
  Least L = Certified L × ((A : Safe) → Certified A → L ⊆' A)

  -- Two certified safe sets with an uncertified intersection leave no least certified safe set.
  no-least : (L : Safe) → ¬ Least L
  no-least L (cL , low) = not-inter (upward L (A₁ ∩ A₂) (∩-glb L A₁ A₂ (low A₁ c₁) (low A₂ c₂)) cL)
