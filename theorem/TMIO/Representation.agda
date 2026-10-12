{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.TMIO.Representation where

-- Structure equivalence and dependent transport for TMIO representation changes (v0.3 §6).
-- A representation change of complete systems is an equivalence of carriers that preserves
-- satisfaction. By univalence it is a path of satisfaction structures, so every construction
-- over such structures, including the generated legal space, transports along it, and the
-- transport computes as the conversion itself. A bare bijection of carriers is not enough.
-- The public Lean endpoints are `generate_transport` and `Seed.transport_whole` in
-- `theorem/TMIO/Representation.lean`.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Unit as U

open import theorem.Conversion

-- Satisfaction of requirements `Q` by complete systems: the M—I semantics of TMIO.
record SatContext (Q : Type) : Type₁ where
  constructor satContext
  field
    Carrier : Type
    sat : Carrier → Q → Type

open SatContext

-- The legal space of a requirement family `Γ`: systems meeting every requirement of `Γ`.
Realize : {Q : Type} → SatContext Q → (Q → Type) → Type
Realize C Γ = Σ[ x ∈ Carrier C ] ((q : _) → Γ q → sat C x q)

-- A structure equivalence: an equivalence of carriers that preserves satisfaction.
record SatEquiv {Q : Type} (C D : SatContext Q) : Type₁ where
  constructor satEquiv
  field
    carrierEquiv : Carrier C ≃ Carrier D
    preserves : (x : Carrier C) (q : Q) → sat C x q ≡ sat D (equivFun carrierEquiv x) q

open SatEquiv

-- Univalence turns a structure equivalence into a path of satisfaction structures.
satPath : {Q : Type} {C D : SatContext Q} → SatEquiv C D → C ≡ D
satPath {Q} {C} {D} E i = satContext (ua (carrierEquiv E) i)
  (ua→ {e = carrierEquiv E} {B = λ _ → Q → Type} {f₀ = sat C} {f₁ = sat D}
    (λ x → funExt (preserves E x)) i)

-- Every construction over satisfaction structures transports along the path.
transportSat : {Q : Type} {C D : SatContext Q} (P : SatContext Q → Type)
  → SatEquiv C D → P C → P D
transportSat P E = subst P (satPath E)

-- In particular the legal space of every requirement family is carried over.
realizeEquiv : {Q : Type} {C D : SatContext Q} (Γ : Q → Type)
  → SatEquiv C D → Realize C Γ ≃ Realize D Γ
realizeEquiv Γ E = pathToEquiv (cong (λ C → Realize C Γ) (satPath E))

-- The carried member is the converted system: transport computes as the equivalence.
realizeEquiv-fst : {Q : Type} {C D : SatContext Q} (Γ : Q → Type) (E : SatEquiv C D)
  (r : Realize C Γ) → fst (equivFun (realizeEquiv Γ E) r) ≡ equivFun (carrierEquiv E) (fst r)
realizeEquiv-fst Γ E r = uaβ (carrierEquiv E) (fst r)

-- A bare bijection is not a structure equivalence: on one carrier, a satisfiable and an
-- unsatisfiable structure admit no structure equivalence at all.
satisfiable unsatisfiable : SatContext U.Unit
satisfiable = satContext Bool (λ _ _ → U.Unit)
unsatisfiable = satContext Bool (λ _ _ → ⊥)

noSatEquiv : SatEquiv satisfiable unsatisfiable → ⊥
noSatEquiv E = snd carried U.tt U.tt
  where
  carried : Realize unsatisfiable (λ _ → U.Unit)
  carried = transportSat (λ C → Realize C (λ _ → U.Unit)) E (true , λ _ _ → U.tt)

-- The RL instance: requirements on impedance models, read on state-space models through the
-- executable conversion of `theorem.Conversion`. Preservation holds by definition.
module RL (ops : Operations) {Q : Type} (meets : Impedance (Operations.Scalar ops)
    (Operations.Unit ops) → Q → Type) where
  open Checked ops

  impedanceContext : SatContext Q
  impedanceContext = satContext Z meets

  stateSpaceContext : SatContext Q
  stateSpaceContext = satContext SS (λ x q → meets (toImpedance x) q)

  stateSpaceEquiv : SatEquiv stateSpaceContext impedanceContext
  stateSpaceEquiv = satEquiv modelEquiv (λ _ _ → refl)

  -- The legal state-space space corresponds to the legal impedance space ...
  realizeStateSpace : (Γ : Q → Type)
    → Realize stateSpaceContext Γ ≃ Realize impedanceContext Γ
  realizeStateSpace Γ = realizeEquiv Γ stateSpaceEquiv

  -- ... and the correspondence is the executable conversion itself.
  realizeStateSpace-conversion : (Γ : Q → Type) (r : Realize stateSpaceContext Γ)
    → fst (equivFun (realizeStateSpace Γ) r) ≡ toImpedance (fst r)
  realizeStateSpace-conversion Γ r = realizeEquiv-fst Γ stateSpaceEquiv r
