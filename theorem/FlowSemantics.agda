{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.FlowSemantics where

-- The semantic layer as the per-object reading scaffolds use it: real scalars (operations and
-- order only), fields at a selected point, affine changes of coordinates, the sentence kinds of the
-- local translation tables, and satisfaction, abstract but invariant under affine changes of
-- coordinates. Lean supplies ℝ, `Dynamics.State n`, `Flow.Property` and `Sentence.holds`; it
-- proves the invariance (`Dynamics.holds_transport_iff`, with `Flow.Property.holds_shift_iff` for
-- the selected point) and every algebraic fact a reading scaffold leaves as an obligation. Nothing
-- here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.FamilyReading

-- Real scalars: operations and order. No law is assumed; a scaffold names the facts it needs.
record Scalars : Type₁ where
  infixl 6 _+_ _-_
  infixl 7 _*_ _/_
  infix 4 _<_ _≤_
  field
    ℝ : Type
    0r halfπ : ℝ
    _+_ _-_ _*_ _/_ : ℝ → ℝ → ℝ
    -_ : ℝ → ℝ
    sin cos : ℝ → ℝ
    _<_ _≤_ : ℝ → ℝ → Type

-- The sentence kinds of the local translation tables; `global` stands for the sentences the
-- requirements do not decide (global stability, decay rates, sampled contraction, conservation).
data Sentence : Type where
  lyapunovStable locallyAsymptoticallyStable locallyExponentiallyStable unstable : Sentence
  global passive : Sentence

-- The flow sentences (every sentence but passivity).
Flow : Sentence → Type
Flow passive = ⊥
Flow _ = Unit

-- The local translation table (Lean `Spectral.localTable`): Lyapunov stability to `Rl`, local
-- asymptotic and local exponential stability to `Rs`, instability to `Ru`, passivity to `Rp`, the
-- global sentences to the whole language.
localTable : {Q : Type} → (Q → Type) → (Q → Type) → (Q → Type) → (Q → Type) → Sentence → Q → Type
localTable Rl Rs Ru Rp lyapunovStable = Rl
localTable Rl Rs Ru Rp locallyAsymptoticallyStable = Rs
localTable Rl Rs Ru Rp locallyExponentiallyStable = Rs
localTable Rl Rs Ru Rp unstable = Ru
localTable Rl Rs Ru Rp global = λ _ → Unit
localTable Rl Rs Ru Rp passive = Rp

-- A field with a selected point (Lean reads a model's flow sentences on its field at its point).
System : Type → Type
System X = (X → X) × X

-- An affine change of coordinates `y = T x + c`: its action on points, the inverse action, and its
-- linear part on vectors.
record Affine (X : Type) : Type where
  field
    point pointInv vector : X → X

-- The field in the new coordinates and the image of the point (Lean `Dynamics.transportField`,
-- `Dynamics.affineCoord`).
transportSystem : {X : Type} → Affine X → System X → System X
transportSystem A (f , x) = (λ y → Affine.vector A (f (Affine.pointInv A y))) , Affine.point A x

-- The semantic layer on the states `X`: satisfaction, invariant under affine changes of
-- coordinates. Families on `X` and their readings by conjugacy live here.
module Flows (X : Type) (holds : System X → Sentence → Type)
  (invariant : (A : Affine X) (a : System X) (s : Sentence) →
    holds (transportSystem A a) s ≃ holds a s)
  where

  flowSemantics : Semantics
  flowSemantics = record { System = System X ; Sentence = Sentence ; holds = holds }

  open Readings flowSemantics public

  affine : Invariance
  affine = record { Conj = Affine X ; act = transportSystem ; invariant = invariant }
