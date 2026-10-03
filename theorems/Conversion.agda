{-# OPTIONS --cubical --safe --guardedness #-}
module theorems.Conversion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_; _++_)

-- Scalar is the coefficient domain; Unit represents positive scaling factors.
-- Lean supplies the real-number instance and proves these algebraic laws there.
record Operations : Type₁ where
  field
    Scalar Unit : Type
    scale : Scalar → Unit → Scalar
    reciprocal : Unit → Unit
    involutive : (y : Unit) → reciprocal (reciprocal y) ≡ y
    cancel : (x : Scalar) (y : Unit) → scale (scale x (reciprocal y)) y ≡ x

record StateSpace (Scalar Unit : Type) : Type where
  constructor state
  field
    decay : Scalar
    inputGain : Unit

record Impedance (Scalar Unit : Type) : Type where
  constructor impedance
  field
    resistance : Scalar
    inductance : Unit

-- One executable body serves BOTH directions of the RL conversion.
run : {Scalar Unit : Type} → (Scalar → Unit → Scalar) → (Unit → Unit)
    → Scalar × Unit → Scalar × Unit
run scale reciprocal x = scale (fst x) (reciprocal (snd x)) , reciprocal (snd x)

module Checked (ops : Operations) where
  open Operations ops
  SS = StateSpace Scalar Unit
  Z = Impedance Scalar Unit

  toImpedance : SS → Z
  toImpedance (state a b) =
    let x = run scale reciprocal (a , b) in impedance (fst x) (snd x)

  toStateSpace : Z → SS
  toStateSpace (impedance r l) =
    let x = run scale reciprocal (r , l) in state (fst x) (snd x)

  recover : (x : Scalar) (y : Unit)
    → scale (scale x (reciprocal y)) (reciprocal (reciprocal y)) ≡ x
  recover x y = cong (scale (scale x (reciprocal y))) (involutive y) ∙ cancel x y

  fromTo : (x : SS) → toStateSpace (toImpedance x) ≡ x
  fromTo (state a b) i = state (recover a b i) (involutive b i)

  toFrom : (x : Z) → toImpedance (toStateSpace x) ≡ x
  toFrom (impedance r l) i = impedance (recover r l i) (involutive l i)

  modelEquiv : SS ≃ Z
  modelEquiv = isoToEquiv (iso toImpedance toStateSpace toFrom fromTo)

  modelPath : SS ≡ Z
  modelPath = ua modelEquiv

  transportAgrees : (x : SS) → transport modelPath x ≡ toImpedance x
  transportAgrees = uaβ modelEquiv

-- Reify the ACTUAL executable body above into a small, versioned data interface.
-- Only projection, scaling and reciprocal are supported; no source text crosses it.
data Expr : Type where
  first second : Expr
  mul : Expr → Expr → Expr
  inv : Expr → Expr

encode : Expr → List ℕ
encode first = 0 ∷ []
encode second = 1 ∷ []
encode (mul x y) = 2 ∷ (encode x ++ encode y)
encode (inv x) = 3 ∷ encode x

body : Expr × Expr
body = run mul inv (first , second)

wire : List ℕ
wire = 20261003 ∷ 1 ∷ (encode (fst body) ++ encode (snd body))
