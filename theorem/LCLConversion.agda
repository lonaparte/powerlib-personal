{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.LCLConversion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_; _++_)
import theorem.Conversion as RL

record Circuit (Scalar Unit : Type) : Type where
  constructor circuit
  field
    firstBranch secondBranch : Scalar × Unit
    capacitance : Unit

record StateSpace (Scalar Unit : Type) : Type where
  constructor state
  field
    firstBranch secondBranch : Scalar × Unit
    capacitorGain : Unit

Payload : Type → Type → Type
Payload Scalar Unit = ((Scalar × Unit) × (Scalar × Unit)) × Unit

-- The RL branch conversion is reused twice; the capacitor gain is reciprocal C.
run : {Scalar Unit : Type} → (Scalar → Unit → Scalar) → (Unit → Unit)
    → Payload Scalar Unit → Payload Scalar Unit
run scale reciprocal x =
  (RL.run scale reciprocal (fst (fst x)) , RL.run scale reciprocal (snd (fst x))) ,
  reciprocal (snd x)

module Checked (ops : RL.Operations) where
  open RL.Operations ops
  module Branch = RL.Checked ops
  SS = StateSpace Scalar Unit
  LC = Circuit Scalar Unit

  toStateSpace : LC → SS
  toStateSpace (circuit first second cap) =
    let x = run scale reciprocal ((first , second) , cap)
    in state (fst (fst x)) (snd (fst x)) (snd x)

  toCircuit : SS → LC
  toCircuit (state first second gain) =
    let x = run scale reciprocal ((first , second) , gain)
    in circuit (fst (fst x)) (snd (fst x)) (snd x)

  fromTo : (x : LC) → toCircuit (toStateSpace x) ≡ x
  fromTo (circuit (a , b) (d , e) cap) i =
    circuit (Branch.recover a b i , involutive b i)
            (Branch.recover d e i , involutive e i) (involutive cap i)

  toFrom : (x : SS) → toStateSpace (toCircuit x) ≡ x
  toFrom (state (a , b) (d , e) gain) i =
    state (Branch.recover a b i , involutive b i)
          (Branch.recover d e i , involutive e i) (involutive gain i)

  modelEquiv : LC ≃ SS
  modelEquiv = isoToEquiv (iso toStateSpace toCircuit toFrom fromTo)

  modelPath : LC ≡ SS
  modelPath = ua modelEquiv

  transportAgrees : (x : LC) → transport modelPath x ≡ toStateSpace x
  transportAgrees = uaβ modelEquiv

data Expr : Type where
  input : ℕ → Expr
  mul : Expr → Expr → Expr
  inv : Expr → Expr

encode : Expr → List ℕ
encode (input index) = 0 ∷ index ∷ []
encode (mul x y) = 1 ∷ (encode x ++ encode y)
encode (inv x) = 2 ∷ encode x

body : Payload Expr Expr
body = run mul inv (((input 0 , input 2) , (input 1 , input 3)) , input 4)

wire : List ℕ
wire = 20261004 ∷ 1 ∷
  (encode (fst (fst (fst body))) ++ encode (snd (fst (fst body))) ++
   encode (fst (snd (fst body))) ++ encode (snd (snd (fst body))) ++ encode (snd body))
