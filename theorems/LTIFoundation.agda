{-# OPTIONS --cubical --safe --guardedness #-}
module theorems.LTIFoundation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Agda.Builtin.Bool using (Bool; false)

-- Index is instantiated by a finite coordinate set in the Lean endpoint.
record StateSpace (Index Scalar : Type) : Type where
  constructor stateSpace
  field matrix : Index → Index → Scalar

record RowModel (Index Scalar : Type) : Type where
  constructor rowModel
  field rows : Index → (Index → Scalar)

toRows : {I S : Type} → StateSpace I S → RowModel I S
toRows (stateSpace A) = rowModel A

toStateSpace : {I S : Type} → RowModel I S → StateSpace I S
toStateSpace (rowModel A) = stateSpace A

fromTo : {I S : Type} → (m : StateSpace I S) → toStateSpace (toRows m) ≡ m
fromTo (stateSpace A) = refl

toFrom : {I S : Type} → (m : RowModel I S) → toRows (toStateSpace m) ≡ m
toFrom (rowModel A) = refl

modelEquiv : {I S : Type} → StateSpace I S ≃ RowModel I S
modelEquiv = isoToEquiv (iso toRows toStateSpace toFrom fromTo)

modelPath : {I S : Type} → StateSpace I S ≡ RowModel I S
modelPath = ua modelEquiv

transportAgrees : {I S : Type} → (m : StateSpace I S) → transport modelPath m ≡ toRows m
transportAgrees = uaβ modelEquiv

-- The executable field operation exported through the restricted interface.
run : {I S : Type} → ((I → S) → S) → (S → S → S)
    → (I → I → S) → (I → S) → I → S
run sum mul A x i = sum (λ j → mul (A i j) (x j))

fieldAgrees : {I S : Type} → (sum : (I → S) → S) → (mul : S → S → S)
    → (m : StateSpace I S) → (x : I → S) → (i : I)
    → run sum mul (StateSpace.matrix m) x i ≡ run sum mul (RowModel.rows (toRows m)) x i
fieldAgrees sum mul (stateSpace A) x i = refl

-- Matrix/state symbols stand for the bound column coordinate. Reification
-- evaluates the actual polymorphic executable operation, not a separate formula.
data Expr : Type where
  matrixEntry stateEntry : Expr
  mulExpr : Expr → Expr → Expr
  sumExpr : Expr → Expr

encode : Expr → List ℕ
encode matrixEntry = 0 ∷ []
encode stateEntry = 1 ∷ []
encode (mulExpr x y) = 2 ∷ (encode x ++ encode y)
encode (sumExpr x) = 3 ∷ encode x

body : Expr
body = run {I = Bool} (λ f → sumExpr (f false)) mulExpr
  (λ _ _ → matrixEntry) (λ _ → stateEntry) false

wire : List ℕ
wire = 20261004 ∷ 2 ∷ encode body
