{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.LTIFoundation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.List using (List; []; _∷_; _++_)

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

-- Intrinsically scoped syntax: index 0 is the most recently bound coordinate.
-- Unlike the old reifier, both matrix indices and the state index are retained.
data Expr (scope : ℕ) : Type where
  matrixEntry : Fin scope → Fin scope → Expr scope
  stateEntry : Fin scope → Expr scope
  mulExpr : Expr scope → Expr scope → Expr scope
  sumExpr : Expr (suc scope) → Expr scope

extend : {I : Type} {scope : ℕ} → I → (Fin scope → I) → Fin (suc scope) → I
extend j env fzero = j
extend j env (fsuc k) = env k

eval : {I S : Type} {scope : ℕ} → ((I → S) → S) → (S → S → S)
     → (I → I → S) → (I → S) → (Fin scope → I) → Expr scope → S
eval sum mul A x env (matrixEntry i j) = A (env i) (env j)
eval sum mul A x env (stateEntry j) = x (env j)
eval sum mul A x env (mulExpr a b) = mul (eval sum mul A x env a) (eval sum mul A x env b)
eval sum mul A x env (sumExpr a) = sum (λ j → eval sum mul A x (extend j env) a)

-- The outer environment contains i; sum introduces j at index 0 and shifts i.
body : Expr 1
body = sumExpr (mulExpr (matrixEntry (fsuc fzero) fzero) (stateEntry fzero))

-- Execute the very same syntax tree that is serialized below: no lossy probe.
run : {I S : Type} → ((I → S) → S) → (S → S → S)
    → (I → I → S) → (I → S) → I → S
run sum mul A x i = eval sum mul A x (λ _ → i) body

-- Independent semantic contract. A changed index or interpreter must still
-- prove this equation for arbitrary coordinates, matrices and states.
run-spec : {I S : Type} → (sum : (I → S) → S) → (mul : S → S → S)
    → (A : I → I → S) → (x : I → S) → (i : I)
    → run sum mul A x i ≡ sum (λ j → mul (A i j) (x j))
run-spec sum mul A x i = refl

fieldAgrees : {I S : Type} → (sum : (I → S) → S) → (mul : S → S → S)
    → (m : StateSpace I S) → (x : I → S) → (i : I)
    → run sum mul (StateSpace.matrix m) x i ≡ run sum mul (RowModel.rows (toRows m)) x i
fieldAgrees sum mul (stateSpace A) x i = refl

-- The versioned wire carries de Bruijn indices with each variable occurrence.
encode : {scope : ℕ} → Expr scope → List ℕ
encode (matrixEntry i j) = 0 ∷ toℕ i ∷ toℕ j ∷ []
encode (stateEntry j) = 1 ∷ toℕ j ∷ []
encode (mulExpr x y) = 2 ∷ (encode x ++ encode y)
encode (sumExpr x) = 3 ∷ encode x

wire : List ℕ
wire = 20261004 ∷ 3 ∷ encode body
