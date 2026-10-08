{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.ImpedanceInterconnection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_; _++_)
record PortModel (M : Type) : Type where
  constructor portModel
  field state input output feedthrough : M

record StrictPortModel (M : Type) : Type where
  constructor strictPortModel
  field state input output : M

record Interconnection (M : Type) : Type where
  constructor interconnection
  field
    source : PortModel M
    load : StrictPortModel M
record ClosedLoop (M : Type) : Type where
  constructor closedLoop
  field a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ c₁ c₂ d : M
record Ops (M : Type) : Type where
  field
    times : M → M → M
    minus : M → M
    diff : M → M → M
data Tag : Type where
  A₁ B₁ C₁ D₁ A₂ B₂ C₂ : Tag

entry : {M : Type} → Interconnection M → Tag → M
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) A₁ = a
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) B₁ = b
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) C₁ = c
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) D₁ = d
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) A₂ = a'
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) B₂ = b'
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) C₂ = c'
data Expr : Type where
  mat : Tag → Expr
  mul : Expr → Expr → Expr
  neg : Expr → Expr
  sub : Expr → Expr → Expr

eval : {M : Type} → Ops M → (Tag → M) → Expr → M
eval ops env (mat t) = env t
eval ops env (mul x y) = Ops.times ops (eval ops env x) (eval ops env y)
eval ops env (neg x) = Ops.minus ops (eval ops env x)
eval ops env (sub x y) = Ops.diff ops (eval ops env x) (eval ops env y)
body : ClosedLoop Expr
body = closedLoop (mat A₁) (mul (mat B₁) (mat C₂)) (neg (mul (mat B₂) (mat C₁)))
                  (sub (mat A₂) (mul (mul (mat B₂) (mat D₁)) (mat C₂)))
                  (neg (mat B₁)) (mul (mat B₂) (mat D₁))
                  (neg (mat C₁)) (neg (mul (mat D₁) (mat C₂)))
                  (mat D₁)
mapClosedLoop : {X Y : Type} → (X → Y) → ClosedLoop X → ClosedLoop Y
mapClosedLoop f (closedLoop a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ c₁ c₂ d) =
  closedLoop (f a₁₁) (f a₁₂) (f a₂₁) (f a₂₂) (f b₁) (f b₂) (f c₁) (f c₂) (f d)
toClosedLoop : {M : Type} → Ops M → Interconnection M → ClosedLoop M
toClosedLoop ops x = mapClosedLoop (eval ops (entry x)) body
toClosedLoop-spec : {M : Type} (ops : Ops M) (a b c d a' b' c' : M) →
  toClosedLoop ops (interconnection (portModel a b c d) (strictPortModel a' b' c')) ≡
    closedLoop a (Ops.times ops b c') (Ops.minus ops (Ops.times ops b' c))
               (Ops.diff ops a' (Ops.times ops (Ops.times ops b' d) c'))
               (Ops.minus ops b) (Ops.times ops b' d)
               (Ops.minus ops c) (Ops.minus ops (Ops.times ops d c'))
               d
toClosedLoop-spec ops a b c d a' b' c' = refl
tag : Tag → ℕ
tag A₁ = 0
tag B₁ = 1
tag C₁ = 2
tag D₁ = 3
tag A₂ = 4
tag B₂ = 5
tag C₂ = 6

encode : Expr → List ℕ
encode (mat t) = 0 ∷ tag t ∷ []
encode (mul x y) = 1 ∷ (encode x ++ encode y)
encode (neg x) = 2 ∷ encode x
encode (sub x y) = 3 ∷ (encode x ++ encode y)

wire : List ℕ
wire = 20261006 ∷ 2 ∷
  (encode (ClosedLoop.a₁₁ body) ++ encode (ClosedLoop.a₁₂ body) ++
   encode (ClosedLoop.a₂₁ body) ++ encode (ClosedLoop.a₂₂ body) ++
   encode (ClosedLoop.b₁ body) ++ encode (ClosedLoop.b₂ body) ++
   encode (ClosedLoop.c₁ body) ++ encode (ClosedLoop.c₂ body) ++
   encode (ClosedLoop.d body))
