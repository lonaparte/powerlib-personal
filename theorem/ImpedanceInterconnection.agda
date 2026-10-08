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
module _ {M : Type} (ops : Ops M) where
  open Ops ops

  record Laws : Type where
    field
      assoc : (x y z : M) → times (times x y) z ≡ times x (times y z)
      mul-minus : (x y : M) → times x (minus y) ≡ minus (times x y)
      minus-mul : (x y : M) → times (minus x) y ≡ minus (times x y)
      mul-diff : (x y z : M) → times x (diff y z) ≡ diff (times x y) (times x z)
      diff-mul : (x y z : M) → times (diff x y) z ≡ diff (times x z) (times y z)

  changeCoordinates : (t₁ t₁' t₂ t₂' : M) → Interconnection M → Interconnection M
  changeCoordinates t₁ t₁' t₂ t₂' (interconnection (portModel a b c d) (strictPortModel a' b' c')) =
    interconnection (portModel (times (times t₁ a) t₁') (times t₁ b) (times c t₁') d)
                    (strictPortModel (times (times t₂ a') t₂') (times t₂ b') (times c' t₂'))

  conjugate : (t₁ t₁' t₂ t₂' : M) → ClosedLoop M → ClosedLoop M
  conjugate t₁ t₁' t₂ t₂' (closedLoop a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ c₁ c₂ d) =
    closedLoop (times (times t₁ a₁₁) t₁') (times (times t₁ a₁₂) t₂')
               (times (times t₂ a₂₁) t₁') (times (times t₂ a₂₂) t₂')
               (times t₁ b₁) (times t₂ b₂) (times c₁ t₁') (times c₂ t₂') d

  module _ (laws : Laws) where
    open Laws laws

    sandwich : (t x y t' : M) → times (times t x) (times y t') ≡ times (times t (times x y)) t'
    sandwich t x y t' =
      assoc t x (times y t') ∙ cong (times t) (sym (assoc x y t')) ∙ sym (assoc t (times x y) t')

    toClosedLoop-covariant : (t₁ t₁' t₂ t₂' : M) (x : Interconnection M) →
      toClosedLoop ops (changeCoordinates t₁ t₁' t₂ t₂' x) ≡
        conjugate t₁ t₁' t₂ t₂' (toClosedLoop ops x)
    toClosedLoop-covariant t₁ t₁' t₂ t₂'
        (interconnection (portModel a b c d) (strictPortModel a' b' c')) =
      λ i → closedLoop (times (times t₁ a) t₁') (p₁₂ i) (p₂₁ i) (p₂₂ i)
                       (sym (mul-minus t₁ b) i) (assoc t₂ b' d i)
                       (sym (minus-mul c t₁') i) (p₂ i) d
      where
      p₁₂ = sandwich t₁ b c' t₂'
      p₂₁ = cong minus (sandwich t₂ b' c t₁') ∙ sym (minus-mul (times t₂ (times b' c)) t₁') ∙
            cong (λ u → times u t₁') (sym (mul-minus t₂ (times b' c)))
      q = cong (λ u → times u (times c' t₂')) (assoc t₂ b' d) ∙ sandwich t₂ (times b' d) c' t₂'
      p₂₂ = cong (diff (times (times t₂ a') t₂')) q ∙
            sym (diff-mul (times t₂ a') (times t₂ (times (times b' d) c')) t₂') ∙
            cong (λ u → times u t₂') (sym (mul-diff t₂ a' (times (times b' d) c')))
      p₂ = cong minus (sym (assoc d c' t₂')) ∙ sym (minus-mul (times d c') t₂')

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
