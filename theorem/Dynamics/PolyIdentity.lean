import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Lean.Meta.Sym.Arith.ToExpr
import theorem.Attributes

/-! # Kernel-checked multivariate polynomial identities by reflection (foundation)

A polynomial identity `lhs = rhs` with integer coefficients, in any commutative ring and in any
atoms, holds when the normal form of `lhs − rhs` is empty. The normal form is computed by an
executable function on sparse polynomials, so the identity is decided by the kernel
(`decide +kernel`) instead of `ring`, whose proof terms and checking time grow with every
intermediate normalization step; the soundness of the normal form is proved once
(`eq_of_check`). The tactic `poly_rfl` reifies the goal and runs the check.

Scope.
* Generic: any commutative ring `α`; expressions are the ring expressions
  `Lean.Grind.CommRing.Expr` of Lean core (numerals, variables, `+`, `−`, `·`, negation,
  powers with literal exponents), read in `α` by Lean's `Expr.denote`; at most `46` atoms.
  Exact identities only, no inequality, no division (a quotient is an atom).
* Data: a sparse polynomial is a list of (monomial code, integer coefficient); the monomial
  `∏ xᵢ^{eᵢ}` is the code `∏ pᵢ^{eᵢ}` (`pᵢ` the `i`-th prime), so a product of monomials is a
  product of natural numbers (computed by the kernel's arbitrary-precision arithmetic) and the
  value of a code is read through the `pᵢ`-adic valuations. The operations are written with the
  recursors, and every chain of reduction steps that produces no constructor passes through the
  constant `tick`, so that the kernel's recursion depth stays bounded.
* Performance (measured, sanity information): the identity `(x₁ + … + x₈ + 1)⁷ = ` its expansion
  (6435 terms, balanced sum) is checked by the kernel in about 30 s; the expansion of the
  Bilharz determinant `Δ₈` of a complex quintic with polynomial coefficients (2922 terms) in
  about 40 s.

Source: the reflection pattern of `theorem/Dynamics/PolyCertificate.lean` (univariate) and
`theorem/Linear/VerifiedSynthesis.lean` (an executable check whose soundness is proved once); the
ring expressions and their denotation are those of Lean core's `grind` ring solver
(`Init/Grind/Ring/CommSolver.lean`); Gödel's prime-power encoding of exponent vectors.

Results.
* Monomial codes: `primes`, `code`, `mval` (the value `∏_{i<n} xᵢ^{v_{pᵢ}(m)}`); `mval_one`,
  `mval_mul` (multiplicative on nonzero codes), `mval_code` (the code of `xᵢ` is read as `xᵢ`).
* Sparse polynomials (`SPoly`) and their value `eval`: `merge` (sum of ordered lists),
  `scale`, `pairs`, `sumRounds`, `sum`, `mul`, `pow`, `const`, `sgn`, the flattening `toTerms`
  and the normal form `toSPoly`; `eval_merge`, `eval_scale`, `eval_sum`, `eval_mul`, `eval_pow`,
  `eval_const`, `eval_sgn`, `evalSum_toTerms`, **`eval_toSPoly`** (the normal form has the value
  of the expression), and the nonvanishing of the codes (`Pos`, `pos_*`, `allPos_toTerms`).
* The check `check` (variables below `n ≤ 46`, empty normal form of `a − b`) and
  **`eq_of_check`**: a passed check proves `a.denote ctx = b.denote ctx` in every commutative
  ring.
* The tactic `poly_rfl`: reification of `lhs = rhs` over its atoms and `decide +kernel` on
  `check`.

Family and connection conclusions.
* None: static algebra, a proof device for polynomial identities of model statements.
-/

namespace powerlib.Dynamics.PolyIdentity
open Lean.Grind.CommRing (Expr Context)
/-! ## Monomial codes -/

/-- The first 46 primes: the monomial `∏ xᵢ^{eᵢ}` is the code `∏ pᵢ^{eᵢ}`. -/
def primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199]

/-- The code of the variable `xᵢ`: the `i`-th prime (`1` beyond the list). -/
def code (i : ℕ) : ℕ := primes.getD i 1

/-! ## Sparse polynomials -/

noncomputable section

/-- A sparse polynomial with integer coefficients: a list of (monomial code, coefficient),
ordered by increasing code. The operations below are written with the recursors (no fuel, no
matcher) so that the kernel evaluates them directly. -/
abbrev SPoly := List (ℕ × ℤ)

/-- The identity, as a separate constant: a chain of reduction steps that produces no constructor
(a run of cancellations, a long traversal) passes through it at every step, so that the kernel
returns to its outer reduction loop and its recursion depth stays bounded. -/
def tick {β : Sort _} (b : β) : β := b

/-- Merge of two sparse polynomials ordered by increasing code: equal codes are added and zero
sums dropped (nested structural recursion: the outer recursion on `p` supplies `merge p'`, the
inner one on `q` supplies `merge (a :: p') q'`). -/
def merge : SPoly → SPoly → SPoly :=
  @List.rec (ℕ × ℤ) (fun _ => SPoly → SPoly) (fun q => q) fun a p ihp =>
    @List.rec (ℕ × ℤ) (fun _ => SPoly) (a :: p) fun b q ihq =>
      Bool.rec
        (Bool.rec (b :: ihq) (a :: ihp (b :: q)) (Nat.blt a.1 b.1))
        (Bool.rec ((a.1, Int.add a.2 b.2) :: ihp q) (tick (ihp q)) (Int.beq' (Int.add a.2 b.2) 0))
        (Nat.beq a.1 b.1)

/-- Product with the term `c · x^m`. -/
def scale (m : ℕ) (c : ℤ) : SPoly → SPoly :=
  @List.rec (ℕ × ℤ) (fun _ => SPoly) [] fun t _ ih => (Nat.mul m t.1, Int.mul c t.2) :: ih

/-- One round of pairwise sums, `[p₁ + p₂, p₃ + p₄, …]`, with the pending unpaired element as the
second argument. -/
def pairs : List SPoly → Option SPoly → List SPoly :=
  @List.rec SPoly (fun _ => Option SPoly → List SPoly)
    (fun o => @Option.rec SPoly (fun _ => List SPoly) [] (fun p => [p]) o)
    (fun q _ ih o => @Option.rec SPoly (fun _ => List SPoly) (ih (some q))
      (fun p => merge p q :: ih none) o)

/-- `k` rounds of pairwise sums, then the sum of what is left. -/
def sumRounds : ℕ → List SPoly → SPoly :=
  @Nat.rec (fun _ => List SPoly → SPoly) (fun l => l.foldr merge [])
    (fun _ ih l => @List.rec SPoly (fun _ => SPoly) []
      (fun p l' _ => @List.rec SPoly (fun _ => SPoly) p (fun _ _ _ => tick (ih (pairs l none))) l')
      l)

/-- The sum of a list of sparse polynomials (`64` rounds of pairwise sums). -/
def sum (l : List SPoly) : SPoly := sumRounds 64 l

/-- Is the first list at most as long as the second? (Simultaneous traversal.) -/
def shorter : SPoly → SPoly → Bool :=
  @List.rec (ℕ × ℤ) (fun _ => SPoly → Bool) (fun _ => true) fun _ _ ih q =>
    @List.rec (ℕ × ℤ) (fun _ => Bool) false (fun _ q' _ => tick (ih q')) q

/-- The scaled copies `t · q`, `t` a term of `p`. -/
def scaled (q : SPoly) : SPoly → List SPoly :=
  @List.rec (ℕ × ℤ) (fun _ => List SPoly) [] fun t _ ih => scale t.1 t.2 q :: ih

/-- Product: the sum of the scaled copies of the longer factor by the terms of the shorter. -/
def mul (p q : SPoly) : SPoly :=
  Bool.rec (sum (scaled q p)) (sum (scaled p q)) (shorter q p)

/-- Power. -/
def pow (p : SPoly) (k : ℕ) : SPoly :=
  @Nat.rec (fun _ => SPoly) [(1, 1)] (fun _ ih => mul ih p) k

/-- A constant. -/
def const (k : ℤ) : SPoly := Bool.rec [(1, k)] [] (Int.beq' k 0)

/-- The sign `−1` (if `s`) applied to a polynomial. -/
def sgn (s : Bool) (p : SPoly) : SPoly := Bool.rec p (scale 1 (-1) p) s

/-- The summands of `±e` (sign `s`), prepended to `acc`: sums and differences are flattened,
every other node is normalized (products and powers of normalized factors). -/
def toTerms (e : Expr) : Bool → List SPoly → List SPoly :=
  @Expr.rec (fun _ => Bool → List SPoly → List SPoly)
    (fun k s acc => sgn s (const k) :: acc)
    (fun k s acc => sgn s (const k) :: acc)
    (fun k s acc => sgn s (const k) :: acc)
    (fun i s acc => sgn s [(code i, 1)] :: acc)
    (fun _ ih s acc => tick (ih (!s) acc))
    (fun _ _ iha ihb s acc => tick (iha s (ihb s acc)))
    (fun _ _ iha ihb s acc => tick (iha s (ihb (!s) acc)))
    (fun _ _ iha ihb s acc => sgn s (mul (sum (iha false [])) (sum (ihb false []))) :: acc)
    (fun _ k ih s acc => sgn s (pow (sum (ih false [])) k) :: acc)
    e

/-- The normal form of a ring expression. -/
def toSPoly (e : Expr) : SPoly := sum (toTerms e false [])

/-- `varsLtK n e k`: every variable index of `e` is below `n`, and `k` (continuation form). -/
def varsLtK (n : ℕ) (e : Expr) : Bool → Bool :=
  @Expr.rec (fun _ => Bool → Bool) (fun _ k => k) (fun _ k => k) (fun _ k => k)
    (fun i k => Bool.rec false (tick k) (Nat.blt i n)) (fun _ ih k => tick (ih k))
    (fun _ _ iha ihb k => tick (iha (ihb k))) (fun _ _ iha ihb k => tick (iha (ihb k)))
    (fun _ _ iha ihb k => tick (iha (ihb k))) (fun _ _ ih k => tick (ih k)) e

/-- Every variable index is below `n`. -/
def varsLt (n : ℕ) (e : Expr) : Bool := varsLtK n e true

/-- The check: `n` at most the number of codes (`46`), all variable indices below `n`, and the
normal form of `a − b` is empty. -/
def check (n : ℕ) (a b : Expr) : Bool :=
  Nat.ble n primes.length && varsLt n a && varsLt n b && (toSPoly (.sub a b)).isEmpty

end

/-! ## Soundness -/

section Soundness

variable {α : Type*} [CommRing α]

/-- The value of a monomial code: `∏_{i < n} xᵢ^{v_{pᵢ}(m)}`. -/
noncomputable def mval (ctx : Context α) (n m : ℕ) : α :=
  ∏ i ∈ Finset.range n, ctx.get i ^ padicValNat (code i) m

/-- The value of a sparse polynomial. -/
noncomputable def eval (ctx : Context α) (n : ℕ) (p : SPoly) : α :=
  (p.map fun t => (t.2 : α) * mval ctx n t.1).sum

@[tmio T, powerlib_foundation] private theorem primes_prime : ∀ p ∈ primes, p.Prime := by
  simp only [primes, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

@[tmio T, powerlib_foundation] private theorem primes_nodup : primes.Nodup := by decide

@[tmio T, powerlib_foundation] private theorem code_prime {i : ℕ} (hi : i < primes.length) :
    (code i).Prime := by
  rw [code, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact primes_prime _ (List.getElem_mem hi)

@[tmio T, powerlib_foundation] private theorem code_ne_zero (i : ℕ) : code i ≠ 0 := by
  rw [code]
  by_cases hi : i < primes.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact (primes_prime _ (List.getElem_mem hi)).ne_zero
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi), Option.getD_none]
    exact one_ne_zero

@[tmio T, powerlib_foundation] private theorem code_inj {i j : ℕ} (hi : i < primes.length)
    (hj : j < primes.length) (h : code i = code j) : i = j := by
  rw [code, code, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h
  exact (List.Nodup.getElem_inj_iff primes_nodup).mp h

@[tmio T, powerlib_foundation] theorem mval_one (ctx : Context α) (n : ℕ) : mval ctx n 1 = 1 := by
  simp [mval]

@[tmio T, powerlib_foundation] theorem mval_mul (ctx : Context α) {n a b : ℕ}
    (hn : n ≤ primes.length) (ha : a ≠ 0) (hb : b ≠ 0) :
    mval ctx n (a * b) = mval ctx n a * mval ctx n b := by
  rw [mval, mval, mval, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have : Fact (code i).Prime := ⟨code_prime (lt_of_lt_of_le (Finset.mem_range.mp hi) hn)⟩
  rw [padicValNat.mul ha hb, pow_add]

@[tmio T, powerlib_foundation] theorem mval_code (ctx : Context α) {n i : ℕ}
    (hn : n ≤ primes.length) (hi : i < n) : mval ctx n (code i) = ctx.get i := by
  rw [mval, Finset.prod_eq_single i]
  · have : Fact (code i).Prime := ⟨code_prime (lt_of_lt_of_le hi hn)⟩
    rw [padicValNat_self, pow_one]
  · intro j hj hji
    have hj' := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    have : Fact (code i).Prime := ⟨code_prime (lt_of_lt_of_le hi hn)⟩
    have : Fact (code j).Prime := ⟨code_prime hj'⟩
    rw [padicValNat_primes (fun h => hji (code_inj hj' (lt_of_lt_of_le hi hn) h)), pow_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hi) h

@[tmio T, powerlib_foundation] theorem eval_nil (ctx : Context α) (n : ℕ) : eval ctx n [] = 0 :=
  rfl

@[tmio T, powerlib_foundation] theorem eval_cons (ctx : Context α) (n m : ℕ) (c : ℤ)
    (p : SPoly) : eval ctx n ((m, c) :: p) = c * mval ctx n m + eval ctx n p := by
  simp [eval]

/-- Every monomial code of the polynomial is nonzero. -/
def Pos (p : SPoly) : Prop := ∀ t ∈ p, t.1 ≠ 0

@[tmio T, powerlib_foundation] private theorem pos_nil : Pos [] := fun _ h => by simp at h

@[tmio T, powerlib_foundation] private theorem pos_cons {m : ℕ} {c : ℤ} {p : SPoly}
    (hm : m ≠ 0) (hp : Pos p) : Pos ((m, c) :: p) := fun t ht => by
  rcases List.mem_cons.mp ht with rfl | ht
  exacts [hm, hp t ht]

@[tmio T, powerlib_foundation] private theorem pos_tail {a : ℕ × ℤ} {p : SPoly}
    (h : Pos (a :: p)) : Pos p := fun t ht => h t (List.mem_cons_of_mem _ ht)

@[tmio T, powerlib_foundation] private theorem merge_cons_cons (a b : ℕ × ℤ) (p q : SPoly) :
    merge (a :: p) (b :: q) =
      Bool.rec (Bool.rec (b :: merge (a :: p) q) (a :: merge p (b :: q)) (Nat.blt a.1 b.1))
        (Bool.rec ((a.1, Int.add a.2 b.2) :: merge p q) (merge p q)
          (Int.beq' (Int.add a.2 b.2) 0)) (Nat.beq a.1 b.1) := rfl

@[tmio T, powerlib_foundation] theorem eval_merge (ctx : Context α) (n : ℕ) (p q : SPoly) :
    eval ctx n (merge p q) = eval ctx n p + eval ctx n q := by
  induction p generalizing q with
  | nil => exact (zero_add _).symm
  | cons a p ihp =>
    obtain ⟨m, c⟩ := a
    induction q with
    | nil => exact (add_zero _).symm
    | cons b q ihq =>
      obtain ⟨k, d⟩ := b
      rw [merge_cons_cons]
      cases hmk : Nat.beq m k
      · cases Nat.blt m k
        · simp only [eval_cons, ihq]; ring
        · simp only [eval_cons, ihp]; ring
      · have hmk' : m = k := Nat.eq_of_beq_eq_true hmk
        subst hmk'
        cases hs : Int.beq' (Int.add c d) 0
        · simp only [eval_cons, ihp, Int.add_def]; push_cast; ring
        · have h0 : c + d = 0 := by rw [← Int.add_def]; exact (Int.beq'_eq _ _).mp hs
          have : (c : α) + d = 0 := by exact_mod_cast congrArg (Int.cast (R := α)) h0
          simp only [eval_cons, ihp]
          linear_combination (-mval ctx n m) * this

@[tmio T, powerlib_foundation] theorem pos_merge {p q : SPoly} (hp : Pos p) (hq : Pos q) :
    Pos (merge p q) := by
  induction p generalizing q with
  | nil => exact hq
  | cons a p ihp =>
    obtain ⟨m, c⟩ := a
    induction q with
    | nil => exact hp
    | cons b q ihq =>
      obtain ⟨k, d⟩ := b
      have hm : m ≠ 0 := hp _ List.mem_cons_self
      have hk : k ≠ 0 := hq _ List.mem_cons_self
      rw [merge_cons_cons]
      cases Nat.beq m k
      · cases Nat.blt m k
        · exact pos_cons hk (ihq (pos_tail hq))
        · exact pos_cons hm (ihp (pos_tail hp) hq)
      · cases Int.beq' (Int.add c d) 0
        · exact pos_cons hm (ihp (pos_tail hp) (pos_tail hq))
        · exact ihp (pos_tail hp) (pos_tail hq)

@[tmio T, powerlib_foundation] theorem eval_scale (ctx : Context α) {n m : ℕ} (c : ℤ)
    {q : SPoly} (hn : n ≤ primes.length) (hm : m ≠ 0) (hq : Pos q) :
    eval ctx n (scale m c q) = c * mval ctx n m * eval ctx n q := by
  induction q with
  | nil => exact (mul_zero _).symm
  | cons t q ih =>
    obtain ⟨k, d⟩ := t
    have hk : k ≠ 0 := hq _ List.mem_cons_self
    show eval ctx n ((Nat.mul m k, Int.mul c d) :: scale m c q) = _
    rw [eval_cons, eval_cons, ih (pos_tail hq), Nat.mul_eq, Int.mul_def, mval_mul ctx hn hm hk]
    push_cast; ring

@[tmio T, powerlib_foundation] theorem pos_scale {m : ℕ} (c : ℤ) {q : SPoly} (hm : m ≠ 0)
    (hq : Pos q) : Pos (scale m c q) := by
  induction q with
  | nil => exact pos_nil
  | cons t q ih =>
    obtain ⟨k, d⟩ := t
    exact pos_cons (mul_ne_zero hm (hq _ List.mem_cons_self)) (ih (pos_tail hq))

/-- The value of a list of sparse polynomials: the sum of their values. -/
noncomputable def evalSum (ctx : Context α) (n : ℕ) (l : List SPoly) : α :=
  (l.map (eval ctx n)).sum

/-- Every polynomial of the list has nonzero codes. -/
def AllPos (l : List SPoly) : Prop := ∀ p ∈ l, Pos p

@[tmio T, powerlib_foundation] private theorem evalSum_cons (ctx : Context α) (n : ℕ)
    (p : SPoly) (l : List SPoly) : evalSum ctx n (p :: l) = eval ctx n p + evalSum ctx n l := by
  simp [evalSum]

@[tmio T, powerlib_foundation] private theorem allPos_cons {p : SPoly} {l : List SPoly}
    (hp : Pos p) (hl : AllPos l) : AllPos (p :: l) := fun r hr => by
  rcases List.mem_cons.mp hr with rfl | hr
  exacts [hp, hl r hr]

@[tmio T, powerlib_foundation] private theorem allPos_tail {p : SPoly} {l : List SPoly}
    (h : AllPos (p :: l)) : AllPos l := fun r hr => h r (List.mem_cons_of_mem _ hr)

@[tmio T, powerlib_foundation] private theorem evalSum_pairs (ctx : Context α) (n : ℕ)
    (l : List SPoly) (o : Option SPoly) :
    evalSum ctx n (pairs l o) = o.elim 0 (eval ctx n) + evalSum ctx n l := by
  induction l generalizing o with
  | nil => cases o <;> simp [pairs, evalSum]
  | cons q l ih =>
    cases o with
    | none => show evalSum ctx n (pairs l (some q)) = _; rw [ih, evalSum_cons]; simp
    | some p =>
      show evalSum ctx n (merge p q :: pairs l none) = _
      rw [evalSum_cons, ih, eval_merge, evalSum_cons]; simp; ring

@[tmio T, powerlib_foundation] private theorem allPos_pairs {l : List SPoly} {o : Option SPoly}
    (hl : AllPos l) (ho : ∀ p, o = some p → Pos p) : AllPos (pairs l o) := by
  induction l generalizing o with
  | nil =>
    cases o with
    | none => exact fun _ h => by simp [pairs] at h
    | some p => exact allPos_cons (ho p rfl) (fun _ h => by simp at h)
  | cons q l ih =>
    cases o with
    | none => exact ih (allPos_tail hl) (fun p h => by cases h; exact hl q (by simp))
    | some p =>
      exact allPos_cons (pos_merge (ho p rfl) (hl q (by simp)))
        (ih (allPos_tail hl) (fun _ h => by cases h))

@[tmio T, powerlib_foundation] private theorem eval_foldr (ctx : Context α) (n : ℕ)
    (l : List SPoly) : eval ctx n (l.foldr merge []) = evalSum ctx n l := by
  induction l with
  | nil => rfl
  | cons r l ih => rw [List.foldr_cons, eval_merge, ih, evalSum_cons]

@[tmio T, powerlib_foundation] private theorem pos_foldr {l : List SPoly} (h : AllPos l) :
    Pos (l.foldr merge []) := by
  induction l with
  | nil => exact pos_nil
  | cons r l ih => exact pos_merge (h r (by simp)) (ih (allPos_tail h))

@[tmio T, powerlib_foundation] theorem eval_sumRounds (ctx : Context α) (n k : ℕ)
    (l : List SPoly) : eval ctx n (sumRounds k l) = evalSum ctx n l := by
  induction k generalizing l with
  | zero => exact eval_foldr ctx n l
  | succ k ih =>
    match l with
    | [] => rfl
    | [p] => simp [sumRounds, evalSum]
    | p :: q :: l =>
      show eval ctx n (sumRounds k (pairs (p :: q :: l) none)) = _
      rw [ih, evalSum_pairs]; simp

@[tmio T, powerlib_foundation] theorem pos_sumRounds {k : ℕ} {l : List SPoly} (h : AllPos l) :
    Pos (sumRounds k l) := by
  induction k generalizing l with
  | zero => exact pos_foldr h
  | succ k ih =>
    match l with
    | [] => exact pos_nil
    | [p] => exact h p (by simp)
    | p :: q :: l =>
      show Pos (sumRounds k (pairs (p :: q :: l) none))
      exact ih (allPos_pairs h (fun _ h => by cases h))

@[tmio T, powerlib_foundation] theorem eval_sum (ctx : Context α) (n : ℕ) (l : List SPoly) :
    eval ctx n (sum l) = evalSum ctx n l :=
  eval_sumRounds ctx n _ l

@[tmio T, powerlib_foundation] theorem pos_sum {l : List SPoly} (h : AllPos l) : Pos (sum l) :=
  pos_sumRounds h

@[tmio T, powerlib_foundation] private theorem evalSum_scaled (ctx : Context α) {n : ℕ}
    (hn : n ≤ primes.length) {p q : SPoly} (hp : Pos p) (hq : Pos q) :
    evalSum ctx n (scaled q p) = eval ctx n p * eval ctx n q := by
  induction p with
  | nil => exact (zero_mul _).symm
  | cons t p ih =>
    obtain ⟨m, c⟩ := t
    show evalSum ctx n (scale m c q :: scaled q p) = _
    rw [evalSum_cons, ih (pos_tail hp), eval_scale ctx c hn (hp _ List.mem_cons_self) hq,
      eval_cons]
    ring

@[tmio T, powerlib_foundation] private theorem allPos_scaled {p q : SPoly} (hp : Pos p)
    (hq : Pos q) : AllPos (scaled q p) := by
  induction p with
  | nil => exact fun _ h => by simp [scaled] at h
  | cons t p ih =>
    obtain ⟨m, c⟩ := t
    exact allPos_cons (pos_scale c (hp _ List.mem_cons_self) hq) (ih (pos_tail hp))

@[tmio T, powerlib_foundation] theorem eval_mul (ctx : Context α) {n : ℕ}
    (hn : n ≤ primes.length) {p q : SPoly} (hp : Pos p) (hq : Pos q) :
    eval ctx n (mul p q) = eval ctx n p * eval ctx n q := by
  unfold mul
  cases shorter q p
  · show eval ctx n (sum (scaled q p)) = _
    rw [eval_sum, evalSum_scaled ctx hn hp hq]
  · show eval ctx n (sum (scaled p q)) = _
    rw [eval_sum, evalSum_scaled ctx hn hq hp, mul_comm]

@[tmio T, powerlib_foundation] theorem pos_mul {p q : SPoly} (hp : Pos p) (hq : Pos q) :
    Pos (mul p q) := by
  unfold mul
  cases shorter q p
  exacts [pos_sum (allPos_scaled hp hq), pos_sum (allPos_scaled hq hp)]

@[tmio T, powerlib_foundation] theorem pos_pow {p : SPoly} (hp : Pos p) (k : ℕ) :
    Pos (pow p k) := by
  induction k with
  | zero => exact pos_cons one_ne_zero pos_nil
  | succ k ih => exact pos_mul ih hp

@[tmio T, powerlib_foundation] theorem eval_pow (ctx : Context α) {n : ℕ}
    (hn : n ≤ primes.length) {p : SPoly} (hp : Pos p) (k : ℕ) :
    eval ctx n (pow p k) = eval ctx n p ^ k := by
  induction k with
  | zero => show eval ctx n [(1, 1)] = _; simp [eval_cons, eval_nil, mval_one]
  | succ k ih =>
    show eval ctx n (mul (pow p k) p) = _
    rw [eval_mul ctx hn (pos_pow hp k) hp, ih, pow_succ]

@[tmio T, powerlib_foundation] theorem eval_const (ctx : Context α) (n : ℕ) (k : ℤ) :
    eval ctx n (const k) = k := by
  unfold const
  cases h : Int.beq' k 0
  · show eval ctx n [(1, k)] = _; simp [eval_cons, eval_nil, mval_one]
  · show eval ctx n [] = _; rw [(Int.beq'_eq _ _).mp h]; simp [eval_nil]

@[tmio T, powerlib_foundation] theorem pos_const (k : ℤ) : Pos (const k) := by
  unfold const
  cases Int.beq' k 0
  exacts [pos_cons one_ne_zero pos_nil, pos_nil]

@[tmio T, powerlib_foundation] theorem eval_sgn (ctx : Context α) {n : ℕ}
    (hn : n ≤ primes.length) (s : Bool) {p : SPoly} (hp : Pos p) :
    eval ctx n (sgn s p) = (if s then -1 else 1) * eval ctx n p := by
  cases s
  · show eval ctx n p = _; simp
  · show eval ctx n (scale 1 (-1) p) = _
    rw [eval_scale ctx _ hn one_ne_zero hp, mval_one]; simp

@[tmio T, powerlib_foundation] theorem pos_sgn (s : Bool) {p : SPoly} (hp : Pos p) :
    Pos (sgn s p) := by
  cases s
  exacts [hp, pos_scale _ one_ne_zero hp]

@[tmio T, powerlib_foundation] private theorem denote_neg (ctx : Context α) (a : Expr) :
    (Expr.neg a).denote ctx = -a.denote ctx := rfl

@[tmio T, powerlib_foundation] private theorem denote_add (ctx : Context α) (a b : Expr) :
    (Expr.add a b).denote ctx = a.denote ctx + b.denote ctx := rfl

@[tmio T, powerlib_foundation] private theorem denote_sub (ctx : Context α) (a b : Expr) :
    (Expr.sub a b).denote ctx = a.denote ctx - b.denote ctx := rfl

@[tmio T, powerlib_foundation] private theorem denote_mul (ctx : Context α) (a b : Expr) :
    (Expr.mul a b).denote ctx = a.denote ctx * b.denote ctx := rfl

@[tmio T, powerlib_foundation] private theorem denote_pow (ctx : Context α) (a : Expr) (k : ℕ) :
    (Expr.pow a k).denote ctx = a.denote ctx ^ k := rfl

@[tmio T, powerlib_foundation] private theorem denote_var (ctx : Context α) (i : ℕ) :
    (Expr.var i).denote ctx = ctx.get i := rfl

@[tmio T, powerlib_foundation] private theorem varsLtK_eq (n : ℕ) (e : Expr) (k : Bool) :
    varsLtK n e k = (varsLt n e && k) := by
  unfold varsLt
  induction e generalizing k with
  | var i =>
    show Bool.rec false (tick k) (Nat.blt i n) = (Bool.rec false (tick true) (Nat.blt i n) && k)
    cases Nat.blt i n <;> rfl
  | neg a ih => exact ih k
  | pow a _ ih => exact ih k
  | add a b iha ihb =>
    show varsLtK n a (varsLtK n b k) = (varsLtK n a (varsLtK n b true) && k)
    rw [iha, ihb, iha (varsLtK n b true), ihb, Bool.and_true, Bool.and_assoc]
  | sub a b iha ihb =>
    show varsLtK n a (varsLtK n b k) = (varsLtK n a (varsLtK n b true) && k)
    rw [iha, ihb, iha (varsLtK n b true), ihb, Bool.and_true, Bool.and_assoc]
  | mul a b iha ihb =>
    show varsLtK n a (varsLtK n b k) = (varsLtK n a (varsLtK n b true) && k)
    rw [iha, ihb, iha (varsLtK n b true), ihb, Bool.and_true, Bool.and_assoc]
  | num _ => exact (Bool.true_and k).symm
  | natCast _ => exact (Bool.true_and k).symm
  | intCast _ => exact (Bool.true_and k).symm

@[tmio T, powerlib_foundation] private theorem varsLt_bin {n : ℕ} {a b : Expr}
    {f : Expr → Expr → Expr} (hf : ∀ k, varsLtK n (f a b) k = varsLtK n a (varsLtK n b k))
    (h : varsLt n (f a b) = true) : varsLt n a = true ∧ varsLt n b = true := by
  rw [varsLt, hf, varsLtK_eq] at h
  exact Bool.and_eq_true _ _ ▸ h

@[tmio T, powerlib_foundation] theorem allPos_toTerms (e : Expr) (s : Bool) {acc : List SPoly}
    (hacc : AllPos acc) : AllPos (toTerms e s acc) := by
  have nil : AllPos [] := fun _ h => by simp at h
  induction e generalizing s acc with
  | add a b iha ihb => exact iha _ (ihb _ hacc)
  | sub a b iha ihb => exact iha _ (ihb _ hacc)
  | neg a ih => exact ih _ hacc
  | mul a b iha ihb =>
    exact allPos_cons (pos_sgn s (pos_mul (pos_sum (iha false nil)) (pos_sum (ihb false nil))))
      hacc
  | pow a k ih => exact allPos_cons (pos_sgn s (pos_pow (pos_sum (ih false nil)) k)) hacc
  | var i => exact allPos_cons (pos_sgn s (pos_cons (code_ne_zero i) pos_nil)) hacc
  | num k => exact allPos_cons (pos_sgn s (pos_const k)) hacc
  | natCast k => exact allPos_cons (pos_sgn s (pos_const k)) hacc
  | intCast k => exact allPos_cons (pos_sgn s (pos_const k)) hacc

@[tmio T, powerlib_foundation] theorem evalSum_toTerms (ctx : Context α) {n : ℕ}
    (hn : n ≤ primes.length) (e : Expr) (s : Bool) (acc : List SPoly) (hacc : AllPos acc)
    (he : varsLt n e = true) :
    evalSum ctx n (toTerms e s acc) =
      (if s then -1 else 1) * e.denote ctx + evalSum ctx n acc := by
  have nil : AllPos [] := fun _ h => by simp at h
  have e0 : evalSum ctx n ([] : List SPoly) = 0 := rfl
  induction e generalizing s acc with
  | add a b iha ihb =>
    have he' := varsLt_bin (f := Expr.add) (fun _ => rfl) he
    show evalSum ctx n (toTerms a s (toTerms b s acc)) = _
    rw [iha s _ (allPos_toTerms b s hacc) he'.1, ihb s acc hacc he'.2, denote_add]
    ring
  | sub a b iha ihb =>
    have he' := varsLt_bin (f := Expr.sub) (fun _ => rfl) he
    show evalSum ctx n (toTerms a s (toTerms b (!s) acc)) = _
    rw [iha s _ (allPos_toTerms _ _ hacc) he'.1, ihb _ acc hacc he'.2, denote_sub]
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> ring
  | neg a ih =>
    show evalSum ctx n (toTerms a (!s) acc) = _
    rw [ih _ acc hacc he, denote_neg]
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> ring
  | mul a b iha ihb =>
    have he' := varsLt_bin (f := Expr.mul) (fun _ => rfl) he
    have ha := allPos_toTerms a false nil
    have hb := allPos_toTerms b false nil
    show evalSum ctx n
      (sgn s (mul (sum (toTerms a false [])) (sum (toTerms b false []))) :: acc) = _
    rw [evalSum_cons, eval_sgn ctx hn s (pos_mul (pos_sum ha) (pos_sum hb)),
      eval_mul ctx hn (pos_sum ha) (pos_sum hb), eval_sum, eval_sum, iha false [] nil he'.1,
      ihb false [] nil he'.2, denote_mul, e0]
    simp
  | pow a k ih =>
    have ha := allPos_toTerms a false nil
    show evalSum ctx n (sgn s (pow (sum (toTerms a false [])) k) :: acc) = _
    rw [evalSum_cons, eval_sgn ctx hn s (pos_pow (pos_sum ha) k),
      eval_pow ctx hn (pos_sum ha), eval_sum, ih false [] nil he, denote_pow, e0]
    simp
  | var i =>
    have hi : i < n := by
      have he' : Bool.rec false (tick true) (Nat.blt i n) = true := he
      cases h : Nat.blt i n
      · rw [h] at he'; exact absurd he' Bool.false_ne_true
      · exact Nat.blt_eq.mp h
    show evalSum ctx n (sgn s [(code i, 1)] :: acc) = _
    rw [evalSum_cons, eval_sgn ctx hn s (pos_cons (code_ne_zero i) pos_nil), eval_cons, eval_nil,
      mval_code ctx hn hi, denote_var]
    simp
  | num k =>
    show evalSum ctx n (sgn s (const k) :: acc) = _
    rw [evalSum_cons, eval_sgn ctx hn s (pos_const k), eval_const,
      show (Expr.num k).denote ctx = (k : α) from Lean.Grind.CommRing.denoteInt_eq k]
  | natCast k =>
    show evalSum ctx n (sgn s (const k) :: acc) = _
    rw [evalSum_cons, eval_sgn ctx hn s (pos_const k), eval_const,
      show (Expr.natCast k).denote ctx = (k : α) from rfl, Int.cast_natCast]
  | intCast k =>
    show evalSum ctx n (sgn s (const k) :: acc) = _
    rw [evalSum_cons, eval_sgn ctx hn s (pos_const k), eval_const]
    rfl

@[tmio T, powerlib_foundation] theorem eval_toSPoly (ctx : Context α) {n : ℕ}
    (hn : n ≤ primes.length) (e : Expr) (he : varsLt n e = true) :
    eval ctx n (toSPoly e) = e.denote ctx := by
  rw [toSPoly, eval_sum, evalSum_toTerms ctx hn e false [] (fun _ h => by simp at h) he]
  simp [evalSum]

/-- **Soundness of the check**: a passed check proves the identity in every commutative ring. -/
@[tmio T, powerlib_foundation] theorem eq_of_check (ctx : Context α) (n : ℕ) (a b : Expr)
    (h : check n a b = true) : a.denote ctx = b.denote ctx := by
  simp only [check, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hn, ha⟩, hb⟩, h0⟩ := h
  have hn' : n ≤ primes.length := Nat.ble_eq.mp hn
  have hab : varsLt n (.sub a b) = true := by
    show varsLtK n a (varsLtK n b true) = true
    rw [varsLtK_eq, show varsLtK n b true = varsLt n b from rfl, ha, hb]; rfl
  have h1 := eval_toSPoly ctx hn' (.sub a b) hab
  rw [h0, eval_nil, denote_sub] at h1
  exact (sub_eq_zero.mp h1.symm)

end Soundness

/-! ## The tactic -/

section Tactic
open Lean Meta Elab Tactic

/-- Reification of a ring expression into `Lean.Grind.CommRing.Expr` over the atoms `as`. -/
partial def reify (α : Lean.Expr) (e : Lean.Expr) :
    StateT (Array Lean.Expr) MetaM Lean.Grind.CommRing.Expr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[t, _, _, _, a, b]) => if t == α then bin .add a b else atom e
  | (``HSub.hSub, #[t, _, _, _, a, b]) => if t == α then bin .sub a b else atom e
  | (``HMul.hMul, #[t, _, _, _, a, b]) => if t == α then bin .mul a b else atom e
  | (``Neg.neg, #[t, _, a]) => if t == α then return .neg (← reify α a) else atom e
  | (``HPow.hPow, #[t, _, _, _, a, n]) =>
    match (← instantiateMVars n).nat? with
    | some k => if t == α then return .pow (← reify α a) k else atom e
    | none => atom e
  | (``OfNat.ofNat, #[t, n, _]) =>
    match n.rawNatLit? with
    | some k => if t == α then return .num k else atom e
    | none => atom e
  | _ => atom e
where
  bin (f : Lean.Grind.CommRing.Expr → Lean.Grind.CommRing.Expr → Lean.Grind.CommRing.Expr)
      (a b : Lean.Expr) : StateT (Array Lean.Expr) MetaM Lean.Grind.CommRing.Expr := do
    return f (← reify α a) (← reify α b)
  atom (e : Lean.Expr) : StateT (Array Lean.Expr) MetaM Lean.Grind.CommRing.Expr := do
    let as ← get
    match as.findIdx? (· == e) with
    | some i => return .var i
    | none => set (as.push e); return .var as.size

/-- `poly_rfl` closes a goal `lhs = rhs` in a commutative ring that is a polynomial identity
with integer coefficients in its atoms: the two sides are reified, and the normal form of
`lhs − rhs` is computed and found empty by the kernel (`decide +kernel` on `check`); soundness
is `eq_of_check`. -/
elab "poly_rfl" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← whnfR (← g.getType))
  let some (α, lhs, rhs) := t.eq? | throwError "poly_rfl: the goal is not an equality"
  let ((a, b), atoms) ← (do return (← reify α lhs, ← reify α rhs)).run #[]
  let u ← getDecLevel α
  let inst ← synthInstance (mkApp (mkConst ``CommRing [u]) α)
  let ctx ← if h : 0 < atoms.size then RArray.toExpr α id (RArray.ofArray atoms h)
    else pure (mkApp2 (mkConst ``Lean.RArray.leaf [u]) α lhs)
  let aE := Lean.Meta.Sym.Arith.ofRingExpr a
  let bE := Lean.Meta.Sym.Arith.ofRingExpr b
  let n := mkRawNatLit atoms.size
  let hty ← mkEq (mkApp3 (mkConst ``check) n aE bE) (mkConst ``Bool.true)
  let hmv ← mkFreshExprMVar hty
  g.assign (mkAppN (mkConst ``eq_of_check [u]) #[α, inst, ctx, n, aE, bE, hmv])
  replaceMainGoal [hmv.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

end Tactic

end powerlib.Dynamics.PolyIdentity
