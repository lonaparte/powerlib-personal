import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import theorem.Attributes

/-! # Kernel-checked identities of rational functions in one real variable (foundation)

A polynomial expression in one real variable `s` and in atoms that are rational functions
`n(s)/∏ⱼ Bⱼ(s)^{eⱼ}` of `s` (integer numerators `n`, a fixed list of nonvanishing integer base
polynomials `Bⱼ`) vanishes identically when the numerator of its exact common-denominator form is
the zero polynomial. That numerator is computed by an executable function on integer coefficient
lists, so the identity is decided by the kernel (`decide +kernel`) instead of `ring`, whose
normalisation does not reach the degrees (`≈ 100`) of centre-manifold and Lyapunov-coefficient
computations.

Scope.
* Generic: integer polynomials as coefficient lists (constant term first), read in `ℝ` by
  Horner's rule (`zeval`); denominators are products of powers of the bases (`bval`), exponent
  vectors are lists (missing entries are `0`). Every statement holds at every `s` where all bases
  are nonzero. No model, no limit, no inequality: exact identities only.

Source: exact rational-function arithmetic (clearing denominators by a common power product of
the bases); the reflection pattern of `theorem/Linear/VerifiedSynthesis.lean` (an executable
check whose soundness is proved once).

Results.
* Integer polynomials: `zeval`, `zadd`, `zscale`, `zmul`, `zpow`, `zIsZero` and their soundness
  `zeval_zadd`, `zeval_zscale`, `zeval_zmul`, `zeval_zpow`, `zeval_of_zIsZero`.
* Denominators: `eadd`, `emax`, `esub`, `escale`, `bden`, `bval`; `bval_nil_right`, `zeval_bden`,
  `bval_eadd`, `bval_escale`, `bval_esub_self`, `bval_emax_left`, `emax_comm`, `bval_ne_zero`,
  `bval_pos`.
* Expressions: `PExpr` (the variable, integers, atoms `n/∏ Bʲ^{eⱼ}`, sums, products, negation,
  powers), its value `PExpr.val`, its common-denominator form `PExpr.clear`; `PExpr.val_eq`
  (the value is the cleared numerator over the cleared denominator) and **`PExpr.val_eq_zero`**
  (a zero cleared numerator gives a vanishing value).
-/

namespace powerlib.Dynamics.PolyCertificate

/-! ## Integer polynomials -/

/-- `Σ pₖ sᵏ` by Horner's rule (coefficients from the constant term up). -/
noncomputable def zeval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, s => a + s * zeval p s

/-- Sum of coefficient lists. -/
def zadd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: zadd p q

/-- Integer multiple of a coefficient list. -/
def zscale (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => (c * a) :: zscale c p

/-- Product of coefficient lists. -/
def zmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => zadd (zscale a q) (0 :: zmul p q)

/-- Power of a coefficient list. -/
def zpow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | k + 1 => zmul p (zpow p k)

/-- All coefficients vanish. -/
def zIsZero (p : List ℤ) : Bool := p.all (· == 0)

@[tmio T, powerlib_foundation] theorem zeval_zadd :
    ∀ (p q : List ℤ) (s : ℝ), zeval (zadd p q) s = zeval p s + zeval q s
  | [], q, s => by simp [zadd, zeval]
  | a :: p, [], s => by simp [zadd, zeval]
  | a :: p, b :: q, s => by simp only [zadd, zeval, zeval_zadd p q s]; push_cast; ring

@[tmio T, powerlib_foundation] theorem zeval_zscale (c : ℤ) :
    ∀ (p : List ℤ) (s : ℝ), zeval (zscale c p) s = c * zeval p s
  | [], s => by simp [zscale, zeval]
  | a :: p, s => by simp only [zscale, zeval, zeval_zscale c p s]; push_cast; ring

@[tmio T, powerlib_foundation] theorem zeval_zmul :
    ∀ (p q : List ℤ) (s : ℝ), zeval (zmul p q) s = zeval p s * zeval q s
  | [], q, s => by simp [zmul, zeval]
  | a :: p, q, s => by
    simp only [zmul, zeval_zadd, zeval_zscale, zeval, zeval_zmul p q s]; push_cast; ring

@[tmio T, powerlib_foundation] theorem zeval_zpow (p : List ℤ) (s : ℝ) :
    ∀ k, zeval (zpow p k) s = zeval p s ^ k
  | 0 => by simp [zpow, zeval]
  | k + 1 => by rw [zpow, zeval_zmul, zeval_zpow p s k, pow_succ']

@[tmio T, powerlib_foundation] theorem zeval_of_zIsZero :
    ∀ {p : List ℤ}, zIsZero p = true → ∀ s : ℝ, zeval p s = 0
  | [], _, s => by simp [zeval]
  | a :: p, h, s => by
    simp only [zIsZero, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [zeval, h.1, zeval_of_zIsZero h.2 s]; simp

/-! ## Denominators: products of powers of the bases -/

/-- Sum of exponent vectors. -/
def eadd : List ℕ → List ℕ → List ℕ
  | [], e => e
  | a :: e, [] => a :: e
  | a :: e, b :: f => (a + b) :: eadd e f

/-- Pointwise maximum of exponent vectors. -/
def emax : List ℕ → List ℕ → List ℕ
  | [], e => e
  | a :: e, [] => a :: e
  | a :: e, b :: f => max a b :: emax e f

/-- Pointwise truncated difference of exponent vectors. -/
def esub : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: e, [] => a :: e
  | a :: e, b :: f => (a - b) :: esub e f

/-- Multiple of an exponent vector. -/
def escale (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: e => (k * a) :: escale k e

/-- The coefficient list of `∏ⱼ Bⱼ^{eⱼ}`. -/
def bden : List (List ℤ) → List ℕ → List ℤ
  | b :: bs, k :: e => zmul (zpow b k) (bden bs e)
  | _, _ => [1]

/-- The value `∏ⱼ Bⱼ(s)^{eⱼ}`. -/
noncomputable def bval : List (List ℤ) → List ℕ → ℝ → ℝ
  | b :: bs, k :: e, s => zeval b s ^ k * bval bs e s
  | _, _, _ => 1

@[tmio T, powerlib_foundation] theorem bval_nil_right (bs : List (List ℤ)) (s : ℝ) :
    bval bs [] s = 1 := by
  cases bs <;> rfl

@[tmio T, powerlib_foundation] theorem zeval_bden :
    ∀ (bs : List (List ℤ)) (e : List ℕ) (s : ℝ), zeval (bden bs e) s = bval bs e s
  | [], e, s => by cases e <;> simp [bden, bval, zeval]
  | b :: bs, [], s => by simp [bden, bval, zeval]
  | b :: bs, k :: e, s => by rw [bden, bval, zeval_zmul, zeval_zpow, zeval_bden bs e s]

@[tmio T, powerlib_foundation] theorem bval_eadd :
    ∀ (bs : List (List ℤ)) (e f : List ℕ) (s : ℝ),
      bval bs (eadd e f) s = bval bs e s * bval bs f s
  | [], e, f, s => by cases e <;> cases f <;> simp [bval]
  | b :: bs, [], f, s => by cases f <;> simp [eadd, bval]
  | b :: bs, a :: e, [], s => by simp [eadd, bval]
  | b :: bs, a :: e, c :: f, s => by
    simp only [eadd, bval, bval_eadd bs e f s, pow_add]; ring

@[tmio T, powerlib_foundation] theorem bval_escale (k : ℕ) :
    ∀ (bs : List (List ℤ)) (e : List ℕ) (s : ℝ), bval bs (escale k e) s = bval bs e s ^ k
  | [], e, s => by cases e <;> simp [bval]
  | b :: bs, [], s => by simp [escale, bval]
  | b :: bs, a :: e, s => by
    simp only [escale, bval, bval_escale k bs e s, mul_pow, ← pow_mul]; ring_nf

@[tmio T, powerlib_foundation] theorem bval_esub_self :
    ∀ (bs : List (List ℤ)) (e : List ℕ) (s : ℝ), bval bs (esub e e) s = 1
  | [], e, s => by cases e <;> simp [bval]
  | b :: bs, [], s => by simp [esub, bval]
  | b :: bs, a :: e, s => by
    simp only [esub, Nat.sub_self, bval, pow_zero, one_mul, bval_esub_self bs e s]

@[tmio T, powerlib_foundation] theorem bval_emax_left :
    ∀ (bs : List (List ℤ)) (e f : List ℕ) (s : ℝ),
      bval bs (emax e f) s = bval bs (esub (emax e f) e) s * bval bs e s
  | [], e, f, s => by cases e <;> cases f <;> simp [bval]
  | b :: bs, [], f, s => by cases f <;> simp [emax, esub, bval]
  | b :: bs, a :: e, [], s => by
    simp only [emax, esub, Nat.sub_self, bval, pow_zero, one_mul, bval_esub_self bs e s]
  | b :: bs, a :: e, c :: f, s => by
    simp only [emax, esub, bval]
    rw [bval_emax_left bs e f s]
    have : zeval b s ^ max a c = zeval b s ^ (max a c - a) * zeval b s ^ a := by
      rw [← pow_add, Nat.sub_add_cancel (le_max_left a c)]
    rw [this]; ring

@[tmio T, powerlib_foundation] theorem emax_comm : ∀ (e f : List ℕ), emax e f = emax f e
  | [], f => by cases f <;> rfl
  | a :: e, [] => rfl
  | a :: e, b :: f => by simp only [emax, emax_comm e f, max_comm]

@[tmio T, powerlib_foundation] theorem bval_ne_zero {bs : List (List ℤ)} {s : ℝ}
    (hb : ∀ b ∈ bs, zeval b s ≠ 0) : ∀ e, bval bs e s ≠ 0 := by
  induction bs with
  | nil => intro e; cases e <;> simp [bval]
  | cons b bs ih =>
    intro e
    cases e with
    | nil => simp [bval]
    | cons k e =>
      simp only [bval]
      exact mul_ne_zero (pow_ne_zero _ (hb b List.mem_cons_self))
        (ih (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) e)

@[tmio T, powerlib_foundation] theorem bval_pos {bs : List (List ℤ)} {s : ℝ}
    (hb : ∀ b ∈ bs, 0 < zeval b s) : ∀ e, 0 < bval bs e s := by
  induction bs with
  | nil => intro e; cases e <;> simp [bval]
  | cons b bs ih =>
    intro e
    cases e with
    | nil => simp [bval]
    | cons k e =>
      simp only [bval]
      exact mul_pos (pow_pos (hb b List.mem_cons_self) _)
        (ih (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) e)

/-! ## Expressions and their common-denominator form -/

/-- Polynomial expressions in the variable `s` and in rational atoms `n/∏ⱼ Bⱼ^{eⱼ}`. -/
inductive PExpr
  /-- The variable `s`. -/
  | var
  /-- An integer. -/
  | int (c : ℤ)
  /-- The atom `n(s)/∏ⱼ Bⱼ(s)^{eⱼ}`. -/
  | atom (n : List ℤ) (e : List ℕ)
  /-- A sum. -/
  | add (a b : PExpr)
  /-- A product. -/
  | mul (a b : PExpr)
  /-- A negation. -/
  | neg (a : PExpr)
  /-- A power. -/
  | pow (a : PExpr) (k : ℕ)

namespace PExpr

/-- The value of an expression at `s`. -/
noncomputable def val (bs : List (List ℤ)) : PExpr → ℝ → ℝ
  | var, s => s
  | int c, _ => c
  | atom n e, s => zeval n s / bval bs e s
  | add a b, s => val bs a s + val bs b s
  | mul a b, s => val bs a s * val bs b s
  | neg a, s => -val bs a s
  | pow a k, s => val bs a s ^ k

/-- The common-denominator form: a numerator coefficient list and a denominator exponent
vector. -/
def clear (bs : List (List ℤ)) : PExpr → List ℤ × List ℕ
  | var => ([0, 1], [])
  | int c => ([c], [])
  | atom n e => (n, e)
  | add a b =>
    let A := clear bs a
    let B := clear bs b
    let M := emax A.2 B.2
    (zadd (zmul A.1 (bden bs (esub M A.2))) (zmul B.1 (bden bs (esub M B.2))), M)
  | mul a b =>
    let A := clear bs a
    let B := clear bs b
    (zmul A.1 B.1, eadd A.2 B.2)
  | neg a =>
    let A := clear bs a
    (zscale (-1) A.1, A.2)
  | pow a k =>
    let A := clear bs a
    (zpow A.1 k, escale k A.2)

/-- **The value is the cleared numerator over the cleared denominator** (all bases nonzero
at `s`). -/
@[tmio T, powerlib_foundation] theorem val_eq {bs : List (List ℤ)} {s : ℝ}
    (hb : ∀ b ∈ bs, zeval b s ≠ 0) :
    ∀ E : PExpr, val bs E s = zeval (clear bs E).1 s / bval bs (clear bs E).2 s
  | var => by simp [val, clear, zeval]; cases bs <;> simp [bval]
  | int c => by simp [val, clear, zeval]; cases bs <;> simp [bval]
  | atom n e => rfl
  | add a b => by
    have ha := val_eq hb a
    have hb' := val_eq hb b
    simp only [val, clear, ha, hb', zeval_zadd, zeval_zmul, zeval_bden]
    set A := clear bs a
    set B := clear bs b
    have h1 := bval_emax_left bs A.2 B.2 s
    have h2 := bval_emax_left bs B.2 A.2 s
    rw [emax_comm B.2 A.2] at h2
    have nA := bval_ne_zero hb A.2
    have nB := bval_ne_zero hb B.2
    have n1 := bval_ne_zero hb (esub (emax A.2 B.2) A.2)
    have n2 := bval_ne_zero hb (esub (emax A.2 B.2) B.2)
    have e1 : zeval A.1 s / bval bs A.2 s =
        zeval A.1 s * bval bs (esub (emax A.2 B.2) A.2) s / bval bs (emax A.2 B.2) s := by
      rw [h1]; field_simp
    have e2 : zeval B.1 s / bval bs B.2 s =
        zeval B.1 s * bval bs (esub (emax A.2 B.2) B.2) s / bval bs (emax A.2 B.2) s := by
      rw [h2]; field_simp
    rw [e1, e2, add_div]
  | mul a b => by
    have ha := val_eq hb a
    have hb' := val_eq hb b
    simp only [val, clear, ha, hb', zeval_zmul, bval_eadd]
    have nA := bval_ne_zero hb (clear bs a).2
    have nB := bval_ne_zero hb (clear bs b).2
    field_simp
  | neg a => by
    have ha := val_eq hb a
    simp only [val, clear, ha, zeval_zscale]
    push_cast; ring
  | pow a k => by
    have ha := val_eq hb a
    simp only [val, clear, ha, zeval_zpow, bval_escale, div_pow]

/-- **A zero cleared numerator gives a vanishing value.** The hypothesis is a finite integer
computation (`decide +kernel`). -/
@[tmio T, powerlib_foundation] theorem val_eq_zero {bs : List (List ℤ)} {s : ℝ}
    (hb : ∀ b ∈ bs, zeval b s ≠ 0) (E : PExpr) (h : zIsZero (clear bs E).1 = true) :
    val bs E s = 0 := by
  rw [val_eq hb, zeval_of_zIsZero h, zero_div]

end PExpr

end powerlib.Dynamics.PolyCertificate
