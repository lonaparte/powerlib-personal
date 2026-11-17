import theorem.Attributes
import dependencies.Mathlib

/-! # Linear multistep methods: Dahlquist order conditions and the BDF methods

Order of a linear multistep method as an algebraic condition on its coefficients, and the exact
order `k` of the `k`-step BDF for every `k ≥ 1`.

Model boundary.
* A `k`-step linear multistep method `Σᵢ αᵢ x_{n+i} = h Σᵢ βᵢ f_{n+i}` with exact rational
  coefficients (`α_k = 1`). Order is the classical algebraic notion: the error constants
  `C_q = Σᵢ αᵢ iᵠ - q Σᵢ βᵢ i^{q-1}` vanish for `q ≤ p`, which is equivalent to the method being
  exact on all monomials `t^q`, `q ≤ p` (`residual_monomial`), and `C_{p+1} ≠ 0` makes the order
  exactly `p`. Consistency (`ρ(1) = 0`, `ρ'(1) = σ(1)`) is order `≥ 1`
  (`consistent_iff_hasOrder_one`); every method of order `p ≥ 1` is consistent
  (`consistent_of_hasOrder`).
* The `k`-step BDF (`bdfLMM k`) has `σ(ζ) = ζ^k / H_k` and
  `ρ(ζ) = Σ_{j=1}^{k} (1/j) ζ^{k-j} (ζ - 1)^j / H_k`, `H_k = Σ_{j=1}^{k} 1/j` (`bdfHarmonic k`;
  the unnormalized `ρ` is `bdfPolyQ k`, summed as `j + 1` over `range k`).

Source: work-sync theory/T-numerical-integration.md §1.5–§1.6 (BDF table).

Results.
* `bdfLMM_hasExactOrder`: for every `k ≥ 1` the `k`-step BDF has exact order `k`
  (`C_{k+1} = -k!/H_k`); its consistency is `LMM.consistent_of_hasOrder` applied to `.1`.
  Proof: the residual `f ↦ Σᵢ αᵢ f(i) - Σᵢ βᵢ f'(i)` is linear in the polynomial `f`, and on the
  shifted rising factorials `(X - k)⁽ᵐ⁾` (monic of degree `m`, a basis) the pairing with
  `ζ^{k-j} (ζ - 1)^j` is the `j`-th forward difference, which picks out `j = m`; so the residual
  is `((m-1)! - (m-1)!)/H_k = 0` for `1 ≤ m ≤ k` and `-k!/H_k` for `m = k + 1`.
* `bdf1`, …, `bdf6`: BDF1–BDF6 as `bdfLMM 1`, …, `bdfLMM 6` (their coefficients, the source
  table with BDF5/BDF6 completed, are listed in the docstrings); exact order `k` is
  `bdfLMM_hasExactOrder`.

Not formalized.
* Zero-stability of BDF1–6. Failure of zero-stability (a root of `ρ` outside the closed unit
  disk) is proved for every `k ≥ 7` in `theorem/Numerics/BDFInstability.lean`
  (`bdfLMM_not_rootCondition`; role names `bdf7`–`bdf9`).
-/

noncomputable section
namespace powerlib.Numerics
open Finset

/-- A `k`-step linear multistep method with rational coefficients. -/
structure LMM (k : ℕ) where
  α : Fin (k + 1) → ℚ
  β : Fin (k + 1) → ℚ

namespace LMM

variable {k : ℕ}

/-- Dahlquist error constant numerator `C_q`. -/
def C (m : LMM k) (q : ℕ) : ℚ :=
  ∑ i, m.α i * (i : ℚ) ^ q - q * ∑ i, m.β i * (i : ℚ) ^ (q - 1)

/-- Order at least `p`. -/
def HasOrder (m : LMM k) (p : ℕ) : Prop := ∀ q ≤ p, m.C q = 0

/-- Order exactly `p`. -/
def HasExactOrder (m : LMM k) (p : ℕ) : Prop := m.HasOrder p ∧ m.C (p + 1) ≠ 0

/-- Consistency: `ρ(1) = 0` and `ρ'(1) = σ(1)`. -/
def Consistent (m : LMM k) : Prop :=
  ∑ i, m.α i = 0 ∧ ∑ i, m.α i * (i : ℚ) = ∑ i, m.β i

@[tmio T, powerlib_foundation] theorem consistent_iff_hasOrder_one (m : LMM k) :
    m.Consistent ↔ m.HasOrder 1 := by
  constructor
  · rintro ⟨h0, h1⟩ q hq
    interval_cases q
    · simpa [C] using h0
    · simp [C, h1]
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 le_rfl
    simp [C] at h0 h1
    exact ⟨h0, by linarith⟩

/-- Every method of order `p ≥ 1` is consistent. -/
@[tmio T, powerlib_foundation] theorem consistent_of_hasOrder (m : LMM k) {p : ℕ}
    (h : m.HasOrder p) (hp : 1 ≤ p) : m.Consistent :=
  (consistent_iff_hasOrder_one m).2 fun q hq => h q (hq.trans hp)

/-- Order conditions are exactness on monomials: the LMM residual of `x(t) = tᵠ` on the grid
`tᵢ = i h` equals `C_q hᵠ`. -/
@[tmio T, powerlib_foundation] theorem residual_monomial (m : LMM k) (q : ℕ) (hq : 1 ≤ q) (h : ℝ) :
    ∑ i, (m.α i : ℝ) * ((i : ℝ) * h) ^ q -
        h * ∑ i, (m.β i : ℝ) * ((q : ℝ) * ((i : ℝ) * h) ^ (q - 1)) =
      (m.C q : ℝ) * h ^ q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [C, Nat.add_sub_cancel]
  push_cast
  simp only [mul_pow, Finset.mul_sum, Finset.sum_mul, sub_mul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end LMM

/-- BDF`k`: `β_j = 0` for `j < k`. -/
def bdf (k : ℕ) (α : Fin (k + 1) → ℚ) (βk : ℚ) : LMM k :=
  ⟨α, fun i => if (i : ℕ) = k then βk else 0⟩

open Polynomial

/-- Harmonic number `H_k = Σ_{j=1}^{k} 1/j`. -/
def bdfHarmonic (k : ℕ) : ℚ := ∑ j ∈ Finset.range k, 1 / ((j + 1 : ℕ) : ℚ)

/-- The unnormalized BDF`k` first characteristic polynomial
`Σ_{j=1}^{k} (1/j) ζ^{k-j} (ζ - 1)^j` with rational coefficients. -/
def bdfPolyQ (k : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range k, C (1 / ((j + 1 : ℕ) : ℚ)) * X ^ (k - 1 - j) * (X - 1) ^ (j + 1)

/-- The `k`-step BDF for every `k`: `ρ = bdfPolyQ k / H_k`, `σ = ζ^k / H_k`. -/
def bdfLMM (k : ℕ) : LMM k :=
  bdf k (fun i => (bdfPolyQ k).coeff i / bdfHarmonic k) (1 / bdfHarmonic k)

/-! ### Exact order of `bdfLMM k` -/

/-- The residual functional `f ↦ Σᵢ αᵢ f(i) - Σᵢ βᵢ f'(i)` on polynomials; `C_q` is its
value at `Xᵠ`. -/
private def lmmResidual {k : ℕ} (m : LMM k) : ℚ[X] →ₗ[ℚ] ℚ :=
  ∑ i, m.α i • leval (i : ℚ) - ∑ i, m.β i • (leval (i : ℚ)).comp derivative

@[tmio T, powerlib_foundation] private theorem lmmResidual_X_pow {k : ℕ} (m : LMM k) (q : ℕ) :
    lmmResidual m (X ^ q) = m.C q := by
  simp only [lmmResidual, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, leval_apply, derivative_X_pow, LMM.C, smul_eq_mul, eval_pow, eval_X,
    eval_mul, eval_C, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Removing the top coefficient with a monic `g` of degree `n` lowers the degree below `n`. -/
@[tmio T, powerlib_foundation] private theorem degree_sub_lt_of_monic {f g : ℚ[X]} {n : ℕ}
    (hg : g.Monic) (hgn : g.natDegree = n) (hf : f.degree < (n + 1 : ℕ)) :
    (f - C (f.coeff n) * g).degree < n := by
  rw [degree_lt_iff_coeff_zero] at hf ⊢
  intro m hm
  rw [coeff_sub, coeff_C_mul]
  rcases hm.eq_or_lt with rfl | hlt
  · rw [← hgn, hg.coeff_natDegree, hgn]; ring
  · rw [hf m hlt, coeff_eq_zero_of_natDegree_lt (p := g) (by rw [hgn]; exact hlt)]; ring

/-- A linear functional vanishing on monic `g n` of degree `n` for `n < N` vanishes on all
polynomials of degree `< N`. -/
@[tmio T, powerlib_foundation] private theorem linearMap_eq_zero_of_degree_lt
    (L : ℚ[X] →ₗ[ℚ] ℚ) (g : ℕ → ℚ[X]) (hg : ∀ n, (g n).Monic ∧ (g n).natDegree = n) :
    ∀ N : ℕ, (∀ n < N, L (g n) = 0) → ∀ f : ℚ[X], f.degree < N → L f = 0 := by
  intro N
  induction N with
  | zero =>
    intro _ f hf
    have : f = 0 := by
      ext m
      exact (degree_lt_iff_coeff_zero f 0).1 (by exact_mod_cast hf) m (Nat.zero_le m)
    rw [this, map_zero]
  | succ n ih =>
    intro hL f hf
    have hd := degree_sub_lt_of_monic (hg n).1 (hg n).2 hf
    have h1 := ih (fun m hm => hL m (hm.trans n.lt_succ_self)) _ hd
    have h2 : f = (f - C (f.coeff n) * g n) + (f.coeff n) • g n := by
      rw [← C_mul']; ring
    rw [h2, map_add, map_smul, h1, hL n n.lt_succ_self, smul_zero, add_zero]

/-- `⟨P, φ⟩ = Σᵢ [Xⁱ]P · φ(i)`. -/
private def bdfPair (φ : ℚ → ℚ) : ℚ[X] →ₗ[ℚ] ℚ := lsum fun n => φ n • LinearMap.id

@[tmio T, powerlib_foundation] private theorem bdfPair_monomial (φ : ℚ → ℚ) (n : ℕ) (c : ℚ) :
    bdfPair φ (monomial n c) = φ n * c := by
  simp [bdfPair, lsum_apply, sum_monomial_index]

/-- Multiplying by `X - 1` is the forward difference `φ(x + 1) - φ(x)` under the pairing. -/
@[tmio T, powerlib_foundation] private theorem bdfPair_mul_X_sub_one (φ ψ : ℚ → ℚ)
    (hψ : ∀ x, ψ x = φ (x + 1) - φ x) (Q : ℚ[X]) :
    bdfPair φ (Q * (X - 1)) = bdfPair ψ Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]
  | monomial n c =>
    rw [mul_sub, mul_one, monomial_mul_X, map_sub, bdfPair_monomial, bdfPair_monomial,
      bdfPair_monomial, hψ]
    push_cast; ring

/-- `⟨X^a (X - 1)^b, r (x - c)⁽ᵐ⁾⟩` is the `b`-th forward difference of the rising factorial
at `a`. -/
@[tmio T, powerlib_foundation] private theorem bdfPair_poch (a b : ℕ) :
    ∀ (m : ℕ) (r c : ℚ), bdfPair (fun x => r * (ascPochhammer ℚ m).eval (x - c))
        (X ^ a * (X - 1) ^ b) =
      r * m.descFactorial b * (ascPochhammer ℚ (m - b)).eval ((a : ℚ) - c + b) := by
  induction b with
  | zero =>
    intro m r c
    rw [pow_zero, mul_one, X_pow_eq_monomial, bdfPair_monomial]
    simp
  | succ b ih =>
    intro m r c
    rw [pow_succ, ← mul_assoc, bdfPair_mul_X_sub_one _
      (fun x => (r * m) * (ascPochhammer ℚ (m - 1)).eval (x - (c - 1))), ih]
    · cases m with
      | zero => simp
      | succ m =>
        rw [Nat.succ_descFactorial_succ, Nat.add_sub_cancel, Nat.add_sub_add_right]
        have e : (a : ℚ) - (c - 1) + b = a - c + ((b + 1 : ℕ) : ℚ) := by push_cast; ring
        rw [e]; push_cast; ring
    · intro x
      cases m with
      | zero => simp
      | succ m =>
        have h1 := ascPochhammer_succ_eval (S := ℚ) m (x - c + 1)
        have h2 : (ascPochhammer ℚ (m + 1)).eval (x - c) =
            (x - c) * (ascPochhammer ℚ m).eval (x - c + 1) := by
          rw [ascPochhammer_succ_left]; simp [eval_comp]
        rw [show x + 1 - c = x - c + 1 by ring, show x - (c - 1) = x - c + 1 by ring, h1, h2,
          Nat.add_sub_cancel]
        push_cast; ring

@[tmio T, powerlib_foundation] private theorem bdfPolyQ_natDegree_le (k : ℕ) :
    (bdfPolyQ k).natDegree ≤ k := by
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have h1 : ((X : ℚ[X]) - 1).natDegree ≤ 1 := by simpa using (natDegree_X_sub_C (1 : ℚ)).le
  rw [mul_assoc]
  refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
  have := natDegree_pow_le_of_le (j + 1) h1
  rw [natDegree_X_pow]
  have := Finset.mem_range.mp hj
  omega

/-- The residual of `bdfLMM k` on the shifted Pochhammer polynomial `(X - k)⁽ᵐ⁾`. -/
@[tmio T, powerlib_foundation] private theorem bdfLMM_residual_poch (k m : ℕ) :
    lmmResidual (bdfLMM k) ((ascPochhammer ℚ m).comp (X - C (k : ℚ))) =
      (∑ j ∈ range k, 1 / ((j + 1 : ℕ) : ℚ) * (if j + 1 = m then (m.factorial : ℚ) else 0) -
        (derivative (ascPochhammer ℚ m)).eval 0) / bdfHarmonic k := by
  set g := (ascPochhammer ℚ m).comp (X - C (k : ℚ)) with hg
  have hφ : bdfPair (fun x => g.eval x) (bdfPolyQ k) =
      ∑ i : Fin (k + 1), g.eval ((i : ℕ) : ℚ) * (bdfPolyQ k).coeff i := by
    rw [bdfPair, lsum_apply, sum_over_range' _ (by simp) (k + 1)
      (Nat.lt_succ_of_le (bdfPolyQ_natDegree_le k))]
    rw [Fin.sum_univ_eq_sum_range (fun i => g.eval (i : ℚ) * (bdfPolyQ k).coeff i) (k + 1)]
    simp
  have hφ' : (fun x : ℚ => g.eval x) = fun x : ℚ => 1 * (ascPochhammer ℚ m).eval (x - (k : ℚ)) := by
    funext x; simp [hg, eval_comp]
  have hpair : bdfPair (fun x => g.eval x) (bdfPolyQ k) =
      ∑ j ∈ range k, 1 / ((j + 1 : ℕ) : ℚ) * (if j + 1 = m then (m.factorial : ℚ) else 0) := by
    rw [hφ']
    simp only [bdfPolyQ, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mul_assoc, C_mul', map_smul, smul_eq_mul, bdfPair_poch]
    have hjk := Finset.mem_range.mp hj
    have e : ((k - 1 - j : ℕ) : ℚ) - k + ((j + 1 : ℕ) : ℚ) = 0 := by
      have h := congrArg (Nat.cast (R := ℚ)) (show k - 1 - j + (j + 1) = k by omega)
      push_cast at h ⊢; linarith
    rw [e, ascPochhammer_eval_zero]
    congr 1
    rcases lt_trichotomy (j + 1) m with h | h | h
    · simp [show m - (j + 1) ≠ 0 by omega, h.ne]
    · subst h; rw [Nat.descFactorial_self]; simp
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]; simp [show j + 1 ≠ m by omega]
  have hβ : ∑ i : Fin (k + 1), (if (i : ℕ) = k then 1 / bdfHarmonic k else 0) *
      (derivative g).eval ((i : ℕ) : ℚ) =
      (derivative (ascPochhammer ℚ m)).eval 0 / bdfHarmonic k := by
    rw [Finset.sum_eq_single (Fin.last k)
      (fun b _ hb => by simp [show (b : ℕ) ≠ k from fun h => hb (Fin.ext (by simpa using h))])
      (by simp)]
    simp [hg, derivative_comp, eval_comp]
    ring
  simp only [lmmResidual, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, leval_apply, smul_eq_mul, bdfLMM, bdf]
  rw [hβ, ← hpair, hφ, sub_div, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Exact order of the `k`-step BDF for every `k ≥ 1`**: `bdfLMM k` has order `k` and
`C_{k+1} = -k! / H_k ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem bdfLMM_hasExactOrder {k : ℕ} (hk : 1 ≤ k) :
    (bdfLMM k).HasExactOrder k := by
  set g : ℕ → ℚ[X] := fun m => (ascPochhammer ℚ m).comp (X - C (k : ℚ)) with hgdef
  have hg : ∀ n, (g n).Monic ∧ (g n).natDegree = n := fun n =>
    ⟨(monic_ascPochhammer ℚ n).comp (monic_X_sub_C _)
        (by rw [natDegree_X_sub_C]; exact one_ne_zero),
      by rw [hgdef, natDegree_comp, ascPochhammer_natDegree, natDegree_X_sub_C, mul_one]⟩
  have hH : 0 < bdfHarmonic k :=
    Finset.sum_pos (fun j _ => by positivity) (Finset.nonempty_range_iff.mpr (by omega))
  have hzero : ∀ n < k + 1, lmmResidual (bdfLMM k) (g n) = 0 := by
    intro n hn
    rw [bdfLMM_residual_poch]
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.sum_eq_single n (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      simp [ascPochhammer_succ_left, derivative_mul, eval_comp, ascPochhammer_eval_one,
        Nat.factorial_succ]
      field_simp
      simp
  have hvan := linearMap_eq_zero_of_degree_lt _ g hg (k + 1) hzero
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [← lmmResidual_X_pow]
    exact hvan _ (by rw [degree_X_pow]; exact_mod_cast Nat.lt_succ_of_le hq)
  · rw [← lmmResidual_X_pow]
    have hd := degree_sub_lt_of_monic (f := (X : ℚ[X]) ^ (k + 1)) (hg (k + 1)).1 (hg (k + 1)).2
      (by rw [degree_X_pow]; exact_mod_cast Nat.lt_succ_self _)
    have e : (X : ℚ[X]) ^ (k + 1) =
        ((X : ℚ[X]) ^ (k + 1) - C (((X : ℚ[X]) ^ (k + 1)).coeff (k + 1)) * g (k + 1)) +
          g (k + 1) := by simp
    rw [e, map_add, hvan _ hd, zero_add, bdfLMM_residual_poch,
      Finset.sum_eq_zero (fun j hj => by simp [(Finset.mem_range.mp hj).ne])]
    simp [ascPochhammer_succ_left, derivative_mul, eval_comp, ascPochhammer_eval_one,
      hH.ne', Nat.factorial_ne_zero]


/-! ### BDF1–BDF6 -/

/-- BDF1 (backward Euler): `α = (-1, 1)`, `β_1 = 1`. -/
abbrev bdf1 : LMM 1 := bdfLMM 1
/-- BDF2: `α = (1/3, -4/3, 1)`, `β_2 = 2/3`. -/
abbrev bdf2 : LMM 2 := bdfLMM 2
/-- BDF3: `α = (-2/11, 9/11, -18/11, 1)`, `β_3 = 6/11`. -/
abbrev bdf3 : LMM 3 := bdfLMM 3
/-- BDF4: `α = (3/25, -16/25, 36/25, -48/25, 1)`, `β_4 = 12/25`. -/
abbrev bdf4 : LMM 4 := bdfLMM 4
/-- BDF5: `α = (-12/137, 75/137, -200/137, 300/137, -300/137, 1)`, `β_5 = 60/137`. -/
abbrev bdf5 : LMM 5 := bdfLMM 5
/-- BDF6: `α = (10/147, -72/147, 225/147, -400/147, 450/147, -360/147, 1)`,
`β_6 = 60/147`. -/
abbrev bdf6 : LMM 6 := bdfLMM 6

end powerlib.Numerics
