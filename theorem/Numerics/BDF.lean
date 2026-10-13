import theorem.Attributes
import dependencies.Mathlib

/-! Linear multistep methods: Dahlquist order conditions and the BDF coefficient table.

Model boundary: a `k`-step linear multistep method `Σᵢ αᵢ x_{n+i} = h Σᵢ βᵢ f_{n+i}` with
exact rational coefficients (`α_k = 1`).  Order is the classical algebraic notion: the error
constants `C_q = Σᵢ αᵢ iᵠ - q Σᵢ βᵢ i^{q-1}` vanish for `q ≤ p`, which is equivalent to the
method being exact on all monomials `t^q`, `q ≤ p` (`residual_monomial`), and `C_{p+1} ≠ 0`
makes the order exactly `p`.  Consistency (`ρ(1) = 0`, `ρ'(1) = σ(1)`) is order `≥ 1`.

Results: BDF1–BDF6 with the coefficients of the source table (BDF5/BDF6 completed, the table
lists only `β_k`) have exact order `k`.

Source: work-sync theory/T-numerical-integration.md §1.5–§1.6 (BDF table).  Foundation.
Not formalized here: zero-stability of BDF1–6. Failure of zero-stability (a root of `ρ` outside
the closed unit disk) is proved for every `7 ≤ k ≤ 20` in `theorem/Numerics/BDFInstability.lean`
(`bdfLMM_not_rootCondition`; coefficient tables `bdf7`–`bdf9`); the general statement for every
`k ≥ 7` remains UNPROVED.
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

@[powerlib_foundation] theorem consistent_iff_hasOrder_one (m : LMM k) :
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

/-- Order conditions are exactness on monomials: the LMM residual of `x(t) = tᵠ` on the grid
`tᵢ = i h` equals `C_q hᵠ`. -/
@[powerlib_foundation] theorem residual_monomial (m : LMM k) (q : ℕ) (hq : 1 ≤ q) (h : ℝ) :
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

def bdf1 : LMM 1 := bdf 1 ![-1, 1] 1
def bdf2 : LMM 2 := bdf 2 ![1/3, -4/3, 1] (2/3)
def bdf3 : LMM 3 := bdf 3 ![-2/11, 9/11, -18/11, 1] (6/11)
def bdf4 : LMM 4 := bdf 4 ![3/25, -16/25, 36/25, -48/25, 1] (12/25)
def bdf5 : LMM 5 := bdf 5 ![-12/137, 75/137, -200/137, 300/137, -300/137, 1] (60/137)
def bdf6 : LMM 6 := bdf 6 ![10/147, -72/147, 225/147, -400/147, 450/147, -360/147, 1] (60/147)

@[powerlib_foundation] theorem bdf1_exactOrder : bdf1.HasExactOrder 1 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;>
      simp only [LMM.C, bdf1, bdf, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num
  · simp only [LMM.C, bdf1, bdf, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num

@[powerlib_foundation] theorem bdf2_exactOrder : bdf2.HasExactOrder 2 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf2, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf2, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf3_exactOrder : bdf3.HasExactOrder 3 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf3, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf3, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf4_exactOrder : bdf4.HasExactOrder 4 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf4, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf4, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf5_exactOrder : bdf5.HasExactOrder 5 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf5, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf5, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf6_exactOrder : bdf6.HasExactOrder 6 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf6, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf6, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf_consistent :
    bdf1.Consistent ∧ bdf2.Consistent ∧ bdf3.Consistent ∧ bdf4.Consistent ∧
      bdf5.Consistent ∧ bdf6.Consistent := by
  simp only [LMM.consistent_iff_hasOrder_one]
  exact ⟨fun q hq => bdf1_exactOrder.1 q hq,
    fun q hq => bdf2_exactOrder.1 q (by omega), fun q hq => bdf3_exactOrder.1 q (by omega),
    fun q hq => bdf4_exactOrder.1 q (by omega), fun q hq => bdf5_exactOrder.1 q (by omega),
    fun q hq => bdf6_exactOrder.1 q (by omega)⟩

end powerlib.Numerics
