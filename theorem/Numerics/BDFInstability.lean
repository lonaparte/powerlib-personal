import theorem.Numerics.BDF
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Zero-instability of BDF`k` for `7 ≤ k ≤ 20`

Foundation layer (static algebra of the methods' coefficients; no time, no trajectories).

Model boundary: the `k`-step linear multistep method `Σᵢ αᵢ x_{n+i} = h Σᵢ βᵢ f_{n+i}` of
`theorem/Numerics/BDF.lean` with exact rational coefficients. Its first characteristic
polynomial is `ρ(ζ) = Σᵢ αᵢ ζⁱ` over ℂ (`LMM.rho`), and the Dahlquist root condition
(`LMM.RootCondition`) requires every root of `ρ` to lie in the closed unit disk, with the roots
on the unit circle simple (`ρ'(ζ) ≠ 0`, `LMM.rhoDeriv`). The root condition is the algebraic
definition of zero-stability; its equivalence with boundedness of the solutions of the
homogeneous recurrence (and Dahlquist's equivalence theorem) is not formalized here.

The `k`-step BDF has `σ(ζ) = β_k ζ^k` and `ρ_k(ζ) = β_k Σ_{j=1}^{k} (1/j) ζ^{k-j} (ζ - 1)^j`
with `β_k = 1 / H_k`, `H_k = Σ_{j=1}^{k} 1/j` (`bdfRhoSum k`, summed as `j + 1` over
`range k`; `bdfLMM k` is this method for every `k`, with `α_i = [ζⁱ] bdfRhoSum k / H_k`).

Results:
* Foundation (any complex polynomial / any LMM):
  - `norm_sub_le_norm_one_sub_conj_mul`: Blaschke-factor bound `‖w - ζ‖ ≤ ‖1 - w̄ ζ‖` in the
    closed unit disk.
  - `norm_eval_le_of_roots_norm_le_one` (Schur–Cohn necessary condition): if all roots of
    `p : ℂ[X]` lie in the closed unit disk, then `‖p(w)‖ ≤ ‖w‖ⁿ ‖p(1/w̄)‖` for `0 < ‖w‖ ≤ 1`.
  - `LMM.norm_rho_le_norm_rhoRev`: all roots of `ρ` in the closed unit disk (in particular a
    zero-stable method) ⇒ `‖ρ(w)‖ ≤ ‖ρ*(w)‖` for `0 < ‖w‖ ≤ 1`, where `ρ*(w) = Σᵢ αᵢ w^{k-i}`
    (`LMM.rhoRev`); contrapositive `LMM.exists_root_norm_gt_one_of_norm_rhoRev_lt` and
    `LMM.not_rootCondition_of_norm_rhoRev_lt`: one point `0 < ‖w‖ ≤ 1` with
    `‖ρ*(w)‖ < ‖ρ(w)‖` exhibits a root of `ρ` outside the closed unit disk.
  - The same for the BDF polynomial for every `k ≥ 1`:
    `bdfRhoSum_exists_root_norm_gt_one_of_lt`, with reversed polynomial
    `bdfRevSum k w = Σ_{j=1}^{k} (1 - w)^j / j` (`bdfRevSum_eq`); `bdfPoly_natDegree`,
    `bdfLMM_rho_eq` (`ρ(bdfLMM k) = bdfRhoSum k / H_k` for every `k`).
* Instability:
  - `bdfRhoSum_exists_root_norm_gt_one`: for every `7 ≤ k ≤ 20`, `bdfRhoSum k` has a root
    `ζ` with `1 < ‖ζ‖`; hence `bdfLMM_exists_root_norm_gt_one` and
    `bdfLMM_not_rootCondition`: the `k`-step BDF is not zero-stable for `7 ≤ k ≤ 20`.
  - `bdf7`, `bdf8`, `bdf9`: the coefficient tables, each of exact order `k`
    (`bdfk_exactOrder`), with `bdfk.rho = β_k · bdfRhoSum k` (`bdfk_rho_eq_sum`),
    `bdfk_rho_eq_bdfLMM` (same `ρ` as `bdfLMM k`), `bdfk_exists_root_norm_gt_one`
    (numerically `‖ζ‖ ≈ 1.0222, 1.1839, 1.3475`) and `bdfk_not_rootCondition`.

Proof method (exact, kernel-checked; no floating point, Rules §12): write `ρ = a Π (ζ - ζᵢ)`
over the roots (ℂ is algebraically closed). For `‖w‖ ≤ 1` and `‖ζᵢ‖ ≤ 1`,
`‖1 - w̄ ζᵢ‖² - ‖w - ζᵢ‖² = (1 - ‖w‖²)(1 - ‖ζᵢ‖²) ≥ 0`, and `‖w‖ ‖1/w̄ - ζᵢ‖ = ‖1 - w̄ ζᵢ‖`;
multiplying gives the Schur–Cohn bound, and for real coefficients `‖ρ(1/w̄)‖ = ‖ρ(1/w)‖`,
`‖w‖^k ‖ρ(1/w)‖ = ‖ρ*(w)‖`. For each `k` a dyadic point `w_k` near `1/ζ̄₀` (`ζ₀` the
unstable root) is a witness: `ρ_k(w_k) = A + B i` and `ρ_k*(w_k) = A' + B' i` are exact
rationals (checked by `linear_combination Q * Complex.I_sq` with an explicit quotient `Q`) and
`A'² + B'² < A² + B²`. The witnesses and quotients were computed outside Lean (untrusted exact
rational arithmetic, numerical root location only for choosing `w_k`); Lean checks every
identity and inequality.

Not formalized (UNPROVED): failure of zero-stability for every `k ≥ 7` (Cryer 1972; see
Hairer–Nørsett–Wanner, Solving ODE I, §III.3). A uniform proof needs a root-location argument
valid for all `k` (order stars, the root-locus curve with the argument principle, or
asymptotics with explicit error bounds for the zeros of the truncated series `Σ_{j ≤ k} u^j / j`,
`u = 1 - 1/ζ`); Mathlib has no argument principle or Rouché theorem, and the witness inequality
above holds only near the reflected unstable roots `1/ζ̄₀`, whose location depends on `k`, so
no single `k`-uniform witness is available. This file covers `7 ≤ k ≤ 20`, one witness per
`k`. Also not formalized: zero-stability of BDF1–BDF6, and exact order `k` of `bdfLMM k` for
general `k` (checked for the tables `bdf7`–`bdf9` here and BDF1–BDF6 in
`theorem/Numerics/BDF.lean`).

Source: work-sync theory/T-numerical-integration.md §1.5 (0-stability: all roots of `ρ` in
`|ζ| ≤ 1`, those on `|ζ| = 1` simple), §1.6 (BDF table row "k ≥ 7: 0-不稳定") and §2.4
("BDF7+ 不存在（0-不稳定）"). The note's claim is formalized for `7 ≤ k ≤ 20`. Foundation.
-/

noncomputable section
namespace powerlib.Numerics
open Finset Polynomial ComplexConjugate

namespace LMM

variable {k : ℕ}

/-- First characteristic polynomial `ρ(ζ) = Σᵢ αᵢ ζⁱ`, evaluated over ℂ. -/
def rho (m : LMM k) (ζ : ℂ) : ℂ := ∑ i, (m.α i : ℂ) * ζ ^ (i : ℕ)

/-- Its derivative `ρ'(ζ) = Σᵢ i αᵢ ζ^{i-1}`. -/
def rhoDeriv (m : LMM k) (ζ : ℂ) : ℂ :=
  ∑ i, (m.α i : ℂ) * ((i : ℕ) : ℂ) * ζ ^ ((i : ℕ) - 1)

/-- Reversed first characteristic polynomial `ρ*(w) = Σᵢ αᵢ w^{k-i}` (`= w^k ρ(1/w)`). -/
def rhoRev (m : LMM k) (w : ℂ) : ℂ := ∑ i, (m.α i : ℂ) * w ^ (k - (i : ℕ))

/-- Dahlquist root condition (algebraic zero-stability): every root of `ρ` lies in the closed
unit disk, and roots on the unit circle are simple. -/
def RootCondition (m : LMM k) : Prop :=
  ∀ ζ : ℂ, m.rho ζ = 0 → ‖ζ‖ ≤ 1 ∧ (‖ζ‖ = 1 → m.rhoDeriv ζ ≠ 0)

/-- A root of `ρ` outside the closed unit disk violates the root condition. -/
@[powerlib_foundation] theorem not_rootCondition_of_root (m : LMM k) {ζ : ℂ} (h : m.rho ζ = 0)
    (h1 : 1 < ‖ζ‖) : ¬ m.RootCondition := fun hm => absurd (hm ζ h).1 (not_le.mpr h1)

end LMM

/-! ## Schur–Cohn necessary condition -/

/-- Blaschke factor bound: for `‖w‖ ≤ 1` and `‖ζ‖ ≤ 1`, `‖w - ζ‖ ≤ ‖1 - w̄ ζ‖`, from
`‖1 - w̄ ζ‖² - ‖w - ζ‖² = (1 - ‖w‖²)(1 - ‖ζ‖²)`. -/
@[powerlib_foundation] theorem norm_sub_le_norm_one_sub_conj_mul {w ζ : ℂ} (hw : ‖w‖ ≤ 1)
    (hζ : ‖ζ‖ ≤ 1) : ‖w - ζ‖ ≤ ‖1 - conj w * ζ‖ := by
  have key : ‖1 - conj w * ζ‖ ^ 2 - ‖w - ζ‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖ζ‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  have h1 : 0 ≤ (1 - ‖w‖ ^ 2) * (1 - ‖ζ‖ ^ 2) :=
    mul_nonneg (by nlinarith [norm_nonneg w]) (by nlinarith [norm_nonneg ζ])
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

/-- Multiset form of the Schur–Cohn bound: `‖Π (w - ζ)‖ ≤ ‖w‖^#s ‖Π (1/w̄ - ζ)‖` when all
`ζ ∈ s` lie in the closed unit disk and `0 < ‖w‖ ≤ 1`. -/
@[powerlib_foundation] theorem norm_prod_sub_le (s : Multiset ℂ) (hs : ∀ ζ ∈ s, ‖ζ‖ ≤ 1) {w : ℂ}
    (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1) :
    ‖(s.map fun ζ => w - ζ).prod‖ ≤
      ‖w‖ ^ Multiset.card s * ‖(s.map fun ζ => (conj w)⁻¹ - ζ).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul]
    have ha := hs a (Multiset.mem_cons_self a s)
    have hs' := ih (fun ζ hζ => hs ζ (Multiset.mem_cons_of_mem hζ))
    have hfac1 : ‖w - a‖ ≤ ‖w‖ * ‖(conj w)⁻¹ - a‖ := by
      have e : ‖w‖ * ‖(conj w)⁻¹ - a‖ = ‖1 - conj w * a‖ := by
        rw [← Complex.norm_conj w, ← norm_mul, mul_sub,
          mul_inv_cancel₀ ((_root_.map_ne_zero _).mpr hw0)]
      rw [e]; exact norm_sub_le_norm_one_sub_conj_mul hw ha
    calc ‖w - a‖ * ‖(s.map fun x => w - x).prod‖
        ≤ (‖w‖ * ‖(conj w)⁻¹ - a‖) * (‖w‖ ^ Multiset.card s *
            ‖(s.map fun x => (conj w)⁻¹ - x).prod‖) :=
          mul_le_mul hfac1 hs' (norm_nonneg _) (by positivity)
      _ = ‖w‖ ^ (Multiset.card s + 1) * (‖(conj w)⁻¹ - a‖ *
            ‖(s.map fun x => (conj w)⁻¹ - x).prod‖) := by ring

/-- **Schur–Cohn necessary condition.** If every root of a complex polynomial `p` lies in the
closed unit disk, then `‖p(w)‖ ≤ ‖w‖ⁿ ‖p(1 / w̄)‖` for every `0 < ‖w‖ ≤ 1` (`n = deg p`). -/
@[powerlib_foundation] theorem norm_eval_le_of_roots_norm_le_one (p : ℂ[X])
    (hroots : ∀ ζ ∈ p.roots, ‖ζ‖ ≤ 1) {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1) :
    ‖p.eval w‖ ≤ ‖w‖ ^ p.natDegree * ‖p.eval (conj w)⁻¹‖ := by
  have hcard := IsAlgClosed.card_roots_eq_natDegree (p := p)
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have key := norm_prod_sub_le p.roots hroots hw0 hw
  rw [hcard] at key
  have e : ∀ z : ℂ, p.eval z = p.leadingCoeff * (p.roots.map fun ζ => z - ζ).prod := by
    intro z
    conv_lhs => rw [← hfac]
    simp [eval_multiset_prod, Multiset.map_map]
  rw [e, e, norm_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left key (norm_nonneg _)

namespace LMM

variable {k : ℕ}

/-- `ρ` as a polynomial over ℂ. -/
def rhoPoly (m : LMM k) : ℂ[X] := ∑ i, Polynomial.C (m.α i : ℂ) * X ^ (i : ℕ)

@[powerlib_foundation] theorem rhoPoly_eval (m : LMM k) (z : ℂ) :
    m.rhoPoly.eval z = m.rho z := by
  simp [rhoPoly, rho, eval_finsetSum]

@[powerlib_foundation] theorem rhoPoly_natDegree (m : LMM k) (h : m.α (Fin.last k) ≠ 0) :
    m.rhoPoly.natDegree = k := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)
  · simp only [rhoPoly, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Fin.last k)]
    · simpa using h
    · intro b _ hb
      simp only [ite_eq_right_iff]
      intro hk
      exact absurd (Fin.ext (by simp [hk])) hb
    · simp

/-- `ρ` has real (rational) coefficients. -/
@[powerlib_foundation] theorem rho_conj (m : LMM k) (z : ℂ) :
    m.rho (conj z) = conj (m.rho z) := by
  simp [rho, map_sum, map_ratCast]

@[powerlib_foundation] theorem rhoRev_eq (m : LMM k) {w : ℂ} (hw : w ≠ 0) :
    m.rhoRev w = w ^ k * m.rho w⁻¹ := by
  simp only [rhoRev, rho, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_sub₀ _ hw (Nat.lt_succ_iff.mp i.isLt), inv_pow]
  ring

/-- If all roots of `ρ` lie in the closed unit disk (e.g. under the root condition), then
`‖ρ(w)‖ ≤ ‖ρ*(w)‖` for `0 < ‖w‖ ≤ 1`. -/
@[powerlib_foundation] theorem norm_rho_le_norm_rhoRev (m : LMM k) (h : m.α (Fin.last k) ≠ 0)
    (hroots : ∀ ζ, m.rho ζ = 0 → ‖ζ‖ ≤ 1) {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1) :
    ‖m.rho w‖ ≤ ‖m.rhoRev w‖ := by
  have hP : m.rhoPoly ≠ 0 := by
    intro h0
    have := m.rhoPoly_natDegree h
    rw [h0, natDegree_zero] at this
    subst this
    apply h
    have := congrArg (fun p => p.coeff 0) h0
    simpa [rhoPoly, finsetSum_coeff, coeff_C_mul_X_pow] using this
  have hr : ∀ ζ ∈ m.rhoPoly.roots, ‖ζ‖ ≤ 1 := fun ζ hζ => by
    rw [mem_roots hP, IsRoot, rhoPoly_eval] at hζ
    exact hroots ζ hζ
  have := norm_eval_le_of_roots_norm_le_one m.rhoPoly hr hw0 hw
  rw [rhoPoly_eval, rhoPoly_eval, rhoPoly_natDegree m h, ← map_inv₀, rho_conj,
    Complex.norm_conj] at this
  rwa [m.rhoRev_eq hw0, norm_mul, norm_pow]

/-- **A root outside the unit disk from one exact inequality.** If `‖ρ*(w)‖ < ‖ρ(w)‖` at a
single point `0 < ‖w‖ ≤ 1`, then `ρ` has a root `ζ` with `1 < ‖ζ‖`. -/
@[powerlib_foundation] theorem exists_root_norm_gt_one_of_norm_rhoRev_lt (m : LMM k)
    (h : m.α (Fin.last k) ≠ 0) {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1)
    (hlt : ‖m.rhoRev w‖ < ‖m.rho w‖) : ∃ ζ, m.rho ζ = 0 ∧ 1 < ‖ζ‖ := by
  by_contra hne
  simp only [not_exists, not_and, not_lt] at hne
  exact absurd (m.norm_rho_le_norm_rhoRev h hne hw0 hw) (not_le.mpr hlt)

/-- The same witness violates the root condition. -/
@[powerlib_foundation] theorem not_rootCondition_of_norm_rhoRev_lt (m : LMM k)
    (h : m.α (Fin.last k) ≠ 0) {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1)
    (hlt : ‖m.rhoRev w‖ < ‖m.rho w‖) : ¬ m.RootCondition := by
  obtain ⟨ζ, hζ, h1⟩ := m.exists_root_norm_gt_one_of_norm_rhoRev_lt h hw0 hw hlt
  exact m.not_rootCondition_of_root hζ h1

end LMM

/-! ## Exact norm comparisons at Gaussian-rational points -/

@[powerlib_foundation] theorem ofReal_add_mul_I_ne_zero {a b : ℝ} (h : 0 < a ^ 2 + b ^ 2) :
    (a : ℂ) + b * Complex.I ≠ 0 := by
  intro h0
  have := congrArg Complex.normSq h0
  rw [Complex.normSq_add_mul_I, map_zero] at this
  linarith

@[powerlib_foundation] theorem norm_ofReal_add_mul_I_le_one {a b : ℝ} (h : a ^ 2 + b ^ 2 ≤ 1) :
    ‖(a : ℂ) + b * Complex.I‖ ≤ 1 := by
  have h2 : ‖(a : ℂ) + b * Complex.I‖ ^ 2 ≤ 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I, one_pow]; exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h2

@[powerlib_foundation] theorem norm_ofReal_add_mul_I_lt {a b c d : ℝ}
    (h : a ^ 2 + b ^ 2 < c ^ 2 + d ^ 2) :
    ‖(a : ℂ) + b * Complex.I‖ < ‖(c : ℂ) + d * Complex.I‖ := by
  have h2 : ‖(a : ℂ) + b * Complex.I‖ ^ 2 < ‖(c : ℂ) + d * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
    exact h
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

/-! ## The BDF polynomial for general `k` -/

/-- The unnormalized BDF`k` first characteristic polynomial
`Σ_{j=1}^{k} (1/j) ζ^{k-j} (ζ - 1)^j`. -/
def bdfRhoSum (k : ℕ) (ζ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range k, (1 / ((j + 1 : ℕ) : ℂ)) * ζ ^ (k - 1 - j) * (ζ - 1) ^ (j + 1)

/-- Its reversal `Σ_{j=1}^{k} (1 - w)^j / j` (`= w^k bdfRhoSum k (1/w)`, `bdfRevSum_eq`). -/
def bdfRevSum (k : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range k, (1 / ((j + 1 : ℕ) : ℂ)) * (1 - w) ^ (j + 1)

/-- `bdfRhoSum k` as a complex polynomial. -/
def bdfPoly (k : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range k, Polynomial.C (1 / ((j + 1 : ℕ) : ℂ)) * X ^ (k - 1 - j) * (X - 1) ^ (j + 1)

@[powerlib_foundation] theorem bdfPoly_eval (k : ℕ) (z : ℂ) :
    (bdfPoly k).eval z = bdfRhoSum k z := by
  simp [bdfPoly, bdfRhoSum, eval_finsetSum]

private theorem bdfPoly_term (k j : ℕ) (hj : j < k) :
    ((X : ℂ[X]) ^ (k - 1 - j) * (X - 1) ^ (j + 1)).Monic ∧
      ((X : ℂ[X]) ^ (k - 1 - j) * (X - 1) ^ (j + 1)).natDegree = k := by
  have h1 : ((X : ℂ[X]) - 1).Monic := by simpa using monic_X_sub_C (1 : ℂ)
  have h1d : ((X : ℂ[X]) - 1).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : ℂ)
  refine ⟨(monic_X_pow _).mul (h1.pow _), ?_⟩
  rw [(monic_X_pow _).natDegree_mul (h1.pow _), natDegree_X_pow, h1.natDegree_pow, h1d]
  omega

@[powerlib_foundation] theorem bdfPoly_natDegree_le (k : ℕ) : (bdfPoly k).natDegree ≤ k :=
  natDegree_sum_le_of_forall_le _ _ fun j hj => by
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans (bdfPoly_term k j (Finset.mem_range.mp hj)).2.le

/-- The leading coefficient of `bdfRhoSum k` is `H_k = Σ_{j=1}^{k} 1/j`. -/
@[powerlib_foundation] theorem bdfPoly_coeff (k : ℕ) :
    (bdfPoly k).coeff k = ∑ j ∈ Finset.range k, 1 / ((j + 1 : ℕ) : ℂ) := by
  simp only [bdfPoly, finsetSum_coeff, mul_assoc, coeff_C_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hm, hd⟩ := bdfPoly_term k j (Finset.mem_range.mp hj)
  have := hm.coeff_natDegree
  rw [hd] at this
  rw [this, mul_one]

@[powerlib_foundation] theorem bdfPoly_natDegree {k : ℕ} (hk : 0 < k) :
    (bdfPoly k).natDegree = k := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (bdfPoly_natDegree_le k)
  rw [bdfPoly_coeff]
  have e : (∑ j ∈ Finset.range k, 1 / ((j + 1 : ℕ) : ℂ)) =
      ((∑ j ∈ Finset.range k, 1 / ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.ofReal_ne_zero]
  exact (Finset.sum_pos (fun j _ => by positivity) (Finset.nonempty_range_iff.mpr hk.ne')).ne'

/-- `bdfRhoSum k` has real coefficients. -/
@[powerlib_foundation] theorem bdfRhoSum_conj (k : ℕ) (z : ℂ) :
    bdfRhoSum k (conj z) = conj (bdfRhoSum k z) := by
  simp [bdfRhoSum, map_sum]

@[powerlib_foundation] theorem bdfRevSum_eq (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    bdfRevSum k w = w ^ k * bdfRhoSum k w⁻¹ := by
  simp only [bdfRevSum, bdfRhoSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  have e1 : w ^ (k - 1 - j) * w⁻¹ ^ (k - 1 - j) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  have e2 : w ^ (j + 1) * (w⁻¹ - 1) ^ (j + 1) = (1 - w) ^ (j + 1) := by
    rw [← mul_pow, mul_sub, mul_inv_cancel₀ hw, mul_one]
  calc (1 / ((j + 1 : ℕ) : ℂ)) * (1 - w) ^ (j + 1)
      = (1 / ((j + 1 : ℕ) : ℂ)) * ((w ^ (k - 1 - j) * w⁻¹ ^ (k - 1 - j)) *
          (w ^ (j + 1) * (w⁻¹ - 1) ^ (j + 1))) := by rw [e1, e2, one_mul]
    _ = (w ^ (k - 1 - j) * w ^ (j + 1)) * ((1 / ((j + 1 : ℕ) : ℂ)) * w⁻¹ ^ (k - 1 - j) *
          (w⁻¹ - 1) ^ (j + 1)) := by ring
    _ = w ^ k * ((1 / ((j + 1 : ℕ) : ℂ)) * w⁻¹ ^ (k - 1 - j) * (w⁻¹ - 1) ^ (j + 1)) := by
        rw [← pow_add, show k - 1 - j + (j + 1) = k by omega]

/-- Schur–Cohn necessary condition for the BDF polynomial: if all roots of `bdfRhoSum k` lie in
the closed unit disk, then `‖bdfRhoSum k w‖ ≤ ‖bdfRevSum k w‖` for `0 < ‖w‖ ≤ 1`. -/
@[powerlib_foundation] theorem norm_bdfRhoSum_le_norm_bdfRevSum {k : ℕ} (hk : 0 < k)
    (hroots : ∀ ζ, bdfRhoSum k ζ = 0 → ‖ζ‖ ≤ 1) {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1) :
    ‖bdfRhoSum k w‖ ≤ ‖bdfRevSum k w‖ := by
  have hP : bdfPoly k ≠ 0 := fun h0 => by
    have := bdfPoly_natDegree hk
    rw [h0, natDegree_zero] at this
    omega
  have hr : ∀ ζ ∈ (bdfPoly k).roots, ‖ζ‖ ≤ 1 := fun ζ hζ => by
    rw [mem_roots hP, IsRoot, bdfPoly_eval] at hζ
    exact hroots ζ hζ
  have := norm_eval_le_of_roots_norm_le_one (bdfPoly k) hr hw0 hw
  rw [bdfPoly_eval, bdfPoly_eval, bdfPoly_natDegree hk, ← map_inv₀, bdfRhoSum_conj,
    Complex.norm_conj] at this
  rwa [bdfRevSum_eq k hw0, norm_mul, norm_pow]

/-- One point `0 < ‖w‖ ≤ 1` with `‖bdfRevSum k w‖ < ‖bdfRhoSum k w‖` exhibits a root of
`bdfRhoSum k` outside the closed unit disk. -/
@[powerlib_foundation] theorem bdfRhoSum_exists_root_norm_gt_one_of_lt {k : ℕ} (hk : 0 < k)
    {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1) (hlt : ‖bdfRevSum k w‖ < ‖bdfRhoSum k w‖) :
    ∃ ζ, bdfRhoSum k ζ = 0 ∧ 1 < ‖ζ‖ := by
  by_contra hne
  simp only [not_exists, not_and, not_lt] at hne
  exact absurd (norm_bdfRhoSum_le_norm_bdfRevSum hk hne hw0 hw) (not_le.mpr hlt)

/-- Harmonic number `H_k = Σ_{j=1}^{k} 1/j`. -/
def bdfHarmonic (k : ℕ) : ℚ := ∑ j ∈ Finset.range k, 1 / ((j + 1 : ℕ) : ℚ)

/-- `bdfRhoSum k` with rational coefficients. -/
def bdfPolyQ (k : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range k, Polynomial.C (1 / ((j + 1 : ℕ) : ℚ)) * X ^ (k - 1 - j) * (X - 1) ^ (j + 1)

/-- The `k`-step BDF for every `k`: `ρ = bdfRhoSum k / H_k`, `σ = ζ^k / H_k`. -/
def bdfLMM (k : ℕ) : LMM k :=
  bdf k (fun i => (bdfPolyQ k).coeff i / bdfHarmonic k) (1 / bdfHarmonic k)

@[powerlib_foundation] theorem bdfPolyQ_map (k : ℕ) :
    (bdfPolyQ k).map (algebraMap ℚ ℂ) = bdfPoly k := by
  simp [bdfPolyQ, bdfPoly, Polynomial.map_sum]

@[powerlib_foundation] theorem bdfLMM_rho_eq (k : ℕ) (ζ : ℂ) :
    (bdfLMM k).rho ζ = (1 / (bdfHarmonic k : ℂ)) * bdfRhoSum k ζ := by
  have hdeg : ((bdfPolyQ k).map (algebraMap ℚ ℂ)).natDegree < k + 1 := by
    rw [bdfPolyQ_map]
    exact Nat.lt_succ_of_le (bdfPoly_natDegree_le k)
  rw [← bdfPoly_eval, ← bdfPolyQ_map, eval_eq_sum_range' hdeg, Finset.mul_sum]
  simp only [LMM.rho, bdfLMM, bdf]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (((bdfPolyQ k).coeff i / bdfHarmonic k : ℚ) : ℂ) * ζ ^ i) (k + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_map, eq_ratCast]
  push_cast
  ring

/-! ## Witnesses, `7 ≤ k ≤ 20` -/

/-- Witness value of `bdfRhoSum 7` at `w = 1/16 + 31/32 i`. -/
private theorem bdfRhoSum_witness_7 :
    bdfRhoSum 7 (((1 / 16 : ℝ) : ℂ)
        + ((31 / 32 : ℝ) : ℂ) * Complex.I) = (((-2361592692043 / 7215545057280 : ℝ) : ℝ) : ℂ)
        + (((-1607795559683 / 14431090114560 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination ((250393267549 / 1030792151040 : ℂ)
      + (11863255626563 / 14431090114560 : ℂ) * Complex.I
      - (2967484459309 / 1030792151040 : ℂ) * Complex.I ^ 2
      + (23207047462959 / 4810363371520 : ℂ) * Complex.I ^ 3
      - (1665844409237 / 343597383680 : ℂ) * Complex.I ^ 4
      + (9987078922293 / 4810363371520 : ℂ) * Complex.I ^ 5) * Complex.I_sq

/-- Witness value of `bdfRevSum 7` at `w = 1/16 + 31/32 i`. -/
private theorem bdfRevSum_witness_7 :
    bdfRevSum 7 (((1 / 16 : ℝ) : ℂ)
        + ((31 / 32 : ℝ) : ℂ) * Complex.I) = (((-33749728583 / 360777252864 : ℝ) : ℝ) : ℂ)
        + (((79205805101 / 3607772528640 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((117881458049 / 51539607552 : ℂ)
      - (20406254999021 / 3607772528640 : ℂ) * Complex.I
      + (293619649135 / 51539607552 : ℂ) * Complex.I ^ 2
      - (3735044926913 / 1202590842880 : ℂ) * Complex.I ^ 3
      + (47037695093 / 51539607552 : ℂ) * Complex.I ^ 4
      - (27512614111 / 240518168576 : ℂ) * Complex.I ^ 5) * Complex.I_sq

/-- BDF7: `bdfRhoSum 7` has a root of modulus `> 1` (numerically `≈ 1.0222`). -/
private theorem bdfRhoSum_exists_root_7 : ∃ ζ : ℂ, bdfRhoSum 7 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((1 / 16 : ℝ) : ℂ)
      + ((31 / 32 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_7, bdfRevSum_witness_7]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 8` at `w = 0 + 3/4 i`. -/
private theorem bdfRhoSum_witness_8 :
    bdfRhoSum 8 (((0 : ℝ) : ℂ)
        + ((3 / 4 : ℝ) : ℂ) * Complex.I) = (((15001241 / 18350080 : ℝ) : ℝ) : ℂ)
        + (((36273 / 71680 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination (-(12707481 / 18350080 : ℂ) - (13959 / 10240 : ℂ) * Complex.I
      + (60876441 / 18350080 : ℂ) * Complex.I ^ 2 - (6885 / 2048 : ℂ) * Complex.I ^ 3
      + (40729959 / 18350080 : ℂ) * Complex.I ^ 4 - (2187 / 2048 : ℂ) * Complex.I ^ 5
      + (4992921 / 18350080 : ℂ) * Complex.I ^ 6) * Complex.I_sq

/-- Witness value of `bdfRevSum 8` at `w = 0 + 3/4 i`. -/
private theorem bdfRevSum_witness_8 :
    bdfRevSum 8 (((0 : ℝ) : ℂ)
        + ((3 / 4 : ℝ) : ℂ) * Complex.I) = (((-8038909 / 18350080 : ℝ) : ℝ) : ℂ)
        + (((-45177 / 71680 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((1654623 / 524288 : ℂ) - (384903 / 71680 : ℂ) * Complex.I
      + (2474145 / 524288 : ℂ) * Complex.I ^ 2 - (179577 / 71680 : ℂ) * Complex.I ^ 3
      + (428895 / 524288 : ℂ) * Complex.I ^ 4 - (2187 / 14336 : ℂ) * Complex.I ^ 5
      + (6561 / 524288 : ℂ) * Complex.I ^ 6) * Complex.I_sq

/-- BDF8: `bdfRhoSum 8` has a root of modulus `> 1` (numerically `≈ 1.1839`). -/
private theorem bdfRhoSum_exists_root_8 : ∃ ζ : ℂ, bdfRhoSum 8 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((0 : ℝ) : ℂ)
      + ((3 / 4 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_8, bdfRevSum_witness_8]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 9` at `w = 0 + 3/4 i`. -/
private theorem bdfRhoSum_witness_9 :
    bdfRhoSum 9 (((0 : ℝ) : ℂ)
        + ((3 / 4 : ℝ) : ℂ) * Complex.I) = (((-22900403 / 20643840 : ℝ) : ℝ) : ℂ)
        + (((16316883 / 73400320 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination ((2289627 / 2293760 : ℂ) + (45614637 / 73400320 : ℂ) * Complex.I
      - (1275021 / 327680 : ℂ) * Complex.I ^ 2 + (387906003 / 73400320 : ℂ) * Complex.I ^ 3
      - (267543 / 65536 : ℂ) * Complex.I ^ 4 + (160768557 / 73400320 : ℂ) * Complex.I ^ 5
      - (59049 / 65536 : ℂ) * Complex.I ^ 6
      + (15591123 / 73400320 : ℂ) * Complex.I ^ 7) * Complex.I_sq

/-- Witness value of `bdfRevSum 9` at `w = 0 + 3/4 i`. -/
private theorem bdfRevSum_witness_9 :
    bdfRevSum 9 (((0 : ℝ) : ℂ)
        + ((3 / 4 : ℝ) : ℂ) * Complex.I) = (((48173299 / 165150720 : ℝ) : ℝ) : ℂ)
        + (((-2196801 / 9175040 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((1330263 / 524288 : ℂ) - (59734719 / 9175040 : ℂ) * Complex.I
      + (3978153 / 524288 : ℂ) * Complex.I ^ 2 - (48645441 / 9175040 : ℂ) * Complex.I ^ 3
      + (1247319 / 524288 : ℂ) * Complex.I ^ 4 - (1244403 / 1835008 : ℂ) * Complex.I ^ 5
      + (59049 / 524288 : ℂ) * Complex.I ^ 6 - (2187 / 262144 : ℂ) * Complex.I ^ 7) * Complex.I_sq

/-- BDF9: `bdfRhoSum 9` has a root of modulus `> 1` (numerically `≈ 1.3475`). -/
private theorem bdfRhoSum_exists_root_9 : ∃ ζ : ℂ, bdfRhoSum 9 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((0 : ℝ) : ℂ)
      + ((3 / 4 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_9, bdfRevSum_witness_9]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 10` at `w = -1/16 + 11/16 i`. -/
private theorem bdfRhoSum_witness_10 :
    bdfRhoSum 10 (((-1 / 16 : ℝ) : ℂ)
        + ((11 / 16 : ℝ) : ℂ) * Complex.I) = (((5885868387253 / 4329327034368 : ℝ) : ℝ) : ℂ)
        + (((-314770770259 / 1924145348608 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination (-(3223364703454379 / 2770769301995520 : ℂ)
      - (345839625303799 / 277076930199552 : ℂ) * Complex.I
      + (4012940806773701 / 692692325498880 : ℂ) * Complex.I ^ 2
      - (2187838060395581 / 277076930199552 : ℂ) * Complex.I ^ 3
      + (8746946457792323 / 1385384650997760 : ℂ) * Complex.I ^ 4
      - (948403801303981 / 277076930199552 : ℂ) * Complex.I ^ 5
      + (942270409103441 / 692692325498880 : ℂ) * Complex.I ^ 6
      - (112476462808391 / 277076930199552 : ℂ) * Complex.I ^ 7
      + (191444130979981 / 2770769301995520 : ℂ) * Complex.I ^ 8) * Complex.I_sq

/-- Witness value of `bdfRevSum 10` at `w = -1/16 + 11/16 i`. -/
private theorem bdfRevSum_witness_10 :
    bdfRevSum 10 (((-1 / 16 : ℝ) : ℂ)
        + ((11 / 16 : ℝ) : ℂ) * Complex.I) = (((1753318992427 / 5411658792960 : ℝ) : ℝ) : ℂ)
        + (((4924574669531 / 21646635171840 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((109791291880963 / 32985348833280 : ℂ)
      - (3254404269524441 / 346346162749440 : ℂ) * Complex.I
      + (94790835409523 / 8246337208320 : ℂ) * Complex.I ^ 2
      - (2966453102021299 / 346346162749440 : ℂ) * Complex.I ^ 3
      + (70005906200549 / 16492674416640 : ℂ) * Complex.I ^ 4
      - (98359020751783 / 69269232549888 : ℂ) * Complex.I ^ 5
      + (853362705261 / 2748779069440 : ℂ) * Complex.I ^ 6
      - (398493159779 / 9895604649984 : ℂ) * Complex.I ^ 7
      + (25937424601 / 10995116277760 : ℂ) * Complex.I ^ 8) * Complex.I_sq

/-- BDF10: `bdfRhoSum 10` has a root of modulus `> 1` (numerically `≈ 1.5127`). -/
private theorem bdfRhoSum_exists_root_10 : ∃ ζ : ℂ, bdfRhoSum 10 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 16 : ℝ) : ℂ)
      + ((11 / 16 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_10, bdfRevSum_witness_10]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 11` at `w = -1/8 + 5/8 i`. -/
private theorem bdfRhoSum_witness_11 :
    bdfRhoSum 11 (((-1 / 8 : ℝ) : ℂ)
        + ((5 / 8 : ℝ) : ℂ) * Complex.I) = (((-13988248765669 / 7441030840320 : ℝ) : ℝ) : ℂ)
        + (((-121204617607 / 496068722688 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination ((6500257003175 / 4329327034368 : ℂ)
      + (44320249850375 / 15874199126016 : ℂ) * Complex.I
      - (20302487974375 / 2164663517184 : ℂ) * Complex.I ^ 2
      + (4540798225625 / 377957122048 : ℂ) * Complex.I ^ 3
      - (10264477871875 / 1082331758592 : ℂ) * Complex.I ^ 4
      + (2938297578125 / 566935683072 : ℂ) * Complex.I ^ 5
      - (4471800390625 / 2164663517184 : ℂ) * Complex.I ^ 6
      + (4927873046875 / 7937099563008 : ℂ) * Complex.I ^ 7
      - (596623046875 / 4329327034368 : ℂ) * Complex.I ^ 8
      + (817490234375 / 47622597378048 : ℂ) * Complex.I ^ 9) * Complex.I_sq

/-- Witness value of `bdfRevSum 11` at `w = -1/8 + 5/8 i`. -/
private theorem bdfRevSum_witness_11 :
    bdfRevSum 11 (((-1 / 8 : ℝ) : ℂ)
        + ((5 / 8 : ℝ) : ℂ) * Complex.I) = (((580735175 / 62008590336 : ℝ) : ℝ) : ℂ)
        + (((208965783085 / 186025771008 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((127454878525 / 25769803776 : ℂ)
      - (85658153242625 / 5952824672256 : ℂ) * Complex.I
      + (228088249375 / 12884901888 : ℂ) * Complex.I ^ 2
      - (40108925174375 / 2976412336128 : ℂ) * Complex.I ^ 3
      + (45106515625 / 6442450944 : ℂ) * Complex.I ^ 4
      - (3799280234375 / 1488206168064 : ℂ) * Complex.I ^ 5
      + (2782421875 / 4294967296 : ℂ) * Complex.I ^ 6
      - (46583984375 / 425201762304 : ℂ) * Complex.I ^ 7
      + (95703125 / 8589934592 : ℂ) * Complex.I ^ 8
      - (48828125 / 94489280512 : ℂ) * Complex.I ^ 9) * Complex.I_sq

/-- BDF11: `bdfRhoSum 11` has a root of modulus `> 1` (numerically `≈ 1.6791`). -/
private theorem bdfRhoSum_exists_root_11 : ∃ ζ : ℂ, bdfRhoSum 11 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 8 : ℝ) : ℂ)
      + ((5 / 8 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_11, bdfRevSum_witness_11]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 12` at `w = -1/8 + 1/2 i`. -/
private theorem bdfRhoSum_witness_12 :
    bdfRhoSum 12 (((-1 / 8 : ℝ) : ℂ)
        + ((1 / 2 : ℝ) : ℂ) * Complex.I) = (((1664116889863013 / 1904903895121920 : ℝ) : ℝ) : ℂ)
        + (((106918075135969 / 119056493445120 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination (-(5759967720407 / 11905649344512 : ℂ)
      - (23577971945203 / 7441030840320 : ℂ) * Complex.I
      + (49096894682603 / 7441030840320 : ℂ) * Complex.I ^ 2
      - (229698258313 / 33218887680 : ℂ) * Complex.I ^ 3
      + (554926024663 / 116266106880 : ℂ) * Complex.I ^ 4
      - (34250790551 / 14533263360 : ℂ) * Complex.I ^ 5
      + (5012028367 / 5813305344 : ℂ) * Complex.I ^ 6 - (61872581 / 259522560 : ℂ) * Complex.I ^ 7
      + (9211801 / 181665792 : ℂ) * Complex.I ^ 8 - (307781 / 37847040 : ℂ) * Complex.I ^ 9
      + (86021 / 113541120 : ℂ) * Complex.I ^ 10) * Complex.I_sq

/-- Witness value of `bdfRevSum 12` at `w = -1/8 + 1/2 i`. -/
private theorem bdfRevSum_witness_12 :
    bdfRevSum 12 (((-1 / 8 : ℝ) : ℂ)
        + ((1 / 2 : ℝ) : ℂ) * Complex.I) = (((-321331755101983 / 317483982520320 : ℝ) : ℝ) : ℂ)
        + (((-5447662453529 / 59528246722560 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((813021345037 / 128849018880 : ℂ)
      - (45941105910181 / 3720515420160 : ℂ) * Complex.I
      + (203739811051 / 16106127360 : ℂ) * Complex.I ^ 2
      - (992190681337 / 116266106880 : ℂ) * Complex.I ^ 3
      + (1027673111 / 251658240 : ℂ) * Complex.I ^ 4 - (2067171565 / 1453326336 : ℂ) * Complex.I ^ 5
      + (22692491 / 62914560 : ℂ) * Complex.I ^ 6 - (1691143 / 25952256 : ℂ) * Complex.I ^ 7
      + (15677 / 1966080 : ℂ) * Complex.I ^ 8 - (107 / 180224 : ℂ) * Complex.I ^ 9
      + (1 / 49152 : ℂ) * Complex.I ^ 10) * Complex.I_sq

/-- BDF12: `bdfRhoSum 12` has a root of modulus `> 1` (numerically `≈ 1.8464`). -/
private theorem bdfRhoSum_exists_root_12 : ∃ ζ : ℂ, bdfRhoSum 12 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 8 : ℝ) : ℂ)
      + ((1 / 2 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_12, bdfRevSum_witness_12]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 13` at `w = -1/8 + 1/2 i`. -/
private theorem bdfRhoSum_witness_13 :
    bdfRhoSum 13 (((-1 / 8 : ℝ) : ℂ)
        + ((1 / 2 : ℝ) : ℂ) * Complex.I) = (((-87104163692410019 / 66036668364226560 : ℝ) : ℝ) : ℂ)
        + (((-2408917654485409 / 4502500115742720 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination ((145191653530591 / 158741991260160 : ℂ)
      + (4749510044585743 / 1547734414786560 : ℂ) * Complex.I
      - (4702212081559 / 566935683072 : ℂ) * Complex.I ^ 2
      + (1969304115219583 / 193466801848320 : ℂ) * Complex.I ^ 3
      - (167243991825 / 20669530112 : ℂ) * Complex.I ^ 4
      + (2783084178997 / 604583755776 : ℂ) * Complex.I ^ 5
      - (151354716361 / 77510737920 : ℂ) * Complex.I ^ 6
      + (475546108099 / 755729694720 : ℂ) * Complex.I ^ 7
      - (377521993 / 2422210560 : ℂ) * Complex.I ^ 8 + (710119703 / 23616552960 : ℂ) * Complex.I ^ 9
      - (4028873 / 908328960 : ℂ) * Complex.I ^ 10
      + (1145993 / 2952069120 : ℂ) * Complex.I ^ 11) * Complex.I_sq

/-- Witness value of `bdfRevSum 13` at `w = -1/8 + 1/2 i`. -/
private theorem bdfRevSum_witness_13 :
    bdfRevSum 13 (((-1 / 8 : ℝ) : ℂ)
        + ((1 / 2 : ℝ) : ℂ) * Complex.I) = (((-2074495091156363 / 8254583545528320 : ℝ) : ℝ) : ℂ)
        + (((4754927337394019 / 6190937659146240 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((1521638484599 / 257698037760 : ℂ)
      - (2952797591809027 / 193466801848320 : ℂ) * Complex.I
      + (597048608087 / 32212254720 : ℂ) * Complex.I ^ 2
      - (351853680754831 / 24183350231040 : ℂ) * Complex.I ^ 3
      + (4087423057 / 503316480 : ℂ) * Complex.I ^ 4
      - (252764471881 / 75572969472 : ℂ) * Complex.I ^ 5
      + (129258187 / 125829120 : ℂ) * Complex.I ^ 6 - (630316889 / 2699034624 : ℂ) * Complex.I ^ 7
      + (150559 / 3932160 : ℂ) * Complex.I ^ 8 - (40225 / 9371648 : ℂ) * Complex.I ^ 9
      + (29 / 98304 : ℂ) * Complex.I ^ 10 - (1 / 106496 : ℂ) * Complex.I ^ 11) * Complex.I_sq

/-- BDF13: `bdfRhoSum 13` has a root of modulus `> 1` (numerically `≈ 2.0145`). -/
private theorem bdfRhoSum_exists_root_13 : ∃ ζ : ℂ, bdfRhoSum 13 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 8 : ℝ) : ℂ)
      + ((1 / 2 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_13, bdfRevSum_witness_13]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 14` at `w = -1/8 + 1/2 i`. -/
private theorem bdfRhoSum_witness_14 :
    bdfRhoSum 14 (((-1 / 8 : ℝ) : ℂ)
        + ((1 / 2 : ℝ) : ℂ)
        * Complex.I) = (((2577393164230952741 / 1584880040741437440 : ℝ) : ℝ) : ℂ)
        + (((-9496180127137139 / 198110005092679680 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination (-(119276951185575257 / 99055002546339840 : ℂ)
      - (17228030380325327 / 6190937659146240 : ℂ) * Complex.I
      + (62355033861234221 / 6190937659146240 : ℂ) * Complex.I ^ 2
      - (11171486623607069 / 773867207393280 : ℂ) * Complex.I ^ 3
      + (5073285433058023 / 386933603696640 : ℂ) * Complex.I ^ 4
      - (20564693017241 / 2418335023104 : ℂ) * Complex.I ^ 5
      + (99987110420999 / 24183350231040 : ℂ) * Complex.I ^ 6
      - (665200604507 / 431845539840 : ℂ) * Complex.I ^ 7
      + (671012760493 / 1511459389440 : ℂ) * Complex.I ^ 8
      - (268895189 / 2699034624 : ℂ) * Complex.I ^ 9 + (110795497 / 6297747456 : ℂ) * Complex.I ^ 10
      - (4054613 / 1686896640 : ℂ) * Complex.I ^ 11
      + (1171733 / 5904138240 : ℂ) * Complex.I ^ 12) * Complex.I_sq

/-- Witness value of `bdfRevSum 14` at `w = -1/8 + 1/2 i`. -/
private theorem bdfRevSum_witness_14 :
    bdfRevSum 14 (((-1 / 8 : ℝ) : ℂ)
        + ((1 / 2 : ℝ) : ℂ) * Complex.I) = (((124484009038522417 / 132073336728453120 : ℝ) : ℝ) : ℂ)
        + (((65017173277104187 / 49527501273169920 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((293379708189541 / 57724360458240 : ℂ)
      - (28043508884941961 / 1547734414786560 : ℂ) * Complex.I
      + (93930920959319 / 3607772528640 : ℂ) * Complex.I ^ 2
      - (4559223151121963 / 193466801848320 : ℂ) * Complex.I ^ 3
      + (3411952462501 / 225485783040 : ℂ) * Complex.I ^ 4
      - (4369460126543 / 604583755776 : ℂ) * Complex.I ^ 5
      + (36867705349 / 14092861440 : ℂ) * Complex.I ^ 6
      - (15522636601 / 21592276992 : ℂ) * Complex.I ^ 7
      + (130473431 / 880803840 : ℂ) * Complex.I ^ 8 - (1666715 / 74973184 : ℂ) * Complex.I ^ 9
      + (25313 / 11010048 : ℂ) * Complex.I ^ 10 - (125 / 851968 : ℂ) * Complex.I ^ 11
      + (1 / 229376 : ℂ) * Complex.I ^ 12) * Complex.I_sq

/-- BDF14: `bdfRhoSum 14` has a root of modulus `> 1` (numerically `≈ 2.1833`). -/
private theorem bdfRhoSum_exists_root_14 : ∃ ζ : ℂ, bdfRhoSum 14 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 8 : ℝ) : ℂ)
      + ((1 / 2 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_14, bdfRevSum_witness_14]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 15` at `w = -1/8 + 7/16 i`. -/
private theorem bdfRhoSum_witness_15 :
    bdfRhoSum 15 (((-1 / 8 : ℝ) : ℂ)
        + ((7 / 16 : ℝ) : ℂ)
        * Complex.I) = (((-269254480822623171774889 / 207733396700061688135680 : ℝ) : ℝ) : ℂ)
        + (((-8410344809246951055059 / 19784133019053494108160 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination ((25321937318046778793167 / 29676199528580241162240 : ℂ)
      + (63211707365091366788819 / 19784133019053494108160 : ℂ) * Complex.I
      - (266507856258248377584847 / 29676199528580241162240 : ℂ) * Complex.I ^ 2
      + (76873383237775949380367 / 6594711006351164702720 : ℂ) * Complex.I ^ 3
      - (295111708025336834969393 / 29676199528580241162240 : ℂ) * Complex.I ^ 4
      + (40753418103636635345137 / 6594711006351164702720 : ℂ) * Complex.I ^ 5
      - (86790411219700456411087 / 29676199528580241162240 : ℂ) * Complex.I ^ 6
      + (7099144381041036656143 / 6594711006351164702720 : ℂ) * Complex.I ^ 7
      - (9227396622299559721073 / 29676199528580241162240 : ℂ) * Complex.I ^ 8
      + (4192851563862539551673 / 59352399057160482324480 : ℂ) * Complex.I ^ 9
      - (75064750667159731667 / 5935239905716048232448 : ℂ) * Complex.I ^ 10
      + (106695333274081461847 / 59352399057160482324480 : ℂ) * Complex.I ^ 11
      - (395175102739375259 / 1978413301905349410816 : ℂ) * Complex.I ^ 12
      + (810989986920701693 / 59352399057160482324480 : ℂ) * Complex.I ^ 13) * Complex.I_sq

/-- Witness value of `bdfRevSum 15` at `w = -1/8 + 7/16 i`. -/
private theorem bdfRevSum_witness_15 :
    bdfRevSum 15 (((-1 / 8 : ℝ) : ℂ)
        + ((7 / 16 : ℝ) : ℂ)
        * Complex.I) = (((209135618141690837237 / 1731111639167180734464 : ℝ) : ℝ) : ℂ)
        + (((1585221156197249432995 / 1483809976429012058112 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((54425995246861785631 / 8646911284551352320 : ℂ)
      - (26782128895618418736547 / 1483809976429012058112 : ℂ) * Complex.I
      + (205152205250637411809 / 8646911284551352320 : ℂ) * Complex.I ^ 2
      - (30144692207350958887517 / 1483809976429012058112 : ℂ) * Complex.I ^ 3
      + (108826255358343482911 / 8646911284551352320 : ℂ) * Complex.I ^ 4
      - (43762194963276280473647 / 7419049882145060290560 : ℂ) * Complex.I ^ 5
      + (18447082853398004449 / 8646911284551352320 : ℂ) * Complex.I ^ 6
      - (4441984805126037346513 / 7419049882145060290560 : ℂ) * Complex.I ^ 7
      + (1121350831498613471 / 8646911284551352320 : ℂ) * Complex.I ^ 8
      - (52721148796868052389 / 2473016627381686763520 : ℂ) * Complex.I ^ 9
      + (4455745651884317 / 1729382256910270464 : ℂ) * Complex.I ^ 10
      - (48601756067390561 / 224819693398335160320 : ℂ) * Complex.I ^ 11
      + (6491563697269 / 576460752303423488 : ℂ) * Complex.I ^ 12
      - (4747561509943 / 17293822569102704640 : ℂ) * Complex.I ^ 13) * Complex.I_sq

/-- BDF15: `bdfRhoSum 15` has a root of modulus `> 1` (numerically `≈ 2.3525`). -/
private theorem bdfRhoSum_exists_root_15 : ∃ ζ : ℂ, bdfRhoSum 15 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 8 : ℝ) : ℂ)
      + ((7 / 16 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_15, bdfRevSum_witness_15]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 16` at `w = -1/8 + 3/8 i`. -/
private theorem bdfRhoSum_witness_16 :
    bdfRhoSum 16 (((-1 / 8 : ℝ) : ℂ)
        + ((3 / 8 : ℝ) : ℂ) * Complex.I) = (((14183666647489035 / 17609778230460416 : ℝ) : ℝ) : ℂ)
        + (((5784224770515 / 7146825580544 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination (-(1526576985929673621 / 4508103226997866496 : ℂ)
      - (976742677713265857 / 281756451687366656 : ℂ) * Complex.I
      + (33636750358495842045 / 4508103226997866496 : ℂ) * Complex.I ^ 2
      - (91846778310537489 / 10836786603360256 : ℂ) * Complex.I ^ 3
      + (29608308164589534711 / 4508103226997866496 : ℂ) * Complex.I ^ 4
      - (409931262009521487 / 108367866033602560 : ℂ) * Complex.I ^ 5
      + (37970229861487630053 / 22540516134989332480 : ℂ) * Complex.I ^ 6
      - (16027673230567107 / 27091966508400640 : ℂ) * Complex.I ^ 7
      + (3726983040359431077 / 22540516134989332480 : ℂ) * Complex.I ^ 8
      - (3994226573146407 / 108367866033602560 : ℂ) * Complex.I ^ 9
      + (147452074886552211 / 22540516134989332480 : ℂ) * Complex.I ^ 10
      - (50034376354293 / 54183933016801280 : ℂ) * Complex.I ^ 11
      + (2349928603333809 / 22540516134989332480 : ℂ) * Complex.I ^ 12
      - (13077145835037 / 1408782258436833280 : ℂ) * Complex.I ^ 13
      + (11653986163671 / 22540516134989332480 : ℂ) * Complex.I ^ 14) * Complex.I_sq

/-- Witness value of `bdfRevSum 16` at `w = -1/8 + 3/8 i`. -/
private theorem bdfRevSum_witness_16 :
    bdfRevSum 16 (((-1 / 8 : ℝ) : ℂ)
        + ((3 / 8 : ℝ) : ℂ) * Complex.I) = (((-74202892475821587 / 88048891152302080 : ℝ) : ℝ) : ℂ)
        + (((1101950313453537 / 2751527848509440 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((1208877786933974307 / 157625986957967360 : ℂ)
      - (24160949920788103719 / 1408782258436833280 : ℂ) * Complex.I
      + (3132358724526487173 / 157625986957967360 : ℂ) * Complex.I ^ 2
      - (10948830686451168363 / 704391129218416640 : ℂ) * Complex.I ^ 3
      + (1414331160555142287 / 157625986957967360 : ℂ) * Complex.I ^ 4
      - (5608034682987858417 / 1408782258436833280 : ℂ) * Complex.I ^ 5
      + (218178592828758153 / 157625986957967360 : ℂ) * Complex.I ^ 6
      - (19122463600144731 / 50313652087029760 : ℂ) * Complex.I ^ 7
      + (12973619285494857 / 157625986957967360 : ℂ) * Complex.I ^ 8
      - (2802138316364511 / 201254608348119040 : ℂ) * Complex.I ^ 9
      + (56885279007555 / 31525197391593472 : ℂ) * Complex.I ^ 10
      - (1584548205687 / 9147936743096320 : ℂ) * Complex.I ^ 11
      + (366150625857 / 31525197391593472 : ℂ) * Complex.I ^ 12
      - (683964567 / 1407374883553280 : ℂ) * Complex.I ^ 13
      + (43046721 / 4503599627370496 : ℂ) * Complex.I ^ 14) * Complex.I_sq

/-- BDF16: `bdfRhoSum 16` has a root of modulus `> 1` (numerically `≈ 2.5222`). -/
private theorem bdfRhoSum_exists_root_16 : ∃ ζ : ℂ, bdfRhoSum 16 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 8 : ℝ) : ℂ)
      + ((3 / 8 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_16, bdfRevSum_witness_16]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 17` at `w = -1/8 + 3/8 i`. -/
private theorem bdfRhoSum_witness_17 :
    bdfRhoSum 17 (((-1 / 8 : ℝ) : ℂ)
        + ((3 / 8 : ℝ) : ℂ)
        * Complex.I) = (((-2723246982475835499 / 2394929839342616576 : ℝ) : ℝ) : ℂ)
        + (((-105802658781713979 / 184225372257124352 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination ((23192586877816840581 / 36064825815982931968 : ℂ)
      + (310951740195429172263 / 87586005553101406208 : ℂ) * Complex.I
      - (328664390224894852509 / 36064825815982931968 : ℂ) * Complex.I ^ 2
      + (7103177923303912522455 / 613102038871709843456 : ℂ) * Complex.I ^ 3
      - (357746428187883845415 / 36064825815982931968 : ℂ) * Complex.I ^ 4
      + (1756143283919624913627 / 278682744941686292480 : ℂ) * Complex.I ^ 5
      - (559877370866216984421 / 180324129079914659840 : ℂ) * Complex.I ^ 6
      + (338300939551122893421 / 278682744941686292480 : ℂ) * Complex.I ^ 7
      - (68702262124665421269 / 180324129079914659840 : ℂ) * Complex.I ^ 8
      + (26865564800002390269 / 278682744941686292480 : ℂ) * Complex.I ^ 9
      - (3543441885639280179 / 180324129079914659840 : ℂ) * Complex.I ^ 10
      + (9854894121271306137 / 3065510194358549217280 : ℂ) * Complex.I ^ 11
      - (75930673454015553 / 180324129079914659840 : ℂ) * Complex.I ^ 12
      + (136051051058622243 / 3065510194358549217280 : ℂ) * Complex.I ^ 13
      - (670381619004567 / 180324129079914659840 : ℂ) * Complex.I ^ 14
      + (604694838600261 / 3065510194358549217280 : ℂ) * Complex.I ^ 15) * Complex.I_sq

/-- Witness value of `bdfRevSum 17` at `w = -1/8 + 3/8 i`. -/
private theorem bdfRevSum_witness_17 :
    bdfRevSum 17 (((-1 / 8 : ℝ) : ℂ)
        + ((3 / 8 : ℝ) : ℂ)
        * Complex.I) = (((-164414279647388889 / 1496831149589135360 : ℝ) : ℝ) : ℂ)
        + (((879890471508390249 / 748415574794567680 : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((1162023676011974457 / 157625986957967360 : ℂ)
      - (3907402814012309995599 / 191594387147409326080 : ℂ) * Complex.I
      + (4216904141205517983 / 157625986957967360 : ℂ) * Complex.I ^ 2
      - (4458757958842375124721 / 191594387147409326080 : ℂ) * Complex.I ^ 3
      + (2347518838403671677 / 157625986957967360 : ℂ) * Complex.I ^ 4
      - (1407564004303840914747 / 191594387147409326080 : ℂ) * Complex.I ^ 5
      + (450792258485041323 / 157625986957967360 : ℂ) * Complex.I ^ 6
      - (24314523787347854499 / 27370626735344189440 : ℂ) * Complex.I ^ 7
      + (34800723044944587 / 157625986957967360 : ℂ) * Complex.I ^ 8
      - (1196461280481373611 / 27370626735344189440 : ℂ) * Complex.I ^ 9
      + (214855983397305 / 31525197391593472 : ℂ) * Complex.I ^ 10
      - (2038947755193279 / 2488238794122199040 : ℂ) * Complex.I ^ 11
      + (2313326003571 / 31525197391593472 : ℂ) * Complex.I ^ 12
      - (882711277857 / 191402984163246080 : ℂ) * Complex.I ^ 13
      + (817887699 / 4503599627370496 : ℂ) * Complex.I ^ 14
      - (129140163 / 38280596832649216 : ℂ) * Complex.I ^ 15) * Complex.I_sq

/-- BDF17: `bdfRhoSum 17` has a root of modulus `> 1` (numerically `≈ 2.6923`). -/
private theorem bdfRhoSum_exists_root_17 : ∃ ζ : ℂ, bdfRhoSum 17 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-1 / 8 : ℝ) : ℂ)
      + ((3 / 8 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_17, bdfRevSum_witness_17]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 18` at `w = -3/32 + 11/32 i`. -/
private theorem bdfRhoSum_witness_18 :
    bdfRhoSum 18 (((-3 / 32 : ℝ) : ℂ)
        + ((11 / 32 : ℝ) : ℂ)
        * Complex.I) =
        (((2466530508517867573964739024631 / 3703012321028786039875499458560 : ℝ) : ℝ) : ℂ)
        + (((926914961137286881003156481819 / 2693099869839117119909454151680 : ℝ) : ℝ) : ℂ)
        * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination (-(165223513953465019575315709635697 / 459622377785875988464546841886720 : ℂ)
      - (1503930956849845566513333528559949 / 689433566678813982696820262830080 : ℂ) * Complex.I
      + (320374502059601948689796689574159 / 57452797223234498558068355235840 : ℂ) * Complex.I ^ 2
      - (4929604587522492820643913645070891 / 689433566678813982696820262830080 : ℂ) * Complex.I ^ 3
      + (713962907427303357403552660043477 / 114905594446468997116136710471680 : ℂ) * Complex.I ^ 4
      - (2778255027378431038683135944137601 / 689433566678813982696820262830080 : ℂ) * Complex.I ^ 5
      + (23441044748788784603635143075169 / 11490559444646899711613671047168 : ℂ) * Complex.I ^ 6
      - (569162935822562014095863915365063 / 689433566678813982696820262830080 : ℂ) * Complex.I ^ 7
      + (62160062903113045273924112999077 / 229811188892937994232273420943360 : ℂ) * Complex.I ^ 8
      - (5528048499037686126403237275343 / 76603729630979331410757806981120 : ℂ) * Complex.I ^ 9
      + (901305035763840421172578897217 / 57452797223234498558068355235840 : ℂ) * Complex.I ^ 10
      - (30303902263024381210284875711 / 10943389947282761630108258140160 : ℂ) * Complex.I ^ 11
      + (45319587903474706385009386061 / 114905594446468997116136710471680 : ℂ) * Complex.I ^ 12
      - (493436059830061357931164309 / 10943389947282761630108258140160 : ℂ) * Complex.I ^ 13
      + (239060229977594841995518427 / 57452797223234498558068355235840 : ℂ) * Complex.I ^ 14
      - (23918690257628769616510629 / 76603729630979331410757806981120 : ℂ) * Complex.I ^ 15
      + (7214903024354497574679071 / 459622377785875988464546841886720 : ℂ) * Complex.I ^ 16)
      * Complex.I_sq

/-- Witness value of `bdfRevSum 18` at `w = -3/32 + 11/32 i`. -/
private theorem bdfRevSum_witness_18 :
    bdfRevSum 18 (((-3 / 32 : ℝ) : ℂ)
        + ((11 / 32 : ℝ) : ℂ)
        * Complex.I) =
        (((105822198314559023460367130557 / 462876540128598254984437432320 : ℝ) : ℝ) : ℂ)
        + (((34706958931633030394325044137 / 336637483729889639988681768960 : ℝ) : ℝ) : ℂ)
        * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((4620455849252028549513423463163 / 779902224749789573186448261120 : ℂ)
      - (1278514381818185774553703825861327 / 86179195834851747837102532853760 : ℂ) * Complex.I
      + (1862923697563760598584660943419 / 97487778093723696648306032640 : ℂ) * Complex.I ^ 2
      - (1435518602192924359633390785709913 / 86179195834851747837102532853760 : ℂ) * Complex.I ^ 3
      + (2106764770482262258298249552057 / 194975556187447393296612065280 : ℂ) * Complex.I ^ 4
      - (470104571733972383064258677318923 / 86179195834851747837102532853760 : ℂ) * Complex.I ^ 5
      + (213942637321796005097958071369 / 97487778093723696648306032640 : ℂ) * Complex.I ^ 6
      - (8768590887005886906255723286091 / 12311313690693106833871790407680 : ℂ) * Complex.I ^ 7
      + (73065340791454980268300567369 / 389951112374894786593224130560 : ℂ) * Complex.I ^ 8
      - (54592042019634225066528298291 / 1367923743410345203763532267520 : ℂ) * Complex.I ^ 9
      + (133265758855329928295099665 / 19497555618744739329661206528 : ℂ) * Complex.I ^ 10
      - (1270426716655008051499898549 / 1367923743410345203763532267520 : ℂ) * Complex.I ^ 11
      + (3818472091167887013638173 / 38995111237489478659322413056 : ℂ) * Complex.I ^ 12
      - (813395505461102209046467 / 105224903339257323366425559040 : ℂ) * Complex.I ^ 13
      + (1198231105652371242397 / 2785365088392105618523029504 : ℂ) * Complex.I ^ 14
      - (316915286869057194417 / 21044980667851464673285111808 : ℂ) * Complex.I ^ 15
      + (5559917313492231481 / 22282920707136844948184236032 : ℂ) * Complex.I ^ 16) * Complex.I_sq

/-- BDF18: `bdfRhoSum 18` has a root of modulus `> 1` (numerically `≈ 2.8628`). -/
private theorem bdfRhoSum_exists_root_18 : ∃ ζ : ℂ, bdfRhoSum 18 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-3 / 32 : ℝ) : ℂ)
      + ((11 / 32 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_18, bdfRevSum_witness_18]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 19` at `w = -3/32 + 5/16 i`. -/
private theorem bdfRhoSum_witness_19 :
    bdfRhoSum 19 (((-3 / 32 : ℝ) : ℂ)
        + ((5 / 16 : ℝ) : ℂ)
        * Complex.I) =
        (((-981851302461656048219801924429682455 / 1844372677579163166510533567123030016 : ℝ) : ℝ) :
        ℂ) + (((-2209268068967408935249545228672455 / 4931477747537869429172549644713984 : ℝ) : ℝ) :
        ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination ((5211407611237216395991316335712525 / 24268061547094252190928073251618816 : ℂ)
      + (174331295231022724019126888625602375 / 76848861565798465271272231963459584 : ℂ) * Complex.I
      - (713308390097237092840697545984375 / 137886713335762796539364052566016 : ℂ) * Complex.I ^ 2
      + (30088947145169487010698527707230625 / 4803053847862404079454514497716224 : ℂ)
      * Complex.I ^ 3
      - (1984591730405197363076213202840625 / 379188461673347690483251144556544 : ℂ) * Complex.I ^ 4
      + (304614609580933940634869180890625 / 92366420151200078451048355725312 : ℂ) * Complex.I ^ 5
      - (310137269586538510086474322421875 / 189594230836673845241625572278272 : ℂ) * Complex.I ^ 6
      + (30196430633626114201680848046875 / 46183210075600039225524177862656 : ℂ) * Complex.I ^ 7
      - (10114787318275943898565830078125 / 47398557709168461310406393069568 : ℂ) * Complex.I ^ 8
      + (661050702328373336643798828125 / 11545802518900009806381044465664 : ℂ) * Complex.I ^ 9
      - (1189980480038927725341796875 / 94044757359461232758742843392 : ℂ) * Complex.I ^ 10
      + (301658196641748236083984375 / 131202301351136475072511868928 : ℂ) * Complex.I ^ 11
      - (28119281290899114990234375 / 82289162689528578663899987968 : ℂ) * Complex.I ^ 12
      + (96690779252710833740234375 / 2345241136651564491921149657088 : ℂ) * Complex.I ^ 13
      - (660498461040069580078125 / 164578325379057157327799975936 : ℂ) * Complex.I ^ 14
      + (1485847549810943603515625 / 4690482273303128983842299314176 : ℂ) * Complex.I ^ 15
      - (841524260711669921875 / 41144581344764289331949993984 : ℂ) * Complex.I ^ 16
      + (1050170131683349609375 / 1172620568325782245960574828544 : ℂ) * Complex.I ^ 17)
      * Complex.I_sq

/-- Witness value of `bdfRevSum 19` at `w = -3/32 + 5/16 i`. -/
private theorem bdfRevSum_witness_19 :
    bdfRevSum 19 (((-3 / 32 : ℝ) : ℂ)
        + ((5 / 16 : ℝ) : ℂ)
        * Complex.I) =
        (((-8332151237985338528573610848226745 / 115273292348697697906908347945189376 : ℝ) : ℝ) : ℂ)
        + (((-5272616134738062829138425272050915 / 57636646174348848953454173972594688 : ℝ) : ℝ) :
        ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((4064329932824827162176464115325 / 623921779799831658549158608896 : ℂ)
      - (214260596753829571363174788194571125 / 14409161543587212238363543493148672 : ℂ) * Complex.I
      + (709988694265074174020588361875 / 38995111237489478659322413056 : ℂ) * Complex.I ^ 2
      - (13796568675929070224206467701291875 / 900572596474200764897721468321792 : ℂ)
      * Complex.I ^ 3
      + (94426791313113445269535609375 / 9748777809372369664830603264 : ℂ) * Complex.I ^ 4
      - (1081914260653330877748594020234375 / 225143149118550191224430367080448 : ℂ) * Complex.I ^ 5
      + (9337011272667711127823828125 / 4874388904686184832415301632 : ℂ) * Complex.I ^ 6
      - (9995547809786368082959185546875 / 16081653508467870801745026220032 : ℂ) * Complex.I ^ 7
      + (201310344934240407576171875 / 1218597226171546208103825408 : ℂ) * Complex.I ^ 8
      - (16082535540648302377783203125 / 446712597457440855604028506112 : ℂ) * Complex.I ^ 9
      + (976385469159658935546875 / 152324653271443276012978176 : ℂ) * Complex.I ^ 10
      - (4692315160980277099609375 / 5076279516561827904591233024 : ℂ) * Complex.I ^ 11
      + (2025836871051025390625 / 19040581658930409501622272 : ℂ) * Complex.I ^ 12
      - (466191304180908203125 / 48810379966940652928761856 : ℂ) * Complex.I ^ 13
      + (3507433624267578125 / 5440166188265831286177792 : ℂ) * Complex.I ^ 14
      - (3006432342529296875 / 97620759933881305857523712 : ℂ) * Complex.I ^ 15
      + (1262664794921875 / 1360041547066457821544448 : ℂ) * Complex.I ^ 16
      - (19073486328125 / 1435599410792372144963584 : ℂ) * Complex.I ^ 17) * Complex.I_sq

/-- BDF19: `bdfRhoSum 19` has a root of modulus `> 1` (numerically `≈ 3.0335`). -/
private theorem bdfRhoSum_exists_root_19 : ∃ ζ : ℂ, bdfRhoSum 19 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-3 / 32 : ℝ) : ℂ)
      + ((5 / 16 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_19, bdfRevSum_witness_19]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-- Witness value of `bdfRhoSum 20` at `w = -3/32 + 5/16 i`. -/
private theorem bdfRhoSum_witness_20 :
    bdfRhoSum 20 (((-3 / 32 : ℝ) : ℂ)
        + ((5 / 16 : ℝ) : ℂ)
        * Complex.I) =
        (((40469947973305223356964979708797466565 / 59019925682533221328337074147936960512 : ℝ) : ℝ)
        : ℂ) + (((2272475092469792994651427343057646245 / 7377490710316652666042134268492120064 : ℝ)
        : ℝ) : ℂ) * Complex.I := by
  simp [bdfRhoSum, Finset.sum_range_succ]
  linear_combination
      (-(2624756345324732294757911125792492175 / 7377490710316652666042134268492120064 : ℂ)
      - (4229270798165120761957653967879745375 / 1844372677579163166510533567123030016 : ℂ)
      * Complex.I
      + (2477545371789384040574796288661670625 / 409860595017591814780118570471784448 : ℂ)
      * Complex.I ^ 2
      - (926444800047832935825899355799999375 / 115273292348697697906908347945189376 : ℂ)
      * Complex.I ^ 3
      + (1795117212234617564940349139671875 / 246310453736533542536128948600832 : ℂ) * Complex.I ^ 4
      - (143276831289438731327654767381953125 / 28818323087174424476727086986297344 : ℂ)
      * Complex.I ^ 5
      + (34234201750961235623253370695703125 / 12808143594299744211878705327243264 : ℂ)
      * Complex.I ^ 6
      - (16740975644544217620220874298828125 / 14409161543587212238363543493148672 : ℂ)
      * Complex.I ^ 7
      + (94790611742779429698500837890625 / 228716849898209718069262595129344 : ℂ) * Complex.I ^ 8
      - (440681059932897748378077197265625 / 3602290385896803059590885873287168 : ℂ) * Complex.I ^ 9
      + (72019163606687246309562255859375 / 2401526923931202039727257248858112 : ℂ) * Complex.I ^ 10
      - (305446520653053104017333984375 / 50031810915233375827651192684544 : ℂ) * Complex.I ^ 11
      + (44115548187366207647705078125 / 42884409355914322137986736586752 : ℂ) * Complex.I ^ 12
      - (111458701969328057861328125 / 781747045550521497307049885696 : ℂ) * Complex.I ^ 13
      + (4838684386205699920654296875 / 300190865491400254965907156107264 : ℂ) * Complex.I ^ 14
      - (2638032409931182861328125 / 1786850389829763422416114024448 : ℂ) * Complex.I ^ 15
      + (590129149951934814453125 / 5360551169489290267248342073344 : ℂ) * Complex.I ^ 16
      - (21112109279632568359375 / 3126988182202085989228199542784 : ℂ) * Complex.I ^ 17
      + (5324853420257568359375 / 18761929093212515935369197256704 : ℂ) * Complex.I ^ 18)
      * Complex.I_sq

/-- Witness value of `bdfRevSum 20` at `w = -3/32 + 5/16 i`. -/
private theorem bdfRevSum_witness_20 :
    bdfRevSum 20 (((-3 / 32 : ℝ) : ℂ)
        + ((5 / 16 : ℝ) : ℂ)
        * Complex.I) =
        (((6248917513533413116960646506495336015 / 14754981420633305332084268536984240128 : ℝ) : ℝ)
        : ℂ) + (((628761127156927977406928148862730095 / 1844372677579163166510533567123030016 : ℝ)
        : ℝ) : ℂ) * Complex.I := by
  simp [bdfRevSum, Finset.sum_range_succ]
  linear_combination ((252304658155906997060781740490175 / 39930993907189226147146150969344 : ℂ)
      - (7846538174788097164201446280087604125 / 461093169394790791627633391780757504 : ℂ)
      * Complex.I
      + (460366067291270234541015606514375 / 19965496953594613073573075484672 : ℂ) * Complex.I ^ 2
      - (609588410644304847061405825083918125 / 28818323087174424476727086986297344 : ℂ)
      * Complex.I ^ 3
      + (2265725507959957126418282640625 / 155980444949957914637289652224 : ℂ) * Complex.I ^ 4
      - (56429456431424832135711203715859375 / 7204580771793606119181771746574336 : ℂ)
      * Complex.I ^ 5
      + (2124093978308458887612182421875 / 623921779799831658549158608896 : ℂ) * Complex.I ^ 6
      - (623142169049962498842834806640625 / 514612912270971865655840839041024 : ℂ) * Complex.I ^ 7
      + (27710904848127296881994140625 / 77990222474978957318644826112 : ℂ) * Complex.I ^ 8
      - (1233367836033837583590283203125 / 14294803118638107379328912195584 : ℂ) * Complex.I ^ 9
      + (675414010564448340576171875 / 38995111237489478659322413056 : ℂ) * Complex.I ^ 10
      - (464530660854741822509765625 / 162440944529978492946919456768 : ℂ) * Complex.I ^ 11
      + (1874560987856097412109375 / 4874388904686184832415301632 : ℂ) * Complex.I ^ 12
      - (8098031646624755859375 / 195241519867762611715047424 : ℂ) * Complex.I ^ 13
      + (2439471771392822265625 / 696341272098026404630757376 : ℂ) * Complex.I ^ 14
      - (697586087799072265625 / 3123864317884201787440758784 : ℂ) * Complex.I ^ 15
      + (879550933837890625 / 87042659012253300578844672 : ℂ) * Complex.I ^ 16
      - (13294219970703125 / 45939181145355908638834688 : ℂ) * Complex.I ^ 17
      + (19073486328125 / 4835703278458516698824704 : ℂ) * Complex.I ^ 18) * Complex.I_sq

/-- BDF20: `bdfRhoSum 20` has a root of modulus `> 1` (numerically `≈ 3.2045`). -/
private theorem bdfRhoSum_exists_root_20 : ∃ ζ : ℂ, bdfRhoSum 20 ζ = 0 ∧ 1 < ‖ζ‖ := by
  refine bdfRhoSum_exists_root_norm_gt_one_of_lt (by norm_num) (w := (((-3 / 32 : ℝ) : ℂ)
      + ((5 / 16 : ℝ) : ℂ) * Complex.I))
    (ofReal_add_mul_I_ne_zero (by norm_num)) (norm_ofReal_add_mul_I_le_one (by norm_num)) ?_
  rw [bdfRhoSum_witness_20, bdfRevSum_witness_20]
  exact norm_ofReal_add_mul_I_lt (by norm_num)

/-! ## BDF`k` is not zero-stable for `7 ≤ k ≤ 20` -/

/-- **BDF`k` is zero-unstable for `7 ≤ k ≤ 20`**: the backward-difference polynomial
`bdfRhoSum k` has a root outside the closed unit disk. -/
@[powerlib_foundation] theorem bdfRhoSum_exists_root_norm_gt_one {k : ℕ} (hk : 7 ≤ k)
    (hk' : k ≤ 20) : ∃ ζ : ℂ, bdfRhoSum k ζ = 0 ∧ 1 < ‖ζ‖ := by
  interval_cases k
  · exact bdfRhoSum_exists_root_7
  · exact bdfRhoSum_exists_root_8
  · exact bdfRhoSum_exists_root_9
  · exact bdfRhoSum_exists_root_10
  · exact bdfRhoSum_exists_root_11
  · exact bdfRhoSum_exists_root_12
  · exact bdfRhoSum_exists_root_13
  · exact bdfRhoSum_exists_root_14
  · exact bdfRhoSum_exists_root_15
  · exact bdfRhoSum_exists_root_16
  · exact bdfRhoSum_exists_root_17
  · exact bdfRhoSum_exists_root_18
  · exact bdfRhoSum_exists_root_19
  · exact bdfRhoSum_exists_root_20

@[powerlib_foundation] theorem bdfLMM_exists_root_norm_gt_one {k : ℕ} (hk : 7 ≤ k)
    (hk' : k ≤ 20) : ∃ ζ : ℂ, (bdfLMM k).rho ζ = 0 ∧ 1 < ‖ζ‖ := by
  obtain ⟨ζ, h, h1⟩ := bdfRhoSum_exists_root_norm_gt_one hk hk'
  exact ⟨ζ, by rw [bdfLMM_rho_eq, h, mul_zero], h1⟩

/-- The `k`-step BDF violates the root condition (is not zero-stable) for `7 ≤ k ≤ 20`. -/
@[powerlib_foundation] theorem bdfLMM_not_rootCondition {k : ℕ} (hk : 7 ≤ k) (hk' : k ≤ 20) :
    ¬ (bdfLMM k).RootCondition := by
  obtain ⟨ζ, hζ, h1⟩ := bdfLMM_exists_root_norm_gt_one hk hk'
  exact (bdfLMM k).not_rootCondition_of_root hζ h1

/-! ## The coefficient tables BDF7–BDF9 -/

/-! ### BDF7 -/

/-- BDF7 (`β_j = 0` for `j < 7`, `β_7 = 140/363`). -/
def bdf7 : LMM 7 :=
  bdf 7 ![-20/363, 490/1089, -196/121, 1225/363, -4900/1089, 490/121, -980/363, 1] (140/363)

@[powerlib_foundation] theorem bdf7_exactOrder : bdf7.HasExactOrder 7 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf7, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf7, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf7_consistent : bdf7.Consistent := by
  rw [LMM.consistent_iff_hasOrder_one]
  exact fun q hq => bdf7_exactOrder.1 q (by omega)

/-- The BDF7 first characteristic polynomial is `β_7 · bdfRhoSum 7`. -/
@[powerlib_foundation] theorem bdf7_rho_eq_sum (ζ : ℂ) :
    bdf7.rho ζ = ((140 / 363) : ℂ) * bdfRhoSum 7 ζ := by
  simp [LMM.rho, bdf7, bdf, Fin.sum_univ_succ, bdfRhoSum, Finset.sum_range_succ]
  ring

/-- The table `bdf7` has the same first characteristic polynomial as `bdfLMM 7`. -/
@[powerlib_foundation] theorem bdf7_rho_eq_bdfLMM (ζ : ℂ) : bdf7.rho ζ = (bdfLMM 7).rho ζ := by
  rw [bdf7_rho_eq_sum, bdfLMM_rho_eq]
  congr 1
  norm_num [bdfHarmonic, Finset.sum_range_succ]

/-- **BDF7 is not zero-stable**: `ρ_7` has a root `ζ` with `1 < ‖ζ‖`. -/
@[powerlib_foundation] theorem bdf7_exists_root_norm_gt_one :
    ∃ ζ : ℂ, bdf7.rho ζ = 0 ∧ 1 < ‖ζ‖ := by
  obtain ⟨ζ, h, h1⟩ := bdfRhoSum_exists_root_7
  exact ⟨ζ, by rw [bdf7_rho_eq_sum, h, mul_zero], h1⟩

/-- BDF7 violates the root condition (it is not zero-stable). -/
@[powerlib_foundation] theorem bdf7_not_rootCondition : ¬ bdf7.RootCondition := by
  obtain ⟨ζ, hζ, h1⟩ := bdf7_exists_root_norm_gt_one
  exact bdf7.not_rootCondition_of_root hζ h1

/-! ### BDF8 -/

/-- BDF8 (`β_j = 0` for `j < 8`, `β_8 = 280/761`). -/
def bdf8 : LMM 8 :=
  bdf 8 ![35/761, -320/761, 3920/2283, -3136/761, 4900/761, -15680/2283, 3920/761, -2240/761,
      1] (280/761)

@[powerlib_foundation] theorem bdf8_exactOrder : bdf8.HasExactOrder 8 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf8, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf8, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf8_consistent : bdf8.Consistent := by
  rw [LMM.consistent_iff_hasOrder_one]
  exact fun q hq => bdf8_exactOrder.1 q (by omega)

/-- The BDF8 first characteristic polynomial is `β_8 · bdfRhoSum 8`. -/
@[powerlib_foundation] theorem bdf8_rho_eq_sum (ζ : ℂ) :
    bdf8.rho ζ = ((280 / 761) : ℂ) * bdfRhoSum 8 ζ := by
  simp [LMM.rho, bdf8, bdf, Fin.sum_univ_succ, bdfRhoSum, Finset.sum_range_succ]
  ring

/-- The table `bdf8` has the same first characteristic polynomial as `bdfLMM 8`. -/
@[powerlib_foundation] theorem bdf8_rho_eq_bdfLMM (ζ : ℂ) : bdf8.rho ζ = (bdfLMM 8).rho ζ := by
  rw [bdf8_rho_eq_sum, bdfLMM_rho_eq]
  congr 1
  norm_num [bdfHarmonic, Finset.sum_range_succ]

/-- **BDF8 is not zero-stable**: `ρ_8` has a root `ζ` with `1 < ‖ζ‖`. -/
@[powerlib_foundation] theorem bdf8_exists_root_norm_gt_one :
    ∃ ζ : ℂ, bdf8.rho ζ = 0 ∧ 1 < ‖ζ‖ := by
  obtain ⟨ζ, h, h1⟩ := bdfRhoSum_exists_root_8
  exact ⟨ζ, by rw [bdf8_rho_eq_sum, h, mul_zero], h1⟩

/-- BDF8 violates the root condition (it is not zero-stable). -/
@[powerlib_foundation] theorem bdf8_not_rootCondition : ¬ bdf8.RootCondition := by
  obtain ⟨ζ, hζ, h1⟩ := bdf8_exists_root_norm_gt_one
  exact bdf8.not_rootCondition_of_root hζ h1

/-! ### BDF9 -/

/-- BDF9 (`β_j = 0` for `j < 9`, `β_9 = 2520/7129`). -/
def bdf9 : LMM 9 :=
  bdf 9 ![-280/7129, 2835/7129, -12960/7129, 35280/7129, -63504/7129, 79380/7129, -70560/7129,
      45360/7129, -22680/7129, 1] (2520/7129)

@[powerlib_foundation] theorem bdf9_exactOrder : bdf9.HasExactOrder 9 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · interval_cases q <;> simp [LMM.C, bdf9, bdf, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.C, bdf9, bdf, Fin.sum_univ_succ]; norm_num

@[powerlib_foundation] theorem bdf9_consistent : bdf9.Consistent := by
  rw [LMM.consistent_iff_hasOrder_one]
  exact fun q hq => bdf9_exactOrder.1 q (by omega)

/-- The BDF9 first characteristic polynomial is `β_9 · bdfRhoSum 9`. -/
@[powerlib_foundation] theorem bdf9_rho_eq_sum (ζ : ℂ) :
    bdf9.rho ζ = ((2520 / 7129) : ℂ) * bdfRhoSum 9 ζ := by
  simp [LMM.rho, bdf9, bdf, Fin.sum_univ_succ, bdfRhoSum, Finset.sum_range_succ]
  ring

/-- The table `bdf9` has the same first characteristic polynomial as `bdfLMM 9`. -/
@[powerlib_foundation] theorem bdf9_rho_eq_bdfLMM (ζ : ℂ) : bdf9.rho ζ = (bdfLMM 9).rho ζ := by
  rw [bdf9_rho_eq_sum, bdfLMM_rho_eq]
  congr 1
  norm_num [bdfHarmonic, Finset.sum_range_succ]

/-- **BDF9 is not zero-stable**: `ρ_9` has a root `ζ` with `1 < ‖ζ‖`. -/
@[powerlib_foundation] theorem bdf9_exists_root_norm_gt_one :
    ∃ ζ : ℂ, bdf9.rho ζ = 0 ∧ 1 < ‖ζ‖ := by
  obtain ⟨ζ, h, h1⟩ := bdfRhoSum_exists_root_9
  exact ⟨ζ, by rw [bdf9_rho_eq_sum, h, mul_zero], h1⟩

/-- BDF9 violates the root condition (it is not zero-stable). -/
@[powerlib_foundation] theorem bdf9_not_rootCondition : ¬ bdf9.RootCondition := by
  obtain ⟨ζ, hζ, h1⟩ := bdf9_exists_root_norm_gt_one
  exact bdf9.not_rootCondition_of_root hζ h1

end powerlib.Numerics
