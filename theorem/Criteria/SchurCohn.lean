import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Schur–Cohn root bounds for complex polynomials (foundation)

Static algebra of an arbitrary complex polynomial `p : ℂ[X]` and its roots; nothing here
describes a physical system or a numerical method.

* `norm_sub_le_norm_one_sub_conj_mul`: Blaschke-factor bound `‖w - ζ‖ ≤ ‖1 - w̄ ζ‖` in the
  closed unit disk, from `‖1 - w̄ ζ‖² - ‖w - ζ‖² = (1 - ‖w‖²)(1 - ‖ζ‖²)`;
  `norm_prod_sub_le` is its multiset product form.
* `norm_eval_le_of_roots_norm_le_one` (Schur–Cohn necessary condition): if all roots of
  `p : ℂ[X]` lie in the closed unit disk, then `‖p(w)‖ ≤ ‖w‖ⁿ ‖p(1/w̄)‖` for `0 < ‖w‖ ≤ 1`.
* `norm_coeff_sq_sub_le_of_roots_norm_le_one` (second power-sum bound): if all roots of
  `p = Σ cᵢ Xⁱ : ℂ[X]` of degree `n ≥ 2` lie in the closed unit disk, then
  `‖c_{n-1}² - 2 c_{n-2} c_n‖ ≤ n ‖c_n‖²` (the left side is `‖c_n‖² ‖Σ ζᵢ²‖` by Vieta);
  contrapositive `exists_root_norm_gt_one_of_coeff`. Multiset helpers
  `multiset_esymm_cons_succ`, `multiset_esymm_one`, `multiset_sum_sq`
  (`(Σ x)² = Σ x² + 2 e₂`).

Used by the zero-instability proof of BDF`k`, `k ≥ 7` (`theorem/Numerics/BDFInstability.lean`).

Source: standard Schur–Cohn / Vieta root bounds; used for work-sync
theory/T-numerical-integration.md §1.5–§1.6.
-/

noncomputable section
namespace powerlib.Criteria
open Finset Polynomial ComplexConjugate

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

/-! ## Second power sum of the roots -/

/-- Recursion of the elementary symmetric functions of a multiset:
`e_{n+1}(a :: s) = e_{n+1}(s) + a e_n(s)`. -/
@[powerlib_foundation] theorem multiset_esymm_cons_succ {R : Type*} [CommSemiring R]
    (s : Multiset R) (a : R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

/-- `e₁(s) = Σ s`. -/
@[powerlib_foundation] theorem multiset_esymm_one {R : Type*} [CommSemiring R]
    (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

/-- Newton's identity for the second power sum: `(Σ x)² = Σ x² + 2 e₂`. -/
@[powerlib_foundation] theorem multiset_sum_sq {R : Type*} [CommRing R] (s : Multiset R) :
    s.sum ^ 2 = (s.map fun x => x ^ 2).sum + 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.esymm_of_card_lt (by simp)]; simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, multiset_esymm_cons_succ,
      multiset_esymm_one]
    linear_combination ih

/-- **Second power-sum bound.** If every root of `p : ℂ[X]` (degree `n ≥ 2`) lies in the closed
unit disk, then `‖c_{n-1}² - 2 c_{n-2} c_n‖ ≤ n ‖c_n‖²`: by Vieta the left side is
`‖c_n‖² ‖Σ ζᵢ²‖ ≤ ‖c_n‖² Σ ‖ζᵢ‖²`. -/
@[powerlib_foundation] theorem norm_coeff_sq_sub_le_of_roots_norm_le_one (p : ℂ[X])
    (hn : 2 ≤ p.natDegree) (hroots : ∀ ζ ∈ p.roots, ‖ζ‖ ≤ 1) :
    ‖p.coeff (p.natDegree - 1) ^ 2 - 2 * p.coeff (p.natDegree - 2) * p.leadingCoeff‖ ≤
      p.natDegree * ‖p.leadingCoeff‖ ^ 2 := by
  have hcard := IsAlgClosed.card_roots_eq_natDegree (p := p)
  have h1 := coeff_eq_esymm_roots_of_card hcard (k := p.natDegree - 1) (by omega)
  have h2 := coeff_eq_esymm_roots_of_card hcard (k := p.natDegree - 2) (by omega)
  rw [show p.natDegree - (p.natDegree - 1) = 1 by omega, multiset_esymm_one] at h1
  rw [show p.natDegree - (p.natDegree - 2) = 2 by omega] at h2
  have key : p.coeff (p.natDegree - 1) ^ 2 - 2 * p.coeff (p.natDegree - 2) * p.leadingCoeff
      = p.leadingCoeff ^ 2 * (p.roots.map fun x => x ^ 2).sum := by
    rw [h1, h2]
    linear_combination (p.leadingCoeff ^ 2) * multiset_sum_sq p.roots
  rw [key, norm_mul, norm_pow, mul_comm]
  gcongr
  calc ‖(p.roots.map fun x => x ^ 2).sum‖
      ≤ ((p.roots.map fun x => x ^ 2).map fun x => ‖x‖).sum := norm_multiset_sum_le _
    _ ≤ Multiset.card ((p.roots.map fun x => x ^ 2).map fun x => ‖x‖) • (1 : ℝ) := by
        refine Multiset.sum_le_card_nsmul _ _ fun x hx => ?_
        simp only [Multiset.map_map, Function.comp_apply, Multiset.mem_map] at hx
        obtain ⟨ζ, hζ, rfl⟩ := hx
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hroots ζ hζ)
    _ = p.natDegree := by simp [hcard]

/-- **A root outside the unit disk from three coefficients.** If `n ≥ 2` and
`n ‖c_n‖² < ‖c_{n-1}² - 2 c_{n-2} c_n‖`, then `p` has a root `ζ` with `1 < ‖ζ‖`. -/
@[powerlib_foundation] theorem exists_root_norm_gt_one_of_coeff (p : ℂ[X])
    (hn : 2 ≤ p.natDegree)
    (hlt : p.natDegree * ‖p.leadingCoeff‖ ^ 2 <
      ‖p.coeff (p.natDegree - 1) ^ 2 - 2 * p.coeff (p.natDegree - 2) * p.leadingCoeff‖) :
    ∃ ζ, p.IsRoot ζ ∧ 1 < ‖ζ‖ := by
  have hP : p ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hn; omega
  by_contra hne
  simp only [not_exists, not_and, not_lt] at hne
  have hr : ∀ ζ ∈ p.roots, ‖ζ‖ ≤ 1 := fun ζ hζ => hne ζ ((mem_roots hP).mp hζ)
  exact absurd (norm_coeff_sq_sub_le_of_roots_norm_le_one p hn hr) (not_le.mpr hlt)

end powerlib.Criteria
