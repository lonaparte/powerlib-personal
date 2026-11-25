import theorem.SpecialFunctions.PolynomialSigns

/-! # Derivative signs of a real polynomial at two positive roots (foundation)

Scope.
* A real polynomial `p` with `p(0) > 0` and at most two positive roots counted with multiplicity
  (the situation of a quartic whose coefficient signs allow at most two sign changes,
  `SpecialFunctions.countP_pos_roots_le_two_of_quartic`). Nothing here describes a physical
  system; the statement is a generic fact about real polynomials, a foundation result. Model
  modules use it to decide which of two equilibria, located as positive roots, is a saddle
  (`theorem/GridTiedConverter/GFM/QVDroopStability.lean`).

Source: factor theorem (Mathlib `Polynomial.mul_divByMonic_eq_iff_isRoot`, `Polynomial.roots_mul`)
and the intermediate value theorem (Mathlib `intermediate_value_Icc'`).

Results.
* `derivative_eval_neg_pos_of_two_roots`: if `p(0) > 0`, `p` has at most two positive roots
  counted with multiplicity and vanishes at `0 < a < b`, then `p'(a) < 0 < p'(b)`:
  `p = (X − a)(X − b) g` with `g` free of positive roots and `g(0) = p(0)/(ab) > 0`, so `g > 0` on
  `[0, ∞)`, `p'(a) = (a − b) g(a)` and `p'(b) = (b − a) g(b)`.
-/

noncomputable section
namespace powerlib.Criteria
open Polynomial

/-- **Derivative signs at two positive roots.** A real polynomial with `p(0) > 0` and at most two
positive roots counted with multiplicity, vanishing at `0 < a < b`, has `p'(a) < 0 < p'(b)`:
`p = (X − a)(X − b) g` with `g > 0` on `[0, ∞)` (`g(0) = p(0)/(ab) > 0` and `g` has no positive
root), so `p'(a) = (a − b) g(a)` and `p'(b) = (b − a) g(b)`. -/
@[tmio T, powerlib_foundation] theorem derivative_eval_neg_pos_of_two_roots {p : ℝ[X]}
    (hp0 : 0 < p.eval 0) (hcount : p.roots.countP (0 < ·) ≤ 2) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (hra : p.IsRoot a) (hrb : p.IsRoot b) :
    (derivative p).eval a < 0 ∧ 0 < (derivative p).eval b := by
  classical
  have hp : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact lt_irrefl 0 hp0
  set p₁ := p /ₘ (X - C a) with hp₁
  have hf₁ : (X - C a) * p₁ = p := mul_divByMonic_eq_iff_isRoot.mpr hra
  have hr₁ : p₁.IsRoot b := by
    have h := hrb
    rw [← hf₁, IsRoot.def, eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hab.ne')
  set g := p₁ /ₘ (X - C b) with hg
  have hf₂ : (X - C b) * g = p₁ := mul_divByMonic_eq_iff_isRoot.mpr hr₁
  have hfac : p = (X - C a) * ((X - C b) * g) := by rw [hf₂, hf₁]
  have hne : (X - C a) * ((X - C b) * g) ≠ 0 := hfac ▸ hp
  have hg0 : g ≠ 0 := fun h => hne (by rw [h, mul_zero, mul_zero])
  have hroots : p.roots = {a} + ({b} + g.roots) := by
    rw [hfac, roots_mul hne, roots_mul (right_ne_zero_of_mul hne), roots_X_sub_C,
      roots_X_sub_C]
  have hcg : g.roots.countP (0 < ·) = 0 := by
    simp only [hroots, Multiset.singleton_add, Multiset.countP_cons, ha, ha.trans hab,
      ite_true] at hcount
    omega
  have hgpos : ∀ x, 0 ≤ x → 0 < g.eval x := by
    have hg00 : 0 < g.eval 0 := by
      have h := hp0
      rw [hfac] at h
      simp only [eval_mul, eval_sub, eval_X, eval_C, zero_sub] at h
      have hab0 : 0 < (-a) * (-b) := by nlinarith
      exact pos_of_mul_pos_right (by linarith [h]) hab0.le
    intro x hx
    by_contra hle
    push Not at hle
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hx (g.continuous.continuousOn)
      ⟨hle, hg00.le⟩
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 fun h => by rw [← h] at hr0; linarith
    have hmem : r ∈ g.roots := (mem_roots hg0).mpr hr0
    rw [Multiset.countP_eq_zero] at hcg
    exact hcg r hmem hrpos
  have hda : (derivative p).eval a = (a - b) * g.eval a := by
    rw [hfac]
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, one_mul, sub_self, zero_mul, add_zero]
  have hdb : (derivative p).eval b = (b - a) * g.eval b := by
    rw [hfac]
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, one_mul, sub_self, zero_mul, add_zero]
    ring
  rw [hda, hdb]
  exact ⟨mul_neg_of_neg_of_pos (by linarith) (hgpos a ha.le),
    mul_pos (by linarith) (hgpos b (ha.trans hab).le)⟩

end powerlib.Criteria
