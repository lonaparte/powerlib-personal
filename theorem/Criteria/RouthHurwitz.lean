import theorem.Criteria.Hurwitz

/-! # The Routh reduction step in every degree (foundation)

The Routh reduction step for real polynomials of any degree, and its complex form (Bilharz):
a polynomial with positive leading coefficient is Hurwitz iff its next coefficient is positive and
the Routh-reduced polynomial (one degree lower) is Hurwitz. No continuity of roots, no argument
principle: the proof is one inequality between the polynomial and its para-conjugate on the closed
right half plane, read from the factorization over `ℂ`.

Scope.
* Static algebra of one polynomial `f : ℂ[X]` (complex form) or `p : ℝ[X]` (real form, its
  complex roots read through `aeval s p`). "Hurwitz" means every complex root has negative real
  part. No model family is defined; the criteria hold for every degree `n ≥ 1` and positive
  leading coefficient.

Source: E. J. Routh, *A Treatise on the Stability of a Given State of Motion* (1877); A. Hurwitz,
*Math. Ann.* 46 (1895); H. Bilharz, *Z. Angew. Math. Mech.* 24 (1944) (complex coefficients);
F. R. Gantmacher, *The Theory of Matrices*, vol. 2, Ch. XV; the reduction step in the form
`p = q + μ s G` of G. Meinsma, *Syst. Control Lett.* 25 (1995) 237–242. The two inequalities
below replace Meinsma's continuity argument; the second is the Julia–Carathéodory inequality
(angular derivative at infinity) for the finite Blaschke product `f^♯/f`, proved by induction
over the roots with one Cauchy–Schwarz step (shared criteria interface for the work-sync
formalization, `theory/T-small-signal-stability.md` §1.6).

Results.
* Two inequalities for `f(s) = c ∏ (s − zᵢ)` with `Re zᵢ ≤ 0`, at `Re s ≥ 0`, with the
  para-conjugate value `f^♯(s) = (−1)ⁿ conj f(−s̄) = c̄ ∏ (s + z̄ᵢ)`
  (`neg_one_pow_mul_conj_eval`):
  `‖f(−s̄)‖ ≤ ‖f(s)‖` (`norm_eval_neg_conj_le`, any leading coefficient), and for real `c ≥ 0`
  the **Julia inequality** `c Re s ‖f − f^♯‖² ≤ Re(a_{n−1}) (‖f‖² − ‖f^♯‖²)` (`julia_eval`),
  from its root form `Re s ‖∏(s − zᵢ) − ∏(s + z̄ᵢ)‖² ≤ (∑ −Re zᵢ)(‖∏(s − zᵢ)‖² − ‖∏(s + z̄ᵢ)‖²)`
  (`julia_multiset`).
* Complex Routh step (Bilharz): `paraConj f` (`eval_paraConj`), `skewPart f = (f − f^♯)/2`,
  `routhStepC f = f − (a/b) X skewPart f` (`a` the real leading coefficient, `b = Re a_{n−1}`;
  `eval_routhStepC`). **`hurwitz_iff_routhStepC`**: for `deg f ≥ 1` and real positive leading
  coefficient, `f` is Hurwitz iff `Re a_{n−1} > 0` and `routhStepC f` is Hurwitz. The positivity
  of `Re a_{n−1}` for Hurwitz `f`: `re_nextCoeff_pos` (Stodola, complex form).
* Real Routh step: `altPart p` (the part of parity `n − 1`, `p = L + altPart p`),
  `routhStep p = p − (a_n/a_{n−1}) X altPart p` (Routh's rows `r₁, r₂`; `aeval_routhStep_eq`, its
  evaluation; `aeval_routhStep`, the evaluation of `routhStepC` of the complexified polynomial).
  **`hurwitz_iff_routhStep`**: for `deg p ≥ 1`, `a_n > 0`: `p` is Hurwitz iff `a_{n−1} > 0` and
  `routhStep p` is Hurwitz.

Proof of the step. Write `F = (f + f^♯)/2`, `G = (f − f^♯)/2` (values at `s`), `μ = a/b`,
`q = f − μ s G`. Necessity: at a root `s` of `q` with `Re s ≥ 0`, `f(s) = μ s G` and
`f^♯(s) = (μ s − 2) G`, and the Julia inequality becomes `4 b ‖G‖² ≤ 0`, so `f(s) = 0`.
Sufficiency: at a root `s` of `f` with `Re s ≥ 0`, `q(s) = μ s f^♯(s)/2` and
`q(−s̄) = f(−s̄)(1 + μ s̄/2)`, so `‖q(−s̄)‖ ≤ ‖q(s)‖` forces `f(−s̄) = 0` (as `‖1 + w‖ > ‖w‖` for
`Re w ≥ 0`), hence `q(s) = 0`.

Family and connection conclusions.
* None: static algebra. The table form and the matrix interface are in
  `theorem/Criteria/RouthTable.lean`, the Hurwitz-determinant form in
  `theorem/Criteria/HurwitzDeterminants.lean`; the degree-specific criteria of
  `theorem/Criteria/Routh3.lean`, `Routh4.lean`, `Routh5.lean` are proved by one Routh step.
-/

noncomputable section
namespace powerlib.Criteria
open Polynomial
open scoped ComplexConjugate

/-! ## The Julia inequality -/

section Julia

/-- The Cauchy–Schwarz step of the induction: from `x A² ≤ d U` and `x B² ≤ D V`,
`x (A + B)² ≤ (d + D)(U + V)` (`2 x A B ≤ d V + D U` by AM–GM). -/
@[tmio T, powerlib_foundation] private theorem amgm_step {x d D A B U V : ℝ} (hx : 0 ≤ x)
    (hd : 0 ≤ d) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h1 : x * A ^ 2 ≤ d * U) (h2 : x * B ^ 2 ≤ D * V) :
    x * (A + B) ^ 2 ≤ (d + D) * (U + V) := by
  have hxA : 0 ≤ x * A ^ 2 := by positivity
  have hxB : 0 ≤ x * B ^ 2 := by positivity
  have h3 : (x * A ^ 2) * (x * B ^ 2) ≤ (d * U) * (D * V) := mul_le_mul h1 h2 hxB (by positivity)
  have hsq : (2 * (x * A * B)) ^ 2 ≤ (d * V + D * U) ^ 2 := by
    nlinarith [sq_nonneg (d * V - D * U)]
  have hk : 2 * (x * A * B) ≤ d * V + D * U :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  nlinarith

/-- **Julia inequality, root form.** For a multiset `Z` of points of the closed left half plane
and `Re s ≥ 0`, with `P = ∏ (s − z)` and `Q = ∏ (s + z̄)`: `‖Q‖ ≤ ‖P‖` and
`Re s ‖P − Q‖² ≤ (∑ −Re z)(‖P‖² − ‖Q‖²)`. -/
@[tmio T, powerlib_foundation] theorem julia_multiset (Z : Multiset ℂ)
    (hZ : ∀ z ∈ Z, z.re ≤ 0) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Z.map fun z => s + conj z).prod‖ ≤ ‖(Z.map fun z => s - z).prod‖ ∧
      s.re * ‖(Z.map fun z => s - z).prod - (Z.map fun z => s + conj z).prod‖ ^ 2 ≤
        (Z.map fun z => -z.re).sum *
          (‖(Z.map fun z => s - z).prod‖ ^ 2 - ‖(Z.map fun z => s + conj z).prod‖ ^ 2) := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons z Z ih =>
    have hz : z.re ≤ 0 := hZ z (Multiset.mem_cons_self z Z)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hZ w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    set P := (Z.map fun z => s - z).prod
    set Q := (Z.map fun z => s + conj z).prod
    set D := (Z.map fun z => -z.re).sum
    have hD : 0 ≤ D := Multiset.sum_nonneg fun w hw => by
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
      linarith [hZ u (Multiset.mem_cons_of_mem hu)]
    have hab : ‖s - z‖ ^ 2 - ‖s + conj z‖ ^ 2 = 4 * s.re * (-z.re) := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hdiff : ‖(s - z) - (s + conj z)‖ = 2 * (-z.re) := by
      have e : (s - z) - (s + conj z) = ((-(2 * z.re) : ℝ) : ℂ) := by
        apply Complex.ext <;> simp <;> ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      ring
    have hb_le : ‖s + conj z‖ ≤ ‖s - z‖ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
        (by nlinarith [mul_nonneg hs (neg_nonneg.mpr hz)])
    have hQP : ‖Q‖ ^ 2 ≤ ‖P‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ih1 2
    refine ⟨?_, ?_⟩
    · rw [norm_mul, norm_mul]
      exact mul_le_mul hb_le ih1 (norm_nonneg _) (norm_nonneg _)
    · have hsplit : (s - z) * P - (s + conj z) * Q =
          ((s - z) - (s + conj z)) * P + (s + conj z) * (P - Q) := by ring
      have htri : ‖(s - z) * P - (s + conj z) * Q‖ ≤
          2 * (-z.re) * ‖P‖ + ‖s + conj z‖ * ‖P - Q‖ := by
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, hdiff]
      have hU : 0 ≤ (‖s - z‖ ^ 2 - ‖s + conj z‖ ^ 2) * ‖P‖ ^ 2 := by
        rw [hab]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (by linarith)) (sq_nonneg _)
      have hV : 0 ≤ ‖s + conj z‖ ^ 2 * (‖P‖ ^ 2 - ‖Q‖ ^ 2) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have h1 : s.re * (2 * (-z.re) * ‖P‖) ^ 2 ≤
          (-z.re) * ((‖s - z‖ ^ 2 - ‖s + conj z‖ ^ 2) * ‖P‖ ^ 2) := by
        rw [hab]; exact le_of_eq (by ring)
      have h2 : s.re * (‖s + conj z‖ * ‖P - Q‖) ^ 2 ≤
          D * (‖s + conj z‖ ^ 2 * (‖P‖ ^ 2 - ‖Q‖ ^ 2)) := by
        have := mul_le_mul_of_nonneg_left ih2 (sq_nonneg ‖s + conj z‖)
        nlinarith
      have hA : 0 ≤ 2 * (-z.re) * ‖P‖ :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (norm_nonneg _)
      have key := amgm_step hs (by linarith : 0 ≤ -z.re) hD hA
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hU hV h1 h2
      calc s.re * ‖(s - z) * P - (s + conj z) * Q‖ ^ 2
          ≤ s.re * (2 * (-z.re) * ‖P‖ + ‖s + conj z‖ * ‖P - Q‖) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) htri 2) hs
        _ ≤ _ := key
        _ = (-z.re + D) * (‖(s - z) * P‖ ^ 2 - ‖(s + conj z) * Q‖ ^ 2) := by
            rw [norm_mul, norm_mul]; ring

/-- The para-conjugate value through the roots: `(−1)ⁿ conj f(−s̄) = c̄ ∏ (s + z̄ᵢ)`. -/
@[tmio T, powerlib_foundation] theorem neg_one_pow_mul_conj_eval (f : ℂ[X]) (s : ℂ) :
    (-1) ^ f.natDegree * conj (f.eval (-conj s)) =
      conj f.leadingCoeff * (f.roots.map fun z => s + conj z).prod := by
  have hs := IsAlgClosed.splits f
  have hcard : f.roots.card = f.natDegree := splits_iff_card_roots.mp hs
  rw [hs.eval_eq_prod_roots, map_mul, map_multiset_prod, Multiset.map_map]
  have e : f.roots.map ((starRingEnd ℂ) ∘ fun z => -conj s - z) =
      (f.roots.map fun z => s + conj z).map Neg.neg := by
    rw [Multiset.map_map]
    congr 1
    funext z
    simp only [Function.comp_apply, map_sub, map_neg, Complex.conj_conj]
    ring
  rw [e, Multiset.prod_map_neg, Multiset.card_map, hcard]
  have h1 : ((-1 : ℂ) ^ f.natDegree) * (-1) ^ f.natDegree = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination (conj f.leadingCoeff * (f.roots.map fun z => s + conj z).prod) * h1

/-- **The para-conjugate is smaller on the closed right half plane.** If every root of `f` has
nonpositive real part and `Re s ≥ 0`, then `‖f(−s̄)‖ ≤ ‖f(s)‖`. -/
@[tmio T, powerlib_foundation] theorem norm_eval_neg_conj_le {f : ℂ[X]}
    (hf : ∀ z, f.eval z = 0 → z.re ≤ 0) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖f.eval (-conj s)‖ ≤ ‖f.eval s‖ := by
  have hZ : ∀ z ∈ f.roots, z.re ≤ 0 := fun z hz => hf z (isRoot_of_mem_roots hz)
  have h := neg_one_pow_mul_conj_eval f s
  have hn : ‖(-1 : ℂ) ^ f.natDegree * conj (f.eval (-conj s))‖ = ‖f.eval (-conj s)‖ := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_conj]
  rw [← hn, h, (IsAlgClosed.splits f).eval_eq_prod_roots, norm_mul, norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (julia_multiset _ hZ hs).1 (norm_nonneg _)

@[tmio T, powerlib_foundation] private theorem neg_re_multiset_sum (Z : Multiset ℂ) :
    -Z.sum.re = (Z.map fun z => -z.re).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons z Z ih => simp only [Multiset.sum_cons, Multiset.map_cons, Complex.add_re, ← ih]; ring

/-- **Julia inequality.** If `f` has real leading coefficient `c ≥ 0` and every root has
nonpositive real part, then at every `s` with `Re s ≥ 0`, with `f^♯(s) = (−1)ⁿ conj f(−s̄)`:
`c Re s ‖f(s) − f^♯(s)‖² ≤ Re(a_{n−1}) (‖f(s)‖² − ‖f(−s̄)‖²)`. -/
@[tmio T, powerlib_foundation] theorem julia_eval {f : ℂ[X]} {c : ℝ} (hc : f.leadingCoeff = c)
    (hc0 : 0 ≤ c) (hf : ∀ z, f.eval z = 0 → z.re ≤ 0) {s : ℂ} (hs : 0 ≤ s.re) :
    c * s.re * ‖f.eval s - (-1) ^ f.natDegree * conj (f.eval (-conj s))‖ ^ 2 ≤
      f.nextCoeff.re * (‖f.eval s‖ ^ 2 - ‖f.eval (-conj s)‖ ^ 2) := by
  have hsp := IsAlgClosed.splits f
  have hZ : ∀ z ∈ f.roots, z.re ≤ 0 := fun z hz => hf z (isRoot_of_mem_roots hz)
  obtain ⟨-, hJ⟩ := julia_multiset _ hZ hs
  have hn : ‖(-1 : ℂ) ^ f.natDegree * conj (f.eval (-conj s))‖ = ‖f.eval (-conj s)‖ := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_conj]
  rw [← hn, neg_one_pow_mul_conj_eval, hsp.eval_eq_prod_roots, hc, Complex.conj_ofReal,
    hsp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, hc]
  set P := (f.roots.map fun z => s - z).prod
  set Q := (f.roots.map fun z => s + conj z).prod
  have hre : (-(c : ℂ) * f.roots.sum).re = c * (f.roots.map fun z => -z.re).sum := by
    rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, ← neg_re_multiset_sum]
    ring
  rw [hre, ← mul_sub]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  have := mul_le_mul_of_nonneg_left hJ (pow_nonneg hc0 3)
  calc c * s.re * (c * ‖P - Q‖) ^ 2 = c ^ 3 * (s.re * ‖P - Q‖ ^ 2) := by ring
    _ ≤ _ := this
    _ = _ := by ring

end Julia

/-! ## The complex Routh step (Bilharz) -/

section Complex

/-- The para-conjugate `f^♯(s) = (−1)ⁿ conj f(−s̄)` of `f` (`n = natDegree f`). -/
def paraConj (f : ℂ[X]) : ℂ[X] := C ((-1) ^ f.natDegree) * (f.map (starRingEnd ℂ)).comp (-X)

/-- The skew part `(f − f^♯)/2` of `f`: the part of the Routh array of degree `n − 1`. -/
def skewPart (f : ℂ[X]) : ℂ[X] := C (1 / 2) * (f - paraConj f)

/-- The complex Routh step (Bilharz): `f − (a/b) X skewPart f`, `a = Re` of the leading
coefficient, `b = Re a_{n−1}`. -/
def routhStepC (f : ℂ[X]) : ℂ[X] :=
  f - C ((f.leadingCoeff.re / f.nextCoeff.re : ℝ) : ℂ) * X * skewPart f

@[tmio T, powerlib_foundation] theorem eval_paraConj (f : ℂ[X]) (s : ℂ) :
    (paraConj f).eval s = (-1) ^ f.natDegree * conj (f.eval (-conj s)) := by
  rw [paraConj, eval_mul, eval_C, eval_comp, eval_neg, eval_X, eval_map]
  congr 1
  rw [show -s = (starRingEnd ℂ) (-conj s) by simp, eval₂_at_apply]

@[tmio T, powerlib_foundation] theorem eval_routhStepC (f : ℂ[X]) (s : ℂ) :
    (routhStepC f).eval s = f.eval s - ((f.leadingCoeff.re / f.nextCoeff.re : ℝ) : ℂ) * s *
      ((f.eval s - (-1) ^ f.natDegree * conj (f.eval (-conj s))) / 2) := by
  rw [routhStepC, skewPart, eval_sub, eval_mul, eval_mul, eval_mul, eval_C, eval_C, eval_X,
    eval_sub, eval_paraConj]
  ring

/-- **Stodola, complex form.** A Hurwitz polynomial of degree `n ≥ 1` with real positive leading
coefficient has `Re a_{n−1} > 0` (`a_{n−1} = −c ∑ zᵢ`). -/
@[tmio T, powerlib_foundation] theorem re_nextCoeff_pos {f : ℂ[X]} (hn : 0 < f.natDegree)
    {a : ℝ} (ha : 0 < a) (hlead : f.leadingCoeff = a) (hf : ∀ s, f.eval s = 0 → s.re < 0) :
    0 < f.nextCoeff.re := by
  have hsp := IsAlgClosed.splits f
  have hcard : f.roots.card = f.natDegree := splits_iff_card_roots.mp hsp
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp (hcard ▸ hn)
  obtain ⟨T, hT⟩ := Multiset.exists_cons_of_mem hz
  rw [hsp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, hlead, neg_mul, Complex.neg_re,
    Complex.re_ofReal_mul, ← mul_neg, neg_re_multiset_sum, hT, Multiset.map_cons,
    Multiset.sum_cons]
  have hz' : z.re < 0 := hf z (isRoot_of_mem_roots hz)
  have hT' : 0 ≤ (T.map fun w => -w.re).sum := by
    refine Multiset.sum_nonneg fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    linarith [hf u (isRoot_of_mem_roots (hT ▸ Multiset.mem_cons_of_mem hu))]
  have : 0 < -z.re + (T.map fun w => -w.re).sum := by linarith
  positivity

/-- The algebra of necessity: with `a, b > 0`, the Julia inequality
`a Re s ‖P − Q‖² ≤ b (‖P‖² − ‖Q‖²)` and `P − (a/b) s (P − Q)/2 = 0` force `P = 0`. -/
@[tmio T, powerlib_foundation] private theorem eq_zero_of_julia {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) {s P Q : ℂ}
    (hJ : a * s.re * ‖P - Q‖ ^ 2 ≤ b * (‖P‖ ^ 2 - ‖Q‖ ^ 2))
    (hq : P - ((a / b : ℝ) : ℂ) * s * ((P - Q) / 2) = 0) : P = 0 := by
  set G := (P - Q) / 2 with hG
  set μ : ℝ := a / b with hμ
  have hP : P = μ * s * G := by linear_combination hq
  have hQ : Q = (μ * s - 2) * G := by rw [hG] at hP ⊢; linear_combination hP
  have hPQ : P - Q = 2 * G := by rw [hG]; ring
  rw [hPQ, hP, hQ, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_mul 2 G,
    Complex.normSq_mul ((μ : ℂ) * s) G, Complex.normSq_mul ((μ : ℂ) * s - 2) G] at hJ
  have hbμ : b * μ = a := by rw [hμ]; field_simp
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  have h3 : Complex.normSq ((μ : ℂ) * s) - Complex.normSq ((μ : ℂ) * s - 2) = 4 * μ * s.re - 4 := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    ring
  have hnG : Complex.normSq G = 0 := by
    have hn0 := Complex.normSq_nonneg G
    rw [h2] at hJ
    have e : b * (Complex.normSq ((μ : ℂ) * s) * Complex.normSq G -
        Complex.normSq ((μ : ℂ) * s - 2) * Complex.normSq G) =
        4 * a * s.re * Complex.normSq G - 4 * b * Complex.normSq G := by
      rw [← sub_mul, h3, ← hbμ]; ring
    rw [e] at hJ
    nlinarith
  rw [hP, Complex.normSq_eq_zero.mp hnG, mul_zero]

/-- The algebra of sufficiency: `‖1 + w‖ > ‖w‖` for `Re w ≥ 0`, so
`‖R (1 + μ s̄/2)‖ ≤ ‖μ s Q/2‖` with `‖Q‖ = ‖R‖`, `μ ≥ 0`, `Re s ≥ 0` forces `R = 0`. -/
@[tmio T, powerlib_foundation] private theorem eq_zero_of_norm_le {μ : ℝ} (hμ : 0 ≤ μ)
    {s R Q : ℂ} (hs : 0 ≤ s.re) (hQ : ‖Q‖ = ‖R‖)
    (h : ‖R * (1 + μ * conj s / 2)‖ ≤ ‖μ * s * Q / 2‖) : R = 0 := by
  by_contra hR
  have hRpos : 0 < ‖R‖ := norm_pos_iff.mpr hR
  have e : ‖μ * s * Q / 2‖ = ‖R‖ * ‖(μ : ℂ) * conj s / 2‖ := by
    rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul, hQ, Complex.norm_conj]; ring
  rw [e, norm_mul] at h
  have h' : ‖1 + (μ : ℂ) * conj s / 2‖ ≤ ‖(μ : ℂ) * conj s / 2‖ := le_of_mul_le_mul_left h hRpos
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h' 2
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at hsq
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.div_re,
    Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im] at hsq
  norm_num at hsq
  nlinarith [mul_nonneg hμ hs]

/-- **The complex Routh step (Bilharz).** For `f : ℂ[X]` of degree `n ≥ 1` with real positive
leading coefficient `a`: every root of `f` has negative real part iff `Re a_{n−1} > 0` and every
root of the Routh-reduced polynomial `routhStepC f` has negative real part. -/
@[tmio T, powerlib_foundation] theorem hurwitz_iff_routhStepC {f : ℂ[X]} (hn : 0 < f.natDegree)
    {a : ℝ} (ha : 0 < a) (hlead : f.leadingCoeff = a) :
    (∀ s, f.eval s = 0 → s.re < 0) ↔
      0 < f.nextCoeff.re ∧ ∀ s, (routhStepC f).eval s = 0 → s.re < 0 := by
  have hare : f.leadingCoeff.re = a := by rw [hlead, Complex.ofReal_re]
  constructor
  · intro hf
    have hb := re_nextCoeff_pos hn ha hlead hf
    refine ⟨hb, fun s hq => ?_⟩
    by_contra hre
    have hs : 0 ≤ s.re := not_lt.mp hre
    have hJ := julia_eval hlead ha.le (fun z hz => (hf z hz).le) hs
    have hnorm : ‖(-1 : ℂ) ^ f.natDegree * conj (f.eval (-conj s))‖ = ‖f.eval (-conj s)‖ := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_conj]
    rw [← hnorm] at hJ
    rw [eval_routhStepC, hare] at hq
    have hP := eq_zero_of_julia ha hb (by simpa only [mul_assoc] using hJ) hq
    exact absurd (hf s hP) (not_lt.mpr hs)
  · rintro ⟨hb, hq⟩ s hP
    by_contra hre
    have hs : 0 ≤ s.re := not_lt.mp hre
    have hA := norm_eval_neg_conj_le (f := routhStepC f) (fun z hz => (hq z hz).le) hs
    have hss : -conj (-conj s) = s := by simp
    rw [eval_routhStepC, eval_routhStepC, hss, hP, hare] at hA
    set R := f.eval (-conj s)
    set Q := (-1 : ℂ) ^ f.natDegree * conj R
    have hQ : ‖Q‖ = ‖R‖ := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_conj]
    have hA' : ‖R * (1 + (a / f.nextCoeff.re : ℝ) * conj s / 2)‖ ≤
        ‖((a / f.nextCoeff.re : ℝ) : ℂ) * s * Q / 2‖ := by
      convert hA using 2 <;> simp only [map_zero, mul_zero, sub_zero, zero_sub] <;> ring
    have hR := eq_zero_of_norm_le (div_pos ha hb).le hs hQ hA'
    have hR' : f.eval (-conj s) = 0 := hR
    have hq0 : (routhStepC f).eval s = 0 := by
      rw [eval_routhStepC, hP, hR']
      simp
    exact hre (hq s hq0)

end Complex

/-! ## The real Routh step -/

section Real

/-- The part of `p` of parity `n − 1` (`n = natDegree p`): `(p(s) − (−1)ⁿ p(−s))/2`, the second
row `a_{n−1} s^{n−1} + a_{n−3} s^{n−3} + …` of the Routh array. -/
def altPart (p : ℝ[X]) : ℝ[X] := C (1 / 2) * (p - C ((-1) ^ p.natDegree) * p.comp (-X))

/-- **The Routh step.** `p − (a_n/a_{n−1}) X altPart p`: the polynomial of degree `n − 1` whose
Routh array is the array of `p` without its first row. -/
def routhStep (p : ℝ[X]) : ℝ[X] := p - C (p.leadingCoeff / p.nextCoeff) * X * altPart p

/-- The evaluation of the Routh step:
`(routhStep p)(s) = p(s) − (a_n/a_{n−1}) s (p(s) − (−1)ⁿ p(−s))/2`. -/
@[tmio T, powerlib_foundation] theorem aeval_routhStep_eq (p : ℝ[X]) (s : ℂ) :
    aeval s (routhStep p) = aeval s p - ((p.leadingCoeff / p.nextCoeff : ℝ) : ℂ) * s *
      ((aeval s p - (-1) ^ p.natDegree * aeval (-s) p) / 2) := by
  simp only [routhStep, altPart, map_sub, map_mul, aeval_C, aeval_X, aeval_comp, map_neg,
    Complex.coe_algebraMap, map_pow, map_one, Complex.ofReal_div, Complex.ofReal_one]
  push_cast
  ring

/-- The real Routh step is the complex one on the complexified polynomial. -/
@[tmio T, powerlib_foundation] theorem aeval_routhStep (p : ℝ[X]) (s : ℂ) :
    aeval s (routhStep p) = (routhStepC (p.map (algebraMap ℝ ℂ))).eval s := by
  have hconj : conj (aeval (-conj s) p) = aeval (-s) p := by
    rw [← Complex.conjAe_coe, ← aeval_algHom_apply]
    simp
  rw [aeval_routhStep_eq, eval_routhStepC, natDegree_map, leadingCoeff_map, nextCoeff_map_eq,
    eval_map_algebraMap, eval_map_algebraMap, hconj]
  simp only [Complex.coe_algebraMap, Complex.ofReal_re]

/-- **The Routh reduction step, every degree.** For `p : ℝ[X]` of degree `n ≥ 1` with
`a_n > 0`: every complex root of `p` has negative real part iff `a_{n−1} > 0` and every complex
root of the Routh-reduced polynomial `routhStep p` (degree `n − 1`) has negative real part. -/
@[tmio T, powerlib_foundation] theorem hurwitz_iff_routhStep {p : ℝ[X]} (hn : 0 < p.natDegree)
    (ha : 0 < p.leadingCoeff) :
    (∀ s : ℂ, aeval s p = 0 → s.re < 0) ↔
      0 < p.nextCoeff ∧ ∀ s : ℂ, aeval s (routhStep p) = 0 → s.re < 0 := by
  have h := hurwitz_iff_routhStepC (f := p.map (algebraMap ℝ ℂ)) (by rwa [natDegree_map]) ha
    (by rw [leadingCoeff_map]; rfl)
  simp only [eval_map_algebraMap, nextCoeff_map_eq, Complex.coe_algebraMap,
    Complex.ofReal_re] at h
  simp only [aeval_routhStep]
  exact h

end Real

end powerlib.Criteria
