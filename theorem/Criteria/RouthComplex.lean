import theorem.Criteria.RouthTable
import theorem.Criteria.ComplexQuadratic
import theorem.SingularPerturbation.Realification

/-! # Routh–Hurwitz for complex polynomials and complex matrices (foundation)

A complex polynomial `f` is Hurwitz iff the real polynomial `f f̄` (`f̄` with conjugated
coefficients) is, so the real Routh table decides complex polynomials; the complex Routh step
(`Criteria.hurwitz_iff_routhStepC`) decides the complex cubic by three explicit inequalities; and
the real form of a complex matrix has the characteristic polynomial `χ χ̄`.

Scope.
* Static algebra of complex polynomials `f : ℂ[X]` and of complex square matrices read through
  their real forms (`SingularPerturbation.realify`). No model family is defined.

Source: H. Bilharz, *Z. Angew. Math. Mech.* 24 (1944) (complex Routh–Hurwitz); F. R. Gantmacher,
*The Theory of Matrices*, vol. 2, Ch. XV; Silvester's determinant of a block matrix
(`Matrix.det_det`); the complex Routh step `theorem/Criteria/RouthHurwitz.lean` and the complex
quadratic `theorem/Criteria/ComplexQuadratic.lean` (shared criteria interface for the work-sync
formalization).

Results.
* `f f̄`: `exists_map_eq_mul_conj` (it has real coefficients), `aeval_eq_mul_conj`
  (`q(s) = f(s) conj f(s̄)`), **`hurwitz_iff_of_aeval_mul_conj`** (`f` Hurwitz iff `q` Hurwitz) and
  `hurwitz_iff_routhColumn_mul_conj` (the real Routh table of `q` decides `f`).
* **Complex cubic** (`complexCubic_roots_re_neg_iff`): `s³ + a₂ s² + a₁ s + a₀` is Hurwitz iff
  `Re a₂ > 0`, `Re a₂ (Re a₁ Re a₂ + Im a₁ Im a₂ − Re a₀) − (Im a₁)² > 0` and
  `complexCubicDet a₂ a₁ a₀ > 0` (one complex Routh step to the quadratic
  `c₁ s² + d₁ s + a₀`, `c₁ = a₂ − j Im a₁/Re a₂`, `d₁ = a₁ − Re a₀/Re a₂`, then
  `Criteria.complexQuadratic_roots_re_neg_iff`; for real coefficients the conditions are
  `a₂ > 0`, `a₂ a₁ − a₀ > 0`, `a₀ (a₂ a₁ − a₀)² > 0`). The determinant (Bilharz) form for complex
  cubics, quartics and quintics is in `theorem/Criteria/Bilharz.lean`.
* Complex matrices: `charpoly_realify` (`χ(realify M) = χ(M) χ(M)‾`, from Silvester's
  `det realify N = |det N|²` at real points), `spectrallyStable_realify_iff_charpoly` (the real
  form is spectrally stable iff every root of `χ(M)` has negative real part) and
  `spectrallyStable_realify_iff_routhColumn_of_det` (decided by the Routh table of any real
  coefficient list whose polynomial is `det(s − M) · conj det(s̄ − M)`; rational form
  `spectrallyStable_realify_iff_routhColumn_of_det_rat`, a decidable table).

Family and connection conclusions.
* None: static algebra.
-/

noncomputable section
namespace powerlib.Criteria
open Polynomial
open scoped ComplexConjugate

/-! ## The real polynomial `f f̄` -/

section MulConj

/-- `f f̄` has real coefficients. -/
@[tmio T, powerlib_foundation] theorem exists_map_eq_mul_conj (f : ℂ[X]) :
    ∃ q : ℝ[X], q.map (algebraMap ℝ ℂ) = f * f.map (starRingEnd ℂ) := by
  have hfix : (f * f.map (starRingEnd ℂ)).map (starRingEnd ℂ) = f * f.map (starRingEnd ℂ) := by
    rw [Polynomial.map_mul, Polynomial.map_map, mul_comm]
    congr 1
    conv_rhs => rw [← Polynomial.map_id (p := f)]
    congr 1
    ext z; simp
  have hl : f * f.map (starRingEnd ℂ) ∈ Polynomial.lifts (algebraMap ℝ ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    refine ⟨((f * f.map (starRingEnd ℂ)).coeff k).re, ?_⟩
    have hk := congrArg (fun g => g.coeff k) hfix
    simp only [coeff_map] at hk
    exact Complex.conj_eq_iff_re.mp hk
  obtain ⟨q, hq⟩ := Polynomial.mem_lifts _ |>.mp hl
  exact ⟨q, hq⟩

/-- The evaluation of a real polynomial with complexification `f f̄`: `q(s) = f(s) conj f(s̄)`. -/
@[tmio T, powerlib_foundation] theorem aeval_eq_mul_conj {f : ℂ[X]} {q : ℝ[X]}
    (h : q.map (algebraMap ℝ ℂ) = f * f.map (starRingEnd ℂ)) (s : ℂ) :
    aeval s q = f.eval s * conj (f.eval (conj s)) := by
  rw [← eval_map_algebraMap, h, eval_mul, eval_map]
  congr 1
  rw [show s = (starRingEnd ℂ) (conj s) by simp, eval₂_at_apply, Complex.conj_conj]

/-- **A complex polynomial is Hurwitz iff `f f̄` is.** For any real `q` with
`q(s) = f(s) conj f(s̄)`, every root of `f` has negative real part iff every root of `q` has. -/
@[tmio T, powerlib_foundation] theorem hurwitz_iff_of_aeval_mul_conj {f : ℂ[X]} {q : ℝ[X]}
    (hq : ∀ s : ℂ, aeval s q = f.eval s * conj (f.eval (conj s))) :
    (∀ s, f.eval s = 0 → s.re < 0) ↔ ∀ s : ℂ, aeval s q = 0 → s.re < 0 := by
  constructor
  · intro hf s hs
    rw [hq, mul_eq_zero, map_eq_zero] at hs
    rcases hs with h | h
    · exact hf s h
    · simpa using hf _ h
  · intro h s hs
    exact h s (by rw [hq, hs, zero_mul])

/-- **The real Routh table of `f f̄` decides `f`** (`f ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem hurwitz_iff_routhColumn_mul_conj {f : ℂ[X]} (hf : f ≠ 0)
    {q : ℝ[X]} (h : q.map (algebraMap ℝ ℂ) = f * f.map (starRingEnd ℂ)) :
    (∀ s, f.eval s = 0 → s.re < 0) ↔ ∀ c ∈ routhColumn q.natDegree (coeffList q), 0 < c := by
  rw [hurwitz_iff_of_aeval_mul_conj (aeval_eq_mul_conj h)]
  refine hurwitz_iff_routhColumn ?_
  have hlc := congrArg leadingCoeff h
  rw [leadingCoeff_map, leadingCoeff_mul, leadingCoeff_map] at hlc
  have hpos : 0 < Complex.normSq f.leadingCoeff :=
    Complex.normSq_pos.mpr (leadingCoeff_ne_zero.mpr hf)
  have hn : (q.leadingCoeff : ℂ) = (Complex.normSq f.leadingCoeff : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]; exact hlc
  rw [Complex.ofReal_inj] at hn
  rw [hn]; exact hpos

end MulConj

/-! ## The complex cubic -/

section Cubic

/-- The last condition of the complex cubic `s³ + a₂ s² + a₁ s + a₀` (`xₖ = Re aₖ`,
`yₖ = Im aₖ`): for real coefficients it is `a₀ (a₂ a₁ − a₀)²`. -/
def complexCubicDet (a2 a1 a0 : ℂ) : ℝ :=
  a0.re ^ 3 - 2 * a0.re ^ 2 * a1.re * a2.re - a0.re ^ 2 * a2.re * a2.im ^ 2 +
    a0.re ^ 2 * a1.im * a2.im + a0.re * a1.re ^ 2 * a2.re ^ 2 +
    a0.re * a1.re * a2.re * a1.im * a2.im - a0.re * a1.re * a1.im ^ 2 +
    2 * a0.re * a2.re ^ 2 * a0.im * a2.im - 3 * a0.re * a2.re * a0.im * a1.im +
    a1.re * a2.re ^ 2 * a0.im * a1.im - a2.re ^ 3 * a0.im ^ 2 +
    a2.re * a0.im * a1.im ^ 2 * a2.im - a0.im * a1.im ^ 3

/-- The monic complex cubic `X³ + a₂ X² + a₁ X + a₀`. -/
private def cubicC (a2 a1 a0 : ℂ) : ℂ[X] := X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

@[tmio T, powerlib_foundation] private theorem cubicC_natDegree (a2 a1 a0 : ℂ) :
    (cubicC a2 a1 a0).natDegree = 3 := by
  unfold cubicC; compute_degree!

@[tmio T, powerlib_foundation] private theorem cubicC_monic (a2 a1 a0 : ℂ) :
    (cubicC a2 a1 a0).Monic := by
  unfold cubicC; monicity!

@[tmio T, powerlib_foundation] private theorem cubicC_nextCoeff (a2 a1 a0 : ℂ) :
    (cubicC a2 a1 a0).nextCoeff = a2 := by
  rw [nextCoeff_of_natDegree_pos (by rw [cubicC_natDegree]; norm_num), cubicC_natDegree]
  simp [cubicC, coeff_X_pow]

@[tmio T, powerlib_foundation] private theorem cubicC_eval (a2 a1 a0 s : ℂ) :
    (cubicC a2 a1 a0).eval s = s ^ 3 + a2 * s ^ 2 + a1 * s + a0 := by
  simp [cubicC]

/-- The Routh-reduced complex quadratic of the cubic, `c₁ s² + d₁ s + a₀`. -/
@[tmio T, powerlib_foundation] private theorem eval_routhStepC_cubicC {a2 a1 a0 : ℂ}
    (hx : a2.re ≠ 0) (s : ℂ) :
    (routhStepC (cubicC a2 a1 a0)).eval s =
      (a2 - ((a1.im / a2.re : ℝ) : ℂ) * Complex.I) * s ^ 2 +
        (a1 - ((a0.re / a2.re : ℝ) : ℂ)) * s + a0 := by
  rw [eval_routhStepC, cubicC_natDegree, (cubicC_monic a2 a1 a0).leadingCoeff, cubicC_nextCoeff,
    cubicC_eval, cubicC_eval]
  simp only [map_add, map_mul, map_pow, map_neg, Complex.conj_conj, Complex.one_re]
  have e2 : conj a2 = 2 * (a2.re : ℂ) - a2 := by
    have := Complex.add_conj a2; push_cast at this; linear_combination this
  have e1 : conj a1 = a1 - 2 * (a1.im : ℂ) * Complex.I := by
    have := Complex.sub_conj a1; push_cast at this; linear_combination -this
  have e0 : conj a0 = 2 * (a0.re : ℂ) - a0 := by
    have := Complex.add_conj a0; push_cast at this; linear_combination this
  have hx' : (a2.re : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [e2, e1, e0]
  push_cast
  field_simp
  ring

/-- The Routh-reduced quadratic, decided by `Criteria.complexQuadratic_roots_re_neg_iff`. -/
@[tmio T, powerlib_foundation] private theorem quadratic_reduced_iff {a2 a1 a0 : ℂ}
    (hx : 0 < a2.re) :
    (∀ s : ℂ, (a2 - ((a1.im / a2.re : ℝ) : ℂ) * Complex.I) * s ^ 2 +
        (a1 - ((a0.re / a2.re : ℝ) : ℂ)) * s + a0 = 0 → s.re < 0) ↔
      0 < a2.re * (a1.re * a2.re + a1.im * a2.im - a0.re) - a1.im ^ 2 ∧
        0 < complexCubicDet a2 a1 a0 := by
  set c1 : ℂ := a2 - ((a1.im / a2.re : ℝ) : ℂ) * Complex.I with hc1
  set d1 : ℂ := a1 - ((a0.re / a2.re : ℝ) : ℂ) with hd1
  have hc1re : c1.re = a2.re := by simp [hc1]
  have hc1im : c1.im = a2.im - a1.im / a2.re := by simp [hc1]
  have hd1re : d1.re = a1.re - a0.re / a2.re := by simp [hd1]
  have hd1im : d1.im = a1.im := by simp [hd1]
  have hc0 : c1 ≠ 0 := fun h => by rw [h, Complex.zero_re] at hc1re; linarith
  have hN : 0 < Complex.normSq c1 := Complex.normSq_pos.mpr hc0
  have hiff : (∀ s : ℂ, c1 * s ^ 2 + d1 * s + a0 = 0 → s.re < 0) ↔
      ∀ s : ℂ, s ^ 2 + d1 / c1 * s + a0 / c1 = 0 → s.re < 0 := by
    refine forall_congr' fun s => imp_congr_left ?_
    constructor
    · intro h; field_simp; linear_combination h
    · intro h; field_simp at h; linear_combination h
  rw [hiff, complexQuadratic_roots_re_neg_iff]
  have hNe : Complex.normSq c1 = a2.re ^ 2 + (a2.im - a1.im / a2.re) ^ 2 := by
    rw [Complex.normSq_apply, hc1re, hc1im]; ring
  have hx0 : a2.re ≠ 0 := hx.ne'
  have hN' : 0 < a2.re ^ 2 + (a2.im - a1.im / a2.re) ^ 2 := hNe ▸ hN
  have k1 : (d1 / c1).re * (a2.re * (a2.re ^ 2 + (a2.im - a1.im / a2.re) ^ 2)) =
      a2.re * (a1.re * a2.re + a1.im * a2.im - a0.re) - a1.im ^ 2 := by
    rw [Complex.div_re, hNe, hc1re, hc1im, hd1re, hd1im]
    field_simp
    ring
  have k2 : ((d1 / c1).re ^ 2 * (a0 / c1).re + (d1 / c1).re * (d1 / c1).im * (a0 / c1).im -
      (a0 / c1).im ^ 2) * (a2.re * (a2.re ^ 2 + (a2.im - a1.im / a2.re) ^ 2) ^ 2) =
      complexCubicDet a2 a1 a0 := by
    rw [Complex.div_re, Complex.div_im, Complex.div_re, Complex.div_im, hNe, hc1re, hc1im, hd1re,
      hd1im, complexCubicDet]
    field_simp
    ring
  have hp1 : 0 < a2.re * (a2.re ^ 2 + (a2.im - a1.im / a2.re) ^ 2) := mul_pos hx hN'
  have hp2 : 0 < a2.re * (a2.re ^ 2 + (a2.im - a1.im / a2.re) ^ 2) ^ 2 :=
    mul_pos hx (pow_pos hN' 2)
  rw [← k1, ← k2, mul_pos_iff_of_pos_right hp1, mul_pos_iff_of_pos_right hp2]

/-- **Routh–Hurwitz for the complex cubic** (Bilharz): `s³ + a₂ s² + a₁ s + a₀` has all roots in
the open left half plane iff `Re a₂ > 0`, `Re a₂ (Re a₁ Re a₂ + Im a₁ Im a₂ − Re a₀) > (Im a₁)²`
and `complexCubicDet a₂ a₁ a₀ > 0`. -/
@[tmio T, powerlib_foundation] theorem complexCubic_roots_re_neg_iff (a2 a1 a0 : ℂ) :
    (∀ s : ℂ, s ^ 3 + a2 * s ^ 2 + a1 * s + a0 = 0 → s.re < 0) ↔
      0 < a2.re ∧ 0 < a2.re * (a1.re * a2.re + a1.im * a2.im - a0.re) - a1.im ^ 2 ∧
        0 < complexCubicDet a2 a1 a0 := by
  have hstep := hurwitz_iff_routhStepC (f := cubicC a2 a1 a0)
    (by rw [cubicC_natDegree]; norm_num) one_pos
    (by rw [(cubicC_monic a2 a1 a0).leadingCoeff, Complex.ofReal_one])
  simp only [cubicC_eval, cubicC_nextCoeff] at hstep
  rw [hstep]
  constructor
  · rintro ⟨hx, hq⟩
    refine ⟨hx, (quadratic_reduced_iff hx).mp fun s hs => hq s ?_⟩
    rw [eval_routhStepC_cubicC hx.ne']; exact hs
  · rintro ⟨hx, h2, h3⟩
    refine ⟨hx, fun s hs => (quadratic_reduced_iff hx).mpr ⟨h2, h3⟩ s ?_⟩
    rw [eval_routhStepC_cubicC hx.ne'] at hs; exact hs

end Cubic

/-! ## Complex matrices -/

section Matrix

open SingularPerturbation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `det(realify N) = |det N|²` (Silvester, `Matrix.det_det`). -/
@[tmio T, powerlib_foundation] theorem det_realify (N : Matrix n n ℂ) :
    (realify N).det = Complex.normSq N.det := by
  have h : ((Algebra.leftMulMatrix Complex.basisOneI) N.det).det = (realify N).det :=
    Matrix.det_det N (Algebra.leftMulMatrix Complex.basisOneI).toRingHom
  rw [← h, Algebra.leftMulMatrix_complex, Matrix.det_fin_two_of, Complex.normSq_apply]
  ring

/-- **The characteristic polynomial of the real form** is `χ(M) χ(M)‾`. -/
@[tmio T, powerlib_foundation] theorem charpoly_realify (M : Matrix n n ℂ) :
    (realify M).charpoly.map (algebraMap ℝ ℂ) =
      M.charpoly * M.charpoly.map (starRingEnd ℂ) := by
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.Infinite.mono (s := Set.range (algebraMap ℝ ℂ)) ?_
    (Set.infinite_range_of_injective (algebraMap ℝ ℂ).injective)
  rintro _ ⟨r, rfl⟩
  have hsc : Matrix.scalar (n × Fin 2) r - realify M =
      realify (Matrix.scalar n (r : ℂ) - M) := by
    rw [sub_eq_add_neg (Matrix.scalar n (r : ℂ)) M, realify_add, realify_neg, ← sub_eq_add_neg]
    congr 1
    rw [show Matrix.scalar n (r : ℂ) = Matrix.diagonal fun _ => (r : ℂ) from rfl,
      realify_diagonal_ofReal]
    rfl
  have hconj : (M.charpoly.map (starRingEnd ℂ)).eval (r : ℂ) =
      conj (M.charpoly.eval (r : ℂ)) := by
    rw [eval_map]
    conv_lhs => rw [show (r : ℂ) = conj (r : ℂ) by simp]
    exact eval₂_at_apply _ _
  simp only [Set.mem_ofPred_eq, Complex.coe_algebraMap]
  rw [eval_mul, hconj, ← Complex.coe_algebraMap, eval_map_algebraMap, aeval_algebraMap_apply,
    coe_aeval_eq_eval, Matrix.eval_charpoly, hsc, det_realify, Complex.coe_algebraMap,
    Matrix.eval_charpoly, Complex.normSq_eq_conj_mul_self, mul_comm]

/-- The real form of `M` is spectrally stable iff every root of `χ(M)` has negative real part. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_realify_iff_charpoly (M : Matrix n n ℂ) :
    Linear.SpectrallyStable (realify M) ↔ ∀ s, M.charpoly.eval s = 0 → s.re < 0 := by
  rw [spectrallyStable_realify_iff]
  have key : ∀ (s : ℂ) (w : n → ℂ), (Matrix.scalar n s - M).mulVec w = 0 ↔ M.mulVec w = s • w := by
    intro s w
    rw [Matrix.sub_mulVec, sub_eq_zero, eq_comm]
    simp [Matrix.scalar_apply]
  constructor
  · intro h s hs
    rw [Matrix.eval_charpoly] at hs
    obtain ⟨w, hw, hwz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs
    exact h s w hw ((key s w).mp hwz)
  · intro h μ w hw heig
    exact h μ (by
      rw [Matrix.eval_charpoly]
      exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, (key μ w).mpr heig⟩)

/-- **Complex matrices through a real coefficient list.** If the polynomial of `a :: l` (`a > 0`)
evaluates to `det(s − M) · conj det(s̄ − M)`, the real form of `M` is spectrally stable iff the
Routh table of `a :: l` is positive. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_realify_iff_routhColumn_of_det
    (M : Matrix n n ℂ) {a : ℝ} (ha : 0 < a) (l : List ℝ)
    (h : ∀ s : ℂ, aeval s (ofList (a :: l)) =
      (Matrix.scalar n s - M).det * conj (Matrix.scalar n (conj s) - M).det) :
    Linear.SpectrallyStable (realify M) ↔ ∀ c ∈ routhColumn l.length (a :: l), 0 < c := by
  rw [spectrallyStable_realify_iff_charpoly, ← hurwitz_ofList_iff ha]
  exact hurwitz_iff_of_aeval_mul_conj fun s => by rw [h, Matrix.eval_charpoly, Matrix.eval_charpoly]

/-- The same with rational coefficients: a decidable rational table. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_realify_iff_routhColumn_of_det_rat
    (M : Matrix n n ℂ) {a : ℚ} (ha : 0 < a) (l : List ℚ)
    (h : ∀ s : ℂ, aeval s (ofList ((a :: l).map (Rat.castHom ℝ))) =
      (Matrix.scalar n s - M).det * conj (Matrix.scalar n (conj s) - M).det) :
    Linear.SpectrallyStable (realify M) ↔ ∀ c ∈ routhColumn l.length (a :: l), 0 < c := by
  rw [spectrallyStable_realify_iff_charpoly, ← hurwitz_ofList_rat_iff ha]
  exact hurwitz_iff_of_aeval_mul_conj fun s => by rw [h, Matrix.eval_charpoly, Matrix.eval_charpoly]

end Matrix

end powerlib.Criteria
