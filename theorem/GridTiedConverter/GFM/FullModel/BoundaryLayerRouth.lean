import theorem.GridTiedConverter.GFM.FullModel.BoundaryLayer

/-! # The 13-state grid-forming converter: the boundary layer decided by the Routh table

Model boundary.
The ten-state fast block `fastBlock δ` of
`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayer.lean` (filter current, capacitor voltage,
line current, current- and voltage-loop integrators, dq, linearized in the fast states; the
real form of the complex `5 × 5` matrix `fastMatrix δ`), at fixed parameters. Continuous time,
constant matrices; every parameter value (no sign assumption is needed for the decision
itself). Excluded: a closed form of the characteristic
polynomial for symbolic gains (the decision is the Routh table of its coefficients, computed at
the given gains), and everything excluded by the full-order model.

Source: GFM counterpart study, full-order model note (t5: "fast block Hurwitz only numerically");
the Routh–Hurwitz criterion in every degree (`theorem/Criteria/RouthTable.lean`) and its complex
form (`theorem/Criteria/RouthComplex.lean`: `χ(realify M) = χ(M) χ(M)‾`). The rational
characteristic polynomials below were computed by expanding the `5 × 5` determinant
(discovery evidence) and are checked here exactly.

Results.
* **Exact decision at fixed gains**: the boundary layer is spectrally stable at every angle iff
  it is at angle 0 (`Params.spectrallyStable_fastBlock_iff`, in `BoundaryLayer.lean`), and at
  angle 0 iff every entry of the first column of the Routh table of its characteristic
  polynomial (degree ten) is positive (`Criteria.spectrallyStable_iff_routhColumn` applied to
  `fastBlock 0`; the composition is not restated: the admission audit would unfold the ten-step
  table of a symbolic `10 × 10` characteristic polynomial);
  `Params.charpoly_fastBlock`: that polynomial is `χ χ̄`, `χ` the characteristic polynomial of
  the complex fast matrix; `Params.spectrallyStable_fastBlock_iff_routhColumn_of_det`: through
  any rational coefficient list whose polynomial is `det(s − M) · conj det(s̄ − M)`, a statement
  decided by `decide +kernel`.
* Checks. `blWitness_det_fastMatrix`: `det(s − fastMatrix 0) = A(s) + j B(s)` at the witness of
  `BoundaryLayer.lean`; `blWitness_fastBlock_routh`: the decision reads its rational table
  `blWitnessRouthList`, whose column has negative entries (`[1, 21/5, 10091/2100, −3035637/504550,
  …]`), in agreement with the eigenvalue `1 + 3j` (`blWitness_not_spectrallyStable`).
  `blFast_det_fastMatrix`, `blWitness_currentScaled_fastBlock_routh`: at the ten times faster
  current loop `blWitness.currentScaled (1/10)` the table `blFastRouthList` is positive, in
  agreement with the Lyapunov certificate (`blWitness_currentScaled_spectrallyStable`).
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex Polynomial
open scoped ComplexConjugate
open powerlib.SingularPerturbation (realify)

namespace Params

variable (p : Params)

/-- The characteristic polynomial of the fast block is `χ χ̄`, `χ` that of the complex fast
matrix (`Criteria.charpoly_realify`). -/
@[tmio M, powerlib_domain] theorem charpoly_fastBlock (δ : ℝ) :
    (p.fastBlock δ).charpoly.map (algebraMap ℝ ℂ) =
      (p.fastMatrix δ).charpoly * (p.fastMatrix δ).charpoly.map (starRingEnd ℂ) := by
  rw [fastBlock_eq_realify]
  exact Criteria.charpoly_realify _

/-- The decision through a rational coefficient list of `det(s − M) · conj det(s̄ − M)`,
`M = fastMatrix 0`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff_routhColumn_of_det (δ : ℝ)
    {a : ℚ} (ha : 0 < a) (l : List ℚ)
    (h : ∀ s : ℂ, aeval s (Criteria.ofList ((a :: l).map (Rat.castHom ℝ))) =
      (Matrix.scalar (Fin 5) s - p.fastMatrix 0).det *
        conj (Matrix.scalar (Fin 5) (conj s) - p.fastMatrix 0).det) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔
      ∀ c ∈ Criteria.routhColumn l.length (a :: l), 0 < c := by
  rw [p.spectrallyStable_fastBlock_iff, fastBlock_eq_realify]
  exact Criteria.spectrallyStable_realify_iff_routhColumn_of_det_rat _ ha l h

end Params

/-! ### Checks at the witness and at the faster current loop -/

/-- The witness's fast matrix at angle `0`, entrywise. -/
@[tmio M, powerlib_domain] private theorem blWitness_fastMatrix_eq :
    blWitness.fastMatrix 0 = !![-11 / 10, -28 / 15 + I, 1, 2, 24; 1, -I, -1, 0, 0;
      0, 10, -1 - I, 0, 0; -1, -28 / 15 + I, 1, 0, 24; 0, -1, 0, 0, 0] := by
  have h0 : ej 0 = 1 := by simp [ej]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Params.fastMatrix, h0, Params.Bf, Params.Zg_eq, Params.Zv, blWitness] <;>
    norm_num [Complex.ext_iff]

/-- The characteristic determinant of the witness's fast matrix,
`A(s) + j B(s)` with `A = s⁵ + 21/10 s⁴ + 419/30 s³ + 65/2 s² + 1136/15 s + 48`,
`B = 2 s⁴ + 11/5 s³ + 119/30 s² + 416/15 s + 48`. -/
@[tmio M, powerlib_domain] theorem blWitness_det_fastMatrix (s : ℂ) :
    (Matrix.scalar (Fin 5) s - blWitness.fastMatrix 0).det =
      (s ^ 5 + 21 / 10 * s ^ 4 + 419 / 30 * s ^ 3 + 65 / 2 * s ^ 2 + 1136 / 15 * s + 48) +
        I * (2 * s ^ 4 + 11 / 5 * s ^ 3 + 119 / 30 * s ^ 2 + 416 / 15 * s + 48) := by
  rw [blWitness_fastMatrix_eq]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.sum_univ_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  linear_combination (s ^ 3 + s ^ 2 / 10) * Complex.I_sq

/-- The rational coefficient list of the degree-ten characteristic polynomial of the witness's
fast block (`A² + B²`). -/
def blWitnessRouthList : List ℚ :=
  [1, 21 / 5, 10903 / 300, 6623 / 50, 453367 / 900, 14503 / 10, 1666393 / 450, 1506304 / 225,
    2251232 / 225, 49664 / 5, 4608]

/-- **The Routh table at the witness**: the decision of the boundary layer of `blWitness` reads
the rational table of `blWitnessRouthList`, and that table has a nonpositive entry (its fourth
entry is `−3035637/504550`) — in agreement with the unstable eigenvalue `1 + 3j`. -/
@[tmio M, powerlib_domain] theorem blWitness_fastBlock_routh :
    (∀ δ, Linear.SpectrallyStable (blWitness.fastBlock δ) ↔
      ∀ c ∈ Criteria.routhColumn 10 blWitnessRouthList, 0 < c) ∧
      ¬ ∀ c ∈ Criteria.routhColumn 10 blWitnessRouthList, 0 < c := by
  refine ⟨fun δ => ?_, by decide +kernel⟩
  refine blWitness.spectrallyStable_fastBlock_iff_routhColumn_of_det δ (a := 1)
    (l := blWitnessRouthList.tail) (by norm_num) fun s => ?_
  rw [blWitness_det_fastMatrix, blWitness_det_fastMatrix]
  simp [Criteria.ofList, blWitnessRouthList, Complex.conj_ofNat, map_div₀]
  linear_combination
    (2 * s ^ 4 + 11 / 5 * s ^ 3 + 119 / 30 * s ^ 2 + 416 / 15 * s + 48) ^ 2 * Complex.I_sq

/-- The fast matrix of `blWitness.currentScaled (1/10)` at angle `0`, entrywise. -/
@[tmio M, powerlib_domain] private theorem blFast_fastMatrix_eq :
    (blWitness.currentScaled (1 / 10)).fastMatrix 0 = !![-11, -56 / 3 + 10 * I, 10, 200, 240;
      1, -I, -1, 0, 0; 0, 10, -1 - I, 0, 0; -1, -28 / 15 + I, 1, 0, 24; 0, -1, 0, 0, 0] := by
  have h0 : ej 0 = 1 := by simp [ej]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Params.fastMatrix, Params.currentScaled, h0, Params.Bf, Params.Zg_eq, Params.Zv,
      blWitness] <;>
    norm_num [Complex.ext_iff]

/-- The characteristic determinant of the fast matrix of `blWitness.currentScaled (1/10)`,
`A(s) + j B(s)` with `A = s⁵ + 12 s⁴ + 716/3 s³ + 841 s² + 16240/3 s + 4800`,
`B = 2 s⁴ + 13 s³ + 659/3 s² + 1840/3 s + 4800`. -/
@[tmio M, powerlib_domain] theorem blFast_det_fastMatrix (s : ℂ) :
    (Matrix.scalar (Fin 5) s - (blWitness.currentScaled (1 / 10)).fastMatrix 0).det =
      (s ^ 5 + 12 * s ^ 4 + 716 / 3 * s ^ 3 + 841 * s ^ 2 + 16240 / 3 * s + 4800) +
        I * (2 * s ^ 4 + 13 * s ^ 3 + 659 / 3 * s ^ 2 + 1840 / 3 * s + 4800) := by
  rw [blFast_fastMatrix_eq]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.sum_univ_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  linear_combination (s ^ 3 + s ^ 2) * Complex.I_sq

/-- The rational coefficient list of the degree-ten characteristic polynomial of the fast block
of `blWitness.currentScaled (1/10)`. -/
def blFastRouthList : List ℚ :=
  [1, 24, 1876 / 3, 7462, 801181 / 9, 549122, 31408610 / 9, 106116160 / 9, 358764800 / 9,
    57856000, 46080000]

/-- **The Routh table at the faster current loop**: the decision of the boundary layer of
`blWitness.currentScaled (1/10)` reads the rational table of `blFastRouthList`, and that table
is positive — in agreement with the Lyapunov certificate. -/
@[tmio M, powerlib_domain] theorem blWitness_currentScaled_fastBlock_routh :
    (∀ δ, Linear.SpectrallyStable ((blWitness.currentScaled (1 / 10)).fastBlock δ) ↔
      ∀ c ∈ Criteria.routhColumn 10 blFastRouthList, 0 < c) ∧
      ∀ c ∈ Criteria.routhColumn 10 blFastRouthList, 0 < c := by
  refine ⟨fun δ => ?_, by decide +kernel⟩
  refine (blWitness.currentScaled (1 / 10)).spectrallyStable_fastBlock_iff_routhColumn_of_det δ
    (a := 1) (l := blFastRouthList.tail) (by norm_num) fun s => ?_
  rw [blFast_det_fastMatrix, blFast_det_fastMatrix]
  simp [Criteria.ofList, blFastRouthList, Complex.conj_ofNat, map_div₀]
  linear_combination
    (2 * s ^ 4 + 13 * s ^ 3 + 659 / 3 * s ^ 2 + 1840 / 3 * s + 4800) ^ 2 * Complex.I_sq

end powerlib.GFM.FullModel
