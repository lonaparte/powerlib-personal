import theorem.Criteria.Routh3

/-! # The Routh–Hurwitz conditions of the droop-loop Jacobian pattern (foundation)

Scope.
* A real 3×3 matrix of the pattern `[[0, 1, 0], [−a/M, −D/M, b/M], [ω c, 0, −ω k]]`
  (`droopJacobian`) for arbitrary reals `M, D, ω, a, b, c, k`. Nothing here describes a physical
  system; every statement is static algebra or a root-location fact, a foundation result. Model
  families with this linearization (a second-order angle loop coupled to a first-order filtered
  loop, e.g. the reactive-power–voltage droop of
  `theorem/GridTiedConverter/GFM/QVDroopStability.lean`) read their stability boundaries from it.

Source: the cubic Routh–Hurwitz criterion of `theorem/Criteria/Routh3.lean`
(`Criteria.isHurwitz_iff_of_coeffs_cubic`, `Criteria.exists_cubic_root_re_pos_of_violation`)
applied to the invariants of the pattern.

Results.
* Invariants (`M ≠ 0`): `tr = −(D + M ω k)/M`, `m₂ = (a + D ω k)/M`,
  `det = −ω (k a − b c)/M` (private), so
  `det(sI − J) = s³ + ((D + Mωk)/M) s² + ((a + Dωk)/M) s + ω (k a − b c)/M`
  (`det_characteristicMatrix_droopJacobian`).
* `isHurwitz_droopJacobian_iff`: for `M, ω > 0` the pattern is Hurwitz iff `D + M ω k > 0`,
  `k a − b c > 0` and `D (a + D ω k + M ω² k²) + M ω b c > 0` (the cubic criterion on
  `M² s³ + M (D + Mωk) s² + M (a + Dωk) s + M ω (k a − b c)`).
* `exists_root_re_pos_droopJacobian`: a strict violation of one of the three gives a
  characteristic root with positive real part.
* `droopJacobian_null`: at `k a = b c` (the fold), `(k, 0, c)` is a right and
  `(D ω k/M, ω k, b/M)` a left null vector.
* `droopJacobian_routh_or_violation`: away from `k a = b c` and the third quantity `0`, either all
  three hold or one is strictly violated (the identity
  `G = (D + Mωk)(a + Dωk) − Mω (k a − b c)` excludes `D + M ω k = 0`).
-/

noncomputable section
namespace powerlib.Criteria
open Matrix

/-- The Jacobian pattern of a reactive-power–voltage droop loop on `(δ, Δω, Q_f)`:
`[[0, 1, 0], [−a/M, −D/M, b/M], [ω c, 0, −ω k]]`. -/
def droopJacobian (M D ω a b c k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; -a / M, -D / M, b / M; ω * c, 0, -(ω * k)]

@[tmio T, powerlib_foundation] private theorem trace_droopJacobian {M : ℝ} (hM : M ≠ 0)
    (D ω a b c k : ℝ) : (droopJacobian M D ω a b c k).trace = -((D + M * ω * k) / M) := by
  simp only [droopJacobian, Matrix.trace_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons]
  field_simp
  ring

@[tmio T, powerlib_foundation] private theorem principalMinorSum_droopJacobian {M : ℝ}
    (hM : M ≠ 0) (D ω a b c k : ℝ) :
    principalMinorSum (droopJacobian M D ω a b c k) = (a + D * ω * k) / M := by
  simp only [droopJacobian, principalMinorSum, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons]
  field_simp
  ring

@[tmio T, powerlib_foundation] private theorem det_droopJacobian {M : ℝ} (hM : M ≠ 0)
    (D ω a b c k : ℝ) :
    (droopJacobian M D ω a b c k).det = -(ω * (k * a - b * c) / M) := by
  simp only [droopJacobian, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons]
  field_simp
  ring

/-- **The characteristic polynomial of the droop-loop Jacobian** (`M ≠ 0`):
`det(sI − J) = s³ + ((D + M ω k)/M) s² + ((a + D ω k)/M) s + ω (k a − b c)/M`. -/
@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_droopJacobian {M : ℝ}
    (hM : M ≠ 0) (D ω a b c k : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (droopJacobian M D ω a b c k) s).det =
      s ^ 3 + (((D + M * ω * k) / M : ℝ) : ℂ) * s ^ 2 + (((a + D * ω * k) / M : ℝ) : ℂ) * s +
        ((ω * (k * a - b * c) / M : ℝ) : ℂ) := by
  rw [det_characteristicMatrix_fin_three', trace_droopJacobian hM,
    principalMinorSum_droopJacobian hM, det_droopJacobian hM]
  push_cast
  ring

/-- **Routh–Hurwitz for the droop-loop Jacobian.** For `M, ω > 0` the matrix
`[[0, 1, 0], [−a/M, −D/M, b/M], [ω c, 0, −ω k]]` is Hurwitz iff `D + M ω k > 0`,
`k a − b c > 0` and `D (a + D ω k + M ω² k²) + M ω b c > 0` (the cubic criterion on
`M² s³ + M (D + Mωk) s² + M (a + Dωk) s + M ω (k a − b c)`). -/
@[tmio T, powerlib_foundation] theorem isHurwitz_droopJacobian_iff {M D ω a b c k : ℝ}
    (hM : 0 < M) (hω : 0 < ω) :
    LinearSystems.IsHurwitz (droopJacobian M D ω a b c k) ↔
      0 < D + M * ω * k ∧ 0 < k * a - b * c ∧
        0 < D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c) := by
  have hM0 := hM.ne'
  rw [isHurwitz_iff_of_coeffs_cubic _ (pow_pos hM 2) (a2 := M * (D + M * ω * k))
    (a1 := M * (a + D * ω * k)) (a0 := M * ω * (k * a - b * c))
    (by rw [trace_droopJacobian hM0]; field_simp)
    (by rw [principalMinorSum_droopJacobian hM0]; field_simp)
    (by rw [det_droopJacobian hM0]; field_simp)]
  have e : M * (D + M * ω * k) * (M * (a + D * ω * k)) - M ^ 2 * (M * ω * (k * a - b * c)) =
      M ^ 2 * (D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c)) := by ring
  have hMω := mul_pos hM hω
  constructor
  · rintro ⟨h2, h0, hg⟩
    refine ⟨pos_of_mul_pos_right h2 hM.le, pos_of_mul_pos_right h0 hMω.le, ?_⟩
    exact pos_of_mul_pos_right (show 0 < M ^ 2 * _ by linarith) (sq_nonneg M)
  · rintro ⟨h2, h0, hg⟩
    exact ⟨mul_pos hM h2, mul_pos hMω h0, by nlinarith [mul_pos (pow_pos hM 2) hg]⟩

/-- **A strict violation gives an unstable root.** For `M, ω > 0`, if `D + M ω k < 0`,
`k a − b c < 0` or `D (a + D ω k + M ω² k²) + M ω b c < 0`, the droop-loop Jacobian has a
characteristic root with positive real part (`exists_cubic_root_re_pos_of_violation`). -/
@[tmio T, powerlib_foundation] theorem exists_root_re_pos_droopJacobian {M D ω a b c k : ℝ}
    (hM : 0 < M) (hω : 0 < ω)
    (h : D + M * ω * k < 0 ∨ k * a - b * c < 0 ∨
      D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c) < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix (droopJacobian M D ω a b c k) s).det = 0 ∧
      0 < s.re := by
  have hM0 := hM.ne'
  have hv : -(droopJacobian M D ω a b c k).trace < 0 ∨
      principalMinorSum (droopJacobian M D ω a b c k) < 0 ∨
      -(droopJacobian M D ω a b c k).det < 0 ∨
      -(droopJacobian M D ω a b c k).trace *
        principalMinorSum (droopJacobian M D ω a b c k) <
        -(droopJacobian M D ω a b c k).det := by
    rw [trace_droopJacobian hM0, principalMinorSum_droopJacobian hM0, det_droopJacobian hM0,
      neg_neg, neg_neg]
    rcases h with h | h | h
    · exact Or.inl (div_neg_of_neg_of_pos h hM)
    · exact Or.inr (Or.inr (Or.inl (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hω h) hM)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have e : (D + M * ω * k) / M * ((a + D * ω * k) / M) - ω * (k * a - b * c) / M =
          (D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c)) / M ^ 2 := by
        field_simp
        ring
      have : (D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c)) / M ^ 2 < 0 :=
        div_neg_of_neg_of_pos h (pow_pos hM 2)
      linarith
  obtain ⟨s, hs, hre⟩ := exists_cubic_root_re_pos_of_violation hv
  refine ⟨s, ?_, hre⟩
  rw [det_characteristicMatrix_fin_three']
  exact hs

/-- **Off the fold and the Hopf surface the Routh conditions decide.** For `M, ω > 0`,
`k a ≠ b c` and `D (a + D ω k + M ω² k²) + M ω b c ≠ 0`, either all three Routh conditions of the
droop-loop Jacobian hold, or one of them is strictly violated (with `C > 0` and `G > 0`, the
identity `G = (D + Mωk)(a + Dωk) − Mω C` excludes `D + M ω k = 0`). -/
@[tmio T, powerlib_foundation] theorem droopJacobian_routh_or_violation {M D ω a b c k : ℝ}
    (hM : 0 < M) (hω : 0 < ω) (hC : k * a - b * c ≠ 0)
    (hG : D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c) ≠ 0) :
    (0 < D + M * ω * k ∧ 0 < k * a - b * c ∧
        0 < D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c)) ∨
      (D + M * ω * k < 0 ∨ k * a - b * c < 0 ∨
        D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c) < 0) := by
  rcases hC.lt_or_gt with hC | hC
  · exact Or.inr (Or.inr (Or.inl hC))
  rcases hG.lt_or_gt with hG | hG
  · exact Or.inr (Or.inr (Or.inr hG))
  rcases lt_or_ge 0 (D + M * ω * k) with hA | hA
  · exact Or.inl ⟨hA, hC, hG⟩
  refine Or.inr (Or.inl (lt_of_le_of_ne hA fun h0 => ?_))
  have e : D * (a + D * ω * k + M * ω ^ 2 * k ^ 2) + M * ω * (b * c) =
      (D + M * ω * k) * (a + D * ω * k) - M * ω * (k * a - b * c) := by ring
  rw [e, h0, zero_mul, zero_sub] at hG
  nlinarith [mul_pos (mul_pos hM hω) hC]

/-- **Null vectors at the fold.** If `k a = b c`, then `(k, 0, c)` is a right and
`(D ω k/M, ω k, b/M)` a left null vector of the droop-loop Jacobian; their product is
`(D ω k² + b c)/M`. -/
@[tmio T, powerlib_foundation] theorem droopJacobian_null {M D ω a b c k : ℝ}
    (h : k * a - b * c = 0) :
    droopJacobian M D ω a b c k *ᵥ ![k, 0, c] = 0 ∧
      Matrix.vecMul ![D * ω * k / M, ω * k, b / M] (droopJacobian M D ω a b c k) = 0 := by
  constructor
  · ext i
    fin_cases i <;>
      simp [droopJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination (-1 / M) * h
  · ext j
    fin_cases j <;>
      simp [droopJacobian, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination (-ω / M) * h

end powerlib.Criteria
