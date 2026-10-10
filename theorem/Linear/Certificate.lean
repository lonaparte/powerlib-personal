import theorem.Linear.Stability

/-! # Lyapunov certificates

A certificate is the evidence a synthesizer returns for a state matrix `A`: a symmetric matrix
`P`, positive on every nonzero state, solving `Aᵀ P + P A = -1`. It is proof-relevant data,
indexed by the exact matrix it was produced for. Its meaning is fixed once: a certificate exists
exactly when `A` is Hurwitz, hence exactly when every attractive sentence holds. Families supply
synthesizers that construct certificates; they do not restate what a certificate proves. -/

noncomputable section

namespace powerlib.Linear

open Matrix LinearSystems

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A quadratic Lyapunov certificate for the state matrix `A`. -/
structure Certificate (A : Matrix (Fin n) (Fin n) ℝ) where
  /-- The quadratic form. -/
  P : Matrix (Fin n) (Fin n) ℝ
  symmetric : Pᵀ = P
  positive : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x)
  lyapunov : Aᵀ * P + P * A = -1

/-- For a symmetric `P`, the quadratic form of `Aᵀ P + P A` is twice that of `P A`. -/
@[powerlib_foundation] theorem quadratic_sym {A P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P)
    (z : Fin n → ℝ) : z ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ z) = 2 * (z ⬝ᵥ (P *ᵥ (A *ᵥ z))) := by
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add]
  have h1 : z ⬝ᵥ (Aᵀ *ᵥ (P *ᵥ z)) = (A *ᵥ z) ⬝ᵥ (P *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h2 : z ⬝ᵥ (P *ᵥ (A *ᵥ z)) = (P *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    conv_lhs => rw [← hP]
    rw [Matrix.vecMul_transpose]
  rw [h1, h2, dotProduct_comm (A *ᵥ z)]
  ring

@[powerlib_foundation] theorem quadratic_lyapunov {A P : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pᵀ = P) (hL : Aᵀ * P + P * A = -1) (z : Fin n → ℝ) :
    2 * (z ⬝ᵥ (P *ᵥ (A *ᵥ z))) = -(z ⬝ᵥ z) := by
  rw [← quadratic_sym hP, hL, Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]

/-- A certificate proves the matrix Hurwitz. -/
@[powerlib_foundation] theorem Certificate.isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) : IsHurwitz A := by
  intro μ v hv heig
  let x : Fin n → ℝ := fun j => (v j).re
  let y : Fin n → ℝ := fun j => (v j).im
  have hcomp (j : Fin n) : ∑ k, (A j k : ℂ) * v k = μ * v j := by
    have hj := congrFun heig j
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hj
  have hAx : A *ᵥ x = μ.re • x - μ.im • y := by
    funext j
    have h := congrArg Complex.re (hcomp j)
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at h
    simp only [Matrix.mulVec, dotProduct, x, y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hAy : A *ᵥ y = μ.im • x + μ.re • y := by
    funext j
    have h := congrArg Complex.im (hcomp j)
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] at h
    simp only [Matrix.mulVec, dotProduct, x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hx := quadratic_lyapunov c.symmetric c.lyapunov x
  have hy := quadratic_lyapunov c.symmetric c.lyapunov y
  rw [hAx, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hx
  rw [hAy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hy
  have hcross : y ⬝ᵥ (c.P *ᵥ x) = x ⬝ᵥ (c.P *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
    congr 1
    conv_lhs => rw [← c.symmetric]
    rw [Matrix.vecMul_transpose]
  rw [hcross] at hy
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext j
    apply Complex.ext
    · exact congrFun h.1 j
    · exact congrFun h.2 j
  have hq : 0 < x ⬝ᵥ (c.P *ᵥ x) + y ⬝ᵥ (c.P *ᵥ y) := by
    have hqx : 0 ≤ x ⬝ᵥ (c.P *ᵥ x) := by
      by_cases h0 : x = 0
      · simp [h0]
      · exact (c.positive x h0).le
    have hqy : 0 ≤ y ⬝ᵥ (c.P *ᵥ y) := by
      by_cases h0 : y = 0
      · simp [h0]
      · exact (c.positive y h0).le
    rcases hxy with h | h
    · linarith [c.positive x h]
    · linarith [c.positive y h]
  have hnn : 0 ≤ x ⬝ᵥ x + y ⬝ᵥ y := by
    have h1 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
    have h2 : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
    linarith
  have hsum : 2 * μ.re * (x ⬝ᵥ (c.P *ᵥ x) + y ⬝ᵥ (c.P *ᵥ y)) = -(x ⬝ᵥ x + y ⬝ᵥ y) := by
    linarith
  have : μ.re < 0 := by
    by_contra hμ
    push Not at hμ
    have : 0 ≤ 2 * μ.re * (x ⬝ᵥ (c.P *ᵥ x) + y ⬝ᵥ (c.P *ᵥ y)) := by positivity
    have hpos : 0 < x ⬝ᵥ x + y ⬝ᵥ y := by
      rcases hxy with h | h
      · have : 0 < x ⬝ᵥ x := by
          obtain ⟨j, hj⟩ := Function.ne_iff.mp h
          exact Finset.sum_pos' (fun k _ => mul_self_nonneg (x k))
            ⟨j, Finset.mem_univ _, mul_self_pos.mpr hj⟩
        have : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
        linarith
      · have : 0 < y ⬝ᵥ y := by
          obtain ⟨j, hj⟩ := Function.ne_iff.mp h
          exact Finset.sum_pos' (fun k _ => mul_self_nonneg (y k))
            ⟨j, Finset.mem_univ _, mul_self_pos.mpr hj⟩
        have : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
        linarith
    linarith
  simpa using this

/-- A certificate exists exactly when the matrix is Hurwitz (LeanForControl's Lyapunov
equation for the converse). -/
@[powerlib_foundation] theorem nonempty_certificate_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    Nonempty (Certificate A) ↔ IsHurwitz A := by
  refine ⟨fun ⟨c⟩ => c.isHurwitz, fun hA => ?_⟩
  obtain ⟨P, hP, hL, -⟩ := hA.exists_posDef_unique_solution_continuous_lyapunov 1 PosDef.one
  refine ⟨⟨P, ?_, fun x hx => ?_, ?_⟩⟩
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq
  · simpa using hP.dotProduct_mulVec_pos hx
  · have h : P * A + Aᵀ * P = -1 := hL
    rw [add_comm]
    exact h

/-- A certificate proves every attractive sentence at every centre. -/
@[powerlib_foundation] theorem Certificate.holds {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e : ℝⁿ) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (affineLinearVectorField A e) e :=
  (holds_iff_isHurwitz e hP).mpr c.isHurwitz

end powerlib.Linear
