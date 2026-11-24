import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import theorem.PH.PositiveReal
import theorem.Linear.Certificate

/-! # Which vector fields have a port-Hamiltonian form (foundation)

Necessary conditions for a given vector field to be the zero-input field of a nonlinear
port-Hamiltonian model with **constant** interconnection and dissipation matrices, and the exact
condition for a linear field to have a linear port-Hamiltonian form with positive definite
dissipation.

Scope.
* Generic: an arbitrary nonlinear port-Hamiltonian model `P : NonlinearModel n m`
  (`theorem/PH/Nonlinear.lean`), its zero-input field `f(x) = (J(x) − R(x)) ∇H(x)`, and an
  arbitrary real square matrix `A` with the linear pH state matrix `(J − R) Q`
  (`theorem/PH/Linear.lean`). No model; every statement is foundation (Rules §3).
* "Constant structure" means `J(x) = J₀`, `R(x) = R₀` for every state; `H` is only assumed
  differentiable with gradient field `dH`, as in `NonlinearModel`. The Jacobian of the field is
  supplied by the caller (`HasFDerivAt f (A x) x`).

Source: T-ph §1.10 (linear pH form `A = (J − R) Q`); the symmetry of second derivatives
(Schwarz–Clairaut; Mathlib `second_derivative_symmetric`); Khalil, *Nonlinear Systems*, Thm. 4.6
(Lyapunov equation of a Hurwitz matrix, LeanForControl
`IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` through
`Linear.nonempty_certificate_iff`).

Results.
* `hessian_symm`: the derivative of a gradient field is a symmetric matrix (Schwarz).
* Obligations of a constant structure `N = J₀ − R₀` (used to refute that a model's field has one):
  `NonlinearModel.exists_covector_of_det_eq_zero` (a singular `N` puts every value of the field in
  one hyperplane), `NonlinearModel.constStructure_hessian_symm` (for invertible `N`, `N⁻¹ A(x)` is
  the Hessian of `H`, hence symmetric at every state), `NonlinearModel.constStructure_inv_nonpos`
  (`vᵀ N⁻¹ v ≤ 0`).
* `exists_linearPH_posDef_iff`: a real matrix is `(J − R) Q` with `J` skew, `R ≻ 0`, `Q ≻ 0`
  exactly when it is Hurwitz. With `R ⪰ 0` only the closed half plane follows
  (`PH.phSpectral_det_ne_zero`, `theorem/PH/PositiveReal.lean`); exactly, a form with `R ⪰ 0`
  exists iff the matrix has a quadratic Lyapunov matrix `Q ≻ 0`, `Aᵀ Q + Q A ⪯ 0`
  (`exists_linearPH_posSemidef_iff`).

Family and connection conclusions.
* None: generic static facts. Models use them to decide whether their fields carry a pH structure
  (for example `theorem/GridTiedConverter/GFM/Port/VSMLPFPH.lean`).
-/

noncomputable section
namespace powerlib.PH
open Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State)

variable {n m : ℕ}

/-- **Symmetry of the Hessian.** If `dH` is the gradient field of `H` everywhere and `dH` has the
derivative `S` at `x`, then `S` is symmetric. -/
@[tmio T, powerlib_foundation] theorem hessian_symm {H : State n → ℝ} {dH : State n → State n}
    (hH : ∀ y, HasGradientAt H (dH y) y) {x : State n} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : HasFDerivAt dH (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) S) x) : Sᵀ = S := by
  have h1 : ∀ y, HasFDerivAt H ((innerSL ℝ (E := State n) : State n →L[ℝ] State n →L[ℝ] ℝ)
      (dH y)) y := fun y => by
    have h := (hH y).hasFDerivAt
    convert h using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
  have h2 : HasFDerivAt (fun y => (innerSL ℝ (E := State n) : State n →L[ℝ] State n →L[ℝ] ℝ)
      (dH y)) ((innerSL ℝ (E := State n) : State n →L[ℝ] State n →L[ℝ] ℝ).comp
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) S)) x :=
    (innerSL ℝ (E := State n) : State n →L[ℝ] State n →L[ℝ] ℝ).hasFDerivAt.comp x hS
  have key := second_derivative_symmetric h1 h2
  ext i j
  have hij := key (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply] at hij
  rw [real_inner_comm, inner_toEuclideanCLM, real_inner_comm, inner_toEuclideanCLM] at hij
  simpa [Matrix.mulVec_single_one, dotProduct_single_one] using hij.symm

namespace NonlinearModel

variable (P : NonlinearModel n m) {J₀ R₀ : Matrix (Fin n) (Fin n) ℝ}

/-- The zero-input field with constant structure `N = J₀ − R₀` is `N ∇H`. -/
@[tmio T, powerlib_foundation] private theorem ofLp_zeroInputField_const
    (hJ : ∀ x, P.J x = J₀) (hR : ∀ x, P.R x = R₀) (x : State n) :
    WithLp.ofLp (P.zeroInputField x) = (J₀ - R₀) *ᵥ WithLp.ofLp (P.dH x) := by
  simp [zeroInputField, field, hJ x, hR x]

/-- A singular constant structure `N = J₀ − R₀` puts every value of the zero-input field in one
hyperplane: some nonzero covector `a` has `aᵀ f(x) = 0` for every state. -/
@[tmio T, powerlib_foundation] theorem exists_covector_of_det_eq_zero (hJ : ∀ x, P.J x = J₀)
    (hR : ∀ x, P.R x = R₀) (hdet : (J₀ - R₀).det = 0) :
    ∃ a : Fin n → ℝ, a ≠ 0 ∧ ∀ x, a ⬝ᵥ WithLp.ofLp (P.zeroInputField x) = 0 := by
  obtain ⟨a, ha, hN⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  refine ⟨a, ha, fun x => ?_⟩
  rw [P.ofLp_zeroInputField_const hJ hR, dotProduct_mulVec, hN, zero_dotProduct]

/-- For an invertible constant structure `N = J₀ − R₀`, the gradient field is `N⁻¹ f`, so where
the zero-input field has the derivative `A(x)`, the matrix `N⁻¹ A(x)` is the Hessian of `H`, hence
symmetric (`hessian_symm`). -/
@[tmio T, powerlib_foundation] theorem constStructure_hessian_symm (hJ : ∀ x, P.J x = J₀)
    (hR : ∀ x, P.R x = R₀) (hdet : IsUnit (J₀ - R₀).det) {x : State n}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt P.zeroInputField (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x) :
    ((J₀ - R₀)⁻¹ * A)ᵀ = (J₀ - R₀)⁻¹ * A := by
  set G := (J₀ - R₀)⁻¹
  have hdH : P.dH = fun y => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) G
      (P.zeroInputField y) := by
    funext y
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM, P.ofLp_zeroInputField_const hJ hR, mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  have hS : HasFDerivAt P.dH (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (G * A)) x := by
    rw [hdH, map_mul]
    exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) G).hasFDerivAt.comp x hA
  exact hessian_symm P.hasGradient hS

/-- For an invertible constant structure `N = J₀ − R₀` (`J₀` skew, `R₀ ⪰ 0`), the inverse has a
negative semidefinite quadratic form: `vᵀ N⁻¹ v = −(N⁻¹ v)ᵀ R₀ (N⁻¹ v) ≤ 0`. -/
@[tmio T, powerlib_foundation] theorem constStructure_inv_nonpos (hJ : ∀ x, P.J x = J₀)
    (hR : ∀ x, P.R x = R₀) (hdet : IsUnit (J₀ - R₀).det) (v : Fin n → ℝ) :
    v ⬝ᵥ ((J₀ - R₀)⁻¹ *ᵥ v) ≤ 0 := by
  set y := (J₀ - R₀)⁻¹ *ᵥ v
  have hv : v = (J₀ - R₀) *ᵥ y := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hskew : y ⬝ᵥ (J₀ *ᵥ y) = 0 :=
    dotProduct_mulVec_self_eq_zero_of_skew (by rw [← hJ 0]; exact P.skew 0) y
  have hpsd : 0 ≤ y ⬝ᵥ (R₀ *ᵥ y) := by
    simpa using (hR 0 ▸ P.dissipation_posSemidef 0).dotProduct_mulVec_nonneg y
  rw [hv, dotProduct_comm, sub_mulVec, dotProduct_sub, hskew]
  linarith

end NonlinearModel

/-- **Linear pH form with positive definite dissipation.** A real matrix is `(J − R) Q` with `J`
skew, `R ≻ 0` and `Q ≻ 0` exactly when it is Hurwitz. Forward: `Q` is a strict Lyapunov matrix,
`wᵀ Q A w = −(Q w)ᵀ R (Q w) < 0` (`Criteria.re_neg_of_lyapunov`); backward: a Lyapunov
certificate `Aᵀ P + P A = −1` (`Linear.nonempty_certificate_iff`) gives `Q = P` and
`J − R = A P⁻¹`. -/
@[tmio T, powerlib_foundation] theorem exists_linearPH_posDef_iff
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ J R Q : Matrix (Fin n) (Fin n) ℝ, Jᵀ = -J ∧ R.PosDef ∧ Q.PosDef ∧
      linearStateMatrix J R Q = A) ↔ LinearSystems.IsHurwitz A := by
  constructor
  · rintro ⟨J, R, Q, hJ, hR, hQ, rfl⟩
    have hQt : Qᵀ = Q := hQ.isHermitian.isSymm
    intro μ v hv heig
    rw [neg_zero]
    refine Criteria.re_neg_of_lyapunov hQt (fun w hw => by
      simpa only [star_trivial] using hQ.dotProduct_mulVec_pos hw) (fun w hw => ?_) hv heig
    have hQw : Q *ᵥ w ≠ 0 := fun h => by
      have := hQ.dotProduct_mulVec_pos hw
      rw [h, dotProduct_zero] at this
      exact lt_irrefl _ this
    have hpos : 0 < (Q *ᵥ w) ⬝ᵥ (R *ᵥ (Q *ᵥ w)) := by
      simpa only [star_trivial] using hR.dotProduct_mulVec_pos hQw
    have hskew := dotProduct_mulVec_self_eq_zero_of_skew hJ (Q *ᵥ w)
    have e : w ⬝ᵥ (Q *ᵥ (linearStateMatrix J R Q *ᵥ w)) =
        (Q *ᵥ w) ⬝ᵥ (J *ᵥ (Q *ᵥ w)) - (Q *ᵥ w) ⬝ᵥ (R *ᵥ (Q *ᵥ w)) := by
      rw [Criteria.dotProduct_mulVec_comm_of_symm hQt, linearStateMatrix, ← mulVec_mulVec,
        sub_mulVec, sub_dotProduct, dotProduct_comm _ (Q *ᵥ w), dotProduct_comm (R *ᵥ _)]
    rw [e, hskew]
    linarith
  · intro hA
    obtain ⟨c⟩ := (Linear.nonempty_certificate_iff A).mpr hA
    have hPd : c.P.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos
      (by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, c.symmetric])
      (fun w hw => by simpa only [star_trivial] using c.positive w hw)
    have hdet : IsUnit c.P.det := (Matrix.isUnit_iff_isUnit_det _).mp hPd.isUnit
    set N := A * c.P⁻¹
    have hPit : (c.P⁻¹)ᵀ = c.P⁻¹ := by rw [transpose_nonsing_inv, c.symmetric]
    refine ⟨(1 / 2 : ℝ) • (N - Nᵀ), -((1 / 2 : ℝ) • (N + Nᵀ)), c.P, ?_, ?_, hPd, ?_⟩
    · rw [transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]
    · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun w hw => ?_
      · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_neg, transpose_smul,
          transpose_add, transpose_transpose, add_comm]
      · set y := c.P⁻¹ *ᵥ w
        have hy : y ≠ 0 := fun h => hw (by
          rw [← one_mulVec w, ← Matrix.mul_nonsing_inv _ hdet, ← mulVec_mulVec]
          change c.P *ᵥ y = 0
          rw [h, mulVec_zero])
        have hwy : w = c.P *ᵥ y := by
          rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
        have hNw : w ⬝ᵥ (N *ᵥ w) = y ⬝ᵥ (c.P *ᵥ (A *ᵥ y)) := by
          rw [show N *ᵥ w = A *ᵥ y by rw [← mulVec_mulVec]]
          rw [Criteria.dotProduct_mulVec_comm_of_symm c.symmetric, hwy, dotProduct_comm]
        have hNt : w ⬝ᵥ (Nᵀ *ᵥ w) = w ⬝ᵥ (N *ᵥ w) := by
          rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
        have hyy : 0 < y ⬝ᵥ y := lt_of_le_of_ne
          (Finset.sum_nonneg fun j _ => mul_self_nonneg (y j))
          (Ne.symm (mt dotProduct_self_eq_zero.mp hy))
        have hL := Linear.quadratic_lyapunov c.symmetric c.lyapunov y
        rw [star_trivial, neg_mulVec, dotProduct_neg, smul_mulVec, dotProduct_smul, add_mulVec,
          dotProduct_add, hNt, hNw, hL, smul_eq_mul]
        linarith
    · simp only [linearStateMatrix, N]
      rw [sub_neg_eq_add, ← smul_add, show N - Nᵀ + (N + Nᵀ) = (2 : ℝ) • N by
        rw [two_smul]; abel, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

/-- **Linear pH form with positive semidefinite dissipation.** A real matrix is `(J − R) Q` with
`J` skew, `R ⪰ 0` and `Q ≻ 0` exactly when it has a quadratic Lyapunov matrix: `Q ≻ 0` with
`Aᵀ Q + Q A ⪯ 0`. Forward: `Aᵀ Q + Q A = −2 Q R Q`; backward: `J − R = A Q⁻¹`, whose symmetric
part is `½ Q⁻¹ (Aᵀ Q + Q A) Q⁻¹`. -/
@[tmio T, powerlib_foundation] theorem exists_linearPH_posSemidef_iff
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ J R Q : Matrix (Fin n) (Fin n) ℝ, Jᵀ = -J ∧ R.PosSemidef ∧ Q.PosDef ∧
      linearStateMatrix J R Q = A) ↔
      ∃ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosDef ∧ (-(Aᵀ * Q + Q * A)).PosSemidef := by
  constructor
  · rintro ⟨J, R, Q, hJ, hR, hQ, rfl⟩
    have hQt : Qᵀ = Q := hQ.isHermitian.isSymm
    have hRt : Rᵀ = R := hR.isHermitian.isSymm
    refine ⟨Q, hQ, ?_⟩
    have e : -((linearStateMatrix J R Q)ᵀ * Q + Q * linearStateMatrix J R Q) =
        Qᴴ * R * Q + Qᴴ * R * Q := by
      rw [conjTranspose_eq_transpose_of_trivial, hQt]
      simp only [linearStateMatrix, transpose_mul, transpose_sub, hJ, hQt, hRt]
      noncomm_ring
    rw [e]
    exact (hR.conjTranspose_mul_mul_same Q).add (hR.conjTranspose_mul_mul_same Q)
  · rintro ⟨Q, hQ, hS⟩
    have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit
    have hQt : Qᵀ = Q := hQ.isHermitian.isSymm
    have hPit : (Q⁻¹)ᵀ = Q⁻¹ := by rw [transpose_nonsing_inv, hQt]
    set N := A * Q⁻¹
    refine ⟨(1 / 2 : ℝ) • (N - Nᵀ), -((1 / 2 : ℝ) • (N + Nᵀ)), Q, ?_, ?_, hQ, ?_⟩
    · rw [transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]
    · have e : -((1 / 2 : ℝ) • (N + Nᵀ)) =
          (1 / 2 : ℝ) • ((Q⁻¹)ᴴ * -(Aᵀ * Q + Q * A) * Q⁻¹) := by
        rw [conjTranspose_eq_transpose_of_trivial, hPit]
        have h1 : Q⁻¹ * -(Aᵀ * Q + Q * A) * Q⁻¹ =
            -(Q⁻¹ * Aᵀ * (Q * Q⁻¹) + Q⁻¹ * Q * (A * Q⁻¹)) := by noncomm_ring
        rw [h1, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one,
          Matrix.one_mul, ← smul_neg]
        congr 1
        simp only [N, transpose_mul, hPit]
        abel
      rw [e]
      exact (hS.conjTranspose_mul_mul_same Q⁻¹).smul (by norm_num)
    · simp only [linearStateMatrix, N]
      rw [sub_neg_eq_add, ← smul_add, show N - Nᵀ + (N + Nᵀ) = (2 : ℝ) • N by
        rw [two_smul]; abel, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

end powerlib.PH
