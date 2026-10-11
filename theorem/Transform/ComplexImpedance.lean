import theorem.Transform.Park
import theorem.LTI
import Mathlib.RingTheory.Complex

/-! Complex-symmetric dq matrices, complex transfer functions and the dq ↔ αβ frequency shift
(foundation).

Source: work-sync `theory/T-impedance-modeling.md` §1.4 (complex transfer function
`Z(s) = Z_dd(s) + j Z_qd(s)` under `Z_dd = Z_qq`, `Z_dq = −Z_qd`) and §2.2 (frequency shift
`s ↔ s ± jω₁` between dq and αβ descriptions).

* `complexSymm a b = [[a, −b], [b, a]]` over any commutative ring. Over `ℝ` it is the matrix of
  multiplication by `a + jb` (`complexSymm_eq_leftMulMatrix` wraps Mathlib's
  `Algebra.leftMulMatrix_complex`). Over `ℂ` (entries evaluated at a complex Laplace variable)
  `toSISO M = M₀₀ + j M₁₀` is multiplicative on complex-symmetric matrices.
* `transfer_complexSymm`: a real 2 × 2 LTI model whose four matrices are complex-symmetric has
  a complex-symmetric transfer matrix, and its SISO complex transfer function is
  `(c + jd)(s − (a + jb))⁻¹(p + jq) + (e + jf)`, at every `s` that is not a pole of the real
  model. (At the conjugate point `s = a − jb` the real resolvent is singular, so the premise
  is needed.)
* `CModel` is a complex-coefficient state-space model. `CModel.shift ω₁` adds `jω₁ I` to the
  state matrix. `transfer_shift`: `G_{shift}(s) = G(s − jω₁)`. `isTrajectory_shift`: if `z`
  solves the model with input `u`, then `e^{jω₁t} z` solves the shifted model with input
  `e^{jω₁t} u`, and the output is multiplied by `e^{jω₁t}`. With `A` the complex dq model and
  `ω₁` the frame speed, the shifted model is the αβ description, i.e.
  `G_{αβ}(s) = G_{dq}(s − jω₁)`.

These are algebraic / calculus identities; no stability claim is made here.
-/

noncomputable section
namespace powerlib.Transform
open Matrix

/-! ## Complex-symmetric 2 × 2 matrices -/

/-- Complex-symmetric 2 × 2 matrix `[[a, −b], [b, a]]`. -/
def complexSymm {R : Type*} [CommRing R] (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a, -b; b, a]

/-- `M` is complex symmetric: `M_dd = M_qq` and `M_dq = −M_qd`. -/
def IsComplexSymm {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) : Prop :=
  M 1 1 = M 0 0 ∧ M 0 1 = -M 1 0

/-- SISO complex form `M_dd + j M_qd` of a 2 × 2 complex matrix. -/
def toSISO (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := M 0 0 + Complex.I * M 1 0

variable {R : Type*} [CommRing R]

@[powerlib_foundation] theorem isComplexSymm_iff (M : Matrix (Fin 2) (Fin 2) R) :
    IsComplexSymm M ↔ M = complexSymm (M 0 0) (M 1 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm, h1, h2]
  · intro h
    rw [h]; simp [IsComplexSymm, complexSymm]

@[powerlib_foundation] theorem isComplexSymm_complexSymm (a b : R) :
    IsComplexSymm (complexSymm a b) := by
  simp [IsComplexSymm, complexSymm]

@[powerlib_foundation] theorem complexSymm_mul (a b c d : R) :
    complexSymm a b * complexSymm c d = complexSymm (a * c - b * d) (a * d + b * c) := by
  simp only [complexSymm, mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

@[powerlib_foundation] theorem complexSymm_add (a b c d : R) :
    complexSymm a b + complexSymm c d = complexSymm (a + c) (b + d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]; ring

@[powerlib_foundation] theorem complexSymm_sub (a b c d : R) :
    complexSymm a b - complexSymm c d = complexSymm (a - c) (b - d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]; ring

@[powerlib_foundation] theorem smul_one_eq_complexSymm (s : R) :
    s • (1 : Matrix (Fin 2) (Fin 2) R) = complexSymm s 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]

@[powerlib_foundation] theorem det_complexSymm (a b : R) : (complexSymm a b).det = a ^ 2 + b ^ 2 := by
  rw [complexSymm, det_fin_two_of]; ring

@[powerlib_foundation] theorem complexSymm_map {S : Type*} [CommRing S] (f : R →+* S) (a b : R) :
    (complexSymm a b).map f = complexSymm (f a) (f b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]

/-- C wrapper: the real complex-symmetric matrix is Mathlib's left-multiplication matrix of
`a + jb` in the basis `(1, j)` (`Algebra.leftMulMatrix_complex`). -/
@[powerlib_foundation] theorem complexSymm_eq_leftMulMatrix (z : ℂ) :
    complexSymm z.re z.im = Algebra.leftMulMatrix Complex.basisOneI z :=
  (Algebra.leftMulMatrix_complex z).symm

/-- Real action: `[[a, −b], [b, a]] x` is `(a + jb) (x_d + j x_q)` in complex form. -/
@[powerlib_foundation] theorem toComplex_complexSymm_mulVec (a b : ℝ) (x : Fin 2 → ℝ) :
    toComplex (complexSymm a b *ᵥ x) = (⟨a, b⟩ : ℂ) * toComplex x := by
  apply Complex.ext <;>
    simp [toComplex, complexSymm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Frequency-domain action on complex phasors: the positive-sequence combination
`Y_d + j Y_q` equals `(α + jβ)(U_d + j U_q)`. -/
@[powerlib_foundation] theorem complexSymm_mulVec_pos (α β : ℂ) (u : Fin 2 → ℂ) :
    (complexSymm α β *ᵥ u) 0 + Complex.I * (complexSymm α β *ᵥ u) 1 =
      (α + Complex.I * β) * (u 0 + Complex.I * u 1) := by
  simp [complexSymm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (-(β * u 1)) * Complex.I_sq

/-- The negative-sequence combination `Y_d − j Y_q` sees `α − jβ`. -/
@[powerlib_foundation] theorem complexSymm_mulVec_neg (α β : ℂ) (u : Fin 2 → ℂ) :
    (complexSymm α β *ᵥ u) 0 - Complex.I * (complexSymm α β *ᵥ u) 1 =
      (α - Complex.I * β) * (u 0 - Complex.I * u 1) := by
  simp [complexSymm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (-(β * u 1)) * Complex.I_sq

@[simp, powerlib_foundation] theorem toSISO_complexSymm (α β : ℂ) :
    toSISO (complexSymm α β) = α + Complex.I * β := by
  simp [toSISO, complexSymm]

@[powerlib_foundation] theorem IsComplexSymm.mul {M N : Matrix (Fin 2) (Fin 2) R}
    (hM : IsComplexSymm M) (hN : IsComplexSymm N) : IsComplexSymm (M * N) := by
  rw [isComplexSymm_iff] at hM hN
  rw [hM, hN, complexSymm_mul]; exact isComplexSymm_complexSymm _ _

@[powerlib_foundation] theorem IsComplexSymm.add {M N : Matrix (Fin 2) (Fin 2) R}
    (hM : IsComplexSymm M) (hN : IsComplexSymm N) : IsComplexSymm (M + N) := by
  rw [isComplexSymm_iff] at hM hN
  rw [hM, hN, complexSymm_add]; exact isComplexSymm_complexSymm _ _

/-- `toSISO` is multiplicative on complex-symmetric matrices. -/
@[powerlib_foundation] theorem toSISO_mul {M N : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : IsComplexSymm M) (hN : IsComplexSymm N) : toSISO (M * N) = toSISO M * toSISO N := by
  rw [isComplexSymm_iff] at hM hN
  rw [hM, hN, complexSymm_mul]
  simp only [toSISO_complexSymm]
  linear_combination (-(M 1 0 * N 1 0)) * Complex.I_sq

@[powerlib_foundation] theorem toSISO_add (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    toSISO (M + N) = toSISO M + toSISO N := by
  simp [toSISO]; ring

/-- Inverse of a nonsingular complex-symmetric matrix. -/
@[powerlib_foundation] theorem complexSymm_inv {α β : ℂ} (h : α ^ 2 + β ^ 2 ≠ 0) :
    (complexSymm α β)⁻¹ = complexSymm (α / (α ^ 2 + β ^ 2)) (-β / (α ^ 2 + β ^ 2)) := by
  apply Matrix.inv_eq_right_inv
  rw [complexSymm_mul, show (1 : Matrix (Fin 2) (Fin 2) ℂ) = complexSymm 1 0 by
    simpa using smul_one_eq_complexSymm (1 : ℂ)]
  congr 1
  · field_simp; ring
  · field_simp; ring

@[powerlib_foundation] theorem sq_add_sq_eq_mul (α β : ℂ) :
    α ^ 2 + β ^ 2 = (α + Complex.I * β) * (α - Complex.I * β) := by
  linear_combination (β ^ 2) * Complex.I_sq

/-- `toSISO` of the inverse is the inverse of `toSISO`. -/
@[powerlib_foundation] theorem toSISO_complexSymm_inv {α β : ℂ} (h : α ^ 2 + β ^ 2 ≠ 0) :
    toSISO (complexSymm α β)⁻¹ = (α + Complex.I * β)⁻¹ := by
  rw [complexSymm_inv h, toSISO_complexSymm]
  rw [sq_add_sq_eq_mul] at h ⊢
  have h1 : α + Complex.I * β ≠ 0 := left_ne_zero_of_mul h
  have h2 : α - Complex.I * β ≠ 0 := right_ne_zero_of_mul h
  field_simp
  ring

/-! ## Complex transfer function of a complex-symmetric real model (§1.4) -/

/-- Real 2 × 2 LTI model whose four matrices are complex symmetric, i.e. one complex state
`x_d + j x_q`: `A ↔ a + jb`, `B ↔ p + jq`, `C ↔ c + jd`, `D ↔ e + jf`. -/
def csModel (a b p q c d e f : ℝ) : LTI.Model (Fin 2) (Fin 2) :=
  ⟨complexSymm a b, complexSymm p q, complexSymm c d, complexSymm e f⟩

@[powerlib_foundation] private lemma complexify_complexSymm (a b : ℝ) :
    LTI.complexify (complexSymm a b) = complexSymm (a : ℂ) (b : ℂ) :=
  complexSymm_map (algebraMap ℝ ℂ) a b

@[powerlib_foundation] theorem characteristicMatrix_complexSymm (a b : ℝ) (s : ℂ) :
    LTI.characteristicMatrix (complexSymm a b) s = complexSymm (s - a) (-b) := by
  rw [LTI.characteristicMatrix, show (complexSymm a b).map (algebraMap ℝ ℂ) =
      LTI.complexify (complexSymm a b) from rfl, complexify_complexSymm,
    smul_one_eq_complexSymm, complexSymm_sub, zero_sub]

/-- The transfer matrix of a complex-symmetric real model is complex symmetric, and its SISO
complex form is the complex transfer function `(c + jd)(s − (a + jb))⁻¹(p + jq) + (e + jf)`
(`T-impedance-modeling.md` §1.4: `Z(s) = Z_dd(s) + j Z_qd(s)`), at every `s` that is not an
eigenvalue of the real state matrix. -/
@[powerlib_foundation] theorem transfer_csModel (a b p q c d e f : ℝ) {s : ℂ}
    (hs : (LTI.characteristicMatrix (complexSymm a b) s).det ≠ 0) :
    IsComplexSymm (LTI.transfer (csModel a b p q c d e f) s) ∧
      toSISO (LTI.transfer (csModel a b p q c d e f) s) =
        (c + Complex.I * d) * (s - (a + Complex.I * b))⁻¹ * (p + Complex.I * q) +
          (e + Complex.I * f) := by
  rw [characteristicMatrix_complexSymm, det_complexSymm] at hs
  have hT : LTI.transfer (csModel a b p q c d e f) s =
      complexSymm (c : ℂ) d * (complexSymm (s - a) (-b))⁻¹ * complexSymm (p : ℂ) q +
        complexSymm (e : ℂ) f := by
    simp only [LTI.transfer, csModel, complexify_complexSymm, characteristicMatrix_complexSymm]
  have hinv : IsComplexSymm (complexSymm (s - a) (-b))⁻¹ := by
    rw [complexSymm_inv hs]; exact isComplexSymm_complexSymm _ _
  rw [hT]
  refine ⟨((isComplexSymm_complexSymm _ _).mul hinv |>.mul
    (isComplexSymm_complexSymm _ _)).add (isComplexSymm_complexSymm _ _), ?_⟩
  rw [toSISO_add, toSISO_mul ((isComplexSymm_complexSymm _ _).mul hinv)
    (isComplexSymm_complexSymm _ _), toSISO_mul (isComplexSymm_complexSymm _ _) hinv,
    toSISO_complexSymm_inv hs]
  simp only [toSISO_complexSymm]
  congr 3
  ring

/-! ## Complex-coefficient models and the frequency shift (§2.2) -/

/-- Complex-coefficient continuous-time state-space model `ż = A z + B u`, `y = C z + D u`. -/
@[ext] structure CModel (ι κ : Type*) where
  A : Matrix ι ι ℂ
  B : Matrix ι κ ℂ
  C : Matrix κ ι ℂ
  D : Matrix κ κ ℂ

namespace CModel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Transfer matrix `C (sI − A)⁻¹ B + D`. -/
def transfer (m : CModel ι κ) (s : ℂ) : Matrix κ κ ℂ :=
  m.C * (s • (1 : Matrix ι ι ℂ) - m.A)⁻¹ * m.B + m.D

/-- Frame shift by `ω₁`: state matrix `A + jω₁ I`. -/
def shift (ω₁ : ℝ) (m : CModel ι κ) : CModel ι κ :=
  ⟨m.A + ((ω₁ : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ), m.B, m.C, m.D⟩

/-- Solutions with input `u`. -/
def IsTrajectory (m : CModel ι κ) (u : ℝ → κ → ℂ) (z : ℝ → ι → ℂ) : Prop :=
  ∀ t, HasDerivAt z (m.A *ᵥ z t + m.B *ᵥ u t) t

/-- Output map. -/
def output (m : CModel ι κ) (z : ι → ℂ) (u : κ → ℂ) : κ → ℂ := m.C *ᵥ z + m.D *ᵥ u

omit [Fintype κ] in
/-- Frequency shift: `G_{shift ω₁}(s) = G(s − jω₁)`. -/
@[powerlib_foundation] theorem transfer_shift (m : CModel ι κ) (ω₁ : ℝ) (s : ℂ) :
    (m.shift ω₁).transfer s = m.transfer (s - (ω₁ : ℂ) * Complex.I) := by
  simp only [transfer, shift]
  congr 3
  rw [sub_smul, sub_add_eq_sub_sub, sub_right_comm]

/-- Rotating phasor `e^{jω₁ t}`. -/
def rotor (ω₁ t : ℝ) : ℂ := Complex.exp ((t : ℂ) * ((ω₁ : ℂ) * Complex.I))

@[powerlib_foundation] theorem hasDerivAt_rotor (ω₁ t : ℝ) :
    HasDerivAt (rotor ω₁) (rotor ω₁ t * ((ω₁ : ℂ) * Complex.I)) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.mul_const ((ω₁ : ℂ) * Complex.I)).cexp
  unfold rotor
  simp only [id, Complex.ofReal_one, one_mul] at h
  exact h

/-- Time-domain form of the shift: if `z` solves `m` with input `u`, then `e^{jω₁t} z` solves
the shifted model with input `e^{jω₁t} u` (dq → αβ when `m` is the complex dq model). -/
@[powerlib_foundation] theorem isTrajectory_shift {m : CModel ι κ} {u : ℝ → κ → ℂ}
    {z : ℝ → ι → ℂ} (ω₁ : ℝ) (h : m.IsTrajectory u z) :
    (m.shift ω₁).IsTrajectory (fun t => rotor ω₁ t • u t) (fun t => rotor ω₁ t • z t) := by
  intro t
  have hd := (hasDerivAt_rotor ω₁ t).smul (h t)
  convert hd using 1
  simp only [shift, Matrix.add_mulVec, Matrix.mulVec_smul, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_add, smul_smul]
  abel

/-- The output of the shifted solution is the shifted output. -/
@[powerlib_foundation] theorem output_shift (m : CModel ι κ) (ω₁ : ℝ) (c : ℂ) (z : ι → ℂ)
    (u : κ → ℂ) : (m.shift ω₁).output (c • z) (c • u) = c • m.output z u := by
  simp [output, shift, Matrix.mulVec_smul, smul_add]

/-- Embedding of a real LTI model. -/
def ofReal (m : LTI.Model ι κ) : CModel ι κ :=
  ⟨LTI.complexify m.A, LTI.complexify m.B, LTI.complexify m.C, LTI.complexify m.D⟩

omit [Fintype κ] in
@[powerlib_foundation] theorem transfer_ofReal (m : LTI.Model ι κ) (s : ℂ) :
    (ofReal m).transfer s = LTI.transfer m s := rfl

end CModel

end powerlib.Transform
