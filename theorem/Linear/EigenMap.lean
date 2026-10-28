import theorem.Linear.Transfer
import theorem.LTI.Discrete

/-! # Eigenvalues of images of a matrix (foundation)

The eigenvalues of a matrix built from a real square matrix `A` are images of the eigenvalues of
`A`: `p(λ)` for a polynomial image `p(A)`, `(α λ + β)/(γ λ + δ)` for a Möbius image, and the same
eigenvalues for a matrix with the same characteristic polynomial. Stability of the image (Hurwitz,
spectral or Schur stability) is then a condition on the eigenvalues of `A`.

Scope.
* Generic linear algebra, independent of any model: real square matrices on a finite index type,
  read through their complexification `Linear.complexify`. Spectra are read through complex
  eigenpairs `(μ, v)`, `v ≠ 0`, `complexify A *ᵥ v = μ • v`, the form of LeanForControl's
  `IsHurwitz` and of `LTI.SchurStable`, or through the characteristic matrix
  (`Linear.SpectrallyStable`, `spectrallyStable_iff_forall_eigen`).
* A Möbius image of `A` is any `M` with `(γ A + δ) M = α A + β` (real coefficients,
  `α δ − β γ ≠ 0`): positive scalings `c A` (time bases), shifts `A − c`, and the one-step matrices
  `1 + hA`, `(1 − hA)⁻¹`, `(1 − hA/2)⁻¹ (1 + hA/2)` of forward Euler, backward Euler and the
  trapezoidal rule. Eigenvectors of a Möbius image are eigenvectors of `A`, so its eigenvalues are
  exactly the images; for a polynomial image only the forward direction is stated.
* Excluded: the exponential `e^{TA}` (`theorem/Periodic/LTI.lean`), and rational images of higher
  degree.

Source: standard spectral mapping for polynomial and Möbius images of a matrix; work-sync
`theory/T-numerical-integration.md` §1.3, §2.7 (the recursion `x_{k+1} = R(hA) x_k`),
`theory/T-PU.md` §1.6 (a time base scales the spectrum).

Results.
* Polynomial images: `mulVec_aeval_of_eigen` (an eigenpair `(μ, v)` of `M` gives `(p(μ), v)` for
  `p(M)`, over any commutative ring), `mulVec_pow_of_eigen`.
* Möbius images: `eigen_mobius` (an eigenpair `(λ, v)` of `A` gives `γ λ + δ ≠ 0` and the eigenpair
  `((α λ + β)/(γ λ + δ), v)` of `M`, when `γ A + δ` is invertible), `exists_eigen_of_mobius` (every
  eigenpair of `M` is such an image, when `α δ − β γ ≠ 0`), and `forall_eigen_mobius_iff`: a
  property holds for every eigenvalue of `M` exactly when it holds for the image of every
  eigenvalue of `A`. `isUnit_det_affine_of_forall_eigen`: `γ A + δ` is invertible when no eigenvalue
  has `γ λ + δ = 0`. Instances: `forall_eigen_smul_iff` (scaling), `isHurwitz_mobius_iff`,
  `schurStable_mobius_iff`, `isHurwitz_smul_iff` (positive scaling keeps the Hurwitz property).
* Characteristic polynomials: `spectrallyStable_iff_forall_eigen`,
  `spectrallyStable_congr_charpoly` (matrices with the same characteristic polynomial, possibly on
  different index types, are spectrally stable together), `isHurwitz_congr_charpoly`;
  `charpoly_conj` (`S T = 1` gives `χ(T A S) = χ(A)`), `spectrallyStable_conj`,
  `isHurwitz_transpose_iff`.

Family and connection conclusions.
* None: static facts about matrices, used by `theorem/Transform/Rebase.lean`,
  `theorem/LTI/Sampling.lean`, `theorem/LTI/Decay.lean`, `theorem/Numerics/LinearSchemes.lean` and
  `theorem/Numerics/MethodOfLines.lean`.
-/

noncomputable section

namespace powerlib.Linear

open Matrix Polynomial LinearSystems

/-! ## Polynomial images -/

section Polynomial

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- An eigenpair `(μ, v)` of `M` is an eigenpair `(p(μ), v)` of every polynomial image `p(M)`. -/
@[tmio T, powerlib_foundation] theorem mulVec_aeval_of_eigen {M : Matrix ι ι R} {μ : R} {v : ι → R}
    (h : M *ᵥ v = μ • v) (p : R[X]) : aeval M p *ᵥ v = p.eval μ • v := by
  induction p using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  | add p q hp hq => simp [Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih,
      smul_smul]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    ring_nf

/-- An eigenpair `(μ, v)` of `M` is an eigenpair `(μ^k, v)` of `M^k`. -/
@[powerlib_foundation] theorem mulVec_pow_of_eigen {M : Matrix ι ι R} {μ : R} {v : ι → R}
    (h : M *ᵥ v = μ • v) (k : ℕ) : (M ^ k) *ᵥ v = μ ^ k • v := by
  simpa using mulVec_aeval_of_eigen h (X ^ k)

end Polynomial

/-! ## Möbius images -/

section Mobius

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
@[powerlib_foundation] theorem complexify_mulVec_ofReal (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    complexify A *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
  funext i
  exact ((algebraMap ℝ ℂ).map_mulVec A v i).symm

omit [Fintype ι] in
@[powerlib_foundation] theorem complexify_affine (A : Matrix ι ι ℝ) (α β : ℝ) :
    complexify (α • A + β • 1) = (α : ℂ) • complexify A + (β : ℂ) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma affine_mulVec (N : Matrix ι ι ℂ) (a b : ℂ) (w : ι → ℂ) :
    (a • N + b • 1) *ᵥ w = a • (N *ᵥ w) + b • w := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

private lemma complexify_affine_mulVec {A : Matrix ι ι ℝ} {lam : ℂ} {v : ι → ℂ}
    (h : complexify A *ᵥ v = lam • v) (α β : ℝ) :
    complexify (α • A + β • 1) *ᵥ v = ((α : ℂ) * lam + β) • v := by
  rw [complexify_affine, affine_mulVec, h, smul_smul, add_smul]

private lemma isUnit_complexify {Q : Matrix ι ι ℝ} (hQ : IsUnit Q.det) : IsUnit (complexify Q) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h : (complexify Q).det = algebraMap ℝ ℂ Q.det := by
    rw [RingHom.map_det]
    rfl
  rw [h]
  exact hQ.map _

/-- **Eigenvalues of a Möbius image, forward.** Let `(γ A + δ) M = α A + β` with `γ A + δ`
invertible. An eigenpair `(λ, v)` of `A` has `γ λ + δ ≠ 0`, and `((α λ + β)/(γ λ + δ), v)` is an
eigenpair of `M`. -/
@[powerlib_foundation] theorem eigen_mobius {A M : Matrix ι ι ℝ} {α β γ δ : ℝ}
    (hQ : IsUnit (γ • A + δ • 1).det) (hM : (γ • A + δ • 1) * M = α • A + β • 1) {lam : ℂ}
    {v : ι → ℂ} (hv : v ≠ 0) (h : complexify A *ᵥ v = lam • v) :
    (γ : ℂ) * lam + δ ≠ 0 ∧
      complexify M *ᵥ v = (((α : ℂ) * lam + β) / ((γ : ℂ) * lam + δ)) • v := by
  have hQv := complexify_affine_mulVec h γ δ
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_complexify hQ)
  have hq : (γ : ℂ) * lam + δ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hQv
    exact hv (hinj (hQv.trans (Matrix.mulVec_zero _).symm))
  refine ⟨hq, hinj ?_⟩
  change complexify (γ • A + δ • 1) *ᵥ (complexify M *ᵥ v) =
    complexify (γ • A + δ • 1) *ᵥ ((((α : ℂ) * lam + β) / ((γ : ℂ) * lam + δ)) • v)
  rw [Matrix.mulVec_mulVec, ← complexify_mul, hM, complexify_affine_mulVec h, Matrix.mulVec_smul,
    hQv, smul_smul, div_mul_cancel₀ _ hq]

/-- **Eigenvalues of a Möbius image, backward.** Let `(γ A + δ) M = α A + β` with
`α δ − β γ ≠ 0`. An eigenpair `(μ, v)` of `M` comes from an eigenpair `(λ, v)` of `A` (the same
eigenvector), with `γ λ + δ ≠ 0` and `μ = (α λ + β)/(γ λ + δ)`. -/
@[powerlib_foundation] theorem exists_eigen_of_mobius {A M : Matrix ι ι ℝ} {α β γ δ : ℝ}
    (hdet : α * δ - β * γ ≠ 0) (hM : (γ • A + δ • 1) * M = α • A + β • 1) {μ : ℂ}
    {v : ι → ℂ} (hv : v ≠ 0) (h : complexify M *ᵥ v = μ • v) :
    ∃ lam : ℂ, complexify A *ᵥ v = lam • v ∧ (γ : ℂ) * lam + δ ≠ 0 ∧
      μ = ((α : ℂ) * lam + β) / ((γ : ℂ) * lam + δ) := by
  have hdet' : (α : ℂ) * δ - β * γ ≠ 0 := by exact_mod_cast hdet
  have hc : complexify (γ • A + δ • 1) *ᵥ (complexify M *ᵥ v) =
      complexify (α • A + β • 1) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, ← complexify_mul, hM]
  rw [h, Matrix.mulVec_smul, complexify_affine, complexify_affine, affine_mulVec,
    affine_mulVec] at hc
  set u := complexify A *ᵥ v
  have hrel : (μ * γ - α : ℂ) • u = (β - μ * δ : ℂ) • v := by
    linear_combination (norm := module) hc
  have hne : (μ * γ - α : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hrel
    have hb : (β : ℂ) - μ * δ = 0 := by
      by_contra hb
      exact hv ((smul_eq_zero.mp hrel.symm).resolve_left hb)
    exact hdet' (by linear_combination (-(δ : ℂ)) * h0 - (γ : ℂ) * hb)
  have hden : (γ : ℂ) * ((β - μ * δ) / (μ * γ - α)) + δ ≠ 0 := by
    have e : (γ : ℂ) * ((β - μ * δ) / (μ * γ - α)) + δ = -((α * δ - β * γ) / (μ * γ - α)) := by
      rw [neg_div', eq_div_iff hne, add_mul, mul_assoc, div_mul_cancel₀ _ hne]
      ring
    rw [e]
    exact neg_ne_zero.mpr (div_ne_zero hdet' hne)
  refine ⟨(β - μ * δ) / (μ * γ - α), ?_, hden, ?_⟩
  · rw [div_eq_inv_mul, mul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · rw [eq_div_iff hden]
    field_simp
    ring

/-- **Spectral mapping for Möbius images.** For `(γ A + δ) M = α A + β` with `γ A + δ` invertible
and `α δ − β γ ≠ 0`, a property holds for every eigenvalue of `M` exactly when it holds for
`(α λ + β)/(γ λ + δ)` for every eigenvalue `λ` of `A`. -/
@[powerlib_foundation] theorem forall_eigen_mobius_iff {A M : Matrix ι ι ℝ} {α β γ δ : ℝ}
    (hdet : α * δ - β * γ ≠ 0) (hQ : IsUnit (γ • A + δ • 1).det)
    (hM : (γ • A + δ • 1) * M = α • A + β • 1) (P : ℂ → Prop) :
    (∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → complexify M *ᵥ v = μ • v → P μ) ↔
      ∀ (lam : ℂ) (v : ι → ℂ), v ≠ 0 → complexify A *ᵥ v = lam • v →
        P (((α : ℂ) * lam + β) / ((γ : ℂ) * lam + δ)) := by
  constructor
  · intro hP lam v hv h
    exact hP _ v hv (eigen_mobius hQ hM hv h).2
  · intro hP μ v hv h
    obtain ⟨lam, hA, -, rfl⟩ := exists_eigen_of_mobius hdet hM hv h
    exact hP lam v hv hA

/-- `γ A + δ` is invertible when no eigenvalue `λ` of `A` has `γ λ + δ = 0` (`γ ≠ 0`). -/
@[powerlib_foundation] theorem isUnit_det_affine_of_forall_eigen {A : Matrix ι ι ℝ} {γ δ : ℝ}
    (hγ : γ ≠ 0)
    (h : ∀ (lam : ℂ) (v : ι → ℂ), v ≠ 0 → complexify A *ᵥ v = lam • v → (γ : ℂ) * lam + δ ≠ 0) :
    IsUnit (γ • A + δ • 1).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hz
  have hAv : A *ᵥ v = (-δ / γ) • v := by
    calc A *ᵥ v = γ⁻¹ • (γ • (A *ᵥ v)) := by rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]
      _ = (-δ / γ) • v := by
        rw [eq_neg_of_add_eq_zero_left hz, smul_neg, smul_smul, neg_div, div_eq_inv_mul, neg_smul]
  have hw : (fun i => (v i : ℂ)) ≠ 0 := by
    intro h0
    exact hv (funext fun i => by simpa using congrFun h0 i)
  have hAw : complexify A *ᵥ (fun i => (v i : ℂ)) = ((-δ / γ : ℝ) : ℂ) • fun i => (v i : ℂ) := by
    rw [complexify_mulVec_ofReal, hAv]
    funext i
    simp
  have hγ' : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  exact h _ _ hw hAw (by push_cast; field_simp; ring)

/-- Scaling: the eigenvalues of `c A` are `c λ`. -/
@[powerlib_foundation] theorem forall_eigen_smul_iff {c : ℝ} (hc : c ≠ 0) (A : Matrix ι ι ℝ)
    (P : ℂ → Prop) :
    (∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → complexify (c • A) *ᵥ v = μ • v → P μ) ↔
      ∀ (lam : ℂ) (v : ι → ℂ), v ≠ 0 → complexify A *ᵥ v = lam • v → P (c * lam) := by
  rw [forall_eigen_mobius_iff (A := A) (M := c • A) (α := c) (β := 0) (γ := 0) (δ := 1)
    (by simpa using hc) (by simp) (by simp)]
  simp

end Mobius

/-! ## Hurwitz and Schur stability of Möbius images -/

section Stability

variable {n : ℕ}

@[powerlib_foundation] theorem isHurwitz_iff_forall_eigen {A : Matrix (Fin n) (Fin n) ℝ} :
    IsHurwitz A ↔
      ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → complexify A *ᵥ v = μ • v → μ.re < 0 := by
  simp only [IsHurwitz, IsHurwitzWithRate, neg_zero]

/-- A Möbius image is Hurwitz exactly when the images of the eigenvalues lie in the open left half
plane. -/
@[powerlib_foundation] theorem isHurwitz_mobius_iff {A M : Matrix (Fin n) (Fin n) ℝ}
    {α β γ δ : ℝ} (hdet : α * δ - β * γ ≠ 0) (hQ : IsUnit (γ • A + δ • 1).det)
    (hM : (γ • A + δ • 1) * M = α • A + β • 1) :
    IsHurwitz M ↔ ∀ (lam : ℂ) (v : Fin n → ℂ), v ≠ 0 → complexify A *ᵥ v = lam • v →
      (((α : ℂ) * lam + β) / ((γ : ℂ) * lam + δ)).re < 0 := by
  rw [isHurwitz_iff_forall_eigen]
  exact forall_eigen_mobius_iff hdet hQ hM fun μ => μ.re < 0

/-- A Möbius image is Schur stable exactly when the images of the eigenvalues lie in the open unit
disk. -/
@[powerlib_foundation] theorem schurStable_mobius_iff {A M : Matrix (Fin n) (Fin n) ℝ}
    {α β γ δ : ℝ} (hdet : α * δ - β * γ ≠ 0) (hQ : IsUnit (γ • A + δ • 1).det)
    (hM : (γ • A + δ • 1) * M = α • A + β • 1) :
    LTI.SchurStable M ↔ ∀ (lam : ℂ) (v : Fin n → ℂ), v ≠ 0 → complexify A *ᵥ v = lam • v →
      ‖((α : ℂ) * lam + β) / ((γ : ℂ) * lam + δ)‖ < 1 :=
  forall_eigen_mobius_iff hdet hQ hM fun μ => ‖μ‖ < 1

/-- A positive scaling (a time base) keeps the Hurwitz property. -/
@[powerlib_foundation] theorem isHurwitz_smul_iff {c : ℝ} (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℝ) : IsHurwitz (c • A) ↔ IsHurwitz A := by
  rw [isHurwitz_iff_forall_eigen, isHurwitz_iff_forall_eigen,
    forall_eigen_smul_iff hc.ne' A fun μ => μ.re < 0]
  refine forall₄_congr fun lam v _ _ => ?_
  rw [Complex.re_ofReal_mul]
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.mpr (mul_nonneg hc.le (not_lt.mp h')))
  · exact mul_neg_of_pos_of_neg hc

end Stability

/-! ## Equal characteristic polynomials -/

section Charpoly

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Spectral stability read through eigenpairs, on any finite index type. -/
@[powerlib_foundation] theorem spectrallyStable_iff_forall_eigen {A : Matrix ι ι ℝ} :
    SpectrallyStable A ↔
      ∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → complexify A *ᵥ v = μ • v → μ.re < 0 := by
  refine forall_congr' fun μ => ⟨fun h v hv heig => h ?_, fun h hdet => ?_⟩
  · apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv, ?_⟩
    rw [characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig,
      sub_self]
  · obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    rw [characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_eq_zero] at hz
    exact h v hv hz.symm

/-- Matrices with the same characteristic polynomial, possibly on different index types, are
spectrally stable together. -/
@[powerlib_foundation] theorem spectrallyStable_congr_charpoly {A : Matrix ι ι ℝ}
    {B : Matrix κ κ ℝ} (h : A.charpoly = B.charpoly) :
    SpectrallyStable A ↔ SpectrallyStable B := by
  simp only [SpectrallyStable, det_characteristicMatrix_eq_eval, complexify, Matrix.charpoly_map, h]

@[powerlib_foundation] theorem isHurwitz_congr_charpoly {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin m) (Fin m) ℝ} (h : A.charpoly = B.charpoly) : IsHurwitz A ↔ IsHurwitz B := by
  rw [← spectrallyStable_iff_isHurwitz, ← spectrallyStable_iff_isHurwitz]
  exact spectrallyStable_congr_charpoly h

/-- A similarity keeps the characteristic polynomial; only the left inverse `S T = 1` is used. -/
@[powerlib_foundation] theorem charpoly_conj {T S : Matrix ι ι ℝ} (hST : S * T = 1)
    (A : Matrix ι ι ℝ) : (T * A * S).charpoly = A.charpoly := by
  rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hST, Matrix.mul_one]

@[powerlib_foundation] theorem spectrallyStable_conj {T S : Matrix ι ι ℝ} (hST : S * T = 1)
    (A : Matrix ι ι ℝ) : SpectrallyStable (T * A * S) ↔ SpectrallyStable A :=
  spectrallyStable_congr_charpoly (charpoly_conj hST A)

@[powerlib_foundation] theorem isHurwitz_transpose_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} :
    IsHurwitz Aᵀ ↔ IsHurwitz A :=
  isHurwitz_congr_charpoly (Matrix.charpoly_transpose A)

end Charpoly

end powerlib.Linear
