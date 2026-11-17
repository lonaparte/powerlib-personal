import theorem.Modal.Participation
import theorem.LinearAlgebra.Conditioning
import theorem.LTI.Discrete
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-! # Eigenvalue perturbation: Bauer–Fike, first-order sensitivity, spectral condition number

The Bauer–Fike bounds (diagonalisable, Hermitian and normal matrices) and the bound of the
first-order eigenvalue sensitivity by the spectral condition number.

Scope.
* Complex square matrices, spectral (`ℓ²` operator) norms (`Matrix.Norms.L2Operator`), vectors in
  `EuclideanSpace ℂ n` acted on by `LinearAlgebra.act A = Matrix.toEuclideanCLM A`.

Source: work-sync theory/T-eigenvalue-analysis.md §1.4 (Bauer–Fike, normal matrices),
§1.8 (first-order perturbation `λ̃ = λ + ψᵀEv/(ψᵀv)`, spectral condition number),
§1.9 (sensitivity `dλ/dα = ψᵀ (∂A/∂α) v`); theory/T-small-signal-stability.md §1.8;
theory/T-participation-factor.md (left/right eigenvectors).

Results.
* `bauerFike` — if `A = V Λ V⁻¹` (`Λ = diag λ`), every eigenvalue `μ` of `A + E` satisfies
  `minᵢ |μ − λᵢ| ≤ ‖V‖ ‖V⁻¹‖ ‖E‖` (for a `ModalBasis`: `bauerFike mb.V_mul_Wt mb.decomp`,
  `V⁻¹ = Wᵀ`).
* `bauerFike_hermitian` — normal-matrix corollary, Hermitian case via Mathlib's spectral theorem
  `Matrix.IsHermitian.spectral_theorem`, unitary `V`, `‖V‖ = ‖V⁻¹‖ = 1`:
  `minᵢ |μ − λᵢ| ≤ ‖E‖`.
* `bauerFike_normal` — **Bauer–Fike for a general normal matrix** (`Aᴴ A = A Aᴴ`): every
  eigenvalue `μ` of `A + E` has some `ν ∈ σ(A)` with `|μ − ν| ≤ ‖E‖`. No diagonalisation is
  assumed: for `μ ∉ σ(A)` the resolvent `R = (μI − A)⁻¹` is normal, so its spectral norm equals
  its spectral radius (Mathlib `IsStarNormal.spectralRadius_eq_nnnorm`; complex matrices with
  the `ℓ²` operator norm form a C⋆-algebra), which is attained at some `1/(μ − ν)`, `ν ∈ σ(A)`
  (`spectrum.exists_nnnorm_eq_spectralRadius`); `x = R E x` gives `1 ≤ ‖R‖ ‖E‖`.
  `mem_spectrum_iff_exists_eigvec`: `σ(M)` is the set of eigenvalues of a complex matrix
  (membership form of `LTI.spectrum_eq_setOf_eigenpair`, `theorem/LTI/Discrete.lean`), which
  turns the hypothesis into `μ ∈ σ(A + E)`.
* The first-order sensitivity along a differentiable eigen-branch,
  `λ'(α₀) (ψᵀ v(α₀)) = ψᵀ A'(α₀) v(α₀)` for a left eigenvector `ψ` of `A(α₀)`, is
  `Modal.eigenvalue_deriv_left_of_eventually` (`theorem/Modal/Sensitivity.lean`, with the
  existence of the branch at a simple eigenvalue, `exists_eigenvector_branch`).
* `abs_sensitivity_le` — `|λ'(α₀)| ≤ κ(λ) ‖A'(α₀)‖` with the spectral condition number
  `κ(λ) = ‖ψ‖ ‖v‖ / |ψᵀ v|` (first-order form of `|λ̃ − λ| ≤ κ(λ)‖E‖ + O(‖E‖²)`).
-/

noncomputable section
namespace powerlib.Modal
open Matrix powerlib.LinearAlgebra
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Bauer–Fike -/

omit [DecidableEq n] in
@[tmio T, powerlib_foundation] private lemma exists_norm_eq_pi_norm [Nonempty n] (d : n → ℂ) :
    ∃ i, ‖d‖ = ‖d i‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖d i‖) Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ (norm_le_pi_norm d i)⟩
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hi j (Finset.mem_univ j)

/-- **Bauer–Fike**: `A = V diag(λ) V⁻¹` ⇒ every eigenvalue `μ` of `A + E` has
`|μ − λᵢ| ≤ ‖V‖ ‖V⁻¹‖ ‖E‖` for some `i`. -/
@[tmio T, powerlib_foundation] theorem bauerFike {A E V Vinv : Matrix n n ℂ} {lam : n → ℂ}
    (hV : V * Vinv = 1) (hA : A = V * diagonal lam * Vinv) {μ : ℂ} {x : EuclideanSpace ℂ n}
    (hx : x ≠ 0) (heig : act (A + E) x = μ • x) :
    ∃ i, ‖μ - lam i‖ ≤ ‖V‖ * ‖Vinv‖ * ‖E‖ := by
  have hVinv : Vinv * V = 1 := mul_eq_one_comm.mp hV
  have hne : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hx (Subsingleton.elim _ _)
  by_cases hex : ∃ i, lam i = μ
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, by rw [hi, sub_self, norm_zero]; positivity⟩
  push Not at hex
  set d : n → ℂ := fun i => (lam i - μ)⁻¹ with hd
  -- `x = V diag(d) V⁻¹ (A − μ) x = −V diag(d) V⁻¹ E x`
  have hres : V * diagonal d * Vinv * (A - μ • 1) = 1 := by
    have : A - μ • 1 = V * diagonal (fun i => lam i - μ) * Vinv := by
      rw [hA]
      have : μ • (1 : Matrix n n ℂ) = V * diagonal (fun _ => μ) * Vinv := by
        rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hV]
      rw [this, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    rw [this]
    calc V * diagonal d * Vinv * (V * diagonal (fun i => lam i - μ) * Vinv)
        = V * (diagonal d * (Vinv * V) * diagonal (fun i => lam i - μ)) * Vinv := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hVinv, Matrix.mul_one, diagonal_mul_diagonal]
          have : (fun i => d i * (lam i - μ)) = fun _ => (1 : ℂ) := by
            funext i; exact inv_mul_cancel₀ (sub_ne_zero.mpr (hex i))
          rw [this, diagonal_one, Matrix.mul_one, hV]
  have hAx : act (A - μ • 1) x = -act E x := by
    have e1 : act (A + E) x = act A x + act E x := by simp [act]
    have e2 : act (A - μ • 1) x = act A x - μ • x := by simp [act]
    rw [e2]
    rw [e1] at heig
    rw [← heig]
    abel
  have hxeq : x = act (V * diagonal d * Vinv) (-act E x) := by
    rw [← hAx, act, act, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      hres, map_one]; rfl
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : ‖x‖ ≤ ‖V‖ * ‖diagonal d‖ * ‖Vinv‖ * (‖E‖ * ‖x‖) := by
    calc ‖x‖ = ‖act (V * diagonal d * Vinv) (-act E x)‖ := by rw [← hxeq]
      _ ≤ ‖V * diagonal d * Vinv‖ * ‖-act E x‖ := norm_act_le _ _
      _ ≤ ‖V‖ * ‖diagonal d‖ * ‖Vinv‖ * (‖E‖ * ‖x‖) := by
          rw [norm_neg]
          gcongr
          · calc ‖V * diagonal d * Vinv‖ ≤ ‖V * diagonal d‖ * ‖Vinv‖ := l2_opNorm_mul _ _
              _ ≤ ‖V‖ * ‖diagonal d‖ * ‖Vinv‖ := by gcongr; exact l2_opNorm_mul _ _
          · exact norm_act_le _ _
  obtain ⟨i, hi⟩ := exists_norm_eq_pi_norm d
  refine ⟨i, ?_⟩
  rw [l2_opNorm_diagonal, hi] at hb
  have hlam : 0 < ‖lam i - μ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hex i))
  have hdi : ‖d i‖ = ‖lam i - μ‖⁻¹ := by rw [hd]; simp
  rw [hdi] at hb
  have h1 : 1 ≤ ‖V‖ * ‖lam i - μ‖⁻¹ * ‖Vinv‖ * ‖E‖ := by
    have := hb
    rw [show ‖V‖ * ‖lam i - μ‖⁻¹ * ‖Vinv‖ * (‖E‖ * ‖x‖) =
      (‖V‖ * ‖lam i - μ‖⁻¹ * ‖Vinv‖ * ‖E‖) * ‖x‖ by ring] at this
    exact (le_mul_iff_one_le_left hxpos).mp this
  rw [norm_sub_rev]
  calc ‖lam i - μ‖ = ‖lam i - μ‖ * 1 := (mul_one _).symm
    _ ≤ ‖lam i - μ‖ * (‖V‖ * ‖lam i - μ‖⁻¹ * ‖Vinv‖ * ‖E‖) := by gcongr
    _ = ‖V‖ * ‖Vinv‖ * ‖E‖ := by field_simp

/-- **Bauer–Fike for Hermitian (normal) matrices**: the eigenvector matrix is unitary, so every
eigenvalue of `A + E` lies within `‖E‖` of the spectrum of `A`. -/
@[tmio T, powerlib_foundation] theorem bauerFike_hermitian {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (E : Matrix n n ℂ) {μ : ℂ} {x : EuclideanSpace ℂ n} (hx : x ≠ 0)
    (heig : act (A + E) x = μ • x) :
    ∃ i, ‖μ - (hA.eigenvalues i : ℂ)‖ ≤ ‖E‖ := by
  have hne : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hx (Subsingleton.elim _ _)
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hU : U ∈ unitary (Matrix n n ℂ) := hA.eigenvectorUnitary.2
  have hUs : star U ∈ unitary (Matrix n n ℂ) := Unitary.star_mem hU
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hU
  have hdec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  obtain ⟨i, hi⟩ := powerlib.Modal.bauerFike hUU hdec hx heig
  refine ⟨i, ?_⟩
  have h1 : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
  have h2 : ‖star U‖ = 1 := CStarRing.norm_of_mem_unitary hUs
  rw [h1, h2, one_mul, one_mul] at hi
  simpa using hi

/-! ## Bauer–Fike for normal matrices -/

/-- The spectrum of a complex matrix is its set of eigenvalues (membership form of
`LTI.spectrum_eq_setOf_eigenpair`). -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_iff_exists_eigvec {M : Matrix n n ℂ} {ν : ℂ} :
    ν ∈ spectrum ℂ M ↔ ∃ w : n → ℂ, w ≠ 0 ∧ M *ᵥ w = ν • w :=
  Set.ext_iff.mp (LTI.spectrum_eq_setOf_eigenpair M) ν

/-- **Bauer–Fike for normal matrices**: if `A` is normal (`Aᴴ A = A Aᴴ`), every eigenvalue `μ` of
`A + E` lies within `‖E‖` (spectral norm) of some eigenvalue `ν ∈ σ(A)`. -/
@[tmio T, powerlib_foundation] theorem bauerFike_normal {A E : Matrix n n ℂ} (hA : Aᴴ * A = A * Aᴴ) {μ : ℂ}
    {x : EuclideanSpace ℂ n} (hx : x ≠ 0) (heig : act (A + E) x = μ • x) :
    ∃ ν ∈ spectrum ℂ A, ‖μ - ν‖ ≤ ‖E‖ := by
  by_cases hμ : μ ∈ spectrum ℂ A
  · exact ⟨μ, hμ, by simp⟩
  have hne : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hx (Subsingleton.elim _ _)
  set b : Matrix n n ℂ := μ • 1 - A with hb
  have hbu : IsUnit b := by
    rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hμ
    exact hμ
  have hbdet : IsUnit b.det := (Matrix.isUnit_iff_isUnit_det b).mp hbu
  set R : Matrix n n ℂ := b⁻¹ with hR
  -- `b` and hence `R = b⁻¹` are normal
  have hbn : bᴴ * b = b * bᴴ := by
    simp only [hb, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hA]
    module
  have hRn : Rᴴ * R = R * Rᴴ := by
    rw [hR, conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hbn]
  have : IsStarNormal R := ⟨by
    change Rᴴ * R = R * Rᴴ
    exact hRn⟩
  -- `x = R E x`
  have hbx : act b x = act E x := by
    have e1 : act (A + E) x = act A x + act E x := by simp [act]
    have e2 : act b x = μ • x - act A x := by simp [act, hb]
    rw [e2, ← heig, e1]
    abel
  have hxeq : x = act R (act E x) := by rw [← hbx, hR, act_inv_act hbdet]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : 1 ≤ ‖R‖ * ‖E‖ := by
    have hb' : ‖x‖ ≤ ‖R‖ * ‖E‖ * ‖x‖ := by
      calc ‖x‖ = ‖act R (act E x)‖ := by rw [← hxeq]
        _ ≤ ‖R‖ * ‖act E x‖ := norm_act_le _ _
        _ ≤ ‖R‖ * (‖E‖ * ‖x‖) := by gcongr; exact norm_act_le _ _
        _ = ‖R‖ * ‖E‖ * ‖x‖ := by ring
    exact (le_mul_iff_one_le_left hxpos).mp (by simpa using hb')
  have hRpos : 0 < ‖R‖ := by
    by_contra h
    push Not at h
    have : ‖R‖ * ‖E‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _)
    linarith
  -- the spectral radius of the normal matrix `R` is its norm and is attained
  obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius R
  rw [IsStarNormal.spectralRadius_eq_nnnorm R, ENNReal.coe_inj] at hzr
  have hzn : ‖z‖ = ‖R‖ := congrArg NNReal.toReal hzr
  obtain ⟨w, hw, hRw⟩ := mem_spectrum_iff_exists_eigvec.mp hz
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hzn; linarith
  -- `b w = z⁻¹ w`, so `A w = (μ − z⁻¹) w`
  have hbw : b *ᵥ w = z⁻¹ • w := by
    have hbR : b * R = 1 := Matrix.mul_nonsing_inv b hbdet
    have : b *ᵥ (R *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, hbR, Matrix.one_mulVec]
    rw [hRw, Matrix.mulVec_smul] at this
    calc b *ᵥ w = z⁻¹ • (z • b *ᵥ w) := by rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
      _ = z⁻¹ • w := by rw [this]
  refine ⟨μ - z⁻¹, mem_spectrum_iff_exists_eigvec.mpr ⟨w, hw, ?_⟩, ?_⟩
  · rw [hb, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hbw
    rw [sub_smul, ← hbw]
    abel
  · rw [sub_sub_cancel, norm_inv, hzn]
    rw [inv_le_iff_one_le_mul₀' hRpos]
    linarith

/-! ## Spectral condition number of the first-order sensitivity -/

/-- **Spectral condition number bound**: `|λ'(α₀)| ≤ κ(λ) ‖A'(α₀)‖`,
`κ(λ) = ‖ψ‖ ‖v‖ / |ψᵀ v|` (Euclidean vector norms, spectral matrix norm). -/
@[tmio T, powerlib_foundation] theorem abs_sensitivity_le (A' : Matrix n n ℂ) (ψ v : EuclideanSpace ℂ n)
    (hnorm : (WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp v) ≠ 0) :
    ‖(WithLp.ofLp ψ) ⬝ᵥ (A' *ᵥ WithLp.ofLp v) / ((WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp v))‖ ≤
      ‖ψ‖ * ‖v‖ / ‖(WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp v)‖ * ‖A'‖ := by
  have hpos : 0 < ‖(WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp v)‖ := norm_pos_iff.mpr hnorm
  rw [norm_div, div_le_iff₀ hpos]
  -- `|ψᵀ w| ≤ ‖ψ‖ ‖w‖` with `w = A' v`
  set w : EuclideanSpace ℂ n := act A' v
  have hw : A' *ᵥ WithLp.ofLp v = WithLp.ofLp w := rfl
  have hcs : ‖(WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp w)‖ ≤ ‖ψ‖ * ‖w‖ := by
    set ψc : EuclideanSpace ℂ n := WithLp.toLp 2 (star (WithLp.ofLp ψ))
    have hinner : inner ℂ ψc w = (WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp w) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      simp [ψc]
    have hnorm' : ‖ψc‖ = ‖ψ‖ := by
      simp [ψc, EuclideanSpace.norm_eq]
    rw [← hinner, ← hnorm']
    exact norm_inner_le_norm ψc w
  rw [hw]
  calc ‖(WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp w)‖ ≤ ‖ψ‖ * ‖w‖ := hcs
    _ ≤ ‖ψ‖ * (‖A'‖ * ‖v‖) := by gcongr; exact norm_act_le _ _
    _ = ‖ψ‖ * ‖v‖ / ‖(WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp v)‖ * ‖A'‖ *
          ‖(WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp v)‖ := by field_simp

end powerlib.Modal
