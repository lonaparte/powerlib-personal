import theorem.Modal.Participation
import theorem.LinearAlgebra.Conditioning
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-! # Eigenvalue perturbation: Bauer–Fike, first-order sensitivity, spectral condition number

Foundation layer (category B).

Sources: work-sync `theory/T-eigenvalue-analysis.md` §1.4 (Bauer–Fike, normal matrices),
§1.8 (first-order perturbation `λ̃ = λ + ψᵀEv/(ψᵀv)`, spectral condition number),
§1.9 (sensitivity `dλ/dα = ψᵀ (∂A/∂α) v`); `theory/T-small-signal-stability.md` §1.8;
`theory/T-participation-factor.md` (left/right eigenvectors).

Setting: complex square matrices, spectral (`ℓ²` operator) norms
(`Matrix.Norms.L2Operator`), vectors in `EuclideanSpace ℂ n` acted on by
`LinearAlgebra.act A = Matrix.toEuclideanCLM A`.

Results.
* `bauerFike`: if `A = V Λ V⁻¹` (`Λ = diag λ`), every eigenvalue `μ` of `A + E` satisfies
  `minᵢ |μ − λᵢ| ≤ ‖V‖ ‖V⁻¹‖ ‖E‖`; `ModalBasis.bauerFike` is the same with the modal data
  (`V⁻¹ = Wᵀ`).
* `bauerFike_hermitian` (normal-matrix corollary, Hermitian case via Mathlib's spectral theorem
  `Matrix.IsHermitian.spectral_theorem`, unitary `V`, `‖V‖ = ‖V⁻¹‖ = 1`): `minᵢ |μ − λᵢ| ≤ ‖E‖`.
* `bauerFike_normal`: **Bauer–Fike for a general normal matrix** (`Aᴴ A = A Aᴴ`): every eigenvalue
  `μ` of `A + E` has some `ν ∈ σ(A)` with `|μ − ν| ≤ ‖E‖`. No diagonalisation is assumed: for
  `μ ∉ σ(A)` the resolvent `R = (μI − A)⁻¹` is normal, so its spectral norm equals its spectral
  radius (Mathlib `IsStarNormal.spectralRadius_eq_nnnorm`; complex matrices with the `ℓ²` operator
  norm form a C⋆-algebra), which is attained at some `1/(μ − ν)`, `ν ∈ σ(A)`
  (`spectrum.exists_nnnorm_eq_spectralRadius`); `x = R E x` gives `1 ≤ ‖R‖ ‖E‖`.
  `mem_spectrum_iff_exists_eigvec`: `σ(M)` is the set of eigenvalues of a complex matrix.
  `bauerFike_normal_spectrum`: the same with `μ ∈ σ(A + E)` (spectrum form).
* `eigenvalue_sensitivity`: along a differentiable eigen-branch `A(α) v(α) = λ(α) v(α)` with a
  left eigenvector `ψ` of `A(α₀)` (`ψᵀ v(α₀) ≠ 0`), `λ'(α₀) = ψᵀ A'(α₀) v(α₀) / (ψᵀ v(α₀))`
  (`= ψᵀ A' v` under the normalisation `ψᵀ v = 1`). The existence of a differentiable branch
  (simple eigenvalue, implicit function theorem) is assumed, not proved.
* `abs_sensitivity_le`: `|λ'(α₀)| ≤ κ(λ) ‖A'(α₀)‖` with the spectral condition number
  `κ(λ) = ‖ψ‖ ‖v‖ / |ψᵀ v|` (first-order form of `|λ̃ − λ| ≤ κ(λ)‖E‖ + O(‖E‖²)`).
-/

noncomputable section
namespace powerlib.Modal
open Matrix powerlib.LinearAlgebra
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Bauer–Fike -/

omit [DecidableEq n] in
@[powerlib_foundation] private lemma exists_norm_eq_pi_norm [Nonempty n] (d : n → ℂ) :
    ∃ i, ‖d‖ = ‖d i‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖d i‖) Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ (norm_le_pi_norm d i)⟩
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hi j (Finset.mem_univ j)

/-- **Bauer–Fike**: `A = V diag(λ) V⁻¹` ⇒ every eigenvalue `μ` of `A + E` has
`|μ − λᵢ| ≤ ‖V‖ ‖V⁻¹‖ ‖E‖` for some `i`. -/
@[powerlib_foundation] theorem bauerFike {A E V Vinv : Matrix n n ℂ} {lam : n → ℂ}
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

/-- Bauer–Fike with the modal data of a `ModalBasis` (`V⁻¹ = Wᵀ`). -/
@[powerlib_foundation] theorem ModalBasis.bauerFike {A : Matrix n n ℂ} (mb : ModalBasis A)
    (E : Matrix n n ℂ) {μ : ℂ} {x : EuclideanSpace ℂ n} (hx : x ≠ 0)
    (heig : act (A + E) x = μ • x) :
    ∃ i, ‖μ - mb.eig i‖ ≤ ‖mb.V‖ * ‖mb.Wᵀ‖ * ‖E‖ :=
  powerlib.Modal.bauerFike mb.V_mul_Wt mb.decomp hx heig

/-- **Bauer–Fike for Hermitian (normal) matrices**: the eigenvector matrix is unitary, so every
eigenvalue of `A + E` lies within `‖E‖` of the spectrum of `A`. -/
@[powerlib_foundation] theorem bauerFike_hermitian {A : Matrix n n ℂ} (hA : A.IsHermitian)
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

/-- The spectrum of a complex matrix is its set of eigenvalues. -/
@[powerlib_foundation] theorem mem_spectrum_iff_exists_eigvec {M : Matrix n n ℂ} {ν : ℂ} :
    ν ∈ spectrum ℂ M ↔ ∃ w : n → ℂ, w ≠ 0 ∧ M *ᵥ w = ν • w := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff, Algebra.algebraMap_eq_smul_one]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]

/-- **Bauer–Fike for normal matrices**: if `A` is normal (`Aᴴ A = A Aᴴ`), every eigenvalue `μ` of
`A + E` lies within `‖E‖` (spectral norm) of some eigenvalue `ν ∈ σ(A)`. -/
@[powerlib_foundation] theorem bauerFike_normal {A E : Matrix n n ℂ} (hA : Aᴴ * A = A * Aᴴ) {μ : ℂ}
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

/-- **Bauer–Fike for normal matrices**, spectral form: `A` normal, `μ ∈ σ(A + E)` ⇒
`∃ ν ∈ σ(A)`, `|μ − ν| ≤ ‖E‖₂`. -/
@[powerlib_foundation] theorem bauerFike_normal_spectrum {A E : Matrix n n ℂ} (hA : Aᴴ * A = A * Aᴴ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A + E)) : ∃ ν ∈ spectrum ℂ A, ‖μ - ν‖ ≤ ‖E‖ := by
  obtain ⟨w, hw, hAw⟩ := mem_spectrum_iff_exists_eigvec.mp hμ
  refine bauerFike_normal hA (x := WithLp.toLp 2 w) (fun h => hw ?_) ?_
  · have := congrArg WithLp.ofLp h
    simpa using this
  · rw [act, Matrix.toEuclideanCLM_toLp, hAw]
    rfl

/-! ## First-order sensitivity of a simple eigenvalue -/

omit [DecidableEq n] in
/-- **Eigenvalue sensitivity** `dλ/dα = ψᵀ A'(α₀) v / (ψᵀ v)` along a differentiable eigen-branch
(entrywise derivatives; `ψ` a left eigenvector of `A(α₀)`). -/
@[powerlib_foundation] theorem eigenvalue_sensitivity {A : ℝ → Matrix n n ℂ}
    {A' : Matrix n n ℂ} {v : ℝ → n → ℂ} {v' : n → ℂ} {lam : ℝ → ℂ} {lam' : ℂ} {α₀ : ℝ}
    {ψ : n → ℂ} (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α)
    (hleft : vecMul ψ (A α₀) = lam α₀ • ψ) (hnorm : ψ ⬝ᵥ v α₀ ≠ 0) :
    lam' = ψ ⬝ᵥ (A' *ᵥ v α₀) / (ψ ⬝ᵥ v α₀) := by
  -- differentiate `Σⱼ A_ij v_j = λ v_i`
  have hrow : ∀ i, (∑ j, (A' i j * v α₀ j + A α₀ i j * v' j)) = lam' * v α₀ i + lam α₀ * v' i := by
    intro i
    have hL : HasDerivAt (fun α => (A α *ᵥ v α) i) (∑ j, (A' i j * v α₀ j + A α₀ i j * v' j)) α₀ := by
      simp only [mulVec, dotProduct]
      exact HasDerivAt.fun_sum fun j _ => (hA i j).mul (hv j)
    have hR : HasDerivAt (fun α => (lam α • v α) i) (lam' * v α₀ i + lam α₀ * v' i) α₀ := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hlam.mul (hv i)
    have heq : (fun α => (A α *ᵥ v α) i) = fun α => (lam α • v α) i := by
      funext α; rw [heig α]
    rw [heq] at hL
    exact hL.unique hR
  -- contract with `ψ` and use `ψᵀ A = λ ψᵀ`
  have hsum : ψ ⬝ᵥ (A' *ᵥ v α₀) + ψ ⬝ᵥ (A α₀ *ᵥ v') = lam' * (ψ ⬝ᵥ v α₀) + lam α₀ * (ψ ⬝ᵥ v') := by
    have h2 : A' *ᵥ v α₀ + A α₀ *ᵥ v' = lam' • v α₀ + lam α₀ • v' := by
      funext i
      simp only [Pi.add_apply, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
        ← Finset.sum_add_distrib]
      exact hrow i
    rw [← dotProduct_add, h2, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
  have hcancel : ψ ⬝ᵥ (A α₀ *ᵥ v') = lam α₀ * (ψ ⬝ᵥ v') := by
    rw [dotProduct_mulVec, hleft, smul_dotProduct, smul_eq_mul]
  rw [hcancel] at hsum
  field_simp
  linear_combination (-1 : ℂ) * hsum

/-- **Spectral condition number bound**: `|λ'(α₀)| ≤ κ(λ) ‖A'(α₀)‖`,
`κ(λ) = ‖ψ‖ ‖v‖ / |ψᵀ v|` (Euclidean vector norms, spectral matrix norm). -/
@[powerlib_foundation] theorem abs_sensitivity_le (A' : Matrix n n ℂ) (ψ v : EuclideanSpace ℂ n)
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
