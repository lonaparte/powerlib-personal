import theorem.SingularPerturbation.QuasiSteadyGraph
import theorem.Linear.EigenMap
import Mathlib.RingTheory.Complex

/-! # The real form of a complex (phasor) matrix: products, spectrum and two time scales

A complex `m × n` matrix `M` acting on complex phasors is the real `(m × 2) × (n × 2)` matrix
`realify M` acting on their real and imaginary parts (each entry `z = a + jb` read as
`[[a, −b], [b, a]]`). Its spectrum is that of `M` together with the complex conjugates, so its
spectral stability is decided by the complex eigenvalues of `M`; and the real form is
multiplicative, so a Schur factorization of `M` is one of `realify M`.

Scope.
* Generic: complex matrices on arbitrary finite index types and their real forms
  (`Matrix.comp` of the entrywise `Algebra.leftMulMatrix Complex.basisOneI`); no model. The
  two-time-scale statement is the matrix law
  `SingularPerturbation.exists_epsStar_spectrallyStable_splitScale_mul` of
  `theorem/SingularPerturbation/QuasiSteadyGraph.lean` read through the real form; constant
  matrices, no field, no trajectory statement.

Source: the real representation of a complex linear map (R. A. Horn and C. R. Johnson, *Topics in
Matrix Analysis*, §1.3 problem 7 / *Matrix Analysis*, §1.3.P20: the spectrum of
`[[Re M, −Im M], [Im M, Re M]]` is `σ(M) ∪ σ(M̄)`); Kokotović–Khalil–O'Reilly, *Singular
Perturbation Methods in Control* (1986), Ch. 2 (linear two-time-scale stability).

Results.
* `realify`, `realify_apply_zero_zero`, `realify_apply_zero_one`, `realify_apply_one_zero`,
  `realify_apply_one_one`: the entries; `realify_mul`, `realify_add`, `realify_zero`,
  `realify_one`, `realify_neg`: the real form is additive and multiplicative (rectangular
  matrices).
* `realify_conjTranspose`, `realify_lyapunov` (a complex Lyapunov equation `P M + Mᴴ P = −1` is a
  real one for the real forms), `absSum_realify` (`Σ |entries|` of the real form).
* `realify_mulVec_eigen`: an eigenvector `w` of `M` gives the eigenvector `(w, −j w)` of the
  complexified real form with the same eigenvalue; `not_spectrallyStable_realify`: an eigenvalue of
  `M` with nonnegative real part makes the real form not spectrally stable.
* `spectrallyStable_realify_of_eigen`: if every eigenvalue of `M` has negative real part, the real
  form is spectrally stable (an eigenvector `v = (v₀, v₁)` of the real form gives the eigenvector
  `v₀ + j v₁` of `M` or `v₀ − j v₁` of `M̄`); `spectrallyStable_realify_iff`.
* Two time scales: `realifySplit` (the real coordinates split along a fast/slow splitting of the
  phasors), `toBlocks_reindex_realify` (the blocks of the real form are the real forms of the
  blocks), `realify_diagonal_ofReal`, `phasorScale`, `realify_phasorScale` (the phasor scaling
  `diag(ε⁻¹ fast, 1 slow)` reads as `splitScale`); `exists_epsStar_spectrallyStable_realify`: if
  `A H + B = 0`, `C H + D = R` for the phasor blocks and the real forms of the fast block `A` and
  of `R` are spectrally stable, the real form of `phasorScale σ ε * M` is spectrally stable for
  every small `ε > 0`; `spectrallyStable_realify_of_lt_graphEpsStar`: the same for every
  `ε ∈ (0, graphEpsStar …)`, given Lyapunov matrices of the two real forms.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix Complex

/-- The real form of a complex matrix: entry `z = a + jb` read as the block `[[a, −b], [b, a]]`
(rows and columns indexed by (phasor, component), component `0` the real part). -/
def realify {m n : Type*} (M : Matrix m n ℂ) : Matrix (m × Fin 2) (n × Fin 2) ℝ :=
  Matrix.comp m n (Fin 2) (Fin 2) ℝ (M.map (Algebra.leftMulMatrix Complex.basisOneI))

section Entries

variable {m n : Type*} (M : Matrix m n ℂ) (a : m) (b : n)

@[tmio T, simp, powerlib_foundation] theorem realify_apply_zero_zero :
    realify M (a, 0) (b, 0) = (M a b).re := by
  simp [realify, Algebra.leftMulMatrix_complex]

@[tmio T, simp, powerlib_foundation] theorem realify_apply_zero_one :
    realify M (a, 0) (b, 1) = -(M a b).im := by
  simp [realify, Algebra.leftMulMatrix_complex]

@[tmio T, simp, powerlib_foundation] theorem realify_apply_one_zero :
    realify M (a, 1) (b, 0) = (M a b).im := by
  simp [realify, Algebra.leftMulMatrix_complex]

@[tmio T, simp, powerlib_foundation] theorem realify_apply_one_one :
    realify M (a, 1) (b, 1) = (M a b).re := by
  simp [realify, Algebra.leftMulMatrix_complex]

end Entries

section Algebra

variable {l m n : Type*}

@[tmio T, powerlib_foundation] theorem realify_mul [Fintype m] (X : Matrix l m ℂ)
    (Y : Matrix m n ℂ) : realify (X * Y) = realify X * realify Y := by
  ext ⟨a, c⟩ ⟨b, d⟩
  fin_cases c <;> fin_cases d <;>
    simp only [Fin.zero_eta, Fin.mk_one, realify_apply_zero_zero, realify_apply_zero_one,
      realify_apply_one_zero, realify_apply_one_one, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      ← Finset.sum_neg_distrib, Fin.isValue] <;>
    refine Finset.sum_congr rfl fun _ _ => by ring

@[tmio T, powerlib_foundation] theorem realify_add (X Y : Matrix m n ℂ) :
    realify (X + Y) = realify X + realify Y := by
  ext ⟨a, c⟩ ⟨b, d⟩
  fin_cases c <;> fin_cases d <;> simp [add_comm]

@[tmio T, powerlib_foundation] theorem realify_neg (X : Matrix m n ℂ) :
    realify (-X) = -realify X := by
  ext ⟨a, c⟩ ⟨b, d⟩
  fin_cases c <;> fin_cases d <;> simp

@[tmio T, simp, powerlib_foundation] theorem realify_zero :
    realify (0 : Matrix m n ℂ) = 0 := by
  ext ⟨a, c⟩ ⟨b, d⟩
  fin_cases c <;> fin_cases d <;> simp

@[tmio T, simp, powerlib_foundation] theorem realify_one [DecidableEq m] :
    realify (1 : Matrix m m ℂ) = 1 := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases h : a = b <;> fin_cases c <;> fin_cases d <;> simp [Matrix.one_apply, h]

end Algebra

/-! ## Transpose and size -/

section Transpose

variable {m n : Type*}

/-- The real form of the conjugate transpose is the transpose of the real form. -/
@[tmio T, powerlib_foundation] theorem realify_conjTranspose (M : Matrix m n ℂ) :
    realify Mᴴ = (realify M)ᵀ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  fin_cases c <;> fin_cases d <;> simp [Matrix.conjTranspose_apply]

/-- A complex Lyapunov equation `P M + Mᴴ P = −1` is a real one for the real forms. -/
@[tmio T, powerlib_foundation] theorem realify_lyapunov [Fintype n] [DecidableEq n]
    {P M : Matrix n n ℂ} (h : P * M + Mᴴ * P = -1) :
    realify P * realify M + (realify M)ᵀ * realify P = -1 := by
  rw [← realify_conjTranspose, ← realify_mul, ← realify_mul, ← realify_add, h, realify_neg,
    realify_one]

/-- `Σ |entries|` of the real form: twice the sum of `|Re| + |Im|` of the complex entries. -/
@[tmio T, powerlib_foundation] theorem absSum_realify [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) :
    absSum (realify M) = ∑ a, ∑ b, 2 * (|(M a b).re| + |(M a b).im|) := by
  simp only [absSum, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [abs_neg]
  ring

end Transpose

/-! ## Spectrum -/

section Spectrum

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complex vector `(w, −j w)` on the real coordinates. -/
def eigenLift (w : n → ℂ) : n × Fin 2 → ℂ := fun x => if x.2 = 0 then w x.1 else -I * w x.1

omit [Fintype n] [DecidableEq n] in
@[tmio T, powerlib_foundation] theorem eigenLift_ne_zero {w : n → ℂ} (hw : w ≠ 0) :
    eigenLift w ≠ 0 := by
  intro h
  apply hw
  funext b
  simpa [eigenLift] using congrFun h (b, 0)

omit [DecidableEq n] in
/-- An eigenvector `w` of `M` (eigenvalue `μ`) gives the eigenvector `(w, −j w)` of the
complexified real form, with the same eigenvalue. -/
@[tmio T, powerlib_foundation] theorem realify_mulVec_eigen {M : Matrix n n ℂ} {w : n → ℂ}
    {μ : ℂ} (h : M *ᵥ w = μ • w) :
    Linear.complexify (realify M) *ᵥ eigenLift w = μ • eigenLift w := by
  ext ⟨a, c⟩
  have ha := congrFun h a
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at ha
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Linear.complexify,
    Matrix.map_apply, Pi.smul_apply, smul_eq_mul, eigenLift, Complex.coe_algebraMap]
  have hz : ∀ z w : ℂ, (z.re : ℂ) * w + (-z.im : ℝ) * (-I * w) = z * w := fun z w => by
    conv_rhs => rw [← Complex.re_add_im z]
    push_cast; ring
  have hz' : ∀ z w : ℂ, (z.im : ℂ) * w + (z.re : ℝ) * (-I * w) = -I * (z * w) := fun z w => by
    conv_rhs => rw [← Complex.re_add_im z]
    linear_combination (z.im * w) * Complex.I_sq
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, realify_apply_zero_zero,
      realify_apply_zero_one, one_ne_zero]
    simp only [hz, ← ha]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, realify_apply_one_zero,
      realify_apply_one_one]
    simp only [hz', ← Finset.mul_sum, ha]
    ring

/-- An eigenvalue of `M` with nonnegative real part makes the real form not spectrally stable. -/
@[tmio T, powerlib_foundation] theorem not_spectrallyStable_realify {M : Matrix n n ℂ}
    {w : n → ℂ} (hw : w ≠ 0) {μ : ℂ} (h : M *ᵥ w = μ • w) (hμ : 0 ≤ μ.re) :
    ¬ Linear.SpectrallyStable (realify M) := by
  intro hs
  have hdet := (Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair (realify M) μ).mpr
    ⟨eigenLift w, eigenLift_ne_zero hw, realify_mulVec_eigen h⟩
  exact absurd (hs μ hdet) (not_lt.mpr hμ)

/-- **Spectral stability of the real form from the complex eigenvalues.** If every eigenvalue of
the complex matrix `M` has negative real part, its real form is spectrally stable. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_realify_of_eigen {M : Matrix n n ℂ}
    (hM : ∀ (μ : ℂ) (w : n → ℂ), w ≠ 0 → M *ᵥ w = μ • w → μ.re < 0) :
    Linear.SpectrallyStable (realify M) := by
  intro μ hdet
  obtain ⟨v, hv, heig⟩ :=
    (Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair (realify M) μ).mp hdet
  set v0 : n → ℂ := fun b => v (b, 0)
  set v1 : n → ℂ := fun b => v (b, 1)
  have e0 : ∀ a, ∑ b, (((M a b).re : ℂ) * v0 b - ((M a b).im : ℂ) * v1 b) = μ * v0 a := by
    intro a
    have := congrFun heig (a, 0)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Linear.complexify, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, Complex.coe_algebraMap,
      realify_apply_zero_zero, realify_apply_zero_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast; ring
  have e1 : ∀ a, ∑ b, (((M a b).im : ℂ) * v0 b + ((M a b).re : ℂ) * v1 b) = μ * v1 a := by
    intro a
    have := congrFun heig (a, 1)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Linear.complexify, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, Complex.coe_algebraMap,
      realify_apply_one_zero, realify_apply_one_one] at this
    rw [← this]
  by_cases hp : (fun b => v0 b + I * v1 b) = 0
  · -- then `v₀ − j v₁ ≠ 0` is an eigenvector of `M̄` with eigenvalue `μ`
    set u : n → ℂ := fun b => v0 b - I * v1 b
    have hu : u ≠ 0 := by
      intro hu
      apply hv
      funext ⟨b, c⟩
      have h1 := congrFun hp b
      have h2 := congrFun hu b
      simp only [Pi.zero_apply, u] at h1 h2
      have hv0 : v0 b = 0 := by linear_combination (h1 + h2) / 2
      have h3 : (2 * I) * v1 b = 0 := by linear_combination h1 - h2
      have hv1 : v1 b = 0 :=
        (mul_eq_zero.mp h3).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      fin_cases c
      · exact hv0
      · exact hv1
    have hcu : M *ᵥ (star u) = (starRingEnd ℂ μ) • star u := by
      funext a
      have h0 := congrArg (starRingEnd ℂ) (e0 a)
      have h1 := congrArg (starRingEnd ℂ) (e1 a)
      simp only [map_sum, map_sub, map_add, map_mul, Complex.conj_ofReal] at h0 h1
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, u, Pi.star_apply,
        star_sub, star_mul', Complex.star_def, Complex.conj_I]
      have key : ∀ b, M a b * (starRingEnd ℂ (v0 b) - -I * starRingEnd ℂ (v1 b)) =
          (((M a b).re : ℂ) * starRingEnd ℂ (v0 b) - ((M a b).im : ℂ) * starRingEnd ℂ (v1 b)) +
          I * (((M a b).im : ℂ) * starRingEnd ℂ (v0 b) + ((M a b).re : ℂ) *
            starRingEnd ℂ (v1 b)) := by
        intro b
        conv_lhs => rw [← Complex.re_add_im (M a b)]
        linear_combination ((M a b).im * starRingEnd ℂ (v1 b)) * Complex.I_sq
      rw [Finset.sum_congr rfl fun b _ => key b, Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1]
      ring
    have hu' : star u ≠ 0 := by
      intro h; apply hu; simpa using congrArg star h
    have := hM _ _ hu' hcu
    simpa using this
  · have hcu : M *ᵥ (fun b => v0 b + I * v1 b) = μ • (fun b => v0 b + I * v1 b) := by
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      have key : ∀ b, M a b * (v0 b + I * v1 b) =
          (((M a b).re : ℂ) * v0 b - ((M a b).im : ℂ) * v1 b) +
          I * (((M a b).im : ℂ) * v0 b + ((M a b).re : ℂ) * v1 b) := by
        intro b
        conv_lhs => rw [← Complex.re_add_im (M a b)]
        linear_combination ((M a b).im * v1 b) * Complex.I_sq
      rw [Finset.sum_congr rfl fun b _ => key b, Finset.sum_add_distrib, ← Finset.mul_sum, e0 a,
        e1 a]
      ring
    exact hM μ _ hp hcu

/-- The real form is spectrally stable exactly when every eigenvalue of `M` has negative real
part. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_realify_iff (M : Matrix n n ℂ) :
    Linear.SpectrallyStable (realify M) ↔
      ∀ (μ : ℂ) (w : n → ℂ), w ≠ 0 → M *ᵥ w = μ • w → μ.re < 0 := by
  refine ⟨fun hs μ w hw h => ?_, spectrallyStable_realify_of_eigen⟩
  by_contra hμ
  exact not_spectrallyStable_realify hw h (not_lt.mp hμ) hs

end Spectrum

/-! ## Two time scales -/

section TwoTimeScale

variable {n F S : Type*} [Fintype n] [DecidableEq n] [Fintype F] [DecidableEq F] [Fintype S]
  [DecidableEq S]

/-- The splitting of the real coordinates `(phasor, component)` induced by a splitting of the
phasors into fast (`F`) and slow (`S`) ones. -/
def realifySplit (σ : n ≃ F ⊕ S) : n × Fin 2 ≃ (F × Fin 2) ⊕ (S × Fin 2) :=
  (Equiv.prodCongr σ (Equiv.refl (Fin 2))).trans (Equiv.sumProdDistrib F S (Fin 2))

omit [Fintype n] [DecidableEq n] [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] in
/-- The blocks of the real form are the real forms of the blocks. -/
@[tmio T, powerlib_foundation] theorem toBlocks_reindex_realify (σ : n ≃ F ⊕ S)
    (M : Matrix n n ℂ) :
    ((realify M).reindex (realifySplit σ) (realifySplit σ)).toBlocks₁₁ =
        realify (M.reindex σ σ).toBlocks₁₁ ∧
      ((realify M).reindex (realifySplit σ) (realifySplit σ)).toBlocks₁₂ =
        realify (M.reindex σ σ).toBlocks₁₂ ∧
      ((realify M).reindex (realifySplit σ) (realifySplit σ)).toBlocks₂₁ =
        realify (M.reindex σ σ).toBlocks₂₁ ∧
      ((realify M).reindex (realifySplit σ) (realifySplit σ)).toBlocks₂₂ =
        realify (M.reindex σ σ).toBlocks₂₂ :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [Fintype n] [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] in
/-- The real form of a real diagonal matrix. -/
@[tmio T, powerlib_foundation] theorem realify_diagonal_ofReal (r : n → ℝ) :
    realify (Matrix.diagonal fun a => (r a : ℂ)) = Matrix.diagonal fun x => r x.1 := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases h : a = b
  · subst h; fin_cases c <;> fin_cases d <;> simp
  · fin_cases c <;> fin_cases d <;> simp [h]

/-- `diag(ε⁻¹ on the fast phasors, 1 on the slow ones)`, as a complex matrix. -/
def phasorScale (σ : n ≃ F ⊕ S) (ε : ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun a => ((Sum.elim (fun _ => ε⁻¹) (fun _ => 1) (σ a) : ℝ) : ℂ)

omit [Fintype n] [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem realify_phasorScale (σ : n ≃ F ⊕ S) (ε : ℝ) :
    realify (phasorScale σ ε) = splitScale (realifySplit σ) ε := by
  rw [phasorScale, realify_diagonal_ofReal, splitScale]
  congr 1
  funext ⟨a, c⟩
  simp only [realifySplit, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq]
  cases σ a <;> rfl

/-- **Two time scales for a phasor matrix.** Let the phasors of a complex matrix `M` be split by
`σ` into fast and slow ones, with blocks `[[A, B], [C, D]]` (fast first), and let `H` solve
`A H + B = 0` with `C H + D = R`. If the real forms of `A` and of the reduced matrix `R` are
spectrally stable, there is `ε* > 0` such that for every `ε ∈ (0, ε*)` the real form of `M` with
its fast rows multiplied by `ε⁻¹` is spectrally stable
(`exists_epsStar_spectrallyStable_splitScale_mul` read through the real form). -/
@[tmio T, powerlib_foundation] theorem exists_epsStar_spectrallyStable_realify
    (σ : n ≃ F ⊕ S) (M : Matrix n n ℂ) {H : Matrix F S ℂ} {R : Matrix S S ℂ}
    (hH : (M.reindex σ σ).toBlocks₁₁ * H + (M.reindex σ σ).toBlocks₁₂ = 0)
    (hR : (M.reindex σ σ).toBlocks₂₁ * H + (M.reindex σ σ).toBlocks₂₂ = R)
    (hA : Linear.SpectrallyStable (realify (M.reindex σ σ).toBlocks₁₁))
    (hRs : Linear.SpectrallyStable (realify R)) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      Linear.SpectrallyStable (realify (phasorScale σ ε * M)) := by
  obtain ⟨h11, h12, h21, h22⟩ := toBlocks_reindex_realify σ M
  obtain ⟨εs, hεs, h⟩ := exists_epsStar_spectrallyStable_splitScale_mul (realifySplit σ)
    (H := realify H) h11
    (by rw [h12, ← realify_mul, ← realify_add, hH, realify_zero])
    (by rw [h21, h22, ← realify_mul, ← realify_add, hR]) hA hRs
  refine ⟨εs, hεs, fun ε hε hlt => ?_⟩
  rw [realify_mul, realify_phasorScale]
  exact h ε hε hlt

/-- **Two time scales for a phasor matrix, explicit `ε*`.** With the block data of
`exists_epsStar_spectrallyStable_realify` and positive definite Lyapunov matrices `P₀` of the real
form of `R` and `P₂` of the real form of the fast block `A`, the real form of
`phasorScale σ ε * M` is spectrally stable for every `ε ∈ (0, graphEpsStar …)`, the bound of
`spectrallyStable_splitScale_mul_of_lt_graphEpsStar` for the real form of `M`. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_realify_of_lt_graphEpsStar
    (σ : n ≃ F ⊕ S) (M : Matrix n n ℂ) {H : Matrix F S ℂ} {R : Matrix S S ℂ}
    (hH : (M.reindex σ σ).toBlocks₁₁ * H + (M.reindex σ σ).toBlocks₁₂ = 0)
    (hR : (M.reindex σ σ).toBlocks₂₁ * H + (M.reindex σ σ).toBlocks₂₂ = R)
    {P0 : Matrix (S × Fin 2) (S × Fin 2) ℝ} {P2 : Matrix (F × Fin 2) (F × Fin 2) ℝ}
    (hP0 : P0.PosDef) (hP2 : P2.PosDef) (hL0 : P0 * realify R + (realify R)ᵀ * P0 = -1)
    (hL2 : P2 * realify (M.reindex σ σ).toBlocks₁₁ +
      (realify (M.reindex σ σ).toBlocks₁₁)ᵀ * P2 = -1) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε < graphEpsStar (realifySplit σ) (realify M) P0 P2) :
    Linear.SpectrallyStable (realify (phasorScale σ ε * M)) := by
  obtain ⟨h11, h12, h21, h22⟩ := toBlocks_reindex_realify σ M
  rw [realify_mul, realify_phasorScale]
  exact spectrallyStable_splitScale_mul_of_lt_graphEpsStar (realifySplit σ) (H := realify H) h11
    (by rw [h12, ← realify_mul, ← realify_add, hH, realify_zero])
    (by rw [h21, h22, ← realify_mul, ← realify_add, hR]) hP0 hP2 hL0 hL2 hε hεs

end TwoTimeScale

end powerlib.SingularPerturbation
