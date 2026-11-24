import theorem.SingularPerturbation.Realification
import theorem.Criteria.ComplexQuadratic

/-! # The converse of the two-time-scale theorem: strictly unstable blocks

If the boundary-layer (fast) block of a two-time-scale matrix, or its reduced (Schur-complement)
matrix, has an eigenvalue with positive real part, then for every sufficiently small `ε > 0` the
matrix with its fast rows multiplied by `ε⁻¹` has an eigenvalue with positive real part. The
argument is the continuity of the roots of a monic complex polynomial in its coefficients,
proved here from the factorization over `ℂ`: if `|p(z)| < r^N` (`N = deg p`), some root lies
within `r` of `z`.

Scope.
* Generic: complex polynomials, continuous families of complex matrices on any finite index, and
  complex (phasor) matrices split into fast and slow phasors read through their real form
  (`SingularPerturbation.realify`, `SingularPerturbation.phasorScale` of
  `theorem/SingularPerturbation/Realification.lean`); no model. Constant matrices; the
  statements hold for every `ε` in a right neighbourhood of `0` (`∀ᶠ ε in 𝓝[>] 0`), with no
  explicit size of the neighbourhood.

Source: continuity of the roots of a polynomial (A. Ostrowski, *Solution of Equations and Systems
of Equations*, 1960, Appendix A; the elementary bound `min |z − zᵢ|^N ≤ |p(z)|` from
`p(z) = ∏ (z − zᵢ)`); Kokotović–Khalil–O'Reilly, *Singular Perturbation Methods in Control*
(1986), Ch. 2 (the eigenvalues of `[[A₁₁, A₁₂], [A₂₁/ε, A₂₂/ε]]` split into `O(1)` ones near the
reduced matrix and `O(1/ε)` ones near `eig(A₂₂)/ε`).

Results.
* `exists_root_norm_lt`: a monic complex polynomial with `‖p(z)‖ < r^{deg p}`, `r ≥ 0`, has a root
  within `r` of `z`.
* `eventually_exists_eigenvalue_near`: for a family of complex matrices `X μ` continuous at
  `μ = 0` and an eigenvalue `λ` of `X 0`, every `X μ` with `μ` near `0` has an eigenvalue within
  any prescribed distance of `λ`; `eventually_exists_eigenpair_re_pos`: an eigenvalue with
  positive real part persists.
* `eventually_not_spectrallyStable_realify_of_fast`: an eigenvalue with positive real part of the
  fast block of `M` makes `realify (phasorScale σ ε * M)` not spectrally stable for every small
  `ε > 0` (the family `diag(1 fast, ε slow) M` at `ε = 0`).
* `eventually_not_spectrallyStable_realify_of_slow`: for invertible `M` with blocks
  `A H + B = 0`, `C H + D = R`, an eigenvalue with positive real part of `R` does the same (the
  family `M⁻¹ diag(ε fast, 1 slow)`, the inverse of the scaled matrix, whose eigenvalue
  `1/λ` at `ε = 0` has eigenvector `(H w, w)`).
* `exists_complexQuadratic_root_re_pos`: `s² + (a + jb) s + c` (`a, b, c` real) has a root with
  positive real part if `a < 0`, or `c < 0` and `a ≠ 0` (Vieta, `Criteria.vieta_discriminant`).
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix Polynomial Filter Topology

/-! ## Roots of a monic polynomial near a near-zero -/

/-- A monic complex polynomial with `‖p(z)‖ < r^{deg p}` has a root within `r` of `z`. -/
@[tmio T, powerlib_foundation] theorem exists_root_norm_lt {p : ℂ[X]} (hp : p.Monic) (z : ℂ)
    {r : ℝ} (hr : 0 ≤ r) (h : ‖p.eval z‖ < r ^ p.natDegree) :
    ∃ w ∈ p.roots, ‖z - w‖ < r := by
  by_contra hc
  push Not at hc
  have hs := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := splits_iff_card_roots.mp hs
  have heval : ‖p.eval z‖ = (p.roots.map fun w => ‖z - w‖).prod := by
    rw [hs.eval_eq_prod_roots_of_monic hp, ← normHom_apply, map_multiset_prod, Multiset.map_map]
    rfl
  have hle : (p.roots.map fun _ => r).prod ≤ (p.roots.map fun w => ‖z - w‖).prod :=
    Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => hr) hc
  rw [Multiset.map_const', Multiset.prod_replicate, hcard, ← heval] at hle
  linarith

/-! ## Eigenvalues of a continuous family of matrices -/

section Family

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Continuity of eigenvalues.** If `X` is continuous at `0` and `λ` is an eigenvalue of `X 0`,
then for every `r > 0` and every `μ` near `0`, `X μ` has an eigenvalue within `r` of `λ`. -/
@[tmio T, powerlib_foundation] theorem eventually_exists_eigenvalue_near
    {X : ℝ → Matrix n n ℂ} (hX : ContinuousAt X 0) {lam : ℂ}
    (hdet : (Matrix.scalar n lam - X 0).det = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ μ in 𝓝 (0 : ℝ), ∃ ν : ℂ, (Matrix.scalar n ν - X μ).det = 0 ∧ ‖lam - ν‖ < r := by
  have hcont : ContinuousAt (fun μ => (Matrix.scalar n lam - X μ).det) 0 :=
    ((continuous_id : Continuous fun A : Matrix n n ℂ => A).matrix_det).continuousAt.comp
      (continuousAt_const.sub hX)
  have hlim : Tendsto (fun μ => (Matrix.scalar n lam - X μ).det) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto
    rwa [hdet] at this
  have hpos : 0 < r ^ Fintype.card n := pow_pos hr _
  filter_upwards [(Metric.tendsto_nhds.mp hlim) _ hpos] with μ hμ
  rw [dist_zero_right] at hμ
  have hmon := (X μ).charpoly_monic
  have heval : (X μ).charpoly.eval lam = (Matrix.scalar n lam - X μ).det := Matrix.eval_charpoly _ _
  obtain ⟨w, hw, hlt⟩ := exists_root_norm_lt hmon lam hr.le
    (by rw [heval, Matrix.charpoly_natDegree_eq_dim]; exact hμ)
  refine ⟨w, ?_, hlt⟩
  have := (Polynomial.mem_roots hmon.ne_zero).mp hw
  rwa [Polynomial.IsRoot, Matrix.eval_charpoly] at this

/-- An eigenpair of `X 0` with positive real part persists, as an eigenpair with real part above
half of it, for every `μ` near `0`. -/
@[tmio T, powerlib_foundation] theorem eventually_exists_eigenpair_re_pos
    {X : ℝ → Matrix n n ℂ} (hX : ContinuousAt X 0) {lam : ℂ} (hlam : 0 < lam.re) {v : n → ℂ}
    (hv : v ≠ 0) (h : X 0 *ᵥ v = lam • v) :
    ∀ᶠ μ in 𝓝 (0 : ℝ), ∃ (ν : ℂ) (w : n → ℂ), w ≠ 0 ∧ X μ *ᵥ w = ν • w ∧ lam.re / 2 < ν.re := by
  have hdet : (Matrix.scalar n lam - X 0).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv, ?_⟩
    ext i
    simp [Matrix.sub_mulVec, h]
  filter_upwards [eventually_exists_eigenvalue_near hX hdet (half_pos hlam)] with μ hμ
  obtain ⟨ν, hν, hlt⟩ := hμ
  obtain ⟨w, hw, hwz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hν
  refine ⟨ν, w, hw, ?_, ?_⟩
  · ext i
    have := congrFun hwz i
    simp [Matrix.sub_mulVec, sub_eq_zero] at this
    simp [this]
  · have hre : |(lam - ν).re| < lam.re / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm _) hlt
    rw [Complex.sub_re, abs_lt] at hre
    linarith [hre.2]

end Family

/-! ## Two time scales: the converse -/

section Converse

variable {n F S : Type*} [Fintype n] [DecidableEq n] [Fintype F] [DecidableEq F] [Fintype S]
  [DecidableEq S]

omit [DecidableEq n] [DecidableEq F] [DecidableEq S] in
/-- A sum over `n` split along `σ`. -/
@[tmio T, powerlib_foundation] private theorem sum_split (σ : n ≃ F ⊕ S) (f : n → ℂ) :
    ∑ b, f b = ∑ j, f (σ.symm (.inl j)) + ∑ k, f (σ.symm (.inr k)) := by
  rw [← σ.symm.sum_comp, Fintype.sum_sum_type]

omit [DecidableEq F] [DecidableEq S] in
/-- **A strictly unstable boundary layer.** If the fast block of the phasor matrix `M` (split by
`σ`) has an eigenvalue with positive real part, then for every sufficiently small `ε > 0` the
real form of `M` with its fast rows multiplied by `ε⁻¹` is not spectrally stable. -/
@[tmio T, powerlib_foundation] theorem eventually_not_spectrallyStable_realify_of_fast
    (σ : n ≃ F ⊕ S) (M : Matrix n n ℂ) {lam : ℂ} (hlam : 0 < lam.re) {v : F → ℂ} (hv : v ≠ 0)
    (h : (M.reindex σ σ).toBlocks₁₁ *ᵥ v = lam • v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ Linear.SpectrallyStable (realify (phasorScale σ ε * M)) := by
  set d : ℝ → n → ℂ := fun ε a => Sum.elim (fun _ => (1 : ℂ)) (fun _ => (ε : ℂ)) (σ a)
  set Y : ℝ → Matrix n n ℂ := fun ε => Matrix.diagonal (d ε) * M
  have hY : Continuous Y := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Y, Matrix.diagonal_mul, d]
    cases σ a <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact continuous_const
    · exact Complex.continuous_ofReal.mul continuous_const
  set y : n → ℂ := fun a => Sum.elim v 0 (σ a)
  have hy : y ≠ 0 := by
    intro h0
    apply hv
    funext j
    simpa [y] using congrFun h0 (σ.symm (.inl j))
  have h0 : Y 0 *ᵥ y = lam • y := by
    funext a
    simp only [Y, d, Matrix.mulVec, dotProduct, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
    obtain ⟨x, rfl⟩ := σ.symm.surjective a
    rcases x with i | k
    · have hi := congrFun h i
      simp only [Matrix.mulVec, dotProduct, Matrix.toBlocks₁₁, Matrix.reindex_apply,
        Matrix.submatrix_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at hi
      simp only [Equiv.apply_symm_apply, Sum.elim_inl, one_mul, y]
      rw [sum_split σ]
      simp [hi]
    · simp [y]
  have hev := eventually_exists_eigenpair_re_pos hY.continuousAt hlam hy h0
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ε hε hpos
  obtain ⟨ν, w, hw, hνw, hre⟩ := hε
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hYε : Y ε = (ε : ℂ) • (phasorScale σ ε * M) := by
    ext a b
    simp only [Y, d, phasorScale, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    cases σ a <;> simp [hε0]
  refine not_spectrallyStable_realify (w := w) (μ := ν / ε) hw ?_ ?_
  · rw [hYε, Matrix.smul_mulVec] at hνw
    funext a
    have := congrFun hνw a
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linear_combination this
  · rw [Complex.div_ofReal_re]
    exact (div_pos (by linarith) hpos).le

omit [DecidableEq F] [DecidableEq S] in
/-- **A strictly unstable reduced matrix.** Let `M` be invertible, split by `σ` with blocks
`[[A, B], [C, D]]` (fast first), `A H + B = 0` and `C H + D = R`. If `R` has an eigenvalue with
positive real part, then for every sufficiently small `ε > 0` the real form of `M` with its fast
rows multiplied by `ε⁻¹` is not spectrally stable. -/
@[tmio T, powerlib_foundation] theorem eventually_not_spectrallyStable_realify_of_slow
    (σ : n ≃ F ⊕ S) {M : Matrix n n ℂ} (hM : IsUnit M.det) {H : Matrix F S ℂ}
    {R : Matrix S S ℂ} (hH : (M.reindex σ σ).toBlocks₁₁ * H + (M.reindex σ σ).toBlocks₁₂ = 0)
    (hR : (M.reindex σ σ).toBlocks₂₁ * H + (M.reindex σ σ).toBlocks₂₂ = R) {lam : ℂ}
    (hlam : 0 < lam.re) {w : S → ℂ} (hw : w ≠ 0) (h : R *ᵥ w = lam • w) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ Linear.SpectrallyStable (realify (phasorScale σ ε * M)) := by
  set d : ℝ → n → ℂ := fun ε a => Sum.elim (fun _ => (ε : ℂ)) (fun _ => (1 : ℂ)) (σ a)
  set Xs : ℝ → Matrix n n ℂ := fun ε => M⁻¹ * Matrix.diagonal (d ε)
  have hX : Continuous Xs := by
    refine continuous_const.matrix_mul ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.diagonal_apply, d]
    split_ifs
    · cases σ a <;> simp only [Sum.elim_inl, Sum.elim_inr]
      · exact Complex.continuous_ofReal
      · exact continuous_const
    · exact continuous_const
  have hlam0 : lam ≠ 0 := fun h0 => by simp [h0] at hlam
  set y : n → ℂ := fun a => Sum.elim (H *ᵥ w) w (σ a)
  have hy : y ≠ 0 := by
    intro h0
    apply hw
    funext k
    simpa [y] using congrFun h0 (σ.symm (.inr k))
  -- `M y = λ · diag(0 fast, 1 slow) y`
  have hMy : M *ᵥ y = lam • (Matrix.diagonal (d 0) *ᵥ y) := by
    funext a
    obtain ⟨x, rfl⟩ := σ.symm.surjective a
    have hrow : (M *ᵥ y) (σ.symm x) =
        ∑ j, M (σ.symm x) (σ.symm (.inl j)) * (H *ᵥ w) j +
          ∑ k, M (σ.symm x) (σ.symm (.inr k)) * w k := by
      rw [Matrix.mulVec, dotProduct, sum_split σ]
      simp [y]
    rw [hrow, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
    rcases x with i | k
    · have key : ((M.reindex σ σ).toBlocks₁₁ *ᵥ (H *ᵥ w)) i +
          ((M.reindex σ σ).toBlocks₁₂ *ᵥ w) i = 0 := by
        rw [Matrix.mulVec_mulVec, ← Pi.add_apply, ← Matrix.add_mulVec, hH, Matrix.zero_mulVec]
        rfl
      simp only [Matrix.mulVec, dotProduct, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
        Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply] at key
      simp only [d, Equiv.apply_symm_apply, Sum.elim_inl, Complex.ofReal_zero, zero_mul, mul_zero]
      simpa [Matrix.mulVec, dotProduct] using key
    · have key : ((M.reindex σ σ).toBlocks₂₁ *ᵥ (H *ᵥ w)) k +
          ((M.reindex σ σ).toBlocks₂₂ *ᵥ w) k = lam * w k := by
        rw [Matrix.mulVec_mulVec, ← Pi.add_apply, ← Matrix.add_mulVec, hR, h]
        rfl
      simp only [Matrix.mulVec, dotProduct, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
        Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply] at key
      simp only [d, y, Equiv.apply_symm_apply, Sum.elim_inr, one_mul]
      simpa [Matrix.mulVec, dotProduct] using key
  have hMinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have h0 : Xs 0 *ᵥ y = lam⁻¹ • y := by
    have : Matrix.diagonal (d 0) *ᵥ y = lam⁻¹ • (M *ᵥ y) := by
      rw [hMy, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    simp only [Xs]
    rw [← Matrix.mulVec_mulVec, this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMinv,
      Matrix.one_mulVec]
  have hre0 : 0 < lam⁻¹.re := by
    rw [Complex.inv_re]
    exact div_pos hlam (Complex.normSq_pos.mpr hlam0)
  have hev := eventually_exists_eigenpair_re_pos hX.continuousAt hre0 hy h0
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ε hε hpos
  obtain ⟨ν, u, hu, hνu, hre⟩ := hε
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hre
    linarith
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hPX : phasorScale σ ε * M * Xs ε = 1 := by
    simp only [Xs]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv M hM, Matrix.one_mul,
      phasorScale, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [d]
    cases σ a <;> simp [hε0]
  refine not_spectrallyStable_realify (w := u) (μ := ν⁻¹) hu ?_ ?_
  · have key : (phasorScale σ ε * M) *ᵥ (Xs ε *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, hPX, Matrix.one_mulVec]
    rw [hνu, Matrix.mulVec_smul] at key
    conv_rhs => rw [← key]
    rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
  · rw [Complex.inv_re]
    exact (div_pos (by linarith) (Complex.normSq_pos.mpr hν0)).le

end Converse

/-! ## A complex quadratic with a root in the right half-plane -/

/-- `s² + (a + jb) s + c` with real `a, b, c` has a root with positive real part if `a < 0`, or
if `c < 0` and `a ≠ 0` (the root sum `−a`, and Vieta's discriminant `a² c`). -/
@[tmio T, powerlib_foundation] theorem exists_complexQuadratic_root_re_pos (a b c : ℝ)
    (h : a < 0 ∨ (c < 0 ∧ a ≠ 0)) :
    ∃ s : ℂ, s ^ 2 + (⟨a, b⟩ : ℂ) * s + (c : ℂ) = 0 ∧ 0 < s.re := by
  set α : ℂ := ⟨a, b⟩
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self (discrim (1 : ℂ) α c)
  obtain ⟨s, hs⟩ := exists_quadratic_eq_zero (one_ne_zero) ⟨d, hd⟩
  have hs' : s ^ 2 + α * s + c = 0 := by linear_combination hs
  have hs₂ := Criteria.quadratic_partner hs'
  have hsum : s.re + (-α - s).re = -a := by simp [α]
  by_contra hno
  push Not at hno
  have h1 := hno s hs'
  have h2 := hno _ hs₂
  rcases h with ha | ⟨hc, ha⟩
  · linarith
  · have hv := Criteria.vieta_discriminant s (-α - s)
    rw [← Criteria.quadratic_partner_sum α s, ← Criteria.quadratic_partner_prod hs'] at hv
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, α,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hv
    have hneg : a ^ 2 * c < 0 := mul_neg_of_pos_of_neg (by positivity) hc
    have hpos : 0 ≤ s.re * (-α - s).re * ((s.re + (-α - s).re) ^ 2 + (s.im - (-α - s).im) ^ 2) :=
      mul_nonneg (mul_nonneg_of_nonpos_of_nonpos h1 h2) (by positivity)
    linarith

end powerlib.SingularPerturbation
