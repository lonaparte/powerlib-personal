import theorem.ParametricResonance.SmoothForcedOrbit

/-! # Real modal coordinates from the critical eigenvectors and a basis-free stable condition

The end-to-end statements for the four-state PSC and matching cores took a real basis `W` of the
stable subspace (`A W = W A_s`, `W' W = I`, `u W = 0`, `W' r = 0`) and a contraction condition on
`A_s` as hypotheses. Here `W` is constructed from the critical eigenvectors `r`, `u` alone, and the
condition on the stable block is expressed on the physical state matrix: the spectral radius of
`e^{TA}(I − Π)` below one, `Π` the real projector onto the critical plane.

Scope.
* `A : Matrix X X ℝ` with `card X = m + 2` and a simple pair `±jΩ`, `Ω ≠ 0`: right and left
  eigenvectors `r`, `u` with `u r = 1`; any `T`.
* The stable complement is `{v : Re u·v = Im u·v = 0}`, of dimension `m` (rank–nullity), invariant
  under `A` because `u` is a left eigenvector.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1 (modal decomposition with right and left eigenvectors), as used by the
averaging step of §2.2.

Results.
* `critP`, `critQ`, `crit_real` — `[2 Re u; 2 Im u][Re r, −Im r] = I` and
  `[2 Re u; 2 Im u] A = base(0, Ω) [2 Re u; 2 Im u]`.
* `mulVec_eq_of_cols`, `exists_stable_basis` — `W`, `W'`, `A_s` with `A W = W A_s`, `W' W = I`,
  `u W = 0`, `W' r = 0`.
* `norm_le_spectralRadius`, `expS_compl` — `e^{TA}(I − Π) = P diag(0, e^{TA_s}) Q`.
* `stable_modal_of_eig` — real modal coordinates `Q A P = diag(base(0, Ω), A_s)` with critical
  columns `Re r`, `−Im r`, and `ρ(e^{TA_s}) < 1` from `ρ(e^{TA}(I − Π)) < 1`.

Corrections.
None: removes the stable basis from the hypotheses of the end-to-end statements.

Family and connection conclusions.
None: static evidence on the linear algebra of the modal decomposition.
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix Module
open scoped Matrix.Norms.Operator
open BlockAveraging (expS)

section StableBasis

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `[Re r, −Im r]`. -/
def critP (r : X → ℂ) : Matrix X (Fin 2) ℝ := Matrix.of fun i j => ![(r i).re, -(r i).im] j

/-- `[2 Re u; 2 Im u]`. -/
def critQ (u : X → ℂ) : Matrix (Fin 2) X ℝ := Matrix.of fun i j => ![2 * (u j).re, 2 * (u j).im] i

omit [DecidableEq X] in
/-- The critical pair in real form: `[2 Re u; 2 Im u] [Re r, −Im r] = I` and
`[2 Re u; 2 Im u] A = base(0, Ω) [2 Re u; 2 Im u]`. -/
@[tmio T, powerlib_foundation] theorem crit_real {A : Matrix X X ℝ} {Ω : ℝ} (hΩ : Ω ≠ 0)
    {r u : X → ℂ} (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1) :
    critQ u * critP r = 1 ∧ critQ u * A = TwoToOne.base 0 Ω * critQ u := by
  obtain ⟨hx, hy⟩ := real_right_eig_gen hr
  obtain ⟨hp, hq⟩ := real_left_eig_gen hu
  set x : X → ℝ := fun k => (r k).re with hxd
  set y : X → ℝ := fun k => (r k).im with hyd
  set p : X → ℝ := fun k => (u k).re with hpd
  set q : X → ℝ := fun k => (u k).im with hqd
  have hre : p ⬝ᵥ x - q ⬝ᵥ y = 1 := by
    have h := congrArg Complex.re hur
    simp [dotProduct, Complex.re_sum] at h
    simp only [hxd, hyd, hpd, hqd, dotProduct]; linarith
  have him : p ⬝ᵥ y + q ⬝ᵥ x = 0 := by
    have h := congrArg Complex.im hur
    simp [dotProduct, Complex.im_sum, Finset.sum_add_distrib] at h
    simp only [hxd, hyd, hpd, hqd, dotProduct]; linarith
  have e1 : -Ω * (q ⬝ᵥ x) = -Ω * (p ⬝ᵥ y) := by
    have h := Matrix.dotProduct_mulVec p A x
    rw [hx, hp, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have e2 : -Ω * (q ⬝ᵥ y) = Ω * (p ⬝ᵥ x) := by
    have h := Matrix.dotProduct_mulVec p A y
    rw [hy, hp, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have hqx : q ⬝ᵥ x = p ⬝ᵥ y := mul_left_cancel₀ (neg_ne_zero.2 hΩ) e1
  have hpx2 : p ⬝ᵥ x = -(q ⬝ᵥ y) :=
    mul_left_cancel₀ hΩ (show Ω * (p ⬝ᵥ x) = Ω * (-(q ⬝ᵥ y)) by linarith)
  have hpx : p ⬝ᵥ x = 1 / 2 := by linarith
  have hqy : q ⬝ᵥ y = -(1 / 2) := by linarith
  have hpy : p ⬝ᵥ y = 0 := by linarith
  have hqx0 : q ⬝ᵥ x = 0 := by linarith
  refine ⟨?_, ?_⟩
  · simp only [dotProduct, hxd, hyd, hpd, hqd] at hpx hqy hpy hqx0
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [critQ, critP, Matrix.mul_apply, mul_assoc, ← Finset.mul_sum] <;> linarith
  · ext a k
    have hpk := congrFun hp k
    have hqk := congrFun hq k
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, hpd, hqd] at hpk hqk
    fin_cases a <;> simp [critQ, Matrix.mul_apply, Fin.sum_univ_two, TwoToOne.base,
      ← Finset.mul_sum, mul_assoc] <;> linarith

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem mulVec_eq_of_cols {Z : Type*} [Fintype Z] [DecidableEq Z]
    {M N : Matrix X Z ℝ} (h : ∀ c : Z → ℝ, M *ᵥ c = N *ᵥ c) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

/-- A real basis of the stable complement from the critical eigenvectors alone: for `A` with the
simple pair `±jΩ` (`r`, `u`, `u r = 1`) on an `(m + 2)`-dimensional state space there are
`W` (columns: a basis of `{v : Re u·v = Im u·v = 0}`), its left inverse `W'` annihilating the
pair, and `A_s = W' A W`, with `A W = W A_s`, `W' W = I`, `u W = 0`, `W' r = 0`. -/
@[tmio T, powerlib_foundation] theorem exists_stable_basis {A : Matrix X X ℝ} {Ω : ℝ} (hΩ : Ω ≠ 0)
    {r u : X → ℂ} (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1) {m : ℕ}
    (hm : Fintype.card X = m + 2) :
    ∃ (W : Matrix X (Fin m) ℝ) (W' : Matrix (Fin m) X ℝ),
      A * W = W * (W' * A * W) ∧ W' * W = 1 ∧ u ᵥ* W.map (algebraMap ℝ ℂ) = 0 ∧
        W'.map (algebraMap ℝ ℂ) *ᵥ r = 0 := by
  obtain ⟨hQP, hQA⟩ := crit_real hΩ hr hu hur
  set Pc := critP r with hPc
  set Qc := critQ u with hQc
  set K : Submodule ℝ (X → ℝ) := LinearMap.ker (Matrix.mulVecLin Qc) with hK
  have hmemK : ∀ v, v ∈ K ↔ Qc *ᵥ v = 0 := fun v => by simp [hK]
  have hsurj : LinearMap.range (Matrix.mulVecLin Qc) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    exact ⟨Pc *ᵥ w, by simp [Matrix.mulVec_mulVec, hQP]⟩
  have hfin : finrank ℝ K = m := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Qc)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, hm] at h
    rw [hK]; omega
  set b : Basis (Fin m) ℝ K := Module.finBasisOfFinrankEq ℝ K hfin with hb
  -- the projection onto `K` along the critical plane
  have hpr : ∀ v : X → ℝ, v - Pc *ᵥ (Qc *ᵥ v) ∈ K := fun v => by
    rw [hmemK, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec, sub_self]
  set pr : (X → ℝ) →ₗ[ℝ] K := LinearMap.codRestrict K
    (LinearMap.id - (Matrix.mulVecLin (Pc * Qc))) (fun v => by
      simpa [Matrix.mulVec_mulVec] using hpr v) with hprd
  have hprv : ∀ v, (pr v : X → ℝ) = v - (Pc * Qc) *ᵥ v := fun v => rfl
  have hprK : ∀ k : K, pr k = k := fun k => by
    apply Subtype.ext
    have hk : Qc *ᵥ (k : X → ℝ) = 0 := (hmemK _).1 k.2
    rw [hprv, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero, sub_zero]
  set W : Matrix X (Fin m) ℝ := Matrix.of fun i j => (b j : X → ℝ) i with hW
  set W' : Matrix (Fin m) X ℝ := LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ pr) with hW'
  have hWc : ∀ c, W *ᵥ c = ((b.equivFun.symm c : K) : X → ℝ) := fun c => by
    funext i
    simp [hW, Matrix.mulVec, dotProduct, Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  have hW'v : ∀ v, W' *ᵥ v = b.equivFun (pr v) := fun v => by
    rw [hW', LinearMap.toMatrix'_mulVec]; rfl
  have hWK : ∀ k : K, W *ᵥ (W' *ᵥ (k : X → ℝ)) = k := fun k => by
    rw [hW'v, hprK, hWc, LinearEquiv.symm_apply_apply]
  have hWmem : ∀ c, W *ᵥ c ∈ K := fun c => by rw [hWc]; exact Submodule.coe_mem _
  refine ⟨W, W', ?_, ?_, ?_, ?_⟩
  · refine mulVec_eq_of_cols fun c => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    have hAK : A *ᵥ (W *ᵥ c) ∈ K := by
      rw [hmemK, Matrix.mulVec_mulVec, hQA, ← Matrix.mulVec_mulVec, (hmemK _).1 (hWmem c),
        Matrix.mulVec_zero]
    exact (hWK ⟨_, hAK⟩).symm
  · refine mulVec_eq_of_cols fun c => ?_
    rw [← Matrix.mulVec_mulVec, hW'v, Matrix.one_mulVec]
    have : pr (W *ᵥ c) = b.equivFun.symm c := by
      apply Subtype.ext
      rw [hWc]
      exact congrArg Subtype.val (hprK _)
    rw [this, LinearEquiv.apply_symm_apply]
  · funext j
    have hj : Qc *ᵥ (b j : X → ℝ) = 0 := (hmemK _).1 (b j).2
    have h0 := congrFun hj 0
    have h1 := congrFun hj 1
    simp only [hQc, critQ, Matrix.mulVec, dotProduct, Matrix.of_apply] at h0 h1
    simp at h0 h1
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hW, Matrix.of_apply, Pi.zero_apply]
    have h0' : ∑ x, (u x).re * (b j : X → ℝ) x = 0 := by
      have : ∑ x, 2 * ((u x).re * (b j : X → ℝ) x) = 0 := by simpa [mul_assoc] using h0
      rw [← Finset.mul_sum] at this; linarith
    have h1' : ∑ x, (u x).im * (b j : X → ℝ) x = 0 := by
      have : ∑ x, 2 * ((u x).im * (b j : X → ℝ) x) = 0 := by simpa [mul_assoc] using h1
      rw [← Finset.mul_sum] at this; linarith
    apply Complex.ext
    · simpa [Complex.re_sum] using h0'
    · simpa [Complex.im_sum] using h1'
  · have hx : W' *ᵥ (fun k => (r k).re) = 0 := by
      rw [hW'v]
      have : pr (fun k => (r k).re) = 0 := by
        apply Subtype.ext
        have e : (fun k => (r k).re) = Pc *ᵥ Pi.single 0 1 := by
          funext k; simp [hPc, critP]
        rw [hprv, e, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQP, Matrix.mul_one, sub_self]
        rfl
      rw [this, map_zero]
    have hy : W' *ᵥ (fun k => (r k).im) = 0 := by
      rw [hW'v]
      have : pr (fun k => (r k).im) = 0 := by
        apply Subtype.ext
        have e : (fun k => (r k).im) = Pc *ᵥ (-Pi.single 1 1) := by
          funext k; simp [hPc, critP, Matrix.mulVec_neg]
        rw [hprv, e, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQP, Matrix.mul_one, sub_self]
        rfl
      rw [this, map_zero]
    funext k
    have h1 := congrFun hx k
    have h2 := congrFun hy k
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1 h2
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
    apply Complex.ext
    · simp [Complex.re_sum]; linarith [h1]
    · simp [Complex.im_sum]; linarith [h2]

omit [DecidableEq X] in
/-- An eigenvalue of `M` is bounded by the spectral radius. -/
@[tmio T, powerlib_foundation] theorem norm_le_spectralRadius {M : Matrix X X ℂ} {μ : ℂ}
    {v : X → ℂ} (hv : v ≠ 0) (h : M *ᵥ v = μ • v) [DecidableEq X] :
    (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ M := by
  have hz : μ ∈ spectrum ℂ M := LTI.mem_spectrum_iff_exists_eigvec.2 ⟨v, hv, h⟩
  rw [spectralRadius_eq_of_unital]
  exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ M) => (‖k‖₊ : ENNReal)) μ hz

/-- The linear monodromy restricted to the complement of the critical plane: in modal coordinates
`e^{TA}(I − Π) = P diag(0, e^{TA_s}) Q` when `I − Π = P diag(0, I) Q`. -/
@[tmio T, powerlib_foundation] theorem expS_compl {Y : Type*} [Fintype Y] [DecidableEq Y]
    {A : Matrix X X ℝ} {Ω : ℝ} {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * A * P = fromBlocks (TwoToOne.base 0 Ω) 0 0 As) (T : ℝ) {Pim : Matrix X X ℝ}
    (hPim : 1 - Pim = P * fromBlocks 0 0 0 1 * Q) :
    expS A T * (1 - Pim) = P * fromBlocks 0 0 0 (expS As T) * Q := by
  set B := fromBlocks (TwoToOne.base 0 Ω) 0 0 As with hB
  set φ := conjHom P Q hPQ hQP
  have hφ : ∀ M, φ M = P * M * Q := fun M => rfl
  have hA : A = P * B * Q := by
    rw [← hA0, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_assoc,
      hPQ, Matrix.mul_one]
  have hφc : Continuous φ := by
    show Continuous fun M => P * M * Q
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hexpA : expS A T = P * expS B T * Q := by
    have e : NormedSpace.exp (T • A) = φ (NormedSpace.exp (T • B)) := by
      have h := NormedSpace.map_exp φ hφc (T • B)
      convert h.symm using 2
      all_goals first | rfl | rw [hφ, hA, Matrix.mul_smul, Matrix.smul_mul]
    rw [BlockAveraging.expS, BlockAveraging.expS, e, hφ]
  have hpsi : expS B T = fromBlocks (NormalForm.rot (2 * Ω * T / 2)) 0 0 (expS As T) := by
    have h := expS_block (2 * Ω) As T
    rw [show 2 * Ω / 2 = Ω by ring] at h
    rw [hB, h]; rfl
  rw [hexpA, hPim]
  calc P * expS B T * Q * (P * fromBlocks 0 0 0 1 * Q) =
      P * (expS B T * (Q * P) * fromBlocks 0 0 0 1) * Q := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hQP, Matrix.mul_one, hpsi, fromBlocks_multiply]
      simp

/-- Real modal coordinates with a spectrally contracting stable block, from the critical
eigen-data and a basis-free condition on the physical matrix: the spectral radius of
`e^{TA}(I − Π)` (`Π = [Re r, −Im r][2 Re u; 2 Im u]`, the real projector onto the critical plane)
below one. -/
@[tmio T, powerlib_foundation] theorem stable_modal_of_eig {n m : ℕ} (hnm : n = m + 2)
    {A : Matrix (Fin n) (Fin n) ℝ} {Ω : ℝ} (hΩ : Ω ≠ 0) {r u : Fin n → ℂ}
    (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1) (T : ℝ)
    (hsr : spectralRadius ℂ ((expS A T * (1 - critP r * critQ u)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ (P : Matrix (Fin n) (Fin 2 ⊕ Fin m) ℝ) (Q : Matrix (Fin 2 ⊕ Fin m) (Fin n) ℝ)
      (As : Matrix (Fin m) (Fin m) ℝ), P * Q = 1 ∧ Q * P = 1 ∧
      Q * A * P = fromBlocks (TwoToOne.base 0 Ω) 0 0 As ∧
      BlockAveraging.physLeft Q = u ∧ BlockAveraging.physRight P = r ∧
      spectralRadius ℂ ((expS As T).map (algebraMap ℝ ℂ)) < 1 := by
  obtain ⟨W, W', hW, hWW, huW, hWr⟩ := exists_stable_basis hΩ hr hu hur (m := m)
    (by simp [hnm])
  set As := W' * A * W
  have e : Fin n ≃ Fin 2 ⊕ Fin m := (finCongr (by omega)).trans finSumFinEquiv.symm
  obtain ⟨hQP, hPQ, hA0, hL, hR⟩ := modal_of_basis e hΩ hr hu hur hW hWW huW hWr
  set P := basisP r W with hPd
  set Q := basisQ u W' with hQd
  have hblk : P * fromBlocks 0 0 0 1 * Q = W * W' := by
    have h1 : P * fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 (1 : Matrix (Fin m) (Fin m) ℝ) =
        Matrix.fromCols 0 W := by
      ext i j
      rcases j with j | j <;> simp [hPd, basisP, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.one_apply]
    rw [h1, hQd, basisQ, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, zero_add]
  have hPim : 1 - critP r * critQ u = P * fromBlocks 0 0 0 1 * Q := by
    rw [hblk, ← hPQ, hPd, hQd, basisP, basisQ, Matrix.fromCols_mul_fromRows]
    simp only [critP, critQ]
    abel
  have hcompl := expS_compl hPQ hQP As hA0 T hPim
  refine ⟨P, Q, As, hPQ, hQP, hA0, hL, hR, ?_⟩
  rw [← LTI.schurStable_iff_spectralRadius_lt_one]
  intro μ w hw heq
  set v : Fin n → ℂ := P.map (algebraMap ℝ ℂ) *ᵥ Sum.elim (0 : Fin 2 → ℂ) w with hv
  have hQv : Q.map (algebraMap ℝ ℂ) *ᵥ v = Sum.elim (0 : Fin 2 → ℂ) w := by
    rw [hv, Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hQv
    apply hw
    funext j
    have := congrFun hQv (Sum.inr j)
    simpa using this.symm
  have hev : (expS A T * (1 - critP r * critQ u)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v := by
    rw [hcompl, Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hQv, fromBlocks_map, Matrix.fromBlocks_mulVec]
    simp only [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, add_zero, zero_add]
    have hc : (Sum.elim (0 : Fin 2 → ℂ) w) ∘ Sum.inr = w := rfl
    rw [hc, heq, hv]
    have : (Sum.elim (0 : Fin 2 → ℂ) (μ • w)) = μ • Sum.elim (0 : Fin 2 → ℂ) w := by
      funext j; rcases j with j | j <;> simp
    rw [this, Matrix.mulVec_smul]
  have hle := norm_le_spectralRadius hv0 hev
  have hlt : (‖μ‖₊ : ENNReal) < 1 := hle.trans_lt hsr
  exact_mod_cast hlt

end StableBasis

end powerlib.ParametricResonance.ForcedOrbit
