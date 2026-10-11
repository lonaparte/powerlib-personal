import theorem.Modal.Participation

/-! Modal response, residues, poles and repeated-eigenvalue participation (foundation).

Source: work-sync `theory/T-small-signal-stability.md` §1.5 (modal decomposition and free
response), §1.9 (transfer-function poles versus eigenvalues);
`theory/T-participation-factor.md` §1.1 (PF as residue), §1.3 (conjugate-pair contribution),
§1.8 (repeated eigenvalues: subspace participation); `theory/T-eigenvalue-analysis.md` §1.1.

All statements assume a `ModalBasis` (diagonalisable state matrix); defective matrices are
excluded.

* `modal_free_response`: every solution of the real LTI model `ẋ = A x` satisfies
  `x(t) = Σ_i e^{λ_i t} (ψ_iᵀ x(0)) v_i`; with `x(0) = e_k`, `x_k(t) = Σ_i p_{ki} e^{λ_i t}`
  (`pf_free_response`): the PF is the modal weight of the `(k,k)` free-response channel.
* `conj_pair_contribution`: `p e^{λt} + p̄ e^{λ̄t} = 2|p| e^{σt} cos(ωt + arg p)`.
* `tendsto_resolvent_residue`, `tendsto_io_residue`: at a simple eigenvalue, `(s − λ_i)` times
  the resolvent / transfer channel tends to the modal residue.
* `det_sub_eq_prod`, `charpoly_eq_prod`, `rootMultiplicity_eq_card`: the characteristic
  polynomial is `Π_i (X − λ_i)`, so the algebraic multiplicity of `μ` is the number of modal
  indices with `λ_i = μ`.
* `spectralProj`: `E_μ = Σ_{λ_i = μ} v_i ψ_iᵀ`. It does not depend on the chosen modal basis
  (`spectralProj_eq`); hence the subspace participation `P_{k,μ} = Σ_{λ_i = μ} p_{ki}` is
  basis independent (`subspacePF_eq`) even though individual `p_{ki}` are not, and
  `Σ_k P_{k,μ}` is the algebraic multiplicity of `μ` (`sum_subspacePF`).
* Poles: for a real LTI model with diagonalisable state matrix, simple eigenvalues and
  modal (PBH) controllability/observability, `G` has a simple pole with nonzero residue at
  exactly the eigenvalues (`transfer_pole_iff`); away from the spectrum `G` is continuous.
-/

noncomputable section
namespace powerlib.Modal
open Matrix Filter
open scoped BigOperators Topology ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace ModalBasis

variable {A : Matrix n n ℂ} (mb : ModalBasis A)

/-! ## Characteristic polynomial and multiplicity -/

/-- `det(sI − A) = Π_i (s − λ_i)`. -/
@[powerlib_foundation] theorem det_sub_eq_prod (s : ℂ) :
    (s • (1 : Matrix n n ℂ) - A).det = ∏ i, (s - mb.eig i) := by
  rw [mb.sub_eq_conj, det_mul, det_mul, det_diagonal]
  have h : mb.V.det * mb.Wᵀ.det = 1 := by rw [← det_mul, mb.V_mul_Wt, det_one]
  calc mb.V.det * (∏ i, (s - mb.eig i)) * mb.Wᵀ.det
      = (∏ i, (s - mb.eig i)) * (mb.V.det * mb.Wᵀ.det) := by ring
    _ = ∏ i, (s - mb.eig i) := by rw [h, mul_one]

/-- The characteristic polynomial is `Π_i (X − λ_i)`. -/
@[powerlib_foundation] theorem charpoly_eq_prod :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (mb.eig i)) := by
  apply Polynomial.funext
  intro s
  rw [Matrix.eval_charpoly, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [← mb.det_sub_eq_prod s, Matrix.scalar_apply, smul_one_eq_diagonal]

/-- The algebraic multiplicity of `μ` is the number of modal indices with `λ_i = μ`. -/
@[powerlib_foundation] theorem rootMultiplicity_eq_card (μ : ℂ) :
    A.charpoly.rootMultiplicity μ = (Finset.univ.filter fun i => mb.eig i = μ).card := by
  classical
  rw [← Polynomial.count_roots, mb.charpoly_eq_prod]
  have hprod : (∏ i, (Polynomial.X - Polynomial.C (mb.eig i))) =
      ((Finset.univ.val.map mb.eig).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C, Multiset.count_map, Finset.card_def,
    Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

/-! ## Spectral projectors and subspace participation (§1.8) -/

/-- Spectral projector `E_μ = Σ_{λ_i = μ} v_i ψ_iᵀ`. -/
def spectralProj (μ : ℂ) : Matrix n n ℂ :=
  mb.V * diagonal (fun i => if mb.eig i = μ then 1 else 0) * mb.Wᵀ

/-- Subspace participation `P_{k,μ} = Σ_{λ_i = μ} p_{ki}`. -/
def subspacePF (k : n) (μ : ℂ) : ℂ := ∑ i ∈ Finset.univ.filter (fun i => mb.eig i = μ), mb.pf k i

@[powerlib_foundation] theorem spectralProj_apply (μ : ℂ) (k l : n) :
    mb.spectralProj μ k l = ∑ i, (if mb.eig i = μ then mb.V k i * mb.W l i else 0) := by
  rw [spectralProj, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

@[powerlib_foundation] theorem subspacePF_eq_spectralProj (k : n) (μ : ℂ) :
    mb.subspacePF k μ = mb.spectralProj μ k k := by
  rw [spectralProj_apply, subspacePF, Finset.sum_filter]; rfl

/-- `ψ_iᵀ x = 0` whenever `x` is a right eigenvector for an eigenvalue different from `λ_i`. -/
@[powerlib_foundation] theorem ψ_dot_eigvec {ν : ℂ} {x : n → ℂ} (hx : A *ᵥ x = ν • x) {i : n}
    (hi : mb.eig i ≠ ν) : mb.ψ i ⬝ᵥ x = 0 := by
  have h1 : mb.ψ i ⬝ᵥ (A *ᵥ x) = ν * (mb.ψ i ⬝ᵥ x) := by rw [hx, dotProduct_smul, smul_eq_mul]
  have h2 : mb.ψ i ⬝ᵥ (A *ᵥ x) = mb.eig i * (mb.ψ i ⬝ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, mb.vecMul_ψ, smul_dotProduct, smul_eq_mul]
  have h3 : (mb.eig i - ν) * (mb.ψ i ⬝ᵥ x) = 0 := by linear_combination h1 - h2
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hi)

@[powerlib_foundation] theorem spectralProj_mulVec_apply (μ : ℂ) (x : n → ℂ) :
    mb.spectralProj μ *ᵥ x = ∑ i, (if mb.eig i = μ then mb.ψ i ⬝ᵥ x else 0) • mb.v i := by
  ext k
  simp only [Matrix.mulVec, dotProduct, spectralProj_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, v, ψ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring
  · simp

/-- Modal expansion of a vector: `x = Σ_i (ψ_iᵀ x) v_i`. -/
@[powerlib_foundation] theorem eq_sum_modal (x : n → ℂ) : x = ∑ i, (mb.ψ i ⬝ᵥ x) • mb.v i := by
  conv_lhs => rw [show x = mb.V *ᵥ (mb.Wᵀ *ᵥ x) by
    rw [Matrix.mulVec_mulVec, mb.V_mul_Wt, Matrix.one_mulVec]]
  ext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, ψ,
    transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `E_μ` acts as the identity on `μ`-eigenvectors and as zero on other eigenvectors. -/
@[powerlib_foundation] theorem spectralProj_mulVec_eigvec (μ : ℂ) {ν : ℂ} {x : n → ℂ}
    (hx : A *ᵥ x = ν • x) : mb.spectralProj μ *ᵥ x = if ν = μ then x else 0 := by
  rw [spectralProj_mulVec_apply]
  have hexp := mb.eq_sum_modal x
  split_ifs with hν
  · subst hν
    conv_rhs => rw [hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rfl
    · rw [mb.ψ_dot_eigvec hx hi, zero_smul]
  · refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · rw [mb.ψ_dot_eigvec hx (by rw [hi]; exact Ne.symm hν), zero_smul]
    · exact zero_smul _ _

/-- The spectral projector does not depend on the modal basis. -/
@[powerlib_foundation] theorem spectralProj_eq (mb' : ModalBasis A) (μ : ℂ) :
    mb.spectralProj μ = mb'.spectralProj μ := by
  have hcols : mb.spectralProj μ * mb'.V = mb'.spectralProj μ * mb'.V := by
    ext k j
    have h1 := congrFun (mb.spectralProj_mulVec_eigvec μ (mb'.mulVec_v j)) k
    have h2 := congrFun (mb'.spectralProj_mulVec_eigvec μ (mb'.mulVec_v j)) k
    change (mb.spectralProj μ *ᵥ mb'.v j) k = (mb'.spectralProj μ *ᵥ mb'.v j) k
    rw [h1, h2]
  calc mb.spectralProj μ = mb.spectralProj μ * mb'.V * mb'.Wᵀ := by
        rw [Matrix.mul_assoc, mb'.V_mul_Wt, Matrix.mul_one]
    _ = mb'.spectralProj μ * mb'.V * mb'.Wᵀ := by rw [hcols]
    _ = mb'.spectralProj μ := by rw [Matrix.mul_assoc, mb'.V_mul_Wt, Matrix.mul_one]

/-- Subspace participation is basis independent. -/
@[powerlib_foundation] theorem subspacePF_eq (mb' : ModalBasis A) (k : n) (μ : ℂ) :
    mb.subspacePF k μ = mb'.subspacePF k μ := by
  rw [subspacePF_eq_spectralProj, subspacePF_eq_spectralProj, spectralProj_eq mb mb']

/-- `Σ_k P_{k,μ}` is the algebraic multiplicity of `μ` (trace of the spectral projector). -/
@[powerlib_foundation] theorem sum_subspacePF (μ : ℂ) :
    ∑ k, mb.subspacePF k μ = (A.charpoly.rootMultiplicity μ : ℂ) := by
  rw [mb.rootMultiplicity_eq_card]
  simp only [subspacePF]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_congr rfl fun i _ => mb.sum_pf_states i

end ModalBasis

/-! ## Residues at simple eigenvalues (§1.1, §1.5) -/

@[powerlib_foundation] theorem eventually_ne_all (lam : n → ℂ) {i : n}
    (hsimple : ∀ j, j ≠ i → lam j ≠ lam i) : ∀ᶠ s in 𝓝[≠] lam i, ∀ j, s ≠ lam j := by
  rw [Filter.eventually_all]
  intro j
  by_cases hj : j = i
  · subst hj; exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds (hsimple j hj).symm)

/-- Partial-fraction residue: `(s − λ_i) Σ_j a_j / (s − λ_j) → a_i` at a simple `λ_i`. -/
@[powerlib_foundation] theorem tendsto_partial_fraction (lam a : n → ℂ) {i : n}
    (hsimple : ∀ j, j ≠ i → lam j ≠ lam i) :
    Tendsto (fun s => (s - lam i) * ∑ j, a j / (s - lam j)) (𝓝[≠] lam i) (𝓝 (a i)) := by
  let g : ℂ → ℂ := fun s => ∑ j, (if j = i then a j else a j * (s - lam i) / (s - lam j))
  have hg : Tendsto g (𝓝 (lam i)) (𝓝 (∑ j, if j = i then a j else 0)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    by_cases hj : j = i
    · simp only [hj, ite_true]; exact tendsto_const_nhds
    · simp only [hj, ite_false]
      have hc : ContinuousAt (fun s : ℂ => a j * (s - lam i) / (s - lam j)) (lam i) :=
        (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div
          (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 (hsimple j hj).symm)
      simpa using hc.tendsto
  rw [Finset.sum_ite_eq' Finset.univ i a, if_pos (Finset.mem_univ _)] at hg
  refine (hg.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_ne_all lam hsimple] with s hs
  simp only [g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj; rw [if_pos rfl]; field_simp [sub_ne_zero.2 (hs j)]
  · rw [if_neg hj]; ring

namespace ModalBasis

variable {A : Matrix n n ℂ} (mb : ModalBasis A)

/-- `(s − λ_i) [(sI − A)⁻¹]_{kl} → v_{ki} ψ_{li}` at a simple eigenvalue. -/
@[powerlib_foundation] theorem tendsto_resolvent_residue {i : n}
    (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) (k l : n) :
    Tendsto (fun s => (s - mb.eig i) * (s • (1 : Matrix n n ℂ) - A)⁻¹ k l) (𝓝[≠] mb.eig i)
      (𝓝 (mb.V k i * mb.W l i)) := by
  refine (tendsto_partial_fraction mb.eig (fun j => mb.V k j * mb.W l j) hsimple).congr' ?_
  filter_upwards [eventually_ne_all mb.eig hsimple] with s hs
  rw [mb.resolvent_apply hs]

/-- The participation factor is the residue of the `(k,k)` resolvent channel. -/
@[powerlib_foundation] theorem tendsto_pf_residue {i : n}
    (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) (k : n) :
    Tendsto (fun s => (s - mb.eig i) * (s • (1 : Matrix n n ℂ) - A)⁻¹ k k) (𝓝[≠] mb.eig i)
      (𝓝 (mb.pf k i)) :=
  mb.tendsto_resolvent_residue hsimple k k

/-- `(s − λ_i) C (sI − A)⁻¹ B → R^{(i)}` at a simple eigenvalue. -/
@[powerlib_foundation] theorem tendsto_io_residue {κ κ' : Type*} (C : Matrix κ n ℂ)
    (B : Matrix n κ' ℂ) {i : n} (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) :
    Tendsto (fun s => (s - mb.eig i) • (C * (s • (1 : Matrix n n ℂ) - A)⁻¹ * B))
      (𝓝[≠] mb.eig i) (𝓝 (mb.residue C B i)) := by
  refine tendsto_pi_nhds.2 fun l => tendsto_pi_nhds.2 fun j => ?_
  refine (tendsto_partial_fraction mb.eig (fun r => mb.residue C B r l j) hsimple).congr' ?_
  filter_upwards [eventually_ne_all mb.eig hsimple] with s hs
  rw [mb.io_expansion C B hs]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

@[powerlib_foundation] theorem residue_eq_zero_iff' {κ κ' : Type*} (C : Matrix κ n ℂ)
    (B : Matrix n κ' ℂ) (i : n) :
    mb.residue C B i = 0 ↔ C *ᵥ mb.v i = 0 ∨ vecMul (mb.ψ i) B = 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hne.1
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne.2
    have := congrFun (congrFun h l) j
    simp only [residue, Matrix.zero_apply] at this
    exact mul_ne_zero hl hj this
  · rintro (h | h) <;> ext l j <;> simp [residue, h]

end ModalBasis

/-! ## Modal free response (`T-small-signal-stability.md` §1.5) -/

@[powerlib_foundation] theorem scalar_linear_ode {w : ℝ → ℂ} {c : ℂ}
    (h : ∀ t, HasDerivAt w (c * w t) t) (t : ℝ) : w t = Complex.exp (c * t) * w 0 := by
  let g : ℝ → ℂ := fun t => Complex.exp (-(c * t)) * w t
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)))
        (Complex.exp (-(c * t)) * -(c * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul c).neg.cexp
    convert he.mul (h t) using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
    (fun t => (hg t).deriv) t 0
  simp only [g, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hconst
  rw [← hconst, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- Modal decomposition of every free response of a real LTI model with diagonalisable
state matrix: `x(t) = Σ_i e^{λ_i t} (ψ_iᵀ x(0)) v_i` (complexified). -/
@[powerlib_foundation] theorem modal_free_response {N : ℕ} {m : LTI.AutonomousModel N}
    (mb : ModalBasis (LTI.complexify m.A)) {x : ℝ → Fin N → ℝ} (hx : LTI.IsTrajectory m x)
    (t : ℝ) :
    (fun k => (x t k : ℂ)) =
      ∑ i, (Complex.exp (mb.eig i * t) * (mb.ψ i ⬝ᵥ fun k => (x 0 k : ℂ))) • mb.v i := by
  let z : ℝ → Fin N → ℂ := fun t k => (x t k : ℂ)
  have hz : ∀ t, HasDerivAt z (LTI.complexify m.A *ᵥ z t) t := by
    intro t
    refine hasDerivAt_pi.2 fun k => ?_
    have h := (hasDerivAt_pi.1 (hx t) k).ofReal_comp
    convert h using 1
    simp [z, LTI.AutonomousModel.field, Matrix.mulVec, dotProduct]
  have hw : ∀ i t, HasDerivAt (fun t => mb.ψ i ⬝ᵥ z t) (mb.eig i * (mb.ψ i ⬝ᵥ z t)) t := by
    intro i t
    have h : HasDerivAt (fun t => mb.ψ i ⬝ᵥ z t)
        (∑ k, mb.ψ i k * (LTI.complexify m.A *ᵥ z t) k) t :=
      HasDerivAt.fun_sum fun k _ => (hasDerivAt_pi.1 (hz t) k).const_mul (mb.ψ i k)
    refine h.congr_deriv ?_
    change mb.ψ i ⬝ᵥ (LTI.complexify m.A *ᵥ z t) = mb.eig i * (mb.ψ i ⬝ᵥ z t)
    rw [Matrix.dotProduct_mulVec, mb.vecMul_ψ, smul_dotProduct, smul_eq_mul]
  have hexp : ∀ i, mb.ψ i ⬝ᵥ z t = Complex.exp (mb.eig i * t) * (mb.ψ i ⬝ᵥ z 0) :=
    fun i => scalar_linear_ode (w := fun t => mb.ψ i ⬝ᵥ z t) (hw i) t
  change z t = _
  rw [mb.eq_sum_modal (z t)]
  exact Finset.sum_congr rfl fun i _ => by rw [hexp i]

/-- With `x(0) = e_k`, the `k`-th state is `x_k(t) = Σ_i p_{ki} e^{λ_i t}`. -/
@[powerlib_foundation] theorem pf_free_response {N : ℕ} {m : LTI.AutonomousModel N}
    (mb : ModalBasis (LTI.complexify m.A)) {x : ℝ → Fin N → ℝ} (hx : LTI.IsTrajectory m x)
    {k : Fin N} (h0 : x 0 = Pi.single k 1) (t : ℝ) :
    (x t k : ℂ) = ∑ i, mb.pf k i * Complex.exp (mb.eig i * t) := by
  have h := congrFun (modal_free_response mb hx t) k
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : (mb.ψ i ⬝ᵥ fun j => (x 0 j : ℂ)) = mb.W k i := by
    rw [h0]
    simp only [dotProduct, ModalBasis.ψ]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [Pi.smul_apply, smul_eq_mul, hd]
  simp only [ModalBasis.pf, ModalBasis.v]
  ring

/-- Conjugate-pair contribution `p e^{λt} + p̄ e^{λ̄t} = 2|p| e^{σt} cos(ωt + arg p)` (§1.3). -/
@[powerlib_foundation] theorem conj_pair_contribution (p lam : ℂ) (t : ℝ) :
    p * Complex.exp (lam * t) + conj p * Complex.exp (conj lam * t) =
      ((2 * ‖p‖ * Real.exp (lam.re * t) * Real.cos (lam.im * t + Complex.arg p) : ℝ) : ℂ) := by
  have hconj : conj p * Complex.exp (conj lam * t) = conj (p * Complex.exp (lam * t)) := by
    rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have hpolar : p * Complex.exp (lam * t) =
      (‖p‖ : ℂ) * Complex.exp (Complex.arg p * Complex.I + lam * t) := by
    rw [Complex.exp_add, ← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
  rw [hconj, Complex.add_conj, hpolar, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  push_cast
  ring_nf

/-! ## Transfer-function poles versus eigenvalues (§1.9) -/

section Poles

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- Away from the spectrum the transfer matrix is continuous (no pole). -/
@[powerlib_foundation] theorem transfer_continuousAt (m : LTI.Model n κ) {μ : ℂ}
    (hμ : (LTI.characteristicMatrix m.A μ).det ≠ 0) : ContinuousAt (LTI.transfer m) μ := by
  have hchar : Continuous (fun s : ℂ => LTI.characteristicMatrix m.A s) := by
    unfold LTI.characteristicMatrix
    exact (continuous_id.smul continuous_const).sub continuous_const
  have hfun : LTI.transfer m = fun s => ((LTI.characteristicMatrix m.A s).det)⁻¹ •
      (LTI.complexify m.C * (LTI.characteristicMatrix m.A s).adjugate * LTI.complexify m.B) +
        LTI.complexify m.D := funext fun s => LTI.transfer_eq_adjugate m s
  rw [hfun]
  refine ContinuousAt.add ?_ continuousAt_const
  exact ((hchar.matrix_det.continuousAt).inv₀ hμ).smul
    ((continuous_const.matrix_mul hchar.matrix_adjugate).matrix_mul continuous_const).continuousAt

/-- Poles of the transfer matrix are exactly the eigenvalues, for a real LTI model with
diagonalisable state matrix, simple eigenvalues and modal (PBH) controllability and
observability (`ψ_iᵀ B ≠ 0`, `C v_i ≠ 0`): `(s − μ) G(s)` has a nonzero limit at `μ` iff `μ`
is an eigenvalue. -/
@[powerlib_foundation] theorem transfer_pole_iff (m : LTI.Model n κ)
    (mb : ModalBasis (LTI.complexify m.A)) (hsimple : ∀ i j, i ≠ j → mb.eig i ≠ mb.eig j)
    (hobs : ∀ i, LTI.complexify m.C *ᵥ mb.v i ≠ 0)
    (hctrl : ∀ i, vecMul (mb.ψ i) (LTI.complexify m.B) ≠ 0) (μ : ℂ) :
    (∃ R : Matrix κ κ ℂ, R ≠ 0 ∧
        Tendsto (fun s => (s - μ) • LTI.transfer m s) (𝓝[≠] μ) (𝓝 R)) ↔
      ∃ i, mb.eig i = μ := by
  constructor
  · rintro ⟨R, hR, hlim⟩
    by_contra hno
    push Not at hno
    have hdet : (LTI.characteristicMatrix m.A μ).det ≠ 0 := by
      rw [show LTI.characteristicMatrix m.A μ =
          μ • (1 : Matrix n n ℂ) - LTI.complexify m.A from rfl, mb.det_sub_eq_prod]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.2 (hno i).symm
    have hc : Tendsto (fun s => (s - μ) • LTI.transfer m s) (𝓝 μ) (𝓝 ((μ - μ) • LTI.transfer m μ)) :=
      ((continuousAt_id.sub continuousAt_const).smul (transfer_continuousAt m hdet)).tendsto
    rw [sub_self, zero_smul] at hc
    exact hR (tendsto_nhds_unique hlim (hc.mono_left nhdsWithin_le_nhds))
  · rintro ⟨i, rfl⟩
    have hs : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i := fun j hj => hsimple j i hj
    refine ⟨mb.residue (LTI.complexify m.C) (LTI.complexify m.B) i, ?_, ?_⟩
    · rw [Ne, mb.residue_eq_zero_iff']
      push Not
      exact ⟨hobs i, hctrl i⟩
    · have h1 := mb.tendsto_io_residue (LTI.complexify m.C) (LTI.complexify m.B) hs
      have h2 : Tendsto (fun s => (s - mb.eig i) • LTI.complexify m.D) (𝓝[≠] mb.eig i)
          (𝓝 ((mb.eig i - mb.eig i) • LTI.complexify m.D)) :=
        (((continuousAt_id.sub continuousAt_const).smul continuousAt_const).tendsto).mono_left
          nhdsWithin_le_nhds
      rw [sub_self, zero_smul] at h2
      have h3 := h1.add h2
      rw [add_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_ne_all mb.eig hs] with s hs'
      rw [LTI.transfer, smul_add]
      rfl

end Poles

end powerlib.Modal
