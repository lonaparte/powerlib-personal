import theorem.Modal.Spectral

/-! # Real form of the modal response of a real state matrix

For a real state matrix (complexified), eigenvectors and eigenvalues come in conjugate pairs, the
spectral projector of `λ̄` is the entrywise conjugate of that of `λ`, the modal residues of a
conjugate pair are conjugate, and every state of the free response is a finite sum of damped
cosines `|p_{ki}| e^{σ_i t} cos(ω_i t + arg p_{ki})`; a conjugate pair of simple modes contributes
exactly `2|p| e^{σt} cos(ω_d t + arg p)`.

Scope.
* A real square matrix `A` acting on `ℂⁿ` through `Linear.complexify A`, on an arbitrary finite
  index (the free-response statements use `Fin N` and `EuclideanSpace ℝ (Fin N)`, as
  `modal_free_response`). Modal statements assume a `ModalBasis (Linear.complexify A)`
  (diagonalisable state matrix; defective matrices are excluded). Pairing statements assume
  that the two eigenvalues of the pair are simple (algebraic multiplicity one).
* No hypothesis pairs the given modal basis: the conjugate relations between the vectors of a
  pair are derived from the basis independence of spectral projectors
  (`ModalBasis.spectralProj_eq`), not assumed.
* Matrix-level statements with no model family.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.1.1, eqs. (2-7)–(2-11)
(conjugate modal equations `ż_r = λ_r z_r`, `ż_r* = λ_r* z_r*`, their solutions with
`Ψ_r^T x₀`, `Ψ_r^{*T} x₀`, and the real form `x_i(t) = 2 Σ_r |φ_ir||z_r0| e^{−α_r t}
cos(ω_dr t + γ_ir + θ_r)`). The report writes the conjugate eigenvectors `Φ_r*`, `Ψ_r*` as part of
its modal matrix; here they are derived (`ModalBasis.conjBasis`, `vecMulVec_conj_pair`). The report's
(2-11) sums over conjugate pairs only ("ignoring the non-oscillatory modes"); `free_response_real`
is the exact real form over all modes, real ones included, and `free_response_pair` is the pair
term of (2-11) with `p = φ_ir z_r0`.

Results.
* `mulVec_conj_of_eigvec`, `vecMul_conj_of_left_eigvec` — `A v = λ v ⇒ A v̄ = λ̄ v̄` and
  `wᵀA = λwᵀ ⇒ w̄ᵀA = λ̄w̄ᵀ` for real `A` (eq. (2-7)).
* `complexify_map_conj` — a complexified real matrix is its own conjugate;
  `ModalBasis.conjBasis` — the entrywise conjugate of a modal basis of a real matrix is a modal basis
  with eigenvalues `λ̄_i`; `spectralProj_conj` — `E_{μ̄} = conj E_μ` (entrywise);
  `spectralProj_of_simple` — for a simple `λ_r`, `E_{λ_r} = v_r ψ_rᵀ` (basis independent);
  `residue_eq_spectralProj` — the modal residue of a simple eigenvalue is `C E_{λ_r} B`.
* `vecMulVec_conj_pair` — for simple `λ_r`, `λ_{r'} = λ̄_r`: `v_{r'} ψ_{r'}ᵀ = conj(v_r ψ_rᵀ)`;
  `residue_conj_pair` — the modal residues of real `(C, B)` satisfy `R^{(r')} = conj R^{(r)}`
  (the report's `A_r`, `B_r` of (2-19) are real); `modalWeight_conj_pair` — the same for the
  weight `p_{kr} = v_{kr} (ψ_rᵀ x₀)` of a real initial state.
* `re_mul_exp` — `Re(p e^{λt}) = |p| e^{Re λ t} cos(Im λ t + arg p)`.
* `free_response_real` — every global solution of `ẋ = A x` satisfies
  `x_k(t) = Σ_i |p_{ki}| e^{Re λ_i t} cos(Im λ_i t + arg p_{ki})`, `p_{ki} = v_{ki}(ψ_iᵀ x(0))`.
* `free_response_pair` — for a simple conjugate pair `r ≠ r'`, the two terms of the modal free
  response sum to `2|p_{kr}| e^{σ_r t} cos(ω_dr t + arg p_{kr})` (eq. (2-11)).
-/

noncomputable section
namespace powerlib.Modal
open Matrix
open scoped BigOperators ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Conjugate eigenvectors (2-7) -/

omit [DecidableEq n] in
/-- For real `A`, `A v = λ v` implies `A v̄ = λ̄ v̄`. -/
@[tmio T, powerlib_foundation] theorem mulVec_conj_of_eigvec {A : Matrix n n ℝ} {lam : ℂ} {v : n → ℂ}
    (h : Linear.complexify A *ᵥ v = lam • v) :
    Linear.complexify A *ᵥ (fun k => conj (v k)) = conj lam • fun k => conj (v k) := by
  ext k
  have hk := congrArg conj (congrFun h k)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Matrix.map_apply, Complex.coe_algebraMap, Complex.conj_ofReal] at hk ⊢
  exact hk

omit [DecidableEq n] in
/-- For real `A`, `wᵀA = λ wᵀ` implies `w̄ᵀA = λ̄ w̄ᵀ`. -/
@[tmio T, powerlib_foundation] theorem vecMul_conj_of_left_eigvec {A : Matrix n n ℝ} {lam : ℂ}
    {w : n → ℂ} (h : vecMul w (Linear.complexify A) = lam • w) :
    vecMul (fun k => conj (w k)) (Linear.complexify A) = conj lam • fun k => conj (w k) := by
  ext k
  have hk := congrArg conj (congrFun h k)
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Matrix.map_apply, Complex.coe_algebraMap, Complex.conj_ofReal] at hk ⊢
  exact hk

/-! ## The conjugate modal basis and spectral projectors -/

omit [Fintype n] [DecidableEq n] in
@[tmio T, powerlib_foundation] theorem complexify_map_conj (A : Matrix n n ℝ) :
    (Linear.complexify A).map (starRingEnd ℂ) = Linear.complexify A := by
  ext i j
  simp

namespace ModalBasis

/-- The entrywise conjugate of a modal basis of a real matrix: right and left eigenvectors
`v̄_i`, `ψ̄_i` with eigenvalues `λ̄_i`. -/
def conjBasis {A : Matrix n n ℝ} (mb : ModalBasis (Linear.complexify A)) :
    ModalBasis (Linear.complexify A) where
  V := mb.V.map (starRingEnd ℂ)
  W := mb.W.map (starRingEnd ℂ)
  eig := fun i => starRingEnd ℂ (mb.eig i)
  right := by
    have h := congrArg (fun M => M.map (starRingEnd ℂ)) mb.right
    simp only [Matrix.map_mul, complexify_map_conj] at h
    rw [h, Matrix.diagonal_map (map_zero _)]
  biorth := by
    have h := congrArg (fun M => M.map (starRingEnd ℂ)) mb.biorth
    simp only [Matrix.map_mul] at h
    rw [Matrix.transpose_map, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h

variable {A : Matrix n n ℝ} (mb : ModalBasis (Linear.complexify A))

/-- `E_{μ̄} = conj E_μ` (entrywise) for a real matrix. -/
@[tmio T, powerlib_foundation] theorem spectralProj_conj (μ : ℂ) :
    mb.spectralProj (starRingEnd ℂ μ) = (mb.spectralProj μ).map (starRingEnd ℂ) := by
  rw [mb.spectralProj_eq mb.conjBasis]
  simp only [spectralProj, Matrix.map_mul, Matrix.transpose_map]
  congr 2
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  simp only [ModalBasis.conjBasis, (RingHom.injective (starRingEnd ℂ)).eq_iff]
  split_ifs <;> simp

end ModalBasis

namespace ModalBasis

variable {A : Matrix n n ℂ} (mb : ModalBasis A)

/-- For a simple eigenvalue `λ_r`, `E_{λ_r} = v_r ψ_rᵀ`. -/
@[tmio T, powerlib_foundation] theorem spectralProj_of_simple {r : n}
    (hsimple : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) :
    mb.spectralProj (mb.eig r) = vecMulVec (mb.v r) (mb.ψ r) := by
  ext k l
  rw [mb.spectralProj_apply, Finset.sum_eq_single r (fun j _ hj => by simp [hsimple j hj])
    (by simp)]
  simp [vecMulVec_apply, ModalBasis.v, ModalBasis.ψ]

/-- For a simple eigenvalue, the modal residue is `C E_{λ_r} B`. -/
@[tmio T, powerlib_foundation] theorem residue_eq_spectralProj {κ κ' : Type*} [Fintype κ']
    (C : Matrix κ n ℂ) (B : Matrix n κ' ℂ) {r : n} (hsimple : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) :
    mb.residue C B r = C * mb.spectralProj (mb.eig r) * B := by
  rw [mb.spectralProj_of_simple hsimple]
  ext l j
  simp only [residue, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    vecMulVec_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  ring

end ModalBasis

/-! ## Conjugate pairs -/

namespace ModalBasis

variable {A : Matrix n n ℝ} (mb : ModalBasis (Linear.complexify A))

/-- For simple `λ_r` and `λ_{r'} = λ̄_r` (also simple): `v_{r'} ψ_{r'}ᵀ = conj(v_r ψ_rᵀ)`, whatever
modal basis is chosen. -/
@[tmio T, powerlib_foundation] theorem vecMulVec_conj_pair {r r' : n}
    (hr : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) (hr' : ∀ j, j ≠ r' → mb.eig j ≠ mb.eig r')
    (hpair : mb.eig r' = starRingEnd ℂ (mb.eig r)) :
    vecMulVec (mb.v r') (mb.ψ r') = (vecMulVec (mb.v r) (mb.ψ r)).map (starRingEnd ℂ) := by
  rw [← mb.spectralProj_of_simple hr', ← mb.spectralProj_of_simple hr, hpair,
    mb.spectralProj_conj]

/-- Modal residues of a real channel `(C, B)` for a simple conjugate pair are conjugate:
`R^{(r')} = conj R^{(r)}` (so `R + R̄` and `R λ̄ + R̄ λ` are real, as the report's `A_r`, `B_r`). -/
@[tmio T, powerlib_foundation] theorem residue_conj_pair {κ κ' : Type*} [Fintype κ']
    (C : Matrix κ n ℝ) (B : Matrix n κ' ℝ) {r r' : n}
    (hr : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) (hr' : ∀ j, j ≠ r' → mb.eig j ≠ mb.eig r')
    (hpair : mb.eig r' = starRingEnd ℂ (mb.eig r)) :
    mb.residue (Linear.complexify C) (Linear.complexify B) r' =
      (mb.residue (Linear.complexify C) (Linear.complexify B) r).map (starRingEnd ℂ) := by
  rw [mb.residue_eq_spectralProj _ _ hr', mb.residue_eq_spectralProj _ _ hr, hpair,
    mb.spectralProj_conj, Matrix.map_mul, Matrix.map_mul]
  congr 2 <;> ext <;> simp

/-- The modal weight `p_{kr} = v_{kr}(ψ_rᵀ x₀)` of a real vector `x₀` is conjugate across a
simple conjugate pair. -/
@[tmio T, powerlib_foundation] theorem modalWeight_conj_pair (x₀ : n → ℝ) {r r' : n}
    (hr : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) (hr' : ∀ j, j ≠ r' → mb.eig j ≠ mb.eig r')
    (hpair : mb.eig r' = starRingEnd ℂ (mb.eig r)) (k : n) :
    mb.v r' k * (mb.ψ r' ⬝ᵥ fun l => (x₀ l : ℂ)) =
      starRingEnd ℂ (mb.v r k * (mb.ψ r ⬝ᵥ fun l => (x₀ l : ℂ))) := by
  have h := mb.vecMulVec_conj_pair hr hr' hpair
  simp only [dotProduct, Finset.mul_sum, map_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl := congrFun (congrFun h k) l
  simp only [vecMulVec_apply, Matrix.map_apply, map_mul] at hl
  rw [← mul_assoc, hl, ← mul_assoc]

end ModalBasis

/-! ## Real form of the free response (2-11) -/

/-- `Re(p e^{λt}) = |p| e^{Re λ t} cos(Im λ t + arg p)`. -/
@[tmio T, powerlib_foundation] theorem re_mul_exp (p lam : ℂ) (t : ℝ) :
    (p * Complex.exp (lam * t)).re =
      ‖p‖ * Real.exp (lam.re * t) * Real.cos (lam.im * t + Complex.arg p) := by
  have hpolar : p * Complex.exp (lam * t) =
      (‖p‖ : ℂ) * Complex.exp (Complex.arg p * Complex.I + lam * t) := by
    rw [Complex.exp_add, ← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
  rw [hpolar, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf

/-- Exact real form of the modal free response, all modes included: every global solution of
`ẋ = A x` satisfies `x_k(t) = Σ_i |p_{ki}| e^{Re λ_i t} cos(Im λ_i t + arg p_{ki})` with
`p_{ki} = v_{ki}(ψ_iᵀ x(0))`. -/
@[tmio T, powerlib_foundation] theorem free_response_real {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (mb : ModalBasis (Linear.complexify A)) {x : ℝ → EuclideanSpace ℝ (Fin N)}
    (hx : ∀ t, HasDerivAt x (Linear.op A (x t)) t) (t : ℝ) (k : Fin N) :
    x t k = ∑ i, ‖mb.v i k * (mb.ψ i ⬝ᵥ fun l => (x 0 l : ℂ))‖ * Real.exp ((mb.eig i).re * t) *
      Real.cos ((mb.eig i).im * t + Complex.arg (mb.v i k * (mb.ψ i ⬝ᵥ fun l => (x 0 l : ℂ)))) := by
  have h := congrFun (modal_free_response mb hx t) k
  have h2 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h2
  rw [h2, Finset.sum_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, ← re_mul_exp]
  congr 1
  ring

/-- Eq. (2-11), one pair: for a simple conjugate pair `r ≠ r'` (`λ_{r'} = λ̄_r`) the two modal
terms of the free response of state `k` sum to `2|p_{kr}| e^{σ_r t} cos(ω_dr t + arg p_{kr})`. -/
@[tmio T, powerlib_foundation] theorem free_response_pair {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (mb : ModalBasis (Linear.complexify A)) (x₀ : Fin N → ℝ) {r r' : Fin N}
    (hr : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) (hr' : ∀ j, j ≠ r' → mb.eig j ≠ mb.eig r')
    (hpair : mb.eig r' = starRingEnd ℂ (mb.eig r)) (k : Fin N) (t : ℝ) :
    Complex.exp (mb.eig r * t) * (mb.ψ r ⬝ᵥ fun l => (x₀ l : ℂ)) * mb.v r k +
        Complex.exp (mb.eig r' * t) * (mb.ψ r' ⬝ᵥ fun l => (x₀ l : ℂ)) * mb.v r' k =
      ((2 * ‖mb.v r k * (mb.ψ r ⬝ᵥ fun l => (x₀ l : ℂ))‖ * Real.exp ((mb.eig r).re * t) *
        Real.cos ((mb.eig r).im * t + Complex.arg (mb.v r k * (mb.ψ r ⬝ᵥ fun l => (x₀ l : ℂ))))
          : ℝ) : ℂ) := by
  rw [← conj_pair_contribution, ← mb.modalWeight_conj_pair x₀ hr hr' hpair k, hpair]
  ring

end powerlib.Modal
