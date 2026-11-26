import theorem.Modal.RealForm
import theorem.Modal.EigenFrequency
import theorem.LTI.SecondOrderResonance
import theorem.ParametricResonance.ForcedResponse

/-! # Modal phasor of the forced steady state, resonance, mode shape and disturbance location

The sinusoidal steady state of a linear system with diagonalisable state matrix, expanded over
its modes; the exact contribution of a conjugate pair and its normalized amplitude and phase;
the exact resonant pair term with an explicit error bound for the report's poorly-damped
approximation; the dominance of a lightly damped mode with an explicit bound on the other modes;
and the consequences for the mode shape and for the disturbance location.

Scope.
* Real LTI system `ẋ = A x + Re(b e^{jωt})` on `ℝᴺ = EuclideanSpace ℝ (Fin N)` with constant
  real `A`, complex drive phasor `b`, real frequency `ω`, continuous time (the plant and the
  steady state `forcedOrbit`, `forcedAmplitude` of `theorem/ParametricResonance/ForcedResponse.lean`).
  The report's sine convention `ΔP_T = Im(ΔP̃_Tm e^{jωt})`, `x = Im(B̃ e^{jωt})` is the case
  `b = −j P` (`forcing_neg_I_smul`, `forcedOrbit_neg_I_smul`).
* Modal statements assume a `ModalBasis (Linear.complexify A)` (diagonalisable state matrix;
  defective matrices are excluded) and that `jω` is not an eigenvalue. Pairing statements assume
  a simple conjugate pair of eigenvalues (no hypothesis on how the modal basis pairs them).
* Pair, normalization, phase and resonance statements are exact identities and inequalities
  about complex numbers `R` (a modal residue `v_{ir} ψ_rᵀ b`, e.g. `φ_ir ψ_lr p` for
  `b = p e_l`) and `λ` (the eigenvalue). The "≈" of the report (dropping the other modes, setting
  `φ_r = π/2`) are replaced by exact statements with explicit symbolic error bounds.
* The mode-shape limit concerns an arbitrary family of complex matrices with fixed modal vectors
  whose resonating eigenvalue approaches `jω_d` while the others stay a fixed distance away.
* No model family; foundation results.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.2.1, eqs. (2-15)–(2-23)
(phasor steady state, modal phasors (2-17), steady state (2-18), conjugate-pair form (2-19) with
`A_r = −(Φ_rΨ_rᵀλ_r* + Φ_r*Ψ_r*ᵀλ_r)`, `B_r = Φ_rΨ_rᵀ + Φ_r*Ψ_r*ᵀ` real, single-input form
(2-20)/(2-21), amplitude (2-22) and phase (2-23)); §2.2.2, eqs. (2-25)–(2-27) (resonance,
`λ̃_r = ω_nr e^{jφ_r}`, `φ_r ≈ π/2`, amplitude grows as `ζ_r → 0`); §2.2.3 (mode shape at
resonance is the right eigenvector); §2.2.4 (the disturbance location acts through `ψ_lr`).

Corrections and sharpenings.
* (2-25)–(2-27): the pair term at `ω = ω_n` is exactly `(ω_n b − ja)/(2ζω_n²)`
  (`pairTerm_at_naturalFreq`); with `λ = ω_n e^{j(π/2 + δ)}`, `ζ = sin δ`, it is exactly
  `[R(1 + e^{−jδ}) + R̄(1 − e^{jδ})]/(2ζω_n)` (`pairTerm_exp`), the report's (2-26). The report's
  `φ_r ≈ π/2` step is replaced by the bound `‖ζω_n·pair − R‖ ≤ ‖R‖ arcsin ζ ≤ (π/2)ζ‖R‖`
  (`resonance_error`), and the time-domain form (2-27) holds up to `(π/2)‖R‖/ω_n` uniformly in
  `t`, while the main term `‖R‖/(ζω_n)` is unbounded as `ζ → 0` (`resonance_time_error`).
* "The `r`-th mode dominates": stated exactly at `ω = ω_d = Im λ_r`, where `jω_d − λ_r = ζ_rω_nr`
  is real, as the bound `‖ζ_rω_nr χ − v_r(ψ_rᵀb)‖ ≤ |ζ_rω_nr| Σ_{i≠r} ‖ψ_iᵀb‖‖v_i‖/‖jω_d − λ_i‖`
  (`dominant_mode_bound`).
* (2-23) is stated without the arctan branch ambiguity: `|H||D|² cos φ` and `|H||D|² sin φ` are
  the report's numerator and denominator (`resonanceResp_phase`); the arctan form holds when the
  cosine part is positive (`resonanceResp_phase_arctan`).

Results.
* `ModalBasis.resolvent_mulVec`, `forcedAmplitude_modal` — `(jωI − A)⁻¹ b = Σ_i
  (ψ_iᵀb)/(jω − λ_i) v_i` (2-18); `ModalBasis.ψ_dot_resolvent_mulVec`, `ψ_dot_forcedAmplitude` —
  modal coordinate `ψ_rᵀχ = (ψ_rᵀb)/(jω − λ_r)` (2-17); `forcedOrbit_modal` — the steady state is
  `x_k(t) = Re(Σ_i (ψ_iᵀb)/(jω − λ_i) v_{ki} e^{jωt})`; `forcing_neg_I_smul`,
  `forcedOrbit_neg_I_smul` — the report's sine convention.
* `steadyState_modal` — for Hurwitz `A`: the modal steady state formula holds and every solution
  converges to it exponentially (why the report may restrict to the steady state);
  `I_mul_ne_eig_of_isHurwitz` — no eigenvalue of a Hurwitz matrix lies on the imaginary axis.
* `pairTerm`, `pairA`, `pairB`, `pairA_eq`, `pairB_eq` — `A_r = −(Rλ̄ + R̄λ)`, `B_r = R + R̄`
  are real; `pairTerm_eq` — `R/(jω − λ) + R̄/(jω − λ̄) = (A_r + jωB_r)/((ω_n² − ω²) + j2ζω_nω)`
  (2-19); `forcedAmplitude_pair` — for real input `P` and a simple conjugate pair `r, r'`, the
  two modal terms of state `k` form `pairTerm (v_{kr}(ψ_rᵀP)) λ_r ω`.
* `normalize_pair`, `pairTerm_eq_resonanceResp` — normalized form (2-20)/(2-21) with
  `ν = ω/ω_n` (`LTI.resonanceResp` of `theorem/LTI/SecondOrderResonance.lean`);
  `sq_norm_pairTerm` — amplitude (2-22); `resonanceResp_phase`, `resonanceResp_phase_arctan`,
  `im_mul_exp` — phase (2-23) and `Im(H p e^{jωt}) = |H| p sin(ωt − φ)`; `re_div_mul_normSq`,
  `im_div_mul_normSq` — `Re(z/w)|w|² = Re z Re w + Im z Im w`, `Im(z/w)|w|² = Im z Re w −
  Re z Im w`.
* `pairTerm_at_naturalFreq` (2-25), `pairTerm_exp` (2-26), `norm_pairTerm_exp_sub_le`,
  `resonance_error`, `im_polar_mul_exp` and `resonance_time_error` ((2-27) with explicit error),
  `tendsto_norm_pairTerm_resonant` (the resonant amplitude tends to `∞` as `ζ → 0⁺`).
* `ModalBasis.norm_resolvent_mulVec_sub_le`, `dominant_mode_bound` — dominant mode;
  `tendsto_mode_shape`, `tendsto_mode_shape_ratio` — §2.2.3: along a family whose resonating
  eigenvalue `−σ + jω_d` approaches the forcing frequency (`σ → 0`), `σ·χ → (ψ_rᵀb) v_r` for
  every input `b`, so the ratios `χ_k/χ_{k'}` (relative amplitude and phase) tend to
  `v_{kr}/v_{k'r}`, independently of `b`.
* `ψ_dot_single`, `leading_vector_location`, `W_eq_zero_iff`, `leading_entry_eq_zero_iff` —
  §2.2.4: for `b = p e_l` the leading vector is `ψ_{lr} p v_r`; two locations give parallel
  leading vectors in ratio `ψ_{lr}/ψ_{l'r}`; the leading coefficient vanishes iff every left
  eigenvector of `λ_r` vanishes at `l` (location `l` cannot excite the mode), or, for the
  observed state `k`, the PBH condition of `residue_eq_zero_iff`.
-/

noncomputable section
namespace powerlib.Modal
open Matrix Complex Filter Topology
open scoped BigOperators ComplexConjugate

/-! ## Modal expansion of the resolvent applied to a vector -/

namespace ModalBasis

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (mb : ModalBasis A)

/-- `(sI − A)⁻¹ b = Σ_i (ψ_iᵀ b)/(s − λ_i) v_i` away from the spectrum. -/
@[tmio T, powerlib_foundation] theorem resolvent_mulVec {s : ℂ} (hs : ∀ i, s ≠ mb.eig i)
    (b : n → ℂ) :
    (s • (1 : Matrix n n ℂ) - A)⁻¹ *ᵥ b = ∑ i, ((mb.ψ i ⬝ᵥ b) / (s - mb.eig i)) • mb.v i := by
  ext k
  simp only [Matrix.mulVec, dotProduct, mb.resolvent_apply hs, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ModalBasis.v, ModalBasis.ψ, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Modal coordinate of `(sI − A)⁻¹ b`: `ψ_rᵀ (sI − A)⁻¹ b = (ψ_rᵀ b)/(s − λ_r)`. -/
@[tmio T, powerlib_foundation] theorem ψ_dot_resolvent_mulVec {s : ℂ} (hs : ∀ i, s ≠ mb.eig i)
    (b : n → ℂ) (r : n) :
    mb.ψ r ⬝ᵥ ((s • (1 : Matrix n n ℂ) - A)⁻¹ *ᵥ b) = (mb.ψ r ⬝ᵥ b) / (s - mb.eig r) := by
  rw [mb.resolvent_mulVec hs, dotProduct_sum]
  simp only [dotProduct_smul, mb.ψ_dot_v, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

/-- Dominant-mode bound: the `r`-th modal term of `(sI − A)⁻¹ b`, scaled by `s − λ_r`, is
`(ψ_rᵀ b) v_r`; the remainder is bounded by `‖s − λ_r‖ Σ_{i≠r} ‖ψ_iᵀb‖ ‖v_i‖/‖s − λ_i‖`. -/
@[tmio T, powerlib_foundation] theorem norm_resolvent_mulVec_sub_le {s : ℂ}
    (hs : ∀ i, s ≠ mb.eig i) (b : n → ℂ) (r : n) :
    ‖(s - mb.eig r) • ((s • (1 : Matrix n n ℂ) - A)⁻¹ *ᵥ b) - (mb.ψ r ⬝ᵥ b) • mb.v r‖ ≤
      ‖s - mb.eig r‖ *
        ∑ i ∈ Finset.univ.erase r, ‖mb.ψ i ⬝ᵥ b‖ / ‖s - mb.eig i‖ * ‖mb.v i‖ := by
  rw [mb.resolvent_mulVec hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ r), smul_add,
    smul_smul, mul_div_cancel₀ _ (sub_ne_zero.mpr (hs r)), add_sub_cancel_left, norm_smul]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_div]

end ModalBasis

/-! ## The forced steady state of a real system (2-17), (2-18) -/

section RealSystem

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

open powerlib.ParametricResonance in
/-- Eq. (2-18): `χ = (jωI − A)⁻¹ b = Σ_i (ψ_iᵀ b)/(jω − λ_i) v_i`. -/
@[tmio T, powerlib_foundation] theorem forcedAmplitude_modal (mb : ModalBasis (Linear.complexify A))
    (b : Fin N → ℂ) {ω : ℝ} (hω : ∀ i, (ω : ℂ) * I ≠ mb.eig i) :
    forcedAmplitude A b ω = ∑ i, ((mb.ψ i ⬝ᵥ b) / ((ω : ℂ) * I - mb.eig i)) • mb.v i :=
  mb.resolvent_mulVec hω b

open powerlib.ParametricResonance in
/-- Eq. (2-17): the modal coordinate of the steady state is `ψ_rᵀ χ = (ψ_rᵀ b)/(jω − λ_r)`. -/
@[tmio T, powerlib_foundation] theorem ψ_dot_forcedAmplitude (mb : ModalBasis (Linear.complexify A))
    (b : Fin N → ℂ) {ω : ℝ} (hω : ∀ i, (ω : ℂ) * I ≠ mb.eig i) (r : Fin N) :
    mb.ψ r ⬝ᵥ forcedAmplitude A b ω = (mb.ψ r ⬝ᵥ b) / ((ω : ℂ) * I - mb.eig r) :=
  mb.ψ_dot_resolvent_mulVec hω b r

open powerlib.ParametricResonance in
/-- The steady state in modal form: `x_k(t) = Re(Σ_i (ψ_iᵀ b)/(jω − λ_i) v_{ki} e^{jωt})`. -/
@[tmio T, powerlib_foundation] theorem forcedOrbit_modal (mb : ModalBasis (Linear.complexify A))
    (b : Fin N → ℂ) {ω : ℝ} (hω : ∀ i, (ω : ℂ) * I ≠ mb.eig i) (t : ℝ) (k : Fin N) :
    forcedOrbit A b ω t k = (∑ i, (mb.ψ i ⬝ᵥ b) / ((ω : ℂ) * I - mb.eig i) * mb.v i k *
      Complex.exp ((ω : ℂ) * t * I)).re := by
  change (forcedAmplitude A b ω k * Complex.exp ((ω : ℂ) * t * I)).re = _
  rw [forcedAmplitude_modal mb b hω, Finset.sum_apply, Finset.sum_mul]
  rfl

open powerlib.ParametricResonance in
/-- The report's sine input: `Re((−jP) e^{jωt}) = Im(P e^{jωt})`. -/
@[tmio T, powerlib_foundation] theorem forcing_neg_I_smul (P : Fin N → ℂ) (ω t : ℝ) (k : Fin N) :
    forcing (-I • P) ω t k = (P k * Complex.exp ((ω : ℂ) * t * I)).im := by
  change ((-I • P) k * Complex.exp ((ω : ℂ) * t * I)).re = _
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

open powerlib.ParametricResonance in
/-- With the sine input the steady state is the report's `x(t) = Im(χ_P e^{jωt})`,
`χ_P = (jωI − A)⁻¹ P`. -/
@[tmio T, powerlib_foundation] theorem forcedOrbit_neg_I_smul (P : Fin N → ℂ) (ω t : ℝ) (k : Fin N) :
    forcedOrbit A (-I • P) ω t k = (forcedAmplitude A P ω k * Complex.exp ((ω : ℂ) * t * I)).im := by
  change (forcedAmplitude A (-I • P) ω k * Complex.exp ((ω : ℂ) * t * I)).re = _
  rw [forcedAmplitude, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, neg_mul,
    Complex.neg_re, Complex.I_mul_re, neg_neg]
  rfl

/-- For a Hurwitz matrix no eigenvalue lies on the imaginary axis. -/
@[tmio T, powerlib_foundation] theorem I_mul_ne_eig_of_isHurwitz (hA : LinearSystems.IsHurwitz A)
    (mb : ModalBasis (Linear.complexify A)) (ω : ℝ) (i : Fin N) : (ω : ℂ) * I ≠ mb.eig i := by
  intro h
  have hre := hA (mb.eig i) (mb.v i) (mb.v_ne_zero i) (mb.mulVec_v i)
  rw [← h] at hre
  simp at hre

open powerlib.ParametricResonance in
/-- Steady state for a Hurwitz matrix: it has the modal form (2-18) and attracts every solution
of `ẋ = A x + Re(b e^{jωt})` exponentially, so after the transient only the steady state
remains. -/
@[tmio T, powerlib_foundation] theorem steadyState_modal (hA : LinearSystems.IsHurwitz A)
    (mb : ModalBasis (Linear.complexify A)) (b : Fin N → ℂ) (ω : ℝ) :
    (∀ t k, forcedOrbit A b ω t k = (∑ i, (mb.ψ i ⬝ᵥ b) / ((ω : ℂ) * I - mb.eig i) * mb.v i k *
      Complex.exp ((ω : ℂ) * t * I)).re) ∧
    ∃ K > 0, ∃ rate > 0, ∀ x : ℝ → EuclideanSpace ℝ (Fin N),
      (∀ t, HasDerivAt x (Linear.op A (x t) + forcing b ω t) t) → ∀ t, 0 ≤ t →
      ‖x t - forcedOrbit A b ω t‖ ≤ K * Real.exp (-(rate * t)) * ‖x 0 - forcedOrbit A b ω 0‖ :=
  ⟨fun t k => forcedOrbit_modal mb b (I_mul_ne_eig_of_isHurwitz hA mb ω) t k,
    forced_error_bound hA b ω⟩

end RealSystem

/-! ## Conjugate pairs (2-19) -/

/-- The contribution of a conjugate pair with residues `R, R̄` at `jω`. -/
def pairTerm (R lam : ℂ) (ω : ℝ) : ℂ :=
  R / ((ω : ℂ) * I - lam) + conj R / ((ω : ℂ) * I - conj lam)

/-- `A_r = −(R λ̄ + R̄ λ)`, a real number. -/
def pairA (R lam : ℂ) : ℝ := -(2 * (R * conj lam).re)

/-- `B_r = R + R̄`, a real number. -/
def pairB (R : ℂ) : ℝ := 2 * R.re

@[tmio T, powerlib_foundation] theorem pairA_eq (R lam : ℂ) :
    (pairA R lam : ℂ) = -(R * conj lam + conj R * lam) := by
  have h := Complex.add_conj (R * conj lam)
  rw [map_mul, Complex.conj_conj] at h
  rw [pairA, Complex.ofReal_neg, ← h]

@[tmio T, powerlib_foundation] theorem pairB_eq (R : ℂ) : (pairB R : ℂ) = R + conj R := by
  rw [pairB, Complex.add_conj]

/-- Eq. (2-19): `R/(jω − λ) + R̄/(jω − λ̄) = (A_r + jωB_r)/((ω_n² − ω²) + j2ζω_nω)`. -/
@[tmio T, powerlib_foundation] theorem pairTerm_eq (R lam : ℂ) {ω : ℝ} (h1 : (ω : ℂ) * I ≠ lam)
    (h2 : (ω : ℂ) * I ≠ conj lam) :
    pairTerm R lam ω = ((pairA R lam : ℂ) + (ω : ℂ) * I * (pairB R : ℂ)) /
      (((naturalFreq lam ^ 2 - ω ^ 2 : ℝ) : ℂ) +
        ((2 * dampingRatio lam * naturalFreq lam * ω : ℝ) : ℂ) * I) := by
  rw [pairTerm, div_add_div _ _ (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2),
    I_mul_sub_mul_I_mul_sub_conj, pairA_eq, pairB_eq]
  congr 1
  ring

/-- Dividing numerator and denominator by `ω_n²`: the single-input normalized form (2-20)/(2-21)
with `ν = ω/ω_n`. -/
@[tmio T, powerlib_foundation] theorem normalize_pair (a b ζ ωn ω : ℝ) (hωn : ωn ≠ 0) :
    ((a : ℂ) + (ω : ℂ) * I * (b : ℂ)) /
        (((ωn ^ 2 - ω ^ 2 : ℝ) : ℂ) + ((2 * ζ * ωn * ω : ℝ) : ℂ) * I) =
      LTI.resonanceResp (a / ωn ^ 2) (b / ωn) ζ (ω / ωn) := by
  have hc : ((ωn ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hωn
  have hωc : (ωn : ℂ) ≠ 0 := by exact_mod_cast hωn
  have hN : (a : ℂ) + (ω : ℂ) * I * (b : ℂ) =
      ((ωn ^ 2 : ℝ) : ℂ) * (((a / ωn ^ 2 : ℝ) : ℂ) + ((ω / ωn * (b / ωn) : ℝ) : ℂ) * I) := by
    push_cast
    field_simp
  have hD : ((ωn ^ 2 - ω ^ 2 : ℝ) : ℂ) + ((2 * ζ * ωn * ω : ℝ) : ℂ) * I =
      ((ωn ^ 2 : ℝ) : ℂ) * LTI.resonanceDen ζ (ω / ωn) := by
    rw [LTI.resonanceDen]
    push_cast
    field_simp
  rw [hN, hD, mul_div_mul_left _ _ hc, LTI.resonanceResp]

/-- The pair term in the normalized form (2-20)/(2-21):
`pair = H(ν)` with `a' = A_r/ω_n²`, `b' = B_r/ω_n`, `ν = ω/ω_n`. -/
@[tmio T, powerlib_foundation] theorem pairTerm_eq_resonanceResp (R : ℂ) {lam : ℂ} (hlam : lam ≠ 0)
    {ω : ℝ} (h1 : (ω : ℂ) * I ≠ lam) (h2 : (ω : ℂ) * I ≠ conj lam) :
    pairTerm R lam ω = LTI.resonanceResp (pairA R lam / naturalFreq lam ^ 2)
      (pairB R / naturalFreq lam) (dampingRatio lam) (ω / naturalFreq lam) := by
  rw [pairTerm_eq R lam h1 h2]
  exact normalize_pair _ _ _ _ _ (norm_ne_zero_iff.mpr hlam)

/-- Eq. (2-22): `|pair|² = ((a/ω_n²)² + (νb/ω_n)²)/((1 − ν²)² + (2ζν)²)`. -/
@[tmio T, powerlib_foundation] theorem sq_norm_pairTerm (R : ℂ) {lam : ℂ} (hlam : lam ≠ 0) {ω : ℝ}
    (h1 : (ω : ℂ) * I ≠ lam) (h2 : (ω : ℂ) * I ≠ conj lam) :
    ‖pairTerm R lam ω‖ ^ 2 =
      ((pairA R lam / naturalFreq lam ^ 2) ^ 2 +
          (ω / naturalFreq lam * (pairB R / naturalFreq lam)) ^ 2) /
        ((1 - (ω / naturalFreq lam) ^ 2) ^ 2 +
          (2 * dampingRatio lam * (ω / naturalFreq lam)) ^ 2) := by
  rw [pairTerm_eq_resonanceResp R hlam h1 h2, LTI.sq_norm_resonanceResp]

/-- A real input `P` and a simple conjugate pair `r ≠ r'` (`λ_{r'} = λ̄_r`): the two modal terms
of state `k` of `(jωI − A)⁻¹ P` form the pair term with residue `R = v_{kr}(ψ_rᵀP)`. -/
@[tmio T, powerlib_foundation] theorem forcedAmplitude_pair {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (mb : ModalBasis (Linear.complexify A)) (P : Fin N → ℝ) {r r' : Fin N}
    (hr : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) (hr' : ∀ j, j ≠ r' → mb.eig j ≠ mb.eig r')
    (hpair : mb.eig r' = conj (mb.eig r)) (ω : ℝ) (k : Fin N) :
    (mb.ψ r ⬝ᵥ fun l => (P l : ℂ)) / ((ω : ℂ) * I - mb.eig r) * mb.v r k +
        (mb.ψ r' ⬝ᵥ fun l => (P l : ℂ)) / ((ω : ℂ) * I - mb.eig r') * mb.v r' k =
      pairTerm (mb.v r k * (mb.ψ r ⬝ᵥ fun l => (P l : ℂ))) (mb.eig r) ω := by
  have h := mb.modalWeight_conj_pair P hr hr' hpair k
  rw [pairTerm, ← h, hpair]
  ring

/-! ## Phase (2-23) -/

@[tmio T, powerlib_foundation] theorem re_div_mul_normSq (z w : ℂ) :
    (z / w).re * normSq w = z.re * w.re + z.im * w.im := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [Complex.div_re]
    field_simp [(Complex.normSq_pos.mpr hw).ne']

@[tmio T, powerlib_foundation] theorem im_div_mul_normSq (z w : ℂ) :
    (z / w).im * normSq w = z.im * w.re - z.re * w.im := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [Complex.div_im]
    field_simp [(Complex.normSq_pos.mpr hw).ne']

/-- Eq. (2-23), exactly: writing `H = |H| e^{−jφ}` (`φ = −arg H`) and `D = (1 − ν²) + j2ζν`,
`|H||D|² cos φ = a(1 − ν²) + 2ζν²b` and `|H||D|² sin φ = 2ζνa − νb(1 − ν²)`. -/
@[tmio T, powerlib_foundation] theorem resonanceResp_phase (a b ζ ν : ℝ) :
    ‖LTI.resonanceResp a b ζ ν‖ * ‖LTI.resonanceDen ζ ν‖ ^ 2 *
        Real.cos (-Complex.arg (LTI.resonanceResp a b ζ ν)) =
      a * (1 - ν ^ 2) + 2 * ζ * ν ^ 2 * b ∧
    ‖LTI.resonanceResp a b ζ ν‖ * ‖LTI.resonanceDen ζ ν‖ ^ 2 *
        Real.sin (-Complex.arg (LTI.resonanceResp a b ζ ν)) =
      2 * ζ * ν * a - ν * b * (1 - ν ^ 2) := by
  have hre := re_div_mul_normSq ((a : ℂ) + ((ν * b : ℝ) : ℂ) * I) (LTI.resonanceDen ζ ν)
  have him := im_div_mul_normSq ((a : ℂ) + ((ν * b : ℝ) : ℂ) * I) (LTI.resonanceDen ζ ν)
  have hD1 : (LTI.resonanceDen ζ ν).re = 1 - ν ^ 2 := by
    simp only [LTI.resonanceDen, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hD2 : (LTI.resonanceDen ζ ν).im = 2 * ζ * ν := by
    simp only [LTI.resonanceDen, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im]
    ring
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, hD1, hD2] at hre him
  rw [← LTI.resonanceResp] at hre him
  rw [Real.cos_neg, Real.sin_neg, Complex.sq_norm]
  constructor
  · rw [mul_right_comm, Complex.norm_mul_cos_arg, hre]
    ring
  · rw [mul_neg, mul_right_comm, Complex.norm_mul_sin_arg, him]
    ring

/-- Eq. (2-23), arctan form: when the cosine part `a(1 − ν²) + 2ζν²b` is positive,
`φ = arctan((2ζνa − νb(1 − ν²))/(a(1 − ν²) + 2ζν²b))`. -/
@[tmio T, powerlib_foundation] theorem resonanceResp_phase_arctan {a b ζ ν : ℝ}
    (h : 0 < a * (1 - ν ^ 2) + 2 * ζ * ν ^ 2 * b) :
    -Complex.arg (LTI.resonanceResp a b ζ ν) =
      Real.arctan ((2 * ζ * ν * a - ν * b * (1 - ν ^ 2)) / (a * (1 - ν ^ 2) + 2 * ζ * ν ^ 2 * b)) := by
  obtain ⟨hc, hs⟩ := resonanceResp_phase a b ζ ν
  set H := LTI.resonanceResp a b ζ ν
  set X := ‖H‖ * ‖LTI.resonanceDen ζ ν‖ ^ 2
  have hX : 0 < X := by
    rcases (eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ X)) with h0 | h0
    · rw [← h0, zero_mul] at hc; linarith
    · exact h0
  have hcos : 0 < Real.cos (-Complex.arg H) := by
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonneg_of_nonpos hX.le hneg
    linarith
  have hre : 0 < H.re := by
    have h1 : 0 < ‖H‖ := by
      by_contra h0
      push Not at h0
      have : ‖H‖ = 0 := le_antisymm h0 (norm_nonneg _)
      simp only [X, this, zero_mul] at hX
      exact lt_irrefl _ hX
    rw [← Complex.norm_mul_cos_arg, ← Real.cos_neg]
    exact mul_pos h1 hcos
  have harg : |Complex.arg H| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have h1 : -(Real.pi / 2) < -Complex.arg H := by
    have := (abs_lt.mp harg).2; linarith
  have h2 : -Complex.arg H < Real.pi / 2 := by
    have := (abs_lt.mp harg).1; linarith
  rw [← hc, ← hs, mul_div_mul_left _ _ hX.ne', ← Real.tan_eq_sin_div_cos, Real.arctan_tan h1 h2]

/-- `Im(H p e^{jθ}) = |H| p sin(θ − φ)`, `φ = −arg H`: the time-domain form (2-21)–(2-23)
`x_{i,r}(t) = B_{i,r} sin(ωt − φ_{i,r})`. -/
@[tmio T, powerlib_foundation] theorem im_mul_exp (H : ℂ) (p θ : ℝ) :
    (H * p * Complex.exp (θ * I)).im = ‖H‖ * p * Real.sin (θ - -Complex.arg H) := by
  have hc := Complex.norm_mul_cos_arg H
  have hs := Complex.norm_mul_sin_arg H
  rw [sub_neg_eq_add, Real.sin_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im]
  linear_combination (-(p * Real.sin θ)) * hc + (-(p * Real.cos θ)) * hs

/-! ## Resonance (2-25)–(2-27) -/

/-- Eq. (2-25), exactly: at `ω = ω_n` the pair term is `(ω_n B_r − jA_r)/(2ζω_n²)`. -/
@[tmio T, powerlib_foundation] theorem pairTerm_at_naturalFreq (R : ℂ) {lam : ℂ} (hre : lam.re ≠ 0) :
    pairTerm R lam (naturalFreq lam) =
      (((naturalFreq lam * pairB R : ℝ) : ℂ) - I * (pairA R lam : ℂ)) /
        ((2 * dampingRatio lam * naturalFreq lam ^ 2 : ℝ) : ℂ) := by
  have hlam : lam ≠ 0 := fun h => hre (by simp [h])
  have hζ : dampingRatio lam ≠ 0 := fun h => hre ((dampingRatio_eq_zero_iff lam).mp h)
  have hn : naturalFreq lam ≠ 0 := norm_ne_zero_iff.mpr hlam
  have h1 : (naturalFreq lam : ℂ) * I ≠ lam := fun h => hre (by rw [← h]; simp)
  have h2 : (naturalFreq lam : ℂ) * I ≠ conj lam := fun h => hre (by
    have := congrArg Complex.re h; simp at this; linarith)
  rw [pairTerm_eq R lam h1 h2, sub_self, Complex.ofReal_zero, zero_add]
  have hden : ((2 * dampingRatio lam * naturalFreq lam ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (mul_ne_zero two_ne_zero hζ) (pow_ne_zero 2 hn)
  rw [div_eq_div_iff (by
    rw [Ne, mul_eq_zero, not_or]
    exact ⟨by exact_mod_cast mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hζ) hn) hn,
      Complex.I_ne_zero⟩) hden]
  push_cast
  linear_combination (2 * (dampingRatio lam : ℂ) * (naturalFreq lam : ℂ) ^ 2 *
    (pairA R lam : ℂ)) * Complex.I_sq

/-- Eq. (2-26), exactly: for `λ = ω_n e^{j(π/2 + δ)}` (so `ζ = sin δ`) the pair term at `ω_n` is
`[R(1 + e^{−jδ}) + R̄(1 − e^{jδ})]/(2 sin δ · ω_n)`. -/
@[tmio T, powerlib_foundation] theorem pairTerm_exp (R : ℂ) {ωn δ : ℝ} (hωn : ωn ≠ 0)
    (hδ : Real.sin δ ≠ 0) :
    pairTerm R ((ωn : ℂ) * Complex.exp (((Real.pi / 2 + δ : ℝ) : ℂ) * I)) ωn =
      (R * (1 + Complex.exp (-(δ : ℂ) * I)) + conj R * (1 - Complex.exp ((δ : ℂ) * I))) /
        ((2 * Real.sin δ * ωn : ℝ) : ℂ) := by
  set e := Complex.exp ((δ : ℂ) * I) with he
  set e' := Complex.exp (-(δ : ℂ) * I) with he'
  have hee : e * e' = 1 := by
    rw [he, he', ← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  have hS : ((2 * Real.sin δ : ℝ) : ℂ) = (e' - e) * I := by
    push_cast; rw [Complex.two_sin]
  have hlam : Complex.exp (((Real.pi / 2 + δ : ℝ) : ℂ) * I) = I * e := by
    have : (((Real.pi / 2 + δ : ℝ) : ℂ) * I) = (Real.pi / 2 : ℂ) * I + (δ : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  have hconj : conj ((ωn : ℂ) * (I * e)) = -((ωn : ℂ) * I * e') := by
    rw [he', map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, he, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  have hfac : ((2 * Real.sin δ : ℝ) : ℂ) = I * (1 - e) * (1 + e') := by
    rw [hS]; linear_combination I * hee
  have hSne : ((2 * Real.sin δ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero hδ
  have h1e : (1 : ℂ) - e ≠ 0 := fun h => hSne (by rw [hfac, h]; ring)
  have h1e' : (1 : ℂ) + e' ≠ 0 := fun h => hSne (by rw [hfac, h]; ring)
  have hωc : (ωn : ℂ) ≠ 0 := by exact_mod_cast hωn
  rw [pairTerm, hlam, hconj]
  have hd1 : (ωn : ℂ) * I - (ωn : ℂ) * (I * e) = (ωn : ℂ) * I * (1 - e) := by ring
  have hd2 : (ωn : ℂ) * I - -((ωn : ℂ) * I * e') = (ωn : ℂ) * I * (1 + e') := by ring
  rw [hd1, hd2]
  have hden : ((2 * Real.sin δ * ωn : ℝ) : ℂ) = ((2 * Real.sin δ : ℝ) : ℂ) * (ωn : ℂ) := by
    push_cast; ring
  rw [hden, div_add_div _ _ (mul_ne_zero (mul_ne_zero hωc I_ne_zero) h1e)
    (mul_ne_zero (mul_ne_zero hωc I_ne_zero) h1e'), div_eq_div_iff (mul_ne_zero (mul_ne_zero
      (mul_ne_zero hωc I_ne_zero) h1e) (mul_ne_zero (mul_ne_zero hωc I_ne_zero) h1e'))
      (mul_ne_zero hSne hωc)]
  rw [hfac]
  ring

/-- The poorly-damped approximation of (2-26)–(2-27) with an explicit error:
`‖sin δ · ω_n · pair − R‖ ≤ ‖R‖ |δ|` for `λ = ω_n e^{j(π/2 + δ)}`. -/
@[tmio T, powerlib_foundation] theorem norm_pairTerm_exp_sub_le (R : ℂ) {ωn δ : ℝ} (hωn : ωn ≠ 0)
    (hδ : Real.sin δ ≠ 0) :
    ‖((Real.sin δ * ωn : ℝ) : ℂ) *
        pairTerm R ((ωn : ℂ) * Complex.exp (((Real.pi / 2 + δ : ℝ) : ℂ) * I)) ωn - R‖ ≤
      ‖R‖ * |δ| := by
  rw [pairTerm_exp R hωn hδ]
  have hc : ((2 * Real.sin δ * ωn : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (mul_ne_zero two_ne_zero hδ) hωn
  have hs' : Complex.sin (δ : ℂ) ≠ 0 := by rw [← Complex.ofReal_sin]; exact_mod_cast hδ
  have hωc : (ωn : ℂ) ≠ 0 := by exact_mod_cast hωn
  have e1 : Complex.exp (-(δ : ℂ) * I) = Complex.exp (I * ((-δ : ℝ) : ℂ)) := by
    congr 1; push_cast; ring
  have e2 : Complex.exp ((δ : ℂ) * I) = Complex.exp (I * (δ : ℂ)) := by rw [mul_comm]
  have hkey : ((Real.sin δ * ωn : ℝ) : ℂ) *
      ((R * (1 + Complex.exp (-(δ : ℂ) * I)) + conj R * (1 - Complex.exp ((δ : ℂ) * I))) /
        ((2 * Real.sin δ * ωn : ℝ) : ℂ)) - R =
      (R * (Complex.exp (I * ((-δ : ℝ) : ℂ)) - 1) -
        conj R * (Complex.exp (I * (δ : ℂ)) - 1)) / 2 := by
    rw [e1, e2]
    push_cast
    field_simp
    ring
  rw [hkey, norm_div, Complex.norm_two]
  have h1 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -δ)
  have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := δ)
  rw [Real.norm_eq_abs, abs_neg] at h1
  rw [Real.norm_eq_abs] at h2
  have hR : ‖conj R‖ = ‖R‖ := Complex.norm_conj R
  calc ‖R * (Complex.exp (I * ((-δ : ℝ) : ℂ)) - 1) - conj R * (Complex.exp (I * (δ : ℂ)) - 1)‖ / 2
      ≤ (‖R‖ * ‖Complex.exp (I * ((-δ : ℝ) : ℂ)) - 1‖ +
          ‖conj R‖ * ‖Complex.exp (I * (δ : ℂ)) - 1‖) / 2 := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (‖R‖ * |δ| + ‖R‖ * |δ|) / 2 := by
        rw [hR]
        gcongr
    _ = ‖R‖ * |δ| := by ring

/-- (2-26)–(2-27) in terms of the damping ratio: for `Re λ < 0 ≤ Im λ`, with `ζ = ζ(λ)`,
`ω_n = |λ|`, `‖ζω_n · pair(ω_n) − R‖ ≤ ‖R‖ arcsin ζ ≤ (π/2) ζ ‖R‖`. -/
@[tmio T, powerlib_foundation] theorem resonance_error (R : ℂ) {lam : ℂ} (hre : lam.re < 0)
    (him : 0 ≤ lam.im) :
    ‖((dampingRatio lam * naturalFreq lam : ℝ) : ℂ) * pairTerm R lam (naturalFreq lam) - R‖ ≤
        ‖R‖ * Real.arcsin (dampingRatio lam) ∧
      ‖R‖ * Real.arcsin (dampingRatio lam) ≤ Real.pi / 2 * dampingRatio lam * ‖R‖ := by
  have hζ : 0 < dampingRatio lam := (dampingRatio_pos_iff lam).mpr hre
  have hζ1 : dampingRatio lam ≤ 1 := (abs_le.mp (abs_dampingRatio_le_one lam)).2
  have hlam : lam ≠ 0 := fun h => by simp [h] at hre
  have hn : naturalFreq lam ≠ 0 := norm_ne_zero_iff.mpr hlam
  obtain ⟨ha0, ha1⟩ := arcsin_le_pi_div_two_mul hζ.le hζ1
  have hsin : Real.sin (Real.arcsin (dampingRatio lam)) = dampingRatio lam :=
    Real.sin_arcsin (by linarith) hζ1
  have hpolar := eq_exp_arcsin him
  refine ⟨?_, ?_⟩
  · have h := norm_pairTerm_exp_sub_le R hn (δ := Real.arcsin (dampingRatio lam))
      (by rw [hsin]; exact hζ.ne')
    rw [hsin, ← hpolar, abs_of_nonneg ha0] at h
    exact h
  · have := mul_le_mul_of_nonneg_left ha1 (norm_nonneg R)
    linarith

/-- The polar form of (2-27): `Im(ρ₁e^{jγ} ρ₂e^{jσ} p / c · e^{jθ}) = ρ₁ρ₂ p/c · sin(θ + γ + σ)`
(`φ̃_ir = |φ̃_ir|e^{jγ_ir}`, `ψ̃_lr = |ψ̃_lr|e^{jσ_lr}`). -/
@[tmio T, powerlib_foundation] theorem im_polar_mul_exp (ρ₁ ρ₂ γ σ p c θ : ℝ) :
    (((ρ₁ : ℂ) * Complex.exp (γ * I)) * ((ρ₂ : ℂ) * Complex.exp (σ * I)) * p / c *
        Complex.exp (θ * I)).im = ρ₁ * ρ₂ * p / c * Real.sin (θ + γ + σ) := by
  have h : ((ρ₁ : ℂ) * Complex.exp (γ * I)) * ((ρ₂ : ℂ) * Complex.exp (σ * I)) * p / c *
      Complex.exp (θ * I) = ((ρ₁ * ρ₂ * p / c : ℝ) : ℂ) * Complex.exp (((θ + γ + σ : ℝ) : ℂ) * I) := by
    push_cast
    rw [show ((θ : ℂ) + γ + σ) * I = γ * I + σ * I + θ * I by ring, Complex.exp_add,
      Complex.exp_add]
    ring
  rw [h, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- (2-27) in the time domain with an explicit error: for `Re λ < 0 ≤ Im λ`,
`|Im(pair(ω_n) e^{jω_n t}) − (‖R‖/(ζω_n)) sin(ω_n t + arg R)| ≤ (π/2)‖R‖/ω_n` for every `t`,
whereas the main term has amplitude `‖R‖/(ζω_n)`. -/
@[tmio T, powerlib_foundation] theorem resonance_time_error (R : ℂ) {lam : ℂ} (hre : lam.re < 0)
    (him : 0 ≤ lam.im) (t : ℝ) :
    |(pairTerm R lam (naturalFreq lam) * Complex.exp ((naturalFreq lam * t : ℝ) * I)).im -
        ‖R‖ / (dampingRatio lam * naturalFreq lam) *
          Real.sin (naturalFreq lam * t + Complex.arg R)| ≤
      Real.pi / 2 * ‖R‖ / naturalFreq lam := by
  have hζ : 0 < dampingRatio lam := (dampingRatio_pos_iff lam).mpr hre
  have hlam : lam ≠ 0 := fun h => by simp [h] at hre
  have hn : 0 < naturalFreq lam := norm_pos_iff.mpr hlam
  set c := dampingRatio lam * naturalFreq lam with hcdef
  have hc : 0 < c := mul_pos hζ hn
  have hmain := im_mul_exp R c⁻¹ (naturalFreq lam * t)
  rw [sub_neg_eq_add] at hmain
  obtain ⟨herr, hbound⟩ := resonance_error R hre him
  set P := pairTerm R lam (naturalFreq lam)
  set E := Complex.exp (((naturalFreq lam * t : ℝ) : ℂ) * I)
  have hE : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hdiff : (P * E).im - ‖R‖ / c * Real.sin (naturalFreq lam * t + Complex.arg R) =
      ((P - R * (c⁻¹ : ℝ)) * E).im := by
    rw [sub_mul, Complex.sub_im, hmain, div_eq_mul_inv]
  rw [hdiff]
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_mul, hE, mul_one]
  have hP : P - R * ((c⁻¹ : ℝ) : ℂ) = ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * P - R) := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    field_simp
  rw [hP, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  have h1 : ‖(c : ℂ) * P - R‖ ≤ Real.pi / 2 * dampingRatio lam * ‖R‖ := by
    exact herr.trans hbound
  calc c⁻¹ * ‖(c : ℂ) * P - R‖ ≤ c⁻¹ * (Real.pi / 2 * dampingRatio lam * ‖R‖) := by
        gcongr
    _ = Real.pi / 2 * ‖R‖ / naturalFreq lam := by
        rw [hcdef]; field_simp

/-- "The smaller the damping ratio, the larger the amplitude": for a fixed residue `R ≠ 0` and
natural frequency `ω_n > 0`, the resonant pair amplitude `|pair(ω_n)|` of
`λ = ω_n(−ζ + j√(1 − ζ²))` tends to `+∞` as `ζ → 0⁺`. -/
@[tmio T, powerlib_foundation] theorem tendsto_norm_pairTerm_resonant {R : ℂ} (hR : R ≠ 0) {ωn : ℝ}
    (hωn : 0 < ωn) :
    Tendsto (fun ζ : ℝ => ‖pairTerm R ((ωn : ℂ) * (-(ζ : ℂ) + (Real.sqrt (1 - ζ ^ 2) : ℂ) * I))
      ωn‖) (𝓝[>] 0) atTop := by
  have hRpos : 0 < ‖R‖ := norm_pos_iff.mpr hR
  -- lower bound `‖R‖/(ζω_n) − (π/2)‖R‖/ω_n`
  have hlow : ∀ᶠ ζ : ℝ in 𝓝[>] (0 : ℝ), ‖R‖ / ωn * ζ⁻¹ - Real.pi / 2 * ‖R‖ / ωn ≤
      ‖pairTerm R ((ωn : ℂ) * (-(ζ : ℂ) + (Real.sqrt (1 - ζ ^ 2) : ℂ) * I)) ωn‖ := by
    have hlt : ∀ᶠ ζ in 𝓝[>] (0 : ℝ), ζ < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, hlt] with ζ hζ hζ1
    have hζ0 : 0 < ζ := hζ
    have habs : |ζ| ≤ 1 := abs_le.mpr ⟨by linarith, hζ1.le⟩
    set lam := (ωn : ℂ) * (-(ζ : ℂ) + (Real.sqrt (1 - ζ ^ 2) : ℂ) * I)
    have hn : naturalFreq lam = ωn := naturalFreq_polar hωn.le habs
    have hd : dampingRatio lam = ζ := dampingRatio_polar hωn habs
    have hre : lam.re < 0 := by
      rw [← dampingRatio_pos_iff, hd]; exact hζ0
    have him : 0 ≤ lam.im := by
      simp only [lam, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.neg_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
        Complex.neg_re]
      have := Real.sqrt_nonneg (1 - ζ ^ 2)
      nlinarith
    obtain ⟨herr, hbound⟩ := resonance_error R hre him
    rw [hn, hd] at herr
    rw [hd] at hbound
    set P := pairTerm R lam ωn
    have hc : 0 < ζ * ωn := mul_pos hζ0 hωn
    -- `‖ζω_n P‖ ≥ ‖R‖ − (π/2)ζ‖R‖`
    have h1 : ‖R‖ - Real.pi / 2 * ζ * ‖R‖ ≤ ζ * ωn * ‖P‖ := by
      have := norm_sub_norm_le R (((ζ * ωn : ℝ) : ℂ) * P)
      rw [norm_sub_rev, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at this
      linarith
    have heq : ‖R‖ / ωn * ζ⁻¹ - Real.pi / 2 * ‖R‖ / ωn =
        (‖R‖ - Real.pi / 2 * ζ * ‖R‖) / (ζ * ωn) := by
      field_simp
    rw [heq, div_le_iff₀ hc]
    linarith
  refine tendsto_atTop_mono' _ hlow ?_
  exact tendsto_atTop_add_const_right _ _
    (Tendsto.const_mul_atTop (div_pos hRpos hωn) tendsto_inv_nhdsGT_zero)

/-! ## Dominant mode at the damped frequency -/

section Dominant

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

open powerlib.ParametricResonance in
/-- Dominant mode: at `ω = ω_d = Im λ_r` one has `jω_d − λ_r = ζ_rω_nr` and
`‖ζ_rω_nr χ − (ψ_rᵀb) v_r‖ ≤ |ζ_rω_nr| Σ_{i≠r} ‖ψ_iᵀb‖ ‖v_i‖/‖jω_d − λ_i‖`, with
`χ = (jω_dI − A)⁻¹ b`. -/
@[tmio T, powerlib_foundation] theorem dominant_mode_bound (mb : ModalBasis (Linear.complexify A))
    (b : Fin N → ℂ) (r : Fin N) (hω : ∀ i, ((mb.eig r).im : ℂ) * I ≠ mb.eig i) :
    ‖((dampingRatio (mb.eig r) * naturalFreq (mb.eig r) : ℝ) : ℂ) •
        forcedAmplitude A b (mb.eig r).im - (mb.ψ r ⬝ᵥ b) • mb.v r‖ ≤
      |dampingRatio (mb.eig r) * naturalFreq (mb.eig r)| *
        ∑ i ∈ Finset.univ.erase r,
          ‖mb.ψ i ⬝ᵥ b‖ / ‖((mb.eig r).im : ℂ) * I - mb.eig i‖ * ‖mb.v i‖ := by
  have hs : ((mb.eig r).im : ℂ) * I - mb.eig r =
      ((dampingRatio (mb.eig r) * naturalFreq (mb.eig r) : ℝ) : ℂ) := by
    rw [dampingRatio_mul_naturalFreq]
    apply Complex.ext <;> simp
  have h := mb.norm_resolvent_mulVec_sub_le hω b r
  rw [hs, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end Dominant

/-! ## Mode shape at resonance (§2.2.3) -/

section ModeShape

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- §2.2.3: along a family of matrices `A ε` with fixed modal vectors (`V`, `W`) whose resonating
eigenvalue is `λ_r = −σ_ε + jω_d` with `σ_ε → 0`, while the other eigenvalues stay at distance
`≥ δ > 0` from `jω_d`, the scaled steady state `σ_ε (jω_dI − A ε)⁻¹ b` tends to `(ψ_rᵀb) v_r`:
for every input `b` the response at resonance is shaped by the right eigenvector `v_r`. -/
@[tmio T, powerlib_foundation] theorem tendsto_mode_shape {ι : Type*} {L : Filter ι}
    {A : ι → Matrix n n ℂ} (mb : ∀ ε, ModalBasis (A ε)) {V W : Matrix n n ℂ}
    (hV : ∀ ε, (mb ε).V = V) (hW : ∀ ε, (mb ε).W = W) (r : n) (ωd : ℝ) {σ : ι → ℝ}
    (hσ : Tendsto σ L (𝓝 0)) (hσ0 : ∀ ε, σ ε ≠ 0)
    (heig : ∀ ε, (mb ε).eig r = -(σ ε : ℂ) + (ωd : ℂ) * I) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ε, ∀ i, i ≠ r → δ ≤ ‖(ωd : ℂ) * I - (mb ε).eig i‖) (b : n → ℂ) :
    Tendsto (fun ε => (σ ε : ℂ) • ((((ωd : ℂ) * I) • (1 : Matrix n n ℂ) - A ε)⁻¹ *ᵥ b)) L
      (𝓝 (((fun l => W l r) ⬝ᵥ b) • fun k => V k r)) := by
  have hs : ∀ ε i, (ωd : ℂ) * I ≠ (mb ε).eig i := by
    intro ε i h
    by_cases hi : i = r
    · subst hi
      rw [heig] at h
      have := congrArg Complex.re h
      simp at this
      exact hσ0 ε (by linarith)
    · have := hsep ε i hi
      rw [h, sub_self, norm_zero] at this
      linarith
  have hsr : ∀ ε, (ωd : ℂ) * I - (mb ε).eig r = (σ ε : ℂ) := by
    intro ε; rw [heig]; ring
  set C := ∑ i ∈ Finset.univ.erase r, ‖(fun l => W l i) ⬝ᵥ b‖ / δ * ‖fun k => V k i‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun ε => ?_) (g := fun ε => |σ ε| * C) ?_
  · have h := (mb ε).norm_resolvent_mulVec_sub_le (hs ε) b r
    rw [hsr, Complex.norm_real, Real.norm_eq_abs] at h
    have hψ : (mb ε).ψ = fun i l => W l i := by
      funext i l; simp [ModalBasis.ψ, hW]
    have hv : (mb ε).v = fun i k => V k i := by
      funext i k; simp [ModalBasis.v, hV]
    rw [hψ, hv] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (abs_nonneg _))
    have hi' : i ≠ r := Finset.ne_of_mem_erase hi
    gcongr
    exact hsep ε i hi'
  · have := (hσ.abs).mul_const C
    simpa using this

/-- §2.2.3, relative amplitude and phase: under the hypotheses of `tendsto_mode_shape`, if the
mode is excited (`ψ_rᵀb ≠ 0`) and visible in state `k'` (`v_{k'r} ≠ 0`), the complex ratio of
the steady-state phasors of states `k` and `k'` tends to `v_{kr}/v_{k'r}`, whatever the input. -/
@[tmio T, powerlib_foundation] theorem tendsto_mode_shape_ratio {ι : Type*} {L : Filter ι}
    {A : ι → Matrix n n ℂ} (mb : ∀ ε, ModalBasis (A ε)) {V W : Matrix n n ℂ}
    (hV : ∀ ε, (mb ε).V = V) (hW : ∀ ε, (mb ε).W = W) (r : n) (ωd : ℝ) {σ : ι → ℝ}
    (hσ : Tendsto σ L (𝓝 0)) (hσ0 : ∀ ε, σ ε ≠ 0)
    (heig : ∀ ε, (mb ε).eig r = -(σ ε : ℂ) + (ωd : ℂ) * I) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ε, ∀ i, i ≠ r → δ ≤ ‖(ωd : ℂ) * I - (mb ε).eig i‖) (b : n → ℂ)
    (hb : (fun l => W l r) ⬝ᵥ b ≠ 0) (k k' : n) (hk' : V k' r ≠ 0) :
    Tendsto (fun ε => ((((ωd : ℂ) * I) • (1 : Matrix n n ℂ) - A ε)⁻¹ *ᵥ b) k /
        ((((ωd : ℂ) * I) • (1 : Matrix n n ℂ) - A ε)⁻¹ *ᵥ b) k') L (𝓝 (V k r / V k' r)) := by
  have h := tendsto_mode_shape mb hV hW r ωd hσ hσ0 heig hδ hsep b
  have hk := (continuous_apply k).continuousAt.tendsto.comp h
  have hk'' := (continuous_apply k').continuousAt.tendsto.comp h
  have hdiv := hk.div hk'' (by simp [hb, hk'])
  have hlim : ((((fun l => W l r) ⬝ᵥ b) • fun k => V k r) k) /
      ((((fun l => W l r) ⬝ᵥ b) • fun k => V k r) k') = V k r / V k' r := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hb]
  rw [hlim] at hdiv
  refine hdiv.congr fun ε => ?_
  have hσc : (σ ε : ℂ) ≠ 0 := by exact_mod_cast hσ0 ε
  simp [mul_div_mul_left _ _ hσc]

end ModeShape

/-! ## Influence of the disturbance location (§2.2.4) -/

namespace ModalBasis

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (mb : ModalBasis A)

/-- A disturbance `p e_l` at location `l` excites mode `r` through `ψ_rᵀ(p e_l) = ψ_{lr} p`. -/
@[tmio T, powerlib_foundation] theorem ψ_dot_single (r l : n) (p : ℂ) :
    mb.ψ r ⬝ᵥ Pi.single l p = mb.W l r * p := by
  rw [dotProduct_single]; rfl

/-- Two disturbance locations `l, l'` give parallel leading vectors, in ratio `ψ_{lr}/ψ_{l'r}`:
the location changes the absolute amplitude, not the relative amplitude or phase. -/
@[tmio T, powerlib_foundation] theorem leading_vector_location (r l l' : n) (p : ℂ)
    (h : mb.W l' r ≠ 0) :
    (mb.ψ r ⬝ᵥ Pi.single l p) • mb.v r =
      (mb.W l r / mb.W l' r) • ((mb.ψ r ⬝ᵥ Pi.single l' p) • mb.v r) := by
  rw [mb.ψ_dot_single, mb.ψ_dot_single, smul_smul]
  congr 1
  field_simp

/-- For a simple eigenvalue, `ψ_{lr} = 0` iff every left eigenvector of `λ_r` vanishes at `l`:
a disturbance at `l` cannot excite the mode (no controllability from `l`). -/
@[tmio T, powerlib_foundation] theorem W_eq_zero_iff {r : n}
    (hsimple : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) (l : n) :
    mb.W l r = 0 ↔ ∀ w : n → ℂ, vecMul w A = mb.eig r • w → w l = 0 := by
  constructor
  · intro h w hw
    have he := mb.left_eigvec_eq hsimple hw
    rw [he, Pi.smul_apply, smul_eq_mul]
    change _ * mb.W l r = 0
    rw [h, mul_zero]
  · intro h
    exact h (mb.ψ r) (mb.vecMul_ψ r)

/-- The leading coefficient `v_{kr} ψ_{lr} p` of state `k` for a disturbance `p e_l` (`p ≠ 0`)
vanishes iff some left eigenvector of `λ_r` vanishes at `l` or some right eigenvector vanishes at
`k` (the PBH form `residue_eq_zero_iff`). -/
@[tmio T, powerlib_foundation] theorem leading_entry_eq_zero_iff {r : n}
    (hsimple : ∀ j, j ≠ r → mb.eig j ≠ mb.eig r) (k l : n) {p : ℂ} (hp : p ≠ 0) :
    mb.V k r * (mb.W l r * p) = 0 ↔
      (∃ w : n → ℂ, w ≠ 0 ∧ vecMul w A = mb.eig r • w ∧ w l = 0) ∨
        (∃ x : n → ℂ, x ≠ 0 ∧ A *ᵥ x = mb.eig r • x ∧ x k = 0) := by
  have h := mb.residue_eq_zero_iff hsimple (Pi.single l p) (Pi.single k 1)
  simp only [single_dotProduct, one_mul, dotProduct_single, mul_eq_zero, hp, or_false] at h
  rw [show mb.V k r * (mb.W l r * p) = 0 ↔ mb.v r k = 0 ∨ mb.ψ r l = 0 by
    simp [ModalBasis.v, ModalBasis.ψ, hp]]
  exact h

end ModalBasis

end powerlib.Modal
