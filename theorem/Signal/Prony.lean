import theorem.Attributes
import dependencies.Mathlib
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Prony's method on exact exponential sums

Prony's method recovers the modes `z_i` and amplitudes `c_i` of a sampled sum of exponentials
`x[k] = Σ_{i<p} c_i z_i^k` exactly from `2p` samples: the Prony polynomial `∏_i (X − z_i)`
annihilates the sequence (linear prediction), its coefficients are the unique solution of the
`p × p` Hankel system built from `x[0], …, x[2p − 1]` (the Hankel matrix is `Vᵀ diag(c) V` with
the Vandermonde matrix `V` of the modes), its roots are the modes, and the amplitudes are the
unique solution of the Vandermonde system. The oscillation phasor of TR-110 (3-6)/(3-7) is the
amplitude of the mode `z = e^{(a + jω)Δt}` of the sampled oscillation, up to the explicit factor
`2j e^{a t₀}`.

Scope.
* Sequences `x : ℕ → ℂ` of the exact form `x[k] = Σ_{i<p} c_i z_i^k` (`expSum c z`) with
  pairwise distinct modes `z_i` (`Function.Injective z`) and nonzero amplitudes `c_i`; `p` is
  known. No noise, no model-order selection, no least-squares (overdetermined) Prony, no
  root-finding algorithm: the statements are the exact algebraic identifiability that these
  numerical procedures approximate.
* The oscillation (3-6) is the sampled signal `e^{a(t − t₀)} P_a sin(ωt + φ_p)` at `t = kΔt`,
  read within one stage of (3-6) (growth: `a` as in the report; sustained stage: `a = 0`); real
  parameters `a, ω, Δt, t₀, P_a, φ_p`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-6), (3-7)
("The oscillation phasors of the active power or angular frequency can be extracted using
Prony's method"), Fig. 3-7; R. de Prony (1795); J. F. Hauer, C. J. Demeure, L. L. Scharf,
"Initial results in Prony analysis of power system response signals", IEEE Trans. Power Syst.
5 (1990).

Results.
* `expSum`, `pronyPoly`, `pronyPoly_monic`, `natDegree_pronyPoly`, `eval_pronyPoly_mode` — the
  exponential sum, the monic Prony polynomial of degree `p`, vanishing at every mode.
* `linearPrediction`, `linearPrediction_recurrence` — `Σ_{j≤p} q_j x[k + j] = 0` for every `k`,
  i.e. `x[k + p] = −Σ_{j<p} q_j x[k + j]` with the coefficients `q_j` of the Prony polynomial.
* `hankel`, `hankel_expSum` (`H = Vᵀ diag(c) V`), `det_hankel_expSum`
  (`det H = (det V)² ∏ c_i`), `det_hankel_expSum_ne_zero`.
* `hankelSystem_iff` — the Hankel system `Σ_{j<p} a_j x[k + j] = −x[k + p]` (`k < p`) holds
  exactly for `a_j = q_j`: the coefficients are uniquely determined by `x[0..2p − 1]`.
* `monicOfCoeffs`, `monicOfCoeffs_eq_pronyPoly`, `roots_pronyPoly`, `prony_modes` — the monic
  polynomial `X^p + Σ_{j<p} a_j X^j` of any solution is the Prony polynomial, whose roots are
  exactly the modes (with multiplicity one each).
* `amplitudes_unique` — given the modes, the amplitudes are the unique solution of the
  Vandermonde system `Σ_i c_i z_i^k = x[k]`, `k < p`.
* `prony_identifiable` — two such sums of `p` terms agreeing on `2p` samples have the same Prony
  polynomial, hence the same modes; with the same modes their amplitudes coincide.
* `oscillation_samples`, `oscillation_mode_norm`, `oscillation_mode_arg`, `oscillation_phasor`,
  `oscillation_phasor_amplitude`, `oscillation_modes_distinct`, `prony_oscillation` — the samples
  of (3-6) are `c z^k + c̄ z̄^k` with `z = e^{(a + jω)Δt}`, `c = e^{−a t₀} P_a e^{jφ_p}/(2j)`;
  `|z| = e^{aΔt}` and `arg z = ωΔt` for `−π < ωΔt ≤ π`; the phasor (3-7) is
  `P_a e^{jφ_p} = 2j e^{a t₀} c` and `P_a = 2 e^{a t₀} |c|`; the two modes are distinct iff
  `sin(ωΔt) ≠ 0`; hence four samples determine the mode and the phasor exactly.

Correction (§3.3). The amplitude that Prony's method returns for the mode
`z = e^{(a + jω)Δt}` is `c = e^{−a t₀} P_a e^{jφ_p}/(2j)`, not the phasor `P_a∠φ_p` itself: the
phasor is `2j e^{a t₀} c` (`oscillation_phasor`), a real factor `2 e^{a t₀}` and a quarter-turn
(the sine convention of (3-6)). Phase angles between two phasors of the same mode are unaffected
by the common factor.

Family and connection conclusions.
* None: this module defines no family; every result is an identity of explicit finite sums,
  matrices and polynomials.
-/

noncomputable section
namespace powerlib.Signal.Prony
open Polynomial Matrix Finset Complex

variable {p : ℕ}

/-- The exponential sum `x[k] = Σ_{i<p} c_i z_i^k`. -/
def expSum (c z : Fin p → ℂ) (k : ℕ) : ℂ := ∑ i, c i * z i ^ k

/-- The Prony polynomial `∏_{i<p} (X − z_i)`. -/
def pronyPoly (z : Fin p → ℂ) : ℂ[X] := ∏ i, (X - C (z i))

@[tmio T, powerlib_foundation] theorem pronyPoly_monic (z : Fin p → ℂ) : (pronyPoly z).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)

@[tmio T, powerlib_foundation] theorem natDegree_pronyPoly (z : Fin p → ℂ) :
    (pronyPoly z).natDegree = p := by
  rw [pronyPoly, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)]
  simp

@[tmio T, powerlib_foundation] theorem eval_pronyPoly_mode (z : Fin p → ℂ) (i : Fin p) :
    (pronyPoly z).eval (z i) = 0 := by
  rw [pronyPoly, eval_prod]
  exact prod_eq_zero (mem_univ i) (by simp)

/-! ## Linear prediction -/

/-- **Linear prediction.** The Prony polynomial annihilates the sequence:
`Σ_{j ≤ p} q_j x[k + j] = 0` for every `k`. -/
@[tmio T, powerlib_foundation] theorem linearPrediction (c z : Fin p → ℂ) (k : ℕ) :
    ∑ j ∈ range (p + 1), (pronyPoly z).coeff j * expSum c z (k + j) = 0 := by
  have h : ∀ i, ∑ j ∈ range (p + 1), (pronyPoly z).coeff j * z i ^ j = 0 := fun i => by
    rw [← eval_pronyPoly_mode z i, eval_eq_sum_range, natDegree_pronyPoly]
  simp only [expSum, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  have : ∀ j, (pronyPoly z).coeff j * (c i * z i ^ (k + j)) =
      c i * z i ^ k * ((pronyPoly z).coeff j * z i ^ j) := fun j => by ring
  simp only [this, ← mul_sum, h i, mul_zero]

/-- The recurrence form: `x[k + p] = −Σ_{j<p} q_j x[k + j]`. -/
@[tmio T, powerlib_foundation] theorem linearPrediction_recurrence (c z : Fin p → ℂ) (k : ℕ) :
    expSum c z (k + p) = -∑ j : Fin p, (pronyPoly z).coeff j * expSum c z (k + j) := by
  have h := linearPrediction c z k
  have hp1 : (pronyPoly z).coeff p = 1 := by
    have := (pronyPoly_monic z).coeff_natDegree
    rwa [natDegree_pronyPoly] at this
  rw [sum_range_succ, hp1, one_mul] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => (pronyPoly z).coeff j * expSum c z (k + j))]
  linear_combination h

/-! ## The Hankel system -/

/-- The `p × p` Hankel matrix `H_{kj} = x[k + j]` of the samples `x[0], …, x[2p − 2]`. -/
def hankel (x : ℕ → ℂ) : Matrix (Fin p) (Fin p) ℂ := of fun k j => x (k + j)

/-- `H = Vᵀ diag(c) V` with the Vandermonde matrix `V_{ij} = z_i^j`. -/
@[tmio T, powerlib_foundation] theorem hankel_expSum (c z : Fin p → ℂ) :
    hankel (expSum c z) = (vandermonde z)ᵀ * diagonal c * vandermonde z := by
  ext k j
  simp only [hankel, of_apply, expSum, mul_apply, transpose_apply, vandermonde_apply,
    diagonal_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true, pow_add]
  refine sum_congr rfl fun i _ => by ring

@[tmio T, powerlib_foundation] theorem det_hankel_expSum (c z : Fin p → ℂ) :
    (hankel (p := p) (expSum c z)).det = (vandermonde z).det ^ 2 * ∏ i, c i := by
  rw [hankel_expSum, det_mul, det_mul, det_transpose, det_diagonal]
  ring

/-- Distinct modes and nonzero amplitudes make the Hankel matrix invertible. -/
@[tmio T, powerlib_foundation] theorem det_hankel_expSum_ne_zero {c z : Fin p → ℂ}
    (hz : Function.Injective z) (hc : ∀ i, c i ≠ 0) : (hankel (p := p) (expSum c z)).det ≠ 0 := by
  rw [det_hankel_expSum]
  exact mul_ne_zero (pow_ne_zero 2 (det_vandermonde_ne_zero_iff.mpr hz))
    (prod_ne_zero_iff.mpr fun i _ => hc i)

/-- **The Hankel system determines the prediction coefficients.** For distinct modes and nonzero
amplitudes, `Σ_{j<p} a_j x[k + j] = −x[k + p]` for all `k < p` (a system in `x[0..2p − 1]`)
holds exactly when `a_j` are the coefficients of the Prony polynomial. -/
@[tmio T, powerlib_foundation] theorem hankelSystem_iff {c z : Fin p → ℂ}
    (hz : Function.Injective z) (hc : ∀ i, c i ≠ 0) (a : Fin p → ℂ) :
    (∀ k : Fin p, ∑ j : Fin p, a j * expSum c z (k + j) = -expSum c z (k + p)) ↔
      ∀ j : Fin p, a j = (pronyPoly z).coeff j := by
  have hq : ∀ k : Fin p, ∑ j : Fin p, (pronyPoly z).coeff j * expSum c z (k + j) =
      -expSum c z (k + p) := fun k => by
    rw [linearPrediction_recurrence c z k, neg_neg]
  constructor
  · intro ha
    have h0 : hankel (expSum c z) *ᵥ (fun j => a j - (pronyPoly z).coeff j) = 0 := by
      funext k
      simp only [mulVec, dotProduct, hankel, of_apply, Pi.zero_apply, mul_sub, sum_sub_distrib]
      have e1 := ha k
      have e2 := hq k
      simp only [mul_comm (expSum c z _)] at e1 e2 ⊢
      rw [e1, e2, sub_self]
    have := eq_zero_of_mulVec_eq_zero (det_hankel_expSum_ne_zero hz hc) h0
    intro j
    exact sub_eq_zero.mp (congrFun this j)
  · intro ha k
    simp only [ha]
    exact hq k

/-! ## Recovery of the modes and amplitudes -/

/-- The monic polynomial `X^p + Σ_{j<p} a_j X^j` of prediction coefficients. -/
def monicOfCoeffs (a : Fin p → ℂ) : ℂ[X] := X ^ p + ∑ j : Fin p, C (a j) * X ^ (j : ℕ)

/-- The polynomial of the Prony coefficients is the Prony polynomial. -/
@[tmio T, powerlib_foundation] theorem monicOfCoeffs_eq_pronyPoly (z : Fin p → ℂ) :
    monicOfCoeffs (fun j : Fin p => (pronyPoly z).coeff j) = pronyPoly z := by
  conv_rhs => rw [(pronyPoly_monic z).as_sum, natDegree_pronyPoly]
  rw [monicOfCoeffs, Fin.sum_univ_eq_sum_range (fun j => C ((pronyPoly z).coeff j) * X ^ j)]

/-- The roots of the Prony polynomial are exactly the modes, each once. -/
@[tmio T, powerlib_foundation] theorem roots_pronyPoly (z : Fin p → ℂ) :
    (pronyPoly z).roots = Multiset.map z univ.val := by
  have h : Multiset.map (fun i => X - C (z i)) univ.val =
      Multiset.map (fun a => X - C a) (Multiset.map z univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [pronyPoly, prod_eq_multiset_prod, h, roots_multiset_prod_X_sub_C]

/-- **Prony's method recovers the modes.** For distinct modes and nonzero amplitudes, every
solution `a` of the Hankel system gives the polynomial `X^p + Σ_{j<p} a_j X^j` whose roots are
exactly the modes. -/
@[tmio T, powerlib_foundation] theorem prony_modes {c z : Fin p → ℂ} (hz : Function.Injective z)
    (hc : ∀ i, c i ≠ 0) {a : Fin p → ℂ}
    (ha : ∀ k : Fin p, ∑ j : Fin p, a j * expSum c z (k + j) = -expSum c z (k + p)) :
    monicOfCoeffs a = pronyPoly z ∧ (monicOfCoeffs a).roots = Multiset.map z univ.val := by
  have h : a = fun j : Fin p => (pronyPoly z).coeff j :=
    funext ((hankelSystem_iff hz hc a).mp ha)
  rw [h, monicOfCoeffs_eq_pronyPoly]
  exact ⟨rfl, roots_pronyPoly z⟩

/-- **Prony's method recovers the amplitudes.** With the modes known (distinct), the amplitudes
are the unique solution of `Σ_i c'_i z_i^k = x[k]`, `k < p`. -/
@[tmio T, powerlib_foundation] theorem amplitudes_unique {c z : Fin p → ℂ}
    (hz : Function.Injective z) {c' : Fin p → ℂ}
    (h : ∀ k : Fin p, ∑ i, c' i * z i ^ (k : ℕ) = expSum c z k) : c' = c := by
  have h0 : (fun i => c' i - c i) = 0 := by
    refine eq_zero_of_forall_pow_sum_mul_pow_eq_zero hz fun k => ?_
    simp only [sub_mul, sum_sub_distrib, h k, expSum, sub_self]
  funext i
  exact sub_eq_zero.mp (congrFun h0 i)

/-- **Identifiability from `2p` samples.** If a `p`-term exponential sum with distinct modes and
nonzero amplitudes agrees on `x[0], …, x[2p − 1]` with any other `p`-term sum, the two have the
same Prony polynomial (hence the same modes, `roots_pronyPoly`); if their modes are the same,
their amplitudes are the same. -/
@[tmio T, powerlib_foundation] theorem prony_identifiable {c z c' z' : Fin p → ℂ}
    (hz : Function.Injective z) (hc : ∀ i, c i ≠ 0)
    (h : ∀ k < 2 * p, expSum c z k = expSum c' z' k) :
    pronyPoly z = pronyPoly z' ∧ (z = z' → c = c') := by
  have hk : ∀ k j : Fin p, (k : ℕ) + j < 2 * p := fun k j => by omega
  have hkp : ∀ k : Fin p, (k : ℕ) + p < 2 * p := fun k => by omega
  -- the coefficients of `z'` solve the Hankel system of the first sum
  have hsys : ∀ k : Fin p, ∑ j : Fin p, (pronyPoly z').coeff j * expSum c z (k + j) =
      -expSum c z (k + p) := fun k => by
    rw [h _ (hkp k)]
    simp only [h _ (hk k _)]
    rw [linearPrediction_recurrence c' z' k, neg_neg]
  have hcoef := (hankelSystem_iff hz hc _).mp hsys
  have hpoly : pronyPoly z = pronyPoly z' := by
    rw [← monicOfCoeffs_eq_pronyPoly z, ← monicOfCoeffs_eq_pronyPoly z']
    congr 1
    funext j
    exact (hcoef j).symm
  refine ⟨hpoly, fun hzz => ?_⟩
  subst hzz
  refine (amplitudes_unique hz fun k => ?_).symm
  rw [h k (by omega)]
  rfl

/-! ## The oscillation phasor of TR-110 (3-6)/(3-7) -/

section Phasor

/-- The samples of (3-6), `e^{a(kΔt − t₀)} P_a sin(ω kΔt + φ)`, are the two-mode sum
`c z^k + c̄ z̄^k` with the mode `z = e^{(a + jω)Δt}` and the amplitude
`c = e^{−a t₀} P_a e^{jφ}/(2j)`. -/
@[tmio T, powerlib_foundation] theorem oscillation_samples (a ω Δt t₀ Pa φ : ℝ) (k : ℕ) :
    ((Real.exp (a * (k * Δt - t₀)) * Pa * Real.sin (ω * (k * Δt) + φ) : ℝ) : ℂ) =
      (cexp (-(a * t₀)) * Pa * cexp (φ * I) / (2 * I)) * cexp ((a + ω * I) * Δt) ^ k +
        (starRingEnd ℂ) (cexp (-(a * t₀)) * Pa * cexp (φ * I) / (2 * I)) *
          (starRingEnd ℂ) (cexp ((a + ω * I) * Δt)) ^ k := by
  set A : ℝ := Real.exp (a * (k * Δt - t₀)) * Pa
  set θ : ℝ := ω * (k * Δt) + φ
  have hA : (A : ℂ) = cexp (((a * (k * Δt - t₀)) : ℝ) : ℂ) * Pa := by
    simp only [A]; push_cast; ring
  have e : cexp (-(a * t₀)) * cexp (φ * I) * cexp (k * ((a + ω * I) * Δt)) =
      cexp (((a * (k * Δt - t₀)) : ℝ) : ℂ) * cexp (θ * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; simp only [θ]; push_cast; ring
  have hcz : (cexp (-(a * t₀)) * Pa * cexp (φ * I) / (2 * I)) * cexp ((a + ω * I) * Δt) ^ k =
      (A : ℂ) * (cexp (θ * I) / (2 * I)) := by
    rw [← Complex.exp_nat_mul, hA]
    calc cexp (-(a * t₀)) * Pa * cexp (φ * I) / (2 * I) * cexp (k * ((a + ω * I) * Δt))
        = Pa / (2 * I) * (cexp (-(a * t₀)) * cexp (φ * I) * cexp (k * ((a + ω * I) * Δt))) := by
          ring
      _ = Pa / (2 * I) * (cexp (((a * (k * Δt - t₀)) : ℝ) : ℂ) * cexp (θ * I)) := by rw [e]
      _ = _ := by ring
  have hre : ((A : ℂ) * (cexp (θ * I) / (2 * I))).re = A * Real.sin θ / 2 := by
    have : cexp (θ * I) / (2 * I) = cexp (θ * I) * (-I / 2) := by
      rw [div_eq_mul_inv]
      congr 1
      field_simp
      linear_combination I_sq
    rw [re_ofReal_mul, this, mul_re]
    simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp
    ring
  rw [← map_pow, ← map_mul, hcz, Complex.add_conj, hre]
  push_cast
  ring

/-- `|z| = e^{aΔt}`: the modulus of the mode gives the growth rate `a`. -/
@[tmio T, powerlib_foundation] theorem oscillation_mode_norm (a ω Δt : ℝ) :
    ‖cexp ((a + ω * I) * Δt)‖ = Real.exp (a * Δt) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- `arg z = ωΔt` for `−π < ωΔt ≤ π`: the argument of the mode gives the frequency `ω`. -/
@[tmio T, powerlib_foundation] theorem oscillation_mode_arg (a ω Δt : ℝ)
    (h₁ : -Real.pi < ω * Δt) (h₂ : ω * Δt ≤ Real.pi) :
    arg (cexp ((a + ω * I) * Δt)) = ω * Δt := by
  rw [Complex.arg_exp]
  have him : ((a + ω * I) * Δt : ℂ).im = ω * Δt := by simp
  rw [him, toIocMod_eq_self]
  exact ⟨h₁, by linarith⟩

/-- The oscillation phasor (3-7) from the amplitude of the mode:
`P_a e^{jφ} = 2j e^{a t₀} c`. -/
@[tmio T, powerlib_foundation] theorem oscillation_phasor (a t₀ φ Pa : ℝ) :
    (Pa : ℂ) * cexp (φ * I) =
      2 * I * cexp (a * t₀) * (cexp (-(a * t₀)) * Pa * cexp (φ * I) / (2 * I)) := by
  have hI : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have he : cexp (a * t₀) * cexp (-(a * t₀)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  field_simp
  linear_combination (-(Pa : ℂ)) * he

/-- The phasor magnitude: `P_a = 2 e^{a t₀} |c|` for `P_a ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem oscillation_phasor_amplitude (a t₀ φ : ℝ) {Pa : ℝ}
    (hPa : 0 ≤ Pa) :
    Pa = 2 * Real.exp (a * t₀) * ‖cexp (-(a * t₀)) * Pa * cexp (φ * I) / (2 * I)‖ := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, norm_mul, Complex.norm_I, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_nonneg hPa]
  have h : (-((a : ℂ) * t₀)).re = -(a * t₀) := by simp
  rw [h, Real.exp_neg]
  have := Real.exp_pos (a * t₀)
  field_simp

/-- The two modes `z`, `z̄` of a sampled oscillation are distinct exactly when
`sin(ωΔt) ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem oscillation_modes_distinct (a ω Δt : ℝ) :
    cexp ((a + ω * I) * Δt) ≠ (starRingEnd ℂ) (cexp ((a + ω * I) * Δt)) ↔
      Real.sin (ω * Δt) ≠ 0 := by
  rw [ne_comm, Ne, Complex.conj_eq_iff_im, Complex.exp_im]
  have h1 : ((a + ω * I) * Δt : ℂ).re = a * Δt := by simp
  have h2 : ((a + ω * I) * Δt : ℂ).im = ω * Δt := by simp
  rw [h1, h2, mul_eq_zero, not_or]
  exact ⟨fun h => h.2, fun h => ⟨(Real.exp_pos _).ne', h⟩⟩

/-- **Prony's method on a sampled oscillation (3-6).** If `P_a ≠ 0` and `sin(ωΔt) ≠ 0`, every
solution `q` of the `2 × 2` Hankel system built from the samples `x[0], …, x[3]` gives the
polynomial `X² + q₁X + q₀` whose roots are exactly `z = e^{(a + jω)Δt}` and `z̄`, and every
solution `c'` of the Vandermonde system for these modes returns the phasor (3-7):
`P_a e^{jφ} = 2j e^{a t₀} c'₀`. -/
@[tmio T, powerlib_foundation] theorem prony_oscillation {a ω Δt t₀ Pa φ : ℝ} (hPa : Pa ≠ 0)
    (hs : Real.sin (ω * Δt) ≠ 0) {q c' : Fin 2 → ℂ}
    (hq : ∀ k : Fin 2, ∑ j : Fin 2, q j *
        ((Real.exp (a * (((k + j : ℕ) : ℝ) * Δt - t₀)) * Pa *
          Real.sin (ω * (((k + j : ℕ) : ℝ) * Δt) + φ) : ℝ) : ℂ) =
      -((Real.exp (a * (((k + 2 : ℕ) : ℝ) * Δt - t₀)) * Pa *
          Real.sin (ω * (((k + 2 : ℕ) : ℝ) * Δt) + φ) : ℝ) : ℂ))
    (hc' : ∀ k : Fin 2, ∑ i, c' i * (![cexp ((a + ω * I) * Δt),
        (starRingEnd ℂ) (cexp ((a + ω * I) * Δt))] i) ^ (k : ℕ) =
      ((Real.exp (a * (((k : ℕ) : ℝ) * Δt - t₀)) * Pa *
          Real.sin (ω * (((k : ℕ) : ℝ) * Δt) + φ) : ℝ) : ℂ)) :
    (∀ w, w ∈ (monicOfCoeffs q).roots ↔
        w = cexp ((a + ω * I) * Δt) ∨ w = (starRingEnd ℂ) (cexp ((a + ω * I) * Δt))) ∧
      (Pa : ℂ) * cexp (φ * I) = 2 * I * cexp (a * t₀) * c' 0 := by
  set z : ℂ := cexp ((a + ω * I) * Δt)
  set c : ℂ := cexp (-(a * t₀)) * Pa * cexp (φ * I) / (2 * I)
  have hx : (fun k : ℕ => ((Real.exp (a * (k * Δt - t₀)) * Pa *
      Real.sin (ω * (k * Δt) + φ) : ℝ) : ℂ)) = expSum ![c, (starRingEnd ℂ) c]
        ![z, (starRingEnd ℂ) z] := by
    funext k
    rw [oscillation_samples, expSum, Fin.sum_univ_two]
    rfl
  have hinj : Function.Injective ![z, (starRingEnd ℂ) z] := by
    have hne : z ≠ (starRingEnd ℂ) z := (oscillation_modes_distinct a ω Δt).mpr hs
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hc0 : c ≠ 0 := by
    have : (Pa : ℂ) ≠ 0 := by exact_mod_cast hPa
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) this)
      (Complex.exp_ne_zero _)) (mul_ne_zero two_ne_zero I_ne_zero)
  have hc : ∀ i, (![c, (starRingEnd ℂ) c] : Fin 2 → ℂ) i ≠ 0 := by
    intro i
    fin_cases i
    · exact hc0
    · simpa using hc0
  have hq' : ∀ k : Fin 2, ∑ j : Fin 2, q j * expSum ![c, (starRingEnd ℂ) c]
      ![z, (starRingEnd ℂ) z] (k + j) = -expSum ![c, (starRingEnd ℂ) c] ![z, (starRingEnd ℂ) z]
        (k + 2) := fun k => by
    rw [← hx]
    exact hq k
  refine ⟨fun w => ?_, ?_⟩
  · rw [(prony_modes hinj hc hq').2, Multiset.mem_map]
    constructor
    · rintro ⟨i, -, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, mem_univ_val _, rfl⟩
      · exact ⟨1, mem_univ_val _, rfl⟩
  · have hc'' : c' = ![c, (starRingEnd ℂ) c] := amplitudes_unique hinj fun k => by
      rw [← hx]
      exact hc' k
    rw [hc'', Matrix.cons_val_zero]
    exact oscillation_phasor a t₀ φ Pa

end Phasor

end powerlib.Signal.Prony
