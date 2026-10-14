import theorem.GFL.DCLink.FourState

/-! # Frozen PLL sub-block of the four-state GFL model

Closed forms (foundation) for the PLL block of `GFL.DCLink.FourState`.

Model boundary.
The `(θ, x)` block of `A₀` with the dc-loop feedback `X_g k_pv Ṽ + X_g k_iv η̃` frozen; linear,
continuous time.

Source: work-sync `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2 (冻结 PLL
子块), §3.2; `.../references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md` §14, §17 (GFL 部分);
`.../gfl-gfm-contrast/archive/notes/concepts/contrast-conclusions.md` 差别一.

Results.
* `pllBlock v k_p k_i`: a two-state single-input single-output `Linear.Plant 2 1` whose state matrix
  is the PLL block `[[−k_p v, k_i], [−v, 0]]` of `A₀` (`pllBlock_A_eq_A0`).  Realization:
  state `(ξ, x)` with `ξ = θ + θ_g` the estimated grid angle, input `θ_g` (grid angle),
  output `θ = ξ − θ_g` (PLL error angle); `pllBlock_field` shows this is the linearized PLL
  `θ̇ = −k_p v θ + k_i x − θ̇_g`, `ẋ = −v θ` rewritten in `ξ`.
* `transfer_pllBlock`: its transfer function is `T_PLL(s) = −s² / L_PLL(s)`,
  `L_PLL(s) = s² + k_p v s + k_i v`.
* `pll_closed_forms`: for the quasi-static PLL Jacobian `[[−k_p S, k_i], [−S, 0]]`,
  `S = V cos θ > 0`: `det(sI − J) = s² + 2ζω_n s + ω_n²`, `ω_n = √(k_i S)`,
  `ζ = (k_p/2)√(S/k_i)` (contrast-conclusions 差别一).
* `norm_T_jΩ`: `|T_PLL(jΩ)| = r² / √((1 − r²)² + 4ζ²r²)`, `r = Ω/ω_pll`,
  `ω_pll = √(k_i v)`, `ζ_pll = k_p v / (2ω_pll)`.
* `hasDerivAt_normSq_LPLL`: `∂_{k_p} |L_PLL(2jω)|² = 8ω² k_p v²`, and `|T(2jω)|` is strictly
  decreasing in `k_p > 0` (`norm_T_strictAnti`).  This is a statement about the frozen block
  only; in the full four-state model the victim mode moves at `O(Γ)`.

Family and connection conclusions.
No family and no connection conclusion: transfer-function and
characteristic-polynomial identities of the frozen block. The frozen block is a
`Linear.Plant 2 1`; `pllBlock_field` states its state
and output equations with explicit matrix-vector products.
-/

noncomputable section
namespace powerlib.GFL.Parametric.PLLBlock
open powerlib.GFL.DCLink
open Matrix

/-- The frozen PLL block as a SISO linear plant (input `θ_g`, output `θ`). -/
def pllBlock (v kp ki : ℝ) : Linear.Plant 2 1 where
  A := !![-kp * v, ki; -v, 0]
  B := !![kp * v; v]
  C := !![1, 0]
  D := !![-1]

/-- `L_PLL(s) = s² + k_p v s + k_i v` -/
def LPLL (v kp ki : ℝ) (s : ℂ) : ℂ := s ^ 2 + ((kp * v : ℝ) : ℂ) * s + ((ki * v : ℝ) : ℂ)

/-- The block matrix is the `(θ, x)` block of the four-state `A₀`. -/
@[powerlib_foundation] theorem pllBlock_A_eq_A0 (p : FourState.Params) (θ0 : ℝ) (i j : Fin 2) :
    (pllBlock (FourState.vd0 p θ0) p.kp p.ki).A i j =
      FourState.A0 p θ0 (Fin.castLE (by norm_num) i) (Fin.castLE (by norm_num) j) := by
  fin_cases i <;> fin_cases j <;> simp [pllBlock, FourState.A0]

/-- Realization: with `ξ = θ + θ_g`, the block's state equation `A (ξ, x) + B θ_g` is the
linearized PLL and its output `C (ξ, x) + D θ_g` is the error angle `θ`. -/
@[powerlib_foundation] theorem pllBlock_field (v kp ki θ x θg : ℝ) :
    (pllBlock v kp ki).A *ᵥ ![θ + θg, x] + (pllBlock v kp ki).B *ᵥ ![θg] =
        ![-kp * v * θ + ki * x, -v * θ] ∧
      (pllBlock v kp ki).C *ᵥ ![θ + θg, x] + (pllBlock v kp ki).D *ᵥ ![θg] = ![θ] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [pllBlock] <;> ring

@[powerlib_foundation] theorem det_characteristicMatrix_pllBlock (v kp ki : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (pllBlock v kp ki).A s).det = LPLL v kp ki s := by
  rw [Criteria.det_characteristicMatrix_fin_two]
  simp [pllBlock, LPLL, Matrix.trace_fin_two, Matrix.det_fin_two]

/-- `T_PLL(s) = −s² / L_PLL(s)`. -/
@[powerlib_foundation] theorem transfer_pllBlock (v kp ki : ℝ) {s : ℂ}
    (hs : LPLL v kp ki s ≠ 0) :
    Linear.transfer (pllBlock v kp ki) s 0 0 = -s ^ 2 / LPLL v kp ki s := by
  rw [Linear.transfer_eq_adjugate, det_characteristicMatrix_pllBlock]
  simp [pllBlock, Linear.characteristicMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  field_simp
  simp [LPLL]
  ring

/-- Quasi-static PLL closed forms: `ω_n = √(k_i S)`, `ζ = (k_p/2)√(S/k_i)`. -/
@[powerlib_foundation] theorem pll_closed_forms {kp ki S : ℝ} (hki : 0 < ki) (hS : 0 < S)
    (s : ℂ) :
    (Linear.characteristicMatrix !![-kp * S, ki; -S, 0] s).det =
      s ^ 2 + ((2 * (kp / 2 * Real.sqrt (S / ki)) * Real.sqrt (ki * S) : ℝ) : ℂ) * s +
        ((Real.sqrt (ki * S) ^ 2 : ℝ) : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  have h1 : Real.sqrt (ki * S) ^ 2 = ki * S := Real.sq_sqrt (by positivity)
  have h2 : 2 * (kp / 2 * Real.sqrt (S / ki)) * Real.sqrt (ki * S) = kp * S := by
    have hm : Real.sqrt (S / ki) * Real.sqrt (ki * S) = S := by
      rw [← Real.sqrt_mul (by positivity)]
      have : S / ki * (ki * S) = S ^ 2 := by field_simp
      rw [this, Real.sqrt_sq hS.le]
    rw [show 2 * (kp / 2 * Real.sqrt (S / ki)) * Real.sqrt (ki * S) =
      kp * (Real.sqrt (S / ki) * Real.sqrt (ki * S)) by ring, hm]
  rw [h1, h2]
  push_cast
  ring

/-- `|T_PLL(jΩ)| = r²/√((1 − r²)² + 4ζ²r²)` with `r = Ω/ω_pll`. -/
@[powerlib_foundation] theorem norm_T_jΩ {v kp ki : ℝ} (hkv : 0 < ki * v) (Ω : ℝ) :
    ‖-(Complex.I * Ω) ^ 2 / LPLL v kp ki (Complex.I * Ω)‖ =
      (Ω / Real.sqrt (ki * v)) ^ 2 /
        Real.sqrt ((1 - (Ω / Real.sqrt (ki * v)) ^ 2) ^ 2 +
          4 * (kp * v / (2 * Real.sqrt (ki * v))) ^ 2 * (Ω / Real.sqrt (ki * v)) ^ 2) := by
  set w := Real.sqrt (ki * v) with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 hkv
  have hw2 : w ^ 2 = ki * v := Real.sq_sqrt hkv.le
  have hnum : ‖-(Complex.I * (Ω : ℂ)) ^ 2‖ = Ω ^ 2 := by
    rw [norm_neg, mul_pow, Complex.I_sq, norm_mul, norm_neg, norm_one, one_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hden : ‖LPLL v kp ki (Complex.I * Ω)‖ =
      Real.sqrt ((ki * v - Ω ^ 2) ^ 2 + (kp * v * Ω) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp [LPLL, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [norm_div, hnum, hden]
  have hrhs : (1 - (Ω / w) ^ 2) ^ 2 + 4 * (kp * v / (2 * w)) ^ 2 * (Ω / w) ^ 2 =
      ((ki * v - Ω ^ 2) ^ 2 + (kp * v * Ω) ^ 2) / (w ^ 2) ^ 2 := by
    rw [← hw2]
    field_simp
    ring
  rw [hrhs, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

/-- `|L_PLL(2jω)|² = (k_i v − 4ω²)² + (2ω k_p v)²`. -/
@[powerlib_foundation] theorem normSq_LPLL (v kp ki ω : ℝ) :
    Complex.normSq (LPLL v kp ki (2 * Complex.I * ω)) =
      (ki * v - 4 * ω ^ 2) ^ 2 + (2 * ω * kp * v) ^ 2 := by
  simp [LPLL, Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- `∂_{k_p} |L_PLL(2jω)|² = 8ω² k_p v²`. -/
@[powerlib_foundation] theorem hasDerivAt_normSq_LPLL (v ki ω kp : ℝ) :
    HasDerivAt (fun kp => Complex.normSq (LPLL v kp ki (2 * Complex.I * ω)))
      (8 * ω ^ 2 * kp * v ^ 2) kp := by
  simp only [normSq_LPLL]
  have := ((hasDerivAt_id kp).const_mul (2 * ω)).mul_const v |>.pow 2 |>.const_add
    ((ki * v - 4 * ω ^ 2) ^ 2)
  convert this using 1
  · ext k; simp
  · simp; ring

/-- `|T(2jω)| = 4ω²/|L_PLL(2jω)|` is strictly decreasing in `k_p > 0` (for `ω, v ≠ 0`). -/
@[powerlib_foundation] theorem norm_T_strictAnti {v ki ω : ℝ} (hω : ω ≠ 0) (hv : v ≠ 0)
    {kp kp' : ℝ} (hkp : 0 < kp) (hlt : kp < kp') :
    ‖-(2 * Complex.I * ω) ^ 2 / LPLL v kp' ki (2 * Complex.I * ω)‖ <
      ‖-(2 * Complex.I * ω) ^ 2 / LPLL v kp ki (2 * Complex.I * ω)‖ := by
  have hsq : ∀ k, ‖LPLL v k ki (2 * Complex.I * ω)‖ ^ 2 =
      (ki * v - 4 * ω ^ 2) ^ 2 + (2 * ω * k * v) ^ 2 := by
    intro k; rw [← Complex.normSq_eq_norm_sq, normSq_LPLL]
  have hsqpos : 0 < ‖LPLL v kp ki (2 * Complex.I * ω)‖ ^ 2 := by
    rw [hsq]; have : 0 < (2 * ω * kp * v) ^ 2 := by positivity
    positivity
  have hpos : 0 < ‖LPLL v kp ki (2 * Complex.I * ω)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hsqpos
    simp at hsqpos
  have hlt2 : ‖LPLL v kp ki (2 * Complex.I * ω)‖ ^ 2 < ‖LPLL v kp' ki (2 * Complex.I * ω)‖ ^ 2 := by
    rw [hsq, hsq]
    have h1 : 0 < (2 * ω * v) ^ 2 := by positivity
    have h2 : kp ^ 2 < kp' ^ 2 := by nlinarith
    have e : ∀ k : ℝ, (2 * ω * k * v) ^ 2 = (2 * ω * v) ^ 2 * k ^ 2 := fun k => by ring
    rw [e, e]
    nlinarith [mul_lt_mul_of_pos_left h2 h1]
  have hlt : ‖LPLL v kp ki (2 * Complex.I * ω)‖ < ‖LPLL v kp' ki (2 * Complex.I * ω)‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt2
  have hnum : 0 < ‖-(2 * Complex.I * (ω : ℂ)) ^ 2‖ := by
    rw [norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real]
    have : 0 < ‖ω‖ := norm_pos_iff.2 hω
    norm_num
    positivity
  rw [norm_div, norm_div]
  exact div_lt_div_of_pos_left hnum hpos hlt

end powerlib.GFL.Parametric.PLLBlock
