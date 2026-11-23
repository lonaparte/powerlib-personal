import theorem.GridTiedConverter.GFL.DCLink.FourState

/-! # Frozen PLL sub-block of the four-state GFL model

Closed forms (domain) for the PLL block of `GFL.DCLink.FourState`.

Model boundary.
The `(θ, x)` block of `A₀` with the dc-loop feedback `X_g k_pv Ṽ + X_g k_iv η̃` frozen; linear,
continuous time.

Source: work-sync `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2 (冻结 PLL
子块), §3.2; `.../references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md` §14, §17 (GFL 部分);
`.../gfl-gfm-contrast/archive/notes/concepts/contrast-conclusions.md` 差别一.

Results.
* `pllBlock v k_p k_i`: a two-state single-input single-output `Linear.Plant 2 1`, the phase model
  `PLL.phaseModel v k_p k_i` of the linearized PLL with feedthrough `D = −1`, whose state matrix
  is the PLL block `[[−k_p v, k_i], [−v, 0]]` of `A₀` (`pllBlock_A_eq_A0`).  Realization:
  state `(ξ, x)` with `ξ = θ + θ_g` the estimated grid angle, input `θ_g` (grid angle),
  output `θ = ξ − θ_g` (PLL error angle); `pllBlock_field` shows this is the linearized PLL
  `θ̇ = −k_p v θ + k_i x − θ̇_g`, `ẋ = −v θ` rewritten in `ξ`.
* `transfer_pllBlock`: its transfer function is `T_PLL(s) = −s² / L_PLL(s)` (`H_pll − 1`,
  `PLL.transfer_phaseModel`), `L_PLL(s) = s² + k_p v s + k_i v` the loop polynomial
  `PLL.loopPoly`.
* Quasi-static PLL closed forms (contrast-conclusions 差别一): the PLL Jacobian
  `[[−k_p S, k_i], [−S, 0]]`, `S = V cos θ > 0`, is `PLL.linA S k_p k_i`, so
  `det(sI − J) = s² + 2ζω_n s + ω_n²` with `ω_n = √(S k_i)`, `ζ = (k_p/2)√(S/k_i)`
  (`PLL.det_characteristicMatrix_linA`, `PLL.loopPoly_eq_standard`, `PLL.zeta_eq`,
  `theorem/GridTiedConverter/PLL/Linear.lean`).
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
open powerlib.NormalForm.BogdanovTakens (proportionalMatrix)

/-- The frozen PLL block as a SISO linear plant (input `θ_g`, output `θ`): the phase model of the
linearized PLL (`PLL.phaseModel`, output `θ̂`) with the feedthrough `−θ_g`. -/
def pllBlock (v kp ki : ℝ) : Linear.Plant 2 1 :=
  { PLL.phaseModel v kp ki with D := !![-1] }

/-- The block matrix is the `(θ, x)` block of the four-state `A₀`. -/
@[tmio M, powerlib_domain] theorem pllBlock_A_eq_A0 (p : FourState.Params) (θ0 : ℝ) (i j : Fin 2) :
    (pllBlock (FourState.vd0 p θ0) p.kp p.ki).A i j =
      FourState.A0 p θ0 (Fin.castLE (by norm_num) i) (Fin.castLE (by norm_num) j) := by
  fin_cases i <;> fin_cases j <;>
    simp [pllBlock, PLL.phaseModel, proportionalMatrix, FourState.A0, mul_comm]

/-- Realization: with `ξ = θ + θ_g`, the block's state equation `A (ξ, x) + B θ_g` is the
linearized PLL and its output `C (ξ, x) + D θ_g` is the error angle `θ`. -/
@[tmio M, powerlib_domain] theorem pllBlock_field (v kp ki θ x θg : ℝ) :
    (pllBlock v kp ki).A *ᵥ ![θ + θg, x] + (pllBlock v kp ki).B *ᵥ ![θg] =
        ![-kp * v * θ + ki * x, -v * θ] ∧
      (pllBlock v kp ki).C *ᵥ ![θ + θg, x] + (pllBlock v kp ki).D *ᵥ ![θg] = ![θ] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [pllBlock, PLL.phaseModel, proportionalMatrix] <;> ring

/-- `T_PLL(s) = −s² / L_PLL(s)`: the closed-loop transfer `H_pll` of the phase model
(`PLL.transfer_phaseModel`) minus the feedthrough `1`. -/
@[tmio M, powerlib_domain] theorem transfer_pllBlock (v kp ki : ℝ) {s : ℂ}
    (hs : PLL.loopPoly v kp ki s ≠ 0) :
    Linear.transfer (pllBlock v kp ki) s 0 0 = -s ^ 2 / PLL.loopPoly v kp ki s := by
  have h : Linear.transfer (pllBlock v kp ki) s =
      Linear.transfer (PLL.phaseModel v kp ki) s + Linear.complexify !![-1] := by
    simp [Linear.transfer, pllBlock, PLL.phaseModel, Linear.complexify]
  rw [h, Matrix.add_apply, PLL.transfer_phaseModel, PLL.closedLoopTF]
  simp [Linear.complexify]
  field_simp
  simp [PLL.loopPoly]
  ring

/-- `|T_PLL(jΩ)| = r²/√((1 − r²)² + 4ζ²r²)` with `r = Ω/ω_pll`. -/
@[tmio M, powerlib_domain] theorem norm_T_jΩ {v kp ki : ℝ} (hkv : 0 < ki * v) (Ω : ℝ) :
    ‖-(Complex.I * Ω) ^ 2 / PLL.loopPoly v kp ki (Complex.I * Ω)‖ =
      (Ω / Real.sqrt (ki * v)) ^ 2 /
        Real.sqrt ((1 - (Ω / Real.sqrt (ki * v)) ^ 2) ^ 2 +
          4 * (kp * v / (2 * Real.sqrt (ki * v))) ^ 2 * (Ω / Real.sqrt (ki * v)) ^ 2) := by
  set w := Real.sqrt (ki * v) with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 hkv
  have hw2 : w ^ 2 = ki * v := Real.sq_sqrt hkv.le
  have hnum : ‖-(Complex.I * (Ω : ℂ)) ^ 2‖ = Ω ^ 2 := by
    rw [norm_neg, mul_pow, Complex.I_sq, norm_mul, norm_neg, norm_one, one_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hden : ‖PLL.loopPoly v kp ki (Complex.I * Ω)‖ =
      Real.sqrt ((ki * v - Ω ^ 2) ^ 2 + (kp * v * Ω) ^ 2) := by
    rw [mul_comm Complex.I, PLL.loopPoly_mul_I, Complex.norm_def, Complex.normSq_mk]
    congr 1
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
@[tmio M, powerlib_domain] theorem normSq_LPLL (v kp ki ω : ℝ) :
    Complex.normSq (PLL.loopPoly v kp ki (2 * Complex.I * ω)) =
      (ki * v - 4 * ω ^ 2) ^ 2 + (2 * ω * kp * v) ^ 2 := by
  rw [show 2 * Complex.I * (ω : ℂ) = ((2 * ω : ℝ) : ℂ) * Complex.I by push_cast; ring,
    PLL.loopPoly_mul_I, Complex.normSq_mk]
  ring

/-- `∂_{k_p} |L_PLL(2jω)|² = 8ω² k_p v²`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_normSq_LPLL (v ki ω kp : ℝ) :
    HasDerivAt (fun kp => Complex.normSq (PLL.loopPoly v kp ki (2 * Complex.I * ω)))
      (8 * ω ^ 2 * kp * v ^ 2) kp := by
  simp only [normSq_LPLL]
  have := ((hasDerivAt_id kp).const_mul (2 * ω)).mul_const v |>.pow 2 |>.const_add
    ((ki * v - 4 * ω ^ 2) ^ 2)
  convert this using 1
  · ext k; simp
  · simp; ring

/-- `|T(2jω)| = 4ω²/|L_PLL(2jω)|` is strictly decreasing in `k_p > 0` (for `ω, v ≠ 0`). -/
@[tmio M, powerlib_domain] theorem norm_T_strictAnti {v ki ω : ℝ} (hω : ω ≠ 0) (hv : v ≠ 0)
    {kp kp' : ℝ} (hkp : 0 < kp) (hlt : kp < kp') :
    ‖-(2 * Complex.I * ω) ^ 2 / PLL.loopPoly v kp' ki (2 * Complex.I * ω)‖ <
      ‖-(2 * Complex.I * ω) ^ 2 / PLL.loopPoly v kp ki (2 * Complex.I * ω)‖ := by
  have hsq : ∀ k, ‖PLL.loopPoly v k ki (2 * Complex.I * ω)‖ ^ 2 =
      (ki * v - 4 * ω ^ 2) ^ 2 + (2 * ω * k * v) ^ 2 := by
    intro k; rw [← Complex.normSq_eq_norm_sq, normSq_LPLL]
  have hsqpos : 0 < ‖PLL.loopPoly v kp ki (2 * Complex.I * ω)‖ ^ 2 := by
    rw [hsq]; have : 0 < (2 * ω * kp * v) ^ 2 := by positivity
    positivity
  have hpos : 0 < ‖PLL.loopPoly v kp ki (2 * Complex.I * ω)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hsqpos
    simp at hsqpos
  have hlt2 : ‖PLL.loopPoly v kp ki (2 * Complex.I * ω)‖ ^ 2 <
      ‖PLL.loopPoly v kp' ki (2 * Complex.I * ω)‖ ^ 2 := by
    rw [hsq, hsq]
    have h1 : 0 < (2 * ω * v) ^ 2 := by positivity
    have h2 : kp ^ 2 < kp' ^ 2 := by nlinarith
    have e : ∀ k : ℝ, (2 * ω * k * v) ^ 2 = (2 * ω * v) ^ 2 * k ^ 2 := fun k => by ring
    rw [e, e]
    nlinarith [mul_lt_mul_of_pos_left h2 h1]
  have hlt : ‖PLL.loopPoly v kp ki (2 * Complex.I * ω)‖ <
      ‖PLL.loopPoly v kp' ki (2 * Complex.I * ω)‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt2
  have hnum : 0 < ‖-(2 * Complex.I * (ω : ℂ)) ^ 2‖ := by
    rw [norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real]
    have : 0 < ‖ω‖ := norm_pos_iff.2 hω
    norm_num
    positivity
  rw [norm_div, norm_div]
  exact div_lt_div_of_pos_left hnum hpos hlt

end powerlib.GFL.Parametric.PLLBlock
