import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SPH
import theorem.GridTiedConverter.PLL.StochasticPH
import theorem.GridTiedConverter.PLL.PIPLLPH
import theorem.PH.Nonlinear
import theorem.GridTiedConverter.GFL.LCLine.Reduction

/-! # SPHS embedding of the reduced 2D GFL–PLL equation: port geometry and the generator

Model boundary.
State `x = (θ_e, η)` (index `0` = PLL phase error, `1` = PI integrator state)
of the reduced 2D slow model (form B / 2D-CP layer, inner loops frozen, rigid DC link in the
`(h, σ_v)` reading).  `h : ℝ → ℝ` is the reduced phase-detector characteristic, `𝒱' = −h`,
`𝓗 = ½ K_i η² + 𝒱(θ_e)`.  Drift `f = (K_p h + K_i η, h)`.  Noise matrix (one state, white-noise
idealization): voltage columns `σ_d (K_p, 1)ᵀ` (amplitude) and `g (K_p, 1)ᵀ` (phase, per unit
phase), frequency column `(−ε, 0)ᵀ`.  All statements are algebraic identities at one state
(gradient `g = ∇𝓗(x)`, Hessian `K = ∇²𝓗(x) = diag(𝒱'', K_i)`), domain model identities
only (Rules §3): no SDE solution, stationary density or escape statement is made here.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/sphs-embedding.md` §2 (Itô
form, `h_noise` with columns `(d, q, ω)`), §2b (invariant noise coordinates: rank-1 voltage block
`(K_p, 1)ᵀ(σ_d, g)` plus the transverse frequency column `(−1, 0)ᵀ`; per-channel FDT), §3
(`𝓛𝓗 = −K_p h² + Δ_Itô`, sign correction), §4 (port split); and
`escape-quasipotential.md` §0 (constant-structure pH form `ẋ = (J − R)∇𝓗`,
`J = [[0, 1], [−1, 0]]`, `R = diag(K_p, 0)`).

Results.
* `embDrift_eq_pH`, `embDrift_dot_grad`: the drift is the pH field `(J − R)∇𝓗` of the PI-PLL,
  with its skew `J = PLL.pllJ = [[0, 1], [−1, 0]]` (skew by `PH.transpose_symplectic_two`) and
  `R = PLL.pllR K_p ⪰ 0` (`PLL.pllR_posSemidef`, `K_p ≥ 0`); the frequency column is
  `ε` times the PLL input port `PLL.pllB` (`theorem/GridTiedConverter/PLL/PIPLLPH.lean`).
* `voltageBlock_eq_vecMulVec`, `voltageBlock_det`, `voltageBlock_rank_le`: the voltage block, the
  PLL voltage coupling `PLL.StochasticPH.pllNoise K_p (σ_d, g)`, is the rank-one matrix
  `(K_p, 1)ᵀ(σ_d, g)`; the frequency column `freqNoise` is the sparse column
  `Synchronous.SM.sparseNoise` and the full port `embNoise` is `PLL.StochasticPH.pllNoiseFreq`.
* `freqNoise_fdt`: the frequency channel satisfies `B Bᵀ = 2 T_eff R`, `T_eff = ε²/(2K_p)`
  (exact FDT); `voltage_alignment`, `voltage_alignment_lt_one`, `freq_alignment`: the voltage
  channel is structurally non-FDT (normalized alignment `K_p²/(1 + K_p²) < 1` with `R`), the
  frequency column has alignment one.
* `ito_emb`, `genL_emb`: the Itô correction (read from `PLL.StochasticPH.pllIto_freq`)
  `Δ_Itô = ½ (σ_d² + g²)(K_p² 𝒱'' + K_i) + ½ ε² 𝒱''` (frequency channel only, `σ_d = g = 0`:
  `½ ε² 𝒱''`) and the generator `𝓛𝓗 = −K_p h² + Δ_Itô` (the generic stochastic-pH balance
  `Stochastic.SPH.genL_pH` with no control port).
* `ito_emb_neg_iff`, `ito_emb_sign_indefinite`: the sign of `Δ_Itô` (Correction below).
* `gflIto`: the form-B voltage channel, the noise row `σ_v(θ_e)` of the quasi-steady reduction
  (`GFL.LCLine.Network.sigmaV`, `theorem/GridTiedConverter/GFL/LCLine/Reduction.lean`), gives
  `Δ_Itô = ½ (K_p² 𝒱'' + K_i)/Δ` (T-gfl-sph §1.1–§1.3).

Correction (sphs-embedding §3, already noted there on 2026-08-13).  `Δ_Itô` is **not** a
nonnegative function: it is affine in `𝒱''(θ_e)` with positive slope, hence negative wherever
`𝒱''` is negative enough (`ito_emb_neg_iff`, `ito_emb_sign_indefinite`); with the frequency
channel only it equals `½ ε² 𝒱''`, negative on the saddle side.
-/

noncomputable section
namespace powerlib.GFL.Noise.Embed

open Matrix
open powerlib.Stochastic.SPH powerlib.PLL.StochasticPH
open powerlib.PLL (pllJ pllR)

/-! ## Constant-structure pH form

The interconnection and dissipation are those of the PI-PLL, `PLL.pllJ = [[0, 1], [−1, 0]]` and
`PLL.pllR K_p = diag(K_p, 0)` (proportional path). -/

/-- Gradient `∇𝓗 = (𝒱'(θ_e), K_i η) = (−h(θ_e), K_i η)`. -/
def embGrad (Ki hθ η : ℝ) : Fin 2 → ℝ := ![-hθ, Ki * η]

/-- Drift `f = (K_p h + K_i η, h)` of the 2D slow model. -/
def embDrift (Kp Ki hθ η : ℝ) : Fin 2 → ℝ := ![Kp * hθ + Ki * η, hθ]

/-- The drift is the pH vector field `(J − R)∇𝓗` (escape-quasipotential §0). -/
@[tmio M, powerlib_domain] theorem embDrift_eq_pH (Kp Ki hθ η : ℝ) :
    embDrift Kp Ki hθ η = (pllJ - pllR Kp) *ᵥ embGrad Ki hθ η := by
  ext i; fin_cases i <;> simp [embDrift, pllJ, pllR, embGrad, mulVec, dotProduct,
    Fin.sum_univ_two]

/-- Power balance of the drift: `f ⬝ ∇𝓗 = −K_p h²`. -/
@[tmio M, powerlib_domain] theorem embDrift_dot_grad (Kp Ki hθ η : ℝ) :
    embDrift Kp Ki hθ η ⬝ᵥ embGrad Ki hθ η = -(Kp * hθ ^ 2) := by
  simp [embDrift, embGrad, dotProduct, Fin.sum_univ_two]; ring

/-! ## Noise ports (§2b) -/

/-- Voltage block in invariant coordinates: columns `σ_d (K_p, 1)ᵀ`, `g (K_p, 1)ᵀ`, the PLL
voltage-noise coupling `PLL.StochasticPH.pllNoise K_p σ_v` with the row `σ_v = (σ_d, g)`. -/
abbrev voltageBlock (Kp σd g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := pllNoise Kp ![σd, g]

/-- The voltage block is the outer product `(K_p, 1)ᵀ (σ_d, g)`. -/
@[tmio M, powerlib_domain] theorem voltageBlock_eq_vecMulVec (Kp σd g : ℝ) :
    voltageBlock Kp σd g = vecMulVec ![Kp, 1] ![σd, g] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pllNoise, vecMulVec]

/-- **Rank one**: the two voltage columns are parallel, the block is singular ... -/
@[tmio M, powerlib_domain] theorem voltageBlock_det (Kp σd g : ℝ) :
    (voltageBlock Kp σd g).det = 0 := by
  rw [voltageBlock, pllNoise, det_fin_two_of]; ring

/-- ... and has rank at most one. -/
@[tmio M, powerlib_domain] theorem voltageBlock_rank_le (Kp σd g : ℝ) :
    (voltageBlock Kp σd g).rank ≤ 1 := by
  rw [voltageBlock_eq_vecMulVec]; exact rank_vecMulVec_le _ _

/-- Full noise matrix `[σ_d(K_p,1)ᵀ | g(K_p,1)ᵀ | (−ε, 0)ᵀ]` (columns: amplitude, phase,
frequency): the PLL port with the frequency channel, `PLL.StochasticPH.pllNoiseFreq K_p (σ_d, g)
(−ε)`, its column index `Fin 2 ⊕ Fin 1` read as `Fin 3`. -/
def embNoise (Kp σd g ε : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  (pllNoiseFreq Kp ![σd, g] (-ε)).submatrix id (finSumFinEquiv (m := 2) (n := 1)).symm

/-- Frequency column alone, the sparse column `Synchronous.SM.sparseNoise` on `θ_e`. -/
abbrev freqNoise (ε : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := Synchronous.SM.sparseNoise ![0] ![-ε]

/-- **Frequency channel FDT (exact)**: `B Bᵀ = 2 T_eff R` with `T_eff = ε²/(2K_p)`. -/
@[tmio M, powerlib_domain] theorem freqNoise_fdt {Kp : ℝ} (hKp : Kp ≠ 0) (ε : ℝ) :
    freqNoise ε * (freqNoise ε)ᵀ = (2 * (ε ^ 2 / (2 * Kp))) • pllR Kp := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Synchronous.SM.sparseNoise, pllR, Matrix.mul_apply]
  field_simp

/-- Frobenius inner product `⟨A, B⟩ = tr(Aᵀ B)`. -/
def frobInner (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (Aᵀ * B).trace

/-- **Voltage channel is structurally non-FDT**: the normalized inner product of `v vᵀ` with `R`
is the constant `K_p²/(1 + K_p²)` (independent of `σ_d`, `g`), never `1` (`K_p > 0`). -/
@[tmio M, powerlib_domain] theorem voltage_alignment {Kp σd g : ℝ} (hKp : 0 < Kp)
    (hs : σd ^ 2 + g ^ 2 ≠ 0) :
    frobInner (voltageBlock Kp σd g * (voltageBlock Kp σd g)ᵀ) (pllR Kp) /
        (Real.sqrt (frobInner (voltageBlock Kp σd g * (voltageBlock Kp σd g)ᵀ)
            (voltageBlock Kp σd g * (voltageBlock Kp σd g)ᵀ)) *
          Real.sqrt (frobInner (pllR Kp) (pllR Kp))) = Kp ^ 2 / (1 + Kp ^ 2) := by
  have hs' : 0 < σd ^ 2 + g ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
  rw [pllNoise_mul_transpose, show ![σd, g] ⬝ᵥ ![σd, g] = σd ^ 2 + g ^ 2 by simp [dotProduct, sq]]
  have h1 : frobInner ((σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1]) (pllR Kp) =
      (σd ^ 2 + g ^ 2) * Kp ^ 3 := by
    simp [frobInner, pllR, Matrix.trace_fin_two]; ring
  have h2 : frobInner ((σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1])
      ((σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1]) = ((σd ^ 2 + g ^ 2) * (1 + Kp ^ 2)) ^ 2 := by
    simp [frobInner, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h3 : frobInner (pllR Kp) (pllR Kp) = Kp ^ 2 := by
    simp [frobInner, pllR]; ring
  rw [h1, h2, h3, Real.sqrt_sq (by positivity), Real.sqrt_sq hKp.le]
  field_simp

/-- The voltage alignment is strictly below one, i.e. `v vᵀ` is never proportional to `R`. -/
@[tmio T, powerlib_foundation] theorem voltage_alignment_lt_one (Kp : ℝ) :
    Kp ^ 2 / (1 + Kp ^ 2) < 1 := by
  rw [div_lt_one (by positivity)]; linarith

/-- The frequency column has alignment exactly one with `R`. -/
@[tmio M, powerlib_domain] theorem freq_alignment {Kp ε : ℝ} (hKp : 0 < Kp) (hε : ε ≠ 0) :
    frobInner (freqNoise ε * (freqNoise ε)ᵀ) (pllR Kp) /
        (Real.sqrt (frobInner (freqNoise ε * (freqNoise ε)ᵀ) (freqNoise ε * (freqNoise ε)ᵀ)) *
          Real.sqrt (frobInner (pllR Kp) (pllR Kp))) = 1 := by
  have e : freqNoise ε * (freqNoise ε)ᵀ = !![ε ^ 2, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Synchronous.SM.sparseNoise, Matrix.mul_apply]
    ring
  rw [e]
  have h1 : frobInner !![ε ^ 2, 0; 0, 0] (pllR Kp) = ε ^ 2 * Kp := by
    simp [frobInner, pllR, Matrix.trace_fin_two]
  have h2 : frobInner !![ε ^ 2, 0; 0, 0] !![ε ^ 2, 0; 0, 0] = (ε ^ 2) ^ 2 := by
    simp [frobInner, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h3 : frobInner (pllR Kp) (pllR Kp) = Kp ^ 2 := by
    simp [frobInner, pllR]; ring
  have hε2 : 0 < ε ^ 2 := by positivity
  rw [h1, h2, h3, Real.sqrt_sq hε2.le, Real.sqrt_sq hKp.le]
  field_simp

/-! ## Generator of `𝓗` (§3) -/

/-- **Itô correction of the embedding**:
`Δ_Itô = ½ (σ_d² + g²)(K_p² 𝒱'' + K_i) + ½ ε² 𝒱''`, the PLL correction with the frequency
channel (`PLL.StochasticPH.pllIto_freq`, `pllIto`; the column order does not matter). -/
@[tmio M, powerlib_domain] theorem ito_emb (Kp Ki σd g ε V2 : ℝ) :
    itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) =
      (1 / 2 : ℝ) * (σd ^ 2 + g ^ 2) * (Kp ^ 2 * V2 + Ki) + (1 / 2 : ℝ) * ε ^ 2 * V2 := by
  have h : itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) =
      itoCorrection (pllNoiseFreq Kp ![σd, g] (-ε)) (pllHess V2 Ki) := by
    unfold itoCorrection
    rw [embNoise, transpose_submatrix, submatrix_mul_equiv, submatrix_id_id]
  rw [h, pllIto_freq, pllIto, show ![σd, g] ⬝ᵥ ![σd, g] = σd ^ 2 + g ^ 2 by simp [dotProduct, sq]]
  ring

/-- **Generator identity (§3)**: `𝓛𝓗 = f ⬝ ∇𝓗 + ½ tr(h hᵀ ∇²𝓗) = −K_p h² + Δ_Itô`. -/
@[tmio M, powerlib_domain] theorem genL_emb (Kp Ki σd g ε hθ η V2 : ℝ) :
    genL (embDrift Kp Ki hθ η) (embNoise Kp σd g ε) (embGrad Ki hθ η) (pllHess V2 Ki) =
      -(Kp * hθ ^ 2) + itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) := by
  unfold genL; rw [embDrift_dot_grad]

/-- **Form-B Itô correction** (T-gfl-sph §1.1–§1.3): with the EMF noise row `σ_v(θ_e)` of the
quasi-steady reduction (`GFL.LCLine.Network.sigmaV`, `hE_noise_split`), whose squared norm is
`1/Δ` at every angle (`sigmaV_dot_self`), `Δ_Itô = ½ (K_p² 𝒱'' + K_i)/Δ`. -/
@[tmio M, powerlib_domain] theorem gflIto (p : LCLine.Network) (hΔ : p.Δ ≠ 0) (Kp Ki V2 θ : ℝ) :
    itoCorrection (pllNoise Kp (p.sigmaV θ)) (pllHess V2 Ki) =
      (1 / 2 : ℝ) * (Kp ^ 2 * V2 + Ki) / p.Δ := by
  rw [pllIto, p.sigmaV_dot_self hΔ]
  ring

/-- **Correction (sign)**: `Δ_Itô < 0 ⇔ 𝒱'' < −(σ_d² + g²) K_i / ((σ_d² + g²) K_p² + ε²)`
whenever some noise acts (`(σ_d² + g²) K_p² + ε² > 0`). -/
@[tmio M, powerlib_domain] theorem ito_emb_neg_iff {Kp Ki σd g ε V2 : ℝ}
    (hpos : 0 < (σd ^ 2 + g ^ 2) * Kp ^ 2 + ε ^ 2) :
    itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) < 0 ↔
      V2 < -((σd ^ 2 + g ^ 2) * Ki) / ((σd ^ 2 + g ^ 2) * Kp ^ 2 + ε ^ 2) := by
  rw [ito_emb, lt_div_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

/-- `Δ_Itô` takes both signs as `𝒱''` varies (for any nonzero noise): it is sign-indefinite. -/
@[tmio M, powerlib_domain] theorem ito_emb_sign_indefinite {Kp Ki σd g ε : ℝ}
    (hpos : 0 < (σd ^ 2 + g ^ 2) * Kp ^ 2 + ε ^ 2) :
    ∃ V2 V2' : ℝ, itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) < 0 ∧
      0 < itoCorrection (embNoise Kp σd g ε) (pllHess V2' Ki) := by
  set c := (σd ^ 2 + g ^ 2) * Kp ^ 2 + ε ^ 2
  have hs : 0 ≤ σd ^ 2 + g ^ 2 := by positivity
  refine ⟨-((σd ^ 2 + g ^ 2) * |Ki| + 1) / c, ((σd ^ 2 + g ^ 2) * |Ki| + 1) / c, ?_, ?_⟩
  · rw [ito_emb]
    have key : (1 / 2 : ℝ) * (σd ^ 2 + g ^ 2) * (Kp ^ 2 * (-((σd ^ 2 + g ^ 2) * |Ki| + 1) / c) + Ki)
        + (1 / 2 : ℝ) * ε ^ 2 * (-((σd ^ 2 + g ^ 2) * |Ki| + 1) / c) =
        (1 / 2 : ℝ) * ((σd ^ 2 + g ^ 2) * Ki - ((σd ^ 2 + g ^ 2) * |Ki| + 1)) := by
      field_simp; ring
    rw [key]
    have : (σd ^ 2 + g ^ 2) * Ki ≤ (σd ^ 2 + g ^ 2) * |Ki| :=
      mul_le_mul_of_nonneg_left (le_abs_self Ki) hs
    linarith
  · rw [ito_emb]
    have key : (1 / 2 : ℝ) * (σd ^ 2 + g ^ 2) * (Kp ^ 2 * (((σd ^ 2 + g ^ 2) * |Ki| + 1) / c) + Ki)
        + (1 / 2 : ℝ) * ε ^ 2 * (((σd ^ 2 + g ^ 2) * |Ki| + 1) / c) =
        (1 / 2 : ℝ) * ((σd ^ 2 + g ^ 2) * Ki + ((σd ^ 2 + g ^ 2) * |Ki| + 1)) := by
      field_simp; ring
    rw [key]
    have : -((σd ^ 2 + g ^ 2) * |Ki|) ≤ (σd ^ 2 + g ^ 2) * Ki := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le Ki) hs
      linarith
    linarith

end powerlib.GFL.Noise.Embed
