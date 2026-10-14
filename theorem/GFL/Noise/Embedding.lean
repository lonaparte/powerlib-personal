import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SPH
import theorem.PLL.StochasticPH

/-! # SPHS embedding of the reduced 2D GFL–PLL equation: port geometry and the generator

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/sphs-embedding.md` §2 (Itô
form, `h_noise` with columns `(d, q, ω)`), §2b (invariant noise coordinates: rank-1 voltage block
`(K_p, 1)ᵀ(σ_d, g)` plus the transverse frequency column `(−1, 0)ᵀ`; per-channel FDT), §3
(`𝓛𝓗 = −K_p h² + Δ_Itô`, sign correction), §4 (port split); and
`escape-quasipotential.md` §0 (constant-structure pH form `ẋ = (J − R)∇𝓗`,
`J = [[0, 1], [−1, 0]]`, `R = diag(K_p, 0)`).

Model boundary.  State `x = (θ_e, η)` (index `0` = PLL phase error, `1` = PI integrator state)
of the reduced 2D slow model (form B / 2D-CP layer, inner loops frozen, rigid DC link in the
`(h, σ_v)` reading).  `h : ℝ → ℝ` is the reduced phase-detector characteristic, `𝒱' = −h`,
`𝓗 = ½ K_i η² + 𝒱(θ_e)`.  Drift `f = (K_p h + K_i η, h)`.  Noise matrix (one state, white-noise
idealization): voltage columns `σ_d (K_p, 1)ᵀ` (amplitude) and `g (K_p, 1)ᵀ` (phase, per unit
phase), frequency column `(−ε, 0)ᵀ`.  All statements are algebraic identities at one state
(gradient `g = ∇𝓗(x)`, Hessian `K = ∇²𝓗(x) = diag(𝒱'', K_i)`), foundation only (Rules §3): no SDE
solution, stationary density or escape statement is made here.

Correction (sphs-embedding §3, already noted there on 2026-08-13).  `Δ_Itô` is **not** a
nonnegative function: it is affine in `𝒱''(θ_e)` with positive slope, hence negative wherever
`𝒱''` is negative enough (`ito_emb_neg_iff`, `ito_emb_sign_indefinite`); with the frequency
channel only it equals `½ ε² 𝒱''`, negative on the saddle side.
-/

noncomputable section
namespace powerlib.GFL.Noise.Embed

open Matrix
open powerlib.Stochastic.SPH powerlib.PLL.StochasticPH

/-! ## Constant-structure pH form -/

/-- Interconnection `J = [[0, 1], [−1, 0]]`. -/
def embJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Dissipation `R = diag(K_p, 0)` (PLL proportional path). -/
def embR (Kp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Kp, 0; 0, 0]

/-- Gradient `∇𝓗 = (𝒱'(θ_e), K_i η) = (−h(θ_e), K_i η)`. -/
def embGrad (Ki hθ η : ℝ) : Fin 2 → ℝ := ![-hθ, Ki * η]

/-- Drift `f = (K_p h + K_i η, h)` of the 2D slow model. -/
def embDrift (Kp Ki hθ η : ℝ) : Fin 2 → ℝ := ![Kp * hθ + Ki * η, hθ]

@[powerlib_foundation] theorem embJ_skew : embJᵀ = -embJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [embJ]

@[powerlib_foundation] theorem embR_posSemidef {Kp : ℝ} (hKp : 0 ≤ Kp) : (embR Kp).PosSemidef := by
  have : embR Kp = Matrix.diagonal ![Kp, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [embR]
  rw [this, Matrix.posSemidef_diagonal_iff]
  intro i; fin_cases i <;> simp [hKp]

/-- The drift is the pH vector field `(J − R)∇𝓗` (escape-quasipotential §0). -/
@[powerlib_foundation] theorem embDrift_eq_pH (Kp Ki hθ η : ℝ) :
    embDrift Kp Ki hθ η = (embJ - embR Kp) *ᵥ embGrad Ki hθ η := by
  ext i; fin_cases i <;> simp [embDrift, embJ, embR, embGrad, mulVec, dotProduct,
    Fin.sum_univ_two]

/-- Power balance of the drift: `f ⬝ ∇𝓗 = −K_p h²`. -/
@[powerlib_foundation] theorem embDrift_dot_grad (Kp Ki hθ η : ℝ) :
    embDrift Kp Ki hθ η ⬝ᵥ embGrad Ki hθ η = -(Kp * hθ ^ 2) := by
  simp [embDrift, embGrad, dotProduct, Fin.sum_univ_two]; ring

/-! ## Noise ports (§2b) -/

/-- Voltage block in invariant coordinates: columns `σ_d (K_p, 1)ᵀ`, `g (K_p, 1)ᵀ`. -/
def voltageBlock (Kp σd g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Kp * σd, Kp * g; σd, g]

/-- The voltage block is the outer product `(K_p, 1)ᵀ (σ_d, g)`. -/
@[powerlib_foundation] theorem voltageBlock_eq_vecMulVec (Kp σd g : ℝ) :
    voltageBlock Kp σd g = vecMulVec ![Kp, 1] ![σd, g] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [voltageBlock, vecMulVec]

/-- **Rank one**: the two voltage columns are parallel, the block is singular ... -/
@[powerlib_foundation] theorem voltageBlock_det (Kp σd g : ℝ) : (voltageBlock Kp σd g).det = 0 := by
  rw [voltageBlock, det_fin_two_of]; ring

/-- ... and has rank at most one. -/
@[powerlib_foundation] theorem voltageBlock_rank_le (Kp σd g : ℝ) :
    (voltageBlock Kp σd g).rank ≤ 1 := by
  rw [voltageBlock_eq_vecMulVec]; exact rank_vecMulVec_le _ _

/-- Full noise matrix `[σ_d(K_p,1)ᵀ | g(K_p,1)ᵀ | (−ε, 0)ᵀ]` (columns: amplitude, phase,
frequency). -/
def embNoise (Kp σd g ε : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![Kp * σd, Kp * g, -ε; σd, g, 0]

/-- Frequency column alone. -/
def freqNoise (ε : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![-ε; 0]

/-- **Frequency channel FDT (exact)**: `B Bᵀ = 2 T_eff R` with `T_eff = ε²/(2K_p)`. -/
@[powerlib_foundation] theorem freqNoise_fdt {Kp : ℝ} (hKp : Kp ≠ 0) (ε : ℝ) :
    freqNoise ε * (freqNoise ε)ᵀ = (2 * (ε ^ 2 / (2 * Kp))) • embR Kp := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [freqNoise, embR, Matrix.mul_apply]
  field_simp

/-- Voltage covariance `v vᵀ = (σ_d² + g²) [[K_p², K_p], [K_p, 1]]`. -/
@[powerlib_foundation] theorem voltageBlock_mul_transpose (Kp σd g : ℝ) :
    voltageBlock Kp σd g * (voltageBlock Kp σd g)ᵀ = (σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [voltageBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Frobenius inner product `⟨A, B⟩ = tr(Aᵀ B)`. -/
def frobInner (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (Aᵀ * B).trace

/-- **Voltage channel is structurally non-FDT**: the normalized inner product of `v vᵀ` with `R`
is the constant `K_p²/(1 + K_p²)` (independent of `σ_d`, `g`), never `1` (`K_p > 0`). -/
@[powerlib_foundation] theorem voltage_alignment {Kp σd g : ℝ} (hKp : 0 < Kp)
    (hs : σd ^ 2 + g ^ 2 ≠ 0) :
    frobInner (voltageBlock Kp σd g * (voltageBlock Kp σd g)ᵀ) (embR Kp) /
        (Real.sqrt (frobInner (voltageBlock Kp σd g * (voltageBlock Kp σd g)ᵀ)
            (voltageBlock Kp σd g * (voltageBlock Kp σd g)ᵀ)) *
          Real.sqrt (frobInner (embR Kp) (embR Kp))) = Kp ^ 2 / (1 + Kp ^ 2) := by
  have hs' : 0 < σd ^ 2 + g ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
  rw [voltageBlock_mul_transpose]
  have h1 : frobInner ((σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1]) (embR Kp) =
      (σd ^ 2 + g ^ 2) * Kp ^ 3 := by
    simp [frobInner, embR, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h2 : frobInner ((σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1])
      ((σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1]) = ((σd ^ 2 + g ^ 2) * (1 + Kp ^ 2)) ^ 2 := by
    simp [frobInner, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h3 : frobInner (embR Kp) (embR Kp) = Kp ^ 2 := by
    simp [frobInner, embR, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  rw [h1, h2, h3, Real.sqrt_sq (by positivity), Real.sqrt_sq hKp.le]
  field_simp

/-- The voltage alignment is strictly below one, i.e. `v vᵀ` is never proportional to `R`. -/
@[powerlib_foundation] theorem voltage_alignment_lt_one (Kp : ℝ) :
    Kp ^ 2 / (1 + Kp ^ 2) < 1 := by
  rw [div_lt_one (by positivity)]; linarith

/-- The frequency column has alignment exactly one with `R`. -/
@[powerlib_foundation] theorem freq_alignment {Kp ε : ℝ} (hKp : 0 < Kp) (hε : ε ≠ 0) :
    frobInner (freqNoise ε * (freqNoise ε)ᵀ) (embR Kp) /
        (Real.sqrt (frobInner (freqNoise ε * (freqNoise ε)ᵀ) (freqNoise ε * (freqNoise ε)ᵀ)) *
          Real.sqrt (frobInner (embR Kp) (embR Kp))) = 1 := by
  have e : freqNoise ε * (freqNoise ε)ᵀ = !![ε ^ 2, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [freqNoise, Matrix.mul_apply]; ring
  rw [e]
  have h1 : frobInner !![ε ^ 2, 0; 0, 0] (embR Kp) = ε ^ 2 * Kp := by
    simp [frobInner, embR, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : frobInner !![ε ^ 2, 0; 0, 0] !![ε ^ 2, 0; 0, 0] = (ε ^ 2) ^ 2 := by
    simp [frobInner, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h3 : frobInner (embR Kp) (embR Kp) = Kp ^ 2 := by
    simp [frobInner, embR, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hε2 : 0 < ε ^ 2 := by positivity
  rw [h1, h2, h3, Real.sqrt_sq hε2.le, Real.sqrt_sq hKp.le]
  field_simp

/-! ## Generator of `𝓗` (§3) -/

/-- `h_noise h_noiseᵀ` of the full port: voltage part plus `diag(ε², 0)`. -/
@[powerlib_foundation] theorem embNoise_mul_transpose (Kp σd g ε : ℝ) :
    embNoise Kp σd g ε * (embNoise Kp σd g ε)ᵀ =
      (σd ^ 2 + g ^ 2) • !![Kp ^ 2, Kp; Kp, 1] + !![ε ^ 2, 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [embNoise, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- **Itô correction of the embedding**:
`Δ_Itô = ½ (σ_d² + g²)(K_p² 𝒱'' + K_i) + ½ ε² 𝒱''`. -/
@[powerlib_foundation] theorem ito_emb (Kp Ki σd g ε V2 : ℝ) :
    itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) =
      (1 / 2 : ℝ) * (σd ^ 2 + g ^ 2) * (Kp ^ 2 * V2 + Ki) + (1 / 2 : ℝ) * ε ^ 2 * V2 := by
  unfold itoCorrection
  rw [embNoise_mul_transpose]
  simp [pllHess, Matrix.trace_fin_two]
  ring

/-- **Generator identity (§3)**: `𝓛𝓗 = f ⬝ ∇𝓗 + ½ tr(h hᵀ ∇²𝓗) = −K_p h² + Δ_Itô`. -/
@[powerlib_foundation] theorem genL_emb (Kp Ki σd g ε hθ η V2 : ℝ) :
    genL (embDrift Kp Ki hθ η) (embNoise Kp σd g ε) (embGrad Ki hθ η) (pllHess V2 Ki) =
      -(Kp * hθ ^ 2) + itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) := by
  unfold genL; rw [embDrift_dot_grad]

/-- The same identity through the generic stochastic-pH balance `genL_pH` (no control port). -/
@[powerlib_foundation] theorem genL_emb_pH (Kp Ki σd g ε hθ η V2 : ℝ) :
    genL ((embJ - embR Kp) *ᵥ embGrad Ki hθ η + (0 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ 0)
        (embNoise Kp σd g ε) (embGrad Ki hθ η) (pllHess V2 Ki) =
      -(embGrad Ki hθ η ⬝ᵥ (embR Kp *ᵥ embGrad Ki hθ η)) +
        itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) := by
  rw [genL_pH embJ_skew]
  simp

/-- Frequency channel only: `Δ_Itô = ½ ε² 𝒱''` (negative on the saddle side `𝒱'' < 0`). -/
@[powerlib_foundation] theorem ito_freq_only (Kp Ki ε V2 : ℝ) :
    itoCorrection (embNoise Kp 0 0 ε) (pllHess V2 Ki) = (1 / 2 : ℝ) * ε ^ 2 * V2 := by
  rw [ito_emb]; ring

/-- **Correction (sign)**: `Δ_Itô < 0 ⇔ 𝒱'' < −(σ_d² + g²) K_i / ((σ_d² + g²) K_p² + ε²)`
whenever some noise acts (`(σ_d² + g²) K_p² + ε² > 0`). -/
@[powerlib_foundation] theorem ito_emb_neg_iff {Kp Ki σd g ε V2 : ℝ}
    (hpos : 0 < (σd ^ 2 + g ^ 2) * Kp ^ 2 + ε ^ 2) :
    itoCorrection (embNoise Kp σd g ε) (pllHess V2 Ki) < 0 ↔
      V2 < -((σd ^ 2 + g ^ 2) * Ki) / ((σd ^ 2 + g ^ 2) * Kp ^ 2 + ε ^ 2) := by
  rw [ito_emb, lt_div_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

/-- `Δ_Itô` takes both signs as `𝒱''` varies (for any nonzero noise): it is sign-indefinite. -/
@[powerlib_foundation] theorem ito_emb_sign_indefinite {Kp Ki σd g ε : ℝ}
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
