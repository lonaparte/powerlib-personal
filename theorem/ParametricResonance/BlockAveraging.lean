import theorem.ParametricResonance.TwoToOneAveraging
import theorem.LTI.Discrete
import theorem.Linear.EigenMap

/-! # First-order averaging with a stable remainder: Floquet multipliers of `n`-state cores

The 2:1 criterion of the source rests on first-order averaging of the variational equation
`ẋ = (A₀ + ε Re{A₁ e^{jωt}}) x`. `TwoToOneAveraging` proves it for two states. Here the state has
a critical pair and an arbitrary stable remainder (the 3- to 6-state cores of droop, VSG, PSC,
dVOC and matching): when the slow flow of the pair is exponentially stable, every Floquet
multiplier of the complete system is inside the unit circle for all small `ε > 0`; when the slow
flow has a positive real exponent (the parametric resonance tongue), the complete system has a
real multiplier below `−1`. Every non-resonant term and every coupling through the stable block is
kept.

Scope.
* States `Fin 2 ⊕ Y`: the critical pair `−εs ± j(ω/2 − εd)` in real modal form on `Fin 2`
  (`TwoToOne.base`), decoupled in `A₀` from a stable block `A_s` on `Y`; an arbitrary complex
  modulation `A₁` coupling all states (`modN`, `fullN`). A constant real similarity brings every
  `A₀` with a simple non-real pair to this block form; it changes neither the Floquet multipliers
  nor the pump coefficient (`Element.pump_similar`).
* The stable block enters through the spectral radius `ρ(e^{TA_s}) < 1`, `T = 2π/ω` (`expS`):
  every eigenvalue of the one-period map of the stable modes lies inside the unit circle. The
  condition does not depend on the basis of the stable subspace; no norm of `e^{TA_s}` is
  assumed (`StableBlockNorm` shows a norm condition can fail in every real basis).
* The pump coefficient is `g = u A₁₁ r̄` (`Element.pump`, `TwoToOne.left`, `TwoToOne.right`) of
  the critical block of `A₁` only.
* The scaling `σ = εs`, `ω/2 − Ω = εd` is the distinguished limit of `TwoToOneAveraging`; the
  statements hold for all sufficiently small `ε > 0`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}`, `g_m = l_mᴴ A₁ r_m*`,
"一阶平均给出 …"), applied there to the cores of §3; [8, 9] of that report (Nayfeh–Mook,
Yakubovich–Starzhinskii).

Results.
* Frame: `Ψ(t) = diag(R(ωt/2), e^{tA_s})` (`Psi`, `hasDerivAt_psi`, `psi_mul_inv`) turns the
  system into the standard form `ż = ε F_z(t) z` (`Fz`, `psi_frame`); on `[0, T]` the transition
  matrix is `Ψ(t)` times that of the standard form frozen outside `[0, T]` (`Fzc`,
  `transition_fullN`).
* Average: the critical block of `(1/T)∫₀ᵀ F_z` is the slow-flow matrix
  `M_slow(s, d, g/2)` (`Fz_toBlocks₁₁`, `average_toBlocks₁₁`).
* `monodromy_blocks` — the monodromy is `[[P, Q], [R, S]]` with
  `P = −(I + εT M_slow) + O(ε²)`, `Q, R = O(ε)`, `S = e^{TA_s} + O(ε)`
  (`Averaging.monodromy_expansion`, `norm_toBlocks_le`).
* Spectral condition through odd powers: `exists_odd_pow_norm_lt_one` (Gelfand: `ρ(E) < 1` gives
  an odd `n` with `‖Eⁿ‖ < 1`), `block_pow_id11`, `block_pow_estimate` (the `n`-th power of the
  block monodromy has critical block `(−1)ⁿ(I + εnT M_slow) + O(ε²)` and stable block
  `Sⁿ = Eⁿ + O(ε)`), `odd_block_identity`, `Linear.mulVec_pow_of_eigen`;
  `block_stable_spec`, `block_unstable_spec` — the conclusions of `block_stable` and
  `block_unstable` under `ρ(E) < 1`; `spectralRadius_lt_one_of_norm` — the earlier norm
  condition is a special case.
* `block_stable` — eigenvalues of such block matrices with `M_slow` Hurwitz lie inside the unit
  circle (`stable_part_le`, `pseudo_eig`, `det_norm_le`, `quad_lower`,
  `norm_eps_mul_sub_one_lt`).
* `block_unstable` — with `det M_slow < 0` there is a real eigenvalue below `−1` (Schur
  complement `schur_estimate`, `inv_norm_le`, `det_add_sub_le`, intermediate values
  `exists_zero_of_mul_neg`, `det_sub_same_sign`).
* `averagingN_stable`, `averagingN_unstable` — `s > 0`, `|g/2|² < s² + d²` give all Floquet
  multipliers inside the unit circle; `s² + d² < |g/2|²` gives Floquet instability; in the
  unscaled variables `ε|g_m| ≶ 2√(σ_m² + Δ_m²)`.

Corrections.
None: the first-order 2:1 criterion of §2.2 holds for the complete `n`-state systems whose
stable block has all one-period eigenvalues inside the unit circle, not only for the two-state
reduction.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.BlockAveraging
open Complex Matrix Filter Topology Set
open scoped Matrix.Norms.Operator
open NormalForm (rot quarter)
open TwoToOne (base modReal stdForm left right)

/-! ### A lower bound for a quadratic with roots in the right half plane -/

/-- If `a < 0 < b`, both roots of `ν² + aν + b` have positive real part, so `|ν² + aν + b|` is
bounded below on a half plane `Re ν ≤ c`. -/
@[tmio T, powerlib_foundation] theorem quad_lower {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∃ c > 0, ∀ ν : ℂ, ν.re ≤ c → c ^ 2 ≤ ‖ν ^ 2 + a * ν + b‖ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self ((a : ℂ) ^ 2 - 4 * b)
  have hre : (z * z).re = a ^ 2 - 4 * b := by rw [← hz]; simp [pow_two]
  have him : (z * z).im = 0 := by rw [← hz]; simp [pow_two]
  simp only [mul_re, mul_im] at hre him
  have hzre : |z.re| < -a := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · rw [h, abs_zero]; linarith
    · rw [h] at hre
      have : z.re ^ 2 < (-a) ^ 2 := by nlinarith
      exact abs_lt_of_sq_lt_sq this (by linarith)
  set r1 := (-a + z.re) / 2
  set r2 := (-a - z.re) / 2
  have hr1 : 0 < r1 := by simp only [r1]; linarith [neg_abs_le z.re]
  have hr2 : 0 < r2 := by simp only [r2]; linarith [le_abs_self z.re]
  refine ⟨min r1 r2 / 2, by positivity, fun ν hν => ?_⟩
  have hfac : ν ^ 2 + a * ν + b = (ν - (-a + z) / 2) * (ν - (-a - z) / 2) := by
    linear_combination (-1 / 4 : ℂ) * hz
  rw [hfac, norm_mul]
  have h1 : min r1 r2 / 2 ≤ ‖ν - (-a + z) / 2‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have : (ν - (-a + z) / 2).re = ν.re - r1 := by simp [r1]
    rw [this, abs_sub_comm, abs_of_pos (by linarith [min_le_left r1 r2])]
    linarith [min_le_left r1 r2]
  have h2 : min r1 r2 / 2 ≤ ‖ν - (-a - z) / 2‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have : (ν - (-a - z) / 2).re = ν.re - r2 := by simp [r2]
    rw [this, abs_sub_comm, abs_of_pos (by linarith [min_le_right r1 r2])]
    linarith [min_le_right r1 r2]
  rw [pow_two]
  exact mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

/-! ### Norms of complexified blocks and a `2 × 2` determinant bound -/

@[tmio T, powerlib_foundation] theorem norm_map_real {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) : ‖M.map (algebraMap ℝ ℂ)‖ = ‖M‖ := by
  simp only [linfty_opNorm_def, Matrix.map_apply]
  congr 2
  funext i
  congr 1
  funext j
  simp

@[tmio T, powerlib_foundation] theorem det_norm_le (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ)
    {B : ℝ} (hB : ∀ i j, ‖M i j‖ ≤ B) : ‖M.det‖ * ‖v‖ ≤ 2 * B * ‖M *ᵥ v‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  set w := M *ᵥ v with hw
  have w0 : w 0 = M 0 0 * v 0 + M 0 1 * v 1 := by
    simp [hw, mulVec, dotProduct, Fin.sum_univ_two]
  have w1 : w 1 = M 1 0 * v 0 + M 1 1 * v 1 := by
    simp [hw, mulVec, dotProduct, Fin.sum_univ_two]
  have hw0 : ‖w 0‖ ≤ ‖w‖ := norm_le_pi_norm w 0
  have hw1 : ‖w 1‖ ≤ ‖w‖ := norm_le_pi_norm w 1
  have e0 : M.det * v 0 = M 1 1 * w 0 - M 0 1 * w 1 := by
    rw [det_fin_two, w0, w1]; ring
  have e1 : M.det * v 1 = M 0 0 * w 1 - M 1 0 * w 0 := by
    rw [det_fin_two, w0, w1]; ring
  rw [← norm_smul]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    rw [e0]
    calc ‖M 1 1 * w 0 - M 0 1 * w 1‖ ≤ ‖M 1 1‖ * ‖w 0‖ + ‖M 0 1‖ * ‖w 1‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ B * ‖w‖ + B * ‖w‖ := by
          gcongr <;> exact hB _ _
      _ = 2 * B * ‖w‖ := by ring
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    rw [e1]
    calc ‖M 0 0 * w 1 - M 1 0 * w 0‖ ≤ ‖M 0 0‖ * ‖w 1‖ + ‖M 1 0‖ * ‖w 0‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ B * ‖w‖ + B * ‖w‖ := by
          gcongr <;> exact hB _ _
      _ = 2 * B * ‖w‖ := by ring

@[tmio T, powerlib_foundation] theorem entry_le_opNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] {𝕜 : Type*} [NormedField 𝕜] (M : Matrix m n 𝕜) (i : m) (j : n) :
    ‖M i j‖ ≤ ‖M‖ := by
  have h := linfty_opNorm_mulVec M (Pi.single j 1)
  have h1 : ‖(Pi.single j (1 : 𝕜) : n → 𝕜)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have h2 : ‖M i j‖ ≤ ‖M *ᵥ Pi.single j 1‖ := by
    have := norm_le_pi_norm (M *ᵥ Pi.single j (1 : 𝕜)) i
    simpa [mulVec_single] using this
  calc ‖M i j‖ ≤ ‖M‖ * ‖(Pi.single j (1 : 𝕜) : n → 𝕜)‖ := h2.trans h
    _ ≤ ‖M‖ * 1 := by gcongr
    _ = ‖M‖ := mul_one _

/-! ### Block matrices near `diag(−(I + εT M), S)`: stability -/

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

@[tmio T, powerlib_foundation] theorem eventually_lt_nhdsGT {ε0 : ℝ} (h : 0 < ε0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < ε0 := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε0 := nhdsWithin_le_nhds (Iio_mem_nhds h)
  exact h1.and h2

/-- The stable components of an eigenvector with `|μ| ≥ 1` are controlled by the coupling. -/
@[tmio T, powerlib_foundation] theorem stable_part_le {R : Matrix Y (Fin 2) ℂ} {S : Matrix Y Y ℂ}
    {vc : Fin 2 → ℂ} {vs : Y → ℂ} {μ : ℂ} {a b : ℝ} (h : R *ᵥ vc + S *ᵥ vs = μ • vs)
    (hμ : 1 ≤ ‖μ‖) (hR : ‖R‖ ≤ a) (hS : ‖S‖ ≤ b) : (1 - b) * ‖vs‖ ≤ a * ‖vc‖ := by
  have h1 : ‖μ‖ * ‖vs‖ ≤ a * ‖vc‖ + b * ‖vs‖ := by
    rw [← norm_smul, ← h]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
    · exact (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  nlinarith [norm_nonneg vs]

/-- `|εν − 1| < 1` when `Re ν > c > 0`, `|ν| ≤ L` and `εL² ≤ c`. -/
@[tmio T, powerlib_foundation] theorem norm_eps_mul_sub_one_lt {ν : ℂ} {ε c L : ℝ} (hε : 0 < ε)
    (hc : 0 < c) (hre : c < ν.re) (hL : ‖ν‖ ≤ L) (hεL : ε * L ^ 2 ≤ c) :
    ‖(ε : ℂ) * ν - 1‖ < 1 := by
  have hνsq : ν.re ^ 2 + ν.im ^ 2 ≤ L ^ 2 := by
    have : ‖ν‖ ^ 2 = ν.re ^ 2 + ν.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← this]
    exact pow_le_pow_left₀ (norm_nonneg _) hL 2
  have hsq : ‖(ε : ℂ) * ν - 1‖ ^ 2 = (ε * ν.re - 1) ^ 2 + (ε * ν.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h : ‖(ε : ℂ) * ν - 1‖ ^ 2 < 1 := by
    rw [hsq]; nlinarith [mul_pos hε hc, sq_nonneg ε]
  by_contra h'
  rw [not_lt] at h'
  nlinarith [h', norm_nonneg ((ε : ℂ) * ν - 1)]

/-- The determinant of `ν I + T M` for a `2 × 2` matrix. -/
@[tmio T, powerlib_foundation] theorem det_smul_one_add (ν : ℂ) (T : ℝ) (Ms : Matrix (Fin 2) (Fin 2) ℝ) :
    (ν • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (T : ℂ) • Ms.map (algebraMap ℝ ℂ)).det =
      ν ^ 2 + ((T * Ms.trace : ℝ) : ℂ) * ν + ((T ^ 2 * Ms.det : ℝ) : ℂ) := by
  simp only [det_fin_two, trace_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply_eq, smul_eq_mul, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Complex.coe_algebraMap]
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem entry_smul_one_add_le (ν : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (Ms : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    ‖(ν • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (T : ℂ) • Ms.map (algebraMap ℝ ℂ)) i j‖ ≤
      ‖ν‖ + T * ‖Ms‖ := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    have : ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    nlinarith [norm_nonneg ν, norm_nonneg ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT]
    simp only [Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simpa using entry_le_opNorm Ms i j) hT

/-- From an `O(ε²)` approximate eigenvector of `−(I + εT M)` to the pseudo-eigenvalue
`ν = (1 + μ)/ε` of `−T M`. -/
@[tmio T, powerlib_foundation] theorem pseudo_eig {μ : ℂ} {vc : Fin 2 → ℂ} {Ms : Matrix (Fin 2) (Fin 2) ℝ}
    {ε T K : ℝ} (hε : 0 < ε)
    (h : ‖(1 + μ) • vc + ((ε * T : ℝ) : ℂ) • (Ms.map (algebraMap ℝ ℂ) *ᵥ vc)‖ ≤ K * ε ^ 2 * ‖vc‖) :
    ‖((1 + μ) / ε) • vc + (T : ℂ) • (Ms.map (algebraMap ℝ ℂ) *ᵥ vc)‖ ≤ K * ε * ‖vc‖ := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have heq : ((1 + μ) / ε) • vc + (T : ℂ) • (Ms.map (algebraMap ℝ ℂ) *ᵥ vc) =
      ((ε : ℂ)⁻¹) • ((1 + μ) • vc + ((ε * T : ℝ) : ℂ) • (Ms.map (algebraMap ℝ ℂ) *ᵥ vc)) := by
    rw [smul_add, smul_smul, smul_smul]
    congr 2
    · field_simp
    · push_cast; field_simp
  rw [heq, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hε.le,
    inv_mul_le_iff₀ hε]
  nlinarith [h]

/-- A block matrix `[[P, Q], [R, S]]` with `P = −(I + εT M) + O(ε²)`, `Q, R = O(ε)`,
`‖S‖ ≤ q + O(ε)`, `q < 1`, and `M` Hurwitz (`tr M < 0 < det M`) has every eigenvalue inside the
unit circle for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem block_stable {T : ℝ} (hT : 0 < T)
    {Ms : Matrix (Fin 2) (Fin 2) ℝ} (htr : Ms.trace < 0) (hdet : 0 < Ms.det) {C q : ℝ}
    (hC : 0 ≤ C) (hq : q < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • Ms‖ ≤ C * ε ^ 2 → ‖Q‖ ≤ C * ε → ‖R‖ ≤ C * ε → ‖S‖ ≤ q + C * ε →
      ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (fromBlocks P Q R S).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨c, hc, hquad⟩ := quad_lower (a := T * Ms.trace) (b := T ^ 2 * Ms.det)
    (mul_neg_of_pos_of_neg hT htr) (by positivity)
  obtain ⟨m, hm⟩ : ∃ m, m = ‖Ms‖ := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := hm ▸ norm_nonneg _
  obtain ⟨K2, hK2⟩ : ∃ K2, K2 = 2 * C ^ 2 / (1 - q) + C := ⟨_, rfl⟩
  have hK20 : 0 ≤ K2 := by
    have : 0 < 1 - q := by linarith
    rw [hK2]; positivity
  obtain ⟨L, hL⟩ : ∃ L, L = T * m + K2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * (L + T * m) * K2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨ε0, hε0⟩ : ∃ ε0, ε0 = min 1 (min ((1 - q) / (2 * (C + 1)))
      (min (c ^ 2 / (D + 1)) (c / (L ^ 2 + 1)))) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    have : 0 < 1 - q := by linarith
    rw [hε0]
    refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  filter_upwards [eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεq : ε ≤ (1 - q) / (2 * (C + 1)) :=
    (hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεD : ε ≤ c ^ 2 / (D + 1) :=
    (hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hεL : ε ≤ c / (L ^ 2 + 1) :=
    (hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  clear hε0 hεlt
  have hCε : C * ε ≤ (1 - q) / 2 := by
    have h := mul_le_mul_of_nonneg_left hεq (by linarith : (0 : ℝ) ≤ C + 1)
    rw [mul_div_assoc', show (C + 1) * (1 - q) / (2 * (C + 1)) = (1 - q) / 2 by field_simp] at h
    nlinarith
  intro P Q R S hP hQ hR hS μ v hv heq
  by_contra hμ
  rw [not_lt] at hμ
  have hq' : 0 < 1 - q := by linarith
  obtain ⟨vc, hvc⟩ : ∃ vc : Fin 2 → ℂ, vc = v ∘ Sum.inl := ⟨_, rfl⟩
  obtain ⟨vs, hvs⟩ : ∃ vs : Y → ℂ, vs = v ∘ Sum.inr := ⟨_, rfl⟩
  rw [fromBlocks_map, fromBlocks_mulVec] at heq
  have e1 : P.map (algebraMap ℝ ℂ) *ᵥ vc + Q.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vc :=
    funext fun i => by have := congrFun heq (Sum.inl i); simpa [hvc, hvs] using this
  have e2 : R.map (algebraMap ℝ ℂ) *ᵥ vc + S.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vs :=
    funext fun y => by have := congrFun heq (Sum.inr y); simpa [hvc, hvs] using this
  have hvsb : ‖vs‖ ≤ 2 * C / (1 - q) * ε * ‖vc‖ := by
    have h := stable_part_le (a := C * ε) (b := q + C * ε) e2 hμ
      (by rw [norm_map_real]; exact hR) (by rw [norm_map_real]; exact hS)
    have h2 : (1 - q) / 2 * ‖vs‖ ≤ C * ε * ‖vc‖ := by nlinarith [norm_nonneg vs]
    rw [show 2 * C / (1 - q) * ε * ‖vc‖ = (C * ε * ‖vc‖) / ((1 - q) / 2) by field_simp,
      le_div_iff₀ (by positivity)]
    linarith
  have hvc0 : vc ≠ 0 := by
    intro h
    apply hv
    have h0 : ‖vs‖ ≤ 0 := by rw [h, norm_zero, mul_zero] at hvsb; exact hvsb
    have hvs0 : vs = 0 := norm_le_zero_iff.mp h0
    funext x
    cases x with
    | inl i => simpa [hvc] using congrFun h i
    | inr y => simpa [hvs] using congrFun hvs0 y
  have hvcpos : 0 < ‖vc‖ := norm_pos_iff.mpr hvc0
  have hkey : ‖(1 + μ) • vc + ((ε * T : ℝ) : ℂ) • (Ms.map (algebraMap ℝ ℂ) *ᵥ vc)‖ ≤
      K2 * ε ^ 2 * ‖vc‖ := by
    have hE : (P + 1 + (ε * T) • Ms).map (algebraMap ℝ ℂ) =
        P.map (algebraMap ℝ ℂ) + 1 + ((ε * T : ℝ) : ℂ) • Ms.map (algebraMap ℝ ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    have key : (1 + μ) • vc + ((ε * T : ℝ) : ℂ) • (Ms.map (algebraMap ℝ ℂ) *ᵥ vc) =
        (P + 1 + (ε * T) • Ms).map (algebraMap ℝ ℂ) *ᵥ vc + Q.map (algebraMap ℝ ℂ) *ᵥ vs := by
      rw [hE, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      have hP' : P.map (algebraMap ℝ ℂ) *ᵥ vc = μ • vc - Q.map (algebraMap ℝ ℂ) *ᵥ vs := by
        rw [← e1]; abel
      rw [hP', add_smul, one_smul]; abel
    rw [key]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(P + 1 + (ε * T) • Ms).map (algebraMap ℝ ℂ) *ᵥ vc‖ ≤ C * ε ^ 2 * ‖vc‖ := by
      refine (linfty_opNorm_mulVec _ _).trans ?_
      rw [norm_map_real]; exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    have h2 : ‖Q.map (algebraMap ℝ ℂ) *ᵥ vs‖ ≤ C * ε * (2 * C / (1 - q) * ε * ‖vc‖) := by
      refine (linfty_opNorm_mulVec _ _).trans ?_
      rw [norm_map_real]
      exact mul_le_mul hQ hvsb (norm_nonneg _) (by positivity)
    have : C * ε * (2 * C / (1 - q) * ε * ‖vc‖) = 2 * C ^ 2 / (1 - q) * ε ^ 2 * ‖vc‖ := by ring
    rw [this] at h2
    rw [hK2]
    nlinarith [h1, h2]
  have hνv := pseudo_eig hε hkey
  obtain ⟨ν, hν⟩ : ∃ ν : ℂ, ν = (1 + μ) / ε := ⟨_, rfl⟩
  rw [← hν] at hνv
  obtain ⟨Msc, hMsc⟩ : ∃ Msc, Msc = Ms.map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  rw [← hMsc] at hνv
  have hMv : ‖(T : ℂ) • (Msc *ᵥ vc)‖ ≤ T * m * ‖vc‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hT.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hT.le
    refine (linfty_opNorm_mulVec _ _).trans ?_
    rw [hMsc, norm_map_real, hm]
  have hνL : ‖ν‖ ≤ L := by
    have h : ‖ν‖ * ‖vc‖ ≤ L * ‖vc‖ := by
      rw [← norm_smul]
      calc ‖ν • vc‖ = ‖(ν • vc + (T : ℂ) • (Msc *ᵥ vc)) - (T : ℂ) • (Msc *ᵥ vc)‖ := by
            rw [add_sub_cancel_right]
        _ ≤ ‖ν • vc + (T : ℂ) • (Msc *ᵥ vc)‖ + ‖(T : ℂ) • (Msc *ᵥ vc)‖ := norm_sub_le _ _
        _ ≤ K2 * ε * ‖vc‖ + T * m * ‖vc‖ := add_le_add hνv hMv
        _ ≤ K2 * 1 * ‖vc‖ + T * m * ‖vc‖ := by gcongr
        _ = L * ‖vc‖ := by rw [hL]; ring
    exact le_of_mul_le_mul_right h hvcpos
  have hdetM : ‖(ν • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (T : ℂ) • Msc).det‖ ≤ D * ε := by
    have h := det_norm_le (ν • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (T : ℂ) • Msc) vc
      (B := L + T * m) (fun i j => by
        rw [hMsc]
        refine (entry_smul_one_add_le ν hT.le Ms i j).trans ?_
        rw [← hm]; linarith)
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at h
    have h' : ‖(ν • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (T : ℂ) • Msc).det‖ * ‖vc‖ ≤
        D * ε * ‖vc‖ := by
      refine h.trans ?_
      rw [hD]
      calc 2 * (L + T * m) * ‖ν • vc + (T : ℂ) • (Msc *ᵥ vc)‖ ≤
          2 * (L + T * m) * (K2 * ε * ‖vc‖) := by gcongr
        _ = 2 * (L + T * m) * K2 * ε * ‖vc‖ := by ring
    exact le_of_mul_le_mul_right h' hvcpos
  rw [hMsc, det_smul_one_add] at hdetM
  have hνre : c < ν.re := by
    by_contra h
    rw [not_lt] at h
    have h1 := hquad ν h
    have h2 : D * ε < c ^ 2 := by
      calc D * ε ≤ D * (c ^ 2 / (D + 1)) := by gcongr
        _ < c ^ 2 := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          have hc2 : 0 < c ^ 2 := by positivity
          linarith [hc2]
    linarith
  have hεL2 : ε * L ^ 2 ≤ c := by
    calc ε * L ^ 2 ≤ c / (L ^ 2 + 1) * L ^ 2 := by gcongr
      _ ≤ c := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        linarith [hc]
  have hμeq : μ = (ε : ℂ) * ν - 1 := by
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    rw [hν]; field_simp; ring
  have := norm_eps_mul_sub_one_lt hε hc hνre hνL hεL2
  rw [← hμeq] at this
  linarith

/-! ### Block matrices: a real multiplier beyond `−1` -/

@[tmio T, powerlib_foundation] theorem opNorm_le_of_mulVec {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m n ℝ} {K : ℝ} (hK : 0 ≤ K) (h : ∀ v, ‖A *ᵥ v‖ ≤ K * ‖v‖) : ‖A‖ ≤ K := by
  rw [linfty_opNorm_eq_opNorm]
  exact ContinuousLinearMap.opNorm_le_bound _ hK h

/-- `μ I − S` is invertible with `‖(μ I − S)⁻¹‖ ≤ 1/δ` when `‖S‖ + δ ≤ |μ|`. -/
@[tmio T, powerlib_foundation] theorem inv_norm_le {S : Matrix Y Y ℝ} {μ δ : ℝ} (hδ : 0 < δ)
    (h : ‖S‖ + δ ≤ |μ|) :
    IsUnit (μ • (1 : Matrix Y Y ℝ) - S).det ∧ ‖(μ • (1 : Matrix Y Y ℝ) - S)⁻¹‖ ≤ 1 / δ := by
  have hlow : ∀ w : Y → ℝ, δ * ‖w‖ ≤ ‖(μ • (1 : Matrix Y Y ℝ) - S) *ᵥ w‖ := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 : ‖S *ᵥ w‖ ≤ ‖S‖ * ‖w‖ := linfty_opNorm_mulVec _ _
    have h2 : ‖μ • w‖ - ‖S *ᵥ w‖ ≤ ‖μ • w - S *ᵥ w‖ := norm_sub_norm_le _ _
    rw [norm_smul, Real.norm_eq_abs] at h2
    nlinarith [norm_nonneg w]
  have hdet : IsUnit (μ • (1 : Matrix Y Y ℝ) - S).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨w, hw, hw0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have := hlow w
    rw [hw0, norm_zero] at this
    have : ‖w‖ ≤ 0 := by nlinarith [norm_nonneg w]
    exact hw (norm_le_zero_iff.mp this)
  refine ⟨hdet, opNorm_le_of_mulVec (by positivity) fun u => ?_⟩
  have h := hlow ((μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
  linarith

/-- `|det(A + X) − det A| ≤ 4ax + 2x²` for `2 × 2` matrices with entries bounded by `a`, `x`. -/
@[tmio T, powerlib_foundation] theorem det_add_sub_le (A X : Matrix (Fin 2) (Fin 2) ℝ) {a x : ℝ}
    (hA : ∀ i j, |A i j| ≤ a) (hX : ∀ i j, |X i j| ≤ x) :
    |(A + X).det - A.det| ≤ 4 * a * x + 2 * x ^ 2 := by
  have hp : ∀ i j k l, |A i j * X k l| ≤ a * x := fun i j k l => by
    rw [abs_mul]; exact mul_le_mul (hA i j) (hX k l) (abs_nonneg _) ((abs_nonneg _).trans (hA i j))
  have hp' : ∀ i j k l, |X i j * X k l| ≤ x * x := fun i j k l => by
    rw [abs_mul]; exact mul_le_mul (hX i j) (hX k l) (abs_nonneg _) ((abs_nonneg _).trans (hX i j))
  have e : (A + X).det - A.det = A 0 0 * X 1 1 + X 0 0 * A 1 1 + X 0 0 * X 1 1 -
      A 0 1 * X 1 0 - X 0 1 * A 1 0 - X 0 1 * X 1 0 := by
    rw [det_fin_two, det_fin_two]; simp only [Matrix.add_apply]; ring
  rw [e]
  have h1 := hp 0 0 1 1
  have h2 : |X 0 0 * A 1 1| ≤ a * x := by rw [mul_comm]; exact hp 1 1 0 0
  have h3 := hp' 0 0 1 1
  have h4 := hp 0 1 1 0
  have h5 : |X 0 1 * A 1 0| ≤ a * x := by rw [mul_comm]; exact hp 1 0 0 1
  have h6 := hp' 0 1 1 0
  obtain ⟨l1, u1⟩ := abs_le.mp h1
  obtain ⟨l2, u2⟩ := abs_le.mp h2
  obtain ⟨l3, u3⟩ := abs_le.mp h3
  obtain ⟨l4, u4⟩ := abs_le.mp h4
  obtain ⟨l5, u5⟩ := abs_le.mp h5
  obtain ⟨l6, u6⟩ := abs_le.mp h6
  rw [abs_le]
  constructor <;> nlinarith

@[tmio T, powerlib_foundation] theorem exists_zero_of_mul_neg {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hf : ContinuousOn f (Icc x y)) (h : f x * f y < 0) : ∃ z ∈ Icc x y, f z = 0 := by
  rcases lt_or_gt_of_ne (show f x ≠ 0 by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h)
    with hx | hx
  · have hy : 0 < f y := by
      by_contra hy; rw [not_lt] at hy; nlinarith
    exact intermediate_value_Icc hxy hf ⟨hx.le, hy.le⟩
  · have hy : f y < 0 := by
      by_contra hy; rw [not_lt] at hy; nlinarith
    exact intermediate_value_Icc' hxy hf ⟨hy.le, hx.le⟩

@[tmio T, powerlib_foundation] theorem continuous_det_sub {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Continuous fun μ : ℝ => (μ • (1 : Matrix n n ℝ) - M).det :=
  ((continuous_id.smul continuous_const).sub continuous_const).matrix_det

/-- `det(μI − S)` has a constant sign on an interval of `μ ≤ −1` when `‖S‖ < 1`. -/
@[tmio T, powerlib_foundation] theorem det_sub_same_sign {S : Matrix Y Y ℝ} {δ x y : ℝ} (hδ : 0 < δ)
    (hS : ‖S‖ + δ ≤ 1) (hxy : x ≤ y) (hy : y ≤ -1) :
    0 < (x • (1 : Matrix Y Y ℝ) - S).det * (y • (1 : Matrix Y Y ℝ) - S).det := by
  have hne : ∀ z : ℝ, z ≤ -1 → (z • (1 : Matrix Y Y ℝ) - S).det ≠ 0 := fun z hz =>
    (inv_norm_le (S := S) (μ := z) hδ (by rw [abs_of_neg (by linarith)]; linarith)).1.ne_zero
  rcases lt_or_gt_of_ne (mul_ne_zero (hne x (hxy.trans hy)) (hne y hy)) with h | h
  · obtain ⟨z, hz, hz0⟩ := exists_zero_of_mul_neg hxy (continuous_det_sub S).continuousOn h
    exact absurd hz0 (hne z (hz.2.trans hy))
  · exact h

/-- The Schur complement of `μ I − [[P, Q], [R, S]]` at `μ = −1 − εa`: the determinant is
`det(μI − S) · ε² d` with `d` within `4αKε + 2K²ε²` of `a² − aT tr M + T² det M`. -/
@[tmio T, powerlib_foundation] theorem schur_estimate {T ε a C δ α : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {Ms P : Matrix (Fin 2) (Fin 2) ℝ} {Q : Matrix (Fin 2) Y ℝ} {R : Matrix Y (Fin 2) ℝ}
    {S : Matrix Y Y ℝ} (hP : ‖P + 1 + (ε * T) • Ms‖ ≤ C * ε ^ 2) (hQ : ‖Q‖ ≤ C * ε)
    (hR : ‖R‖ ≤ C * ε) (hS : ‖S‖ + δ ≤ |-1 - ε * a|) (hC : 0 ≤ C)
    (hα : ∀ i j, |(T • Ms - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤ α) :
    ∃ d, ((-1 - ε * a) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det =
        ((-1 - ε * a) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 2 * d) ∧
      |d - (a ^ 2 - a * T * Ms.trace + T ^ 2 * Ms.det)| ≤
        4 * α * ((C + C ^ 2 / δ) * ε) + 2 * ((C + C ^ 2 / δ) * ε) ^ 2 := by
  set μ := -1 - ε * a with hμ
  obtain ⟨hN, hNinv⟩ := inv_norm_le (S := S) (μ := μ) hδ hS
  set N := μ • (1 : Matrix Y Y ℝ) - S with hNdef
  let _ : Invertible N := Matrix.invertibleOfIsUnitDet N hN
  have hblk : μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S =
      fromBlocks (μ • 1 - P) (-Q) (-R) N := by
    rw [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp [hNdef, sub_eq_add_neg]
  set W := -(P + 1 + (ε * T) • Ms) - Q * N⁻¹ * R with hW
  have hZ : μ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - P - -Q * ⅟N * -R =
      ε • ((T • Ms - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + ε⁻¹ • W) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    have e : ε • ((T • Ms - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + ε⁻¹ • W) =
        ε • (T • Ms - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + W := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
    rw [e, hW, hμ]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_sub, smul_smul, sub_smul, neg_smul,
      one_smul]
    abel
  have hWn : ‖W‖ ≤ (C + C ^ 2 / δ) * ε ^ 2 := by
    rw [hW]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    have h1 : ‖Q * N⁻¹ * R‖ ≤ C * ε * (1 / δ) * (C * ε) := by
      refine (linfty_opNorm_mul _ _).trans ?_
      refine mul_le_mul ((linfty_opNorm_mul _ _).trans (mul_le_mul hQ hNinv (norm_nonneg _)
        (by positivity))) hR (norm_nonneg _) (by positivity)
    have : C * ε * (1 / δ) * (C * ε) = C ^ 2 / δ * ε ^ 2 := by field_simp
    rw [this] at h1
    nlinarith [hP, h1]
  refine ⟨((T • Ms - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + ε⁻¹ • W).det, ?_, ?_⟩
  · rw [hblk, det_fromBlocks₂₂, hZ, det_smul, Fintype.card_fin]
  · have hdetA : (T • Ms - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
        a ^ 2 - a * T * Ms.trace + T ^ 2 * Ms.det := by
      simp only [det_fin_two, trace_fin_two, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
      ring
    rw [← hdetA]
    refine det_add_sub_le _ _ hα fun i j => ?_
    calc |(ε⁻¹ • W) i j| ≤ ‖ε⁻¹ • W‖ := by
          have := entry_le_opNorm (ε⁻¹ • W) i j
          rwa [Real.norm_eq_abs] at this
      _ = ε⁻¹ * ‖W‖ := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
      _ ≤ ε⁻¹ * ((C + C ^ 2 / δ) * ε ^ 2) := by gcongr
      _ = (C + C ^ 2 / δ) * ε := by field_simp

set_option maxHeartbeats 1000000 in
/-- A block matrix `[[P, Q], [R, S]]` with `P = −(I + εT M) + O(ε²)`, `Q, R = O(ε)`,
`‖S‖ ≤ q + O(ε)`, `q < 1`, and `det M < 0` has a real eigenvalue `μ < −1` for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem block_unstable {T : ℝ} (hT : 0 < T)
    {Ms : Matrix (Fin 2) (Fin 2) ℝ} (hdet : Ms.det < 0) {C q : ℝ} (hC : 0 ≤ C) (hq : q < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • Ms‖ ≤ C * ε ^ 2 → ‖Q‖ ≤ C * ε → ‖R‖ ≤ C * ε → ‖S‖ ≤ q + C * ε →
      ∃ μ : ℝ, μ < -1 ∧ (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, m = ‖Ms‖ := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := hm ▸ norm_nonneg _
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = |Ms.trace| := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := hτ ▸ abs_nonneg _
  have hdm : 0 < -(T ^ 2 * Ms.det) := by nlinarith [sq_pos_of_pos hT]
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = min 1 (-(T ^ 2 * Ms.det) / (2 * (1 + T * τ))) := ⟨_, rfl⟩
  have ha1pos : 0 < a1 := by rw [ha1]; exact lt_min one_pos (by positivity)
  have ha1le : a1 ≤ 1 := ha1 ▸ min_le_left _ _
  have ha1le' : a1 ≤ -(T ^ 2 * Ms.det) / (2 * (1 + T * τ)) := ha1 ▸ min_le_right _ _
  obtain ⟨a2, ha2⟩ : ∃ a2, a2 = 2 + 2 * T * τ - T ^ 2 * Ms.det := ⟨_, rfl⟩
  have htr : |Ms.trace| ≤ τ := hτ ▸ le_rfl
  have htr1 := neg_abs_le Ms.trace
  have htr2 := le_abs_self Ms.trace
  -- the sign of the reduced determinant `q(a) = a² − aT tr M + T² det M`
  have hq1 : a1 ^ 2 - a1 * T * Ms.trace + T ^ 2 * Ms.det ≤ T ^ 2 * Ms.det / 2 := by
    have h1 : a1 ^ 2 ≤ a1 := by nlinarith
    have h2 : -(a1 * T * Ms.trace) ≤ a1 * (T * τ) := by
      have : -(T * Ms.trace) ≤ T * τ := by nlinarith
      nlinarith
    have h3 : a1 * (1 + T * τ) ≤ -(T ^ 2 * Ms.det) / 2 := by
      have hpos : 0 < 1 + T * τ := by positivity
      calc a1 * (1 + T * τ) ≤ -(T ^ 2 * Ms.det) / (2 * (1 + T * τ)) * (1 + T * τ) := by gcongr
        _ = -(T ^ 2 * Ms.det) / 2 := by field_simp
    nlinarith
  have hq2 : 1 ≤ a2 ^ 2 - a2 * T * Ms.trace + T ^ 2 * Ms.det := by
    have h1 : a2 * T * Ms.trace ≤ a2 * (T * τ) := by
      have : T * Ms.trace ≤ T * τ := by nlinarith
      have : 0 ≤ a2 := by rw [ha2]; nlinarith [hdm, mul_nonneg hT.le hτ0]
      nlinarith
    have h2 : 2 + T * τ ≤ a2 - T * τ := by rw [ha2]; linarith
    have ha2' : 2 ≤ a2 := by rw [ha2]; nlinarith
    nlinarith
  obtain ⟨η, hη⟩ : ∃ η, η = min (-(T ^ 2 * Ms.det) / 2) 1 / 2 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; exact half_pos (lt_min (by linarith) one_pos)
  have hη1 : a1 ^ 2 - a1 * T * Ms.trace + T ^ 2 * Ms.det ≤ -(2 * η) := by
    have : 2 * η ≤ -(T ^ 2 * Ms.det) / 2 := by rw [hη]; linarith [min_le_left (-(T ^ 2 * Ms.det) / 2) 1]
    linarith
  have hη2 : 2 * η ≤ a2 ^ 2 - a2 * T * Ms.trace + T ^ 2 * Ms.det := by
    have : 2 * η ≤ 1 := by rw [hη]; linarith [min_le_right (-(T ^ 2 * Ms.det) / 2) 1]
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (1 - q) / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨K, hK⟩ : ∃ K, K = C + C ^ 2 / δ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨α, hα⟩ : ∃ α, α = T * m + a2 := ⟨_, rfl⟩
  have ha20 : 0 ≤ a2 := by rw [ha2]; nlinarith [hdm, mul_nonneg hT.le hτ0]
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  obtain ⟨ε0, hε0⟩ : ∃ ε0, ε0 = min 1 (min ((1 - q) / (2 * (C + 1)))
      (η / (4 * α * K + 2 * K ^ 2 + 1))) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    have : 0 < 1 - q := by linarith
    rw [hε0]
    exact lt_min one_pos (lt_min (by positivity) (by positivity))
  filter_upwards [eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεq : ε ≤ (1 - q) / (2 * (C + 1)) :=
    (hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεη : ε ≤ η / (4 * α * K + 2 * K ^ 2 + 1) :=
    (hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  clear hεlt hε0
  have hCε : C * ε ≤ δ := by
    have h := mul_le_mul_of_nonneg_left hεq (by linarith : (0 : ℝ) ≤ C + 1)
    rw [mul_div_assoc', show (C + 1) * (1 - q) / (2 * (C + 1)) = (1 - q) / 2 by field_simp] at h
    rw [hδ]; linarith
  have herr : 4 * α * (K * ε) + 2 * (K * ε) ^ 2 < η := by
    have h1 : 4 * α * (K * ε) + 2 * (K * ε) ^ 2 ≤ (4 * α * K + 2 * K ^ 2) * ε := by
      have : (K * ε) ^ 2 ≤ K ^ 2 * ε := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (by rw [sq]; exact mul_le_of_le_one_left hε.le hε1)
          (sq_nonneg K)
      linarith [this]
    have h2 : (4 * α * K + 2 * K ^ 2) * ε < η := by
      calc (4 * α * K + 2 * K ^ 2) * ε ≤ (4 * α * K + 2 * K ^ 2) *
            (η / (4 * α * K + 2 * K ^ 2 + 1)) := by gcongr
        _ < η := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          linarith [hηpos]
    linarith
  intro P Q R S hP hQ hR hS
  have hSδ : ‖S‖ + δ ≤ 1 := by rw [hδ] at hCε ⊢; linarith
  have hentry : ∀ a, 0 ≤ a → a ≤ a2 → ∀ i j,
      |(T • Ms - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤ α := by
    intro a ha0 ha i j
    rw [hα]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hT, abs_of_nonneg ha0]
    have h1 : |Ms i j| ≤ m := by rw [hm]; simpa using entry_le_opNorm Ms i j
    have h2 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    have h3 := mul_le_mul_of_nonneg_left h1 hT.le
    have h4 := mul_le_mul_of_nonneg_left h2 ha0
    linarith only [h3, h4, ha]
  have habs : ∀ a, 0 ≤ a → ‖S‖ + δ ≤ |-1 - ε * a| := by
    intro a ha
    have h0 := mul_nonneg hε.le ha
    rw [abs_of_neg (by linarith only [h0])]
    linarith only [h0, hSδ]
  have ha2' : 2 ≤ a2 := by rw [ha2]; nlinarith [hdm, mul_nonneg hT.le hτ0]
  have ha12 : a1 ≤ a2 := by linarith only [ha1le, ha2']
  obtain ⟨d1, hd1, hd1b⟩ := schur_estimate (a := a1) hε hδpos hP hQ hR (habs a1 ha1pos.le) hC
    (hentry a1 ha1pos.le ha12)
  obtain ⟨d2, hd2, hd2b⟩ := schur_estimate (a := a2) hε hδpos hP hQ hR (habs a2 ha20) hC
    (hentry a2 ha20 le_rfl)
  rw [← hK] at hd1b hd2b
  have hd1neg : d1 < 0 := by
    have := (abs_le.mp (hd1b.trans herr.le)).2; linarith
  have hd2pos : 0 < d2 := by
    have := (abs_le.mp (hd2b.trans herr.le)).1; linarith
  have hμ12 : -1 - ε * a2 ≤ -1 - ε * a1 := by
    have := mul_le_mul_of_nonneg_left ha12 hε.le; linarith only [this]
  have hsign := det_sub_same_sign (S := S) hδpos hSδ hμ12
    (by have := mul_pos hε ha1pos; linarith only [this])
  set f := fun μ : ℝ => (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det
    with hf
  have hneg : f (-1 - ε * a2) * f (-1 - ε * a1) < 0 := by
    simp only [hf]
    rw [hd1, hd2]
    have hε2 : 0 < ε ^ 2 := by positivity
    have : (((-1 - ε * a2) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 2 * d2)) *
        (((-1 - ε * a1) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 2 * d1)) =
        (((-1 - ε * a2) • (1 : Matrix Y Y ℝ) - S).det *
          ((-1 - ε * a1) • (1 : Matrix Y Y ℝ) - S).det) * ((ε ^ 2) ^ 2 * (d2 * d1)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hsign (mul_neg_of_pos_of_neg (by positivity)
      (mul_neg_of_pos_of_neg hd2pos hd1neg))
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_mul_neg hμ12 (continuous_det_sub _).continuousOn hneg
  exact ⟨z, by have := mul_pos hε ha1pos; linarith only [this, hz.2], hz0⟩

/-! ### The `n`-state model: a critical pair and a stable block -/

/-! ### Spectral condition on the stable block: odd powers -/

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem block_pow_id11 (A P X : Matrix (Fin 2) (Fin 2) ℝ)
    (B : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (s κ : ℝ) [Fintype Y] :
    A * P + B * R - (-s) • (1 + (κ + 1) • X) =
      (A - s • (1 + κ • X)) * P + s • ((1 + κ • X) * (P + 1 + X)) - s • (κ • (X * X)) +
        B * R := by
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_one, smul_add, add_smul, one_smul, smul_smul, neg_smul]
  module

/-- Block estimates of the powers of a block matrix close to `diag(−(I + εT M), E)`:
`(M^k)₁₁ = (−1)^k(I + kεT M) + O(ε²)`, `(M^k)₁₂, (M^k)₂₁ = O(ε)`, `(M^k)₂₂ = E^k + O(ε)`. -/
@[tmio T, powerlib_foundation] theorem block_pow_estimate (T : ℝ) (Ms : Matrix (Fin 2) (Fin 2) ℝ)
    (E : Matrix Y Y ℝ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    ∃ c, 0 ≤ c ∧ ∀ ε, 0 < ε → ε ≤ 1 → ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • Ms‖ ≤ C * ε ^ 2 → ‖Q‖ ≤ C * ε → ‖R‖ ≤ C * ε → ‖S - E‖ ≤ C * ε →
      ‖(fromBlocks P Q R S ^ k).toBlocks₁₁ - (-1 : ℝ) ^ k • (1 + ((k : ℝ) * (ε * T)) • Ms)‖ ≤
          c * ε ^ 2 ∧
        ‖(fromBlocks P Q R S ^ k).toBlocks₁₂‖ ≤ c * ε ∧
        ‖(fromBlocks P Q R S ^ k).toBlocks₂₁‖ ≤ c * ε ∧
        ‖(fromBlocks P Q R S ^ k).toBlocks₂₂ - E ^ k‖ ≤ c * ε := by
  set a := ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ with ha
  set t := |T| * ‖Ms‖ with ht
  set e := ‖E‖ with he
  have ha0 : 0 ≤ a := norm_nonneg _
  have ht0 : 0 ≤ t := by positivity
  have he0 : 0 ≤ e := norm_nonneg _
  clear_value a t e
  induction k with
  | zero =>
    refine ⟨0, le_rfl, fun ε _ _ P Q R S _ _ _ _ => ?_⟩
    have h1 : (fromBlocks P Q R S) ^ 0 = fromBlocks 1 0 0 1 := by
      rw [pow_zero, fromBlocks_one]
    rw [h1, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      toBlocks_fromBlocks₂₂]
    simp
  | succ k ih =>
    obtain ⟨c, hc, hk⟩ := ih
    set dk := ‖E ^ k‖ with hdk
    have hdk0 : 0 ≤ dk := norm_nonneg _
    clear_value dk
    refine ⟨c * (a + t + C) + (a + k * t) * C + k * t ^ 2 + c * C + ((a + k * t) + c) * C +
        c * (e + C) + c * (a + t + C) + (dk + c) * C + c * C + c * (e + C) + dk * C,
        by positivity, fun ε hε hε1 P Q R S hP hQ hR hS => ?_⟩
    obtain ⟨h11, h12, h21, h22⟩ := hk ε hε hε1 P Q R S hP hQ hR hS
    set M := fromBlocks P Q R S with hM
    set A := (M ^ k).toBlocks₁₁
    set B := (M ^ k).toBlocks₁₂
    set Cc := (M ^ k).toBlocks₂₁
    set D := (M ^ k).toBlocks₂₂
    have hpow : M ^ (k + 1) = fromBlocks (A * P + B * R) (A * Q + B * S) (Cc * P + D * R)
        (Cc * Q + D * S) := by
      rw [pow_succ, ← fromBlocks_toBlocks (M ^ k), hM, fromBlocks_multiply]
    rw [hpow, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      toBlocks_fromBlocks₂₂]
    clear_value A B Cc D
    set X : Matrix (Fin 2) (Fin 2) ℝ := (ε * T) • Ms with hX
    have hXn : ‖X‖ ≤ ε * t := by
      rw [hX, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε, ht, mul_assoc]
    clear_value X
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have hεt : ε * t ≤ t := by nlinarith
    have hCε : C * ε ≤ C := by nlinarith
    set Δ := P + 1 + X with hΔ
    clear_value Δ
    have hPn : ‖P‖ ≤ a + t + C := by
      have : P = Δ - 1 - X := by rw [hΔ]; abel
      rw [this]
      have h3 : ‖Δ - 1 - X‖ ≤ ‖Δ‖ + a + ‖X‖ := by
        have n1 := norm_sub_le (Δ - 1) X
        have n2 := norm_sub_le Δ (1 : Matrix (Fin 2) (Fin 2) ℝ)
        rw [← ha] at n2; linarith
      refine h3.trans ?_
      nlinarith [hP, hXn]
    have hSn : ‖S‖ ≤ e + C := by
      have : S = (S - E) + E := by abel
      rw [this]; exact (norm_add_le _ _).trans (by nlinarith [hS])
    set Yk : Matrix (Fin 2) (Fin 2) ℝ := 1 + ((k : ℝ) * (ε * T)) • Ms with hYk
    have hYkX : Yk = 1 + (k : ℝ) • X := by rw [hYk, hX, smul_smul]
    clear_value Yk
    have hYn : ‖Yk‖ ≤ a + k * t := by
      rw [hYkX]
      refine (norm_add_le _ _).trans (add_le_add ha.symm.le ?_)
      rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg k)]
      exact mul_le_mul_of_nonneg_left (hXn.trans hεt) (Nat.cast_nonneg k)
    have hAn : ‖A‖ ≤ (a + k * t) + c := by
      have : A = (-1 : ℝ) ^ k • Yk + (A - (-1 : ℝ) ^ k • Yk) := by abel
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]; exact hYn
      · exact h11.trans (mul_le_of_le_one_right hc (by nlinarith))
    have hDn : ‖D‖ ≤ dk + c := by
      have : D = (D - E ^ k) + E ^ k := by abel
      rw [this]; exact (norm_add_le _ _).trans (by nlinarith [h22])
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hid : A * P + B * R - (-1 : ℝ) ^ (k + 1) • (1 + (((k + 1 : ℕ) : ℝ) * (ε * T)) • Ms) =
          (A - (-1 : ℝ) ^ k • Yk) * P + (-1 : ℝ) ^ k • (Yk * Δ) -
            (-1 : ℝ) ^ k • ((k : ℝ) • (X * X)) + B * R := by
        have e : (-1 : ℝ) ^ (k + 1) • (1 + (((k + 1 : ℕ) : ℝ) * (ε * T)) • Ms) =
            (-((-1 : ℝ) ^ k)) • (1 + ((k : ℝ) + 1) • X) := by
          rw [pow_succ, mul_neg_one, hX, smul_smul]; push_cast; rfl
        rw [e, hYkX, hΔ]
        exact block_pow_id11 A P X B R _ _
      rw [hid]
      have e1 : ‖(A - (-1 : ℝ) ^ k • Yk) * P‖ ≤ c * ε ^ 2 * (a + t + C) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul h11 hPn (norm_nonneg _) (by positivity))
      have e2 : ‖(-1 : ℝ) ^ k • (Yk * Δ)‖ ≤ (a + k * t) * (C * ε ^ 2) := by
        rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hYn hP (norm_nonneg _) (by positivity))
      have e3 : ‖(-1 : ℝ) ^ k • ((k : ℝ) • (X * X))‖ ≤ k * (ε * t) ^ 2 := by
        rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_smul,
          Real.norm_of_nonneg (Nat.cast_nonneg k)]
        refine mul_le_mul_of_nonneg_left ((Matrix.linfty_opNorm_mul _ _).trans ?_) (Nat.cast_nonneg k)
        rw [sq]; exact mul_le_mul hXn hXn (norm_nonneg _) (mul_nonneg hε.le ht0)
      have e4 : ‖B * R‖ ≤ c * ε * (C * ε) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul h12 hR (norm_nonneg _) (by positivity))
      have n1 := norm_add_le ((A - (-1 : ℝ) ^ k • Yk) * P + (-1 : ℝ) ^ k • (Yk * Δ) -
        (-1 : ℝ) ^ k • ((k : ℝ) • (X * X))) (B * R)
      have n2 := norm_sub_le ((A - (-1 : ℝ) ^ k • Yk) * P + (-1 : ℝ) ^ k • (Yk * Δ))
        ((-1 : ℝ) ^ k • ((k : ℝ) • (X * X)))
      have n3 := norm_add_le ((A - (-1 : ℝ) ^ k • Yk) * P) ((-1 : ℝ) ^ k • (Yk * Δ))
      have hsum : c * ε ^ 2 * (a + t + C) + (a + k * t) * (C * ε ^ 2) + k * (ε * t) ^ 2 +
          c * ε * (C * ε) = (c * (a + t + C) + (a + k * t) * C + k * t ^ 2 + c * C) * ε ^ 2 := by
        ring
      have hrest : 0 ≤ ((a + k * t) + c) * C + c * (e + C) + c * (a + t + C) + (dk + c) * C +
          c * C + c * (e + C) + dk * C := by positivity
      have hfin : (c * (a + t + C) + (a + k * t) * C + k * t ^ 2 + c * C) * ε ^ 2 ≤
          (c * (a + t + C) + (a + k * t) * C + k * t ^ 2 + c * C + ((a + k * t) + c) * C +
            c * (e + C) + c * (a + t + C) + (dk + c) * C + c * C + c * (e + C) + dk * C) *
              ε ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ε)
      linarith
    · have e1 : ‖A * Q‖ ≤ ((a + k * t) + c) * (C * ε) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hAn hQ (norm_nonneg _) (by positivity))
      have e2 : ‖B * S‖ ≤ c * ε * (e + C) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul h12 hSn (norm_nonneg _) (by positivity))
      refine (norm_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
      have : 0 ≤ c * (a + t + C) + (a + k * t) * C + k * t ^ 2 + c * C + c * (a + t + C) +
          (dk + c) * C + c * C + c * (e + C) + dk * C := by positivity
      rw [show ((a + k * t) + c) * (C * ε) + c * ε * (e + C) =
        (((a + k * t) + c) * C + c * (e + C)) * ε by ring]
      exact mul_le_mul_of_nonneg_right (by linarith) hε.le
    · have e1 : ‖Cc * P‖ ≤ c * ε * (a + t + C) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul h21 hPn (norm_nonneg _) (by positivity))
      have e2 : ‖D * R‖ ≤ (dk + c) * (C * ε) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hDn hR (norm_nonneg _) (by positivity))
      refine (norm_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
      have : 0 ≤ c * (a + t + C) + (a + k * t) * C + k * t ^ 2 + c * C + ((a + k * t) + c) * C +
          c * (e + C) + c * C + c * (e + C) + dk * C := by positivity
      rw [show c * ε * (a + t + C) + (dk + c) * (C * ε) = (c * (a + t + C) + (dk + c) * C) * ε by
        ring]
      exact mul_le_mul_of_nonneg_right (by linarith) hε.le
    · have hid : Cc * Q + D * S - E ^ (k + 1) = Cc * Q + (D - E ^ k) * S + E ^ k * (S - E) := by
        rw [pow_succ]; noncomm_ring
      rw [hid]
      have e1 : ‖Cc * Q‖ ≤ c * ε * (C * ε) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul h21 hQ (norm_nonneg _) (by positivity))
      have e2 : ‖(D - E ^ k) * S‖ ≤ c * ε * (e + C) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul h22 hSn (norm_nonneg _) (by positivity))
      have e3 : ‖E ^ k * (S - E)‖ ≤ dk * (C * ε) :=
        (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hdk.symm.le hS (norm_nonneg _) hdk0)
      refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add e1 e2))
        e3).trans ?_)
      have : 0 ≤ c * (a + t + C) + (a + k * t) * C + k * t ^ 2 + c * C + ((a + k * t) + c) * C +
          c * (e + C) + c * (a + t + C) + (dk + c) * C := by positivity
      have e4 : c * ε * (C * ε) ≤ c * C * ε := by
        rw [show c * ε * (C * ε) = c * C * ε * ε by ring]
        exact mul_le_of_le_one_right (by positivity) hε1
      calc c * ε * (C * ε) + c * ε * (e + C) + dk * (C * ε) ≤
            c * C * ε + c * ε * (e + C) + dk * (C * ε) := by linarith
        _ = (c * C + c * (e + C) + dk * C) * ε := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hε.le

/-- A spectral radius below one gives an odd contracting power. -/
@[tmio T, powerlib_foundation] theorem exists_odd_pow_norm_lt_one (E : Matrix Y Y ℝ)
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) : ∃ m : ℕ, ‖E ^ (2 * m + 1)‖ < 1 := by
  obtain ⟨n, hn, hlt⟩ := LTI.exists_pow_norm_lt_one E hρ
  set q := ‖E ^ n‖ with hqd
  have hq0 : 0 ≤ q := norm_nonneg _
  have he0 : 0 ≤ ‖E‖ := norm_nonneg _
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (‖E‖ + 1) by positivity) hlt
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, lt_div_iff₀ (by positivity)] at hj
    linarith
  refine ⟨n * j, ?_⟩
  have e : E ^ (2 * (n * j) + 1) = (E ^ n) ^ (2 * j) * E := by
    rw [← pow_mul, pow_succ]; ring_nf
  rw [e]
  have h1 : ‖(E ^ n) ^ (2 * j)‖ ≤ q ^ (2 * j) := norm_pow_le' _ (by omega)
  have h2 : q ^ (2 * j) ≤ q ^ j := pow_le_pow_of_le_one hq0 hlt.le (by omega)
  have h3 : q ^ j * (‖E‖ + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hj
  calc ‖(E ^ n) ^ (2 * j) * E‖ ≤ ‖(E ^ n) ^ (2 * j)‖ * ‖E‖ := norm_mul_le _ _
    _ ≤ q ^ j * ‖E‖ := mul_le_mul_of_nonneg_right (h1.trans h2) he0
    _ < 1 := by nlinarith [pow_nonneg hq0 j]

@[tmio T, powerlib_foundation] private theorem map_pow_real {Z : Type*} [Fintype Z] [DecidableEq Z]
    (M : Matrix Z Z ℝ) (n : ℕ) : (M ^ n).map (algebraMap ℝ ℂ) = M.map (algebraMap ℝ ℂ) ^ n := by
  have h := (RingHom.mapMatrix (algebraMap ℝ ℂ) : Matrix Z Z ℝ →+* Matrix Z Z ℂ).map_pow M n
  simpa [RingHom.mapMatrix_apply] using h

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem odd_block_identity (P : Matrix (Fin 2) (Fin 2) ℝ)
    (Ms : Matrix (Fin 2) (Fin 2) ℝ) (m : ℕ) (ε T : ℝ) :
    P + 1 + (ε * ((2 * m + 1 : ℕ) * T)) • Ms =
      P - (-1 : ℝ) ^ (2 * m + 1) • (1 + (((2 * m + 1 : ℕ) : ℝ) * (ε * T)) • Ms) := by
  rw [Odd.neg_one_pow ⟨m, rfl⟩, neg_one_smul, sub_neg_eq_add, add_assoc]
  congr 2
  ring_nf

/-- A contracting norm bounds the spectral radius: `‖E‖ < 1 ⇒ ρ(E) < 1`. -/
@[tmio T, powerlib_foundation] theorem spectralRadius_lt_one_of_norm {Z : Type*} [Fintype Z]
    [DecidableEq Z] [Nonempty Z] (E : Matrix Z Z ℝ) (h : ‖E‖ < 1) :
    spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1 := by
  refine (spectralRadius_le_nnnorm _).trans_lt ?_
  have e : ‖E.map (algebraMap ℝ ℂ)‖₊ = ‖E‖₊ := NNReal.eq (norm_map_real E)
  rw [e]
  have h' : ‖E‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; simpa using h
  exact_mod_cast h'

/-- `block_stable` with the spectral condition on the stable block: `S = E + O(ε)` with
`ρ(E) < 1` (instead of `‖S‖ ≤ q + O(ε)`, `q < 1`). The proof applies `block_stable` to an odd
power. -/
@[tmio T, powerlib_foundation] theorem block_stable_spec {T : ℝ} (hT : 0 < T)
    {Ms : Matrix (Fin 2) (Fin 2) ℝ} (htr : Ms.trace < 0) (hdet : 0 < Ms.det) {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • Ms‖ ≤ C * ε ^ 2 → ‖Q‖ ≤ C * ε → ‖R‖ ≤ C * ε → ‖S - E‖ ≤ C * ε →
      ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (fromBlocks P Q R S).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨m, hm⟩ := exists_odd_pow_norm_lt_one E hρ
  obtain ⟨c, hc, hpow⟩ := block_pow_estimate T Ms E hC (2 * m + 1)
  have hTn : 0 < ((2 * m + 1 : ℕ) : ℝ) * T := by positivity
  have h := block_stable (Y := Y) hTn htr hdet hc hm
  filter_upwards [h, eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
  intro P Q R S hP hQ hR hS μ v hv heq
  obtain ⟨h11, h12, h21, h22⟩ := hpow ε hε0 hε1.le P Q R S hP hQ hR hS
  set Mk := fromBlocks P Q R S ^ (2 * m + 1) with hMk
  have hP' : ‖Mk.toBlocks₁₁ + 1 + (ε * (((2 * m + 1 : ℕ) : ℝ) * T)) • Ms‖ ≤ c * ε ^ 2 := by
    rw [odd_block_identity]; exact h11
  have hS' : ‖Mk.toBlocks₂₂‖ ≤ ‖E ^ (2 * m + 1)‖ + c * ε := by
    have : Mk.toBlocks₂₂ = (Mk.toBlocks₂₂ - E ^ (2 * m + 1)) + E ^ (2 * m + 1) := by abel
    rw [this]; exact (norm_add_le _ _).trans (by linarith)
  have heq' : (fromBlocks Mk.toBlocks₁₁ Mk.toBlocks₁₂ Mk.toBlocks₂₁ Mk.toBlocks₂₂).map
      (algebraMap ℝ ℂ) *ᵥ v = μ ^ (2 * m + 1) • v := by
    rw [fromBlocks_toBlocks, hMk, map_pow_real]
    exact Linear.mulVec_pow_of_eigen heq _
  have := hε _ _ _ _ hP' h12 h21 hS' _ v hv heq'
  rw [norm_pow] at this
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this

/-- `block_unstable` with the spectral condition on the stable block: some eigenvalue lies
strictly outside the unit circle. -/
@[tmio T, powerlib_foundation] theorem block_unstable_spec {T : ℝ} (hT : 0 < T)
    {Ms : Matrix (Fin 2) (Fin 2) ℝ} (hdet : Ms.det < 0) {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • Ms‖ ≤ C * ε ^ 2 → ‖Q‖ ≤ C * ε → ‖R‖ ≤ C * ε → ‖S - E‖ ≤ C * ε →
      ∃ ρ ∈ spectrum ℂ ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)), 1 < ‖ρ‖ := by
  obtain ⟨m, hm⟩ := exists_odd_pow_norm_lt_one E hρ
  obtain ⟨c, hc, hpow⟩ := block_pow_estimate T Ms E hC (2 * m + 1)
  have hTn : 0 < ((2 * m + 1 : ℕ) : ℝ) * T := by positivity
  have h := block_unstable (Y := Y) hTn hdet hc hm
  filter_upwards [h, eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
  intro P Q R S hP hQ hR hS
  obtain ⟨h11, h12, h21, h22⟩ := hpow ε hε0 hε1.le P Q R S hP hQ hR hS
  set Mk := fromBlocks P Q R S ^ (2 * m + 1) with hMk
  have hP' : ‖Mk.toBlocks₁₁ + 1 + (ε * (((2 * m + 1 : ℕ) : ℝ) * T)) • Ms‖ ≤ c * ε ^ 2 := by
    rw [odd_block_identity]; exact h11
  have hS' : ‖Mk.toBlocks₂₂‖ ≤ ‖E ^ (2 * m + 1)‖ + c * ε := by
    have : Mk.toBlocks₂₂ = (Mk.toBlocks₂₂ - E ^ (2 * m + 1)) + E ^ (2 * m + 1) := by abel
    rw [this]; exact (norm_add_le _ _).trans (by linarith)
  obtain ⟨ν, hν, hdetν⟩ := hε _ _ _ _ hP' h12 h21 hS'
  rw [fromBlocks_toBlocks] at hdetν
  have hmem : (ν : ℂ) ∈ spectrum ℂ (Mk.map (algebraMap ℝ ℂ)) := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det]
    have hmap : (ν : ℂ) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) - Mk.map (algebraMap ℝ ℂ) =
        (ν • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - Mk).map (algebraMap ℝ ℂ) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdetν, map_zero]
    exact not_isUnit_zero
  rw [hMk, map_pow_real, spectrum.map_pow_of_pos _ (by omega)] at hmem
  obtain ⟨ρ, hρmem, hρν⟩ := hmem
  refine ⟨ρ, hρmem, ?_⟩
  have hn : ‖ρ‖ ^ (2 * m + 1) = |ν| := by
    rw [← norm_pow]; simp only at hρν; rw [hρν, Complex.norm_real, Real.norm_eq_abs]
  have h1 : 1 < ‖ρ‖ ^ (2 * m + 1) := by rw [hn, abs_of_neg (by linarith)]; linarith
  exact (one_lt_pow_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1


/-- The real modulation `Re{A₁ e^{jωt}}` of an `n`-state system. -/
def modN (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (ω t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  fun i j => (A i j).re * Real.cos (ω * t) - (A i j).im * Real.sin (ω * t)

/-- The full variational state matrix: the critical pair `−εs ± j(ω/2 − εd)` in real modal form,
a stable block `A_s`, and the modulation `ε Re{A₁ e^{jωt}}` coupling everything. -/
def fullN (s d ω : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (ε t : ℝ) :
    Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  fromBlocks (base (ε * s) (ω / 2 - ε * d)) 0 0 As + ε • modN A ω t

/-- `e^{tA_s}`. -/
def expS (As : Matrix Y Y ℝ) (t : ℝ) : Matrix Y Y ℝ := NormedSpace.exp (t • As)

/-- The frame `Ψ(t) = diag(R(ωt/2), e^{tA_s})` and its inverse. -/
def Psi (ω : ℝ) (As : Matrix Y Y ℝ) (t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  fromBlocks (rot (ω * t / 2)) 0 0 (expS As t)
def PsiInv (ω : ℝ) (As : Matrix Y Y ℝ) (t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  fromBlocks (rot (-(ω * t / 2))) 0 0 (expS As (-t))

@[tmio T, powerlib_foundation] theorem expS_mul_neg (As : Matrix Y Y ℝ) (t : ℝ) :
    expS As t * expS As (-t) = 1 ∧ expS As (-t) * expS As t = 1 := by
  have hc : Commute (t • As) ((-t) • As) := (Commute.refl As).smul_left t |>.smul_right (-t)
  constructor
  · rw [expS, expS, ← Matrix.exp_add_of_commute _ _ hc, ← add_smul, add_neg_cancel, zero_smul,
      NormedSpace.exp_zero]
  · rw [expS, expS, ← Matrix.exp_add_of_commute _ _ hc.symm, ← add_smul, neg_add_cancel,
      zero_smul, NormedSpace.exp_zero]

@[tmio T, powerlib_foundation] theorem psi_mul_inv (ω : ℝ) (As : Matrix Y Y ℝ) (t : ℝ) :
    Psi ω As t * PsiInv ω As t = 1 := by
  rw [Psi, PsiInv, fromBlocks_multiply, TwoToOne.rot_mul_rot_neg, (expS_mul_neg As t).1]
  simp

@[tmio T, powerlib_foundation] theorem hasDerivAt_expS (As : Matrix Y Y ℝ) (t : ℝ) :
    HasDerivAt (expS As) (expS As t * As) t :=
  hasDerivAt_exp_smul_const As t

@[tmio T, powerlib_foundation] theorem expS_comm (As : Matrix Y Y ℝ) (t : ℝ) :
    expS As t * As = As * expS As t :=
  ((Commute.refl As).smul_left t).exp_left.eq

/-- `fromBlocks` with zero off-diagonal blocks as a continuous linear map of the diagonal blocks. -/
def blkDiag : (Matrix (Fin 2) (Fin 2) ℝ × Matrix Y Y ℝ) →L[ℝ] Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => fromBlocks p.1 0 0 p.2
      map_add' := fun p q => by simp [fromBlocks_add]
      map_smul' := fun c p => by simp [fromBlocks_smul] }

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem blkDiag_apply (p : Matrix (Fin 2) (Fin 2) ℝ × Matrix Y Y ℝ) :
    blkDiag p = fromBlocks p.1 0 0 p.2 := rfl

@[tmio T, powerlib_foundation] theorem hasDerivAt_psi (ω : ℝ) (As : Matrix Y Y ℝ) (t : ℝ) :
    HasDerivAt (Psi ω As)
      (fromBlocks ((ω / 2) • (rot (ω * t / 2) * quarter)) 0 0 (expS As t * As)) t := by
  have h := blkDiag.hasFDerivAt.comp_hasDerivAt t
    ((NormalForm.hasDerivAt_rot ω t).prodMk (hasDerivAt_expS As t))
  convert h using 1
  · rfl
  · funext r; simp [Psi, blkDiag_apply]
  · rfl

/-- The standard form in the frame `Ψ`: `ż = ε F_z(t) z`. -/
def Fz (s d ω : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (t : ℝ) :
    Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  fromBlocks (slowFlowMatrix s d 0) 0 0 0 + PsiInv ω As t * modN A ω t * Psi ω As t

/-- `Ψ' + Ψ (ε F_z) = A_ε Ψ`. -/
@[tmio T, powerlib_foundation] theorem psi_frame (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (ε t : ℝ) :
    fromBlocks ((ω / 2) • (rot (ω * t / 2) * quarter)) 0 0 (expS As t * As) +
        Psi ω As t * (ε • Fz s d ω As A t) = fullN s d ω As A ε t * Psi ω As t := by
  have hb : base (ε * s) (ω / 2 - ε * d) = (ω / 2) • quarter + ε • slowFlowMatrix s d 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [base, quarter, slowFlowMatrix] <;> ring
  have hPP : Psi ω As t * (PsiInv ω As t * modN A ω t * Psi ω As t) = modN A ω t * Psi ω As t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, psi_mul_inv, Matrix.one_mul]
  rw [Fz, Matrix.mul_smul, Matrix.mul_add, hPP, fullN, Matrix.add_mul, Matrix.smul_mul]
  have hblk : Psi ω As t * fromBlocks (slowFlowMatrix s d 0) 0 0 0 =
      fromBlocks (rot (ω * t / 2) * slowFlowMatrix s d 0) 0 0 0 := by
    rw [Psi, fromBlocks_multiply]; simp
  have hblk2 : fromBlocks (base (ε * s) (ω / 2 - ε * d)) 0 0 As * Psi ω As t =
      fromBlocks (base (ε * s) (ω / 2 - ε * d) * rot (ω * t / 2)) 0 0 (As * expS As t) := by
    rw [Psi, fromBlocks_multiply]; simp
  rw [hblk, hblk2, smul_add, ← add_assoc, TwoToOne.base_comm_rot, hb, ← expS_comm, fromBlocks_smul, fromBlocks_add]
  simp only [smul_zero, add_zero, Matrix.mul_add, Matrix.mul_smul]

/-- Clamping to `[0, T]`. -/
def clampT (T t : ℝ) : ℝ := max 0 (min t T)

@[tmio T, powerlib_foundation] theorem clampT_of_mem {T t : ℝ} (ht : t ∈ Icc 0 T) : clampT T t = t := by
  rw [clampT, min_eq_left ht.2, max_eq_right ht.1]

@[tmio T, powerlib_foundation] theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampT T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

@[tmio T, powerlib_foundation] theorem continuous_clampT (T : ℝ) : Continuous (clampT T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The standard form frozen outside `[0, T]` (only `[0, T]` enters the monodromy). -/
def Fzc (s d ω T : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (t : ℝ) :
    Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  Fz s d ω As A (clampT T t)

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem continuous_modN (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (ω : ℝ) :
    Continuous (modN A ω) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [modN]
  fun_prop

@[tmio T, powerlib_foundation] theorem continuous_psi (ω : ℝ) (As : Matrix Y Y ℝ) :
    Continuous (Psi ω As) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_psi ω As t).continuousAt

@[tmio T, powerlib_foundation] theorem continuous_expS (As : Matrix Y Y ℝ) : Continuous (expS As) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_expS As t).continuousAt

@[tmio T, powerlib_foundation] theorem continuous_psiInv (ω : ℝ) (As : Matrix Y Y ℝ) :
    Continuous (PsiInv ω As) := by
  have h1 : Continuous fun t : ℝ => rot (-(ω * t / 2)) := by unfold rot; fun_prop
  have h2 : Continuous fun t : ℝ => expS As (-t) := (continuous_expS As).comp continuous_neg
  exact Continuous.matrix_fromBlocks h1 continuous_const continuous_const h2

@[tmio T, powerlib_foundation] theorem continuous_Fz (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) : Continuous (Fz s d ω As A) :=
  continuous_const.add (((continuous_psiInv ω As).mul (continuous_modN A ω)).mul
    (continuous_psi ω As))

@[tmio T, powerlib_foundation] theorem continuous_Fzc (s d ω T : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) : Continuous (Fzc s d ω T As A) :=
  (continuous_Fz s d ω As A).comp (continuous_clampT T)

@[tmio T, powerlib_foundation] theorem exists_bound_Fzc (s d ω : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    ∃ M, 0 ≤ M ∧ ∀ t, ‖Fzc s d ω T As A t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_Fz s d ω As A).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  exact (hM _ (clampT_mem hT t)).trans (le_max_left _ _)

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem continuous_fullN (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (ε : ℝ) : Continuous (fullN s d ω As A ε) :=
  continuous_const.add ((continuous_modN A ω).const_smul ε)

/-- On `[0, T]` the transition matrix of the full system is `Ψ(t)` times that of the frozen
standard form. -/
@[tmio T, powerlib_foundation] theorem transition_fullN (s d ω : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (ε : ℝ) :
    Periodic.transition (fullN s d ω As A ε) T 0 =
      Psi ω As T * Periodic.transition (fun t => ε • Fzc s d ω T As A t) T 0 := by
  have hF : Continuous (fun t => ε • Fzc s d ω T As A t) :=
    (continuous_Fzc s d ω T As A).const_smul ε
  have hA := continuous_fullN s d ω As A ε
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  set Z := fun t => Periodic.transition (fun t => ε • Fzc s d ω T As A t) t 0 with hZ
  have hYs : IsIntegralCurveOn (fun t => Psi ω As t * Z t) (Periodic.matField (fullN s d ω As A ε))
      (uIcc 0 T) := by
    intro r hr
    rw [uIcc_of_le hT] at hr
    have h := (hasDerivAt_psi ω As r).mul (Dynamics.stm_hasDerivAt hF r 0)
    have key : fromBlocks ((ω / 2) • (rot (ω * r / 2) * quarter)) 0 0 (expS As r * As) * Z r +
        Psi ω As r * ((ε • Fzc s d ω T As A r) * Z r) =
        Periodic.matField (fullN s d ω As A ε) r (Psi ω As r * Z r) := by
      rw [Periodic.matField, Fzc, clampT_of_mem hr, ← Matrix.mul_assoc, ← Matrix.add_mul,
        psi_frame, Matrix.mul_assoc]
    rw [key] at h
    exact h.hasDerivWithinAt
  have hu := LinearSystems.stateTransitionMatrix_mul_unique hA (M := B)
    (fun r hr => by rw [uIcc_of_le hT] at hr; exact hB r hr) _
    (hYs.isIntegralSolution (hA.continuousOn.mul hYs.continuousOn)) hYs.continuousOn T
    right_mem_uIcc
  have h0 : Psi ω As 0 * Z 0 = 1 := by
    simp [hZ, Psi, expS, rot, LinearSystems.stateTransitionMatrix_self]
  rw [h0, Matrix.mul_one] at hu
  exact hu.symm

/-! ### Block estimates of the monodromy -/

@[tmio T, powerlib_foundation] theorem norm_submatrix_le {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] (M : Matrix m n ℝ) (f : m' → m) (g : n' ↪ n) :
    ‖M.submatrix f g‖ ≤ ‖M‖ := by
  simp only [linfty_opNorm_def]
  refine NNReal.coe_le_coe.2 (Finset.sup_le fun i _ => ?_)
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (f i)))
  simp only [Matrix.submatrix_apply]
  calc ∑ j, ‖M (f i) (g j)‖₊ = ∑ k ∈ Finset.univ.map g, ‖M (f i) k‖₊ := by rw [Finset.sum_map]
    _ ≤ ∑ k, ‖M (f i) k‖₊ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

@[tmio T, powerlib_foundation] theorem norm_toBlocks_le (M : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    ‖M.toBlocks₁₁‖ ≤ ‖M‖ ∧ ‖M.toBlocks₁₂‖ ≤ ‖M‖ ∧ ‖M.toBlocks₂₁‖ ≤ ‖M‖ ∧ ‖M.toBlocks₂₂‖ ≤ ‖M‖ :=
  ⟨norm_submatrix_le M Sum.inl ⟨Sum.inl, Sum.inl_injective⟩,
    norm_submatrix_le M Sum.inl ⟨Sum.inr, Sum.inr_injective⟩,
    norm_submatrix_le M Sum.inr ⟨Sum.inl, Sum.inl_injective⟩,
    norm_submatrix_le M Sum.inr ⟨Sum.inr, Sum.inr_injective⟩⟩

/-- The `(1,1)` block as a continuous linear map. -/
def blk11 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₁₁
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[tmio T, powerlib_foundation] theorem Fz_toBlocks₁₁ (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (t : ℝ) :
    (Fz s d ω As A t).toBlocks₁₁ = stdForm s d ω A.toBlocks₁₁ t := by
  have hm : modN A ω t = fromBlocks (modReal A.toBlocks₁₁ ω t) (modN A ω t).toBlocks₁₂
      (modN A ω t).toBlocks₂₁ (modN A ω t).toBlocks₂₂ := by
    rw [← fromBlocks_toBlocks (modN A ω t)]
    congr 1
  rw [Fz, PsiInv, Psi, hm, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add, toBlocks_fromBlocks₁₁,
    stdForm]
  simp

/-- The average of the frozen standard form over one period has the slow-flow matrix as its
critical block: `F̄₁₁ = M_slow(s, d, g/2)`, `g = u A₁₁ r̄`. -/
@[tmio T, powerlib_foundation] theorem average_toBlocks₁₁ (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    ((2 * Real.pi / ω)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi / ω),
        Fzc s d ω (2 * Real.pi / ω) As A t).toBlocks₁₁ =
      slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2) := by
  set T := 2 * Real.pi / ω with hT
  have hT0 : 0 < T := by positivity
  have hint : (∫ t in (0 : ℝ)..T, Fzc s d ω T As A t).toBlocks₁₁ =
      ∫ t in (0 : ℝ)..T, stdForm s d ω A.toBlocks₁₁ t := by
    have h := blk11.intervalIntegral_comp_comm
      ((continuous_Fzc s d ω T As A).intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    have h' : (∫ t in (0 : ℝ)..T, blk11 (Fzc s d ω T As A t)) =
        ∫ t in (0 : ℝ)..T, stdForm s d ω A.toBlocks₁₁ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hT0.le] at ht
      show (Fzc s d ω T As A t).toBlocks₁₁ = _
      rw [Fzc, clampT_of_mem ht, Fz_toBlocks₁₁]
    rw [← h']
    exact h.symm
  have hsmul : ∀ (c : ℝ) (M : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ),
      (c • M).toBlocks₁₁ = c • M.toBlocks₁₁ := fun _ _ => rfl
  rw [hsmul, hint, hT, TwoToOne.integral_stdForm s d hω, smul_smul, inv_mul_cancel₀ hT0.ne',
    one_smul]

@[tmio T, powerlib_foundation] theorem norm_average_le {F : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {M T : ℝ} (hT : 0 < T) (hF : ∀ t, ‖F t‖ ≤ M) :
    ‖T⁻¹ • ∫ t in (0 : ℝ)..T, F t‖ ≤ M := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hT.le)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
    (fun t _ => hF t)
  rw [sub_zero, abs_of_pos hT] at h
  calc T⁻¹ * ‖∫ t in (0 : ℝ)..T, F t‖ ≤ T⁻¹ * (M * T) := by gcongr
    _ = M := by field_simp

/-- The monodromy of the full system in blocks: `P = −(I + εT M_slow) + O(ε²)`, `Q, R = O(ε)`,
`S = e^{TA_s} + O(ε)`, `T = 2π/ω`. -/
@[tmio T, powerlib_foundation] theorem monodromy_blocks (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    ∃ C, 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ 1 → ∃ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0 = fromBlocks P Q R S ∧
      ‖P + 1 + (ε * (2 * Real.pi / ω)) •
          slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2)‖ ≤ C * ε ^ 2 ∧
      ‖Q‖ ≤ C * ε ∧ ‖R‖ ≤ C * ε ∧ ‖S - expS As (2 * Real.pi / ω)‖ ≤ C * ε := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨M, hM0, hM⟩ := exists_bound_Fzc s d ω hT.le As A
  set Fbar := T⁻¹ • ∫ t in (0 : ℝ)..T, Fzc s d ω T As A t with hFbar
  have havg : ∫ t in (0 : ℝ)..T, Fzc s d ω T As A t = T • Fbar := by
    rw [hFbar, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  have hFb : ‖Fbar‖ ≤ M := norm_average_le hT hM
  have hF11 : Fbar.toBlocks₁₁ = slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2) :=
    average_toBlocks₁₁ s d hω As A
  set K := M * T * (M * T * (‖(1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)‖ * Real.exp (M * T)))
    with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set C0 := T * M + K with hC0
  have hC00 : 0 ≤ C0 := by positivity
  set e := ‖expS As T‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hCC : C0 ≤ C0 * (1 + e) := le_mul_of_one_le_right hC00 (by linarith)
  have hCe : e * C0 ≤ C0 * (1 + e) := by
    rw [mul_comm e C0]; exact mul_le_mul_of_nonneg_left (by linarith) hC00
  refine ⟨C0 * (1 + e), by positivity, fun ε hε hε1 => ?_⟩
  have hexp := Averaging.monodromy_expansion (continuous_Fzc s d ω T As A) hM hM0 hT.le havg
    hε.le hε1
  set Φz := Periodic.monodromy (fun t => ε • Fzc s d ω T As A t) T 0 with hΦz
  set R2 := Φz - 1 - (ε * T) • Fbar with hR2
  rw [mul_comm] at hexp
  have hR2n : ‖R2‖ ≤ K * ε ^ 2 := hexp
  have hΦzR : Φz = 1 + (ε * T) • Fbar + R2 := by rw [hR2]; abel
  have hpsiT : Psi ω As T = fromBlocks (-1) 0 0 (expS As T) := by
    have h : ω * T / 2 = Real.pi := by rw [hTdef]; field_simp
    rw [Psi, h]
    congr 1
    simp [rot]
  have hmono : Periodic.monodromy (fullN s d ω As A ε) T 0 = fromBlocks (-Φz.toBlocks₁₁)
      (-Φz.toBlocks₁₂) (expS As T * Φz.toBlocks₂₁) (expS As T * Φz.toBlocks₂₂) := by
    rw [Periodic.monodromy, zero_add, transition_fullN s d ω hT.le As A ε, hpsiT]
    have : Periodic.transition (fun t => ε • Fzc s d ω T As A t) T 0 = Φz := by
      rw [hΦz, Periodic.monodromy, zero_add]
    rw [this, ← fromBlocks_toBlocks Φz, fromBlocks_multiply]
    simp
  obtain ⟨b11, b12, b21, b22⟩ := norm_toBlocks_le R2
  obtain ⟨f11, f12, f21, f22⟩ := norm_toBlocks_le Fbar
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have h12 : Φz.toBlocks₁₂ = (ε * T) • Fbar.toBlocks₁₂ + R2.toBlocks₁₂ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₁₂]
  have h21 : Φz.toBlocks₂₁ = (ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₁]
  have h22 : Φz.toBlocks₂₂ = 1 + ((ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂) := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply, add_assoc]
  have h11 : -Φz.toBlocks₁₁ + 1 + (ε * T) • slowFlowMatrix s d
      (Element.pump A.toBlocks₁₁ left right / 2) = -R2.toBlocks₁₁ := by
    rw [hΦzR, ← hF11]
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]; ring
  have hblk : ∀ (Fb Rb : ℝ), Fb ≤ M → Rb ≤ K * ε ^ 2 → ε * T * Fb + Rb ≤ (T * M + K) * ε := by
    intro Fb Rb hFb' hRb
    have h1 : ε * T * Fb ≤ ε * T * M := by
      have : 0 ≤ ε * T := by positivity
      exact mul_le_mul_of_nonneg_left hFb' this
    have h2 : K * ε ^ 2 ≤ K * ε := mul_le_mul_of_nonneg_left hε2 hK0
    nlinarith
  refine ⟨_, _, _, _, hmono, ?_, ?_, ?_, ?_⟩
  · rw [h11, norm_neg]
    refine b11.trans (hR2n.trans ?_)
    have h1 : K * ε ^ 2 ≤ C0 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [hC0]; exact le_add_of_nonneg_left (mul_nonneg hT.le hM0))
        (sq_nonneg ε)
    exact h1.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg ε))
  · rw [h12, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact (hblk _ _ (f12.trans hFb) (b12.trans hR2n)).trans
      (mul_le_mul_of_nonneg_right hCC hε.le)
  · rw [h21]
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁‖ ≤ (T * M + K) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact hblk _ _ (f21.trans hFb) (b21.trans hR2n)
    calc ‖expS As T‖ * ‖(ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁‖ ≤ e * (C0 * ε) :=
          mul_le_mul_of_nonneg_left h he0
      _ = e * C0 * ε := by ring
      _ ≤ C0 * (1 + e) * ε := mul_le_mul_of_nonneg_right hCe hε.le
  · rw [h22, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂‖ ≤ (T * M + K) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact hblk _ _ (f22.trans hFb) (b22.trans hR2n)
    calc ‖expS As T‖ * ‖(ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂‖ ≤ e * (C0 * ε) :=
          mul_le_mul_of_nonneg_left h he0
      _ = e * C0 * ε := by ring
      _ ≤ C0 * (1 + e) * ε := mul_le_mul_of_nonneg_right hCe hε.le

/-! ### First-order averaging for `n` states -/

/-- First-order averaging with a stable remainder, stability: if the slow flow of the critical
pair is exponentially stable (`s > 0`, `|g/2|² < s² + d²`, `g = u A₁₁ r̄`) and the one-period
map of the stable block has spectral radius `ρ(e^{TA_s}) < 1`, every Floquet multiplier of the
complete `n`-state system lies inside the unit circle for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averagingN_stable {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (hs : 0 < s)
    (hg : ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2 < s ^ 2 + d ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
      (Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v =
        μ • v → ‖μ‖ < 1 := by
  obtain ⟨C, hC, hblk⟩ := monodromy_blocks s d hω As A
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have h := block_stable_spec (Y := Y) hT
    (Ms := slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2))
    (by rw [trace_slowFlowMatrix]; linarith) (by rw [det_slowFlowMatrix]; linarith) hρ hC
  filter_upwards [h, eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
  obtain ⟨P, Q, R, S, heq, hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
  rw [heq]
  exact hε P Q R S hP hQ hR hS

/-- First-order averaging with a stable remainder, parametric instability: if the slow flow of the
critical pair has a positive real exponent (`s² + d² < |g/2|²`) and the stable block contracts
over one period, the complete `n`-state system has a real Floquet multiplier below `−1` for all
small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averagingN_unstable {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (hg : s ^ 2 + d ^ 2 < ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fullN s d ω As A ε) (2 * Real.pi / ω) := by
  obtain ⟨C, hC, hblk⟩ := monodromy_blocks s d hω As A
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have h := block_unstable_spec (Y := Y) hT
    (Ms := slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2))
    (by rw [det_slowFlowMatrix]; linarith) hρ hC
  filter_upwards [h, eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
  obtain ⟨P, Q, R, S, heq, hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
  obtain ⟨ρ, hρm, hρ1⟩ := hε P Q R S hP hQ hR hS
  exact ⟨ρ, by rw [heq]; exact hρm, hρ1⟩

end powerlib.ParametricResonance.BlockAveraging
