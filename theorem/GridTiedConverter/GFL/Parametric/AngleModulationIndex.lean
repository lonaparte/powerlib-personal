import theorem.GridTiedConverter.GFL.Parametric.AngleModulationHopf
import theorem.GridTiedConverter.GFL.Parametric.PLLBlock

/-! # GFL converter under a 2:1 grid-angle variation: relative dynamics, Hopf surface and the index

`GFL.Parametric.AngleModulationHopf` gives the Floquet multipliers of the forced orbit at a Hopf
point of the DVC mode. This module completes the remaining steps of the source's argument:
* the relative dynamics about the forced trajectory (p. 19);
* the Hopf surface in closed form;
* the instability index `ε𝒜_m` of pp. 26–27 as the hypothesis of the Floquet theorems;
* the structure of the modulation (pp. 24–25) and the decoupled limit `Γ = 0`.

Model boundary.
* The field `afield` of `GFL.Parametric.AngleModulation` in the absolute PLL angle, at the
  operating point `V₀ sin δ₀ = X_g i_{d0}`, under `θ_g = θ_{g0} + ε cos ω_p t`.
* `relative_dynamics` assumes `A₀` Hurwitz (the forced orbit is then the unique small periodic
  solution); the index theorems assume the Hopf conditions of `AngleModulationHopf`.
* The decay and detuning of the perturbed mode are of order `ε`: `σ_m = −ε Re λ₁` and
  `Δ_m = ε Im λ₁` with `λ₁ = l A₀' r`. This is the distinguished limit in which the source's
  first-order averaging is exact. A fixed decay `σ_m` (independent of `ε`) is outside this module:
  for it the source's `𝒜_m` is a statement about the averaged model only.

Source: slides "Hidden Instability of Grid-Following Converters Under Small Grid Angle
Variations" (KTH, 2026-11-27), pp. 19, 24–27.

Results.
* `smJ_eq_jac` — the variational matrix of the absolute-angle system is the source's `J_p` at
  `η = y − w e₁`, plus `εA₀'`.
* `relative_dynamics` — p. 19: about the forced orbit,
  `F(η_p + ξ) − F(η_p) = [A₀ + ε Re{A₁e^{jω_pt}}]ξ + O(ε²‖ξ‖ + ‖ξ‖²)`, with `A₁ = gA1(z⁽¹⁾(jω_p))`.
* `hopf_point_iff`, `hopf_freq` — the Hopf conditions `a₁ = a₃Ω²`, `a₀ = (a₂ − Ω²)Ω²`,
  `a₂ > Ω²` hold for some `Ω > 0` iff `0 < a₁ < a₃a₂` and `a₁² + a₃²a₀ = a₃a₂a₁` (the Routh
  boundary); then `Ω = √(a₁/a₃)`.
* `index_eq`, `index_lt_one_iff`, `one_lt_index_iff`, `rotating_frame_norm` — pp. 26–27: with
  `σ_m = −ε Re λ₁`, `Δ_m = ε Im λ₁` the index is `ε𝒜_m = |g_m|/(2|λ₁|)` for every `ε > 0`;
  `ε𝒜_m < 1 ⟺ |g_m/2| < |λ₁|` and `ε𝒜_m > 1 ⟺ |λ₁| < |g_m/2|`; the rotating frame preserves
  the modulus.
* `orbit_gfl_index_stable`, `orbit_gfl_index_unstable` — p. 27 as Floquet theorems on the actual
  forced orbit: `ε𝒜_m < 1` (with `Re λ₁ < 0`) gives all multipliers inside the unit circle and
  `ε𝒜_m > 1` gives parametric instability, for all small `ε > 0`.
* `delta_ratio_lt_one_iff` — p. 24: the `(3, 1)` angle part of the pump is the smaller one iff
  `|w₃₁| < tan²δ₀ |w_ik|`.
* `dvc_pll_gains_const` — p. 25: the DVC-to-PLL gains do not depend on the state, so the forced
  trajectory does not modulate them.
* `Dg_decoupled`, `zc_decoupled` — with `Γ = X_g A₃₁ = 0`, `D_GFL = L_PLL · L_dc` and the
  first-order angle response is the PLL transfer `z₁⁽¹⁾ = −s²/L_PLL(s)`.
* `gA1_zc_noload` — at no load (`i_{d0} = 0`) the periodic coefficient matrix `A₁` vanishes.

Corrections.
None. The source's criterion `ε𝒜_m ≶ 1` is proved for the actual system in the distinguished
limit above; for a decay `σ_m` of order one it remains a first-order averaging estimate.

Family and connection conclusions.
* The GFL index criterion is the same `|g/2| ≶ |λ₁|` criterion as the GFM theorems
  (`SmoothForcedOrbit`), applied to the DVC mode coupled to the PLL through `Γ`.
* With `Γ = 0` the GFL angle response reduces to the negative PLL sensitivity
  (`PLLBlock.transfer_pllBlock`), as the GFM droop response `1 − z_δ` is the loop sensitivity
  (`GFM.DroopPump.one_sub_forced_zero`).
-/

noncomputable section
namespace powerlib.GFL.Parametric.AngleModulation
open Complex Matrix Filter Topology Metric
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (matX smJ)
open scoped Matrix.Norms.Operator

namespace Params
variable (p : Params)

/-- The variational matrix of the absolute-angle system is the source's GFL Jacobian `J_p` at the
deviation `η = y − w e₁`, plus `εA₀'`. -/
@[tmio M, powerlib_domain] theorem smJ_eq_jac {ω ε t : ℝ} (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    {y : Fin 4 → ℝ} (hy : 1 + y 2 ≠ 0) :
    smJ p.afield (p.xs, 0) 1 ω A0' ε t y =
      p.jac (p.xs + (y - (ε * Real.cos (ω * t)) • e0)) + ε • A0' := by
  have hq : (p.xs + y, (0 : ℝ) + ε * (1 * Real.cos (ω * t))).1 2 ≠ 0 := by
    simpa [xs, add_comm] using hy
  simp only [ParametricResonance.ForcedOrbit.smJ]
  rw [p.matX_afield hq]
  simp [add_sub_assoc]

/-- The relative dynamics about the forced trajectory (p. 19): along the orbit,
`F(η_p + ξ) − F(η_p) = [A₀ + ε Re{A₁e^{jω_pt}}]ξ + O(ε²‖ξ‖ + ‖ξ‖²)`. -/
@[tmio M, powerlib_domain] theorem relative_dynamics
    (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hA : LinearSystems.IsHurwitz p.A0) {ω : ℝ}
    (hω : 0 < ω) :
    ∃ c K L r ε3, 0 ≤ c ∧ 0 ≤ K ∧ 0 ≤ L ∧ 0 < r ∧ 0 < ε3 ∧ ∀ ε, 0 < ε → ε ≤ ε3 →
      (∃ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (p.afield (p.xs + y t, ε * Real.cos (ω * t))) t) ∧
      ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (p.afield (p.xs + y t, ε * Real.cos (ω * t))) t) →
        ∀ (t : ℝ) (ξ : Fin 4 → ℝ), ‖ξ‖ ≤ r →
          ‖p.afield (p.xs + y t + ξ, ε * Real.cos (ω * t)) -
              p.afield (p.xs + y t, ε * Real.cos (ω * t)) -
            (p.A0 + ε • BlockAveraging.modX (p.gA1 (p.zc (ω * I))) ω t) *ᵥ ξ‖ ≤
            K * ε ^ 2 * ‖ξ‖ + L * ‖ξ‖ ^ 2 := by
  obtain ⟨c, K, ε2, hc, hK, hε2, H⟩ := p.jac_angle_expansion hs hA hω
  have hq0 : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  obtain ⟨R, KL, hR, hKL, hd, hl⟩ :=
    ParametricResonance.ForcedOrbit.exists_lipschitz_ball (p.contDiffAt_afield (n := 2) hq0)
  refine ⟨c, K, KL, R / 3, min ε2 (min (R / (3 * (c + 1))) (1 / (2 * (c + 1)))), hc, hK, hKL,
    by positivity, lt_min hε2 (lt_min (by positivity) (by positivity)), fun ε hε hε' => ?_⟩
  have hε2' : ε ≤ ε2 := hε'.trans (min_le_left _ _)
  have hεR : ε ≤ R / (3 * (c + 1)) := hε'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 / (2 * (c + 1)) := hε'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hex, hJ⟩ := H ε hε hε2'
  refine ⟨hex, fun y hy1 hy2 hy3 t ξ hξ => ?_⟩
  have hce : (c + 1) * ε ≤ R / 3 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * (c + 1))] at hεR
    nlinarith
  set q : (Fin 4 → ℝ) × ℝ := (p.xs + y t, ε * Real.cos (ω * t)) with hqdef
  have hqd : ‖q - (p.xs, 0)‖ ≤ R / 3 := by
    have h1 : ‖y t‖ ≤ (c + 1) * ε := by nlinarith [hy2 t]
    have h2 : ‖ε * Real.cos (ω * t)‖ ≤ (c + 1) * ε := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hε, Real.norm_eq_abs]
      nlinarith [Real.abs_cos_le_one (ω * t)]
    have : q - (p.xs, 0) = (y t, ε * Real.cos (ω * t)) := by
      simp [hqdef]
    rw [this, Prod.norm_def]
    exact max_le (h1.trans hce) (h2.trans hce)
  have hball : ∀ q' ∈ closedBall q ‖ξ‖, q' ∈ closedBall (p.xs, (0 : ℝ)) R := by
    intro q' hq'
    rw [mem_closedBall, dist_eq_norm] at hq' ⊢
    calc ‖q' - (p.xs, 0)‖ ≤ ‖q' - q‖ + ‖q - (p.xs, 0)‖ := by
          rw [← sub_add_sub_cancel q' q (p.xs, 0)]; exact norm_add_le _ _
      _ ≤ R / 3 + R / 3 := add_le_add (hq'.trans hξ) hqd
      _ ≤ R := by linarith
  have hqball : q ∈ closedBall (p.xs, (0 : ℝ)) R := hball q (mem_closedBall_self (norm_nonneg _))
  have ht := ParametricResonance.ForcedOrbit.taylor_sub hKL
    (fun q' hq' => hd q' (hball q' hq'))
    (fun q' hq' => hl q' (hball q' hq') q hqball) le_rfl
    (q1 := q + (ξ, 0)) (q2 := q)
    (by simp) (by simp)
  have hm := ParametricResonance.ForcedOrbit.matX_mulVec p.afield q ξ
  have hy2' : |y t 2| < 1 := by
    have h1 : |y t 2| ≤ ‖y t‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (y t) 2
    have h2 : c * ε < 1 := by
      calc c * ε ≤ c * (1 / (2 * (c + 1))) := by gcongr
        _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
    linarith [hy2 t]
  have hne : q.1 2 ≠ 0 := by
    have hx2 : p.xs 2 = 1 := rfl
    show p.xs 2 + y t 2 ≠ 0
    rw [hx2]
    intro h
    have : y t 2 = -1 := by linarith
    rw [this] at hy2'
    norm_num at hy2'
  rw [p.matX_afield hne] at hm
  have hJt := hJ y hy1 hy2 hy3 t
  have e1 : q.1 - q.2 • e0 = p.xs + (y t - (ε * Real.cos (ω * t)) • e0) := by
    simp [hqdef, add_sub_assoc]
  rw [e1] at hm
  have e2 : q + (ξ, 0) = (p.xs + y t + ξ, ε * Real.cos (ω * t)) := by simp [hqdef]
  rw [add_sub_cancel_left, ParametricResonance.ForcedOrbit.norm_prod_zero, ← hm, e2] at ht
  set Jq := p.jac (p.xs + (y t - (ε * Real.cos (ω * t)) • e0))
  have key : p.afield (p.xs + y t + ξ, ε * Real.cos (ω * t)) -
      p.afield (p.xs + y t, ε * Real.cos (ω * t)) -
      (p.A0 + ε • BlockAveraging.modX (p.gA1 (p.zc (ω * I))) ω t) *ᵥ ξ =
      (p.afield (p.xs + y t + ξ, ε * Real.cos (ω * t)) - p.afield q - Jq *ᵥ ξ) +
        (Jq - p.A0 - ε • BlockAveraging.modX (p.gA1 (p.zc (ω * I))) ω t) *ᵥ ξ := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec]
    abel
  rw [key]
  calc _ ≤ ‖p.afield (p.xs + y t + ξ, ε * Real.cos (ω * t)) - p.afield q - Jq *ᵥ ξ‖ +
        ‖(Jq - p.A0 - ε • BlockAveraging.modX (p.gA1 (p.zc (ω * I))) ω t) *ᵥ ξ‖ :=
        norm_add_le _ _
    _ ≤ KL * ‖ξ‖ * ‖ξ‖ + K * ε ^ 2 * ‖ξ‖ := by
        gcongr
        exact (Matrix.linfty_opNorm_mulVec _ _).trans (by gcongr)
    _ = K * ε ^ 2 * ‖ξ‖ + KL * ‖ξ‖ ^ 2 := by ring

/-! ### The Hopf surface and the instability index -/

/-- The Hopf conditions solved: the DVC mode sits at a Hopf point `±jΩ` of `A₀` with the other
two modes stable exactly on the Routh boundary `a₁² + a₃²a₀ = a₃a₂a₁` with `0 < a₁ < a₃a₂`. -/
@[tmio M, powerlib_domain] theorem hopf_point_iff (h3 : 0 < p.da3) :
    (∃ Ω : ℝ, 0 < Ω ∧ p.da1 = p.da3 * Ω ^ 2 ∧ p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2 ∧
      0 < p.da2 - Ω ^ 2) ↔
      0 < p.da1 ∧ p.da1 < p.da3 * p.da2 ∧
        p.da1 ^ 2 + p.da3 ^ 2 * p.da0 = p.da3 * p.da2 * p.da1 := by
  constructor
  · rintro ⟨Ω, hΩ, hA, hB, hq⟩
    refine ⟨by rw [hA]; positivity, by rw [hA]; nlinarith, ?_⟩
    rw [hA, hB]; ring
  · rintro ⟨h1, h2, hD⟩
    have hr : 0 < p.da1 / p.da3 := div_pos h1 h3
    refine ⟨Real.sqrt (p.da1 / p.da3), Real.sqrt_pos.2 hr, ?_, ?_, ?_⟩
    · rw [Real.sq_sqrt hr.le]; field_simp
    · rw [Real.sq_sqrt hr.le]
      field_simp
      linear_combination hD
    · rw [Real.sq_sqrt hr.le, sub_pos, div_lt_iff₀ h3]
      linarith

/-- The Hopf frequency is `Ω = √(a₁/a₃)`. -/
@[tmio M, powerlib_domain] theorem hopf_freq (h3 : 0 < p.da3) {Ω : ℝ} (hΩ : 0 < Ω)
    (hA : p.da1 = p.da3 * Ω ^ 2) : Ω = Real.sqrt (p.da1 / p.da3) := by
  rw [hA, mul_div_cancel_left₀ _ h3.ne', Real.sqrt_sq hΩ.le]

end Params

/-- The source's index `ε𝒜_m` with the decay `σ_m = −ε Re λ₁` and the detuning
`Δ_m = ε Im λ₁` of the perturbed mode (`λ₁ = l A₀' r`) does not depend on `ε > 0`:
`ε𝒜_m = |g_m|/(2|λ₁|)`. -/
@[tmio T, powerlib_foundation] theorem index_eq {g l1 : ℂ} {ε : ℝ} (hε : 0 < ε) :
    ε * (‖g‖ / (2 * Real.sqrt ((-(ε * l1.re)) ^ 2 + (ε * l1.im) ^ 2))) = ‖g‖ / (2 * ‖l1‖) := by
  have hs : Real.sqrt ((-(ε * l1.re)) ^ 2 + (ε * l1.im) ^ 2) = ε * ‖l1‖ := by
    rw [show (-(ε * l1.re)) ^ 2 + (ε * l1.im) ^ 2 = ε ^ 2 * (l1.re * l1.re + l1.im * l1.im) by
      ring, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le, Complex.norm_def,
      Complex.normSq_apply]
  rw [hs]
  by_cases h : ‖l1‖ = 0
  · simp [h]
  · field_simp

/-- `ε𝒜_m < 1 ⟺ |g_m/2| < |λ₁|`: the source's criterion is the hypothesis of the Floquet
theorems. -/
@[tmio T, powerlib_foundation] theorem index_lt_one_iff {g l1 : ℂ} (hl1 : l1 ≠ 0) :
    ‖g‖ / (2 * ‖l1‖) < 1 ↔ ‖g / 2‖ ^ 2 < ‖l1‖ ^ 2 := by
  have hn : 0 < ‖l1‖ := norm_pos_iff.2 hl1
  rw [div_lt_one (by positivity), norm_div, Complex.norm_two]
  constructor
  · intro h
    have : ‖g‖ / 2 < ‖l1‖ := by linarith
    exact pow_lt_pow_left₀ this (by positivity) two_ne_zero
  · intro h
    have := lt_of_pow_lt_pow_left₀ 2 hn.le h
    linarith

/-- `ε𝒜_m > 1 ⟺ |λ₁| < |g_m/2|`. -/
@[tmio T, powerlib_foundation] theorem one_lt_index_iff {g l1 : ℂ} (hl1 : l1 ≠ 0) :
    1 < ‖g‖ / (2 * ‖l1‖) ↔ ‖l1‖ ^ 2 < ‖g / 2‖ ^ 2 := by
  have hn : 0 < ‖l1‖ := norm_pos_iff.2 hl1
  rw [one_lt_div (by positivity), norm_div, Complex.norm_two]
  constructor
  · intro h
    have : ‖l1‖ < ‖g‖ / 2 := by linarith
    exact pow_lt_pow_left₀ this hn.le two_ne_zero
  · intro h
    have := lt_of_pow_lt_pow_left₀ 2 (by positivity) h
    linarith

/-- The rotating frame `q = c e^{jω_pt/2}` preserves the modulus, hence the growth rates. -/
@[tmio T, powerlib_foundation] theorem rotating_frame_norm (c : ℂ) (ω t : ℝ) :
    ‖c * Complex.exp (((ω * t / 2 : ℝ) : ℂ) * I)‖ = ‖c‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- p. 24: the `(3, 1)` angle part is the smaller one exactly when `|w₃₁| < tan²δ₀ |w_ik|`. -/
@[tmio M, powerlib_domain] theorem delta_ratio_lt_one_iff {δ0 : ℝ} (hsn : Real.sin δ0 ≠ 0)
    (hcs : Real.cos δ0 ≠ 0) {z1 w31 w r1 rk : ℂ} (hz : z1 ≠ 0) (hw : w ≠ 0) (hr1 : r1 ≠ 0)
    (hrk : rk ≠ 0) :
    ‖(Real.cot δ0 : ℂ) * z1 * (star r1 / r1) * w31‖ /
        ‖(-(Real.tan δ0 : ℂ)) * z1 * (star rk / rk) * w‖ < 1 ↔
      ‖w31‖ < |Real.tan δ0| ^ 2 * ‖w‖ := by
  rw [delta_ratio hsn hcs hz hw hr1 hrk]
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have ht : |Real.tan δ0| = (|Real.cot δ0|)⁻¹ := by
    rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, abs_div, abs_div, inv_div]
  have hct : 0 < |Real.cot δ0| := by
    rw [Real.cot_eq_cos_div_sin]; exact abs_pos.2 (div_ne_zero hcs hsn)
  rw [ht, div_lt_one hw', inv_pow, ← div_eq_inv_mul, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

namespace Params
variable (p : Params)

/-- p. 25: the DVC-to-PLL gains `∂(δ̇, ξ̇_PLL)/∂(v_dc, ξ_DVC)` are the same at every state, so the
periodic trajectory does not modulate them; `(3, 1)` is the `δ → v̇_dc` gain. -/
@[tmio M, powerlib_domain] theorem dvc_pll_gains_const (x : Fin 4 → ℝ) (z : Fin 4 → ℂ) :
    p.jac x 0 2 = p.A0 0 2 ∧ p.jac x 0 3 = p.A0 0 3 ∧ p.jac x 1 2 = p.A0 1 2 ∧
      p.jac x 1 3 = p.A0 1 3 ∧ p.gA1 z 0 2 = 0 ∧ p.gA1 z 0 3 = 0 ∧ p.gA1 z 1 2 = 0 ∧
      p.gA1 z 1 3 = 0 := by
  simp [jac, A0, gA1]

/-- Without the PLL–DVC loop gain `Γ = X_g A₃₁` the characteristic polynomial splits into the PLL
loop `s² + k_p v_{d0} s + k_i v_{d0}` and the dc loop `L_dc`. -/
@[tmio M, powerlib_domain] theorem Dg_decoupled (hG : p.Gam = 0) (s : ℂ) :
    p.Dg s = (s ^ 2 + p.kp * p.vd0 * s + p.ki * p.vd0) * p.Ldc s := by
  simp [Dg, hG]

/-- p. 27 as a Floquet theorem: at the Hopf point, with the decay and detuning `ελ₁`
(`Re λ₁ < 0`), `ε𝒜_m = |g_m|/(2|λ₁|) < 1` gives, for all small `ε > 0`, the forced orbit with all
Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_index_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hidx : ‖p.gleft (Ω * I) ⬝ᵥ (p.gA1 (p.zc (((2 * Ω : ℝ) : ℂ) * I)) *ᵥ
        star (p.gright (Ω * I)))‖ /
      (2 * ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖) < 1) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ p.afield (p.xs, 0) 1 (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hl1 : p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I)) ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  exact p.orbit_gfl_hopf_stable hsd hΩ hC hki hL hA hB h3 hq A0' hs
    ((index_lt_one_iff hl1).1 hidx)

/-- p. 27 as a Floquet theorem: `ε𝒜_m = |g_m|/(2|λ₁|) > 1` gives parametric instability of the
forced orbit for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_index_unstable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hl1 : p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I)) ≠ 0)
    (hidx : 1 < ‖p.gleft (Ω * I) ⬝ᵥ (p.gA1 (p.zc (((2 * Ω : ℝ) : ℂ) * I)) *ᵥ
        star (p.gright (Ω * I)))‖ /
      (2 * ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖)) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.afield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε * (1 * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ p.afield (p.xs, 0) 1 (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) :=
  p.orbit_gfl_hopf_unstable hsd hΩ hC hki hL hA hB h3 hq A0' ((one_lt_index_iff hl1).1 hidx)

/-- Without the PLL–DVC coupling (`Γ = 0`) the first-order angle response is the transfer of the
frozen PLL block, `z₁⁽¹⁾ = −s²/L_PLL(s)` (`PLLBlock.transfer_pllBlock`): the relative-angle
response is the negative PLL sensitivity. -/
@[tmio M, powerlib_domain] theorem zc_decoupled (hG : p.Gam = 0) {s : ℂ} (hL : p.Ldc s ≠ 0)
    (hP : PLLBlock.LPLL p.vd0 p.kp p.ki s ≠ 0) :
    p.zc s 0 = Linear.transfer (PLLBlock.pllBlock p.vd0 p.kp p.ki) s 0 0 := by
  rw [PLLBlock.transfer_pllBlock _ _ _ hP]
  simp only [zc, Matrix.cons_val_zero, p.Dg_decoupled hG]
  simp only [PLLBlock.LPLL, PLL.loopPoly] at hP ⊢
  field_simp

/-- At no load (`i_{d0} = 0`) the angle variation does not reach the dc loop (`A₃₁ = 0`, so
`z₃ = z₄ = 0`), and the periodic coefficient matrix vanishes: `A₁ = 0`. -/
@[tmio M, powerlib_domain] theorem gA1_zc_noload (h : p.id0 = 0) (s : ℂ) :
    p.gA1 (p.zc s) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gA1, zc, A31, b1, b3, b4, ih, vh, h]

end Params
end powerlib.GFL.Parametric.AngleModulation
