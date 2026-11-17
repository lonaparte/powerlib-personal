import theorem.GridTiedConverter.GFL.RatePLL
import theorem.Dynamics.Calculus
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.Dynamics.Degenerate.WeakFocus

/-! # Rate-coupled GFL PLL at the boundary angle: Hopf normal form

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold: `theorem/Transform/CurrentDirection.agda`.

Model boundary.
The model of `theorem/GridTiedConverter/GFL/RatePLL.lean`, unchanged: a single
grid-following converter on an infinite bus of amplitude `V` behind a lossless inductive line
`X_g = ω_s L_g`; three-phase balanced averaged dq model in the PLL frame, continuous time. States,
in order: `θ` (PLL error angle), `x` (PLL integrator). Ideal current loop with the d-axis current
`i_d` (into the converter) a frozen parameter, `I_q = 0`; the only line dynamics kept is the
speed-EMF coupling `−L_g u i_d`, `v_q = −V sin θ − X_g i_d − L_g u i_d`; SRF-PLL
`u = k_p v_q + k_i x`, `D₀ = 1 + k_p L_g i_d`. No PWM, delay,
limiter, dc link, outer loop, line resistance or `L_f`. Every parameter is an arbitrary real, as
in `RatePLL.family`. All statements are local, about the full nonlinear field translated to the
selected point `(θ*, 0)` (`RatePLL.Model.field`).

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (推论二 `tan θ_H`, 推论五 GFL 速率耦合 Hopf 全参数亚临界,
lyap1 网格); model `GFLRate` in `.../archive/simulation/src/gfl_gfm_contrast_sim/models.py`.
Normal form and `κ` derived in SymPy (Kuznetsov's planar `l₁` formula cross-checked numerically).

Results.
Normal form (static). Write `A = V cos θ*`, `B = V sin θ*`, `b = −L_g i_d`, `α = k_i/D₀`,
`β = k_p/D₀`, `φ = θ − θ*`, `w = x − b φ` and `N(φ) = A(φ − sin φ) + B(1 − cos φ)` (`hopfN`). At a
balanced point the corrected integrator obeys `ẇ = −Aφ + N(φ)` exactly, and on the boundary
`tr J = 0` (i.e. `k_i b = k_p A`, the angle `tan θ* = ω_s k_p/k_i` of `RatePLL`) the angle obeys
`φ̇ = αw + βN(φ)`: a sinusoidal Liénard system with `det J = αA > 0`. The normal-form
polynomials and their identities are generic, in `Dynamics.Degenerate`
(`theorem/Dynamics/Degenerate/WeakFocus.lean`):
* `hopf_lie_poly`: for the explicit polynomial `hopfW` (quadratic part `(φ² + (α/A) w²)/2`, six
  cubic/quartic monomials) the derivative along the cubic truncation `N₃ = Bφ²/2 + Aφ³/6` is
  `−κ (φ² + (α/A) w²)²` plus eight monomials of degree five and six, with
  `κ = −β(A² + B²)/(16A) = −k_p V²/(16 D₀ V cos θ*)` (`hopfκ`; first Lyapunov quantity, computed in
  SymPy and checked here by `field_simp; ring`).
* `hopfN_sub_hopfN3_isBigO`: `N − N₃ = O(φ⁴)` (Mathlib's `Real.sin_bound`, `Real.cos_bound`).
* `hasFDerivAt_lyapPoly`, `contDiff_lyapPoly`: derivative and smoothness of the polynomial in the
  coordinates `(φ, w)`.
* The stability laws of a `C¹` field in this normal form (generic, same module):
  `localAsymptoticStable_of_sineLienard` (`κ > 0`), `unstable_of_sineLienard` (`κ < 0`, Chetaev)
  and `not_localAsymptoticStable_of_sineLienard_conservative` (`β = 0`, conserved energy).
Since `α/A = det J/A² > 0`, `κ > 0 ⇔ k_p k_i < 0`.

Family and connection conclusions.
* `mem_den_locallyAsymptoticallyStable_of_hopf`: on the boundary (balanced, `D₀ ≠ 0`, `tr J = 0`,
  `det J > 0`) with `k_p k_i < 0` the point is locally asymptotically stable — a supercritical
  Hopf point, decided by `hopfW` (`Dynamics.Degenerate.localAsymptoticStable_of_sineLienard`).
* `mem_den_unstable_of_hopf`: on the boundary with `k_p k_i > 0` it is unstable (subcritical;
  Chetaev with the same polynomial, `Dynamics.Degenerate.unstable_of_sineLienard`).
* `mem_den_unstable_of_tan_eq`: with physical gains (`V, k_p, k_i, ω_s > 0`, `D₀ > 0`,
  `cos θ > 0`) the point exactly at the boundary angle `tan θ = ω_s k_p/k_i` is unstable;
  `mem_den_locallyAsymptoticallyStable_iff_tan_lt`: with physical gains the point is locally
  asymptotically stable iff `tan θ < ω_s k_p/k_i`.
* `mem_den_locallyAsymptoticallyStable_iff`: **complete membership** — locally asymptotically
  stable iff balanced with `D₀ ≠ 0`, `det J > 0` and (`tr J < 0` or (`tr J = 0` and
  `k_p k_i < 0`)). The remaining cases fail: non-equilibrium (unstable); `D₀ = 0` (frozen angle);
  `det J < 0` or `tr J > 0` (linear instability); `det J = 0` (a line of equilibria for `k_i = 0`
  or `V = 0`, `Dynamics.not_localAsymptoticStable_of_line`; the fold `cos θ* = 0`, where
  `x + L_g i_d θ` is monotone along the flow, `ẇ = V sin θ*(1 − cos φ)`); `tr J = 0` with `k_p = 0`
  (conserved energy `α w²/2 + A(1 − cos φ) − B(φ − sin φ)`) or `k_p k_i > 0` (subcritical).
* `not_exact_locallyAsymptoticallyStable`: the local asymptotic translation of `RatePLL.family`
  (`{equilibrium, jacobianStable}`) is **not exact**. Witness `supercriticalPLL`
  (`V = √2`, `X_g = ω_s = 1`, `k_p = −1/2`, `k_i = 1/2`, `i_d = 1`, `θ* = −π/4`; `D₀ = 1/2`,
  `tr J = 0`, `det J = 1`), locally asymptotically stable
  (`supercriticalPLL_mem_den_locallyAsymptoticallyStable`) with a trace-zero Jacobian.

Scope note: the source's numerical finding that the rate-coupled Hopf is subcritical over its whole
(physical) parameter grid is proved here for every `k_p k_i > 0`; it does not extend to gains of
opposite signs, which give a supercritical boundary.
-/

noncomputable section
namespace powerlib.GFL.RatePLL
open Filter Topology Asymptotics
open powerlib.Dynamics.Degenerate (hopfN hopfκ localAsymptoticStable_of_sineLienard
  unstable_of_sineLienard not_localAsymptoticStable_of_sineLienard_conservative)

/-! ## The rate-coupled PLL at the boundary angle -/

section Boundary

@[tmio M, powerlib_domain] private theorem gridQ_shift (p : Params) {θ : ℝ} (heq : p.V * Real.sin θ = -(p.Xg * p.Id))
    (φ : ℝ) : gridQ p (φ + θ) =
      -(p.V * Real.cos θ) * φ + hopfN (p.V * Real.cos θ) (p.V * Real.sin θ) φ := by
  unfold gridQ hopfN
  rw [Real.sin_add]
  linear_combination -heq

@[tmio M, powerlib_domain] private theorem model_field0 (m : Model) (z : Dynamics.State 2) :
    m.field z 0 = (m.params.kp * gridQ m.params (z 0 + m.θ) + m.params.ki * z 1) / m.params.D0 := by
  simp [Model.field, RatePLL.field, Dynamics.lift, coordField, equilibrium, pllOut]

@[tmio M, powerlib_domain] private theorem model_field1 (m : Model) (z : Dynamics.State 2) :
    m.field z 1 = gridQ m.params (z 0 + m.θ) - m.params.Lg * m.field z 0 * m.params.Id := by
  simp [Model.field, RatePLL.field, Dynamics.lift, coordField, equilibrium, pllOut, vq]

/-- `ẇ = ḣ`: the PLL integrator corrected by the speed-EMF term, `w = x + L_g i_d θ`, is driven by
the grid q-voltage alone. -/
@[tmio M, powerlib_domain] private theorem model_hg1 {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (z : Dynamics.State 2) :
    m.field z 1 - -(m.params.Lg * m.params.Id) * m.field z 0 =
      -(m.params.V * Real.cos m.θ) * z 0 +
        hopfN (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ) (z 0) := by
  rw [model_field1, ← gridQ_shift m.params heq]
  ring

/-- On the boundary (`tr J = 0`) the angle equation is `θ̇ = α w + β N(φ)`. -/
@[tmio M, powerlib_domain] private theorem model_hg0 {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id))
    (hD0 : m.params.D0 ≠ 0) (htr : (jac m.params m.θ).trace = 0) (z : Dynamics.State 2) :
    m.field z 0 = m.params.ki / m.params.D0 * (z 1 - -(m.params.Lg * m.params.Id) * z 0) +
      m.params.kp / m.params.D0 *
        hopfN (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ) (z 0) := by
  have htr' : -m.params.kp * m.params.V * Real.cos m.θ - m.params.ki * m.params.Lg * m.params.Id
      = 0 := by
    rw [trace_jac, div_eq_zero_iff] at htr
    exact htr.resolve_right hD0
  rw [model_field0, gridQ_shift m.params heq]
  field_simp
  linear_combination (z 0) * htr'

/-- `A = V cos θ ≠ 0` on the boundary (`det J > 0`). -/
@[tmio M, powerlib_domain] private theorem model_Vcos_ne_zero {m : Model}
    (hD0 : m.params.D0 ≠ 0) (hdet : 0 < (jac m.params m.θ).det) :
    m.params.V * Real.cos m.θ ≠ 0 := by
  rw [det_jac m.params hD0] at hdet
  intro h
  rw [mul_assoc, h, mul_zero, zero_div] at hdet
  exact lt_irrefl 0 hdet

/-- `α = k_i / D₀ ≠ 0` on the boundary (`det J > 0`). -/
@[tmio M, powerlib_domain] private theorem model_kiD0_ne_zero {m : Model}
    (hD0 : m.params.D0 ≠ 0) (hdet : 0 < (jac m.params m.θ).det) :
    m.params.ki / m.params.D0 ≠ 0 := by
  rw [det_jac m.params hD0] at hdet
  intro h
  have : m.params.ki = 0 := by
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hD0
  rw [this, zero_mul, zero_mul, zero_div] at hdet
  exact lt_irrefl 0 hdet

/-- `α / A = det J / A² > 0` on the boundary. -/
@[tmio M, powerlib_domain] private theorem model_ratio_pos {m : Model} (hD0 : m.params.D0 ≠ 0)
    (hdet : 0 < (jac m.params m.θ).det) :
    0 < m.params.ki / m.params.D0 / (m.params.V * Real.cos m.θ) := by
  have hA := model_Vcos_ne_zero hD0 hdet
  rw [det_jac m.params hD0] at hdet
  have : m.params.ki / m.params.D0 / (m.params.V * Real.cos m.θ) =
      m.params.ki * m.params.V * Real.cos m.θ / m.params.D0 /
        (m.params.V * Real.cos m.θ) ^ 2 := by
    field_simp
  rw [this]
  positivity

/-- The sign of the normal-form coefficient for gains of opposite signs:
`k_p k_i < 0 → κ > 0`. -/
@[tmio M, powerlib_domain] private theorem model_kappa_pos {m : Model} (hD0 : m.params.D0 ≠ 0)
    (hdet : 0 < (jac m.params m.θ).det) :
    m.params.kp * m.params.ki < 0 →
      0 < hopfκ (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ)
        (m.params.kp / m.params.D0) := by
  have hA := model_Vcos_ne_zero hD0 hdet
  have hq := model_ratio_pos hD0 hdet
  set A := m.params.V * Real.cos m.θ
  set B := m.params.V * Real.sin m.θ
  have hAB : 0 < A ^ 2 + B ^ 2 := by positivity
  have hκ : hopfκ A B (m.params.kp / m.params.D0) =
      -(A ^ 2 + B ^ 2) / 16 * (m.params.kp / m.params.D0 / A) := by
    unfold hopfκ; field_simp
  have hprod : m.params.kp / m.params.D0 / A * (m.params.ki / m.params.D0 / A) =
      m.params.kp * m.params.ki / (m.params.D0 * A) ^ 2 := by
    field_simp
  have hDA : 0 < (m.params.D0 * A) ^ 2 := by positivity
  rw [hκ]
  intro hk
  have h1 : m.params.kp / m.params.D0 / A * (m.params.ki / m.params.D0 / A) < 0 := by
    rw [hprod]; exact div_neg_of_neg_of_pos hk hDA
  have h2 : m.params.kp / m.params.D0 / A < 0 := by
    by_contra hc; push Not at hc; nlinarith
  have h3 : -(A ^ 2 + B ^ 2) / 16 < 0 := by linarith
  nlinarith

/-- The sign of the normal-form coefficient for gains of equal signs:
`k_p k_i > 0 → κ < 0`. -/
@[tmio M, powerlib_domain] private theorem model_kappa_neg {m : Model} (hD0 : m.params.D0 ≠ 0)
    (hdet : 0 < (jac m.params m.θ).det) :
    0 < m.params.kp * m.params.ki →
      hopfκ (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ)
        (m.params.kp / m.params.D0) < 0 := by
  have hA := model_Vcos_ne_zero hD0 hdet
  have hq := model_ratio_pos hD0 hdet
  set A := m.params.V * Real.cos m.θ
  set B := m.params.V * Real.sin m.θ
  have hAB : 0 < A ^ 2 + B ^ 2 := by positivity
  have hκ : hopfκ A B (m.params.kp / m.params.D0) =
      -(A ^ 2 + B ^ 2) / 16 * (m.params.kp / m.params.D0 / A) := by
    unfold hopfκ; field_simp
  have hprod : m.params.kp / m.params.D0 / A * (m.params.ki / m.params.D0 / A) =
      m.params.kp * m.params.ki / (m.params.D0 * A) ^ 2 := by
    field_simp
  have hDA : 0 < (m.params.D0 * A) ^ 2 := by positivity
  rw [hκ]
  intro hk
  have h1 : 0 < m.params.kp / m.params.D0 / A * (m.params.ki / m.params.D0 / A) := by
    rw [hprod]; exact div_pos hk hDA
  have h2 : 0 < m.params.kp / m.params.D0 / A := by
    by_contra hc; push Not at hc; nlinarith
  have h3 : -(A ^ 2 + B ^ 2) / 16 < 0 := by linarith
  nlinarith

end Boundary

/-! ## Members of the local asymptotic denotation -/

section Members

/-- An equilibrium of the translated field with a nondegenerate loop is balanced. -/
@[tmio M, powerlib_domain] private theorem balance_of_model_field_zero {m : Model} (h : m.field 0 = 0) :
    m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id) := by
  have h0 := congrArg (fun y : Dynamics.State 2 => y 0) h
  have h1 := congrArg (fun y : Dynamics.State 2 => y 1) h
  simp only [PiLp.zero_apply] at h0 h1
  rw [model_field1, h0] at h1
  simp only [PiLp.zero_apply, zero_add, mul_zero, zero_mul, sub_zero] at h1
  unfold gridQ at h1
  linarith

/-- With a degenerate loop `D₀ = 0` the angle is frozen. -/
@[tmio TM, powerlib_domain] private theorem not_las_of_D0_eq_zero {m : Model} (hD0 : m.params.D0 = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change ¬ LocalAsymptoticStable m.field 0
  have hd : ∀ z : Dynamics.State 2, HasFDerivAt (fun z : Dynamics.State 2 => -(z 0))
      (-(PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ)) z := fun z =>
    ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)).neg
  refine Dynamics.not_localAsymptoticStable_of_eventually_lie_nonpos m.field_contDiff
    (fun z => (hd z).differentiableAt) (Eventually.of_forall fun z => ?_)
    (Dynamics.frequently_of_forall_smul (EuclideanSpace.single 0 1) fun t ht => ?_)
  · rw [(hd z).fderiv]
    simp [model_field0, hD0]
  · simp [ht]

/-- A singular Jacobian (`det J = 0`) at a balanced point with `D₀ ≠ 0`: no local asymptotic
stability (a line of equilibria for `k_i = 0` or `V = 0`, the fold `cos θ* = 0` otherwise). -/
@[tmio TM, powerlib_domain] private theorem not_las_of_det_eq_zero {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (hdet : (jac m.params m.θ).det = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change ¬ LocalAsymptoticStable m.field 0
  rw [det_jac m.params hD0, div_eq_zero_iff] at hdet
  have hkvc : m.params.ki * m.params.V * Real.cos m.θ = 0 := hdet.resolve_right hD0
  have hq0 : gridQ m.params m.θ = 0 := by unfold gridQ; linarith
  by_cases hV : m.params.V = 0
  · -- `V = 0`: the line `x = 0` of equilibria
    have hq : ∀ φ, gridQ m.params φ = 0 := fun φ => by
      unfold gridQ; rw [hV] at heq ⊢; linarith
    refine Dynamics.not_localAsymptoticStable_of_line (v := EuclideanSpace.single 0 1) (by simp)
      fun t _ => ?_
    have h0 : m.field (0 + t • EuclideanSpace.single 0 1) 0 = 0 := by
      rw [model_field0]; simp [hq]
    ext i
    fin_cases i
    · simpa using h0
    · simp only [Fin.mk_one, PiLp.zero_apply]
      rw [model_field1, h0]; simp [hq]
  by_cases hki : m.params.ki = 0
  · -- `k_i = 0`: the line `θ = θ*` of equilibria
    refine Dynamics.not_localAsymptoticStable_of_line (v := EuclideanSpace.single 1 1) (by simp)
      fun t _ => ?_
    have h0 : m.field (0 + t • EuclideanSpace.single 1 1) 0 = 0 := by
      rw [model_field0]; simp [hki, hq0]
    ext i
    fin_cases i
    · simpa using h0
    · simp only [Fin.mk_one, PiLp.zero_apply]
      rw [model_field1, h0]; simp [hq0]
  -- the fold `cos θ* = 0`: `w = x + L_g i_d θ` is monotone, `ẇ = V sin θ* (1 − cos φ)`
  have hc : Real.cos m.θ = 0 := by
    rcases mul_eq_zero.mp hkvc with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hki
      · exact absurd h hV
    · exact h
  set B := m.params.V * Real.sin m.θ with hB
  set b := -(m.params.Lg * m.params.Id) with hb
  have hBne : B ≠ 0 := by
    intro h
    have hs : Real.sin m.θ = 0 := (mul_eq_zero.mp h).resolve_left hV
    have := Real.sin_sq_add_cos_sq m.θ
    rw [hs, hc] at this
    norm_num at this
  have hd : ∀ z : Dynamics.State 2, HasFDerivAt (fun z : Dynamics.State 2 => -B * (z 1 - b * z 0))
      ((-B) • ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : Dynamics.State 2 →L[ℝ] ℝ) -
        b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ))) z := fun z => by
    have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
    have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
    exact ((h1.sub (h0.const_mul b)).const_mul (-B)).congr_fderiv (by ext v; simp)
  refine Dynamics.not_localAsymptoticStable_of_eventually_lie_nonpos m.field_contDiff
    (fun z => (hd z).differentiableAt) (Eventually.of_forall fun z => ?_)
    (Dynamics.frequently_of_forall_smul (EuclideanSpace.single 1 B) fun t ht => ?_)
  · rw [(hd z).fderiv]
    have h1 := model_hg1 heq z
    rw [hc, mul_zero, neg_zero, zero_mul, zero_add] at h1
    have hcos := Real.cos_le_one (z 0)
    simp only [smul_apply, sub_apply, PiLp.proj_apply, smul_eq_mul]
    rw [h1]
    unfold hopfN
    nlinarith [sq_nonneg B]
  · simp only [PiLp.zero_apply, mul_zero, sub_zero]
    simp
    nlinarith [sq_pos_of_ne_zero hBne]

/-- A boundary point without proportional gain (`k_p = 0`) conserves an energy. -/
@[tmio TM, powerlib_domain] private theorem not_las_of_hopf_kp_eq_zero {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hkp : m.params.kp = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change ¬ LocalAsymptoticStable m.field 0
  have hα := model_kiD0_ne_zero hD0 hdet
  exact not_localAsymptoticStable_of_sineLienard_conservative hα m.field_contDiff
    (fun z => by rw [model_hg0 heq hD0 htr z, hkp, zero_div, zero_mul, add_zero]) (model_hg1 heq)

end Members

/-! ### Connection conclusions at the boundary angle -/

/-- Rate-coupled GFL PLL on the boundary `tr J = 0` (balanced point, `D₀ ≠ 0`, `det J > 0`)
with gains of opposite signs, `k_p k_i < 0`: a supercritical Hopf point. The Jacobian has the
imaginary pair `± j √det J`, yet the operating point is locally asymptotically stable: the
normal-form polynomial `hopfW` has derivative `−κ (φ² + (α/A) w²)² + O(s⁵)` with
`κ = −k_p V² / (16 D₀ V cos θ*) > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_hopf (m : Model)
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hk : m.params.kp * m.params.ki < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable m.field 0
  have hA := model_Vcos_ne_zero hD0 hdet
  have hα := model_kiD0_ne_zero hD0 hdet
  have hq := model_ratio_pos hD0 hdet
  exact localAsymptoticStable_of_sineLienard hA hα hq (model_kappa_pos hD0 hdet hk)
    m.field_contDiff
    (model_hg0 heq hD0 htr) (model_hg1 heq)

/-- Rate-coupled GFL PLL on the boundary `tr J = 0` with gains of equal signs, `k_p k_i > 0`: a
subcritical Hopf point, unstable (Chetaev with the normal-form polynomial, `κ < 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_hopf (m : Model)
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hk : 0 < m.params.kp * m.params.ki) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  have hA := model_Vcos_ne_zero hD0 hdet
  have hα := model_kiD0_ne_zero hD0 hdet
  have hq := model_ratio_pos hD0 hdet
  exact unstable_of_sineLienard hA hα hq (model_kappa_neg hD0 hdet hk) m.field_contDiff
    (model_hg0 heq hD0 htr) (model_hg1 heq)

/-- Rate-coupled GFL PLL with physical gains (`V, k_p, k_i, ω_s > 0`, `D₀ > 0`, `cos θ > 0`)
exactly at the boundary angle `tan θ = ω_s k_p / k_i`: the operating point is unstable
(subcritical Hopf). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_tan_eq (p : Params) (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (heq : p.V * Real.sin θ = -(p.Xg * p.Id))
    (htan : Real.tan θ = p.ωs * p.kp / p.ki) :
    connection% (Model.mk p θ ∈ family.den (.flow .unstable)) := by
  have htr := trace_jac_eq_zero_of_tan_eq p hki hωs hcos heq htan
  have hdet := det_jac_pos p hD0 hV hki hcos
  exact mem_den_unstable_of_hopf (Model.mk p θ) heq hD0.ne' htr hdet (mul_pos hkp hki)

/-- With physical gains the operating point is locally asymptotically stable exactly below the
boundary angle: `tan θ < ω_s k_p / k_i` (`V, k_p, k_i, ω_s > 0`, `D₀ > 0`, `cos θ > 0`,
`V sin θ = −X_g i_d`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_tan_lt (p : Params)
    (hD0 : 0 < p.D0) (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    connection% (Model.mk p θ ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      Model.mk p θ ∈ {m : Model | Real.tan m.θ < m.params.ωs * m.params.kp / m.params.ki}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hu : Model.mk p θ ∈ family.den (.flow .unstable) := by
      rcases hc.lt_or_eq with hc | hc
      · have := mem_den_unstable_of_tan_gt p hD0 hV hki hωs hcos heq hc
        unfold powerlib.TMIO.Statement at this
        exact this
      · have := mem_den_unstable_of_tan_eq p hD0 hV hkp hki hωs hcos heq hc.symm
        unfold powerlib.TMIO.Statement at this
        exact this
    rw [(connection_proof% family_isAutonomous.mem_den_flow)] at h hu
    exact hu h.1
  · intro h
    have := mem_den_locallyExponentiallyStable_of_tan_lt p hD0 hV hki hωs hcos heq h
    unfold powerlib.TMIO.Statement at this
    rw [(connection_proof% family_isAutonomous.mem_den_flow)] at this ⊢
    exact Flow.locallyExponentiallyStable_localAsymptoticStable this

/-- **Complete membership of the local asymptotic sentence.** A rate-coupled PLL model is locally
asymptotically stable at `(θ*, 0)` exactly when the point is balanced with a nondegenerate loop
(`V sin θ* = −X_g i_d`, `D₀ ≠ 0`), `det J > 0`, and either `tr J < 0` (Hurwitz) or `tr J = 0` with
gains of opposite signs (`k_p k_i < 0`, supercritical Hopf). Everything else fails: a
non-equilibrium or `D₀ = 0` (frozen angle); `det J < 0` or `tr J > 0` (linear instability);
`det J = 0` (a line of equilibria for `k_i = 0` or `V = 0`, the monotone fold coordinate
`x + L_g i_d θ` for `cos θ* = 0`); `tr J = 0` with `k_p = 0` (conserved energy) or `k_p k_i > 0`
(subcritical Hopf). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (m : Model) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | (m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id) ∧
        m.params.D0 ≠ 0) ∧ 0 < (jac m.params m.θ).det ∧ ((jac m.params m.θ).trace < 0 ∨
          ((jac m.params m.θ).trace = 0 ∧ m.params.kp * m.params.ki < 0))}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  have hs := chain_le_semantics
  unfold powerlib.TMIO.Statement at hs
  have hden : ∀ s, (∀ q ∈ translate s, Meets m q) → m ∈ family.den s := fun s h =>
    (Family.chain_le_semantics_iff.mp hs s) ((TMIO.mem_realize _ _ _).mpr h)
  constructor
  · intro hLAS
    rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hLAS
    change LocalAsymptoticStable m.field 0 at hLAS
    have hunst : Meets m .equilibrium → Meets m .jacobianUnstable → False := by
      intro he hu
      have h := hden (.flow .unstable) (by
        intro q hq
        simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · exact he
        · exact hu)
      rw [(connection_proof% family_isAutonomous.mem_den_flow)] at h
      exact h hLAS.1
    have hf0 : m.field 0 = 0 := by
      by_contra h
      exact Dynamics.unstable_of_ne_zero m.field_contDiff h hLAS.1
    have hD0 : m.params.D0 ≠ 0 := fun h => (fun hFlowConnection => (not_las_of_D0_eq_zero h) (family_isAutonomous.mem_den_flow.mpr hFlowConnection)) hLAS
    have heq := balance_of_model_field_zero hf0
    have he : Meets m .equilibrium := ⟨heq, hD0⟩
    have hdet : 0 < (jac m.params m.θ).det := by
      rcases lt_trichotomy (jac m.params m.θ).det 0 with h | h | h
      · exact (hunst he (Or.inr h)).elim
      · exact ((fun hFlowConnection => (not_las_of_det_eq_zero heq hD0 h) (family_isAutonomous.mem_den_flow.mpr hFlowConnection)) hLAS).elim
      · exact h
    refine ⟨he, hdet, ?_⟩
    rcases lt_trichotomy (jac m.params m.θ).trace 0 with htr | htr | htr
    · exact Or.inl htr
    · refine Or.inr ⟨htr, ?_⟩
      rcases lt_trichotomy (m.params.kp * m.params.ki) 0 with hk | hk | hk
      · exact hk
      · have hki : m.params.ki ≠ 0 := model_kiD0_ne_zero hD0 hdet ∘ fun h => by
          rw [h, zero_div]
        have hkp : m.params.kp = 0 := (mul_eq_zero.mp hk).resolve_right hki
        exact ((fun hFlowConnection => (not_las_of_hopf_kp_eq_zero heq hD0 htr hdet hkp) (family_isAutonomous.mem_den_flow.mpr hFlowConnection)) hLAS).elim
      · exact ((family_isAutonomous.mem_den_flow.mp
          (mem_den_unstable_of_hopf m heq hD0 htr hdet hk)) hLAS.1).elim
    · exact (hunst he (Or.inl htr)).elim
  · rintro ⟨he, hdet, htr | ⟨htr, hk⟩⟩
    · exact hden (.flow .locallyAsymptoticallyStable) (by
        intro q hq
        simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · exact he
        · exact ⟨htr, hdet⟩)
    · rw [(connection_proof% family_isAutonomous.mem_den_flow)]
      exact (family_isAutonomous.mem_den_flow.mp
        (mem_den_locallyAsymptoticallyStable_of_hopf m he.1 he.2 htr hdet hk))

/-! ### The local asymptotic translation is not exact -/

/-- A supercritical boundary PLL: `V = √2`, `X_g = ω_s = 1`, `k_p = −1/2`, `k_i = 1/2`,
`i_d = 1` (so `L_g i_d = 1`, `D₀ = 1/2`; the OUT-positive source point `I_d = −1`) at
`θ* = −π/4`. Balanced (`V sin θ* = −1 = −X_g i_d`), `tr J = 0`, `det J = 1`, `k_p k_i = −1/4`. -/
def supercriticalPLL : Model := ⟨⟨Real.sqrt 2, ⟨0, 1, 0⟩, 1, -1 / 2, 1 / 2, 1, rfl⟩, -(Real.pi / 4)⟩

/-- The supercritical boundary PLL is balanced: `V sin θ* = −X_g i_d`. -/
@[tmio M, powerlib_domain] private theorem supercriticalPLL_balance :
    supercriticalPLL.params.V * Real.sin supercriticalPLL.θ =
      -(supercriticalPLL.params.Xg * supercriticalPLL.params.Id) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [Passive.SeriesRLC.reactance, Params.Xg, supercriticalPLL, Real.sin_neg,
    Real.sin_pi_div_four]
  linear_combination (-1 / 2 : ℝ) * h2

/-- The supercritical boundary PLL has `D₀ ≠ 0` (`D₀ = 1/2`). -/
@[tmio M, powerlib_domain] private theorem supercriticalPLL_D0_ne_zero :
    supercriticalPLL.params.D0 ≠ 0 := by
  have hD0 : supercriticalPLL.params.D0 = 1 / 2 := by
    simp [Passive.SeriesRLC.reactance, Params.Xg, supercriticalPLL, Params.D0, Params.Lg]; norm_num
  rw [hD0]; norm_num

/-- The supercritical boundary PLL lies on the boundary: `tr J = 0`. -/
@[tmio M, powerlib_domain] private theorem supercriticalPLL_trace_jac :
    (jac supercriticalPLL.params supercriticalPLL.θ).trace = 0 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hD0 : supercriticalPLL.params.D0 = 1 / 2 := by
    simp [Passive.SeriesRLC.reactance, Params.Xg, supercriticalPLL, Params.D0, Params.Lg]; norm_num
  rw [trace_jac, hD0]
  simp only [Passive.SeriesRLC.reactance, Params.Xg, supercriticalPLL, Real.cos_neg,
      Real.cos_pi_div_four, Params.Lg]
  linear_combination (1 / 2 : ℝ) * h2

/-- The supercritical boundary PLL has `det J > 0` (`det J = 1`). -/
@[tmio M, powerlib_domain] private theorem supercriticalPLL_det_jac_pos :
    0 < (jac supercriticalPLL.params supercriticalPLL.θ).det := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hD0 : supercriticalPLL.params.D0 = 1 / 2 := by
    simp [Passive.SeriesRLC.reactance, Params.Xg, supercriticalPLL, Params.D0, Params.Lg]; norm_num
  rw [det_jac _ (by rw [hD0]; norm_num), hD0]
  simp only [supercriticalPLL, Real.cos_neg, Real.cos_pi_div_four]
  nlinarith [h2]

/-- The supercritical boundary PLL has gains of opposite signs: `k_p k_i < 0`. -/
@[tmio M, powerlib_domain] private theorem supercriticalPLL_kp_mul_ki_neg :
    supercriticalPLL.params.kp * supercriticalPLL.params.ki < 0 := by
  simp [supercriticalPLL]; norm_num

/-- The supercritical boundary PLL is locally asymptotically stable. -/
@[tmio TM, powerlib_domain] theorem supercriticalPLL_mem_den_locallyAsymptoticallyStable :
    connection% (supercriticalPLL ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  exact mem_den_locallyAsymptoticallyStable_of_hopf supercriticalPLL supercriticalPLL_balance
    supercriticalPLL_D0_ne_zero supercriticalPLL_trace_jac supercriticalPLL_det_jac_pos
    supercriticalPLL_kp_mul_ki_neg

/-- **The local asymptotic translation is not exact.** The supercritical boundary PLL is locally
asymptotically stable, but its Jacobian has trace `0`, so it meets no stable-Jacobian
requirement. -/
@[tmio TM, powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness supercriticalPLL_mem_den_locallyAsymptoticallyStable
    (q := .jacobianStable) (by simp [family, translate]) fun hs => ?_
  have := (hs : Meets supercriticalPLL .jacobianStable).1
  rw [supercriticalPLL_trace_jac] at this
  exact lt_irrefl 0 this


end powerlib.GFL.RatePLL
