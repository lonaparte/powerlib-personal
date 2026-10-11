import theorem.GFLParametric.Basic

/-! # Rate-coupled two-state GFL PLL (form-C-lite, frozen `I_d`)

**Model boundary.** Single grid-following converter on an infinite bus of amplitude `V`
behind a lossless inductive line `X_g = ω_s L_g`; three-phase balanced, averaged dq model in
the PLL frame, continuous time.
* States, in order: `θ` (PLL error angle `θ̂_g − θ_g`), `x` (PLL integrator state).
* The current loop is ideal (controlled current source); the d-axis current `I_d` is a
  **frozen parameter**, not a state; `I_q = 0`.  Port current is OUT-positive (converter →
  grid), as in the source project (`convention_override` there; IN-positive `i_d = −I_d`).
* The only line dynamics kept is the speed-EMF coupling `L_g u I_d` of the line inductance:
  `v_q = h + L_g u I_d`, `h = −V sin θ + X_g I_d`, and the SRF-PLL is
  `u = k_p v_q + k_i x`.  Solving the algebraic loop gives
  `θ̇ = u = (k_p h + k_i x) / D₀`, `ẋ = v_q`, with `D₀ = 1 − k_p L_g I_d ≠ 0`
  (`D₀ > 0` is assumed for the stability results).
* No PWM, delay, limiter, dc link, outer loop, line resistance, or `L_f`.
* Equilibria: `x = 0`, `V sin θ = X_g I_d`.  Results are at the equilibrium (linearization)
  level: local exponential stability / instability of the full nonlinear two-state field.

**Results.**
* `jacobian_eq`: the Jacobian at an equilibrium is
  `(1/D₀) [[−k_p V cos θ, k_i], [−V cos θ, k_i V sin θ / ω_s]]` (derived with `fderiv`).
* `locallyExponentiallyStable_of_tan_lt` / `unstable_of_tan_gt`: for `V, k_p, k_i, ω_s > 0`,
  `D₀ > 0`, `cos θ > 0`: `tan θ < ω_s k_p / k_i` ⇒ locally exponentially stable,
  `tan θ > ω_s k_p / k_i` ⇒ unstable.  `det J = k_i V cos θ / D₀ > 0` always holds, so
  `tan θ_H = ω_s k_p / k_i` is the stability boundary; on it the Jacobian has the purely
  imaginary pair `± j √det J` (`imaginary_pair_at_boundary`; a Hopf *candidate* — no
  transversality or Lyapunov-coefficient claim is made).
* `zeta_ratio`: damping ratio of the rate-coupled Jacobian over the quasi-static closed form
  `(k_p/2) √(V cos θ / k_i)` equals `(1 − r)/√D₀`, `r = tan θ / (ω_s k_p / k_i)`.
* `jacobian_indep_Xg`: at a fixed equilibrium angle the Jacobian does not depend on `X_g`
  (`L_g I_d = V sin θ / ω_s` there).
* `omega_kp_div_ki_of_pllGains`: with the source tuning rule `k_p = 2ζ₀ω_{n0}/V`,
  `k_i = ω_{n0}²/V`, `ω_{n0} = 2π f_{n0}`, one gets `ω_s k_p / k_i = ω_s ζ₀ / (π f_{n0})`.
* Frozen-coefficient threshold (`frozen_hurwitz_forall_iff`): with the grid amplitude
  modulated as `V(t) = V_g + ε cos(ω_p t)`, `ε ≥ 0`, `ω_p ≠ 0`, `I_d ≥ 0`, the *frozen*
  Jacobian at the fixed angle `θ_{e0}` is Hurwitz for every `t` iff
  `ε < ε_frozen = V_g − k_i L_g I_d / (k_p cos θ_{e0})`.  This is a statement about a
  family of constant matrices only: frozen-time Hurwitz stability does **not** imply
  stability of the linear time-varying (periodic) system, and the source note exhibits
  parametric resonance below `ε_frozen`.

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (推论二 `tan θ_H`, 推论四 ζ 比),
`.../archive/notes/concepts/disturbance-layer.md` (`X_g` 精确消去, `tan θ_H = ω_s ζ₀/(π f_{n0})`),
`projects/gfl-gfm-stability-tree/notes/concepts/nonautonomous-criteria.md` (N1 冻结阈 `ε_frozen`);
model `GFLRate` in `.../archive/simulation/src/gfl_gfm_contrast_sim/models.py`.
-/

noncomputable section
namespace powerlib.GFLParametric.RatePLL
open Matrix

/-- Parameters of the rate-coupled PLL model. -/
structure Params where
  /-- grid voltage amplitude -/
  V : ℝ
  /-- grid reactance at `ω_s` -/
  Xg : ℝ
  /-- synchronous angular frequency -/
  ωs : ℝ
  /-- PLL proportional gain -/
  kp : ℝ
  /-- PLL integral gain -/
  ki : ℝ
  /-- frozen d-axis current (OUT-positive) -/
  Id : ℝ

namespace Params
variable (p : Params)

/-- line inductance `L_g = X_g / ω_s` -/
def Lg : ℝ := p.Xg / p.ωs

/-- algebraic-loop factor `D₀ = 1 − k_p L_g I_d` -/
def D0 : ℝ := 1 - p.kp * p.Lg * p.Id

end Params

variable (p : Params)

/-- `h = −V sin θ + X_g I_d` (q-axis PCC voltage without the speed-EMF term) -/
def gridQ (θ : ℝ) : ℝ := -p.V * Real.sin θ + p.Xg * p.Id

/-- PLL frequency deviation after solving the algebraic loop -/
def pllOut (θ x : ℝ) : ℝ := (p.kp * gridQ p θ + p.ki * x) / p.D0

/-- q-axis PCC voltage `v_q = h + L_g u I_d` -/
def vq (θ x : ℝ) : ℝ := gridQ p θ + p.Lg * pllOut p θ x * p.Id

/-- Coordinate form of the field, state `(θ, x)`. -/
def coordField (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![pllOut p (y 0) (y 1), vq p (y 0) (y 1)]

/-- The nonlinear two-state field on `Dynamics.State 2`. -/
def field : Dynamics.State 2 → Dynamics.State 2 := lift (coordField p)

/-- The operating point `(θ, 0)`. -/
def equilibrium (θ : ℝ) : Dynamics.State 2 := WithLp.toLp 2 ![θ, 0]

/-- Closed-form Jacobian at the state `(θ, x)` (independent of `x`). -/
def jac (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-p.kp * p.V * Real.cos θ / p.D0, p.ki / p.D0;
     -p.V * Real.cos θ / p.D0, p.ki * p.Lg * p.Id / p.D0]

@[powerlib_foundation] theorem field_equilibrium {θ : ℝ} (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    field p (equilibrium θ) = 0 := by
  have hq : gridQ p θ = 0 := by unfold gridQ; linarith
  apply lift_toLp_eq_zero
  ext i
  fin_cases i <;> simp [coordField, vq, pllOut, hq]

@[powerlib_foundation] theorem contDiff_field : ContDiff ℝ 1 (field p) := by
  apply contDiff_lift
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [coordField, vq, pllOut, gridQ] <;> fun_prop

@[powerlib_foundation] theorem hasFDerivAt_coordField (hD0 : p.D0 ≠ 0) (y : Fin 2 → ℝ) :
    HasFDerivAt (coordField p) (Matrix.toLin' (jac p (y 0))).toContinuousLinearMap y := by
  have h0 := hasFDerivAt_coord (0 : Fin 2) y
  have h1 := hasFDerivAt_coord (1 : Fin 2) y
  have hq := (h0.sin.const_mul (-p.V)).add_const (p.Xg * p.Id)
  have hu := ((hq.const_mul p.kp).add (h1.const_mul p.ki)).mul_const p.D0⁻¹
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine hasFDerivAt_of_eq hu (fun z => by simp [coordField, pllOut, gridQ, div_eq_mul_inv]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_two]
    field_simp
  · refine hasFDerivAt_of_eq (hq.add ((hu.const_mul p.Lg).mul_const p.Id))
      (fun z => by simp [coordField, vq, pllOut, gridQ, div_eq_mul_inv]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_two]
    have hD : p.D0 = 1 - p.kp * p.Lg * p.Id := rfl
    field_simp
    rw [hD]
    ring

@[powerlib_foundation] theorem fderiv_field (hD0 : p.D0 ≠ 0) (θ x : ℝ) :
    fderiv ℝ (field p) (WithLp.toLp 2 ![θ, x]) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jac p θ) := by
  have := hasFDerivAt_coordField p hD0 ![θ, x]
  exact fderiv_lift (by simpa using this)

/-- Jacobian at an equilibrium in the source form
`(1/D₀) [[−k_p V cos θ, k_i], [−V cos θ, k_i V sin θ / ω_s]]`. -/
@[powerlib_foundation] theorem jacobian_eq {θ : ℝ} (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    jac p θ = !![-p.kp * p.V * Real.cos θ / p.D0, p.ki / p.D0;
      -p.V * Real.cos θ / p.D0, p.ki * (p.V * Real.sin θ / p.ωs) / p.D0] := by
  have : p.Lg * p.Id = p.V * Real.sin θ / p.ωs := by
    rw [Params.Lg, heq]
    ring
  simp only [jac, mul_assoc, this]

@[powerlib_foundation] theorem trace_jac (θ : ℝ) :
    (jac p θ).trace = (-p.kp * p.V * Real.cos θ + p.ki * p.Lg * p.Id) / p.D0 := by
  rw [jac, Matrix.trace_fin_two_of]
  ring

@[powerlib_foundation] theorem det_jac (hD0 : p.D0 ≠ 0) (θ : ℝ) :
    (jac p θ).det = p.ki * p.V * Real.cos θ / p.D0 := by
  rw [jac, Matrix.det_fin_two_of]
  have hD : p.D0 = 1 - p.kp * p.Lg * p.Id := rfl
  field_simp
  rw [hD]
  ring

@[powerlib_foundation] theorem det_jac_pos (hD0 : 0 < p.D0) (hV : 0 < p.V) (hki : 0 < p.ki)
    {θ : ℝ} (hcos : 0 < Real.cos θ) : 0 < (jac p θ).det := by
  rw [det_jac p hD0.ne']
  positivity

/-- At an equilibrium, `tr J = (V/ω_s)(k_i sin θ − ω_s k_p cos θ) / D₀`. -/
@[powerlib_foundation] theorem trace_jac_eq (hωs : p.ωs ≠ 0) {θ : ℝ}
    (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    (jac p θ).trace =
      p.V / p.ωs * (p.ki * Real.sin θ - p.ωs * p.kp * Real.cos θ) / p.D0 := by
  have hLI : p.Lg * p.Id = p.V * Real.sin θ / p.ωs := by rw [Params.Lg, heq]; ring
  rw [trace_jac, mul_assoc p.ki, hLI]
  field_simp
  ring

/-- At an equilibrium, `tr J < 0 ↔ tan θ < ω_s k_p / k_i`. -/
@[powerlib_foundation] theorem trace_jac_neg_iff (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    (jac p θ).trace < 0 ↔ Real.tan θ < p.ωs * p.kp / p.ki := by
  have hVw : 0 < p.V / p.ωs := div_pos hV hωs
  rw [trace_jac_eq p hωs.ne' heq, Real.tan_eq_sin_div_cos, div_lt_div_iff₀ hcos hki]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : 0 ≤ p.V / p.ωs * (p.ki * Real.sin θ - p.ωs * p.kp * Real.cos θ) / p.D0 :=
      div_nonneg (mul_nonneg hVw.le (by linarith)) hD0.le
    linarith
  · intro h
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hVw (by linarith)) hD0

/-- At an equilibrium, `tr J > 0 ↔ tan θ > ω_s k_p / k_i`. -/
@[powerlib_foundation] theorem trace_jac_pos_iff (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    0 < (jac p θ).trace ↔ p.ωs * p.kp / p.ki < Real.tan θ := by
  have hVw : 0 < p.V / p.ωs := div_pos hV hωs
  rw [trace_jac_eq p hωs.ne' heq, Real.tan_eq_sin_div_cos, div_lt_div_iff₀ hki hcos]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : p.V / p.ωs * (p.ki * Real.sin θ - p.ωs * p.kp * Real.cos θ) / p.D0 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hVw.le (by linarith))
        hD0.le
    linarith
  · intro h
    exact div_pos (mul_pos hVw (by linarith)) hD0

/-- Rate-coupled GFL PLL: below the angle `tan θ_H = ω_s k_p / k_i` the equilibrium is
locally exponentially stable. -/
@[powerlib_domain] theorem locallyExponentiallyStable_of_tan_lt (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) (htan : Real.tan θ < p.ωs * p.kp / p.ki) :
    Dynamics.LocallyExponentiallyStable (field p) (equilibrium θ) :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two (jac p θ) (contDiff_field p)
    (field_equilibrium p heq) (fderiv_field p hD0.ne' θ 0)
    ((trace_jac_neg_iff p hD0 hV hki hωs hcos heq).2 htan) (det_jac_pos p hD0 hV hki hcos)

/-- Rate-coupled GFL PLL: above the angle `tan θ_H = ω_s k_p / k_i` the equilibrium is
unstable. -/
@[powerlib_domain] theorem unstable_of_tan_gt (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) (htan : p.ωs * p.kp / p.ki < Real.tan θ) :
    Dynamics.Unstable (field p) (equilibrium θ) :=
  Criteria.unstable_of_jacobian_trace_pos_fin_two (jac p θ) (contDiff_field p)
    (field_equilibrium p heq) (fderiv_field p hD0.ne' θ 0)
    ((trace_jac_pos_iff p hD0 hV hki hωs hcos heq).2 htan)

/-- The Jacobian is Hurwitz exactly below the boundary angle. -/
@[powerlib_foundation] theorem isHurwitz_jac_iff (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    LinearSystems.IsHurwitz (jac p θ) ↔ Real.tan θ < p.ωs * p.kp / p.ki := by
  rw [Criteria.isHurwitz_fin_two_iff, trace_jac_neg_iff p hD0 hV hki hωs hcos heq]
  exact ⟨fun h => h.1, fun h => ⟨h, det_jac_pos p hD0 hV hki hcos⟩⟩

/-- On the boundary `tan θ = ω_s k_p / k_i` the Jacobian has the imaginary pair `± j√det`. -/
@[powerlib_foundation] theorem imaginary_pair_at_boundary (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) (htan : Real.tan θ = p.ωs * p.kp / p.ki) :
    (jac p θ).trace = 0 ∧ 0 < (jac p θ).det ∧
      (LTI.characteristicMatrix (jac p θ) (Complex.I * Real.sqrt (jac p θ).det)).det = 0 := by
  have htr : (jac p θ).trace = 0 := by
    rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hcos.ne' hki.ne'] at htan
    rw [trace_jac_eq p hωs.ne' heq]
    have : p.ki * Real.sin θ - p.ωs * p.kp * Real.cos θ = 0 := by linarith
    rw [this, mul_zero, zero_div]
  have hdet := det_jac_pos p hD0 hV hki hcos
  refine ⟨htr, hdet, ?_⟩
  have hs : ((Real.sqrt (jac p θ).det : ℝ) : ℂ) ^ 2 = ((jac p θ).det : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hdet.le]
  rw [Criteria.det_characteristicMatrix_fin_two, htr, mul_pow, Complex.I_sq, hs]
  push_cast
  ring

/-! ## Damping-ratio comparison and `X_g` elimination -/

/-- At an equilibrium the loop factor is `D₀ = 1 − k_p V sin θ / ω_s`. -/
@[powerlib_foundation] theorem D0_eq_of_equilibrium {θ : ℝ}
    (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    p.D0 = 1 - p.kp * p.V * Real.sin θ / p.ωs := by
  rw [Params.D0, Params.Lg, mul_assoc p.kp, div_mul_eq_mul_div, ← heq]
  ring

/-- Damping ratio `−tr / (2 √det)` of a real 2×2 matrix (meaningful for a complex pair). -/
def dampingRatio (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := -A.trace / (2 * Real.sqrt A.det)

/-- Quasi-static PLL damping-ratio closed form `(k_p/2) √(V cos θ / k_i)`. -/
def zetaQS (θ : ℝ) : ℝ := p.kp / 2 * Real.sqrt (p.V * Real.cos θ / p.ki)

/-- The rate-coupled damping ratio equals the quasi-static closed form times
`(1 − r)/√D₀`, `r = tan θ / (ω_s k_p / k_i)`, `D₀ = 1 − k_p V sin θ / ω_s`. -/
@[powerlib_foundation] theorem zeta_ratio (hD0 : 0 < p.D0) (hV : 0 < p.V) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) :
    dampingRatio (jac p θ) =
      zetaQS p θ * (1 - Real.tan θ / (p.ωs * p.kp / p.ki)) /
        Real.sqrt (1 - p.kp * p.V * Real.sin θ / p.ωs) := by
  rw [← D0_eq_of_equilibrium p heq]
  have hS : 0 < p.V * Real.cos θ := mul_pos hV hcos
  have hdet : (jac p θ).det = p.ki * (p.V * Real.cos θ) / p.D0 := by
    rw [det_jac p hD0.ne']; ring
  have htr : -(jac p θ).trace =
      p.kp * (p.V * Real.cos θ) * (1 - Real.tan θ / (p.ωs * p.kp / p.ki)) / p.D0 := by
    rw [trace_jac_eq p hωs.ne' heq, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have h1 : Real.sqrt (p.ki * (p.V * Real.cos θ) / p.D0) =
      Real.sqrt p.ki * Real.sqrt (p.V * Real.cos θ) / Real.sqrt p.D0 := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hki.le]
  have h2 : Real.sqrt (p.V * Real.cos θ / p.ki) =
      Real.sqrt (p.V * Real.cos θ) / Real.sqrt p.ki := Real.sqrt_div hS.le _
  have ha := Real.sq_sqrt hS.le
  have hb := Real.sq_sqrt hki.le
  have hc := Real.sq_sqrt hD0.le
  have ha0 : 0 < Real.sqrt (p.V * Real.cos θ) := Real.sqrt_pos.2 hS
  have hb0 : 0 < Real.sqrt p.ki := Real.sqrt_pos.2 hki
  have hc0 : 0 < Real.sqrt p.D0 := Real.sqrt_pos.2 hD0
  rw [dampingRatio, neg_div, ← neg_div, htr, hdet, h1, zetaQS, h2]
  set a := Real.sqrt (p.V * Real.cos θ)
  set b := Real.sqrt p.ki
  set c := Real.sqrt p.D0
  set r := 1 - Real.tan θ / (p.ωs * p.kp / p.ki)
  rw [← ha, ← hc]
  field_simp

/-- At an equilibrium angle the Jacobian depends on `(V, ω_s, k_p, k_i, θ)` only: two
parameter sets that differ in `X_g` (with `I_d` re-solved to keep `θ` an equilibrium) have the
same Jacobian. -/
@[powerlib_foundation] theorem jacobian_indep_Xg (q : Params) (hV : p.V = q.V)
    (hωs : p.ωs = q.ωs) (hkp : p.kp = q.kp) (hki : p.ki = q.ki) {θ : ℝ}
    (hp : p.V * Real.sin θ = p.Xg * p.Id) (hq : q.V * Real.sin θ = q.Xg * q.Id) :
    jac p θ = jac q θ := by
  have hDp := D0_eq_of_equilibrium p hp
  have hDq := D0_eq_of_equilibrium q hq
  rw [jacobian_eq p hp, jacobian_eq q hq, hDp, hDq, hV, hωs, hkp, hki]

/-- Source tuning rule `k_p = 2 ζ₀ ω_{n0} / V`, `k_i = ω_{n0}² / V`, `ω_{n0} = 2π f_{n0}`:
`ω_s k_p / k_i = ω_s ζ₀ / (π f_{n0})`, i.e. `tan θ_H = ω_s ζ₀ / (π f_{n0})`. -/
@[powerlib_foundation] theorem omega_kp_div_ki_of_pllGains (ωs fn0 ζ0 V : ℝ) (hV : V ≠ 0)
    (hfn : fn0 ≠ 0) :
    ωs * (2 * ζ0 * (2 * Real.pi * fn0) / V) / ((2 * Real.pi * fn0) ^ 2 / V) =
      ωs * ζ0 / (Real.pi * fn0) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## Frozen-coefficient threshold under grid-amplitude modulation -/

/-- The same model with the grid amplitude replaced by `V'` (frozen-time evaluation). -/
def withV (V' : ℝ) : Params := { p with V := V' }

/-- Frozen threshold `ε_frozen = V_g − k_i L_g I_d / (k_p cos θ_{e0})`. -/
def epsFrozen (Vg θ : ℝ) : ℝ := Vg - p.ki * p.Lg * p.Id / (p.kp * Real.cos θ)

/-- The frozen Jacobian at the fixed angle `θ` and grid amplitude `V'` is Hurwitz iff
`V' > k_i L_g I_d / (k_p cos θ)` (when `L_g I_d ≥ 0`). -/
@[powerlib_foundation] theorem frozen_isHurwitz_iff (hD0 : 0 < p.D0) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) {θ : ℝ} (hcos : 0 < Real.cos θ) (hLI : 0 ≤ p.Lg * p.Id) (V' : ℝ) :
    LinearSystems.IsHurwitz (jac (withV p V') θ) ↔
      p.ki * p.Lg * p.Id / (p.kp * Real.cos θ) < V' := by
  have hD : (withV p V').D0 = p.D0 := rfl
  have hL : (withV p V').Lg = p.Lg := rfl
  rw [Criteria.isHurwitz_fin_two_iff, det_jac _ (hD ▸ hD0.ne'), trace_jac, hD, hL]
  simp only [withV]
  have hkc : 0 < p.kp * Real.cos θ := mul_pos hkp hcos
  rw [div_lt_iff₀ hkc]
  constructor
  · rintro ⟨htr, -⟩
    have : -p.kp * V' * Real.cos θ + p.ki * p.Lg * p.Id < 0 := by
      by_contra hc
      push Not at hc
      exact absurd htr (not_lt.mpr (div_nonneg hc hD0.le))
    nlinarith
  · intro h
    have hV' : 0 < V' := by
      have : 0 ≤ p.ki * p.Lg * p.Id := by rw [mul_assoc]; exact mul_nonneg hki.le hLI
      nlinarith
    refine ⟨div_neg_of_neg_of_pos (by nlinarith) hD0, by positivity⟩

/-- Frozen-coefficient criterion (N1): for `V(t) = V_g + ε cos(ω_p t)`, `ε ≥ 0`, `ω_p ≠ 0`,
the frozen Jacobian is Hurwitz at every instant iff `ε < ε_frozen`.  Frozen-time Hurwitz
stability is a property of a family of constant matrices; it does not imply stability of the
periodic linear time-varying system. -/
@[powerlib_foundation] theorem frozen_hurwitz_forall_iff (hD0 : 0 < p.D0) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) {θ : ℝ} (hcos : 0 < Real.cos θ) (hLI : 0 ≤ p.Lg * p.Id)
    {Vg ε ωp : ℝ} (hε : 0 ≤ ε) (hωp : ωp ≠ 0) :
    (∀ t : ℝ, LinearSystems.IsHurwitz (jac (withV p (Vg + ε * Real.cos (ωp * t))) θ)) ↔
      ε < epsFrozen p Vg θ := by
  simp only [frozen_isHurwitz_iff p hD0 hkp hki hcos hLI, epsFrozen]
  constructor
  · intro h
    have := h (Real.pi / ωp)
    rw [mul_div_cancel₀ _ hωp, Real.cos_pi] at this
    linarith
  · intro h t
    have := Real.neg_one_le_cos (ωp * t)
    nlinarith

end powerlib.GFLParametric.RatePLL
