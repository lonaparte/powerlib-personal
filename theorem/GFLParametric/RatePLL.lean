import theorem.GFLParametric.Basic
import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Flow.Shift
import theorem.TMIO.ClaimElab

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

**Family and connection conclusions.** A complete system (`Model`) is a parameter set with a
selected angle `θ*`; the system map reads it as the autonomous field translated so that the
operating point `(θ*, 0)` is the origin, `z ↦ field p (z + (θ*, 0))` (every flow sentence is
invariant under this translation, `Flow.Property.holds_shift_iff`). The requirement language is
static: `(θ*, 0)` is an equilibrium with a nondegenerate loop (`V sin θ* = X_g I_d`, `D₀ ≠ 0`);
the closed-form Jacobian `jac p θ*` (proved to be the `fderiv`) has `tr < 0`, `det > 0`; or it has
`tr > 0` or `det < 0`. The local sentences translate into the first two, instability into the
first and the third, passivity into nothing, and the global sentences, decay rates, sampled
contraction and conservation into the whole (inconsistent) language: unavailable translation
coverage. `chain_le_semantics` proves every translation sound; `exact_passive` proves the
passivity translation exact. The former domain theorems are now connection memberships:
`mem_den_locallyExponentiallyStable_of_tan_lt` and `mem_den_unstable_of_tan_gt`, together with
`not_mem_den_lyapunovStable_of_tan_gt`. The local exponential translation is exact
(`exact_locallyExponentiallyStable`): by the converse linearization theorem
(`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`) local exponential stability of
`(θ*, 0)` holds exactly when it is an equilibrium with a Hurwitz Jacobian; a degenerate loop
`D₀ = 0` freezes the angle, a linear first integral that excludes local exponential stability
(`Dynamics.not_locallyExponentiallyStable_of_firstIntegral`). Exactness of the local asymptotic,
Lyapunov and instability translations is not claimed (UNPROVED). The boundary pair, damping ratio, `X_g` elimination and the frozen-coefficient
threshold remain static foundation results (`frozen_hurwitz_forall_iff` is about constant
matrices, not the time-varying system).

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
      (Linear.characteristicMatrix (jac p θ) (Complex.I * Real.sqrt (jac p θ).det)).det = 0 := by
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

/-! ## The rate-coupled PLL family -/

/-- A rate-coupled PLL model read about a selected angle `θ*`: the operating point is
`(θ*, 0)`. -/
structure Model where
  /-- The parameters. -/
  params : Params
  /-- The selected angle `θ*`. -/
  θ : ℝ

/-- The field translated so that the selected point `(θ*, 0)` is the origin. -/
def Model.field (m : Model) (z : Dynamics.State 2) : Dynamics.State 2 :=
  RatePLL.field m.params (z + equilibrium m.θ)

/-- Requirements on the rate-coupled PLL models, all static. -/
inductive Requirement
  /-- `(θ*, 0)` is an equilibrium (`V sin θ* = X_g I_d`) with a nondegenerate loop `D₀ ≠ 0`. -/
  | equilibrium
  /-- The closed-form Jacobian at `θ*` has `tr < 0` and `det > 0`. -/
  | jacobianStable
  /-- The closed-form Jacobian at `θ*` has `tr > 0` or `det < 0`. -/
  | jacobianUnstable

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => m.params.V * Real.sin m.θ = m.params.Xg * m.params.Id ∧ m.params.D0 ≠ 0
  | .jacobianStable => (jac m.params m.θ).trace < 0 ∧ 0 < (jac m.params m.θ).det
  | .jacobianUnstable => 0 < (jac m.params m.θ).trace ∨ (jac m.params m.θ).det < 0

/-- The translation of the sentences: the local ones into an equilibrium with a stable Jacobian,
instability into one with an unstable Jacobian, passivity into nothing. The global sentences,
decay rates, sampled contraction and conservation are not decided by the linearization and are
translated into the whole language, which no model meets (unavailable translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.equilibrium, .jacobianStable}
  | .flow .unstable => {.equilibrium, .jacobianUnstable}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The rate-coupled PLL family: every model read as its field translated to the selected
point. -/
def family : Family Model Requirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

/-- A flow sentence of a model is the sentence of the untranslated field at `(θ*, 0)`. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (RatePLL.field m.params) (equilibrium m.θ) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Linearization at `(θ*, 0)`: a stable Jacobian gives local exponential stability (the proof
of the former public `locallyExponentiallyStable_of_tan_lt`). -/
private theorem les_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianStable) : m ∈ family.den (.flow .locallyExponentiallyStable) :=
  mem_den_flow_iff.mpr (Criteria.locallyExponentiallyStable_of_jacobian_fin_two
    (jac m.params m.θ) (contDiff_field m.params) (field_equilibrium m.params he.1)
    (fderiv_field m.params he.2 m.θ 0) hs.1 hs.2)

/-- Linearization at `(θ*, 0)`: an unstable Jacobian gives instability (the proof of the former
public `unstable_of_tan_gt`). -/
private theorem unstable_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianUnstable) : m ∈ family.den (.flow .unstable) := by
  refine mem_den_flow_iff.mpr ?_
  rcases hs with htr | hdet
  · exact Criteria.unstable_of_jacobian_trace_pos_fin_two (jac m.params m.θ)
      (contDiff_field m.params) (field_equilibrium m.params he.1)
      (fderiv_field m.params he.2 m.θ 0) htr
  · exact Criteria.unstable_of_jacobian_det_neg_fin_two (jac m.params m.θ)
      (contDiff_field m.params) (field_equilibrium m.params he.1)
      (fderiv_field m.params he.2 m.θ 0) hdet

/-! ### Soundness of the translation -/

/-- No model has both a stable and an unstable Jacobian: the whole requirement language is
inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨h1, h2⟩ : Meets m .jacobianStable := h .jacobianStable
  rcases (h .jacobianUnstable : Meets m .jacobianUnstable) with h3 | h3 <;> linarith

/-- Every translation of the rate-coupled PLL family is sound: its translation chain lies below
its semantics connection. A stable Jacobian at an equilibrium proves the local sentences, an
unstable one proves instability (LeanForControl's linearization theorems at `(θ*, 0)`, moved to
the origin), and passivity holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · have hles : Meets m .equilibrium → Meets m .jacobianStable →
        LocallyExponentiallyStable m.field 0 := fun he hs =>
      family_isAutonomous.mem_den_flow.mp (les_of_meets he hs)
    rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable =>
      exact (hles (hm .equilibrium (by simp [translate]))
        (hm .jacobianStable (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (hles (hm .equilibrium (by simp [translate])) (hm .jacobianStable (by simp [translate])))
    case locallyExponentiallyStable =>
      exact hles (hm .equilibrium (by simp [translate])) (hm .jacobianStable (by simp [translate]))
    case unstable =>
      exact family_isAutonomous.mem_den_flow.mp (unstable_of_meets
        (hm .equilibrium (by simp [translate])) (hm .jacobianUnstable (by simp [translate])))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-! ### Exactness of the local exponential translation -/

/-- With a degenerate algebraic loop `D₀ = 0` the angle is frozen: `θ` is a linear first
integral of the field, so no point is locally exponentially stable. -/
private theorem not_les_of_D0_eq_zero {p : Params} (hD0 : p.D0 = 0) (x : Dynamics.State 2) :
    ¬ LocallyExponentiallyStable (RatePLL.field p) x := by
  refine Dynamics.not_locallyExponentiallyStable_of_firstIntegral (contDiff_field p)
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) ?_ fun y => ?_
  · intro h
    have := congrArg (fun L : Dynamics.State 2 →L[ℝ] ℝ => L (EuclideanSpace.single 0 1)) h
    simp at this
  · simp [RatePLL.field, lift, coordField, pllOut, hD0]

/-- An equilibrium of the field at `(θ*, 0)` with `D₀ ≠ 0` is balanced, `V sin θ* = X_g I_d`. -/
private theorem balance_of_field_eq_zero {p : Params} (hD0 : p.D0 ≠ 0) {θ : ℝ}
    (h : RatePLL.field p (equilibrium θ) = 0) : p.V * Real.sin θ = p.Xg * p.Id := by
  have h0 := congrArg (fun y : Dynamics.State 2 => y 0) h
  have h1 := congrArg (fun y : Dynamics.State 2 => y 1) h
  simp [RatePLL.field, lift, coordField, equilibrium, pllOut, vq, hD0] at h0 h1
  have hk : p.kp * gridQ p θ = 0 := by
    rcases h0 with h0 | h0 <;> simp [h0]
  rw [hk, zero_div, mul_zero, zero_mul, add_zero] at h1
  unfold gridQ at h1
  linarith

/-- The local exponential translation is exact: a model is locally exponentially stable at
`(θ*, 0)` exactly when the point is an equilibrium with a nondegenerate loop
(`V sin θ* = X_g I_d`, `D₀ ≠ 0`) and the closed-form Jacobian has `tr < 0`, `det > 0`. Converse
linearization: local exponential stability of the `C¹` field forces an equilibrium with a Hurwitz
Jacobian; with `D₀ = 0` the frozen angle excludes it. -/
@[powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [TMIO.mem_realize, mem_den_flow_iff]
  change _ ↔ LocallyExponentiallyStable _ _
  simp only [family, translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, Meets]
  by_cases hD0 : m.params.D0 = 0
  · simp only [hD0, ne_eq, not_true_eq_false, and_false, false_and, false_iff]
    exact not_les_of_D0_eq_zero hD0 _
  · change _ ↔ LocallyExponentiallyStable _ (WithLp.toLp 2 ![m.θ, 0])
    rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (contDiff_field m.params)
      (fderiv_field m.params hD0 m.θ 0), Criteria.isHurwitz_fin_two_iff]
    constructor
    · rintro ⟨⟨hb, -⟩, hs⟩
      exact ⟨field_equilibrium m.params hb, hs⟩
    · rintro ⟨he, hs⟩
      exact ⟨⟨balance_of_field_eq_zero hD0 he, hD0⟩, hs⟩

/-! ### Members of the local denotations: the boundary angle `tan θ_H = ω_s k_p / k_i` -/

/-- Rate-coupled GFL PLL: below the angle `tan θ_H = ω_s k_p / k_i` the operating point
`(θ, 0)` is locally exponentially stable (`V, k_i, ω_s > 0`, `D₀ > 0`, `cos θ > 0`,
`V sin θ = X_g I_d`). -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_tan_lt (p : Params)
    (hD0 : 0 < p.D0) (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (heq : p.V * Real.sin θ = p.Xg * p.Id)
    (htan : Real.tan θ < p.ωs * p.kp / p.ki) :
    connection% (Model.mk p θ ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact les_of_meets ⟨heq, hD0.ne'⟩
    ⟨(trace_jac_neg_iff p hD0 hV hki hωs hcos heq).2 htan, det_jac_pos p hD0 hV hki hcos⟩

/-- Rate-coupled GFL PLL: above the angle `tan θ_H = ω_s k_p / k_i` the operating point
`(θ, 0)` is unstable. -/
@[powerlib_domain] theorem mem_den_unstable_of_tan_gt (p : Params) (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) (htan : p.ωs * p.kp / p.ki < Real.tan θ) :
    connection% (Model.mk p θ ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact unstable_of_meets ⟨heq, hD0.ne'⟩
    (Or.inl ((trace_jac_pos_iff p hD0 hV hki hωs hcos heq).2 htan))

/-- Above the boundary angle the operating point is not Lyapunov stable. -/
@[powerlib_domain] theorem not_mem_den_lyapunovStable_of_tan_gt (p : Params) (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = p.Xg * p.Id) (htan : p.ωs * p.kp / p.ki < Real.tan θ) :
    connection% (Model.mk p θ ∉ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := mem_den_unstable_of_tan_gt p hD0 hV hki hωs hcos heq htan
  unfold powerlib.TMIO.Statement at h
  rw [family_isAutonomous.mem_den_flow] at h ⊢
  exact h

end powerlib.GFLParametric.RatePLL
