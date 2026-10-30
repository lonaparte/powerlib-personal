import theorem.Dynamics.Locality
import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Coordinates
import theorem.Spectral.Local
import theorem.Dynamics.Pendulum

/-! # Rate-coupled two-state GFL PLL (form-C-lite, frozen `i_d`)

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold: `theorem/CurrentDirection.agda`.

Model boundary.
Single grid-following converter on an infinite bus of amplitude `V`
behind a lossless inductive line `X_g = ω_s L_g`; three-phase balanced, averaged dq model in
the PLL frame, continuous time.
* States, in order: `θ` (PLL error angle `θ̂_g − θ_g`), `x` (PLL integrator state).
* The current loop is ideal (controlled current source); the d-axis current `i_d` (into the
  converter) is a **frozen parameter**, not a state; `I_q = 0`. An exporting converter has
  `i_d < 0`.
* Line `v_pcc = v_g − j ω₁ L_g i` (`ω₁ = ω_s + u`); the only line dynamics kept is the speed-EMF
  coupling `−L_g u i_d` of the line inductance: `v_q = h − L_g u i_d`, `h = −V sin θ − X_g i_d`,
  and the SRF-PLL is `u = k_p v_q + k_i x`.  Solving the algebraic loop gives
  `θ̇ = u = (k_p h + k_i x) / D₀`, `ẋ = v_q`, with `D₀ = 1 + k_p L_g i_d ≠ 0`
  (`D₀ > 0` is assumed for the stability results).
* No PWM, delay, limiter, dc link, outer loop, line resistance, or `L_f`.
* Equilibria: `x = 0`, `V sin θ = −X_g i_d`.  Results are at the equilibrium (linearization)
  level: local exponential stability / instability of the full nonlinear two-state field.

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (推论二 `tan θ_H`, 推论四 ζ 比),
`.../archive/notes/concepts/disturbance-layer.md` (`X_g` 精确消去, `tan θ_H = ω_s ζ₀/(π f_{n0})`),
`projects/gfl-gfm-stability-tree/notes/concepts/nonautonomous-criteria.md` (N1 冻结阈 `ε_frozen`);
model `GFLRate` in `.../archive/simulation/src/gfl_gfm_contrast_sim/models.py`. The source writes
the frozen current OUT-positive, `I_d = −i_d` (`convention_override` there): that form is
`literatureField`, and `field_eq_literatureField` reads it by the substitution `I_d = −i_d`
(conventions §D8).

Results.
* `field_eq_literatureField` (§D8 boundary translation): the field at `i_d` is the OUT-positive
  source field at `I_d = −i_d`.
* `jacobian_eq`: the Jacobian at an equilibrium is
  `(1/D₀) [[−k_p V cos θ, k_i], [−V cos θ, k_i V sin θ / ω_s]]` (derived with `fderiv`; at an
  equilibrium `−L_g i_d = V sin θ / ω_s`).
* `mem_den_locallyExponentiallyStable_of_tan_lt` / `mem_den_unstable_of_tan_gt` (connection
  memberships, below): for `V, k_p, k_i, ω_s > 0`,
  `D₀ > 0`, `cos θ > 0`: `tan θ < ω_s k_p / k_i` ⇒ locally exponentially stable,
  `tan θ > ω_s k_p / k_i` ⇒ unstable.  `det J = k_i V cos θ / D₀ > 0` always holds, so
  `tan θ_H = ω_s k_p / k_i` is the stability boundary; on it the Jacobian has the purely
  imaginary pair `± j √det J` (`imaginary_pair_at_boundary`; a Hopf *candidate* — no
  transversality or Lyapunov-coefficient claim is made).
* `zeta_ratio`: damping ratio of the rate-coupled Jacobian over the quasi-static closed form
  `(k_p/2) √(V cos θ / k_i)` equals `(1 − r)/√D₀`, `r = tan θ / (ω_s k_p / k_i)`.
* `jacobian_indep_Xg`: at a fixed equilibrium angle the Jacobian does not depend on `X_g`
  (`−L_g i_d = V sin θ / ω_s` there).
* `omega_kp_div_ki_of_pllGains`: with the source tuning rule `k_p = 2ζ₀ω_{n0}/V`,
  `k_i = ω_{n0}²/V`, `ω_{n0} = 2π f_{n0}`, one gets `ω_s k_p / k_i = ω_s ζ₀ / (π f_{n0})`.
* Frozen-coefficient threshold (`frozen_hurwitz_forall_iff`): with the grid amplitude
  modulated as `V(t) = V_g + ε cos(ω_p t)`, `ε ≥ 0`, `ω_p ≠ 0`, `L_g i_d ≤ 0` (exporting), the
  *frozen* Jacobian at the fixed angle `θ_{e0}` is Hurwitz for every `t` iff
  `ε < ε_frozen = V_g + k_i L_g i_d / (k_p cos θ_{e0})` (the source's
  `V_g − k_i L_g I_d / (k_p cos θ_{e0})`).  This is a statement about a
  family of constant matrices only: frozen-time Hurwitz stability does **not** imply
  stability of the linear time-varying (periodic) system, and the source note exhibits
  parametric resonance below `ε_frozen`.

Family and connection conclusions.
A complete system (`Model`) is a parameter set with a
selected angle `θ*`; the system map reads it as the autonomous field translated so that the
operating point `(θ*, 0)` is the origin, `z ↦ field p (z + (θ*, 0))` (every flow sentence is
invariant under this translation, `Flow.Property.holds_shift_iff`). The requirement language is
static: `(θ*, 0)` is an equilibrium with a nondegenerate loop (`V sin θ* = −X_g i_d`, `D₀ ≠ 0`);
the closed-form Jacobian `jac p θ*` (proved to be the `fderiv`) has `tr < 0`, `det > 0`; or it has
`tr > 0` or `det < 0`. The local sentences translate into the first two, instability into the
first and the third, passivity into nothing, and the global sentences, decay rates, sampled
contraction and conservation into the whole (inconsistent) language: unavailable translation
coverage. `chain_le_semantics` proves every translation sound; `exact_passive` proves the
passivity translation exact. The stability results are connection memberships:
`mem_den_locallyExponentiallyStable_of_tan_lt` and `mem_den_unstable_of_tan_gt`, together with
`not_mem_den_lyapunovStable_of_tan_gt`. The local exponential translation is exact
(`exact_locallyExponentiallyStable`): by the converse linearization theorem
(`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`) local exponential stability of
`(θ*, 0)` holds exactly when it is an equilibrium with a Hurwitz Jacobian; a degenerate loop
`D₀ = 0` freezes the angle, a linear first integral that excludes local exponential stability
(`Dynamics.not_locallyExponentiallyStable_of_firstIntegral`). The instability translation is not
exact (`not_exact_unstable`): instability is the failure of Lyapunov stability, so a model whose
selected point is not an equilibrium (`offEquilibrium`) is unstable
(`offEquilibrium_mem_den_unstable`). The Lyapunov translation is not exact
(`not_exact_lyapunovStable`): the undamped PLL `undampedPLL` (`k_p = 0`, `i_d = 0`) is the pendulum
`θ̇ = x`, `ẋ = −sin θ`, Lyapunov stable through its conserved energy `1 − cos θ + x²/2`
(`undampedPLL_mem_den_lyapunovStable`) with a trace-zero Jacobian. The local asymptotic
translation is not exact (`not_exact_locallyAsymptoticallyStable`, in
`theorem/GFL/RatePLLHopf.lean`): on the boundary `tr J = 0` (`tan θ = ω_s k_p / k_i` for
physical gains) the Jacobian has the imaginary pair `± j √det J` (`imaginary_pair_at_boundary`),
and the Hopf normal form decides the point — supercritical, hence locally asymptotically stable,
for `k_p k_i < 0` (witness `supercriticalPLL`), subcritical and unstable for `k_p k_i > 0` (the
physical boundary angle is unstable, `mem_den_unstable_of_tan_eq`). That module proves the
complete membership `mem_den_locallyAsymptoticallyStable_iff` (Hurwitz, or `tr J = 0` with
`k_p k_i < 0`; `k_i = 0` and `V = 0` give lines of equilibria, `cos θ* = 0` a fold with a monotone
coordinate, `k_p = 0` on the boundary a conserved energy). The boundary pair, damping ratio, `X_g`
elimination and the
frozen-coefficient threshold remain static foundation results (`frozen_hurwitz_forall_iff` is
about constant matrices, not the time-varying system).
-/

noncomputable section
namespace powerlib.GFL.RatePLL
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
  /-- frozen d-axis current `i_d` (IN-positive: into the converter) -/
  Id : ℝ

namespace Params
variable (p : Params)

/-- line inductance `L_g = X_g / ω_s` -/
def Lg : ℝ := p.Xg / p.ωs

/-- algebraic-loop factor `D₀ = 1 + k_p L_g i_d` -/
def D0 : ℝ := 1 + p.kp * p.Lg * p.Id

end Params

variable (p : Params)

/-- `h = −V sin θ − X_g i_d` (q-axis PCC voltage without the speed-EMF term) -/
def gridQ (θ : ℝ) : ℝ := -p.V * Real.sin θ - p.Xg * p.Id

/-- PLL frequency deviation after solving the algebraic loop -/
def pllOut (θ x : ℝ) : ℝ := (p.kp * gridQ p θ + p.ki * x) / p.D0

/-- q-axis PCC voltage `v_q = h − L_g u i_d` -/
def vq (θ x : ℝ) : ℝ := gridQ p θ - p.Lg * pllOut p θ x * p.Id

/-- Coordinate form of the field, state `(θ, x)`. -/
def coordField (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![pllOut p (y 0) (y 1), vq p (y 0) (y 1)]

/-- The nonlinear two-state field on `Dynamics.State 2`. -/
def field : Dynamics.State 2 → Dynamics.State 2 := Dynamics.lift (coordField p)

/-- The operating point `(θ, 0)`. -/
def equilibrium (θ : ℝ) : Dynamics.State 2 := WithLp.toLp 2 ![θ, 0]

/-- Closed-form Jacobian at the state `(θ, x)` (independent of `x`). -/
def jac (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-p.kp * p.V * Real.cos θ / p.D0, p.ki / p.D0;
     -p.V * Real.cos θ / p.D0, -(p.ki * p.Lg * p.Id) / p.D0]

@[tmio M, powerlib_foundation] theorem field_equilibrium {θ : ℝ}
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    field p (equilibrium θ) = 0 := by
  have hq : gridQ p θ = 0 := by unfold gridQ; linarith
  apply Dynamics.lift_toLp_eq_zero
  ext i
  fin_cases i <;> simp [coordField, vq, pllOut, hq]

@[powerlib_foundation] theorem contDiff_field : ContDiff ℝ 1 (field p) := by
  apply Dynamics.contDiff_lift
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [coordField, vq, pllOut, gridQ] <;> fun_prop

@[powerlib_foundation] theorem hasFDerivAt_coordField (hD0 : p.D0 ≠ 0) (y : Fin 2 → ℝ) :
    HasFDerivAt (coordField p) (Matrix.toLin' (jac p (y 0))).toContinuousLinearMap y := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) y
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) y
  have hq := (h0.sin.const_mul (-p.V)).sub_const (p.Xg * p.Id)
  have hu := ((hq.const_mul p.kp).add (h1.const_mul p.ki)).mul_const p.D0⁻¹
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine Dynamics.hasFDerivAt_of_eq hu
      (fun z => by simp [coordField, pllOut, gridQ, div_eq_mul_inv]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_two]
    field_simp
  · refine Dynamics.hasFDerivAt_of_eq (hq.sub ((hu.const_mul p.Lg).mul_const p.Id))
      (fun z => by simp [coordField, vq, pllOut, gridQ, div_eq_mul_inv]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_two]
    have hD : p.D0 = 1 + p.kp * p.Lg * p.Id := rfl
    field_simp
    rw [hD]
    ring

@[powerlib_foundation] theorem fderiv_field (hD0 : p.D0 ≠ 0) (θ x : ℝ) :
    fderiv ℝ (field p) (WithLp.toLp 2 ![θ, x]) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jac p θ) := by
  have := hasFDerivAt_coordField p hD0 ![θ, x]
  exact Dynamics.fderiv_lift (by simpa using this)

/-- Jacobian at an equilibrium in the source form
`(1/D₀) [[−k_p V cos θ, k_i], [−V cos θ, k_i V sin θ / ω_s]]`. -/
@[powerlib_foundation] theorem jacobian_eq {θ : ℝ} (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    jac p θ = !![-p.kp * p.V * Real.cos θ / p.D0, p.ki / p.D0;
      -p.V * Real.cos θ / p.D0, p.ki * (p.V * Real.sin θ / p.ωs) / p.D0] := by
  have : p.Lg * p.Id = -(p.V * Real.sin θ / p.ωs) := by
    rw [Params.Lg, heq]
    ring
  simp only [jac, mul_assoc, this, mul_neg, neg_neg]

@[powerlib_foundation] theorem trace_jac (θ : ℝ) :
    (jac p θ).trace = (-p.kp * p.V * Real.cos θ - p.ki * p.Lg * p.Id) / p.D0 := by
  rw [jac, Matrix.trace_fin_two_of]
  ring

@[powerlib_foundation] theorem det_jac (hD0 : p.D0 ≠ 0) (θ : ℝ) :
    (jac p θ).det = p.ki * p.V * Real.cos θ / p.D0 := by
  rw [jac, Matrix.det_fin_two_of]
  have hD : p.D0 = 1 + p.kp * p.Lg * p.Id := rfl
  field_simp
  rw [hD]
  ring

@[powerlib_foundation] theorem det_jac_pos (hD0 : 0 < p.D0) (hV : 0 < p.V) (hki : 0 < p.ki)
    {θ : ℝ} (hcos : 0 < Real.cos θ) : 0 < (jac p θ).det := by
  rw [det_jac p hD0.ne']
  positivity

/-- At an equilibrium, `tr J = (V/ω_s)(k_i sin θ − ω_s k_p cos θ) / D₀`. -/
@[powerlib_foundation] theorem trace_jac_eq (hωs : p.ωs ≠ 0) {θ : ℝ}
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    (jac p θ).trace =
      p.V / p.ωs * (p.ki * Real.sin θ - p.ωs * p.kp * Real.cos θ) / p.D0 := by
  have hLI : p.Lg * p.Id = -(p.V * Real.sin θ / p.ωs) := by rw [Params.Lg, heq]; ring
  rw [trace_jac, mul_assoc p.ki, hLI]
  field_simp
  ring

/-- At an equilibrium, `tr J < 0 ↔ tan θ < ω_s k_p / k_i`. -/
@[powerlib_foundation] theorem trace_jac_neg_iff (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
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
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
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
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    LinearSystems.IsHurwitz (jac p θ) ↔ Real.tan θ < p.ωs * p.kp / p.ki := by
  rw [Criteria.isHurwitz_fin_two_iff, trace_jac_neg_iff p hD0 hV hki hωs hcos heq]
  exact ⟨fun h => h.1, fun h => ⟨h, det_jac_pos p hD0 hV hki hcos⟩⟩

/-- On the boundary `tan θ = ω_s k_p / k_i` the Jacobian has the imaginary pair `± j√det`. -/
@[powerlib_foundation] theorem imaginary_pair_at_boundary (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) (htan : Real.tan θ = p.ωs * p.kp / p.ki) :
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

/-! ## The OUT-positive form of the source (conventions §D8) -/

/-- The OUT-positive form of the source model `GFLRate` (work-sync conventions §D8): the frozen
current `p.Id` read as `I_d`, flowing converter → grid; `h = −V sin θ + X_g I_d`,
`D₀ = 1 − k_p L_g I_d`, `θ̇ = (k_p h + k_i x)/D₀`, `ẋ = h + L_g θ̇ I_d`. A static definition only:
the family reads `field`. -/
def literatureField : Dynamics.State 2 → Dynamics.State 2 :=
  Dynamics.lift fun y =>
    ![(p.kp * (-p.V * Real.sin (y 0) + p.Xg * p.Id) + p.ki * y 1) / (1 - p.kp * p.Lg * p.Id),
      -p.V * Real.sin (y 0) + p.Xg * p.Id +
        p.Lg * ((p.kp * (-p.V * Real.sin (y 0) + p.Xg * p.Id) + p.ki * y 1) /
          (1 - p.kp * p.Lg * p.Id)) * p.Id]

/-- §D8 boundary translation: the IN-positive field at the current `i_d` is the OUT-positive
source field at `I_d = −i_d`. -/
@[powerlib_foundation] theorem field_eq_literatureField :
    field p = literatureField { p with Id := -p.Id } := by
  funext y
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [field, literatureField, Dynamics.lift, coordField, pllOut, vq, gridQ, Params.D0,
      Params.Lg] <;> ring

/-! ## Damping-ratio comparison and `X_g` elimination -/

/-- At an equilibrium the loop factor is `D₀ = 1 − k_p V sin θ / ω_s`. -/
@[powerlib_foundation] theorem D0_eq_of_equilibrium {θ : ℝ}
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    p.D0 = 1 - p.kp * p.V * Real.sin θ / p.ωs := by
  rw [Params.D0, Params.Lg, mul_assoc p.kp, div_mul_eq_mul_div]
  linear_combination (p.kp / p.ωs) * heq

/-- Damping ratio `−tr / (2 √det)` of a real 2×2 matrix (meaningful for a complex pair). -/
def dampingRatio (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := -A.trace / (2 * Real.sqrt A.det)

/-- Quasi-static PLL damping-ratio closed form `(k_p/2) √(V cos θ / k_i)`. -/
def zetaQS (θ : ℝ) : ℝ := p.kp / 2 * Real.sqrt (p.V * Real.cos θ / p.ki)

/-- The rate-coupled damping ratio equals the quasi-static closed form times
`(1 − r)/√D₀`, `r = tan θ / (ω_s k_p / k_i)`, `D₀ = 1 − k_p V sin θ / ω_s`. -/
@[powerlib_foundation] theorem zeta_ratio (hD0 : 0 < p.D0) (hV : 0 < p.V) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
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
    (hp : p.V * Real.sin θ = -(p.Xg * p.Id)) (hq : q.V * Real.sin θ = -(q.Xg * q.Id)) :
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

/-- Frozen threshold `ε_frozen = V_g + k_i L_g i_d / (k_p cos θ_{e0})`. -/
def epsFrozen (Vg θ : ℝ) : ℝ := Vg + p.ki * p.Lg * p.Id / (p.kp * Real.cos θ)

/-- The frozen Jacobian at the fixed angle `θ` and grid amplitude `V'` is Hurwitz iff
`V' > −k_i L_g i_d / (k_p cos θ)` (when `L_g i_d ≤ 0`, an exporting converter). -/
@[powerlib_foundation] theorem frozen_isHurwitz_iff (hD0 : 0 < p.D0) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) {θ : ℝ} (hcos : 0 < Real.cos θ) (hLI : p.Lg * p.Id ≤ 0) (V' : ℝ) :
    LinearSystems.IsHurwitz (jac (withV p V') θ) ↔
      -(p.ki * p.Lg * p.Id / (p.kp * Real.cos θ)) < V' := by
  have hD : (withV p V').D0 = p.D0 := rfl
  have hL : (withV p V').Lg = p.Lg := rfl
  rw [Criteria.isHurwitz_fin_two_iff, det_jac _ (hD ▸ hD0.ne'), trace_jac, hD, hL]
  simp only [withV]
  have hkc : 0 < p.kp * Real.cos θ := mul_pos hkp hcos
  rw [← neg_div, div_lt_iff₀ hkc]
  constructor
  · rintro ⟨htr, -⟩
    have : -p.kp * V' * Real.cos θ - p.ki * p.Lg * p.Id < 0 := by
      by_contra hc
      push Not at hc
      exact absurd htr (not_lt.mpr (div_nonneg hc hD0.le))
    nlinarith
  · intro h
    have hV' : 0 < V' := by
      have : p.ki * p.Lg * p.Id ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonneg_of_nonpos hki.le hLI
      nlinarith
    refine ⟨div_neg_of_neg_of_pos (by nlinarith) hD0, by positivity⟩

/-- Frozen-coefficient criterion (N1): for `V(t) = V_g + ε cos(ω_p t)`, `ε ≥ 0`, `ω_p ≠ 0`,
the frozen Jacobian is Hurwitz at every instant iff `ε < ε_frozen`.  Frozen-time Hurwitz
stability is a property of a family of constant matrices; it does not imply stability of the
periodic linear time-varying system. -/
@[powerlib_foundation] theorem frozen_hurwitz_forall_iff (hD0 : 0 < p.D0) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) {θ : ℝ} (hcos : 0 < Real.cos θ) (hLI : p.Lg * p.Id ≤ 0)
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

/-- The translated field is `C¹`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem Model.field_contDiff (m : Model) : ContDiff ℝ 1 m.field :=
  (contDiff_field m.params).comp (contDiff_id.add contDiff_const)

/-- Requirements on the rate-coupled PLL models, all static. -/
inductive Requirement
  /-- `(θ*, 0)` is an equilibrium (`V sin θ* = −X_g i_d`) with a nondegenerate loop `D₀ ≠ 0`. -/
  | equilibrium
  /-- The closed-form Jacobian at `θ*` has `tr < 0` and `det > 0`. -/
  | jacobianStable
  /-- The closed-form Jacobian at `θ*` has `tr > 0` or `det < 0`. -/
  | jacobianUnstable

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id) ∧ m.params.D0 ≠ 0
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
  | .envelope _ => Set.univ

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
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => RatePLL.field m.params)
    (pt := fun m => equilibrium m.θ) family_isAutonomous

/-- Linearization at `(θ*, 0)`: a stable Jacobian gives local exponential stability. -/
@[tmio TM] private theorem les_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianStable) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := show m ∈ family.den (.flow .locallyExponentiallyStable) from
  mem_den_flow_iff.mpr (Criteria.locallyExponentiallyStable_of_jacobian_fin_two
    (jac m.params m.θ) (contDiff_field m.params) (field_equilibrium m.params he.1)
    (fderiv_field m.params he.2 m.θ 0) hs.1 hs.2)

/-- Linearization at `(θ*, 0)`: an unstable Jacobian gives instability. -/
@[tmio TM] private theorem unstable_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianUnstable) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  change m ∈ family.den (.flow .unstable)
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
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .jacobianStable .jacobianUnstable fun m hs hu => ?_
  obtain ⟨h1, h2⟩ : Meets m .jacobianStable := hs
  rcases (hu : Meets m .jacobianUnstable) with h3 | h3 <;> linarith

/-- Every translation of the rate-coupled PLL family is sound: its translation chain lies below
its semantics connection. A stable Jacobian at an equilibrium proves the local sentences, an
unstable one proves instability (LeanForControl's linearization theorems at `(θ*, 0)`, moved to
the origin), and passivity holds without requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same
    (Rs := {.equilibrium, .jacobianStable}) (Ru := {.equilibrium, .jacobianUnstable})
    (fun s => ?_) realize_univ (fun m hm => ?_) (fun m hm => ?_) family_isAutonomous.den_passive
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact les_of_meets (hm .equilibrium (by simp)) (hm .jacobianStable (by simp))
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact unstable_of_meets (hm .equilibrium (by simp)) (hm .jacobianUnstable (by simp))

/-- Passivity is translated exactly: a system without ports is passive. -/
@[tmio TM, powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
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
  · simp [RatePLL.field, Dynamics.lift, coordField, pllOut, hD0]

/-- An equilibrium of the field at `(θ*, 0)` with `D₀ ≠ 0` is balanced, `V sin θ* = −X_g i_d`. -/
@[tmio M] private theorem balance_of_field_eq_zero {p : Params} (hD0 : p.D0 ≠ 0) {θ : ℝ}
    (h : RatePLL.field p (equilibrium θ) = 0) :
    connection% ((⟨p, θ⟩ : Model) ∈ TMIO.realize Meets {.equilibrium}) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets]
  refine ⟨?_, hD0⟩
  have h0 := congrArg (fun y : Dynamics.State 2 => y 0) h
  have h1 := congrArg (fun y : Dynamics.State 2 => y 1) h
  simp [RatePLL.field, Dynamics.lift, coordField, equilibrium, pllOut, vq, hD0] at h0 h1
  have hk : p.kp * gridQ p θ = 0 := by
    rcases h0 with h0 | h0 <;> simp [h0]
  rw [hk, zero_div, mul_zero, zero_mul, sub_zero] at h1
  unfold gridQ at h1
  linarith

/-- The local exponential translation is exact: a model is locally exponentially stable at
`(θ*, 0)` exactly when the point is an equilibrium with a nondegenerate loop
(`V sin θ* = −X_g i_d`, `D₀ ≠ 0`) and the closed-form Jacobian has `tr < 0`, `det > 0`. Converse
linearization: local exponential stability of the `C¹` field forces an equilibrium with a Hurwitz
Jacobian; with `D₀ = 0` the frozen angle excludes it. -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exact_of_exactUnder_empty (Spectral.exactUnder_les_of_jacobian_on
    (fun m P => mem_den_flow_iff) ∅ (fun m => m.params.D0 ≠ 0) (fun m => jac m.params m.θ)
    (fun m _ hm => ?_) (fun m _ hD0 h => ?_) (fun m _ _ => contDiff_field m.params)
    (fun m _ hD0 => fderiv_field m.params hD0 m.θ 0) fun m _ hD0 he hH => ?_)
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact les_of_meets (hm .equilibrium (by simp [family, translate]))
      (hm .jacobianStable (by simp [family, translate]))
  · exact not_les_of_D0_eq_zero (not_not.mp hD0) _ (mem_den_flow_iff.mp h)
  · rw [Criteria.isHurwitz_fin_two_iff] at hH
    rw [(connection_proof% TMIO.mem_realize)]
    rintro q (rfl | rfl)
    · simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family, Meets]
        using balance_of_field_eq_zero hD0 he
    · exact hH

/-! ### Members of the local denotations: the boundary angle `tan θ_H = ω_s k_p / k_i` -/

/-- Rate-coupled GFL PLL: below the angle `tan θ_H = ω_s k_p / k_i` the operating point
`(θ, 0)` is locally exponentially stable (`V, k_i, ω_s > 0`, `D₀ > 0`, `cos θ > 0`,
`V sin θ = −X_g i_d`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_tan_lt (p : Params)
    (hD0 : 0 < p.D0) (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (heq : p.V * Real.sin θ = -(p.Xg * p.Id))
    (htan : Real.tan θ < p.ωs * p.kp / p.ki) :
    connection% (Model.mk p θ ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact les_of_meets ⟨heq, hD0.ne'⟩
    ⟨(trace_jac_neg_iff p hD0 hV hki hωs hcos heq).2 htan, det_jac_pos p hD0 hV hki hcos⟩

/-- Rate-coupled GFL PLL: above the angle `tan θ_H = ω_s k_p / k_i` the operating point
`(θ, 0)` is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_tan_gt (p : Params) (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) (htan : p.ωs * p.kp / p.ki < Real.tan θ) :
    connection% (Model.mk p θ ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact unstable_of_meets ⟨heq, hD0.ne'⟩
    (Or.inl ((trace_jac_pos_iff p hD0 hV hki hωs hcos heq).2 htan))

/-- Above the boundary angle the operating point is not Lyapunov stable. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_lyapunovStable_of_tan_gt (p : Params) (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) (htan : p.ωs * p.kp / p.ki < Real.tan θ) :
    connection% (Model.mk p θ ∉ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_mem_den_lyapunovStable_of_unstable
    (mem_den_unstable_of_tan_gt p hD0 hV hki hωs hcos heq htan)

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: `V = 0`, `X_g = ω_s = 1`, `i_d = −1` (the OUT-positive source point
`I_d = 1`), `k_p = k_i = 0` (so `D₀ = 1`), `θ* = 0`. -/
def offEquilibrium : Model := ⟨⟨0, 1, 1, 0, 0, -1⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[tmio TM, powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff) (contDiff_field _)
    fun h => ?_
  have := congrArg (fun y : Dynamics.State 2 => y 1) h
  simp [offEquilibrium, RatePLL.field, Dynamics.lift, coordField, equilibrium, vq, pllOut, gridQ,
    Params.D0, Params.Lg] at this

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for an equilibrium. -/
@[tmio TM, powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .equilibrium)
    (by simp [family, translate]) (by simp [family, Meets, offEquilibrium])

/-! ### The Lyapunov translation -/

/-- An undamped PLL: `V = k_i = ω_s = 1`, `k_p = X_g = i_d = 0` (so `D₀ = 1`) at `θ* = 0`; the
field is the pendulum `θ̇ = x`, `ẋ = −sin θ`. -/
def undampedPLL : Model := ⟨⟨1, 0, 1, 0, 1, 0⟩, 0⟩

private theorem undampedPLL_field (z : Dynamics.State 2) :
    RatePLL.field undampedPLL.params z = WithLp.toLp 2 ![z 1, -Real.sin (z 0)] := by
  ext i
  fin_cases i <;>
    simp [RatePLL.field, Dynamics.lift, coordField, undampedPLL, vq, pllOut, gridQ, Params.D0,
      Params.Lg]

/-- The pendulum energy `1 − cos θ + x²/2`. -/
private theorem pendulumEnergy_hasFDerivAt (z : Dynamics.State 2) :
    HasFDerivAt (fun y : Dynamics.State 2 => 1 - Real.cos (y 0) + 1 / 2 * y 1 ^ 2)
      (Real.sin (z 0) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ) +
        z 1 • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : Dynamics.State 2 →L[ℝ] ℝ)) z := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
    Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
    Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have hc := (Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z h0
  have h := (hc.const_sub 1).add ((h1.pow 2).const_mul (1 / 2 : ℝ))
  refine h.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp
  ring

/-- The undamped PLL is Lyapunov stable at `θ* = 0`: the pendulum energy `1 − cos θ + x²/2` is
conserved and has a strict minimum on `|θ| < π` (`Dynamics.pendulumEnergy_pos`). Its Jacobian
`[[0, 1], [−1, 0]]` has trace `0`, so it meets no stable-Jacobian requirement. -/
@[tmio TM, powerlib_domain] theorem undampedPLL_mem_den_lyapunovStable :
    connection% (undampedPLL ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr ?_
  change LyapunovStable _ _
  have hpt : equilibrium undampedPLL.θ = 0 := by
    ext i
    fin_cases i <;> simp [equilibrium, undampedPLL]
  rw [hpt]
  have hcont : Continuous fun y : Dynamics.State 2 => y 0 :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : Dynamics.State 2 →L[ℝ] ℝ).continuous
  refine lyapunov_stable (V := fun y : Dynamics.State 2 => 1 - Real.cos (y 0) + 1 / 2 * y 1 ^ 2)
    (D := {y | |y 0| < Real.pi}) two_pos
    ⟨isOpen_lt (continuous_abs.comp hcont) continuous_const, by simp [Real.pi_pos],
      continuous_iff_continuousAt.mpr fun y => (pendulumEnergy_hasFDerivAt y).continuousAt,
      fun y => (pendulumEnergy_hasFDerivAt y).differentiableAt, by simp,
      fun y hy hne => ?_, fun y _ => ?_⟩
  · have hy' : |y 0| < Real.pi := hy
    have hw : 1 / 2 * (‖y - 0‖ ^ 2 - y 0 ^ 2) ≤ 1 / 2 * y 1 ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    exact Dynamics.pendulumEnergy_pos 0 one_half_pos (by simp) hw
      (by linarith [Real.pi_pos]) hne
  · rw [(pendulumEnergy_hasFDerivAt y).fderiv, undampedPLL_field]
    simp [mul_comm]

/-- The Lyapunov translation is sound but not exact: the undamped PLL is Lyapunov stable at an
equilibrium whose Jacobian has trace `0`. -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness undampedPLL_mem_den_lyapunovStable (q := .jacobianStable)
    (by simp [family, translate]) fun hs => ?_
  have := (hs : Meets undampedPLL .jacobianStable).1
  simp [jac, Matrix.trace_fin_two, undampedPLL, Params.D0, Params.Lg] at this

end powerlib.GFL.RatePLL
