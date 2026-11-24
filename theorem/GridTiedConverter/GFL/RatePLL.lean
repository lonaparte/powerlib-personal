import theorem.Dynamics.Locality
import theorem.Passive.Series
import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Coordinates
import theorem.Spectral.Local
import theorem.PhasePlane.Pendulum
import theorem.GridTiedConverter.PLL.Model
import theorem.GridTiedConverter.PLL.Linear

/-! # Rate-coupled two-state GFL PLL (form-C-lite, frozen `i_d`)

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold: `theorem/Transform/CurrentDirection.agda`.

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
the frozen current OUT-positive, `I_d = −i_d` (a convention override declared by the source):
that form is `literatureField`, and `field_eq_literatureField` reads it by the substitution
`I_d = −i_d` (conventions §D8).

Results.
* `field_eq_literatureField` (§D8 boundary translation): the field at `i_d` is the OUT-positive
  source field at `I_d = −i_d`.
* `field_eq_srfField`: with `i_d = 0` the field is the SRF-PLL field `PLL.srfField V k_p k_i 0`
  (`D₀ = 1`).
* `field_equilibrium_eq_zero_iff`: `(θ, 0)` is an equilibrium iff `V sin θ = −X_g i_d`, for every
  `D₀`.
* `jacobian_eq`: the Jacobian at an equilibrium is
  `(1/D₀) [[−k_p V cos θ, k_i], [−V cos θ, k_i V sin θ / ω_s]]` (derived with `fderiv`; at an
  equilibrium `−L_g i_d = V sin θ / ω_s`).
* `mem_den_locallyExponentiallyStable_of_tan_lt` / `mem_den_unstable_of_tan_gt` (connection
  memberships, below): for `V, k_p, k_i, ω_s > 0`,
  `D₀ > 0`, `cos θ > 0`: `tan θ < ω_s k_p / k_i` ⇒ locally exponentially stable,
  `tan θ > ω_s k_p / k_i` ⇒ unstable.  `det J = k_i V cos θ / D₀ > 0` always holds and `tr J` is
  a positive multiple of `tan θ − ω_s k_p / k_i` (`trace_jac_eq_mul_tan_sub`), so
  `tan θ_H = ω_s k_p / k_i` is the stability boundary; on it `tr J = 0`
  (`trace_jac_eq_zero_of_tan_eq`) and the Jacobian has the purely imaginary pair `± j √det J`
  (`imaginary_pair_at_boundary`; a Hopf *candidate* — no transversality or Lyapunov-coefficient
  claim is made).
* `zeta_ratio`: the damping ratio (`Criteria.dampingRatio`) of the rate-coupled Jacobian over the
  quasi-static one `zetaQS` (`PLL.zeta` at the slope `V cos θ`, closed form
  `(k_p/2) √(V cos θ / k_i)`) equals `(1 − r)/√D₀`, `r = tan θ / (ω_s k_p / k_i)`.
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
coverage. `chain_le_semantics` proves every translation sound from the linearization
(`Spectral.chain_le_semantics_of_jacobian`); `family_isAutonomous.exact_passive` proves the
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
`θ̇ = x`, `ẋ = −sin θ` (`field_eq_srfField`), Lyapunov stable at its lower equilibrium
(`PhasePlane.Pendulum.origin_lyapunovStable`, `undampedPLL_mem_den_lyapunovStable`) with a
trace-zero Jacobian. The local asymptotic
translation is not exact (`not_exact_locallyAsymptoticallyStable`, in
`theorem/GridTiedConverter/GFL/RatePLLHopf.lean`): on the boundary `tr J = 0`
(`tan θ = ω_s k_p / k_i` for physical gains) the Jacobian has the imaginary pair `± j √det J`
(`imaginary_pair_at_boundary`), and the Hopf normal form decides the point — supercritical, hence
locally asymptotically stable, for `k_p k_i < 0` (witness `supercriticalPLL`), subcritical and
unstable for `k_p k_i > 0` (the physical boundary angle is unstable, `mem_den_unstable_of_tan_eq`).
That module proves the complete membership `mem_den_locallyAsymptoticallyStable_iff` (Hurwitz, or
`tr J = 0` with `k_p k_i < 0`; `k_i = 0` and `V = 0` give lines of equilibria, `cos θ* = 0` a fold
with a monotone coordinate, `k_p = 0` on the boundary a conserved energy). The boundary pair,
damping ratio, `X_g` elimination and the
frozen-coefficient threshold remain static domain results (`frozen_hurwitz_forall_iff` is
about constant matrices, not the time-varying system).
-/

noncomputable section
namespace powerlib.GFL.RatePLL
open Matrix

/-- Parameters of the rate-coupled PLL model. -/
structure Params where
  /-- grid voltage amplitude -/
  V : ℝ
  /-- grid line, a series RLC branch; its phasor impedance `R + jX` is taken at `ω_s`; lossless -/
  line : Passive.SeriesRLC
  /-- synchronous angular frequency -/
  ωs : ℝ
  /-- PLL proportional gain -/
  kp : ℝ
  /-- PLL integral gain -/
  ki : ℝ
  /-- frozen d-axis current `i_d` (IN-positive: into the converter) -/
  Id : ℝ
  /-- The grid line is lossless. -/
  line_lossless : line.R = 0

/-- The grid reactance `X_g`: the line reactance at `ω_s`. -/
abbrev Params.Xg (p : Params) : ℝ := p.line.reactance p.ωs

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

/-- The points `(θ, 0)` that are equilibria are exactly the balanced ones, `V sin θ = −X_g i_d`,
for every loop gain `D₀`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_equilibrium_eq_zero_iff {θ : ℝ} :
    field p (equilibrium θ) = 0 ↔ p.V * Real.sin θ = -(p.Xg * p.Id) := by
  refine ⟨fun h => ?_, fun heq => ?_⟩
  · have h1 : field p (equilibrium θ) 1 =
        gridQ p θ - p.Lg * field p (equilibrium θ) 0 * p.Id := by
      simp [field, Dynamics.lift, coordField, equilibrium, pllOut, vq]
    simp only [h, PiLp.zero_apply, mul_zero, zero_mul, sub_zero] at h1
    unfold gridQ at h1
    linarith
  · have hq : gridQ p θ = 0 := by unfold gridQ; linarith
    apply Dynamics.lift_toLp_eq_zero
    ext i
    fin_cases i <;> simp [coordField, vq, pllOut, hq]

/-- With a zero frozen current the rate-coupled field is the SRF-PLL field: `D₀ = 1` and
`v_q = −V sin θ` (`PLL.srfField V k_p k_i 0`, `theorem/GridTiedConverter/PLL/Model.lean`). -/
@[tmio M, powerlib_domain] theorem field_eq_srfField (hId : p.Id = 0) :
    field p = PLL.srfField p.V p.kp p.ki 0 := by
  funext y
  ext i
  fin_cases i <;>
    simp [field, Dynamics.lift, coordField, pllOut, vq, gridQ, Params.D0, hId, PLL.srfField,
      PLL.piPLLField, PLL.srfPD]

@[tmio M, powerlib_domain] theorem contDiff_field : ContDiff ℝ 1 (field p) := by
  apply Dynamics.contDiff_lift
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [coordField, vq, pllOut, gridQ] <;> fun_prop

@[tmio M, powerlib_domain] theorem hasFDerivAt_coordField (hD0 : p.D0 ≠ 0) (y : Fin 2 → ℝ) :
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

@[tmio M, powerlib_domain] theorem fderiv_field (hD0 : p.D0 ≠ 0) (θ x : ℝ) :
    fderiv ℝ (field p) (WithLp.toLp 2 ![θ, x]) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jac p θ) := by
  have := hasFDerivAt_coordField p hD0 ![θ, x]
  exact (Dynamics.hasFDerivAt_lift (by simpa using this)).fderiv

/-- Jacobian at an equilibrium in the source form
`(1/D₀) [[−k_p V cos θ, k_i], [−V cos θ, k_i V sin θ / ω_s]]`. -/
@[tmio M, powerlib_domain] theorem jacobian_eq {θ : ℝ} (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    jac p θ = !![-p.kp * p.V * Real.cos θ / p.D0, p.ki / p.D0;
      -p.V * Real.cos θ / p.D0, p.ki * (p.V * Real.sin θ / p.ωs) / p.D0] := by
  have : p.Lg * p.Id = -(p.V * Real.sin θ / p.ωs) := by
    rw [Params.Lg, heq]
    ring
  simp only [jac, mul_assoc, this, mul_neg, neg_neg]

@[tmio M, powerlib_domain] theorem trace_jac (θ : ℝ) :
    (jac p θ).trace = (-p.kp * p.V * Real.cos θ - p.ki * p.Lg * p.Id) / p.D0 := by
  rw [jac, Matrix.trace_fin_two_of]
  ring

@[tmio M, powerlib_domain] theorem det_jac (hD0 : p.D0 ≠ 0) (θ : ℝ) :
    (jac p θ).det = p.ki * p.V * Real.cos θ / p.D0 := by
  rw [jac, Matrix.det_fin_two_of]
  have hD : p.D0 = 1 + p.kp * p.Lg * p.Id := rfl
  field_simp
  rw [hD]
  ring

@[tmio M, powerlib_domain] theorem det_jac_pos (hD0 : 0 < p.D0) (hV : 0 < p.V) (hki : 0 < p.ki)
    {θ : ℝ} (hcos : 0 < Real.cos θ) : 0 < (jac p θ).det := by
  rw [det_jac p hD0.ne']
  positivity

/-- At an equilibrium, `tr J = (V/ω_s)(k_i sin θ − ω_s k_p cos θ) / D₀`. -/
@[tmio M, powerlib_domain] theorem trace_jac_eq (hωs : p.ωs ≠ 0) {θ : ℝ}
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    (jac p θ).trace =
      p.V / p.ωs * (p.ki * Real.sin θ - p.ωs * p.kp * Real.cos θ) / p.D0 := by
  have hLI : p.Lg * p.Id = -(p.V * Real.sin θ / p.ωs) := by rw [Params.Lg, heq]; ring
  rw [trace_jac, mul_assoc p.ki, hLI]
  field_simp
  ring

/-- At an equilibrium with `cos θ ≠ 0`, `tr J = (V k_i cos θ / (ω_s D₀)) (tan θ − ω_s k_p / k_i)`:
for a positive prefactor the sign of `tr J` is the side of the boundary angle. -/
@[tmio M, powerlib_domain] theorem trace_jac_eq_mul_tan_sub (hki : p.ki ≠ 0) (hωs : p.ωs ≠ 0)
    {θ : ℝ} (hcos : Real.cos θ ≠ 0) (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    (jac p θ).trace =
      p.V * p.ki * Real.cos θ / (p.ωs * p.D0) * (Real.tan θ - p.ωs * p.kp / p.ki) := by
  rw [trace_jac_eq p hωs heq, Real.tan_eq_sin_div_cos]
  by_cases hD0 : p.D0 = 0
  · simp [hD0]
  · field_simp

/-- At an equilibrium, `tr J < 0 ↔ tan θ < ω_s k_p / k_i`. -/
@[tmio M, powerlib_domain] theorem trace_jac_neg_iff (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    (jac p θ).trace < 0 ↔ Real.tan θ < p.ωs * p.kp / p.ki := by
  have hc : 0 < p.V * p.ki * Real.cos θ / (p.ωs * p.D0) := by positivity
  rw [trace_jac_eq_mul_tan_sub p hki.ne' hωs.ne' hcos.ne' heq]
  exact ⟨fun h => sub_neg.mp (neg_of_mul_neg_right h hc.le),
    fun h => mul_neg_of_pos_of_neg hc (sub_neg.mpr h)⟩

/-- At an equilibrium, `tr J > 0 ↔ tan θ > ω_s k_p / k_i`. -/
@[tmio M, powerlib_domain] theorem trace_jac_pos_iff (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    0 < (jac p θ).trace ↔ p.ωs * p.kp / p.ki < Real.tan θ := by
  have hc : 0 < p.V * p.ki * Real.cos θ / (p.ωs * p.D0) := by positivity
  rw [trace_jac_eq_mul_tan_sub p hki.ne' hωs.ne' hcos.ne' heq, mul_pos_iff_of_pos_left hc, sub_pos]

/-- The Jacobian is Hurwitz exactly below the boundary angle. -/
@[tmio TM, powerlib_domain] theorem isHurwitz_jac_iff (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    LinearSystems.IsHurwitz (jac p θ) ↔ Real.tan θ < p.ωs * p.kp / p.ki := by
  rw [Criteria.isHurwitz_fin_two_iff, trace_jac_neg_iff p hD0 hV hki hωs hcos heq]
  exact ⟨fun h => h.1, fun h => ⟨h, det_jac_pos p hD0 hV hki hcos⟩⟩

/-- On the boundary `tan θ = ω_s k_p / k_i` the Jacobian has zero trace. -/
@[tmio M, powerlib_domain] theorem trace_jac_eq_zero_of_tan_eq (hki : 0 < p.ki) (hωs : 0 < p.ωs)
    {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) (htan : Real.tan θ = p.ωs * p.kp / p.ki) :
    (jac p θ).trace = 0 := by
  rw [trace_jac_eq_mul_tan_sub p hki.ne' hωs.ne' hcos.ne' heq, htan, sub_self, mul_zero]

/-- On the boundary `tan θ = ω_s k_p / k_i` the Jacobian has the imaginary pair `± j√det`
(`det J > 0` is `det_jac_pos`). -/
@[tmio M, powerlib_domain] theorem imaginary_pair_at_boundary (hD0 : 0 < p.D0) (hV : 0 < p.V)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) (htan : Real.tan θ = p.ωs * p.kp / p.ki) :
    (Linear.characteristicMatrix (jac p θ) (Complex.I * Real.sqrt (jac p θ).det)).det = 0 := by
  have htr := trace_jac_eq_zero_of_tan_eq p hki hωs hcos heq htan
  have hdet := det_jac_pos p hD0 hV hki hcos
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
@[tmio M, powerlib_domain] theorem field_eq_literatureField :
    field p = literatureField { p with Id := -p.Id } := by
  funext y
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [field, literatureField, Dynamics.lift, coordField, pllOut, vq, gridQ, Params.D0,
      Params.Lg] <;> ring

/-! ## Damping-ratio comparison and `X_g` elimination -/

/-- At an equilibrium the loop factor is `D₀ = 1 − k_p V sin θ / ω_s`. -/
@[tmio M, powerlib_domain] theorem D0_eq_of_equilibrium {θ : ℝ}
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    p.D0 = 1 - p.kp * p.V * Real.sin θ / p.ωs := by
  rw [Params.D0, Params.Lg, mul_assoc p.kp, div_mul_eq_mul_div]
  linear_combination (p.kp / p.ωs) * heq

/-- Quasi-static PLL damping ratio: the PI-PLL damping ratio `PLL.zeta` at the detector slope
`V cos θ`, `(k_p/2) √(V cos θ / k_i)` for `V cos θ, k_i > 0` (`PLL.zeta_eq`). -/
def zetaQS (θ : ℝ) : ℝ := PLL.zeta (p.V * Real.cos θ) p.kp p.ki

/-- The rate-coupled damping ratio equals the quasi-static closed form times
`(1 − r)/√D₀`, `r = tan θ / (ω_s k_p / k_i)`, `D₀ = 1 − k_p V sin θ / ω_s`. -/
@[tmio M, powerlib_domain] theorem zeta_ratio (hD0 : 0 < p.D0) (hV : 0 < p.V) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    Criteria.dampingRatio (jac p θ) =
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
  rw [Criteria.dampingRatio, neg_div, ← neg_div, htr, hdet, h1, zetaQS, PLL.zeta_eq hS hki, h2]
  set a := Real.sqrt (p.V * Real.cos θ)
  set b := Real.sqrt p.ki
  set c := Real.sqrt p.D0
  set r := 1 - Real.tan θ / (p.ωs * p.kp / p.ki)
  rw [← ha, ← hc]
  field_simp

/-- At an equilibrium angle the Jacobian depends on `(V, ω_s, k_p, k_i, θ)` only: two
parameter sets that differ in `X_g` (with `I_d` re-solved to keep `θ` an equilibrium) have the
same Jacobian. -/
@[tmio M, powerlib_domain] theorem jacobian_indep_Xg (q : Params) (hV : p.V = q.V)
    (hωs : p.ωs = q.ωs) (hkp : p.kp = q.kp) (hki : p.ki = q.ki) {θ : ℝ}
    (hp : p.V * Real.sin θ = -(p.Xg * p.Id)) (hq : q.V * Real.sin θ = -(q.Xg * q.Id)) :
    jac p θ = jac q θ := by
  have hDp := D0_eq_of_equilibrium p hp
  have hDq := D0_eq_of_equilibrium q hq
  rw [jacobian_eq p hp, jacobian_eq q hq, hDp, hDq, hV, hωs, hkp, hki]

/-- Source tuning rule `k_p = 2 ζ₀ ω_{n0} / V`, `k_i = ω_{n0}² / V`, `ω_{n0} = 2π f_{n0}`:
`ω_s k_p / k_i = ω_s ζ₀ / (π f_{n0})`, i.e. `tan θ_H = ω_s ζ₀ / (π f_{n0})`. -/
@[tmio T, powerlib_foundation] theorem omega_kp_div_ki_of_pllGains (ωs fn0 ζ0 V : ℝ) (hV : V ≠ 0)
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
@[tmio TM, powerlib_domain] theorem frozen_isHurwitz_iff (hD0 : 0 < p.D0) (hkp : 0 < p.kp)
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
@[tmio TM, powerlib_domain] theorem frozen_hurwitz_forall_iff (hD0 : 0 < p.D0) (hkp : 0 < p.kp)
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
@[tmio M, powerlib_domain] theorem Model.field_contDiff (m : Model) : ContDiff ℝ 1 m.field :=
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

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

/-- A flow sentence of a model is the sentence of the untranslated field at `(θ*, 0)`. -/
@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (RatePLL.field m.params) (equilibrium m.θ) :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => RatePLL.field m.params)
    (pt := fun m => equilibrium m.θ) family_isAutonomous

/-! ### Soundness of the translation -/

/-- No model has both a stable and an unstable Jacobian: the whole requirement language is
inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
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
  refine Spectral.chain_le_semantics_of_jacobian (fun m P => mem_den_flow_iff)
    family_isAutonomous.den_passive (Rs := {.equilibrium, .jacobianStable})
    (Ru := {.equilibrium, .jacobianUnstable})
    (fun s => by rcases s with P | _ | _ <;> (try cases P) <;> rfl) (fun m => jac m.params m.θ)
    (fun m hm => ?_) (fun m hm => ?_) fun m hm => ?_
  · have he : Meets m .equilibrium := by
      rcases hm with hm | hm <;> exact (TMIO.mem_realize _ _ _).mp hm .equilibrium (by simp)
    exact ⟨contDiff_field m.params, (field_equilibrium_eq_zero_iff m.params).mpr he.1,
      fderiv_field m.params he.2 m.θ 0⟩
  · exact (Criteria.isHurwitz_fin_two_iff _).2 ((TMIO.mem_realize _ _ _).mp hm .jacobianStable
      (by simp))
  · exact Criteria.exists_root_re_pos_of_violation_fin_two _
      ((TMIO.mem_realize _ _ _).mp hm .jacobianUnstable (by simp))

/-! ### Exactness of the local exponential translation -/

/-- With a degenerate algebraic loop `D₀ = 0` the angle is frozen: `θ` is a linear first
integral of the field, so no point is locally exponentially stable. -/
@[tmio TM, powerlib_domain] private theorem not_les_of_D0_eq_zero {p : Params} (hD0 : p.D0 = 0) (x : Dynamics.State 2) :
    ¬ LocallyExponentiallyStable (RatePLL.field p) x := by
  refine Dynamics.not_locallyExponentiallyStable_of_firstIntegral (contDiff_field p)
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) ?_ fun y => ?_
  · intro h
    have := congrArg (fun L : Dynamics.State 2 →L[ℝ] ℝ => L (EuclideanSpace.single 0 1)) h
    simp at this
  · simp [RatePLL.field, Dynamics.lift, coordField, pllOut, hD0]

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
    (fun m _ hm => Family.chain_le_semantics_iff.mp chain_le_semantics _ hm)
    (fun m _ hD0 h => ?_) (fun m _ _ => contDiff_field m.params)
    (fun m _ hD0 => fderiv_field m.params hD0 m.θ 0) fun m _ hD0 he hH => ?_)
  · exact not_les_of_D0_eq_zero (not_not.mp hD0) _ (mem_den_flow_iff.mp h)
  · rw [Criteria.isHurwitz_fin_two_iff] at hH
    rw [(connection_proof% TMIO.mem_realize)]
    rintro q (rfl | rfl)
    · exact And.intro ((field_equilibrium_eq_zero_iff m.params).mp he) hD0
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
  refine Family.chain_le_semantics_iff.mp chain_le_semantics _
    ((TMIO.mem_realize _ _ _).mpr fun q hq => ?_)
  rcases hq with rfl | rfl
  exacts [⟨heq, hD0.ne'⟩,
    ⟨(trace_jac_neg_iff p hD0 hV hki hωs hcos heq).2 htan, det_jac_pos p hD0 hV hki hcos⟩]

/-- Rate-coupled GFL PLL: above the angle `tan θ_H = ω_s k_p / k_i` the operating point
`(θ, 0)` is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_tan_gt (p : Params) (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) (htan : p.ωs * p.kp / p.ki < Real.tan θ) :
    connection% (Model.mk p θ ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mp chain_le_semantics _
    ((TMIO.mem_realize _ _ _).mpr fun q hq => ?_)
  rcases hq with rfl | rfl
  exacts [⟨heq, hD0.ne'⟩, Or.inl ((trace_jac_pos_iff p hD0 hV hki hωs hcos heq).2 htan)]

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
def offEquilibrium : Model := ⟨⟨0, ⟨0, 1, 0⟩, 1, 0, 0, -1, rfl⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[tmio TM, powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff) (contDiff_field _)
    fun h => ?_
  have := congrArg (fun y : Dynamics.State 2 => y 1) h
  simp [Passive.SeriesRLC.reactance, Params.Xg, offEquilibrium, RatePLL.field, Dynamics.lift,
      coordField, equilibrium, vq, pllOut, gridQ, Params.D0, Params.Lg] at this

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for an equilibrium. -/
@[tmio TM, powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .equilibrium)
    (by simp [family, translate]) (by simp [Passive.SeriesRLC.reactance, Params.Xg,
        family, Meets, offEquilibrium])

/-! ### The Lyapunov translation -/

/-- An undamped PLL: `V = k_i = ω_s = 1`, `k_p = X_g = i_d = 0` (so `D₀ = 1`) at `θ* = 0`; the
field is the pendulum `θ̇ = x`, `ẋ = −sin θ`. -/
def undampedPLL : Model := ⟨⟨1, ⟨0, 0, 0⟩, 1, 0, 1, 0, rfl⟩, 0⟩

/-- The undamped PLL is Lyapunov stable at `θ* = 0`: with `i_d = 0` its field is the SRF-PLL field
(`field_eq_srfField`) with `V = k_i = 1`, `k_p = 0`, the pendulum `θ̇ = x`, `ẋ = −sin θ`, whose
lower equilibrium is Lyapunov stable (`PhasePlane.Pendulum.origin_lyapunovStable`). Its Jacobian
`[[0, 1], [−1, 0]]` has trace `0`, so it meets no stable-Jacobian requirement. -/
@[tmio TM, powerlib_domain] theorem undampedPLL_mem_den_lyapunovStable :
    connection% (undampedPLL ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr ?_
  change LyapunovStable _ _
  have hpt : equilibrium undampedPLL.θ = PhasePlane.mk 0 0 := by
    rw [PhasePlane.ext_iff']
    simp [equilibrium, undampedPLL]
  have hf : RatePLL.field undampedPLL.params = PhasePlane.Pendulum.field 1 := by
    rw [field_eq_srfField _ rfl]
    funext z
    rw [PhasePlane.ext_iff']
    simp [PLL.srfField, PLL.piPLLField, PLL.srfPD, PhasePlane.Pendulum.field,
      PhasePlane.Pendulum.torque, undampedPLL]
  rw [hpt, hf]
  exact PhasePlane.Pendulum.origin_lyapunovStable one_ne_zero

/-- The Lyapunov translation is sound but not exact: the undamped PLL is Lyapunov stable at an
equilibrium whose Jacobian has trace `0`. -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness undampedPLL_mem_den_lyapunovStable (q := .jacobianStable)
    (by simp [family, translate]) fun hs => ?_
  have := (hs : Meets undampedPLL .jacobianStable).1
  simp [Passive.SeriesRLC.reactance, Params.Xg, jac, Matrix.trace_fin_two, undampedPLL, Params.D0,
      Params.Lg] at this

end powerlib.GFL.RatePLL
