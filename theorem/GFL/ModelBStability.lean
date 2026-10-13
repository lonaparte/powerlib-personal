import theorem.GFL.ReducedOrder
import theorem.Criteria.Routh4
import theorem.Criteria.Jacobian
import theorem.Dynamics.Basin
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Flow.Shift
import theorem.TMIO.ClaimElab
import theorem.CurrentControl.SISO
import theorem.Dynamics.ModelBLocal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # GFL reduced-order model B: local stability by linearization (4×4 Routh–Hurwitz)

Model boundary. The system is `ModelBParams.field` of
`theorem/GFL/ReducedOrder.lean` (T-gfl-reduced-order-dynamics §1.6): continuous-time autonomous
field on `State 4`, state order `x = (Δθ, x_pll, V_dc, ξ_v)` (PLL phase error `θ̂ − θ_g`, swing
sign; PLL integrator; DC-link voltage; DC-voltage-loop integrator), constant grid frequency `ω_g`,
infinite bus `V_g` behind `Z_g = R_g + j X_g`, inner current loop eliminated (`i = i*`),
`i_d* = k_pv (V_dc* − V_dc) + k_iv ξ_v`, reactive current frozen at `i_q0`, IN-positive currents,
`P_bridge` replaced by the PCC power `(3/2)(v_d i_d + v_q i_q)`. No saturation, PWM, delay,
feed-forward filter or decoupling mismatch. Parameters are arbitrary reals except `V_dc* > 0`.
Level: local behaviour at an equilibrium (linearization), not a basin estimate.

The field contains `1/V_dc` and is therefore not globally `C¹`; the powerlib linearization
theorems need a globally `C¹` field. This module
* proves that local exponential stability and instability only depend on the field on a ball
  around the equilibrium (`locallyExponentiallyStable_of_eqOn_ball`, `unstable_of_eqOn_ball`,
  first-exit argument on finite solution segments);
* builds a globally `C¹` field `regField` that coincides with `field` on `{V_dc > 3V_dc*/4}`
  (the denominator `V_dc` is replaced by a smooth `regDen ≥ V_dc*/2`), which contains a ball
  around every equilibrium (equilibria have `V_dc = V_dc*`);
* computes the Jacobian of `field` at any state with `V_dc ≠ 0` from the field with `fderiv`
  (`hasFDerivAt_field`, `jacobian`), with `c = cos Δθ`, `s = sin Δθ`, `i_d = i_d*(x)`,
  `v_d = v_{g,d}(x)`, `P = v_d i_d + v_q i_q0`:
  `[[−k_p V_g c, k_i, k_p X_g k_pv, −k_p X_g k_iv],`
  ` [−V_g c, 0, X_g k_pv, −X_g k_iv],`
  ` [3(−V_g s i_d − V_g c i_q0)/(2 V_dc C_dc), 0, 3(k_pv(R_g i_d − v_d + X_g i_q0) V_dc − P)/(2 V_dc² C_dc),`
  `  3 k_iv (v_d − R_g i_d − X_g i_q0)/(2 V_dc C_dc)],`
  ` [0, 0, −1, 0]]`.

Results (`modelB_locallyExponentiallyStable`, `modelB_unstable_of_det_neg`): at an equilibrium,
the 4×4 Routh conditions on the Jacobian (`tr < 0`, `m₃ < 0`, `det > 0`,
`m₃² + tr² det < tr m₂ m₃`, i.e. `a3, a1, a0 > 0`, `a1² + a3² a0 < a3 a2 a1` for the characteristic
polynomial `s⁴ + a3 s³ + a2 s² + a1 s + a0`) give local exponential stability; `det J < 0` gives
instability. The trigonometric values `cos Δθ*`, `sin Δθ*` enter as exact real numbers (no
floating point). Only the sufficient direction of Routh–Hurwitz is used.
Non-vacuity (`modelB_noLoad_locallyExponentiallyStable`): at the no-load point (`I₀ = 0`, `R_g = 0`,
`i_q0 = 0`, positive gains, `V_g, V_dc*, C_dc > 0`) the equilibrium `(0, (ω_g − ω_s)/k_i, V_dc*, 0)`
satisfies the Routh conditions and is locally exponentially stable.

Source: work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.6 (model B), §1.7 (equilibria);
local-stability statement requested as the "4×4 Routh–Hurwitz of model B" item (the note itself
states no stability condition for model B).

## Family and connection conclusions
`ModelB.family` reads a complete system `ModelB.Model` — the model-B parameters `p` and a
selected state `x*` — as the autonomous field `z ↦ p.field (z + x*)`, so that the library
semantics at the origin speaks about `x*` (`Flow.Property.holds_shift_iff`). Requirements are
static: `x*` is a zero of the field, `V_dc* > 0`, the 4×4 Routh conditions on `jacobian x*`,
`det (jacobian x*) < 0`, or `jacobian x*` off the Routh boundary (`offBoundary`, used only as a
context). The local sentences translate into the first three, instability into the
first two and the determinant condition, passivity into nothing; the global sentences, decay
rates, sampled contraction and conservation into the whole (inconsistent) language. Connection
conclusions: soundness (`chain_le_semantics`), exact passivity (`exact_passive`), and the former
domain theorems as memberships (`mem_den_locallyExponentiallyStable`,
`mem_den_unstable_of_det_neg`, `noLoad_mem_den_locallyExponentiallyStable`). At equilibria with
positive reference the local exponential translation is exact
(`exactUnder_locallyExponentiallyStable`, context `{equilibrium, positiveReference}`): by the
converse linearization theorem applied to `regField`
(`Dynamics.isHurwitz_of_locallyExponentiallyStable`) local exponential stability forces a
Hurwitz Jacobian, i.e. the 4×4 Routh conditions
(`Criteria.isHurwitz_fin_four_iff`). The untranslated
local-stability statements are private implementation evidence; the ball-locality lemmas, the
regularized field and the Jacobian are foundation.

Without that context the local exponential translation is not exact
(`not_exact_locallyExponentiallyStable`, and not even within the context of an equilibrium,
`not_exactUnder_equilibrium_locallyExponentiallyStable`): the converter `negativeReference`
with a negative DC-voltage reference `V_dc* = −1` and negative DC-loop gains is locally
exponentially stable (`negativeReference_mem_den_locallyExponentiallyStable`). Model B is `C¹`
on `V_dc ≠ 0` (`ModelBParams.field_contDiffOn`, both signs), so on either side the converse
linearization theorem for locally `C¹` fields applies directly and no separate negative-side
regularization is needed: for every selected state with `V_dc* ≠ 0`,
`mem_den_locallyExponentiallyStable_iff` (an equilibrium whose Jacobian satisfies the 4×4 Routh
conditions; at an equilibrium `V_dc* = V_dc,ref`, so the positive-reference requirement is what
excludes the negative side from the translation). On the singular plane `V_dc = 0` the field is
read with Lean's `x / 0 = 0`: the power term vanishes and the DC components are `I₀ / C_dc` and
`V_dc,ref` (`ModelBParams.field_eq_zero_iff_of_Vdc_eq_zero`); an equilibrium there
(`V_dc,ref = 0`, `I₀ / C_dc = 0`) lies on a curve of equilibria of that plane and is neither
locally asymptotically nor exponentially stable
(`not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero`,
`not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero`).

Selected states on the singular plane that are not equilibria. With `P = pccP x*`:
* `mem_den_locallyExponentiallyStable_of_collapse`: if the power term drives `V_dc` into the plane
  from both sides (`P / C_dc < 0`) and the injection crosses it (`I₀ / C_dc ≠ 0`), the state
  satisfies the segment-based local exponential estimate although it is not an equilibrium: near
  `x*`, `d(V_dc²)/dt = (2 I₀ V_dc + 3 P) / C_dc` is bounded below zero, so solution segments end
  before reaching the plane, after a time `O(V_dc(t₀)²)` (generic
  `Dynamics.locallyExponentiallyStable_of_collapse`, `theorem/Dynamics/ModelBLocal.lean`). The
  estimate holds because solutions cease, not because they converge.
* `mem_den_unstable_of_repel`: if `P / C_dc > 0` the state is unstable (`V_dc²` grows linearly;
  generic `Dynamics.unstable_of_repel`).
* `not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero_of_I0`: if `I₀ / C_dc = 0` (in particular
  `C_dc = 0`) no state on the plane is locally exponentially stable (the smooth field
  `(f₀, f₁, 0, f₃)` agrees with model B on the invariant plane).
* `mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero`: hence for `P / C_dc ≠ 0`, local
  exponential stability on the plane holds exactly when `P / C_dc < 0 ∧ I₀ / C_dc ≠ 0`. The
  degenerate power balance `P(x*) = 0` is treated in `theorem/GFL/ModelBCollapse.lean`: with
  `q = (I₀ V_dc + (3/2) P) / C_dc`, the pair `(V_dc, q)` is, in the time `dt / V_dc`, a linear
  system whose discriminant `D = H² + 4G` decides: `D > 0` ⇒ unstable
  (`mem_den_unstable_of_disc_pos`), `D < 0` with `I₀ / C_dc ≠ 0` ⇒ the local exponential estimate
  (`mem_den_locallyExponentiallyStable_of_disc_neg`), and
  `mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nondegenerate` characterizes the whole
  plane except the degenerate set `{P = 0, I₀ / C_dc ≠ 0, D = 0}` (UNPROVED there: a double root
  of the reduced system, decided by higher-order terms).
* The concrete `collapsePoint` (`V_dc,ref = 1 > 0`, `x* = (0, 0, 0, −1)`) is such a collapse state
  (`collapsePoint_mem_den_locallyExponentiallyStable`). Therefore none of the local translations
  is exact within the context of a positive reference alone
  (`not_exactUnder_positiveReference_locallyExponentiallyStable`,
  `not_exactUnder_positiveReference_locallyAsymptoticallyStable`,
  `not_exactUnder_positiveReference_lyapunovStable`); for the local exponential sentence the exact
  context is that of an equilibrium with positive reference
  (`exactUnder_locallyExponentiallyStable`).

The local asymptotic and Lyapunov translations are not exact (`not_exact_locallyAsymptoticallyStable`,
`not_exact_lyapunovStable`, the same witness). At equilibria with positive reference they are exact
off the 4×4 Routh boundary and not exact on it: requirement `Requirement.offBoundary` (Routh
conditions or a strict violation `RouthViolationFin4`), with the conclusions
`exactUnder_offBoundary_lyapunovStable`, `exactUnder_offBoundary_locallyAsymptoticallyStable`,
`not_exactUnder_lyapunovStable`, `not_exactUnder_locallyAsymptoticallyStable` and three boundary
witnesses (asymptotically stable, stable but not attractive, unstable) in
`theorem/GFL/ModelBBoundary.lean`.
-/

noncomputable section
namespace powerlib.GFL
open Set Filter Matrix
open scoped Topology
open powerlib.Dynamics (State)

/-! ## Local stability notions depend only on the field near the equilibrium -/

/-- First-exit argument: a curve continuous on `[t₀, t₁]` that starts strictly inside the ball of
radius `ρ` and is strictly inside at every `s` up to which it has stayed in the closed ball,
stays strictly inside on the whole interval. -/
@[powerlib_foundation] theorem forall_norm_sub_lt_of_first_exit {n : ℕ} {φ : ℝ → State n}
    {x : State n} {t₀ t₁ ρ : ℝ} (hφ : ContinuousOn φ (Icc t₀ t₁)) (h0 : ‖φ t₀ - x‖ < ρ)
    (hstep : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ ≤ ρ) → ‖φ s - x‖ < ρ) :
    ∀ u ∈ Icc t₀ t₁, ‖φ u - x‖ < ρ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, hu'⟩ := hcon
  set A : Set ℝ := Icc t₀ t₁ ∩ φ ⁻¹' {y | ρ ≤ ‖y - x‖} with hAdef
  have hAne : A.Nonempty := ⟨u, hu, hu'⟩
  have hAclosed : IsClosed A :=
    hφ.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right x)))
  have hAbdd : BddBelow A := ⟨t₀, fun t ht => ht.1.1⟩
  have hτA : sInf A ∈ A := hAclosed.csInf_mem hAne hAbdd
  have hbelow : ∀ t ∈ Ico t₀ (sInf A), ‖φ t - x‖ < ρ := by
    intro t ht
    by_contra h
    push Not at h
    have : sInf A ≤ t := csInf_le hAbdd ⟨⟨ht.1, ht.2.le.trans hτA.1.2⟩, h⟩
    linarith [ht.2]
  have hle : ∀ t ∈ Icc t₀ (sInf A), ‖φ t - x‖ ≤ ρ := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rcases eq_or_lt_of_le hτA.1.1 with h' | h'
      · rw [h, ← h']; exact h0.le
      · have hcl : IsClosed (Icc t₀ (sInf A) ∩ φ ⁻¹' {y | ‖y - x‖ ≤ ρ}) :=
          (hφ.mono (Icc_subset_Icc le_rfl hτA.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
            (isClosed_le (continuous_norm.comp (continuous_sub_right x)) continuous_const)
        have hsub : Ico t₀ (sInf A) ⊆ Icc t₀ (sInf A) ∩ φ ⁻¹' {y | ‖y - x‖ ≤ ρ} :=
          fun t' ht' => ⟨Ico_subset_Icc_self ht', (hbelow t' ht').le⟩
        have hcl' := hcl.closure_subset_iff.mpr hsub
        rw [closure_Ico h'.ne] at hcl'
        exact (hcl' ht).2
    · exact (hbelow t ⟨ht.1, h⟩).le
  exact absurd hτA.2 (not_le.mpr (hstep _ hτA.1 hle))

/-- Local exponential stability only depends on the field on a ball around the equilibrium. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_eqOn_ball {n : ℕ}
    {f g : State n → State n} {x : State n} {R : ℝ} (hR : 0 < R)
    (hfg : ∀ y ∈ Metric.ball x R, f y = g y) (hg : LocallyExponentiallyStable g x) :
    LocallyExponentiallyStable f x := by
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ := hg
  have hC0 : 0 < C := by linarith
  refine ⟨min r (R / (2 * C)), C, a, lt_min hr (by positivity), hC, ha, ?_⟩
  intro t₀ t₁ φ hφ h0
  have h0r : ‖φ t₀ - x‖ < r := lt_of_lt_of_le h0 (min_le_left _ _)
  have h0R : C * ‖φ t₀ - x‖ < R / 2 := by
    have h := lt_of_lt_of_le h0 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  have hexp : ∀ t, t₀ ≤ t →
      C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖ ≤ C * ‖φ t₀ - x‖ := by
    intro t ht
    have h1 : Real.exp (-a * (t - t₀)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : 0 ≤ C * ‖φ t₀ - x‖ := by positivity
    calc C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖
        = Real.exp (-a * (t - t₀)) * (C * ‖φ t₀ - x‖) := by ring
      _ ≤ 1 * (C * ‖φ t₀ - x‖) := mul_le_mul_of_nonneg_right h1 h2
      _ = C * ‖φ t₀ - x‖ := one_mul _
  have key : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ ≤ R / 2) →
      ∀ t ∈ Icc t₀ s, ‖φ t - x‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖ := by
    intro s hs hin
    have hseg : IsTrajectoryOn φ g t₀ s :=
      Dynamics.isIntegralCurveOn_of_eq_on_curve (hφ.mono (Icc_subset_Icc le_rfl hs.2))
        (fun u hu => hfg _ (by rw [Metric.mem_ball, dist_eq_norm]; linarith [hin u hu]))
    exact hb t₀ s φ hseg h0r
  have hC1 : ‖φ t₀ - x‖ ≤ C * ‖φ t₀ - x‖ := le_mul_of_one_le_left (norm_nonneg _) hC
  have hstay := forall_norm_sub_lt_of_first_exit (x := x) (ρ := R / 2) hφ.continuousOn (by linarith)
    (fun s hs hin => by
      have := key s hs hin s ⟨hs.1, le_rfl⟩
      linarith [hexp s hs.1])
  intro t ht
  exact key t₁ ⟨ht.1.trans ht.2, le_rfl⟩ (fun u hu => (hstay u hu).le) t ht

/-- Lyapunov stability only depends on the field on a ball around the equilibrium. -/
@[powerlib_foundation] theorem lyapunovStable_of_eqOn_ball {n : ℕ}
    {f g : State n → State n} {x : State n} {R : ℝ} (hR : 0 < R)
    (hfg : ∀ y ∈ Metric.ball x R, f y = g y) (hg : LyapunovStable g x) :
    LyapunovStable f x := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hg (min ε (R / 2)) (lt_min hε (by positivity))
  refine ⟨min δ (min ε (R / 2)), lt_min hδ (lt_min hε (by positivity)), ?_⟩
  intro t₀ t₁ φ hφ h0
  have h0δ : ‖φ t₀ - x‖ < δ := lt_of_lt_of_le h0 (min_le_left _ _)
  have h0ε : ‖φ t₀ - x‖ < min ε (R / 2) := lt_of_lt_of_le h0 (min_le_right _ _)
  have hstay := forall_norm_sub_lt_of_first_exit hφ.continuousOn h0ε (fun s hs hin => by
    have hseg : IsTrajectoryOn φ g t₀ s :=
      Dynamics.isIntegralCurveOn_of_eq_on_curve (hφ.mono (Icc_subset_Icc le_rfl hs.2))
        (fun u hu => hfg _ (by
          rw [Metric.mem_ball, dist_eq_norm]
          have := hin u hu
          have : min ε (R / 2) ≤ R / 2 := min_le_right _ _
          linarith))
    exact hb t₀ s φ hseg h0δ s ⟨hs.1, le_rfl⟩)
  intro t ht
  exact lt_of_lt_of_le (hstay t ht) (min_le_left _ _)

/-- Instability only depends on the field on a ball around the equilibrium. -/
@[powerlib_foundation] theorem unstable_of_eqOn_ball {n : ℕ}
    {f g : State n → State n} {x : State n} {R : ℝ} (hR : 0 < R)
    (hfg : ∀ y ∈ Metric.ball x R, f y = g y) (hg : Unstable g x) :
    Unstable f x := fun hf =>
  hg (lyapunovStable_of_eqOn_ball hR (fun y hy => (hfg y hy).symm) hf)

/-! ## A smooth positive denominator -/

/-- Smooth denominator: `regDen V v = v` for `v ≥ 3V/4` and `regDen V v ≥ V/2` (`V > 0`). -/
def regDen (V v : ℝ) : ℝ :=
  Real.smoothTransition (4 * v / V - 2) * v +
    (1 - Real.smoothTransition (4 * v / V - 2)) * (V / 2)

@[powerlib_foundation] theorem regDen_eq {V v : ℝ} (hV : 0 < V) (hv : 3 * V / 4 ≤ v) :
    regDen V v = v := by
  have h : 1 ≤ 4 * v / V - 2 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hV]
    linarith
  simp [regDen, Real.smoothTransition.one_of_one_le h]

@[powerlib_foundation] theorem half_le_regDen {V : ℝ} (hV : 0 < V) (v : ℝ) :
    V / 2 ≤ regDen V v := by
  unfold regDen
  have hs0 := Real.smoothTransition.nonneg (4 * v / V - 2)
  have hs1 := Real.smoothTransition.le_one (4 * v / V - 2)
  by_cases hv : V / 2 ≤ v
  · nlinarith
  · have h : 4 * v / V - 2 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ hV]
      linarith
    rw [Real.smoothTransition.zero_of_nonpos h]
    simp

@[powerlib_foundation] theorem contDiff_regDen (V : ℝ) : ContDiff ℝ 1 (regDen V) := by
  have h : ContDiff ℝ 1 (fun v : ℝ => Real.smoothTransition (4 * v / V - 2)) :=
    (Real.smoothTransition.contDiff (n := 1)).comp (by fun_prop)
  unfold regDen
  exact (h.mul contDiff_id).add ((contDiff_const.sub h).mul contDiff_const)

namespace ModelBParams

variable (p : ModelBParams)

/-! ## A globally `C¹` field equal to model B near its equilibria -/

/-- PCC active-power-like product `P = v_d i_d + v_q i_q0` as a function of the state. -/
def pccP (x : State 4) : ℝ :=
  p.vgd (x 0) (p.idRef (x 2) (x 3)) * p.idRef (x 2) (x 3) +
    p.vgq (x 0) (p.idRef (x 2) (x 3)) * p.iq0

/-- Model B with the denominator `V_dc` replaced by `regDen V_dc* V_dc`. -/
def regField (x : State 4) : State 4 :=
  let id := p.idRef (x 2) (x 3)
  WithLp.toLp 2 ![p.ωs - p.ωg + p.kp * p.vgq (x 0) id + p.ki * x 1,
    p.vgq (x 0) id,
    (p.I0 + 3 * (p.vgd (x 0) id * id + p.vgq (x 0) id * p.iq0) /
      (2 * regDen p.VdcRef (x 2))) / p.Cdc,
    p.VdcRef - x 2]

@[powerlib_foundation] theorem contDiff_regField (hV : 0 < p.VdcRef) : ContDiff ℝ 1 p.regField := by
  have hden : ContDiff ℝ 1 (fun y : State 4 => 2 * regDen p.VdcRef (y 2)) :=
    contDiff_const.mul ((contDiff_regDen _).comp (Criteria.contDiff_coord 2))
  have hden0 : ∀ y : State 4, 2 * regDen p.VdcRef (y 2) ≠ 0 := fun y => by
    have := half_le_regDen hV (y 2)
    have : 0 < regDen p.VdcRef (y 2) := lt_of_lt_of_le (by positivity) this
    positivity
  have hP : ContDiff ℝ 1 p.pccP := by
    unfold pccP vgd vgq idRef
    fun_prop
  have hq : ContDiff ℝ 1 (fun y : State 4 => p.vgq (y 0) (p.idRef (y 2) (y 3))) := by
    unfold vgq idRef
    fun_prop
  have h0 : ContDiff ℝ 1 (fun y : State 4 => p.regField y 0) := by
    show ContDiff ℝ 1 (fun y : State 4 =>
      p.ωs - p.ωg + p.kp * p.vgq (y 0) (p.idRef (y 2) (y 3)) + p.ki * y 1)
    fun_prop
  have h1 : ContDiff ℝ 1 (fun y : State 4 => p.regField y 1) := hq
  have h2 : ContDiff ℝ 1 (fun y : State 4 => p.regField y 2) := by
    show ContDiff ℝ 1 (fun y : State 4 =>
      (p.I0 + 3 * p.pccP y / (2 * regDen p.VdcRef (y 2))) / p.Cdc)
    exact (contDiff_const.add ((contDiff_const.mul hP).div hden hden0)).div_const _
  have h3 : ContDiff ℝ 1 (fun y : State 4 => p.regField y 3) := by
    show ContDiff ℝ 1 (fun y : State 4 => p.VdcRef - y 2)
    fun_prop
  apply Criteria.contDiff_of_components
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3]

/-- On the half-space `V_dc > 3 V_dc*/4` the regularized field is model B. -/
@[powerlib_foundation] theorem field_eq_regField {y : State 4} (hV : 0 < p.VdcRef)
    (hy : 3 * p.VdcRef / 4 ≤ y 2) : p.field y = p.regField y := by
  unfold field regField
  rw [regDen_eq hV hy]

/-- Every point of the ball of radius `V_dc*/4` around a state with `V_dc = V_dc*` lies in the
half-space where the two fields agree. -/
@[powerlib_foundation] theorem field_eq_regField_of_mem_ball (hV : 0 < p.VdcRef) {x y : State 4}
    (hx : x 2 = p.VdcRef) (hy : y ∈ Metric.ball x (p.VdcRef / 4)) :
    p.field y = p.regField y := by
  apply p.field_eq_regField hV
  have h1 : dist (y 2) (x 2) ≤ dist y x := PiLp.dist_apply_le (p := 2) y x 2
  rw [Real.dist_eq] at h1
  rw [Metric.mem_ball] at hy
  have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hy)).1
  linarith

/-! ## Jacobian of model B -/

/-- The linear functional `a v₀ + b v₁ + c v₂ + d v₃` on `State 4`. -/
def row4 (a b c d : ℝ) : State 4 →L[ℝ] ℝ :=
  a • Criteria.coord 0 + b • Criteria.coord 1 + c • Criteria.coord 2 + d • Criteria.coord 3

omit p in
@[simp, powerlib_foundation] theorem row4_apply (a b c d : ℝ) (v : State 4) :
    row4 a b c d v = a * v 0 + b * v 1 + c * v 2 + d * v 3 := by
  simp [row4]

/-- Jacobian of model B at a state `x` (valid where `V_dc = x 2 ≠ 0`). -/
def jacobian (x : State 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  let c := Real.cos (x 0)
  let s := Real.sin (x 0)
  let id := p.idRef (x 2) (x 3)
  let vd := p.vgd (x 0) id
  let V := x 2
  !![p.kp * (-p.Vg * c), p.ki, p.kp * (p.Xg * p.kpv), p.kp * (-(p.Xg * p.kiv));
    -p.Vg * c, 0, p.Xg * p.kpv, -(p.Xg * p.kiv);
    3 * (-p.Vg * s * id - p.Vg * c * p.iq0) / (2 * V * p.Cdc), 0,
      3 * (p.kpv * (p.Rg * id - vd + p.Xg * p.iq0) * V - p.pccP x) / (2 * V ^ 2 * p.Cdc),
      3 * p.kiv * (vd - p.Rg * id - p.Xg * p.iq0) / (2 * V * p.Cdc);
    0, 0, -1, 0]

@[powerlib_foundation] theorem hasFDerivAt_idRef (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.idRef (y 2) (y 3)) (row4 0 0 (-p.kpv) p.kiv) x := by
  have h := (((Criteria.hasFDerivAt_coord 2 x).const_sub p.VdcRef).const_mul p.kpv).add
    ((Criteria.hasFDerivAt_coord 3 x).const_mul p.kiv)
  refine h.congr_fderiv ?_
  ext v
  simp [row4]

@[powerlib_foundation] theorem hasFDerivAt_vgq (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.vgq (y 0) (p.idRef (y 2) (y 3)))
      (row4 (-p.Vg * Real.cos (x 0)) 0 (p.Xg * p.kpv) (-(p.Xg * p.kiv))) x := by
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x (Criteria.hasFDerivAt_coord 0 x)
  have h := (hs.const_mul (-p.Vg)).sub (((p.hasFDerivAt_idRef x).const_mul p.Xg).add_const
    (p.Rg * p.iq0))
  refine h.congr_fderiv ?_
  ext v
  simp [row4]
  ring

@[powerlib_foundation] theorem hasFDerivAt_vgd (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.vgd (y 0) (p.idRef (y 2) (y 3)))
      (row4 (-p.Vg * Real.sin (x 0)) 0 (p.Rg * p.kpv) (-(p.Rg * p.kiv))) x := by
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x (Criteria.hasFDerivAt_coord 0 x)
  have h := (hc.const_mul p.Vg).sub (((p.hasFDerivAt_idRef x).const_mul p.Rg).sub_const
    (p.Xg * p.iq0))
  refine h.congr_fderiv ?_
  ext v
  simp [row4]
  ring

@[powerlib_foundation] theorem hasFDerivAt_pccP (x : State 4) :
    HasFDerivAt p.pccP
      (row4 (-p.Vg * Real.sin (x 0) * p.idRef (x 2) (x 3) - p.Vg * Real.cos (x 0) * p.iq0) 0
        (p.kpv * (p.Rg * p.idRef (x 2) (x 3) - p.vgd (x 0) (p.idRef (x 2) (x 3)) +
          p.Xg * p.iq0))
        (p.kiv * (p.vgd (x 0) (p.idRef (x 2) (x 3)) - p.Rg * p.idRef (x 2) (x 3) -
          p.Xg * p.iq0))) x := by
  have h := ((p.hasFDerivAt_vgd x).mul (p.hasFDerivAt_idRef x)).add
    ((p.hasFDerivAt_vgq x).mul_const p.iq0)
  refine h.congr_fderiv ?_
  ext v
  simp [row4]
  ring

@[powerlib_foundation] theorem hasFDerivAt_field_zero (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.field y 0)
      (row4 (p.kp * (-p.Vg * Real.cos (x 0))) p.ki (p.kp * (p.Xg * p.kpv))
        (p.kp * (-(p.Xg * p.kiv)))) x := by
  have h := (((p.hasFDerivAt_vgq x).const_mul p.kp).const_add (p.ωs - p.ωg)).add
    ((Criteria.hasFDerivAt_coord 1 x).const_mul p.ki)
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · ext v
    simp [row4]
    ring
  · simp [field]

@[powerlib_foundation] theorem hasFDerivAt_field_one (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.field y 1)
      (row4 (-p.Vg * Real.cos (x 0)) 0 (p.Xg * p.kpv) (-(p.Xg * p.kiv))) x := by
  refine (p.hasFDerivAt_vgq x).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [field]

@[powerlib_foundation] theorem hasFDerivAt_field_two {x : State 4} (hx : x 2 ≠ 0) :
    HasFDerivAt (fun y : State 4 => p.field y 2)
      (row4 (3 * (-p.Vg * Real.sin (x 0) * p.idRef (x 2) (x 3) - p.Vg * Real.cos (x 0) * p.iq0) /
          (2 * x 2 * p.Cdc)) 0
        (3 * (p.kpv * (p.Rg * p.idRef (x 2) (x 3) - p.vgd (x 0) (p.idRef (x 2) (x 3)) +
          p.Xg * p.iq0) * x 2 - p.pccP x) / (2 * x 2 ^ 2 * p.Cdc))
        (3 * p.kiv * (p.vgd (x 0) (p.idRef (x 2) (x 3)) - p.Rg * p.idRef (x 2) (x 3) -
          p.Xg * p.iq0) / (2 * x 2 * p.Cdc))) x := by
  have h2 : 2 * x 2 ≠ 0 := mul_ne_zero two_ne_zero hx
  have hd := ((Criteria.hasFDerivAt_coord 2 x).const_mul (2 : ℝ))
  have hinv := (hasDerivAt_inv h2).comp_hasFDerivAt x hd
  have h := ((((p.hasFDerivAt_pccP x).const_mul 3).mul hinv).const_add p.I0).mul_const
    p.Cdc⁻¹
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · by_cases hC : p.Cdc = 0
    · ext v
      simp [row4, hC]
    · ext v
      simp [row4]
      field_simp
      ring
  · simp [field, pccP, div_eq_mul_inv]

@[powerlib_foundation] theorem hasFDerivAt_field_three (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.field y 3) (row4 0 0 (-1) 0) x := by
  have h := (Criteria.hasFDerivAt_coord 2 x).const_sub p.VdcRef
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · ext v
    simp [row4]
  · simp [field]

/-- The Jacobian of model B, computed from the field: `D field (x) = jacobian x` wherever
`V_dc ≠ 0`. -/
@[powerlib_foundation] theorem hasFDerivAt_field {x : State 4} (hx : x 2 ≠ 0) :
    HasFDerivAt p.field (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (p.jacobian x)) x := by
  refine Criteria.hasFDerivAt_toEuclideanCLM_of_components (p.jacobian x)
    (fun i => row4 (p.jacobian x i 0) (p.jacobian x i 1) (p.jacobian x i 2) (p.jacobian x i 3))
    ?_ ?_
  · intro i
    fin_cases i
    · simpa [jacobian] using p.hasFDerivAt_field_zero x
    · simpa [jacobian] using p.hasFDerivAt_field_one x
    · simpa [jacobian] using p.hasFDerivAt_field_two hx
    · simpa [jacobian] using p.hasFDerivAt_field_three x
  · intro i v
    simp [Fin.sum_univ_four]

@[powerlib_foundation] theorem fderiv_field {x : State 4} (hx : x 2 ≠ 0) :
    fderiv ℝ p.field x = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (p.jacobian x) :=
  (p.hasFDerivAt_field hx).fderiv

/-! ## Local stability of model B equilibria -/

/-- Every equilibrium has `V_dc = V_dc*`. -/
@[powerlib_foundation] theorem equilibrium_Vdc {x : State 4} (hx : p.field x = 0) :
    x 2 = p.VdcRef := by
  obtain ⟨-, -, -, h3⟩ := (p.field_eq_zero_iff x).mp hx
  linarith

/-- Near an equilibrium the regularized field has the same equilibrium and Jacobian. -/
@[powerlib_foundation] theorem regField_equilibrium_jacobian (hV : 0 < p.VdcRef) {x : State 4}
    (hx : p.field x = 0) :
    p.regField x = 0 ∧
      fderiv ℝ p.regField x = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (p.jacobian x) := by
  have hx2 := p.equilibrium_Vdc hx
  have hR : 0 < p.VdcRef / 4 := by positivity
  have hball : ∀ y ∈ Metric.ball x (p.VdcRef / 4), p.field y = p.regField y :=
    fun y hy => p.field_eq_regField_of_mem_ball hV hx2 hy
  refine ⟨by rw [← hball x (Metric.mem_ball_self hR)]; exact hx, ?_⟩
  have hev : p.regField =ᶠ[𝓝 x] p.field :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x hR) fun y hy => (hball y hy).symm
  exact ((p.hasFDerivAt_field (by rw [hx2]; exact hV.ne')).congr_of_eventuallyEq hev).fderiv

/-- **Model B, local exponential stability.** At an equilibrium of model B (`V_dc* > 0`), if the
Jacobian `J = jacobian x` satisfies the 4×4 Routh conditions (`tr J < 0`, `m₃(J) < 0`,
`det J > 0`, `m₃² + tr² det < tr m₂ m₃`, i.e. `a3, a1, a0 > 0` and `a1² + a3² a0 < a3 a2 a1` for
`det(sI − J) = s⁴ + a3 s³ + a2 s² + a1 s + a0`), the equilibrium is locally exponentially
stable. Implementation evidence for `ModelB.mem_den_locallyExponentiallyStable`. -/
private theorem modelB_locallyExponentiallyStable (hV : 0 < p.VdcRef) {x : State 4}
    (hx : p.field x = 0) (htr : (p.jacobian x).trace < 0)
    (hm3 : Criteria.principalMinorSum3Fin4 (p.jacobian x) < 0)
    (hdet : 0 < (p.jacobian x).det)
    (hg : Criteria.principalMinorSum3Fin4 (p.jacobian x) ^ 2 +
        (p.jacobian x).trace ^ 2 * (p.jacobian x).det <
      (p.jacobian x).trace * Criteria.principalMinorSum2Fin4 (p.jacobian x) *
        Criteria.principalMinorSum3Fin4 (p.jacobian x)) :
    LocallyExponentiallyStable p.field x := by
  obtain ⟨hreg0, hJ⟩ := p.regField_equilibrium_jacobian hV hx
  have hreg := Criteria.locallyExponentiallyStable_of_jacobian_fin_four (p.jacobian x)
    (p.contDiff_regField hV) hreg0 hJ htr hm3 hdet hg
  exact locallyExponentiallyStable_of_eqOn_ball (by positivity)
    (fun y hy => p.field_eq_regField_of_mem_ball hV (p.equilibrium_Vdc hx) hy) hreg

/-- **Model B, instability.** At an equilibrium of model B (`V_dc* > 0`) with `det J < 0` the
Jacobian has a positive real eigenvalue and the equilibrium is unstable. Implementation evidence
for `ModelB.mem_den_unstable_of_det_neg`. -/
private theorem modelB_unstable_of_det_neg (hV : 0 < p.VdcRef) {x : State 4}
    (hx : p.field x = 0) (hdet : (p.jacobian x).det < 0) :
    Unstable p.field x := by
  obtain ⟨hreg0, hJ⟩ := p.regField_equilibrium_jacobian hV hx
  have hreg := Criteria.unstable_of_jacobian_det_neg_fin_four (p.jacobian x)
    (p.contDiff_regField hV) hreg0 hJ hdet
  exact unstable_of_eqOn_ball (by positivity)
    (fun y hy => p.field_eq_regField_of_mem_ball hV (p.equilibrium_Vdc hx) hy) hreg

/-- Concrete non-vacuous instance: the no-load operating point. With `I₀ = 0`, `R_g = 0`,
`i_q0 = 0`, `V_dc* > 0`, `V_g > 0` and positive gains `k_p, k_i, k_pv, k_iv` and `C_dc > 0`
(any `X_g`, `ω_s`, `ω_g`), the equilibrium `(0, (ω_g − ω_s)/k_i, V_dc*, 0)` of model B is locally
exponentially stable. Its Jacobian is block upper-triangular with characteristic polynomial
`(s² + a s + b)(s² + c s + d)`, `a = k_p V_g`, `b = k_i V_g`, `c = 3 k_pv V_g/(2 V_dc* C_dc)`,
`d = 3 k_iv V_g/(2 V_dc* C_dc)`; the Routh determinant is
`a3 a2 a1 − a1² − a3² a0 = a c ((b − d)² + (a + c)(a d + b c)) > 0`. Implementation evidence
for `ModelB.noLoad_mem_den_locallyExponentiallyStable`. -/
private theorem modelB_noLoad_locallyExponentiallyStable (hV : 0 < p.VdcRef)
    (hVg : 0 < p.Vg) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkpv : 0 < p.kpv) (hkiv : 0 < p.kiv)
    (hC : 0 < p.Cdc) (hI : p.I0 = 0) (hR : p.Rg = 0) (hq : p.iq0 = 0) :
    LocallyExponentiallyStable p.field
      (WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]) := by
  have hx : p.field (WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]) = 0 := by
    rw [field_eq_zero_iff]
    simp [idRef, vgq, vgd, hI, hR, hq]
    field_simp
    ring
  set a := p.kp * p.Vg with ha
  set b := p.ki * p.Vg with hb
  set c := 3 * p.kpv * p.Vg / (2 * p.VdcRef * p.Cdc) with hc
  set d := 3 * p.kiv * p.Vg / (2 * p.VdcRef * p.Cdc) with hd
  have ha0 : 0 < a := mul_pos hkp hVg
  have hb0 : 0 < b := mul_pos hki hVg
  have hc0 : 0 < c := by positivity
  have hd0 : 0 < d := by positivity
  set J := p.jacobian (WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]) with hJ
  have e00 : J 0 0 = -a := by simp [J, jacobian, a]
  have e01 : J 0 1 = p.ki := by simp [J, jacobian]
  have e10 : J 1 0 = -p.Vg := by simp [J, jacobian]
  have e11 : J 1 1 = 0 := by simp [J, jacobian]
  have e20 : J 2 0 = 0 := by simp [J, jacobian, idRef, hq]
  have e21 : J 2 1 = 0 := by simp [J, jacobian]
  have e22 : J 2 2 = -c := by
    simp [J, jacobian, idRef, vgd, pccP, vgq, hR, hq, c]
    field_simp
  have e23 : J 2 3 = d := by
    simp [J, jacobian, idRef, vgd, hR, hq, d]
  have e30 : J 3 0 = 0 := by simp [J, jacobian]
  have e31 : J 3 1 = 0 := by simp [J, jacobian]
  have e32 : J 3 2 = -1 := by simp [J, jacobian]
  have e33 : J 3 3 = 0 := by simp [J, jacobian]
  have htr : J.trace = -(a + c) := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four, e00, e11, e22, e33]
    ring
  have hm2 : Criteria.principalMinorSum2Fin4 J = b + d + a * c := by
    simp only [Criteria.principalMinorSum2Fin4, e00, e01, e10, e11, e20, e21, e22, e23, e30, e31,
      e32, e33]
    rw [hb]
    ring
  have hm3 : Criteria.principalMinorSum3Fin4 J = -(a * d + b * c) := by
    simp only [Criteria.principalMinorSum3Fin4, e00, e01, e10, e11, e20, e21, e22, e23, e30, e31,
      e32, e33]
    rw [hb]
    ring
  have hdet : J.det = b * d := by
    rw [Criteria.det_fin_four]
    simp only [e00, e01, e10, e11, e20, e21, e22, e23, e30, e31, e32, e33]
    rw [hb]
    ring
  have hD : 0 < a * c * ((b - d) ^ 2 + (a + c) * (a * d + b * c)) := by positivity
  refine p.modelB_locallyExponentiallyStable hV hx ?_ ?_ ?_ ?_
  · rw [← hJ, htr]; linarith
  · rw [← hJ, hm3]; nlinarith [mul_pos ha0 hd0, mul_pos hb0 hc0]
  · rw [← hJ, hdet]; positivity
  · rw [← hJ, htr, hm2, hm3, hdet]
    nlinarith [hD]

/-! ## Model B away from the singular plane `V_dc = 0` -/

/-- The states with nonzero DC-link voltage, where the field is smooth. -/
def nonzeroVdc : Set (State 4) := {x | x 2 ≠ 0}

@[powerlib_foundation] theorem isOpen_nonzeroVdc : IsOpen nonzeroVdc :=
  isOpen_ne_fun (Criteria.contDiff_coord (n := 4) (k := 0) 2).continuous continuous_const

/-- Model B is `C¹` on `V_dc ≠ 0` (both signs of the DC-link voltage). -/
@[powerlib_foundation] theorem field_contDiffOn : ContDiffOn ℝ 1 p.field nonzeroVdc := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  · simp only [field, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
    apply ContDiff.contDiffOn
    unfold vgq idRef
    fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply ContDiff.contDiffOn
    unfold vgq idRef
    fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.reduceFinMk, Matrix.cons_val]
    apply ContDiffOn.div_const
    apply contDiffOn_const.add
    apply ContDiffOn.div _ (contDiff_const.mul (Criteria.contDiff_coord 2)).contDiffOn
    · intro x hx
      exact mul_ne_zero two_ne_zero hx
    · apply ContDiff.contDiffOn
      unfold vgq vgd idRef
      fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.reduceFinMk, Matrix.cons_val]
    apply ContDiff.contDiffOn
    fun_prop

/-- At `V_dc = 0` the field is read with Lean's `x / 0 = 0`: the power term `3 P / (2 V_dc)`
vanishes, so the DC-link and DC-loop components are `I₀ / C_dc` and `V_dc*`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_iff_of_Vdc_eq_zero {x : State 4} (hx : x 2 = 0) :
    p.field x = 0 ↔
      p.ωs - p.ωg + p.kp * p.vgq (x 0) (p.kiv * x 3) + p.ki * x 1 = 0 ∧
        p.vgq (x 0) (p.kiv * x 3) = 0 ∧ p.I0 / p.Cdc = 0 ∧ p.VdcRef = 0 := by
  rw [field_eq_zero_iff, hx]
  simp only [mul_zero, div_zero, add_zero, sub_zero]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    have hid : p.idRef 0 (x 3) = p.kiv * x 3 := by simp [idRef, h3]
    rw [hid] at h0 h1
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    have hid : p.idRef 0 (x 3) = p.kiv * x 3 := by simp [idRef, h3]
    rw [hid]
    exact ⟨h0, h1, h2, h3⟩

/-! ## Model B near the singular plane `V_dc = 0` -/

/-- Off the singular plane, `2 V_dc` times the DC-link component of the field is the smooth
function `(2 I₀ V_dc + 3 P) / C_dc`. Static evidence on the model. -/
@[powerlib_foundation] theorem two_mul_field_two {y : State 4} (hy : y 2 ≠ 0) :
    2 * y 2 * p.field y 2 = (2 * p.I0 * y 2 + 3 * p.pccP y) / p.Cdc := by
  have h : p.field y 2 = (p.I0 + 3 * p.pccP y / (2 * y 2)) / p.Cdc := by
    simp [field, pccP]
  rw [h, show 2 * y 2 * ((p.I0 + 3 * p.pccP y / (2 * y 2)) / p.Cdc) =
    (2 * y 2 * (p.I0 + 3 * p.pccP y / (2 * y 2))) / p.Cdc by ring]
  congr 1
  field_simp

/-- On the singular plane the DC-link component of the field is `I₀ / C_dc` (`x / 0 = 0`). -/
@[powerlib_foundation] theorem field_two_of_Vdc_eq_zero {y : State 4} (hy : y 2 = 0) :
    p.field y 2 = p.I0 / p.Cdc := by
  simp [field, hy]

@[powerlib_foundation] theorem contDiff_pccP : ContDiff ℝ 1 p.pccP := by
  unfold pccP vgd vgq idRef
  fun_prop

/-- The components of model B other than the DC-link voltage are smooth on the whole space. -/
@[powerlib_foundation] theorem contDiff_field_offDC :
    ContDiff ℝ 1 (fun y : State 4 => (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] :
      State 4)) := by
  apply Criteria.contDiff_of_components
  intro i
  fin_cases i
  · show ContDiff ℝ 1 (fun y : State 4 =>
      p.ωs - p.ωg + p.kp * p.vgq (y 0) (p.idRef (y 2) (y 3)) + p.ki * y 1)
    unfold vgq idRef
    fun_prop
  · show ContDiff ℝ 1 (fun y : State 4 => p.vgq (y 0) (p.idRef (y 2) (y 3)))
    unfold vgq idRef
    fun_prop
  · exact contDiff_const
  · show ContDiff ℝ 1 (fun y : State 4 => p.VdcRef - y 2)
    fun_prop

/-- With `C_dc = 0` the DC-link component vanishes (`x / 0 = 0`) and model B is smooth on the
whole space. -/
@[powerlib_foundation] theorem contDiff_field_of_Cdc_eq_zero (hC : p.Cdc = 0) :
    ContDiff ℝ 1 p.field := by
  have h : p.field = fun y : State 4 =>
      (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] : State 4) := by
    funext y
    ext i
    fin_cases i <;> simp [field, hC]
  rw [h]
  exact p.contDiff_field_offDC

/-- **Model B on the singular plane: collapse.** At a state `x` with `V_dc = 0` where the power
term pushes the DC-link voltage towards the plane from both sides (`P(x) / C_dc < 0`) and the
current injection crosses it (`I₀ / C_dc ≠ 0`), the segment-based local exponential estimate holds,
although `x` is not an equilibrium (`field x 2 = I₀ / C_dc ≠ 0`): near `x`,
`d(V_dc²)/dt = (2 I₀ V_dc + 3 P) / C_dc ≤ −a`, so every solution segment reaches the plane only at
its end, after a time at most `V_dc(t₀)² / a`. Implementation evidence for
`ModelB.mem_den_locallyExponentiallyStable_of_collapse`. -/
private theorem modelB_locallyExponentiallyStable_of_collapse {x : State 4} (hx : x 2 = 0)
    (hP : p.pccP x / p.Cdc < 0) (hI : p.I0 / p.Cdc ≠ 0) :
    LocallyExponentiallyStable p.field x := by
  set g : State 4 → ℝ := fun y => (2 * p.I0 * y 2 + 3 * p.pccP y) / p.Cdc with hg
  have hgc : Continuous g :=
    ((continuous_const.mul (Criteria.contDiff_coord (n := 4) (k := 1) 2).continuous).add
      (continuous_const.mul p.contDiff_pccP.continuous)).div_const _
  have hgx : g x = 3 * (p.pccP x / p.Cdc) := by
    simp only [hg, hx, mul_zero, zero_add]
    ring
  set a := -(g x) / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuous_iff.mp hgc x a ha0
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    p.contDiff_field_offDC.continuous.continuousOn
  refine Dynamics.locallyExponentiallyStable_of_collapse 2 hx (ρ := min ρ₁ 1) (a := a) (M := M)
    (lt_min hρ₁ one_pos) ha0 ?_ ?_ ?_
  · intro y hy hy2
    rw [p.two_mul_field_two hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_left _ _))
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    show g y ≤ -a
    linarith
  · intro y _ hy2
    rwa [p.field_two_of_Vdc_eq_zero hy2]
  · intro y hy
    have hFy : p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ) =
        (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] : State 4) := by
      ext i
      fin_cases i <;> simp
    rw [hFy]
    exact hM y (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (lt_of_lt_of_le hy (min_le_right _ _)).le)

/-- **Model B on the singular plane: repulsion.** At a state `x` with `V_dc = 0` where the power
term pushes the DC-link voltage away from the plane on both sides (`P(x) / C_dc > 0`), the state
is unstable: near `x`, `d(V_dc²)/dt = (2 I₀ V_dc + 3 P) / C_dc` is bounded below by a positive
rate, and on each half ball `{V_dc ≥ s}` model B is the smooth field with denominator
`regDen s V_dc`. Implementation evidence for `ModelB.mem_den_unstable_of_repel`. -/
private theorem modelB_unstable_of_repel {x : State 4} (hx : x 2 = 0)
    (hP : 0 < p.pccP x / p.Cdc) : Unstable p.field x := by
  set g : State 4 → ℝ := fun y => (2 * p.I0 * y 2 + 3 * p.pccP y) / p.Cdc with hg
  have hgc : Continuous g :=
    ((continuous_const.mul (Criteria.contDiff_coord (n := 4) (k := 1) 2).continuous).add
      (continuous_const.mul p.contDiff_pccP.continuous)).div_const _
  have hgx : g x = 3 * (p.pccP x / p.Cdc) := by
    simp only [hg, hx, mul_zero, zero_add]
    ring
  set a := g x / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.mp hgc x a ha0
  refine Dynamics.unstable_of_repel 2 hx hρ ha0 (fun y hy hy2 => ?_) (fun s hs => ?_)
  · rw [p.two_mul_field_two hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact hy)
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).1
    show a ≤ g y
    linarith
  · refine ⟨fun y => (WithLp.toLp 2 ![p.field y 0, p.field y 1,
      (p.I0 + 3 * p.pccP y / (2 * regDen s (y 2))) / p.Cdc, p.field y 3] : State 4), ?_, ?_⟩
    · have hden : ContDiff ℝ 1 (fun y : State 4 => 2 * regDen s (y 2)) :=
        contDiff_const.mul ((contDiff_regDen _).comp (Criteria.contDiff_coord 2))
      have hden0 : ∀ y : State 4, 2 * regDen s (y 2) ≠ 0 := fun y => by
        have := half_le_regDen hs (y 2)
        have : 0 < regDen s (y 2) := lt_of_lt_of_le (by positivity) this
        positivity
      have hoff := p.contDiff_field_offDC
      apply Criteria.contDiff_of_components
      intro i
      fin_cases i
      · show ContDiff ℝ 1 (fun y : State 4 => p.field y 0)
        have h := (Criteria.contDiff_coord (n := 4) (k := 1) 0).comp hoff
        exact h
      · show ContDiff ℝ 1 (fun y : State 4 => p.field y 1)
        have h := (Criteria.contDiff_coord (n := 4) (k := 1) 1).comp hoff
        exact h
      · show ContDiff ℝ 1 (fun y : State 4 =>
          (p.I0 + 3 * p.pccP y / (2 * regDen s (y 2))) / p.Cdc)
        exact (contDiff_const.add ((contDiff_const.mul p.contDiff_pccP).div hden hden0)).div_const _
      · show ContDiff ℝ 1 (fun y : State 4 => p.field y 3)
        have h := (Criteria.contDiff_coord (n := 4) (k := 1) 3).comp hoff
        exact h
    · intro y _ hy2
      have hr : regDen s (y 2) = y 2 := regDen_eq hs (by linarith)
      ext i
      fin_cases i
      · rfl
      · rfl
      · show (p.I0 + 3 * p.pccP y / (2 * regDen s (y 2))) / p.Cdc = p.field y 2
        rw [hr]
        simp [field, pccP]
      · rfl

end ModelBParams


/-! ## The model-B family -/

namespace ModelB

/-- A model-B system read about a selected state `x*`. -/
structure Model where
  /-- The model-B parameters. -/
  p : ModelBParams
  /-- The selected state `x* = (Δθ*, x_pll*, V_dc*, ξ_v*)`. -/
  x : State 4

/-- Model B translated so that the selected state is the origin. -/
def Model.field (m : Model) (z : State 4) : State 4 := m.p.field (z + m.x)

/-- The 4×4 Routh conditions on a matrix `J`: `tr J < 0`, `m₃(J) < 0`, `det J > 0` and
`m₃² + tr² det < tr m₂ m₃`. -/
def RouthFin4 (J : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  J.trace < 0 ∧ Criteria.principalMinorSum3Fin4 J < 0 ∧ 0 < J.det ∧
    Criteria.principalMinorSum3Fin4 J ^ 2 + J.trace ^ 2 * J.det <
      J.trace * Criteria.principalMinorSum2Fin4 J * Criteria.principalMinorSum3Fin4 J

/-- A strict violation of the 4×4 Routh conditions on a matrix `J`: `tr J > 0`, `m₂(J) < 0`,
`m₃(J) > 0`, `det J < 0` or `tr m₂ m₃ < m₃² + tr² det`; each places a characteristic root in the
open right half plane (`Criteria.exists_eigenvalue_re_pos_of_violation_fin_four`). -/
def RouthViolationFin4 (J : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  0 < J.trace ∨ Criteria.principalMinorSum2Fin4 J < 0 ∨ 0 < Criteria.principalMinorSum3Fin4 J ∨
    J.det < 0 ∨ J.trace * Criteria.principalMinorSum2Fin4 J * Criteria.principalMinorSum3Fin4 J <
      Criteria.principalMinorSum3Fin4 J ^ 2 + J.trace ^ 2 * J.det

/-- Requirements on model B, all static. -/
inductive Requirement
  /-- The selected state is a zero of the field. -/
  | equilibrium
  /-- Positive DC-voltage reference. -/
  | positiveReference
  /-- The 4×4 Routh conditions on the Jacobian at the selected state. -/
  | routh
  /-- Negative Jacobian determinant at the selected state. -/
  | detNeg
  /-- The Jacobian at the selected state is off the 4×4 Routh boundary: it meets the Routh
  conditions or violates them strictly. -/
  | offBoundary

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => m.p.field m.x = 0
  | .positiveReference => 0 < m.p.VdcRef
  | .routh => RouthFin4 (m.p.jacobian m.x)
  | .detNeg => (m.p.jacobian m.x).det < 0
  | .offBoundary => RouthFin4 (m.p.jacobian m.x) ∨ RouthViolationFin4 (m.p.jacobian m.x)

/-- The translation of the sentences: the local sentences into an equilibrium with positive
reference satisfying the Routh conditions, instability into one with a negative Jacobian
determinant, passivity into nothing. The global sentences, decay rates, sampled contraction and
conservation are not decided by the linearization and are translated into the whole language,
which no model meets (unavailable translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.equilibrium, .positiveReference, .routh}
  | .flow .unstable => {.equilibrium, .positiveReference, .detNeg}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The model-B family: every model read as its field translated to the selected state. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-- A flow sentence of a model is the sentence of the untranslated field at the selected state. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.x :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- No model meets the Routh conditions and a negative determinant: the whole requirement
language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : RouthFin4 (m.p.jacobian m.x) := h .routh
  have h2 : (m.p.jacobian m.x).det < 0 := h .detNeg
  linarith [h1.2.2.1]

private theorem les_of_meets {m : Model} (he : Meets m .equilibrium)
    (hV : Meets m .positiveReference) (hr : Meets m .routh) :
    m ∈ family.den (.flow .locallyExponentiallyStable) :=
  mem_den_flow_iff.mpr (m.p.modelB_locallyExponentiallyStable hV he hr.1 hr.2.1 hr.2.2.1 hr.2.2.2)

/-- Every translation of the model-B family is sound: the Routh conditions at an equilibrium
prove the local sentences, a negative Jacobian determinant proves instability (LeanForControl's
linearization theorems, applied to the regularized field and transferred through the ball on
which it agrees with model B), and passivity holds without requirement. -/
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
  · have hles : Meets m .equilibrium → Meets m .positiveReference → Meets m .routh →
        LocallyExponentiallyStable m.field 0 := fun he hV hr =>
      family_isAutonomous.mem_den_flow.mp (les_of_meets he hV hr)
    rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable =>
      exact (hles (hm .equilibrium (by simp [translate])) (hm .positiveReference
        (by simp [translate])) (hm .routh (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (hles (hm .equilibrium (by simp [translate])) (hm .positiveReference
          (by simp [translate])) (hm .routh (by simp [translate])))
    case locallyExponentiallyStable =>
      exact hles (hm .equilibrium (by simp [translate])) (hm .positiveReference
        (by simp [translate])) (hm .routh (by simp [translate]))
    case unstable =>
      refine family_isAutonomous.mem_den_flow.mp (mem_den_flow_iff.mpr ?_)
      exact m.p.modelB_unstable_of_det_neg (hm .positiveReference (by simp [translate]))
        (hm .equilibrium (by simp [translate])) (hm .detNeg (by simp [translate]))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- **Model B, local exponential stability.** At an equilibrium of model B (`V_dc* > 0`), if the
Jacobian `J = jacobian x*` satisfies the 4×4 Routh conditions (`tr J < 0`, `m₃(J) < 0`,
`det J > 0`, `m₃² + tr² det < tr m₂ m₃`, i.e. `a3, a1, a0 > 0` and `a1² + a3² a0 < a3 a2 a1` for
`det(sI − J) = s⁴ + a3 s³ + a2 s² + a1 s + a0`), the equilibrium is locally exponentially
stable. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hV : 0 < m.p.VdcRef) (hx : m.p.field m.x = 0) (htr : (m.p.jacobian m.x).trace < 0)
    (hm3 : Criteria.principalMinorSum3Fin4 (m.p.jacobian m.x) < 0)
    (hdet : 0 < (m.p.jacobian m.x).det)
    (hg : Criteria.principalMinorSum3Fin4 (m.p.jacobian m.x) ^ 2 +
        (m.p.jacobian m.x).trace ^ 2 * (m.p.jacobian m.x).det <
      (m.p.jacobian m.x).trace * Criteria.principalMinorSum2Fin4 (m.p.jacobian m.x) *
        Criteria.principalMinorSum3Fin4 (m.p.jacobian m.x)) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact les_of_meets hx hV ⟨htr, hm3, hdet, hg⟩

/-- **Model B, instability.** At an equilibrium of model B (`V_dc* > 0`) with `det J < 0` the
Jacobian has a positive real eigenvalue and the equilibrium is unstable. -/
@[powerlib_domain] theorem mem_den_unstable_of_det_neg (m : Model) (hV : 0 < m.p.VdcRef)
    (hx : m.p.field m.x = 0) (hdet : (m.p.jacobian m.x).det < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (m.p.modelB_unstable_of_det_neg hV hx hdet)

/-- Concrete non-vacuous instance: the no-load operating point. With `I₀ = 0`, `R_g = 0`,
`i_q0 = 0`, `V_dc* > 0`, `V_g > 0` and positive gains `k_p, k_i, k_pv, k_iv` and `C_dc > 0`
(any `X_g`, `ω_s`, `ω_g`), the equilibrium `(0, (ω_g − ω_s)/k_i, V_dc*, 0)` of model B is locally
exponentially stable. -/
@[powerlib_domain] theorem noLoad_mem_den_locallyExponentiallyStable (p : ModelBParams)
    (hV : 0 < p.VdcRef) (hVg : 0 < p.Vg) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkpv : 0 < p.kpv)
    (hkiv : 0 < p.kiv) (hC : 0 < p.Cdc) (hI : p.I0 = 0) (hR : p.Rg = 0) (hq : p.iq0 = 0) :
    connection% (⟨p, WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]⟩ ∈
      family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr
    (p.modelB_noLoad_locallyExponentiallyStable hV hVg hkp hki hkpv hkiv hC hI hR hq)

/-! ### Exactness of the local exponential translation at equilibria -/

/-- At an equilibrium with positive DC-voltage reference, local exponential stability is
translated exactly: the equilibrium is locally exponentially stable exactly when its Jacobian
satisfies the 4×4 Routh conditions. Converse linearization of the regularized field, which is
model B on a ball around the equilibrium, and the quartic Routh–Hurwitz criterion. -/
@[powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.equilibrium, .positiveReference}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets ({.equilibrium, .positiveReference, .routh} ∪
    {.equilibrium, .positiveReference}) = _
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_inter_iff]
  constructor
  · intro h
    have he : Meets m .equilibrium := h .equilibrium (by simp)
    have hV : Meets m .positiveReference := h .positiveReference (by simp)
    refine ⟨les_of_meets he hV (h .routh (by simp)), fun q hq => ?_⟩
    rcases hq with rfl | rfl
    · exact he
    · exact hV
  · rintro ⟨hd, hI⟩ q hq
    have hx : m.p.field m.x = 0 := hI .equilibrium (by simp)
    have hV : 0 < m.p.VdcRef := hI .positiveReference (by simp)
    obtain ⟨-, hJ⟩ := m.p.regField_equilibrium_jacobian hV hx
    have hles : LocallyExponentiallyStable m.p.regField m.x :=
      locallyExponentiallyStable_of_eqOn_ball (by positivity)
        (fun y hy => (m.p.field_eq_regField_of_mem_ball hV (m.p.equilibrium_Vdc hx) hy).symm)
        (mem_den_flow_iff.mp hd)
    have hA := Dynamics.isHurwitz_of_locallyExponentiallyStable _ (m.p.contDiff_regField hV) hJ
      hles
    rcases hq with ((rfl | rfl | rfl) | (rfl | rfl))
    · exact hx
    · exact hV
    · exact (Criteria.isHurwitz_fin_four_iff _).mp hA
    · exact hx
    · exact hV

/-! ### The local exponential translation without context -/

/-- At a selected state with nonzero DC-link voltage — of either sign — local exponential
stability holds exactly when the state is an equilibrium whose Jacobian satisfies the 4×4 Routh
conditions. Model B is `C¹` on `V_dc ≠ 0` (`ModelBParams.field_contDiffOn`), so the converse
linearization theorem for fields that are `C¹` on an open neighbourhood applies
(`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`): the negative side needs no
separate regularization. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model) (hx : m.x 2 ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.p.field m.x = 0 ∧ RouthFin4 (m.p.jacobian m.x)}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq, mem_den_flow_iff]
  change LocallyExponentiallyStable _ _ ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local
    ModelBParams.isOpen_nonzeroVdc hx (m.p.jacobian m.x) m.p.field_contDiffOn
    (m.p.fderiv_field hx), Criteria.isHurwitz_fin_four_iff]
  rfl

/-- A converter with a negative DC-voltage reference: `V_dc* = −1` with negative DC-loop gains
`k_pv = k_iv = −1` (so that the loop still regulates), `V_g = C_dc = k_p = k_i = 1`, no load,
lossless line `R_g = X_g = 0`, `i_q0 = 0`, `ω_s = ω_g = 0`, at `x* = (0, 0, −1, 0)`. -/
def negativeReference : Model :=
  ⟨⟨0, 0, 1, 1, 1, 0, -1, -1, -1, 1, 0, 0, 0⟩, WithLp.toLp 2 ![0, 0, -1, 0]⟩

private theorem negativeReference_equilibrium :
    negativeReference.p.field negativeReference.x = 0 := by
  rw [ModelBParams.field_eq_zero_iff]
  simp [negativeReference, ModelBParams.idRef, ModelBParams.vgq, ModelBParams.vgd]

/-- The negative-reference converter is locally exponentially stable: its Jacobian is block
diagonal, `[[−1, 1], [−1, 0]]` (PLL) and `[[−3/2, 3/2], [−1, 0]]` (DC loop), both Hurwitz. -/
@[powerlib_domain] theorem negativeReference_mem_den_locallyExponentiallyStable :
    connection% (negativeReference ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_iff negativeReference (by simp [negativeReference])
  unfold powerlib.TMIO.Statement at h ⊢
  refine h.mpr ⟨negativeReference_equilibrium, ?_⟩
  set J := negativeReference.p.jacobian negativeReference.x with hJ
  have e00 : J 0 0 = -1 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e01 : J 0 1 = 1 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e02 : J 0 2 = 0 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e03 : J 0 3 = 0 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e10 : J 1 0 = -1 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e11 : J 1 1 = 0 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e12 : J 1 2 = 0 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e13 : J 1 3 = 0 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e20 : J 2 0 = 0 := by
    simp [J, ModelBParams.jacobian, negativeReference, ModelBParams.idRef]
  have e21 : J 2 1 = 0 := by simp [J, ModelBParams.jacobian, negativeReference]
  have e22 : J 2 2 = -3 / 2 := by
    simp [J, ModelBParams.jacobian, negativeReference, ModelBParams.idRef, ModelBParams.vgd,
      ModelBParams.vgq, ModelBParams.pccP]
  have e23 : J 2 3 = 3 / 2 := by
    simp [J, ModelBParams.jacobian, negativeReference, ModelBParams.idRef, ModelBParams.vgd]
  have e30 : J 3 0 = 0 := by simp [J, ModelBParams.jacobian]
  have e31 : J 3 1 = 0 := by simp [J, ModelBParams.jacobian]
  have e32 : J 3 2 = -1 := by simp [J, ModelBParams.jacobian]
  have e33 : J 3 3 = 0 := by simp [J, ModelBParams.jacobian]
  have htr : J.trace = -5 / 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four, e00, e11, e22, e33]
    norm_num
  have hm2 : Criteria.principalMinorSum2Fin4 J = 4 := by
    simp only [Criteria.principalMinorSum2Fin4, e00, e01, e02, e03, e10, e11, e12, e13, e20, e21,
      e22, e23, e30, e31, e32, e33]
    norm_num
  have hm3 : Criteria.principalMinorSum3Fin4 J = -3 := by
    simp only [Criteria.principalMinorSum3Fin4, e00, e01, e02, e03, e10, e11, e12, e13, e20, e21,
      e22, e23, e30, e31, e32, e33]
    norm_num
  have hdet : J.det = 3 / 2 := by
    rw [Criteria.det_fin_four]
    simp only [e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htr]; norm_num
  · rw [hm3]; norm_num
  · rw [hdet]; norm_num
  · rw [htr, hm2, hm3, hdet]; norm_num

/-- The local exponential translation is not exact without context: the negative-reference
converter is locally exponentially stable at an equilibrium whose Jacobian meets the Routh
conditions, but its DC-voltage reference is negative. Not even the context of an equilibrium
makes it exact (`not_exactUnder_equilibrium_locallyExponentiallyStable`). -/
@[powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeReference_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hV : Meets negativeReference .positiveReference :=
    hmem .positiveReference (by simp [family, translate])
  have : (0 : ℝ) < -1 := hV
  norm_num at this

/-- Within the context of an equilibrium the local exponential translation is still not exact:
the negative-reference converter is an equilibrium. -/
@[powerlib_domain] theorem not_exactUnder_equilibrium_locallyExponentiallyStable :
    connection% (¬ family.ExactUnder {.equilibrium} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  intro h
  have hmem := negativeReference_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  have hI : negativeReference ∈ TMIO.realize family.meets {.equilibrium} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact negativeReference_equilibrium
  have h' : negativeReference ∈ TMIO.realize family.meets
      (family.translate (.flow .locallyExponentiallyStable) ∪ {.equilibrium}) := by
    rw [h]
    exact ⟨hmem, hI⟩
  rw [TMIO.mem_realize] at h'
  have hV : Meets negativeReference .positiveReference :=
    h' .positiveReference (by simp [family, translate])
  have : (0 : ℝ) < -1 := hV
  norm_num at this

/-- On the singular plane `V_dc = 0` (read with `x / 0 = 0`) an equilibrium is not locally
asymptotically stable: there the DC-link and DC-loop components vanish identically, and the
equilibria of the plane form a curve through the point (along `Δθ` with
`ξ_v = −(V_g sin Δθ + R_g i_q0)/(X_g k_iv)` when `X_g k_iv ≠ 0`, along `ξ_v` otherwise). -/
@[powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero (m : Model)
    (hx : m.x 2 = 0) (heq : m.p.field m.x = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro hm
  have hlas : LocalAsymptoticStable m.p.field m.x := mem_den_flow_iff.mp hm
  obtain ⟨h0, h1, h2, h3⟩ := (m.p.field_eq_zero_iff_of_Vdc_eq_zero hx).mp heq
  have hpt : ∀ a c : ℝ, m.p.vgq a (m.p.kiv * c) = 0 →
      m.p.field (WithLp.toLp 2 ![a, m.x 1, 0, c]) = 0 := by
    intro a c hq
    rw [m.p.field_eq_zero_iff_of_Vdc_eq_zero (by simp)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨?_, hq, h2, h3⟩
    rw [hq]
    have : m.p.ωs - m.p.ωg + m.p.ki * m.x 1 = 0 := by rw [h1] at h0; linarith
    linarith
  have hnorm : ∀ a c : ℝ, ‖(WithLp.toLp 2 ![a, m.x 1, 0, c] : State 4) - m.x‖ ≤
      |a - m.x 0| + |c - m.x 3| := by
    intro a c
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
    simp only [PiLp.sub_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, hx, sub_self, Real.norm_eq_abs, sq_abs]
    norm_num
    nlinarith [abs_nonneg (a - m.x 0), abs_nonneg (c - m.x 3), sq_abs (a - m.x 0),
      sq_abs (c - m.x 3)]
  have hxeq : (WithLp.toLp 2 ![m.x 0, m.x 1, 0, m.x 3] : State 4) = m.x := by
    ext i
    fin_cases i <;> simp [hx]
  by_cases hX : m.p.Xg * m.p.kiv = 0
  · -- equilibria along `ξ_v`
    refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
      ⟨WithLp.toLp 2 ![m.x 0, m.x 1, 0, m.x 3 + ε / 2], fun h => ?_, ?_, ?_⟩) hlas
    · have := congrArg (fun y : State 4 => y 3) h
      simp at this
      linarith
    · refine (hnorm _ _).trans_lt ?_
      rw [sub_self, abs_zero, zero_add, add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith
    · refine hpt _ _ ?_
      have : m.p.vgq (m.x 0) (m.p.kiv * m.x 3) = 0 := h1
      simp only [ModelBParams.vgq] at this ⊢
      have hX' : m.p.Xg * (m.p.kiv * (m.x 3 + ε / 2)) = m.p.Xg * (m.p.kiv * m.x 3) := by
        rw [← mul_assoc, ← mul_assoc, hX, zero_mul, zero_mul]
      rw [hX']
      exact this
  · -- equilibria along `Δθ`
    set k := m.p.Xg * m.p.kiv with hk
    set ξ : ℝ → ℝ := fun a => -(m.p.Vg * Real.sin a + m.p.Rg * m.p.iq0) / k with hξ
    have hξa : ξ (m.x 0) = m.x 3 := by
      have : m.p.vgq (m.x 0) (m.p.kiv * m.x 3) = 0 := h1
      simp only [ModelBParams.vgq] at this
      simp only [hξ]
      field_simp
      linarith
    have hq : ∀ a, m.p.vgq a (m.p.kiv * ξ a) = 0 := fun a => by
      simp only [ModelBParams.vgq, hξ]
      field_simp
      ring
    have hξlip : ∀ a, |ξ a - m.x 3| ≤ |m.p.Vg / k| * |a - m.x 0| := by
      intro a
      rw [← hξa]
      simp only [hξ]
      rw [show -(m.p.Vg * Real.sin a + m.p.Rg * m.p.iq0) / k -
          -(m.p.Vg * Real.sin (m.x 0) + m.p.Rg * m.p.iq0) / k =
          -(m.p.Vg / k) * (Real.sin a - Real.sin (m.x 0)) by field_simp; ring]
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (abs_nonneg _)
    refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε => ?_) hlas
    set L := |m.p.Vg / k| with hL
    set s := ε / (2 * (1 + L)) with hs
    have hL0 : 0 ≤ L := abs_nonneg _
    have hs0 : 0 < s := by positivity
    refine ⟨WithLp.toLp 2 ![m.x 0 + s, m.x 1, 0, ξ (m.x 0 + s)], fun h => ?_, ?_, ?_⟩
    · have := congrArg (fun y : State 4 => y 0) h
      simp at this
      linarith
    · refine (hnorm _ _).trans_lt ?_
      have h1' := hξlip (m.x 0 + s)
      rw [add_sub_cancel_left] at h1' ⊢
      rw [abs_of_pos hs0] at h1' ⊢
      have : s + L * s = ε / 2 := by
        rw [hs]
        field_simp
      linarith
    · exact hpt _ _ (hq _)

/-- On the singular plane an equilibrium is not locally exponentially stable either. -/
@[powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero (m : Model)
    (hx : m.x 2 = 0) (heq : m.p.field m.x = 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have h := not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero m hx heq
  unfold powerlib.TMIO.Statement at h ⊢
  intro hm
  apply h
  rw [family_isAutonomous.mem_den_flow] at hm ⊢
  exact Flow.locallyExponentiallyStable_localAsymptoticStable hm

/-! ### Selected states on the singular plane that are not equilibria -/

/-- **Collapse onto the singular plane.** A selected state with `V_dc* = 0` at which the power term
drives the DC-link voltage into the plane from both sides (`P(x*) / C_dc < 0`) while the current
injection crosses the plane (`I₀ / C_dc ≠ 0`) is locally exponentially stable in the segment
semantics, although it is not an equilibrium (the DC-link component of the field is
`I₀ / C_dc ≠ 0` there): near `x*`, `d(V_dc²)/dt = (2 I₀ V_dc + 3 P) / C_dc` is bounded below zero,
so every solution segment reaches the plane at most at its end, after a time `O(V_dc(t₀)²)`, and
moves by `O(‖x(t₀) − x*‖²)` (`Dynamics.locallyExponentiallyStable_of_collapse`). The estimate is
met because the solutions cease to exist, not because they converge. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_collapse (m : Model)
    (hx : m.x 2 = 0) (hP : m.p.pccP m.x / m.p.Cdc < 0) (hI : m.p.I0 / m.p.Cdc ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (m.p.modelB_locallyExponentiallyStable_of_collapse hx hP hI)

/-- When the injection does not cross the singular plane (`I₀ / C_dc = 0`, in particular when
`C_dc = 0`), no selected state on the plane is locally exponentially stable. The field agrees on
the plane with the smooth field `G = (f₀, f₁, 0, f₃)`, which keeps the plane invariant: a solution of
`G` through `x*` is a solution of model B, so the estimate forces it to stay at `x*`, making `x*` an
equilibrium (`not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero`). -/
@[powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero_of_I0
    (m : Model) (hx : m.x 2 = 0) (hI : m.p.I0 / m.p.Cdc = 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have heqn := not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero m hx
  unfold powerlib.TMIO.Statement at heqn ⊢
  intro hm
  have hles : LocallyExponentiallyStable m.p.field m.x := mem_den_flow_iff.mp hm
  set G : State 4 → State 4 := fun y =>
    (WithLp.toLp 2 ![m.p.field y 0, m.p.field y 1, 0, m.p.field y 3] : State 4) with hG
  have hGc : ContDiff ℝ 1 G := m.p.contDiff_field_offDC
  have hGf : ∀ y : State 4, y 2 = 0 → G y = m.p.field y := fun y hy => by
    ext i
    fin_cases i
    · rfl
    · rfl
    · show (0 : ℝ) = m.p.field y 2
      rw [m.p.field_two_of_Vdc_eq_zero hy, hI]
    · rfl
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ := (hGc.contDiffAt (x := m.x)).exists_isIntegralCurveOn_Icc
  -- the solution of `G` stays on the plane
  have hplane : ∀ t ∈ Icc 0 T, ψ t 2 = 0 := by
    have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (ψ t 2 : ℝ)) (G (ψ t) 2 : ℝ)
        (Icc 0 T) t := fun t ht =>
      (Criteria.coord 2 : State 4 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hψ t ht)
    have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd (C := 0) (fun t _ => by simp [hG])
    intro t ht
    have := hb t ht
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero, hψ0, hx] at this
    exact this
  have hseg : IsTrajectoryOn ψ m.p.field 0 T :=
    Dynamics.isIntegralCurveOn_of_eq_on_curve hψ fun t ht => hGf _ (hplane t ht)
  obtain ⟨r, C, a, hr, -, -, hb⟩ := hles
  have hconst : ∀ t ∈ Icc 0 T, ψ t = m.x := fun t ht => by
    have := hb 0 T ψ hseg (by rw [hψ0, sub_self, norm_zero]; exact hr) t ht
    rw [hψ0, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hd1 : HasDerivWithinAt ψ (m.p.field m.x) (Icc 0 T) 0 := by
    have := hseg 0 hmem0
    rwa [hψ0] at this
  have hd2 : HasDerivWithinAt ψ 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const 0 (Icc 0 T) m.x).congr (fun t ht => hconst t ht) (hconst 0 hmem0)
  exact heqn (UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hT 0 hmem0) hd1 hd2) hm

/-- **Repulsion from the singular plane.** A selected state with `V_dc* = 0` at which the power
term pushes the DC-link voltage away from the plane (`P(x*) / C_dc > 0`) is unstable: near `x*`,
`d(V_dc²)/dt` is bounded below by a positive rate, and the solution from `V_dc = s > 0` exists
while it stays near `x*` (`Dynamics.unstable_of_repel`). -/
@[powerlib_domain] theorem mem_den_unstable_of_repel (m : Model) (hx : m.x 2 = 0)
    (hP : 0 < m.p.pccP m.x / m.p.Cdc) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (m.p.modelB_unstable_of_repel hx hP)

/-- **Local exponential stability on the singular plane.** For a selected state with `V_dc* = 0`
and nonzero power term `P(x*) / C_dc ≠ 0` (so `C_dc ≠ 0`), the segment-based local exponential
estimate holds exactly when the power term drives `V_dc` into the plane (`P(x*) / C_dc < 0`) and the
injection crosses it (`I₀ / C_dc ≠ 0`); such a state is never an equilibrium. The degenerate
power-balance case `P(x*) = 0` is not decided here. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero (m : Model)
    (hx : m.x 2 = 0) (hP : m.p.pccP m.x / m.p.Cdc ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.p.pccP m.x / m.p.Cdc < 0 ∧ m.p.I0 / m.p.Cdc ≠ 0}) := by
  have hcol := mem_den_locallyExponentiallyStable_of_collapse m hx
  have hI0 := not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero_of_I0 m hx
  unfold powerlib.TMIO.Statement at hcol hI0 ⊢
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hm
    refine ⟨?_, fun h => hI0 h hm⟩
    rcases lt_or_gt_of_ne hP with h | h
    · exact h
    · exact absurd (mem_den_flow_iff.mp hm).lyapunovStable
        (m.p.modelB_unstable_of_repel hx h)
  · rintro ⟨h1, h2⟩
    exact hcol h1 h2

/-- A converter at rest on the singular plane: `V_dc* = 0` and `ξ_v* = −1`, so that `i_d* = −1`,
`v_d = 1` and `P = −1`; positive reference `V_dc,ref = 1`; `I₀ = C_dc = V_g = k_p = k_i = k_iv = 1`,
`k_pv = R_g = X_g = i_q0 = 0`, `ω_s = ω_g = 0`; `x* = (0, 0, 0, −1)`. -/
def collapsePoint : Model :=
  ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, WithLp.toLp 2 ![0, 0, 0, -1]⟩

private theorem collapsePoint_field_ne_zero :
    collapsePoint.p.field collapsePoint.x ≠ 0 := by
  intro h
  have := congrArg (fun y : State 4 => y 3) h
  simp [collapsePoint, ModelBParams.field] at this

/-- The collapse point, which is not an equilibrium and has positive DC-voltage reference, is
locally exponentially stable in the segment semantics. -/
@[powerlib_domain] theorem collapsePoint_mem_den_locallyExponentiallyStable :
    connection% (collapsePoint ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_of_collapse collapsePoint
    (by simp [collapsePoint]) (by
      simp [collapsePoint, ModelBParams.pccP, ModelBParams.vgd, ModelBParams.vgq,
        ModelBParams.idRef])
    (by simp [collapsePoint])
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- A member of a local denotation outside the equilibria, with positive reference, refutes
exactness of the translation within the context of a positive reference. -/
private theorem not_exactUnder_positiveReference_of_mem {P : Flow.Property}
    (hP : family.translate (.flow P) = {.equilibrium, .positiveReference, .routh})
    (hmem : collapsePoint ∈ family.den (.flow P)) :
    ¬ family.ExactUnder {.positiveReference} (.flow P) := by
  unfold Family.ExactUnder TMIO.ExactUnder
  intro h
  have hI : collapsePoint ∈ TMIO.realize family.meets {.positiveReference} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    show (0 : ℝ) < collapsePoint.p.VdcRef
    simp [collapsePoint]
  have h' : collapsePoint ∈ TMIO.realize family.meets
      (family.translate (.flow P) ∪ {.positiveReference}) := by
    rw [h]
    exact ⟨hmem, hI⟩
  rw [TMIO.mem_realize, hP] at h'
  exact collapsePoint_field_ne_zero (h' .equilibrium (by simp))

/-- Within the context of a positive DC-voltage reference the local exponential translation is not
exact: the collapse point is locally exponentially stable but not an equilibrium. The exact context
is that of an equilibrium with positive reference (`exactUnder_locallyExponentiallyStable`). -/
@[powerlib_domain] theorem not_exactUnder_positiveReference_locallyExponentiallyStable :
    connection% (¬ family.ExactUnder {.positiveReference} (.flow .locallyExponentiallyStable)) := by
  have hmem := collapsePoint_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem ⊢
  exact not_exactUnder_positiveReference_of_mem rfl hmem

/-- Within the context of a positive DC-voltage reference the local asymptotic translation is not
exact (the collapse point). -/
@[powerlib_domain] theorem not_exactUnder_positiveReference_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.positiveReference} (.flow .locallyAsymptoticallyStable)) := by
  have hmem := collapsePoint_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine not_exactUnder_positiveReference_of_mem rfl ?_
  rw [family_isAutonomous.mem_den_flow] at hmem ⊢
  exact Flow.locallyExponentiallyStable_localAsymptoticStable hmem

/-- Within the context of a positive DC-voltage reference the Lyapunov translation is not exact
(the collapse point). -/
@[powerlib_domain] theorem not_exactUnder_positiveReference_lyapunovStable :
    connection% (¬ family.ExactUnder {.positiveReference} (.flow .lyapunovStable)) := by
  have hmem := collapsePoint_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine not_exactUnder_positiveReference_of_mem rfl ?_
  rw [family_isAutonomous.mem_den_flow] at hmem ⊢
  exact hmem.lyapunovStable

/-- The local asymptotic translation is not exact (the negative-reference converter). -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  have hles := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hsound hles
  refine Spectral.not_exact_of_den_subset (s := .flow .locallyExponentiallyStable)
    (s' := .flow .locallyAsymptoticallyStable) rfl
    (Family.chain_le_semantics_iff.mp hsound _) (fun m hm => ?_) hles
  rw [family_isAutonomous.mem_den_flow] at hm ⊢
  exact Flow.locallyExponentiallyStable_localAsymptoticStable hm

/-- The Lyapunov translation is not exact (the negative-reference converter). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  have hles := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hsound hles
  refine Spectral.not_exact_of_den_subset (s := .flow .locallyExponentiallyStable)
    (s' := .flow .lyapunovStable) rfl
    (Family.chain_le_semantics_iff.mp hsound _) (fun m hm => ?_) hles
  rw [family_isAutonomous.mem_den_flow] at hm ⊢
  exact hm.lyapunovStable

end ModelB

end powerlib.GFL
