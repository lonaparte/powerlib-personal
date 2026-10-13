import theorem.GFL.ReducedOrder
import theorem.Criteria.Routh4
import theorem.Criteria.Jacobian
import theorem.Dynamics.Basin
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Flow.Shift
import theorem.TMIO.ClaimElab
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
static: `x*` is a zero of the field, `V_dc* > 0`, the 4×4 Routh conditions on `jacobian x*`, or
`det (jacobian x*) < 0`. The local sentences translate into the first three, instability into the
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

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => m.p.field m.x = 0
  | .positiveReference => 0 < m.p.VdcRef
  | .routh => RouthFin4 (m.p.jacobian m.x)
  | .detNeg => (m.p.jacobian m.x).det < 0

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

end ModelB

end powerlib.GFL
