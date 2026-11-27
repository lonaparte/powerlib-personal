import theorem.Periodic.OrbitalInstability
import theorem.ParametricResonance.SmoothOrbitStability
import theorem.ParametricResonance.ScalarOscillator
import theorem.ParametricResonance.Wirtinger
import theorem.NormalForm.Hopf

/-! # What the linear levels see and what they do not, at a forced operating point

At a forced operating point, an equilibrium `q₀ = (x₀, w₀)` of `F(x, w)` driven by
`w = w₀ + ε V̂ cos ωt` (with the state perturbation `ε A₀'`), small-signal analysis (level L3)
linearizes at `q₀`: its matrix `∂ₓF(q₀) + ε A₀'` does not involve the drive amplitude `V̂`, and
its critical pair moves from `±jω/2` by `ε λ₁ + O(ε²)`, `λ₁ = u A₀' r` (first-order eigenvalue
perturbation, used here only as the reading of `λ₁`). The linearization along the forced orbit
(level L1) carries the pump `A₁ = D_x(∂ₓF)(q₀)[z] + V̂ D_w(∂ₓF)(q₀)`: the curvature of the field
acting on the forced response `z`, plus the direct modulation of the Jacobian by the input
(`ForcedOrbit.smA1`; `ForcedOrbit.orbit_variational` in
`theorem/ParametricResonance/ForcedOrbitFloquet.lean`: `J_ε(t) = A + ε(D_x y_p(t) + D_u(t))
+ O(ε²)`). Since `z = V̂ z₁` is linear in the drive, so is the pump: `g(V̂) = V̂ g₁`. Composed with
the Floquet criterion of the forced orbit (`ForcedOrbit.smooth_orbit_floquet_stable`,
`smooth_orbit_floquet_unstable`) and with the passage from multipliers to the nonlinear orbit
(level L0: `Periodic.exp_stable_of_floquet` inside, `Periodic.unstable_of_floquet` outside the unit
circle), this gives the validity boundary of small-signal analysis at a forced operating point in
parameter space: with `Re λ₁ < 0` (small-signal stable for every drive amplitude), the nonlinear
forced orbit is exponentially stable for `|V̂| |g₁| < 2|λ₁|` and unstable for `|V̂| |g₁| > 2|λ₁|`.
Without curvature and direct modulation (`D_x(∂ₓF)(q₀) = 0`, `D_w(∂ₓF)(q₀) = 0`) the pump vanishes
and the small-signal verdict holds for every drive amplitude; this is the forced-orbit
counterpart, for small `ε`, of `ParametricResonance.affine_of_const_jacobian` and
`orbitExponentiallyStable_iff`, where the Jacobian is constant everywhere.

For the quadratic-stiffness oscillator `q̈ + 2ζω₀q̇ + ω₀²q + aq² = F cos ω_p t`
(`ParametricResonance.ScalarOscillator`) the pump is explicit: along an operating trajectory `q_o`
the variational stiffness is `ω₀² + 2a q_o(t)`, along the first-order trajectory
`q₁ = Re(Q e^{jω_p t})`, `Q = F/D(ω_p)`, a modulation of amplitude `2|a||Q|`; a subharmonic of the
variational equation (multiplier `−1`) needs `ζω₀ω_p ≤ 2|a||Q|`, at the 2:1 tuning
`|aF| ≥ ζω₀⁴√(9 + 16ζ²)`.

What no linear level sees: the existence and the amplitude of a limit cycle. Truncated Hopf fields
with the same Jacobian at the equilibrium have, depending only on the cubic coefficient, an
attracting oscillation of any prescribed amplitude or none at all.

Scope.
* Forced operating point: the hypotheses of `ForcedOrbit.smooth_orbit_floquet_stable` /
  `smooth_orbit_floquet_unstable` (`C³` field `F : ℝ^X × ℝ → ℝ^X`, sup norms, `F(q₀) = 0`, real
  modal coordinates of `∂ₓF(q₀)` with the pair `±jω/2` and a stable block with
  `ρ(e^{TA_s}) < 1`, `T = 2π/ω`); `z₁` is the forced response per unit drive amplitude,
  `(jωI − ∂ₓF(q₀)) z₁ = ∂_wF(q₀)`. The conclusions hold for all small `ε > 0`; deviation
  coordinates `x = state − x₀`. Solutions of the instability statements are integral curves on
  segments `[s, t]`, those of the stability statements on `[s, ∞)`.
* The thresholds `|V̂||g₁| ≶ 2|λ₁|` are the first-order (in `ε`) criterion of the actual forced
  orbit, exact for all small `ε`; the boundary `|V̂||g₁| = 2|λ₁|` itself is not decided at that
  order (decided at second order in `theorem/ParametricResonance/SmoothForcedOrbitSecond.lean`,
  `smooth_orbit_at_threshold`).
* Oscillator: the variational equation is written out in the statements (its link to the field is
  `ScalarOscillator.hasFDerivAt_field`); only the multiplier `−1` (antiperiodic solutions) is
  bounded, with the derivative bound `|q̇_o| ≤ V` of the operating trajectory; the exact forced
  orbit is any such `q_o`, the first-order trajectory `q₁` an instance.
* Hopf: the cubic truncation `NormalForm.Hopf.field` (no `O(|z|⁴)` remainder); the saturated
  amplitude of a parametric (2:1) oscillation is not formalized separately (its envelope obeys the
  same logistic law `NormalForm.Logistic.field` in the averaged coordinates, which is not derived
  here).

Source: the wave-3 question of this library (small-signal instability versus parametric
oscillation across the assumption levels L0–L3: nonlinear periodic model, Floquet linearization
along the periodic operating trajectory, averaging, frozen small-signal matrix); technical report
`GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的统一元素级比较：A₀、A₁ 与 Γ")
§2.1–§2.2 (`A₁ = D_x z + G`, `g = u A₁ r̄`, the criterion `|g/2| ≶ |λ₁|`); work-sync
projects/vsc-parametric-oscillation/notes/theory-draft.md §2.1.2–§2.1.3 (the additive drive
reappears as a periodic stiffness through the curvature, `D²f[χ]`); work-sync
theory/T-hopf-bifurcation.md §1.1–1.4 (super- and subcritical Hopf normal form).

Results.
* `smooth_orbit_unstable` — under the hypotheses of `smooth_orbit_floquet_unstable`, for all small
  `ε > 0` the forced orbit exists and is unstable for the nonlinear driven system (the complement
  of `ForcedOrbit.smooth_orbit_exp_stable`).
* `smA1_drive`, `forced_response_drive`, `pump_drive` — `A₁(V̂) = V̂ A₁(1)`, the forced response is
  `V̂ z₁`, `g(V̂) = V̂ g₁`; `pump_sq_lt_iff`, `sq_lt_pump_iff` — `|g/2|² ≶ |λ₁|²` iff
  `|V̂| |g₁| ≶ 2|λ₁|`.
* `orbit_stable_below_threshold`, `orbit_unstable_above_threshold` — the forced orbit is
  exponentially stable for `|V̂| |g₁| < 2|λ₁|` (with `Re λ₁ < 0`) and unstable for
  `|V̂| |g₁| > 2|λ₁|`.
* `smA1_eq_zero_of_flat`, `orbit_stable_of_flat` — without curvature and direct modulation the pump
  vanishes and the forced orbit is stable for every drive amplitude when `Re λ₁ < 0`.
* `subharmonic_needs_pump` — along any periodic operating trajectory with `|q̇_o| ≤ V`, a
  subharmonic of the oscillator's variational equation needs `ζω₀ω_p² ≤ 2|a|V`;
  `first_order_subharmonic_needs_pump` — along `q₁`: `ζω₀ω_p ≤ 2|a||F/D(ω_p)|`;
  `norm_denom_two_to_one`, `two_to_one_drive_bound` — at `ω_p = 2ω₀`: `|aF| ≥ ζω₀⁴√(9 + 16ζ²)`.
* `linear_data_not_determine_cycle` — for `μ > 0`, `ω₀ ≠ 0` all truncated Hopf fields share the
  Jacobian at the equilibrium; for every `R > 0` one of them (`l₁ = −μ/R²`) has a periodic orbit of
  amplitude `R` that attracts every other nonzero solution, and for `l₁ ≥ 0` the only periodic
  solution is the equilibrium.

Corrections.
None: an extension (the levels' agreement and disagreement at a forced operating point).

Family and connection conclusions.
None: static evidence on smooth periodically forced ODEs, on the oscillator's variational equation
and on the Hopf normal form.
-/

noncomputable section
namespace powerlib.Periodic.Levels
open Complex Matrix Set Filter Topology Metric
open scoped Matrix.Norms.Operator
open ParametricResonance.ForcedOrbit (smJ smA1 matX matX_mulVec smooth_orbit_floquet_unstable
  smooth_estimates exists_lipschitz_ball quad_remainder norm_prod_zero taylor_sub)
open ParametricResonance.TwoToOne (base)
open ParametricResonance.BlockAveraging (expS physLeft physRight)

section Forced

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **End-to-end, nonlinear parametric instability of the forced orbit** (level L0). Under the
hypotheses of `smooth_orbit_floquet_unstable` (`C³` field `F(x, w)` with `F(x₀, w₀) = 0`, drive
`w₀ + ε V̂ cos ωt`, state perturbation `ε A₀'`, real modal coordinates of `∂ₓF(q₀)` with the pair
`±jω/2`, `z` the first-order forced response, `|λ₁| < |g/2|`), for all small `ε > 0` the forced
periodic orbit `y` exists and is unstable for the nonlinear driven system from every initial time
`s`: some `η > 0` is reached by solutions starting arbitrarily close to `y(s)` (deviation
coordinates `x = state − x₀`). The complement of `smooth_orbit_exp_stable`. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_unstable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh z *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
        ε • (A0' *ᵥ y t)) t) ∧
      ∀ s, ∃ η, 0 < η ∧ ∀ δ, 0 < δ → ∃ (x : ℝ → X → ℝ) (t : ℝ), s ≤ t ∧
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ v)) (Icc s t) ∧ ‖x s - y s‖ < δ ∧ η ≤ ‖x t - y t‖ := by
  obtain ⟨c, hc, hex, hfl⟩ := smooth_orbit_floquet_unstable hF hF0 hω hPQ hQP As hA0 hsr hz A0'
    hg
  obtain ⟨-, ρ, ε0, -, -, -, hρ, hε0, -, -, -, -, -, -, hJc, -⟩ := smooth_estimates hF hF0 Vh ω A0'
  obtain ⟨R, KL, hR, hKL, hd, hl⟩ :=
    exists_lipschitz_ball (hF.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  refine ⟨c, hc, ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ ε0 ∧ c * ε ≤ ρ ∧ c * ε ≤ R / 3 ∧ ε * |Vh| ≤ R / 3 := by
    have hlim : Tendsto (fun ε : ℝ => (ε, c * ε, c * ε, ε * |Vh|)) (𝓝[>] 0)
        (𝓝 (0, 0, 0, 0)) := by
      have hcont : Continuous (fun ε : ℝ => (ε, c * ε, c * ε, ε * |Vh|)) := by fun_prop
      have h0 := hcont.tendsto 0
      simp only [mul_zero, zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hopen : ∀ᶠ p : ℝ × ℝ × ℝ × ℝ in 𝓝 (0, 0, 0, 0),
        p.1 < ε0 ∧ p.2.1 < ρ ∧ p.2.2.1 < R / 3 ∧ p.2.2.2 < R / 3 := by
      refine ((continuous_fst.tendsto _).eventually (gt_mem_nhds hε0)).and
        (((continuous_fst.comp continuous_snd).tendsto _).eventually (gt_mem_nhds hρ) |>.and
        ((((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).eventually
          (gt_mem_nhds (by positivity : (0 : ℝ) < R / 3))).and
        (((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).eventually
          (gt_mem_nhds (by positivity : (0 : ℝ) < R / 3)))))
    filter_upwards [hlim.eventually hopen] with ε hε
    exact ⟨hε.1.le, hε.2.1.le, hε.2.2.1.le, hε.2.2.2.le⟩
  filter_upwards [hex, hfl, hsmall, self_mem_nhdsWithin] with ε hεex hεfl ⟨hε0', hcρ, hcR, hVR⟩
    hεpos
  obtain ⟨y, hper, hbd, hode⟩ := hεex
  refine ⟨y, hper, hbd, hode, fun s => ?_⟩
  have hεpos' : 0 < ε := hεpos
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hode t).continuousAt
  have hJcont : Continuous fun t => smJ F q0 Vh ω A0' ε t (y t) :=
    (hJc ε hεpos'.le hε0').comp_continuous (continuous_id.prodMk hyc) fun t =>
      Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hbd t).trans hcρ))
  have hJp : Function.Periodic (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) := by
    intro t
    have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
    simp only [smJ, hper t, e, Real.cos_add_two_pi]
  have hpt : ∀ t (v : X → ℝ), ‖v - y t‖ ≤ R / 3 →
      ‖((q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) - q0‖ ≤ 2 * R / 3 := by
    intro t v hv
    have h1 : ‖v‖ ≤ 2 * R / 3 := by
      have := norm_le_insert' v (y t)
      have h2 : ‖v‖ ≤ ‖y t‖ + ‖v - y t‖ := by
        have := norm_add_le (y t) (v - y t); simpa using this
      linarith [hbd t]
    have h3 : |ε * (Vh * Real.cos (ω * t))| ≤ 2 * R / 3 := by
      rw [abs_mul, abs_mul, abs_of_pos hεpos']
      have := Real.abs_cos_le_one (ω * t)
      have : ε * (|Vh| * |Real.cos (ω * t)|) ≤ ε * |Vh| := by
        have := mul_le_mul_of_nonneg_left this (abs_nonneg Vh)
        nlinarith
      linarith
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left, Real.norm_eq_abs]
    exact max_le h1 h3
  have hGc : ContinuousOn (fun p : ℝ × (X → ℝ) =>
      F (q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) + ε • (A0' *ᵥ p.2))
      {p | ‖p.2 - y p.1‖ ≤ R / 3} := by
    intro p hp
    have hφ : Continuous fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ) := by fun_prop
    have hmem : ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ) ∈
        closedBall q0 R := by
      rw [mem_closedBall, dist_eq_norm]; have := hpt p.1 p.2 hp; linarith
    refine ContinuousWithinAt.add ?_ ?_
    · have hca := ContinuousAt.comp (g := F) (x := p) (f := fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ))
        (hd _ hmem).continuousAt hφ.continuousAt
      exact hca.continuousWithinAt
    · exact (by fun_prop : Continuous fun p : ℝ × (X → ℝ) => ε • (A0' *ᵥ p.2)).continuousWithinAt
  have hRem : ∀ t (e : X → ℝ), ‖e‖ ≤ R / 3 →
      ‖(F (q0.1 + (y t + e), q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ (y t + e))) -
        (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) -
        smJ F q0 Vh ω A0' ε t (y t) *ᵥ e‖ ≤ KL * ‖e‖ ^ 2 := by
    intro t e he
    set a : (X → ℝ) × ℝ := (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) with had
    have ha : ‖a - q0‖ ≤ 2 * R / 3 := hpt t (y t) (by simp; positivity)
    have hsub : closedBall a ‖((e, (0 : ℝ)) : (X → ℝ) × ℝ)‖ ⊆ closedBall q0 R := by
      intro q hq
      rw [mem_closedBall, dist_eq_norm] at hq ⊢
      rw [norm_prod_zero] at hq
      have := norm_sub_le_norm_sub_add_norm_sub q a q0
      linarith
    have hq := quad_remainder hKL hd hl hsub
    rw [norm_prod_zero] at hq
    have e1 : ((q0.1 + (y t + e), q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) =
        a + (e, 0) := by
      rw [had]; ext <;> simp [add_assoc]
    have e2 : smJ F q0 Vh ω A0' ε t (y t) *ᵥ e = fderiv ℝ F a (e, 0) + ε • (A0' *ᵥ e) := by
      rw [smJ, Matrix.add_mulVec, Matrix.smul_mulVec, matX_mulVec]
    rw [e1, e2, Matrix.mulVec_add, smul_add]
    convert hq using 2
    abel
  set KF : ℝ := ‖fderiv ℝ F q0‖ + KL * R + ε * ‖A0'‖ with hKFdef
  have hKF : 0 ≤ KF := by positivity
  have hLip : ∀ t, LipschitzOnWith (Real.toNNReal KF)
      (fun v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ v))
      (closedBall (y t) (R / 3)) := by
    intro t
    refine LipschitzOnWith.of_dist_le_mul fun v1 hv1 v2 hv2 => ?_
    rw [Real.coe_toNNReal _ hKF, dist_eq_norm, dist_eq_norm]
    rw [mem_closedBall, dist_eq_norm] at hv1 hv2
    set q1 : (X → ℝ) × ℝ := (q0.1 + v1, q0.2 + ε * (Vh * Real.cos (ω * t))) with hq1d
    set q2 : (X → ℝ) × ℝ := (q0.1 + v2, q0.2 + ε * (Vh * Real.cos (ω * t))) with hq2d
    have hq1 : q1 ∈ closedBall q0 R := by
      rw [mem_closedBall, dist_eq_norm]; have := hpt t v1 hv1; linarith
    have hq2 : q2 ∈ closedBall q0 R := by
      rw [mem_closedBall, dist_eq_norm]; have := hpt t v2 hv2; linarith
    have hdiff : q1 - q2 = (v1 - v2, 0) := by
      rw [hq1d, hq2d]; ext <;> simp
    have hts := taylor_sub (G := F) (q0 := q0) (r := R) (L := KL) hKL hd
      (fun q hq => hl q hq q0 (mem_closedBall_self hR.le)) le_rfl hq1 hq2
    rw [hdiff, norm_prod_zero] at hts
    have hlin : ‖fderiv ℝ F q0 (v1 - v2, 0)‖ ≤ ‖fderiv ℝ F q0‖ * ‖v1 - v2‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [norm_prod_zero]
    have hA : ‖ε • (A0' *ᵥ v1) - ε • (A0' *ᵥ v2)‖ ≤ ε * ‖A0'‖ * ‖v1 - v2‖ := by
      rw [← smul_sub, ← Matrix.mulVec_sub, norm_smul, Real.norm_of_nonneg hεpos'.le, mul_assoc]
      exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) hεpos'.le
    calc ‖(F q1 + ε • (A0' *ᵥ v1)) - (F q2 + ε • (A0' *ᵥ v2))‖ =
          ‖(F q1 - F q2 - fderiv ℝ F q0 (v1 - v2, 0)) + fderiv ℝ F q0 (v1 - v2, 0) +
            (ε • (A0' *ᵥ v1) - ε • (A0' *ᵥ v2))‖ := by congr 1; abel
      _ ≤ KL * R * ‖v1 - v2‖ + ‖fderiv ℝ F q0‖ * ‖v1 - v2‖ + ε * ‖A0'‖ * ‖v1 - v2‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hts hlin)) hA)
      _ = KF * ‖v1 - v2‖ := by rw [hKFdef]; ring
  exact Periodic.unstable_of_floquet hT hJcont hJp (hεfl y hper hbd hode) hode (by positivity) hKL
    hGc hLip hRem s

/-! ## The pump grows with the drive amplitude: the threshold in parameter space -/

/-- With the unit forced response `z₁` (`(jωI − A) z₁ = ∂_wF(q₀)`), the modulation of the drive
amplitude `V̂` is `A₁(V̂) = V̂ A₁(1)`: `D_x(∂ₓF)(q₀)[V̂ z₁] + V̂ D_w(∂ₓF)(q₀)`. -/
@[tmio T, powerlib_foundation] theorem smA1_drive (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ)
    (Vh : ℝ) (z₁ : X → ℂ) :
    smA1 F q0 Vh ((Vh : ℂ) • z₁) = (Vh : ℂ) • smA1 F q0 1 z₁ := by
  have hre : (fun k => Vh * (z₁ k).re) = Vh • fun k => (z₁ k).re := by funext k; simp
  have him : (fun k => Vh * (z₁ k).im) = Vh • fun k => (z₁ k).im := by funext k; simp
  ext i j
  apply Complex.ext
  · simp [smA1, ParametricResonance.ForcedOrbit.DxC, Complex.mul_re]
    rw [hre, map_smul, Matrix.smul_apply, smul_eq_mul]; ring
  · simp [smA1, ParametricResonance.ForcedOrbit.DxC, Complex.mul_im]
    rw [him, map_smul, Matrix.smul_apply, smul_eq_mul]

/-- The forced response of the drive amplitude `V̂` is `V̂ z₁`. -/
@[tmio T, powerlib_foundation] theorem forced_response_drive {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} {ω : ℝ} {z₁ : X → ℂ}
    (hz₁ : ((ω : ℂ) * I) • z₁ - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z₁ =
      fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) (Vh : ℝ) :
    ((ω : ℂ) * I) • ((Vh : ℂ) • z₁) - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ ((Vh : ℂ) • z₁) =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ) := by
  rw [Matrix.mulVec_smul, smul_comm, ← smul_sub, hz₁]

/-- The pump coefficient is linear in the drive amplitude, `g(V̂) = V̂ g₁`; hence the first-order
criterion `|g/2|² ≶ |λ₁|²` is the drive threshold `|V̂| |g₁| ≶ 2|λ₁|`. -/
@[tmio T, powerlib_foundation] theorem pump_sq_lt_iff (lam g₁ : ℂ) (Vh : ℝ) :
    ‖(Vh : ℂ) * g₁ / 2‖ ^ 2 < ‖lam‖ ^ 2 ↔ |Vh| * ‖g₁‖ < 2 * ‖lam‖ := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_two,
    sq_lt_sq₀ (by positivity) (norm_nonneg _)]
  constructor <;> intro h <;> linarith

@[tmio T, powerlib_foundation] theorem sq_lt_pump_iff (lam g₁ : ℂ) (Vh : ℝ) :
    ‖lam‖ ^ 2 < ‖(Vh : ℂ) * g₁ / 2‖ ^ 2 ↔ 2 * ‖lam‖ < |Vh| * ‖g₁‖ := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_two,
    sq_lt_sq₀ (norm_nonneg _) (by positivity)]
  constructor <;> intro h <;> linarith

/-- The pump of the drive amplitude `V̂` along the forced orbit,
`g(V̂) = u A₁(V̂) r̄ = V̂ g₁` with `g₁ = u A₁(1) r̄`. -/
@[tmio T, powerlib_foundation] theorem pump_drive {Y : Type*} [Fintype Y] [DecidableEq Y]
    (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (P : Matrix X (Fin 2 ⊕ Y) ℝ)
    (Q : Matrix (Fin 2 ⊕ Y) X ℝ) (Vh : ℝ) (z₁ : X → ℂ) :
    physLeft Q ⬝ᵥ (smA1 F q0 Vh ((Vh : ℂ) • z₁) *ᵥ star (physRight P)) =
      (Vh : ℂ) * (physLeft Q ⬝ᵥ (smA1 F q0 1 z₁ *ᵥ star (physRight P))) := by
  rw [smA1_drive, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Below the parametric threshold the forced operating point is stable** (levels L1 and L0).
`z₁` is the forced response per unit drive amplitude, `λ₁ = u A₀' r` the first-order damping of
the critical pair (`Re λ₁ < 0`: small-signal stable for every drive amplitude), and
`g₁ = u A₁(1) r̄` the pump per unit drive amplitude, `A₁(1) = D_x(∂ₓF)(q₀)[z₁] + D_w(∂ₓF)(q₀)`
(curvature acting on the forced response, plus direct modulation). If `|V̂| |g₁| < 2 |λ₁|`, then
for all small `ε > 0` the forced orbit exists and is locally exponentially stable for the nonlinear
driven system. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_below_threshold {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    {z₁ : X → ℂ}
    (hz₁ : ((ω : ℂ) * I) • z₁ - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z₁ =
      fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hdrive : |Vh| * ‖physLeft Q ⬝ᵥ (smA1 F q0 1 z₁ *ᵥ star (physRight P))‖ <
      2 * ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
        ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable hF hF0 hω hPQ hQP As hA0 hsr
    (forced_response_drive hz₁ Vh) A0' hs ?_
  rw [pump_drive, pump_sq_lt_iff]
  exact hdrive

/-- **Above the parametric threshold the forced operating point is unstable** (levels L1 and L0),
although the small-signal verdict at `q₀` does not depend on the drive: if `2 |λ₁| < |V̂| |g₁|`,
then for all small `ε > 0` the forced orbit exists and is unstable for the nonlinear driven system
from every initial time. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_above_threshold {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    {z₁ : X → ℂ}
    (hz₁ : ((ω : ℂ) * I) • z₁ - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z₁ =
      fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ)
    (hdrive : 2 * ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ <
      |Vh| * ‖physLeft Q ⬝ᵥ (smA1 F q0 1 z₁ *ᵥ star (physRight P))‖) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
        ε • (A0' *ᵥ y t)) t) ∧
      ∀ s, ∃ η, 0 < η ∧ ∀ δ, 0 < δ → ∃ (x : ℝ → X → ℝ) (t : ℝ), s ≤ t ∧
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ v)) (Icc s t) ∧ ‖x s - y s‖ < δ ∧ η ≤ ‖x t - y t‖ := by
  refine smooth_orbit_unstable hF hF0 hω hPQ hQP As hA0 hsr (forced_response_drive hz₁ Vh) A0' ?_
  rw [pump_drive, sq_lt_pump_iff]
  exact hdrive

/-- **Without curvature there is no pump.** If the state Hessian and the mixed derivative of the
Jacobian vanish at the operating point (`D_x(∂ₓF)(q₀) = 0`, `D_w(∂ₓF)(q₀) = 0`), then `A₁ = 0`
for every drive amplitude and every forced response. -/
@[tmio T, powerlib_foundation] theorem smA1_eq_zero_of_flat {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hDx : ParametricResonance.ForcedOrbit.smDx F q0 = 0)
    (hM1 : ParametricResonance.ForcedOrbit.smM1 F q0 = 0) (Vh : ℝ) (z : X → ℂ) :
    smA1 F q0 Vh z = 0 := by
  ext i j
  apply Complex.ext <;>
    simp [smA1, ParametricResonance.ForcedOrbit.DxC, hDx, hM1]

/-- **Without curvature the small-signal verdict is exact for every drive amplitude.** With
`D_x(∂ₓF)(q₀) = 0` and `D_w(∂ₓF)(q₀) = 0` and `Re λ₁ < 0`, the forced orbit is locally
exponentially stable for all small `ε > 0`, whatever the drive amplitude `V̂`. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_flat {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    {z₁ : X → ℂ}
    (hz₁ : ((ω : ℂ) * I) • z₁ - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z₁ =
      fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (hDx : ParametricResonance.ForcedOrbit.smDx F q0 = 0)
    (hM1 : ParametricResonance.ForcedOrbit.smM1 F q0 = 0)
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0) (Vh : ℝ) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
        ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  refine orbit_stable_below_threshold hF hF0 hω hPQ hQP As hA0 hsr hz₁ A0' hs ?_
  rw [smA1_eq_zero_of_flat hDx hM1, Matrix.zero_mulVec, dotProduct_zero, norm_zero, mul_zero]
  have h : physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P) ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hs; exact lt_irrefl _ hs
  have := norm_pos_iff.mpr h
  linarith

end Forced

/-! ## The quadratic-stiffness oscillator: the pump that the curvature makes from the drive -/

section Oscillator

open ParametricResonance ParametricResonance.ScalarOscillator
open powerlib.Dynamics (State)

/-- **A subharmonic of the variational equation needs a pump above the damping.** Along any
periodic operating trajectory `q_o` (period `2π/ω_p`, `|q̇_o| ≤ V`) of
`q̈ + 2ζω₀q̇ + ω₀²q + aq² = F cos ω_p t` the variational equation is
`δ̈ + 2ζω₀δ̇ + (ω₀² + 2a q_o(t)) δ = 0` (`ScalarOscillator.hasFDerivAt_field`): the curvature `aq²`
turns the operating trajectory into the periodic stiffness `2a q_o(t)`. A nonzero
`2π/ω_p`-antiperiodic solution (a Floquet multiplier `−1`, the period-doubling boundary of the
forced orbit) forces `ζω₀ω_p² ≤ 2|a|V` (`Wirtinger.pump_bound`). -/
@[tmio T, powerlib_foundation] theorem subharmonic_needs_pump {ζ ω₀ a ωp V : ℝ} (hωp : 0 < ωp)
    {qo qo' : ℝ → ℝ} (hqo : ∀ t, HasDerivAt qo (qo' t) t) (hqo' : Continuous qo')
    (hqoT : Function.Periodic qo (2 * Real.pi / ωp)) (hV : ∀ t, |qo' t| ≤ V)
    {δ δ' δ'' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, δ'' t + 2 * ζ * ω₀ * δ' t + (ω₀ ^ 2 + 2 * a * qo t) * δ t = 0)
    (hanti : Function.Antiperiodic δ (2 * Real.pi / ωp)) (hne : ∃ t, δ t ≠ 0) :
    ζ * ω₀ * ωp ^ 2 ≤ 2 * |a| * V := by
  have hT : 0 < 2 * Real.pi / ωp := by positivity
  have hK : ∀ t, HasDerivAt (fun s => ω₀ ^ 2 + 2 * a * qo s) (2 * a * qo' t) t := fun t =>
    ((hqo t).const_mul (2 * a)).const_add _
  have hKT : Function.Periodic (fun s => ω₀ ^ 2 + 2 * a * qo s) (2 * Real.pi / ωp) := fun t => by
    simp only [hqoT t]
  have hκ : ∀ t, |2 * a * qo' t| ≤ 2 * |a| * V := fun t => by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (hV t) (by positivity)
  have h := Wirtinger.pump_bound (m := 1) (D := 2 * ζ * ω₀) hT hδ hδ' hK
    (continuous_const.mul hqo') hKT (fun t => by have := heq t; simp only [one_mul]; linarith)
    hanti hne hκ
  have e : Real.pi / (2 * Real.pi / ωp) = ωp / 2 := by field_simp
  rw [e] at h
  nlinarith [h]

/-- **The curvature-induced pump of the first-order operating point.** With the first-order
forced displacement `q₁(t) = Re(Q e^{jω_p t})`, `Q = F/D(ω_p)`, `D = ω₀² − ω_p² + 2jζω₀ω_p`
(`ScalarOscillator.forced_q_eq_re`), the variational stiffness is `ω₀² + 2a q₁(t)`, a pump of
amplitude `2|a||Q|`; a subharmonic of the variational equation along `q₁` needs
`ζω₀ω_p ≤ 2|a||Q|`. Below this level (`2|a||Q| < ζω₀ω_p`) the period-doubling boundary is not
reached, whatever the small-signal verdict at `q = 0`. -/
@[tmio TM, powerlib_foundation] theorem first_order_subharmonic_needs_pump {ζ ω₀ a F ωp : ℝ}
    (hωp : 0 < ωp) (hD : denom ζ ω₀ ωp ≠ 0) {δ δ' δ'' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, δ'' t + 2 * ζ * ω₀ * δ' t +
      (ω₀ ^ 2 + 2 * a * forcedOrbit (linPart ζ ω₀) (drive F) ωp t 0) * δ t = 0)
    (hanti : Function.Antiperiodic δ (2 * Real.pi / ωp)) (hne : ∃ t, δ t ≠ 0) :
    ζ * ω₀ * ωp ≤ 2 * |a| * ‖(F : ℂ) / denom ζ ω₀ ωp‖ := by
  have hq : ∀ t, HasDerivAt (fun s => forcedOrbit (linPart ζ ω₀) (drive F) ωp s 0)
      (forcedOrbit (linPart ζ ω₀) (drive F) ωp t 1) t := fun t => (forced_q_solves F hD t).1
  have hq1 : ∀ t, forcedOrbit (linPart ζ ω₀) (drive F) ωp t 1 =
      ((ωp : ℂ) * I * ((F : ℂ) / denom ζ ω₀ ωp) * Complex.exp ((ωp : ℂ) * t * I)).re := by
    intro t
    simp only [forcedOrbit, forcedAmplitude_oscillator F hD]
    rfl
  have hqc : Continuous fun t => forcedOrbit (linPart ζ ω₀) (drive F) ωp t 1 := by
    simp only [hq1]; fun_prop
  have hqT : Function.Periodic (fun s => forcedOrbit (linPart ζ ω₀) (drive F) ωp s 0)
      (2 * Real.pi / ωp) := fun t => by
    simp only [forcedOrbit_periodic (drive F) (by field_simp : ωp * (2 * Real.pi / ωp) =
      2 * Real.pi) t]
  have hV : ∀ t, |forcedOrbit (linPart ζ ω₀) (drive F) ωp t 1| ≤
      ωp * ‖(F : ℂ) / denom ζ ω₀ ωp‖ := by
    intro t
    rw [hq1]
    refine (Complex.abs_re_le_norm _).trans_eq ?_
    rw [show (ωp : ℂ) * t * I = ((ωp * t : ℝ) : ℂ) * I by push_cast; ring, norm_mul, norm_mul,
      norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hωp.le]
    ring
  have h := subharmonic_needs_pump hωp hq hqc hqT hV hδ hδ' heq hanti hne
  have h2 : ωp * (ζ * ω₀ * ωp) ≤ ωp * (2 * |a| * ‖(F : ℂ) / denom ζ ω₀ ωp‖) := by
    nlinarith [h]
  exact le_of_mul_le_mul_left h2 hωp

/-- `|D(2ω₀)| = ω₀² √(9 + 16ζ²)`. -/
@[tmio M, powerlib_foundation] theorem norm_denom_two_to_one (ζ ω₀ : ℝ) :
    ‖denom ζ ω₀ (2 * ω₀)‖ = ω₀ ^ 2 * Real.sqrt (9 + 16 * ζ ^ 2) := by
  rw [denom, Complex.norm_add_mul_I]
  rw [show (ω₀ ^ 2 - (2 * ω₀) ^ 2) ^ 2 + (2 * ζ * ω₀ * (2 * ω₀)) ^ 2 =
    (ω₀ ^ 2) ^ 2 * (9 + 16 * ζ ^ 2) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]

/-- **The 2:1 drive bound.** At the 2:1 tuning `ω_p = 2ω₀` (`ω₀ > 0`) a subharmonic of the
variational equation along the first-order operating point needs the drive
`|a F| ≥ ζ ω₀⁴ √(9 + 16ζ²)`: the curvature-induced pump `2|a||Q|`, `|Q| = |F|/(ω₀²√(9 + 16ζ²))`,
must exceed the damping level `2ζω₀²`. -/
@[tmio TM, powerlib_foundation] theorem two_to_one_drive_bound {ζ ω₀ a F : ℝ} (hω₀ : 0 < ω₀)
    (hD : denom ζ ω₀ (2 * ω₀) ≠ 0) {δ δ' δ'' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, δ'' t + 2 * ζ * ω₀ * δ' t +
      (ω₀ ^ 2 + 2 * a * forcedOrbit (linPart ζ ω₀) (drive F) (2 * ω₀) t 0) * δ t = 0)
    (hanti : Function.Antiperiodic δ (2 * Real.pi / (2 * ω₀))) (hne : ∃ t, δ t ≠ 0) :
    ζ * ω₀ ^ 4 * Real.sqrt (9 + 16 * ζ ^ 2) ≤ |a| * |F| := by
  have h := first_order_subharmonic_needs_pump (by positivity) hD hδ hδ' heq hanti hne
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_denom_two_to_one] at h
  have hs : 0 < Real.sqrt (9 + 16 * ζ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hw : 0 < ω₀ ^ 2 * Real.sqrt (9 + 16 * ζ ^ 2) := by positivity
  rw [mul_div_assoc', le_div_iff₀ hw] at h
  nlinarith [h]

end Oscillator

/-! ## The linear data do not decide the existence or the amplitude of a limit cycle -/

section Hopf

open NormalForm NormalForm.Hopf
open powerlib.Dynamics (State)

/-- **Same linearization, different nonlinear fates.** Fix `μ > 0` and `ω₀ ≠ 0`. Every truncated
Hopf field `ż = (μ + jω₀) z + (l₁ + jκ) z|z|²` has the Jacobian `!![μ, −ω₀; ω₀, μ]` at the
equilibrium (`fderiv_field_zero`), so the small-signal data, and the Floquet data of the
equilibrium as a periodic solution, are the same for all `l₁, κ`. Yet
(i) for every amplitude `R > 0` the field with `l₁ = −μ/R²`, `κ = 0` has a nonconstant periodic
orbit on the circle `‖x‖ = R`, and every forward-complete solution that does not start at the
equilibrium approaches the amplitude `R`;
(ii) for every `l₁ ≥ 0` the only periodic solution is the equilibrium.
The existence and the amplitude of the oscillation are set by the cubic coefficient, which no
linear level sees. -/
@[tmio TM, powerlib_foundation] theorem linear_data_not_determine_cycle {μ ω₀ : ℝ} (hμ : 0 < μ)
    (hω₀ : ω₀ ≠ 0) :
    (∀ l₁ κ, linPart ⟨μ, ω₀, l₁, κ⟩ = !![μ, -ω₀; ω₀, μ]) ∧
    (∀ R, 0 < R → ∃ T, 0 < T ∧ ∃ γ : ℝ → State 2,
      (∀ t, HasDerivAt γ (field ⟨μ, ω₀, -μ / R ^ 2, 0⟩ (γ t)) t) ∧ (∀ t, γ (t + T) = γ t) ∧
      (∃ t, γ t ≠ γ 0) ∧ (∀ t, ‖γ t‖ = R) ∧
      ∀ (a : ℝ) (φ : ℝ → State 2),
        IsIntegralCurveOn φ (fun _ x => field ⟨μ, ω₀, -μ / R ^ 2, 0⟩ x) (Set.Ici a) → φ a ≠ 0 →
          Tendsto (fun t => ‖φ t‖) atTop (𝓝 R)) ∧
    ∀ l₁, 0 ≤ l₁ → ∀ (κ T : ℝ) (γ : ℝ → State 2), 0 < T →
      (∀ t, HasDerivAt γ (field ⟨μ, ω₀, l₁, κ⟩ (γ t)) t) → (∀ t, γ (t + T) = γ t) →
        ∀ t, γ t = 0 := by
  refine ⟨fun l₁ κ => rfl, fun R hR => ?_, fun l₁ hl κ T γ hT hγ hper t0 => ?_⟩
  · set p : Params := ⟨μ, ω₀, -μ / R ^ 2, 0⟩ with hp
    have hl : p.l₁ < 0 := by
      simp only [hp]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
    have hR2 : -p.μ / p.l₁ = R ^ 2 := by
      simp only [hp]; field_simp
    have hrad : radius p = R := by rw [radius, hR2, Real.sqrt_sq hR.le]
    have hfreq : frequency p = ω₀ := by simp [frequency, hp]
    obtain ⟨hT, hd, hpT, hnc⟩ :=
      cycle_isPeriodicOrbit p hl.ne (by rw [hR2]; positivity) (by rw [hfreq]; exact hω₀)
    refine ⟨_, hT, cycle p, hd, hpT, hnc, fun t => by rw [norm_cycle, hrad], fun a φ hφ ha => ?_⟩
    rw [← hrad]
    exact supercritical_norm_tendsto p hμ hl hφ ha
  · set p : Params := ⟨μ, ω₀, l₁, κ⟩ with hp
    have hρ := normSq_isIntegralCurveOn p (s := Set.univ) fun t _ => (hγ t).hasDerivWithinAt
    have hd : ∀ t, HasDerivAt (fun t => ‖γ t‖ ^ 2) (Logistic.field μ l₁ (‖γ t‖ ^ 2)) t :=
      fun t => hasDerivWithinAt_univ.mp (hρ t (Set.mem_univ t))
    set g : ℝ → ℝ := fun t => Real.exp (-(2 * μ) * t) * ‖γ t‖ ^ 2 with hg
    have hgd : ∀ t, HasDerivAt g (Real.exp (-(2 * μ) * t) * (2 * l₁ * (‖γ t‖ ^ 2) ^ 2)) t := by
      intro t
      have he : HasDerivAt (fun s => Real.exp (-(2 * μ) * s)) (Real.exp (-(2 * μ) * t) *
          (-(2 * μ))) t := by
        simpa using ((hasDerivAt_id t).const_mul (-(2 * μ))).exp
      convert he.mul (hd t) using 1
      simp only [Logistic.field]; ring
    have hmono := monotone_of_hasDerivAt_nonneg hgd fun t => by positivity
    have hle := hmono (show t0 ≤ t0 + T by linarith)
    simp only [hg, hper t0] at hle
    have hexp : Real.exp (-(2 * μ) * (t0 + T)) < Real.exp (-(2 * μ) * t0) :=
      Real.exp_lt_exp.2 (by nlinarith)
    have h0 : ‖γ t0‖ ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    have : ‖γ t0‖ = 0 := by nlinarith [norm_nonneg (γ t0)]
    exact norm_eq_zero.mp this

end Hopf

end powerlib.Periodic.Levels
