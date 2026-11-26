import theorem.ParametricResonance.Signature
import theorem.ParametricResonance.ForcedResponse
import theorem.ParametricResonance.SlowFlowBranches
import theorem.ParametricResonance.UniversalThreshold
import theorem.Periodic.Persistence

/-! # Small-signal, averaged and Floquet verdicts: when the levels agree and when they differ

A periodic operating regime can be analysed at four levels of assumption: L0 the nonlinear
time-periodic model `ẋ = F(x, t)`; L1 its linearization about the periodic trajectory,
`ẏ = J(t) y`, judged by the Floquet multipliers; L2 the averaged (first-order, slow-flow) model
of L1 for small modulation; L3 small-signal analysis, the linearization about an equilibrium,
judged on one constant matrix `A₀` (the frozen or the averaged state matrix) by "`A₀` Hurwitz".
This module states, with explicit hypotheses, where the verdicts coincide and where they differ.

* (i) A constant Jacobian removes the parametric channel: L0 = L1 = L3.
* (ii) L3 stable, L1 unstable is realised for every positive damping: two Hurwitz frozen
  stiffness levels with a Hurwitz average and a Floquet multiplier outside the unit circle
  (the Meissner frozen-damping paradox) — small-signal analysis misses parametric instability.
* (iii) L3 unstable, L1 stable is realised for every positive damping: a negative mean stiffness
  (averaged and soft frozen matrices saddles) with a Schur-stable monodromy (parametric
  stabilization, `theorem/ParametricResonance/Kapitza.lean`) — a small-signal false alarm.
* (iv) Agreement regions. A negative mean damping (positive mean trace) is unstable at every
  level for every modulation; in the universal region `ε/√(1 − ε) < 2ξ` every level is stable,
  for every period and waveform; for a hyperbolic `A₀` and small modulation depth L1 inherits
  both strict L3 verdicts (and the largest Floquet exponent tends to the spectral abscissa of
  `A₀`, `Periodic.floquet_exponent_tendsto`). With positive damping every Floquet instability is
  parametric: a real multiplier with a real eigenvector, locked to the pump.
* (v) L2 against L1. First-order averaging is exactly the fast limit: a Hurwitz average is
  equivalent to uniform decay for all short periods, and at a finite period the verdicts can
  differ in both directions ((ii), (iii); at the Kapitza half turn the L1 boundary is `κ = r₀ν`,
  `r₀ ∈ (1, 2)`, while the averaged boundary is `κ = ν`). For the 2:1 slow flow the averaged
  verdicts hold for small depth (`Branches.averaging_branches`, exact for the normal form,
  `Branches.nf_spectrum`); the small-signal branch `s < 0` is unstable at every depth, and for
  `s > 0` every instability at every depth is frequency locked. Quantitatively, for a sinusoidal
  pump the first-order centre threshold is `ε = 4σΩ_m/Ω² ≈ 4ξ`, while the frequency-free Floquet
  bound certifies stability only below `ε/√(1 − ε) = 2ξ`, inside the first-order stable region at
  every detuning.

Scope.
* L1 for continuous `T`-periodic `A(t)` uses `Periodic.monodromy`, `LTI.SchurStable` and
  `Periodic.FloquetUnstable`; the two-level oscillator `ẍ + 2cẋ + k(t)x = 0` (`k = k₁`, then
  `k₂`, over each half period) uses the period map `Averaging.periodMap (1/2) T` of its switched
  form (`theorem/ParametricResonance/Kapitza.lean`; the Meissner monodromy is the case
  `k_{1,2} = ω₀²(1 ± ε)`). L3 is LeanForControl's `LinearSystems.IsHurwitz` of the frozen state
  matrices `oscMatrix c k` and of the averaged matrix `Averaging.avgMatrix`. L2 is the
  state-space average (fast switching) or the 2:1 slow flow `slowFlowMatrix`.
* The nonlinear level enters only through (i) (`ParametricResonance.orbitExponentiallyStable_iff`,
  global solutions of `ż = f(z, u(t))` with constant Jacobian). That a Floquet-stable trajectory is
  locally exponentially stable is `Periodic.exp_stable_of_floquet`; the converse instability
  statement and every amplitude (saturation) question belong to L0 and are not covered here.
* Generic mathematics; no model family. Every theorem composes the cited results.

Source: the hierarchy small-signal / averaging / Floquet of periodically time-varying systems
(Richards, *Analysis of Periodically Time-Varying Systems*, 1983; Nayfeh–Mook, *Nonlinear
Oscillations*, parametrically excited systems); Kapitza (1951) and Arnold, *Mathematical Methods
of Classical Mechanics*, §25, for parametric stabilization; the library results composed here:
`ParametricResonance.Signature.frozen_damping_paradox`, `ParametricResonance.Kapitza`,
`ParametricResonance.Branches`, `Periodic.MeanTrace` (`theorem/Periodic/MeanTrace.lean`),
`Periodic.Persistence` (`theorem/Periodic/Persistence.lean`),
`ParametricResonance.UniversalThreshold`, `Averaging.switched_decay_of_isHurwitz`,
`Averaging.isHurwitz_of_switched_decay`, `ParametricResonance.Element.mathieu_pump`.

Corrections.
* "Positive intrinsic damping and a frozen Hurwitz matrix mean stability" fails in general ((ii));
  "a frozen saddle means instability" fails as well ((iii)). Both small-signal verdicts are
  reliable exactly in the regions of (iv): constant Jacobian, negative mean damping, the
  universal region, and small modulation depth with a hyperbolic `A₀`.
* The exact square-wave tongue centre (`ParametricResonance.Meissner.centre_threshold_iff`) and its
  comparison with the first-order value `4ξ` of the fundamental `4ε/π` are stated where they are
  exact (`Meissner.centre_threshold_lower`, `UniversalThreshold.meissner_centre_above_universal`).
  The first-order (L2) model of the square wave and its direct comparison with the exact centre
  are in `theorem/ParametricResonance/SquareWaveAveraging.lean` (`averaged_centre_threshold`:
  L2 threshold `πξ`; `centre_threshold_ratio`, `centre_levels_agree`: exact and averaged verdicts
  agree outside the cone `|ε − πξ| ≤ ηξ` for small `ξ, ε`; `meissner_averaging_stable`,
  `meissner_averaging_unstable`: the L2 verdict holds for the exact monodromy at small depth).

Results.
* `floquet_iff_smallSignal_of_const` — `A(t) ≡ A₀`: Schur-stable monodromy iff `A₀` Hurwitz;
  `levels_agree_of_const_jacobian` — constant Jacobian `A₀`: the variational matrix along every
  reference solution is `A₀`, and orbit exponential stability (L0) ⇔ Schur stability of the
  variational monodromy (L1) ⇔ `A₀` Hurwitz (L3).
* `smallSignal_misses_parametric` — every `c > 0`: Hurwitz frozen levels and average, a multiplier
  outside the unit circle.
* `smallSignal_false_alarm` — every `c > 0`: negative mean stiffness, averaged and soft frozen
  matrices not Hurwitz, Schur-stable monodromy.
* `negativeDamping_levels_agree` — two-level oscillator, `c < 0`: no frozen or averaged matrix is
  Hurwitz, a multiplier outside the unit circle, for all levels and periods.
* `isHurwitz_iff_fast_switched_decay` — the averaged matrix is Hurwitz iff uniform exponential
  decay holds for every period `T ∈ (0, T₀]`.
* `floquet_iff_smallSignal_of_small` — hyperbolic `A₀`: for `|ε| < ε₀`, Schur stability of
  `ẋ = (A₀ + εA₁(t))x` iff `A₀` Hurwitz (any dimension).
* `secondOrder_verdict_table` — `m δ̈ + D δ̇ + K(t) δ = 0`: `D < 0` all levels unstable;
  `D > 0` every Floquet instability is a real multiplier with a real eigenvector; the universal
  region all levels stable.
* `integral_trace_full` — the complete two-state 2:1 system has mean trace `−2εs`;
  `twoToOne_branches_every_depth` — every `ε > 0`: `s < 0` Floquet unstable; `s > 0` multipliers
  with `|μ| ≥ 1` real and instabilities carried by a real eigenvector.
* `universal_inside_firstOrder` — damped Mathieu pump: first-order centre threshold
  `ε < 4σΩ_m/Ω²` (iff); below the universal bound `ε/√(1 − ε) < 2σ/Ω` the slow flow is Hurwitz at
  every detuning and the monodromy Schur stable for every period.
-/

noncomputable section
namespace powerlib.Periodic.Levels

open Set Matrix Function Filter Topology
open powerlib.Periodic (oscMatrix)

/-! ## (i) A constant Jacobian: the levels coincide -/

section Constant

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Constant state matrix: Floquet = small signal.** For `A(t) ≡ A₀` and any period `T > 0`
the monodromy matrix `e^{TA₀}` is Schur stable iff `A₀` is Hurwitz (`Periodic.monodromy_const`,
`LTI.isHurwitz_iff_schurStable_exp`). -/
@[tmio T, powerlib_foundation] theorem floquet_iff_smallSignal_of_const
    (A₀ : Matrix (Fin n) (Fin n) ℝ) {T : ℝ} (hT : 0 < T) :
    LTI.SchurStable (Periodic.monodromy (fun _ => A₀) T 0) ↔ LinearSystems.IsHurwitz A₀ := by
  rw [Periodic.monodromy_const A₀ hT.le, ← LTI.isHurwitz_iff_schurStable_exp A₀ hT]

/-- **Constant Jacobian: the nonlinear, Floquet and small-signal verdicts coincide.** If the state
Jacobian of `ż = f(z, u)` is the constant `A₀` (for all `z`, `u`), then along every reference
solution `z_orb` of `ż = f(z, u(t))` the variational matrix is `A₀`, and the three verdicts are
equivalent: exponential stability of `z_orb` (every solution converges to it at a uniform
exponential rate, level L0), Schur stability of the variational monodromy over any period
`T > 0` (L1), and `A₀` Hurwitz (L3) (`ParametricResonance.orbitExponentiallyStable_iff`). -/
@[tmio T, powerlib_foundation] theorem levels_agree_of_const_jacobian {U : Type*}
    {f : ℝⁿ → U → ℝⁿ} {A₀ : Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ z u, HasFDerivAt (fun z => f z u) (Linear.op A₀) z)
    {u : ℝ → U} {z_orb : ℝ → ℝⁿ} (horb : ∀ t, HasDerivAt z_orb (f (z_orb t) (u t)) t)
    {T : ℝ} (hT : 0 < T) :
    (∀ t, fderiv ℝ (fun z => f z (u t)) (z_orb t) = Linear.op A₀) ∧
      ((∃ K > 0, ∃ rate > 0, ∀ z : ℝ → ℝⁿ, (∀ t, HasDerivAt z (f (z t) (u t)) t) →
          ∀ t, 0 ≤ t → ‖z t - z_orb t‖ ≤ K * Real.exp (-(rate * t)) * ‖z 0 - z_orb 0‖) ↔
        LTI.SchurStable (Periodic.monodromy (fun _ => A₀) T 0)) ∧
      (LTI.SchurStable (Periodic.monodromy (fun _ => A₀) T 0) ↔ LinearSystems.IsHurwitz A₀) :=
  ⟨ParametricResonance.jacobian_along_orbit hf u z_orb,
    (ParametricResonance.orbitExponentiallyStable_iff hf horb).trans
      (floquet_iff_smallSignal_of_const A₀ hT).symm,
    floquet_iff_smallSignal_of_const A₀ hT⟩

end Constant

/-! ## (ii), (iii) The two disagreements, on the two-level oscillator -/

section TwoLevel

open scoped Matrix.Norms.Operator

/-- **(ii) Small-signal stable, Floquet unstable, for every positive damping.** For every
`c > 0` there are stiffness levels `k₁, k₂ > 0` and a period `T > 0` such that both frozen state
matrices `oscMatrix c k_i` and the averaged matrix are Hurwitz, yet the two-level oscillator
(`k = k₁` on the first, `k₂` on the second half period) has a Floquet multiplier outside the unit
circle: a parametric instability that small-signal analysis misses
(`ParametricResonance.Signature.frozen_damping_paradox` with `ν = 4πc`). -/
@[tmio T, powerlib_foundation] theorem smallSignal_misses_parametric {c : ℝ} (hc : 0 < c) :
    ∃ k₁ k₂ T : ℝ, 0 < T ∧ LinearSystems.IsHurwitz (oscMatrix c k₁) ∧
      LinearSystems.IsHurwitz (oscMatrix c k₂) ∧
      LinearSystems.IsHurwitz (Averaging.avgMatrix (1 / 2) (oscMatrix c k₁) (oscMatrix c k₂)) ∧
      ∃ μ ∈ spectrum ℂ ((Averaging.periodMap (1 / 2) T (oscMatrix c k₁)
        (oscMatrix c k₂)).map (algebraMap ℝ ℂ)), 1 < ‖μ‖ := by
  set ν := 4 * Real.pi * c with hν
  have hν0 : 0 < ν := by positivity
  obtain ⟨-, -, hu⟩ := ParametricResonance.Signature.frozen_damping_paradox hc hν0 le_rfl
  set ω₀ := √((5 * ν ^ 2 + 2 * c ^ 2) / 2)
  set ε := 3 * ν ^ 2 / (5 * ν ^ 2 + 2 * c ^ 2) with hε
  have hD : 0 < 5 * ν ^ 2 + 2 * c ^ 2 := by positivity
  have hω₀sq : ω₀ ^ 2 = (5 * ν ^ 2 + 2 * c ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hp : ω₀ ^ 2 * (1 + ε) = 4 * ν ^ 2 + c ^ 2 := by
    rw [hω₀sq, hε]; field_simp; ring
  have hm : ω₀ ^ 2 * (1 - ε) = ν ^ 2 + c ^ 2 := by
    rw [hω₀sq, hε]; field_simp; ring
  have hH : ∀ k, 0 < k → LinearSystems.IsHurwitz (oscMatrix c k) := fun k hk => by
    rw [Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix, Periodic.det_oscMatrix]
    exact ⟨by linarith, hk⟩
  refine ⟨ω₀ ^ 2 * (1 + ε), ω₀ ^ 2 * (1 - ε), 2 * Real.pi / (3 * ν), by positivity,
    hH _ (by rw [hp]; positivity), hH _ (by rw [hm]; positivity), ?_, hu⟩
  rw [ParametricResonance.Kapitza.avgMatrix_oscMatrix]
  exact hH _ (by rw [hp, hm]; positivity)

/-- **(iii) Small-signal unstable, Floquet stable, for every positive damping.** For every
`c > 0` there are stiffness levels with negative mean (`k₁ + k₂ < 0`) and a period `T > 0` such
that the averaged matrix and the frozen matrix of the soft half period are saddles (not
Hurwitz), yet the monodromy matrix of the two-level oscillator is Schur stable: a small-signal
false alarm (parametric stabilization, `ParametricResonance.Kapitza.small_signal_false_alarm` on
the window of `ParametricResonance.Kapitza.exists_window`). -/
@[tmio T, powerlib_foundation] theorem smallSignal_false_alarm {c : ℝ} (hc : 0 < c) :
    ∃ k₁ k₂ T : ℝ, 0 < T ∧ k₁ + k₂ < 0 ∧
      ¬ LinearSystems.IsHurwitz (Averaging.avgMatrix (1 / 2) (oscMatrix c k₁) (oscMatrix c k₂)) ∧
      ¬ LinearSystems.IsHurwitz (oscMatrix c k₂) ∧
      LTI.SchurStable (Averaging.periodMap (1 / 2) T (oscMatrix c k₁) (oscMatrix c k₂)) := by
  obtain ⟨r₀, hr₀, -, -, hwin⟩ := ParametricResonance.Kapitza.exists_window
  set r := (1 + r₀) / 2 with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hrr : r < r₀ := by rw [hr]; linarith
  set ν := 2 * c / (r - 1) + 1 with hνdef
  have hν : 0 < ν := add_pos_of_nonneg_of_pos (div_nonneg (by positivity) (by linarith)) one_pos
  have hνc : 2 * c < (r - 1) * ν := by
    have h1 : (r - 1) * (2 * c / (r - 1)) = 2 * c := mul_div_cancel₀ _ (by linarith)
    nlinarith
  have hκ : 0 < r * ν := by positivity
  have hm : ν ^ 2 + 2 * c ^ 2 < (r * ν) ^ 2 := by nlinarith
  have hτ := (hwin ν (r * ν) hν (by nlinarith)).mpr (by nlinarith)
  obtain ⟨hmean, -, hnot, hnot₂, hS, -⟩ :=
    ParametricResonance.Kapitza.small_signal_false_alarm hν hκ hc (div_pos Real.pi_pos hν) hm hτ
  exact ⟨_, _, _, div_pos Real.pi_pos hν, by linarith, hnot, hnot₂, hS⟩

/-- **Negative damping: every level says unstable.** For `c < 0`, whatever the stiffness levels
`k₁`, `k₂` and the period `T > 0`: both frozen matrices and the averaged matrix are not Hurwitz,
and the two-level oscillator has a Floquet multiplier outside the unit circle
(`ParametricResonance.Kapitza.negative_damping_unstable`: `det M = e^{−2cT} > 1`). -/
@[tmio T, powerlib_foundation] theorem negativeDamping_levels_agree {c : ℝ} (hc : c < 0)
    (k₁ k₂ : ℝ) {T : ℝ} (hT : 0 < T) :
    ¬ LinearSystems.IsHurwitz (oscMatrix c k₁) ∧ ¬ LinearSystems.IsHurwitz (oscMatrix c k₂) ∧
      ¬ LinearSystems.IsHurwitz (Averaging.avgMatrix (1 / 2) (oscMatrix c k₁) (oscMatrix c k₂)) ∧
      ∃ μ ∈ spectrum ℂ ((Averaging.periodMap (1 / 2) T (oscMatrix c k₁)
        (oscMatrix c k₂)).map (algebraMap ℝ ℂ)), 1 < ‖μ‖ := by
  have hN : ∀ k, ¬ LinearSystems.IsHurwitz (oscMatrix c k) := fun k h => by
    rw [Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix] at h
    linarith [h.1]
  obtain ⟨h1, h2⟩ := ParametricResonance.Kapitza.negative_damping_unstable hc k₁ k₂ hT
  exact ⟨hN k₁, hN k₂, h1, h2⟩

end TwoLevel

/-! ## (v) The averaged level as the fast limit of the Floquet level -/

section Fast

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- **First-order averaging is exactly the fast-switching limit.** For the two-topology switched
system (`ẋ = A₁ x`, then `ẋ = A₂ x`, duty ratio `d`, period `T`) the averaged matrix
`d A₁ + (1 − d) A₂` is Hurwitz iff there are `T₀ > 0` and `C`, `α > 0` such that for every period
`T ∈ (0, T₀]` every switched trajectory decays as `C e^{−αt}`
(`Averaging.switched_decay_of_isHurwitz`, `Averaging.isHurwitz_of_switched_decay`). At a fixed
finite period the verdicts can differ in both directions (`smallSignal_misses_parametric`,
`smallSignal_false_alarm`). -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_fast_switched_decay {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) :
    LinearSystems.IsHurwitz (Averaging.avgMatrix d A₁ A₂) ↔
      ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ T ∈ Ioc (0 : ℝ) T₀,
        ∀ x : ℝ → Fin n → ℝ,
        (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
          IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
        ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖ := by
  constructor
  · exact Averaging.switched_decay_of_isHurwitz hd0 hd1 A₁ A₂
  · rintro ⟨T₀, hT₀, C, α, -, hα, h⟩
    exact Averaging.isHurwitz_of_switched_decay hd0 hd1 A₁ A₂ hT₀ hα h

end Fast

/-! ## (iv) Agreement regions -/

section Small

variable {n : ℕ}

/-- **Small modulation: the Floquet verdict is the small-signal verdict.** If `A₀` has no
eigenvalue on the imaginary axis, there is `ε₀ > 0` such that for `|ε| < ε₀` the periodic system
`ẋ = (A₀ + ε A₁(t)) x` (`A₁` continuous, `T`-periodic) has a Schur-stable monodromy matrix iff
`A₀` is Hurwitz, in any dimension (`Periodic.exists_schurStable_of_isHurwitz`,
`Periodic.exists_floquetUnstable_of_re_pos`): L1 inherits both strict L3 verdicts, and a
parametric instability of a small-signal-stable system needs a modulation depth bounded away
from `0`. -/
@[tmio T, powerlib_foundation] theorem floquet_iff_smallSignal_of_small
    {A₀ : Matrix (Fin n) (Fin n) ℝ}
    (hhyp : ∀ μ ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ)), μ.re ≠ 0)
    {A₁ : ℝ → Matrix (Fin n) (Fin n) ℝ} (hA₁ : Continuous A₁) {T : ℝ} (hP : Periodic A₁ T)
    (hT : 0 < T) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ →
      (LTI.SchurStable (Periodic.monodromy (fun t => A₀ + ε • A₁ t) T 0) ↔
        LinearSystems.IsHurwitz A₀) := by
  by_cases hH : LinearSystems.IsHurwitz A₀
  · obtain ⟨ε₀, hε₀, h⟩ := Periodic.exists_schurStable_of_isHurwitz hH hA₁ hP hT
    exact ⟨ε₀, hε₀, fun ε hε => iff_of_true (h ε hε) hH⟩
  · obtain ⟨μ, v, hv, heig, hre⟩ := (Criteria.not_isHurwitz_iff A₀).mp hH
    have hμ : μ ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ)) :=
      LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, heig⟩
    have hre' : 0 < μ.re := lt_of_le_of_ne hre (hhyp μ hμ).symm
    obtain ⟨ε₀, hε₀, h⟩ := Periodic.exists_floquetUnstable_of_re_pos hμ hre' hA₁ hP hT
    refine ⟨ε₀, hε₀, fun ε hε => iff_of_false (fun hS => ?_) hH⟩
    obtain ⟨ρ, hρ, h1⟩ := h ε hε
    obtain ⟨w, hw, hρw⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hρ
    exact absurd (hS ρ w hw hρw) (not_lt.mpr h1.le)

end Small

section SecondOrder

open ParametricResonance.UniversalThreshold in
/-- **The verdict table of `m δ̈ + D δ̇ + K(t) δ = 0`** (constant damping `D`, `m > 0`,
continuous `T`-periodic stiffness `K`, state matrix `oscMatrix (D/(2m)) (K(t)/m)`).
* `D < 0`: for every stiffness `k` (every frozen value `K(t)/m` and the averaged one) the
  small-signal matrix is not Hurwitz, and the periodic system is Floquet unstable, for every
  modulation (`Periodic.secondOrder_levels_agree_of_mean_damping_neg`): the levels agree.
* `D > 0`: a Floquet instability is carried by a real multiplier `|r| > 1` with a real
  eigenvector, i.e. it is a parametric (frequency-locked) instability
  (`Periodic.secondOrder_parametric_of_mean_damping_pos`); small-signal analysis of the frozen
  matrices can then disagree (`smallSignal_misses_parametric`, `smallSignal_false_alarm`).
* `D > 0`, `|K(t) − K̄| ≤ εK̄`, `ε/√(1 − ε) < D/√(mK̄)` (`2ξ`): every frozen matrix and the matrix
  of the centre stiffness `K̄` are Hurwitz and the monodromy is Schur stable
  (`UniversalThreshold.levels_agree_of_threshold`): the levels agree, whatever the period and
  the waveform. -/
@[tmio T, powerlib_foundation] theorem secondOrder_verdict_table {m D T : ℝ} {K : ℝ → ℝ}
    (hm : 0 < m) (hT : 0 < T) (hK : Continuous K) (hKP : Periodic K T) :
    (D < 0 → (∀ k : ℝ, ¬ LinearSystems.IsHurwitz (oscMatrix (D / (2 * m)) k)) ∧
        Periodic.FloquetUnstable (fun t => oscMatrix (D / (2 * m)) (K t / m)) T) ∧
      (0 < D → Periodic.FloquetUnstable (fun t => oscMatrix (D / (2 * m)) (K t / m)) T →
        ∃ r : ℝ, 1 < |r| ∧ ∃ w : Fin 2 → ℝ, w ≠ 0 ∧
          Periodic.monodromy (fun t => oscMatrix (D / (2 * m)) (K t / m)) T 0 *ᵥ w = r • w) ∧
      (∀ Kbar ε : ℝ, 0 < Kbar → 0 ≤ ε → ε < 1 → ε / √(1 - ε) < D / √(m * Kbar) →
        (∀ t, |K t - Kbar| ≤ ε * Kbar) →
        (∀ t, LinearSystems.IsHurwitz (oscMatrix (D / (2 * m)) (K t / m))) ∧
          LinearSystems.IsHurwitz (oscMatrix (D / (2 * m)) (Kbar / m)) ∧
          LTI.SchurStable (Periodic.monodromy (fun t => oscMatrix (D / (2 * m)) (K t / m)) T 0)) := by
  have hint : ∫ _ in (0 : ℝ)..T, D = T * D := by simp
  have hD : Continuous fun _ : ℝ => D := continuous_const
  have hDP : Periodic (fun _ : ℝ => D) T := fun _ => rfl
  refine ⟨fun hneg => ?_, fun hpos hU => ?_, fun Kbar ε hKbar hε hε1 hξ hdev => ?_⟩
  · obtain ⟨h1, h2⟩ := Periodic.secondOrder_levels_agree_of_mean_damping_neg (D := fun _ => D)
      hD hK hDP hKP hm hT (by rw [hint]; nlinarith)
    refine ⟨fun k => ?_, h2⟩
    have := h1 k
    rwa [hint, mul_div_cancel_left₀ _ hT.ne'] at this
  · exact (Periodic.secondOrder_parametric_of_mean_damping_pos (D := fun _ => D) hD hK hDP hKP hm
      (by rw [hint]; positivity)).2 hU
  · obtain ⟨h1, h2, -⟩ := levels_agree_of_threshold hm hKbar hε hε1 hξ hT hK hKP hdev
    refine ⟨h1, ?_, h2⟩
    have hs1 : 0 ≤ ε / √(1 - ε) := div_nonneg hε (Real.sqrt_nonneg _)
    have hDpos : 0 < D := (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (by positivity))).mp
      (hs1.trans_lt hξ)
    rw [Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix, Periodic.det_oscMatrix]
    exact ⟨by have : 0 < D / (2 * m) := by positivity
              linarith, by positivity⟩

end SecondOrder

/-! ## (v) The averaged 2:1 level against the Floquet level -/

section TwoToOne

open ParametricResonance.TwoToOne (full base modReal integral_cos_mul_period
  integral_sin_mul_period continuous_full periodic_full)

/-- The mean trace of the complete two-state system `ẋ = (A₀ + ε Re{A₁ e^{jωt}}) x` with
`σ = εs` (`TwoToOne.full`) over one pump period: `∫₀ᵀ tr = −2εs T` (the modulation has zero
mean trace). -/
@[tmio T, powerlib_foundation] theorem integral_trace_full (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), (full s d ω A ε t).trace =
      -(2 * (ε * s)) * (2 * Real.pi / ω) := by
  have htr : ∀ t, (full s d ω A ε t).trace = -(2 * (ε * s)) +
      ε * (((A 0 0).re + (A 1 1).re) * Real.cos ((1 : ℕ) * (ω * t)) -
        ((A 0 0).im + (A 1 1).im) * Real.sin ((1 : ℕ) * (ω * t))) := by
    intro t
    simp [full, base, modReal, Matrix.trace_fin_two]
    ring
  simp only [htr]
  have hc := integral_cos_mul_period hω 1 one_ne_zero
  have hs := integral_sin_mul_period hω 1 one_ne_zero
  rw [intervalIntegral.integral_add intervalIntegrable_const (by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (by
      apply Continuous.intervalIntegrable; fun_prop) (by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hc, hs]
  simp
  ring

/-- **The two branches of the slow flow at every modulation depth.** For the complete two-state
system `TwoToOne.full s d ω A ε` and every depth `ε > 0` (not only small ones):
* `s < 0` (small-signal branch): Floquet unstable, for every modulation `A₁` and detuning `d`
  (positive mean trace, `Periodic.floquetUnstable_of_integral_trace_pos`);
* `s > 0`: every multiplier on or outside the unit circle is real, and an instability is carried
  by a real multiplier `|r| > 1` with a real eigenvector (`Periodic.im_eq_zero_of_integral_trace_neg`,
  `Periodic.real_multiplier_of_floquetUnstable`): only the frequency-locked parametric mechanism
  of `Branches.parametric_real_roots` can destabilize. -/
@[tmio T, powerlib_foundation] theorem twoToOne_branches_every_depth {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε : 0 < ε) :
    (s < 0 → Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω)) ∧
      (0 < s → (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), 1 ≤ ‖μ‖ → μ.im = 0) ∧
        (Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω) →
          ∃ r : ℝ, 1 < |r| ∧ ∃ w : Fin 2 → ℝ, w ≠ 0 ∧
            Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0 *ᵥ w = r • w)) := by
  have hc := continuous_full s d ω A ε
  have hp := periodic_full s d hω.ne' A ε
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hI := integral_trace_full s d hω A ε
  refine ⟨fun hs => Periodic.floquetUnstable_of_integral_trace_pos hc hp ?_, fun hs => ?_⟩
  · rw [hI]
    have : 0 < -(2 * (ε * s)) := by nlinarith
    positivity
  · have hneg : ∫ t in (0 : ℝ)..(2 * Real.pi / ω), (full s d ω A ε t).trace < 0 := by
      rw [hI]
      have : -(2 * (ε * s)) < 0 := by nlinarith
      exact mul_neg_of_neg_of_pos this hT
    exact ⟨fun μ hμ h1 => Periodic.im_eq_zero_of_integral_trace_neg hc hp hneg hμ h1,
      Periodic.real_multiplier_of_floquetUnstable hc hp hneg⟩

end TwoToOne

section Gap

open ParametricResonance.UniversalThreshold
open ParametricResonance.Element (pump mathieuA₁ mathieuLeft mathieuRight mathieu_pump)
open ParametricResonance (slowFlowMatrix trace_slowFlowMatrix det_slowFlowMatrix)

/-- **The universal Floquet region against the first-order 2:1 boundary (sinusoidal pump).** For
`ẍ + 2σẋ + Ω²(1 + ε cos(2πt/T)) x = 0` (`σ > 0`, `Ω > 0`, `Ω_m² = Ω² − σ²`, `Ω_m > 0`,
`4σ² ≤ 3Ω²`, `0 ≤ ε < 1`), with first-order pump coefficient `g` of the damped Mathieu equation
(`Element.mathieu_pump`, `|g| = Ω²/(2Ω_m)`) and slow flow `slowFlowMatrix σ Δ (εg/2)`:
* at the tongue centre (`Δ = 0`) the first-order (L2) slow flow is Hurwitz iff
  `ε < 4σΩ_m/Ω²` (≈ `4ξ`, `ξ = σ/Ω`);
* if `ε/√(1 − ε) < 2σ/Ω` (≈ `2ξ`, the universal threshold), the slow flow is Hurwitz at every
  detuning `Δ` and the periodic system is Floquet stable for every period `T > 0`
  (`UniversalThreshold.schurStable_of_threshold_waveform`): L1 and L2 agree there. Between the two
  thresholds the first-order verdict "stable" is not certified at the Floquet level by any
  frequency-free bound; at finite `ε` the levels can be compared only by the exact boundary. -/
@[tmio T, powerlib_foundation] theorem universal_inside_firstOrder {σ Ω Ωm ε : ℝ} (hσ : 0 < σ)
    (hΩ : 0 < Ω) (hΩm : 0 < Ωm) (hm : Ωm ^ 2 = Ω ^ 2 - σ ^ 2) (h3 : 4 * σ ^ 2 ≤ 3 * Ω ^ 2)
    (hε : 0 ≤ ε) (hε1 : ε < 1) :
    (LinearSystems.IsHurwitz (slowFlowMatrix σ 0
        ((ε : ℂ) * pump (mathieuA₁ Ω 1) (mathieuLeft σ Ωm) (mathieuRight σ Ωm) / 2)) ↔
      ε < 4 * σ * Ωm / Ω ^ 2) ∧
      (ε / √(1 - ε) < 2 * σ / Ω →
        (∀ Δ : ℝ, LinearSystems.IsHurwitz (slowFlowMatrix σ Δ
          ((ε : ℂ) * pump (mathieuA₁ Ω 1) (mathieuLeft σ Ωm) (mathieuRight σ Ωm) / 2))) ∧
        ∀ T : ℝ, 0 < T → LTI.SchurStable (Periodic.monodromy
          (fun t => oscMatrix (2 * σ / (2 * 1)) (Ω ^ 2 * (1 + ε * Real.cos (2 * Real.pi / T * t)) / 1))
          T 0)) := by
  have hg : ‖(ε : ℂ) * pump (mathieuA₁ Ω 1) (mathieuLeft σ Ωm) (mathieuRight σ Ωm) / 2‖ =
      ε * Ω ^ 2 / (4 * Ωm) := by
    rw [mathieu_pump σ Ω Ωm 1 hΩm.ne', norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hε, norm_mul, Complex.norm_I, one_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hΩm.le]
    field_simp
    ring
  have hH : ∀ Δ : ℝ, LinearSystems.IsHurwitz (slowFlowMatrix σ Δ
      ((ε : ℂ) * pump (mathieuA₁ Ω 1) (mathieuLeft σ Ωm) (mathieuRight σ Ωm) / 2)) ↔
        (ε * Ω ^ 2 / (4 * Ωm)) ^ 2 < σ ^ 2 + Δ ^ 2 := by
    intro Δ
    rw [Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix, det_slowFlowMatrix, hg]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩
  have hpos : 0 ≤ ε * Ω ^ 2 / (4 * Ωm) := by positivity
  refine ⟨?_, fun hξ => ⟨fun Δ => ?_, fun T hT => ?_⟩⟩
  · rw [hH, zero_pow two_ne_zero, add_zero, ← Real.sqrt_lt_sqrt_iff (sq_nonneg _),
      Real.sqrt_sq hpos, Real.sqrt_sq hσ.le, div_lt_iff₀ (by positivity),
      lt_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  · -- `ε ≤ ε/√(1 − ε) < 2σ/Ω`, and `Ω ≤ 2Ω_m`
    have hs1 : √(1 - ε) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have hs0 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
    have hεle : ε ≤ ε / √(1 - ε) := by
      rw [le_div_iff₀ hs0]; nlinarith
    have hεσ : ε * Ω < 2 * σ := by
      have := hεle.trans_lt hξ
      rwa [lt_div_iff₀ hΩ] at this
    have h2m : Ω ≤ 2 * Ωm := by nlinarith
    rw [hH]
    have hlt : ε * Ω ^ 2 / (4 * Ωm) < σ := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith [sq_nonneg Δ]
  · have hsq : √(1 * Ω ^ 2) = Ω := by rw [one_mul, Real.sqrt_sq hΩ.le]
    refine schurStable_of_threshold_waveform (m := 1) (D := 2 * σ) (Kbar := Ω ^ 2) one_pos
      (by positivity) hε hε1 (by rw [hsq]; exact hξ) T hT (fun t => Real.cos (2 * Real.pi / T * t))
      (by fun_prop) (fun t => ?_) (fun t => Real.abs_cos_le_one _) ε ⟨by linarith, le_rfl⟩
    show Real.cos (2 * Real.pi / T * (t + T)) = Real.cos (2 * Real.pi / T * t)
    rw [show 2 * Real.pi / T * (t + T) = 2 * Real.pi / T * t + 2 * Real.pi by field_simp,
      Real.cos_add_two_pi]

end Gap

end powerlib.Periodic.Levels
