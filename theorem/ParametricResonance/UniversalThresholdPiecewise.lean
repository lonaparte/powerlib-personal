import theorem.ParametricResonance.SquareWaveAveraging
import theorem.ParametricResonance.Kapitza

/-! # The universal threshold for piecewise-continuous stiffness

The frequency- and waveform-free bound of `theorem/ParametricResonance/UniversalThreshold.lean`,
`2ξ ≤ ε / √(1 − ε)` for a sustained oscillation of `m δ̈ + D δ̇ + K(t) δ = 0` with
`|K − K̄| ≤ εK̄`, is extended to stiffness functions that jump: `K` only needs to be integrable,
and solutions are continuous with continuous velocity and right derivatives, the switched
trajectories of the square-wave (Meissner) and two-level (Kapitza, general duty) models. The
energy argument is unchanged: the right derivatives of `m δ̇²/2 + K̄ δ²/2` and `m δ̇ δ + D δ²/2`
are `−(D δ̇² + (K − K̄) δ δ̇)` and `−(K δ² − m δ̇²)` wherever the equation holds, and the
fundamental theorem of calculus for right derivatives (Mathlib
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`) integrates them across the jumps.
Only the values at the two ends of the interval enter, so the bound holds for every solution on
`[0, L]` with `δ(L) = ±δ(0)`, `δ̇(L) = ±δ̇(0)`: periodic and antiperiodic boundary values.

For the Floquet statement no periodic extension and no continuous monodromy is needed: a matrix
`M` is a period map of the switched system when every initial state `w` has a solution on
`[0, T]` with `y(T) = M w`. Liouville's formula holds for such solutions (the Wronskian has right
derivative `−(D/m) W`), so `det M = e^{−DT/m} < 1`; a multiplier with `|μ| ≥ 1` is real, its real
mode has `y(T) = r y(0)`, and `e^{−λt} y`, `λ = ln |r| / T`, has periodic or antiperiodic boundary
values for an oscillator with more damping and the same stiffness deviation. Hence below the
universal curve every period map is Schur stable, for every pump period, every duty ratio and
every waveform with finitely many (or infinitely many) jumps.

This turns the algebraic comparisons of waves 3 and 4 into theorems: the square-wave (Meissner)
and two-level general-duty oscillators are Floquet stable at every pump frequency in the region
`|ε| / √(1 − |ε|) < 2ξ`, instability at any pump frequency forces `2ξ √(1 − |ε|) ≤ |ε|`
(`UniversalThreshold.meissner_centre_above_universal` compared this with the centre of the
principal tongue only), and in that region the frozen (L3), exact (L1) and averaged (L2) verdicts
of the square wave all agree (`SquareWave.averaged_hurwitz_of_universal` compared L2 with the
universal curve only).

Scope.
* The scalar real equation `m δ̈ + D δ̇ + K(t) δ = 0`, continuous time, constants `m > 0` and `D`,
  an interval-integrable stiffness on `[0, L]` with `|K(t) − K̄| ≤ η < K̄` (absolute form) or
  `|K(t) − K̄| ≤ ε K̄`, `0 ≤ ε < 1` (relative form) on `[0, L]`. Solutions: `δ` and `δ̇` continuous
  on `[0, L]`, right derivatives `δ̇` of `δ` and `δ̈` of `δ̇` on `(0, L)` (written out), the equation
  on `(0, L)`; at the jumps of `K` the acceleration `δ̈` jumps.
* The Floquet statements use the state `(δ, δ̇)` and `ẏ = oscMatrix (D/(2m)) (K(t)/m) y`
  (`theorem/Periodic/TwoStateBoundary.lean`) with right derivatives on `[0, T)`; a period map is a
  real `2 × 2` matrix `M` with `y(T) = M y(0)` along a solution from every initial state (written
  out). Multipliers: the complex spectrum of `M`; `LTI.SchurStable`.
* The two-level instances: `Averaging.periodMap d T B₁ B₂ = e^{(1−d)TB₂} e^{dTB₁}`,
  `B_i = oscMatrix c k_i`, any duty ratio `d ∈ [0, 1]` (`theorem/Averaging/StateSpaceAveraging.lean`),
  and the Meissner monodromy `Meissner.meissnerMonodromy` (`d = 1/2`, `k = ω₀²(1 ± ε)`); unit mass,
  damping `D = 2c`, centre `K̄ = ω₀²` or arbitrary.
* Generic mathematics; no model family.

Source: the energy mechanism of parametric oscillations (Landau–Lifshitz, *Mechanics* §27) and the
period identities of `UniversalThreshold.period_identities`, here for switched solutions; the
two-state Floquet boundary `Periodic.schurStable_iff_abs_trace_lt`, `Periodic.exists_real_eig_of_le`,
`Periodic.exists_real_eigvec`; the switched-system period map of
`theorem/Averaging/StateSpaceAveraging.lean` and the decay `Kapitza.switched_decay_of_schurStable`;
the square-wave models `Meissner.meissnerMonodromy`, `SquareWave.averaged_threshold`.

Results.
* `boundary_identities` — `∫₀ᴸ (D δ̇² + (K − K̄) δ δ̇) = 0` and `∫₀ᴸ (K δ² − m δ̇²) = 0` for a
  right-differentiable solution with `δ(L) = sδ(0)`, `δ̇(L) = sδ̇(0)`, `s² = 1`, integrable `K`.
* `damping_le_of_boundary` — `|K − K̄| ≤ η < K̄` on `[0, L]`: a nonzero such solution forces
  `D √(K̄ − η) ≤ η √m`; `damping_le_of_boundary_rel` — relative form `D ≤ ε √(m K̄) / √(1 − ε)`.
* `det_periodMap_eq` — Liouville for switched solutions: a period map has `det M = e^{−2cT}`.
* `schurStable_of_threshold_piecewise` — `ε / √(1 − ε) < D / √(m K̄)`: every period map of every
  integrable stiffness with `|K − K̄| ≤ εK̄` on `[0, T]` is Schur stable.
* `exists_switched_solution` — the two-level switched system with duty `d` has, from every initial
  state, a solution on `[0, T]` ending at `periodMap d T B₁ B₂ w`.
* `periodMap_schurStable_of_threshold` — two levels `k₁`, `k₂` within `εK̄` of `K̄`,
  `ε / √(1 − ε) < 2c / √K̄`: Schur stable for every period and every duty ratio.
* `meissner_schurStable_of_universal`, `meissner_universal_of_unstable` — the square wave: Schur
  stable for every period when `|ε| / √(1 − |ε|) < 2c/ω₀`; a multiplier outside the unit circle at
  any period forces `2c √(1 − |ε|) ≤ |ε| ω₀`.
* `square_wave_levels_agree_of_universal` — in the universal region: both frozen matrices Hurwitz,
  the exact monodromy Schur stable for every period, every switched trajectory decaying
  exponentially, and the averaged (L2) matrix Hurwitz for `4ω₀√(1 − |ε|) ≤ πω`.
-/

noncomputable section
namespace powerlib.ParametricResonance.PiecewiseThreshold

open Set Function Matrix Filter Topology MeasureTheory
open powerlib.Periodic (oscMatrix)

/-! ## The energy identities for switched solutions -/

section Bound

variable {m D Kbar η L s : ℝ} {K δ δ' δ'' : ℝ → ℝ}

/-- **The boundary identities.** For a solution of `m δ̈ + D δ̇ + K(t) δ = 0` on `[0, L]` with an
integrable stiffness, continuous `δ`, `δ̇`, right derivatives on `(0, L)` and boundary values
`δ(L) = sδ(0)`, `δ̇(L) = sδ̇(0)`, `s² = 1` (periodic or antiperiodic):
`∫₀ᴸ (D δ̇² + (K − K̄) δ δ̇) = 0` and `∫₀ᴸ (K δ² − m δ̇²) = 0`. -/
@[tmio T, powerlib_foundation] theorem boundary_identities (hL : 0 ≤ L)
    (hδc : ContinuousOn δ (Icc 0 L)) (hδ'c : ContinuousOn δ' (Icc 0 L))
    (hδ : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ (δ' t) (Ici t) t)
    (hδ' : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ' (δ'' t) (Ici t) t)
    (hK : IntervalIntegrable K volume 0 L)
    (heq : ∀ t ∈ Ioo 0 L, m * δ'' t + D * δ' t + K t * δ t = 0)
    (hs : s ^ 2 = 1) (hb : δ L = s * δ 0) (hb' : δ' L = s * δ' 0) (Kbar : ℝ) :
    ∫ t in (0 : ℝ)..L, (D * δ' t ^ 2 + (K t - Kbar) * δ t * δ' t) = 0 ∧
      ∫ t in (0 : ℝ)..L, (K t * δ t ^ 2 - m * δ' t ^ 2) = 0 := by
  have hu : uIcc (0 : ℝ) L = Icc 0 L := uIcc_of_le hL
  have hδδ' : ContinuousOn (fun t => δ t * δ' t) (uIcc 0 L) := hu ▸ hδc.mul hδ'c
  have hδ2 : ContinuousOn (fun t => δ t ^ 2) (uIcc 0 L) := hu ▸ hδc.pow 2
  constructor
  · -- `D δ̇² + (K − K̄) δ δ̇ = −(d/dt)(m δ̇²/2 + K̄ δ²/2)` from the right
    have hG : ∀ t ∈ Ioo 0 L, HasDerivWithinAt (fun t => -(m / 2 * δ' t ^ 2 + Kbar / 2 * δ t ^ 2))
        (D * δ' t ^ 2 + (K t - Kbar) * δ t * δ' t) (Ioi t) t := by
      intro t ht
      have h := ((((hδ' t ht).fun_pow 2).const_mul (m / 2)).add
        (((hδ t ht).fun_pow 2).const_mul (Kbar / 2))).neg
      have h' := h.mono (Ioi_subset_Ici_self)
      convert h' using 1
      have := heq t ht
      simp only [Nat.cast_ofNat]
      linear_combination (δ' t) * this
    have hint : IntervalIntegrable (fun t => D * δ' t ^ 2 + (K t - Kbar) * δ t * δ' t) volume 0 L := by
      refine IntervalIntegrable.add ?_ ?_
      · exact ContinuousOn.intervalIntegrable (hu ▸ (hδ'c.pow 2).const_smul D)
      · have h := (hK.sub (intervalIntegrable_const : IntervalIntegrable (fun _ => Kbar) volume 0 L)).mul_continuousOn hδδ'
        exact h.congr fun t _ => by ring
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL (by fun_prop) hG hint]
    simp only [hb, hb', mul_pow, hs, one_mul, sub_self]
  · -- `K δ² − m δ̇² = −(d/dt)(m δ̇ δ + D δ²/2)` from the right
    have hH : ∀ t ∈ Ioo 0 L, HasDerivWithinAt (fun t => -(m * (δ' t * δ t) + D / 2 * δ t ^ 2))
        (K t * δ t ^ 2 - m * δ' t ^ 2) (Ioi t) t := by
      intro t ht
      have h := (((((hδ' t ht).mul (hδ t ht)).const_mul m).add
        (((hδ t ht).fun_pow 2).const_mul (D / 2)))).neg
      have h' := h.mono (Ioi_subset_Ici_self)
      convert h' using 1
      have := heq t ht
      simp only [Nat.cast_ofNat]
      linear_combination (δ t) * this
    have hint : IntervalIntegrable (fun t => K t * δ t ^ 2 - m * δ' t ^ 2) volume 0 L := by
      refine IntervalIntegrable.sub (hK.mul_continuousOn hδ2) ?_
      exact ContinuousOn.intervalIntegrable (hu ▸ (hδ'c.pow 2).const_smul m)
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL (by fun_prop) hH hint]
    rw [hb, hb']
    linear_combination (-(m * (δ' 0 * δ 0)) - D / 2 * δ 0 ^ 2) * hs

/-- The squared core bound for switched solutions with periodic or antiperiodic boundary values:
`D > 0`, `|K − K̄| ≤ η < K̄` on `[0, L]` and a nonzero solution give `D² (K̄ − η) ≤ η² m`. -/
@[tmio T, powerlib_foundation] private theorem sq_damping_le (hm : 0 < m) (hη : 0 ≤ η)
    (hηK : η < Kbar) (hL : 0 < L)
    (hδc : ContinuousOn δ (Icc 0 L)) (hδ'c : ContinuousOn δ' (Icc 0 L))
    (hδ : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ (δ' t) (Ici t) t)
    (hδ' : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ' (δ'' t) (Ici t) t)
    (hK : IntervalIntegrable K volume 0 L)
    (heq : ∀ t ∈ Ioo 0 L, m * δ'' t + D * δ' t + K t * δ t = 0)
    (hs : s ^ 2 = 1) (hb : δ L = s * δ 0) (hb' : δ' L = s * δ' 0)
    (hne : ∃ t ∈ Icc 0 L, δ t ≠ 0) (hdev : ∀ t ∈ Icc 0 L, |K t - Kbar| ≤ η) (hD : 0 < D) :
    D ^ 2 * (Kbar - η) ≤ η ^ 2 * m := by
  have hu : uIcc (0 : ℝ) L = Icc 0 L := uIcc_of_le hL.le
  obtain ⟨h1, h2⟩ := boundary_identities hL.le hδc hδ'c hδ hδ' hK heq hs hb hb' Kbar
  set I0 := ∫ t in (0 : ℝ)..L, δ t ^ 2 with hI0
  set I1 := ∫ t in (0 : ℝ)..L, δ' t ^ 2 with hI1
  have hI0pos : 0 < I0 := by
    obtain ⟨t, ht, hδt⟩ := hne
    exact intervalIntegral.integral_pos hL (hδc.pow 2) (fun x _ => sq_nonneg _)
      ⟨t, ht, by positivity⟩
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 L) → IntervalIntegrable f volume 0 L :=
    fun f hf => ContinuousOn.intervalIntegrable (hu ▸ hf)
  have hKd : IntervalIntegrable (fun t => (K t - Kbar) * δ t * δ' t) volume 0 L := by
    have h := (hK.sub (intervalIntegrable_const : IntervalIntegrable (fun _ => Kbar) volume 0 L))
      |>.mul_continuousOn (hu ▸ hδc.mul hδ'c : ContinuousOn (fun t => δ t * δ' t) (uIcc 0 L))
    exact h.congr fun t _ => by ring
  have hKδ : IntervalIntegrable (fun t => K t * δ t ^ 2) volume 0 L :=
    hK.mul_continuousOn (hu ▸ hδc.pow 2 : ContinuousOn (fun t => δ t ^ 2) (uIcc 0 L))
  -- `D I₁ = −∫ (K − K̄) δ δ̇` and `∫ K δ² = m I₁`
  have hDI : D * I1 = -∫ t in (0 : ℝ)..L, (K t - Kbar) * δ t * δ' t := by
    rw [intervalIntegral.integral_add (hc _ (by fun_prop)) hKd,
      intervalIntegral.integral_const_mul] at h1
    linarith
  have hKI : ∫ t in (0 : ℝ)..L, K t * δ t ^ 2 = m * I1 := by
    rw [intervalIntegral.integral_sub hKδ (hc _ (by fun_prop)),
      intervalIntegral.integral_const_mul] at h2
    linarith
  -- `(K̄ − η) I₀ ≤ m I₁`
  have hlow : (Kbar - η) * I0 ≤ m * I1 := by
    rw [← hKI, hI0, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hL.le (hc _ (by fun_prop)) hKδ fun t ht => ?_
    have := (abs_le.mp (hdev t ht)).1
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hI1pos : 0 < I1 := by
    have : 0 < (Kbar - η) * I0 := mul_pos (by linarith) hI0pos
    nlinarith
  rcases hη.eq_or_lt with hη0 | hηpos
  · -- no modulation: `D I₁ = 0`
    subst hη0
    have hz : ∫ t in (0 : ℝ)..L, (K t - Kbar) * δ t * δ' t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
      · simp
      · rw [uIcc_of_le hL.le] at ht
        have := hdev t ht
        rw [abs_nonpos_iff, sub_eq_zero] at this
        simp only [this, sub_self, zero_mul]
    rw [hz, neg_zero] at hDI
    nlinarith
  · -- AM–GM with the weight `λ = D (K̄ − η) / (η m)`
    set lam := D * (Kbar - η) / (η * m) with hlam
    have hlampos : 0 < lam := by
      have : 0 < Kbar - η := by linarith
      positivity
    have hpt : ∀ t ∈ Icc 0 L, -((K t - Kbar) * δ t * δ' t) ≤
        η / 2 * (lam * δ t ^ 2 + δ' t ^ 2 / lam) := by
      intro t ht
      have hab : -((K t - Kbar) * δ t * δ' t) ≤ η * |δ t * δ' t| := by
        calc -((K t - Kbar) * δ t * δ' t) ≤ |(K t - Kbar) * δ t * δ' t| := neg_le_abs _
          _ = |K t - Kbar| * |δ t * δ' t| := by rw [mul_assoc, abs_mul]
          _ ≤ η * |δ t * δ' t| := mul_le_mul_of_nonneg_right (hdev t ht) (abs_nonneg _)
      have hamgm : 2 * |δ t * δ' t| ≤ lam * δ t ^ 2 + δ' t ^ 2 / lam := by
        rw [abs_mul, ← sq_abs (δ t), ← sq_abs (δ' t)]
        have key : 2 * (|δ t| * |δ' t|) * lam ≤
            (lam * |δ t| ^ 2 + |δ' t| ^ 2 / lam) * lam := by
          rw [add_mul, div_mul_cancel₀ _ hlampos.ne']
          nlinarith [sq_nonneg (lam * |δ t| - |δ' t|)]
        exact le_of_mul_le_mul_right key hlampos
      nlinarith
    have hint_le : -∫ t in (0 : ℝ)..L, (K t - Kbar) * δ t * δ' t ≤
        η / 2 * (lam * I0 + I1 / lam) := by
      rw [← intervalIntegral.integral_neg]
      have := intervalIntegral.integral_mono_on hL.le hKd.neg
        (hc (fun t => η / 2 * (lam * δ t ^ 2 + δ' t ^ 2 / lam)) (by fun_prop)) hpt
      refine this.trans_eq ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hc _ (by fun_prop)) (hc _ (by fun_prop)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div]
    have hmain : D * I1 ≤ η / 2 * (lam * I0 + I1 / lam) := hDI ▸ hint_le
    have hKη : 0 < Kbar - η := by linarith
    have hI0le : I0 ≤ m * I1 / (Kbar - η) := by rw [le_div_iff₀ hKη]; linarith
    have hstep : D * I1 ≤ η / 2 * (lam * (m * I1 / (Kbar - η)) + I1 / lam) := by
      refine hmain.trans ?_
      gcongr
    have hval : η / 2 * (lam * (m * I1 / (Kbar - η)) + I1 / lam) =
        (D / 2 + η ^ 2 * m / (2 * D * (Kbar - η))) * I1 := by
      rw [hlam]
      field_simp
    rw [hval] at hstep
    have hD' : D ≤ D / 2 + η ^ 2 * m / (2 * D * (Kbar - η)) := le_of_mul_le_mul_right hstep hI1pos
    have : D / 2 ≤ η ^ 2 * m / (2 * D * (Kbar - η)) := by linarith
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith

/-- **The universal bound for switched solutions (absolute deviation).** A nonzero solution of
`m δ̈ + D δ̇ + K(t) δ = 0` on `[0, L]` (`m > 0`, `L > 0`, `K` integrable with
`|K − K̄| ≤ η < K̄` on `[0, L]`, `δ` and `δ̇` continuous with right derivatives on `(0, L)`, the
stiffness and the acceleration may jump) with periodic or antiperiodic boundary values
`δ(L) = sδ(0)`, `δ̇(L) = sδ̇(0)`, `s² = 1`, forces `D √(K̄ − η) ≤ η √m`. -/
@[tmio T, powerlib_foundation] theorem damping_le_of_boundary (hm : 0 < m) (hη : 0 ≤ η)
    (hηK : η < Kbar) (hL : 0 < L)
    (hδc : ContinuousOn δ (Icc 0 L)) (hδ'c : ContinuousOn δ' (Icc 0 L))
    (hδ : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ (δ' t) (Ici t) t)
    (hδ' : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ' (δ'' t) (Ici t) t)
    (hK : IntervalIntegrable K volume 0 L)
    (heq : ∀ t ∈ Ioo 0 L, m * δ'' t + D * δ' t + K t * δ t = 0)
    (hs : s ^ 2 = 1) (hb : δ L = s * δ 0) (hb' : δ' L = s * δ' 0)
    (hne : ∃ t ∈ Icc 0 L, δ t ≠ 0) (hdev : ∀ t ∈ Icc 0 L, |K t - Kbar| ≤ η) :
    D * √(Kbar - η) ≤ η * √m := by
  rcases le_or_gt D 0 with hD | hD
  · have h1 : 0 ≤ η * √m := by positivity
    have h2 : D * √(Kbar - η) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD (Real.sqrt_nonneg _)
    linarith
  · have h := sq_damping_le hm hη hηK hL hδc hδ'c hδ hδ' hK heq hs hb hb' hne hdev hD
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hm.le]
    exact h

variable {ε : ℝ}

/-- **The universal threshold for piecewise-continuous stiffness.** For `m > 0`, `K̄ > 0`,
`0 ≤ ε < 1` and an integrable stiffness with `|K(t) − K̄| ≤ εK̄` on `[0, L]` (any number of
jumps), a nonzero switched solution with periodic or antiperiodic boundary values on `[0, L]`
forces `D ≤ ε √(m K̄) / √(1 − ε)`, i.e. `2ξ ≤ ε / √(1 − ε)`, `ξ = D / (2√(m K̄))`. -/
@[tmio T, powerlib_foundation] theorem damping_le_of_boundary_rel (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hL : 0 < L)
    (hδc : ContinuousOn δ (Icc 0 L)) (hδ'c : ContinuousOn δ' (Icc 0 L))
    (hδ : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ (δ' t) (Ici t) t)
    (hδ' : ∀ t ∈ Ioo 0 L, HasDerivWithinAt δ' (δ'' t) (Ici t) t)
    (hK : IntervalIntegrable K volume 0 L)
    (heq : ∀ t ∈ Ioo 0 L, m * δ'' t + D * δ' t + K t * δ t = 0)
    (hs : s ^ 2 = 1) (hb : δ L = s * δ 0) (hb' : δ' L = s * δ' 0)
    (hne : ∃ t ∈ Icc 0 L, δ t ≠ 0) (hdev : ∀ t ∈ Icc 0 L, |K t - Kbar| ≤ ε * Kbar) :
    D ≤ ε * √(m * Kbar) / √(1 - ε) := by
  have h := damping_le_of_boundary hm (mul_nonneg hε hKbar.le) (by nlinarith) hL hδc hδ'c hδ hδ'
    hK heq hs hb hb' hne hdev
  rw [show Kbar - ε * Kbar = Kbar * (1 - ε) by ring, Real.sqrt_mul hKbar.le] at h
  have hs' : 0 < √Kbar := Real.sqrt_pos.mpr hKbar
  have hsq : √Kbar * √Kbar = Kbar := Real.mul_self_sqrt hKbar.le
  rw [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith)), Real.sqrt_mul hm.le]
  refine le_of_mul_le_mul_left ?_ hs'
  calc √Kbar * (D * √(1 - ε)) = D * (√Kbar * √(1 - ε)) := by ring
    _ ≤ ε * Kbar * √m := h
    _ = √Kbar * (ε * (√m * √Kbar)) := by
      rw [show ε * Kbar * √m = ε * (√Kbar * √Kbar) * √m by rw [hsq]]; ring

end Bound

/-! ## Period maps of switched oscillators -/

section Floquet

variable {c T : ℝ} {k : ℝ → ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}

@[tmio T, powerlib_foundation] private theorem components {κ : ℝ} {y : ℝ → Fin 2 → ℝ} {t : ℝ}
    {S : Set ℝ} (h : HasDerivWithinAt y (oscMatrix c κ *ᵥ y t) S t) :
    HasDerivWithinAt (fun t => y t 0) (y t 1) S t ∧
      HasDerivWithinAt (fun t => y t 1) (-κ * y t 0 - 2 * c * y t 1) S t := by
  have h0 := hasDerivWithinAt_pi.1 h 0
  have h1 := hasDerivWithinAt_pi.1 h 1
  refine ⟨h0.congr_deriv ?_, h1.congr_deriv ?_⟩
  · simp [oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- **Liouville's formula for switched solutions.** If every initial state `w` has a solution of
`ẏ = oscMatrix c (k t) y` on `[0, T]` (continuous, right derivatives on `[0, T)`, `k` arbitrary)
with `y(T) = M w`, then `det M = e^{−2cT}`: the Wronskian of two solutions has right derivative
`−2c W` (Mathlib `constant_of_has_deriv_right_zero` for `e^{2ct} W`). -/
@[tmio T, powerlib_foundation] theorem det_periodMap_eq (hT : 0 ≤ T)
    (hsol : ∀ w : Fin 2 → ℝ, ∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, HasDerivWithinAt y (oscMatrix c (k t) *ᵥ y t) (Ici t) t) ∧
      y 0 = w ∧ y T = M *ᵥ w) :
    M.det = Real.exp (-(2 * c) * T) := by
  obtain ⟨y, hyc, hyd, hy0, hyT⟩ := hsol ![1, 0]
  obtain ⟨z, hzc, hzd, hz0, hzT⟩ := hsol ![0, 1]
  set F : ℝ → ℝ := fun t =>
    Real.exp (2 * c * t) * (y t 0 * z t 1 - y t 1 * z t 0) with hF
  have hFc : ContinuousOn F (Icc 0 T) := by
    have h0 : ContinuousOn (fun t => y t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hyc
    have h1 : ContinuousOn (fun t => y t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hyc
    have g0 : ContinuousOn (fun t => z t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hzc
    have g1 : ContinuousOn (fun t => z t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hzc
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((h0.mul g1).sub (h1.mul g0))
  have hFd : ∀ t ∈ Ico 0 T, HasDerivWithinAt F 0 (Ici t) t := by
    intro t ht
    obtain ⟨a0, a1⟩ := components (hyd t ht)
    obtain ⟨b0, b1⟩ := components (hzd t ht)
    have he : HasDerivWithinAt (fun t => Real.exp (2 * c * t))
        (Real.exp (2 * c * t) * (2 * c)) (Ici t) t := by
      have := ((hasDerivAt_id t).const_mul (2 * c)).exp
      simpa using this.hasDerivWithinAt
    have h := he.fun_mul ((a0.fun_mul b1).fun_sub (a1.fun_mul b0))
    convert h using 1
    ring
  have hconst := constant_of_has_deriv_right_zero hFc hFd T ⟨hT, le_rfl⟩
  have hF0 : F 0 = 1 := by simp [hF, hy0, hz0]
  have hFT : F T = Real.exp (2 * c * T) * M.det := by
    simp only [hF, hyT, hzT, Matrix.det_fin_two]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hF0, hFT] at hconst
  have he : Real.exp (-(2 * c) * T) * Real.exp (2 * c * T) = 1 := by
    rw [← Real.exp_add]; simp
  calc M.det = Real.exp (-(2 * c) * T) * (Real.exp (2 * c * T) * M.det) := by
        rw [← mul_assoc, he, one_mul]
    _ = Real.exp (-(2 * c) * T) := by rw [hconst, mul_one]

variable {m D Kbar ε : ℝ} {K : ℝ → ℝ}

/-- **Stable at every pump frequency, for every switched waveform.** Let `m > 0`, `K̄ > 0`,
`0 ≤ ε < 1` and `ε / √(1 − ε) < 2ξ`, `2ξ = D / √(m K̄)`. For every period `T > 0`, every
interval-integrable stiffness with `|K(t) − K̄| ≤ εK̄` on `[0, T]` (any number of jumps) and every
period map `M` of `m δ̈ + D δ̇ + K(t) δ = 0` (state `(δ, δ̇)`, `oscMatrix (D/(2m)) (K/m)`; every
initial state `w` has a right-differentiable solution on `[0, T]` with `y(T) = M w`), every
multiplier lies strictly inside the unit circle.

Proof: `det M = e^{−DT/m} < 1` (`det_periodMap_eq`), so a multiplier with `|μ| ≥ 1` is real,
`μ = r`, with a real eigenvector `w`; along its solution `y(T) = r y(0)`, and
`e^{−λt} y`, `λ = ln |r| / T ≥ 0`, has periodic or antiperiodic boundary values on `[0, T]` for
`m ÿ + (D + 2mλ) ẏ + (K + Dλ + mλ²) y = 0`, whose stiffness deviates from its centre
`K̄ + Dλ + mλ²` by at most `εK̄`; the switched bound contradicts the threshold. -/
@[tmio T, powerlib_foundation] theorem schurStable_of_threshold_piecewise (hm : 0 < m)
    (hKbar : 0 < Kbar) (hε : 0 ≤ ε) (hε1 : ε < 1) (hξ : ε / √(1 - ε) < D / √(m * Kbar))
    (hT : 0 < T) (hK : IntervalIntegrable K volume 0 T)
    (hdev : ∀ t ∈ Icc 0 T, |K t - Kbar| ≤ ε * Kbar)
    (hsol : ∀ w : Fin 2 → ℝ, ∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T,
        HasDerivWithinAt y (oscMatrix (D / (2 * m)) (K t / m) *ᵥ y t) (Ici t) t) ∧
      y 0 = w ∧ y T = M *ᵥ w) :
    LTI.SchurStable M := by
  have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : 0 < √(m * Kbar) := Real.sqrt_pos.mpr (by positivity)
  have hcross : ε * √(m * Kbar) < D * √(1 - ε) := by
    rw [div_lt_div_iff₀ hs1 hs2] at hξ; linarith
  have hD : 0 < D := by
    have : 0 ≤ ε * √(m * Kbar) := by positivity
    by_contra hD; push Not at hD
    nlinarith
  have hdet : M.det < 1 := by
    rw [det_periodMap_eq hT.le hsol, Real.exp_lt_one_iff]
    have : 0 < 2 * (D / (2 * m)) * T := by positivity
    linarith
  rw [Periodic.schurStable_iff_abs_trace_lt hdet]
  by_contra hle
  push Not at hle
  obtain ⟨r, hr, hr1⟩ := Periodic.exists_real_eig_of_le hle
  obtain ⟨w, hw0, hw⟩ := Periodic.exists_real_eigvec hr
  obtain ⟨y, hyc, hyd, hy0, hyT⟩ := hsol w
  rw [hw] at hyT
  have hr0 : r ≠ 0 := by rintro h; rw [h, abs_zero] at hr1; linarith
  have habs : 0 < |r| := abs_pos.mpr hr0
  set lam := Real.log |r| / T with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (Real.log_nonneg hr1) hT.le
  have hexpT : Real.exp (-(lam * T)) = |r|⁻¹ := by
    rw [hlam, div_mul_cancel₀ _ hT.ne', Real.exp_neg, Real.exp_log habs]
  -- the components of the real mode
  set δ : ℝ → ℝ := fun t => y t 0
  set δ' : ℝ → ℝ := fun t => y t 1
  set δ'' : ℝ → ℝ := fun t => -(K t / m) * y t 0 - 2 * (D / (2 * m)) * y t 1
  have hδc : ContinuousOn δ (Icc 0 T) := (continuous_apply 0).comp_continuousOn hyc
  have hδ'c : ContinuousOn δ' (Icc 0 T) := (continuous_apply 1).comp_continuousOn hyc
  have hδ : ∀ t ∈ Ico 0 T, HasDerivWithinAt δ (δ' t) (Ici t) t := fun t ht =>
    (components (hyd t ht)).1
  have hδ' : ∀ t ∈ Ico 0 T, HasDerivWithinAt δ' (δ'' t) (Ici t) t := fun t ht =>
    (components (hyd t ht)).2
  have heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0 := by
    intro t
    simp only [δ, δ', δ'']
    field_simp
    ring
  have hne : ∃ t ∈ Icc 0 T, δ t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hev : δ =ᶠ[𝓝[Ici 0] 0] fun _ => 0 := by
      filter_upwards [Icc_mem_nhdsGE hT] with u hu using hcon u hu
    have h0 : HasDerivWithinAt δ 0 (Ici 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (0 : ℝ)).congr_of_eventuallyEq hev
        (hcon 0 ⟨le_rfl, hT.le⟩)
    have hd0 : δ' 0 = 0 :=
      (uniqueDiffWithinAt_Ici 0).eq_deriv _ (hδ 0 ⟨le_rfl, hT⟩) h0
    apply hw0
    funext i
    fin_cases i
    · have := hcon 0 ⟨le_rfl, hT.le⟩
      simp only [δ, hy0] at this
      simpa using this
    · simp only [δ', hy0] at hd0
      simpa using hd0
  -- remove the envelope `e^{λt}`
  set z : ℝ → ℝ := fun t => Real.exp (-(lam * t)) * δ t
  set z' : ℝ → ℝ := fun t => Real.exp (-(lam * t)) * (δ' t - lam * δ t)
  set z'' : ℝ → ℝ := fun t => Real.exp (-(lam * t)) * (δ'' t - 2 * lam * δ' t + lam ^ 2 * δ t)
  have he : ∀ t, HasDerivAt (fun t => Real.exp (-(lam * t))) (-lam * Real.exp (-(lam * t))) t :=
    fun t => by
      have h0 : HasDerivAt (fun t => -(lam * t)) (-lam) t := by
        convert (hasDerivAt_id t).const_mul (-lam) using 1
        · funext s; simp
        · simp
      convert h0.exp using 1
      ring
  have hec : Continuous fun t => Real.exp (-(lam * t)) := by fun_prop
  have hz : ∀ t ∈ Ioo 0 T, HasDerivWithinAt z (z' t) (Ici t) t := fun t ht => by
    have h := (he t).hasDerivWithinAt.fun_mul (hδ t (Ioo_subset_Ico_self ht))
    convert h using 1
    simp only [z']; ring
  have hz' : ∀ t ∈ Ioo 0 T, HasDerivWithinAt z' (z'' t) (Ici t) t := fun t ht => by
    have h := (he t).hasDerivWithinAt.fun_mul ((hδ' t (Ioo_subset_Ico_self ht)).fun_sub
      ((hδ t (Ioo_subset_Ico_self ht)).const_mul lam))
    convert h using 1
    simp only [z'']; ring
  have hzeq : ∀ t ∈ Ioo 0 T, m * z'' t + (D + 2 * m * lam) * z' t +
      (K t + D * lam + m * lam ^ 2) * z t = 0 := by
    intro t _
    have := heq t
    simp only [z, z', z'']
    linear_combination Real.exp (-(lam * t)) * this
  set sg := r / |r| with hsg
  have hsg2 : sg ^ 2 = 1 := by
    rw [hsg, div_pow, sq_abs, div_self (pow_ne_zero 2 hr0)]
  have hδT : δ T = r * δ 0 := by simp only [δ, hyT, hy0, Pi.smul_apply, smul_eq_mul]
  have hδ'T : δ' T = r * δ' 0 := by simp only [δ', hyT, hy0, Pi.smul_apply, smul_eq_mul]
  have hzb : z T = sg * z 0 := by
    simp only [z, hδT, hexpT, hsg, mul_zero, neg_zero, Real.exp_zero]
    field_simp
  have hz'b : z' T = sg * z' 0 := by
    simp only [z', hδT, hδ'T, hexpT, hsg, mul_zero, neg_zero, Real.exp_zero]
    field_simp
  have hzne : ∃ t ∈ Icc 0 T, z t ≠ 0 := by
    obtain ⟨t, ht, hδt⟩ := hne
    exact ⟨t, ht, mul_ne_zero (Real.exp_pos _).ne' hδt⟩
  -- apply the bound to the shifted oscillator
  have hbound := sq_damping_le (m := m) (D := D + 2 * m * lam)
    (Kbar := Kbar + D * lam + m * lam ^ 2) (η := ε * Kbar) (L := T)
    (K := fun t => K t + D * lam + m * lam ^ 2) hm (mul_nonneg hε hKbar.le)
    (by nlinarith [mul_nonneg hD.le hlam0, mul_nonneg hm.le (sq_nonneg lam)]) hT
    (hec.continuousOn.mul hδc)
    (hec.continuousOn.mul (hδ'c.sub (continuousOn_const.mul hδc))) hz hz'
    ((hK.add (intervalIntegrable_const : IntervalIntegrable (fun _ => D * lam + m * lam ^ 2)
      volume 0 T)).congr fun t _ => by ring) hzeq hsg2 hzb hz'b hzne
    (fun t ht => by
      rw [show K t + D * lam + m * lam ^ 2 - (Kbar + D * lam + m * lam ^ 2) = K t - Kbar by ring]
      exact hdev t ht)
    (by positivity)
  have hsq : ε ^ 2 * (m * Kbar) < D ^ 2 * (1 - ε) := by
    have h := pow_lt_pow_left₀ hcross (by positivity) two_ne_zero
    rwa [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)] at h
  have h1 : D ^ 2 * (Kbar - ε * Kbar) ≤
      (D + 2 * m * lam) ^ 2 * (Kbar + D * lam + m * lam ^ 2 - ε * Kbar) := by
    have hDD : D ^ 2 ≤ (D + 2 * m * lam) ^ 2 := by
      have : D ≤ D + 2 * m * lam := by nlinarith [mul_nonneg hm.le hlam0]
      exact pow_le_pow_left₀ hD.le this 2
    have hKK : Kbar - ε * Kbar ≤ Kbar + D * lam + m * lam ^ 2 - ε * Kbar := by
      nlinarith [mul_nonneg hD.le hlam0, mul_nonneg hm.le (sq_nonneg lam)]
    exact mul_le_mul hDD hKK (by nlinarith) (sq_nonneg _)
  have h3 : (ε * Kbar) ^ 2 * m < D ^ 2 * (Kbar - ε * Kbar) := by
    have := mul_lt_mul_of_pos_right hsq hKbar
    calc (ε * Kbar) ^ 2 * m = ε ^ 2 * (m * Kbar) * Kbar := by ring
      _ < D ^ 2 * (1 - ε) * Kbar := this
      _ = D ^ 2 * (Kbar - ε * Kbar) := by ring
  linarith

end Floquet

/-! ## Two-level stiffness: every duty ratio, the square wave -/

section TwoLevel

open scoped Matrix.Norms.Operator
open powerlib.SpecialFunctions.PeriodicWaves (squareWave)

/-- **The two-level switched system has a period map.** For a duty ratio `d ∈ [0, 1]`, a period
`T > 0` and any square matrices `A₁`, `A₂`, every initial state `w` has a solution on `[0, T]`,
continuous, with right derivative `A₁ y` before `dT` and `A₂ y` from `dT` on, ending at
`y(T) = e^{(1−d)TA₂} e^{dTA₁} w = periodMap d T A₁ A₂ w`
(`Averaging.exists_switched_trajectory`, `Averaging.switched_sample`). -/
@[tmio T, powerlib_foundation] theorem exists_switched_solution {X : Type*} [Fintype X]
    [DecidableEq X] {d T : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hT : 0 < T) (A₁ A₂ : Matrix X X ℝ)
    (w : X → ℝ) :
    ∃ y : ℝ → X → ℝ, ContinuousOn y (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, HasDerivWithinAt y ((if t < d * T then A₁ else A₂) *ᵥ y t) (Ici t) t) ∧
      y 0 = w ∧ y T = Averaging.periodMap d T A₁ A₂ *ᵥ w := by
  obtain ⟨x, hx0, hx⟩ := Averaging.exists_switched_trajectory hd0 hd1 A₁ A₂ hT w
  obtain ⟨h1, h2⟩ := hx 0
  simp only [Nat.cast_zero, zero_mul, zero_add, one_mul] at h1 h2
  have hdT : d * T ≤ T := by nlinarith
  have hdT0 : 0 ≤ d * T := by positivity
  refine ⟨x, ?_, ?_, hx0, ?_⟩
  · have c1 : ContinuousOn x (Icc 0 (d * T)) := fun t ht => (h1 t ht).continuousWithinAt
    have c2 : ContinuousOn x (Icc (d * T) T) := fun t ht => (h2 t ht).continuousWithinAt
    have := c1.union_of_isClosed c2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hdT0 hdT] at this
  · intro t ht
    split_ifs with h
    · exact (h1 t ⟨ht.1, h.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ⟨ht.1, h⟩)
    · push Not at h
      exact (h2 t ⟨h, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ⟨h, ht.2⟩)
  · have := Averaging.switched_sample hd0 hd1 hT.le hx 1
    simpa [hx0] using this

@[tmio T, powerlib_foundation] private theorem intervalIntegrable_two_level (a k₁ k₂ u v : ℝ) :
    IntervalIntegrable (fun t => if t < a then k₁ else k₂) volume u v := by
  rcases le_total k₁ k₂ with h | h
  · refine Monotone.intervalIntegrable fun s t hst => ?_
    by_cases ht : t < a
    · simp [ht, hst.trans_lt ht]
    · by_cases hs : s < a <;> simp [ht, hs, h]
  · refine Antitone.intervalIntegrable fun s t hst => ?_
    by_cases ht : t < a
    · simp [ht, hst.trans_lt ht]
    · by_cases hs : s < a <;> simp [ht, hs, h]

variable {c Kbar ε k₁ k₂ d T : ℝ}

/-- **Two-level stiffness, every duty ratio.** For `ẍ + 2cẋ + k(t)x = 0` with `k = k₁` on the
first fraction `d ∈ [0, 1]` of every period `T > 0` and `k = k₂` on the rest, both levels within
`εK̄` of `K̄ > 0` (`0 ≤ ε < 1`), and the universal threshold `ε / √(1 − ε) < 2c / √K̄` (`2ξ`):
the period map `Averaging.periodMap d T (oscMatrix c k₁) (oscMatrix c k₂)` is Schur stable. -/
@[tmio T, powerlib_foundation] theorem periodMap_schurStable_of_threshold (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hξ : ε / √(1 - ε) < 2 * c / √Kbar)
    (hk₁ : |k₁ - Kbar| ≤ ε * Kbar) (hk₂ : |k₂ - Kbar| ≤ ε * Kbar) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hT : 0 < T) :
    LTI.SchurStable (Averaging.periodMap d T (oscMatrix c k₁) (oscMatrix c k₂)) := by
  refine schurStable_of_threshold_piecewise (m := 1) (D := 2 * c)
    (K := fun t => if t < d * T then k₁ else k₂) one_pos hKbar hε hε1 (by rwa [one_mul]) hT
    (intervalIntegrable_two_level _ _ _ _ _) (fun t _ => by split_ifs <;> assumption)
    (fun w => ?_)
  obtain ⟨y, hyc, hyd, hy0, hyT⟩ := exists_switched_solution hd0 hd1 hT (oscMatrix c k₁)
    (oscMatrix c k₂) w
  refine ⟨y, hyc, fun t ht => ?_, hy0, hyT⟩
  have e : oscMatrix (2 * c / (2 * 1)) ((if t < d * T then k₁ else k₂) / 1) =
      if t < d * T then oscMatrix c k₁ else oscMatrix c k₂ := by
    rw [show 2 * c / (2 * 1) = c by ring, div_one]
    split_ifs <;> rfl
  rw [e]
  exact hyd t ht

variable {ω₀ : ℝ}

/-- **The square wave below the universal curve.** The Meissner oscillator
`ẍ + 2cẋ + ω₀²(1 ± ε)x = 0` (`ω₀ > 0`, `|ε| < 1`) with `|ε| / √(1 − |ε|) < 2c/ω₀` (`= 2ξ`) has a
Schur-stable monodromy for every period `T > 0`, i.e. at every pump frequency, in every tongue. -/
@[tmio T, powerlib_foundation] theorem meissner_schurStable_of_universal (hω : 0 < ω₀)
    (hε1 : |ε| < 1) (hξ : |ε| / √(1 - |ε|) < 2 * c / ω₀) (hT : 0 < T) :
    LTI.SchurStable (Meissner.meissnerMonodromy c ω₀ ε T) := by
  have hdev : ∀ σ : ℝ, |σ| = |ε| → |ω₀ ^ 2 * (1 + σ) - ω₀ ^ 2| ≤ |ε| * ω₀ ^ 2 := fun σ hσ => by
    rw [show ω₀ ^ 2 * (1 + σ) - ω₀ ^ 2 = ω₀ ^ 2 * σ by ring, abs_mul, abs_of_pos (by positivity), hσ,
      mul_comm]
  have h := periodMap_schurStable_of_threshold (c := c) (d := 1 / 2) (T := T)
    (k₁ := ω₀ ^ 2 * (1 + ε)) (k₂ := ω₀ ^ 2 * (1 - ε)) (by positivity : 0 < ω₀ ^ 2)
    (abs_nonneg ε) hε1 (by rwa [Real.sqrt_sq hω.le]) (hdev ε rfl)
    (by rw [show ω₀ ^ 2 * (1 - ε) = ω₀ ^ 2 * (1 + -ε) by ring]; exact hdev (-ε) (abs_neg ε))
    (by norm_num) (by norm_num) hT
  exact h

/-- **Instability at any pump frequency needs the universal depth.** If the Meissner monodromy has
a multiplier outside the unit circle at some period `T > 0` (any tongue, any detuning), then
`2c √(1 − |ε|) ≤ |ε| ω₀`, i.e. `2ξ ≤ |ε| / √(1 − |ε|)`: the exact square-wave boundary lies above
the universal curve everywhere, not only at the centre of the principal tongue
(`UniversalThreshold.meissner_centre_above_universal`). -/
@[tmio T, powerlib_foundation] theorem meissner_universal_of_unstable (hω : 0 < ω₀)
    (hε1 : |ε| < 1) (hT : 0 < T)
    (hu : ∃ μ ∈ spectrum ℂ ((Meissner.meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)),
      1 < ‖μ‖) :
    2 * c * √(1 - |ε|) ≤ |ε| * ω₀ := by
  by_contra hlt
  push Not at hlt
  have hr : 0 < √(1 - |ε|) := Real.sqrt_pos.mpr (by linarith)
  have hξ : |ε| / √(1 - |ε|) < 2 * c / ω₀ := by
    rw [div_lt_div_iff₀ hr hω]; linarith
  obtain ⟨μ, hμ, hμ1⟩ := hu
  obtain ⟨v, hv, hMv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
  have := meissner_schurStable_of_universal hω hε1 hξ hT μ v hv hMv
  linarith

open SquareWave in
/-- **All levels agree for the square wave in the universal region.** For the Meissner oscillator
with `ω₀ > 0`, `|ε| < 1` and `|ε| / √(1 − |ε|) < 2c/ω₀`:
* L3: both frozen matrices `oscMatrix c (ω₀²(1 ± ε))` are Hurwitz;
* L1: for every period `T > 0` the exact monodromy is Schur stable and every switched trajectory
  decays, `‖x(t)‖ ≤ C e^{−αt} ‖x(0)‖` (`Kapitza.switched_decay_of_schurStable`);
* L2: at every pump frequency `ω` with `4ω₀√(1 − |ε|) ≤ πω` (in particular near `2ω₀`) the
  averaged matrix is Hurwitz (`SquareWave.averaged_hurwitz_of_universal`).
The universal stability margin is now a theorem at every level for the discontinuous square wave;
`SquareWave.averaged_hurwitz_of_universal` alone compared L2 with the curve. -/
@[tmio T, powerlib_foundation] theorem square_wave_levels_agree_of_universal (hω : 0 < ω₀)
    (hε1 : |ε| < 1) (hξ : |ε| / √(1 - |ε|) < 2 * c / ω₀) :
    LinearSystems.IsHurwitz (oscMatrix c (ω₀ ^ 2 * (1 + ε))) ∧
      LinearSystems.IsHurwitz (oscMatrix c (ω₀ ^ 2 * (1 - ε))) ∧
      (∀ T : ℝ, 0 < T → LTI.SchurStable (Meissner.meissnerMonodromy c ω₀ ε T) ∧
        ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ x : ℝ → Fin 2 → ℝ,
          (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => oscMatrix c (ω₀ ^ 2 * (1 + ε)) *ᵥ y)
              (Icc (k * T) (k * T + 1 / 2 * T)) ∧
            IsIntegralCurveOn x (fun _ y => oscMatrix c (ω₀ ^ 2 * (1 - ε)) *ᵥ y)
              (Icc (k * T + 1 / 2 * T) ((k + 1) * T))) →
          ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖) ∧
      ∀ ω T : ℝ, 0 < ω → T = 2 * Real.pi / ω → 4 * ω₀ * √(1 - |ε|) ≤ Real.pi * ω →
        LinearSystems.IsHurwitz (averagedMatrix c ω₀ ω T (squareWave ε T)) := by
  have hc : 0 < c := by
    have h0 : 0 ≤ |ε| / √(1 - |ε|) := by positivity
    have := h0.trans_lt hξ
    have h2 : 0 < 2 * c := (div_pos_iff_of_pos_right hω).mp this
    linarith
  have hfrozen : ∀ σ : ℝ, |σ| < 1 → LinearSystems.IsHurwitz (oscMatrix c (ω₀ ^ 2 * (1 + σ))) := by
    intro σ hσ
    rw [Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix, Periodic.det_oscMatrix]
    have := (abs_lt.mp hσ).1
    exact ⟨by linarith, by have : 0 < 1 + σ := by linarith
                           positivity⟩
  refine ⟨hfrozen ε hε1, ?_, fun T hT => ?_, fun ω T hω' hT hΩ => ?_⟩
  · rw [show ω₀ ^ 2 * (1 - ε) = ω₀ ^ 2 * (1 + -ε) by ring]
    exact hfrozen (-ε) (by rwa [abs_neg])
  · have hS := meissner_schurStable_of_universal hω hε1 hξ hT
    have hS' : LTI.SchurStable (Averaging.periodMap (1 / 2) T (oscMatrix c (ω₀ ^ 2 * (1 + ε)))
        (oscMatrix c (ω₀ ^ 2 * (1 - ε)))) := hS
    exact ⟨hS, Kapitza.switched_decay_of_schurStable (d := 1 / 2) (by norm_num) (by norm_num) hT
      _ _ hS'⟩
  · exact averaged_hurwitz_of_universal hω' hT hω hc hε1 hξ hΩ

end TwoLevel

end powerlib.ParametricResonance.PiecewiseThreshold
