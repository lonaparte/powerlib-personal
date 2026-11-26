import theorem.Periodic.MeanTrace
import theorem.ParametricResonance.Wirtinger
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A frequency- and waveform-free threshold for parametric instability

For `m δ̈ + D δ̇ + K(t) δ = 0` with a stiffness that stays within `ε K̄` of a centre `K̄ > 0`
(`0 ≤ ε < 1`), a sustained oscillation — a nonzero periodic solution of any period, in particular
the harmonic (multiplier `+1`) and half-frequency (multiplier `−1`, antiperiodic) responses on the
boundaries of every instability tongue — requires `2ξ ≤ ε / √(1 − ε)` with
`ξ = D / (2 √(m K̄))`, whatever the pump frequency and the waveform of `K`. Multiplying the
equation by `δ̇` and by `δ` and integrating over a period gives `D ∫ δ̇² = −∫ (K − K̄) δ δ̇` and
`∫ K δ² = m ∫ δ̇²`; with `|K − K̄| ≤ εK̄`, `K ≥ (1 − ε)K̄` and `2|δ δ̇| ≤ λδ² + δ̇²/λ` the bound
follows. No derivative and no periodicity of `K` is used, unlike the pump-work bound of
`theorem/ParametricResonance/Wirtinger.lean`.

The bound decides Floquet stability without any continuation in the modulation depth: a real
multiplier `r` with `|r| ≥ 1` has a mode `δ(t + T) = r δ(t)`, and `y = e^{−λt} δ`,
`λ = ln |r| / T ≥ 0`, is a nonzero `2T`-periodic solution of
`m ÿ + (D + 2mλ) ẏ + (K + Dλ + mλ²) y = 0`, an oscillator with more damping, a larger centre
stiffness and the same deviation `εK̄`, for which the threshold is violated a fortiori; complex
multipliers have `|μ|² = det M = e^{−DT/m} < 1`. Hence below the threshold every multiplier lies
strictly inside the unit circle, for every pump period and every waveform: in the region
`ξ > 0`, `ε / √(1 − ε) < 2ξ` the frozen small-signal analysis and the Floquet analysis agree.

Scope.
* The scalar real equation `m δ̈ + D δ̇ + K(t) δ = 0`, continuous time, constants `m > 0` and `D`,
  a continuous stiffness with `|K(t) − K̄| ≤ η < K̄` (absolute form) or `|K(t) − K̄| ≤ ε K̄`,
  `0 ≤ ε < 1` (relative form), solutions twice differentiable on `ℝ` (derivatives `δ'`, `δ''`
  written out). The bound on periodic solutions needs only the periodicity of `δ` (period
  `L > 0`), not that of `K`.
* The Floquet statements use the state `(δ, δ̇)` and `ẋ = oscMatrix (D/(2m)) (K(t)/m) x`
  (`theorem/Periodic/TwoStateBoundary.lean`), a continuous `T`-periodic `K`, `T > 0`, the
  monodromy matrix `monodromy _ T 0` and `LTI.SchurStable` (every multiplier inside the unit
  circle). The frozen small-signal matrices are `oscMatrix (D/(2m)) (K(t)/m)` at fixed `t`.
* Comparisons: the sinusoidal modulation `K = K̄ (1 + ε cos Ωt)` of
  `Wirtinger.pump_amplitude_cos`, and the square-wave Meissner oscillator of
  `theorem/ParametricResonance/Meissner.lean` at the centre of its principal tongue. The square
  wave is discontinuous, so the bound itself does not cover it; `meissner_centre_above_universal`
  compares the two thresholds algebraically.
* Generic mathematics; no model family.

Source: the energy mechanism of parametric oscillations (Landau–Lifshitz, *Mechanics* §27: the
pump work of the varying parameter must balance the dissipation) and the period identities of the
damped Hill equation obtained with the multipliers `δ̇` and `δ`; the two-state Floquet boundary
`Periodic.damped_boundary` and the real Floquet modes `Periodic.real_mode_add_period` of
`theorem/Periodic/MeanTrace.lean`; the necessary bounds `Wirtinger.pump_amplitude_cos` and
`Meissner.centre_threshold_lower` compared here.

Sharpenings.
* The Wirtinger bound `|ε| ≥ DΩ/(2K̄)` needs a sinusoidal (differentiable) modulation and a
  half-frequency solution; the universal bound needs neither, holds for the periodic (`+1`)
  responses too and, unlike either necessary bound, gives a sufficient stability condition for
  every pump frequency. Where both apply, the Wirtinger bound is the sharper one exactly when
  `Ω ≥ 2ω₀ √(1 − ε)`, `ω₀ = √(K̄/m)` (`wirtinger_le_universal_iff`), so near the principal
  resonance `Ω = 2ω₀`; for slower pumps the universal bound is sharper. At small `ε` the
  universal threshold reads `ε ≳ 2ξ`, half of the first-order Mathieu threshold `ε ≈ 4ξ` of the
  principal tongue: it is a guaranteed stability margin, not the tongue boundary.

Results.
* `period_identities` — `∫₀ᴸ (D δ̇² + (K − K̄) δ δ̇) = 0` and `∫₀ᴸ (K δ² − m δ̇²) = 0` for an
  `L`-periodic solution.
* `damping_le_of_abs_le` — `|K − K̄| ≤ η < K̄`: a nonzero periodic solution forces
  `D √(K̄ − η) ≤ η √m`.
* `damping_le_of_periodic`, `damping_le_of_antiperiodic` — `|K − K̄| ≤ εK̄`: a nonzero periodic or
  antiperiodic solution forces `D ≤ ε √(m K̄) / √(1 − ε)`, i.e. `2ξ ≤ ε / √(1 − ε)`.
* `schurStable_of_threshold` — `ε / √(1 − ε) < D / √(m K̄)` (`= 2ξ`): Schur-stable monodromy for
  every period `T > 0` and every continuous `T`-periodic `K` with `|K − K̄| ≤ εK̄`;
  `schurStable_of_threshold_waveform` — the same for `K = K̄ (1 + s p(t))`, every waveform
  `|p| ≤ 1`, every period and every depth `|s| ≤ ε`.
* `levels_agree_of_threshold` — in that region the frozen matrices are Hurwitz at every instant,
  the multipliers lie inside the unit circle, and `‖Φ(t, s)‖ ≤ C e^{−β(t − s)}`.
* `sinusoidal_necessary` — for `K = K̄ (1 + ε cos Ωt)` a nonzero half-frequency solution satisfies
  both `DΩ/(2K̄) ≤ |ε|` and `D ≤ |ε| √(m K̄) / √(1 − |ε|)`.
* `wirtinger_le_universal_iff` — `2K̄ε/Ω ≤ ε √(m K̄)/√(1 − ε)` iff `2 √(K̄/m) √(1 − ε) ≤ Ω`.
* `meissner_centre_above_universal` — at the centre of the principal Meissner tongue
  (`Ω = ν₁ + ν₂`) instability requires `π c √(ν₁ν₂) < ε ω₀²`, and for `2c² ≤ ω₀²(1 − ε)` this
  exact threshold dominates the universal one: `2 c ω₀ √(1 − ε) ≤ π c √(ν₁ν₂)`.
-/

noncomputable section
namespace powerlib.ParametricResonance.UniversalThreshold

open Set Function Matrix
open powerlib.Periodic
open scoped Matrix.Norms.Operator

/-! ## The bound for periodic solutions -/

section Bound

variable {m D Kbar η L : ℝ} {K δ δ' δ'' : ℝ → ℝ}

/-- The two period identities of `m δ̈ + D δ̇ + K(t) δ = 0` for an `L`-periodic solution, without
any derivative or periodicity of `K`: multiplying by `δ̇`,
`∫₀ᴸ (D δ̇² + (K − K̄) δ δ̇) = 0`; multiplying by `δ`, `∫₀ᴸ (K δ² − m δ̇²) = 0`. -/
@[tmio T, powerlib_foundation] theorem period_identities (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : Continuous K)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0) (hper : Periodic δ L) (Kbar : ℝ) :
    ∫ t in (0 : ℝ)..L, (D * δ' t ^ 2 + (K t - Kbar) * δ t * δ' t) = 0 ∧
      ∫ t in (0 : ℝ)..L, (K t * δ t ^ 2 - m * δ' t ^ 2) = 0 := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hδ'c : Continuous δ' := continuous_iff_continuousAt.2 fun t => (hδ' t).continuousAt
  have hper' : Periodic δ' L := EnergyBalance.periodic_of_hasDerivAt hδ hper
  constructor
  · -- `D δ̇² + (K − K̄) δ δ̇ = −(d/dt)(m δ̇²/2 + K̄ δ²/2)`
    have hG : ∀ t, HasDerivAt (fun t => -(m / 2 * δ' t ^ 2 + Kbar / 2 * δ t ^ 2))
        (D * δ' t ^ 2 + (K t - Kbar) * δ t * δ' t) t := by
      intro t
      have h := ((((hδ' t).pow 2).const_mul (m / 2)).add (((hδ t).pow 2).const_mul (Kbar / 2))).neg
      convert h using 1
      have := heq t
      simp only [Nat.cast_ofNat]
      linear_combination (δ' t) * this
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG t)
      ((by fun_prop : Continuous fun t =>
        D * δ' t ^ 2 + (K t - Kbar) * δ t * δ' t).intervalIntegrable _ _)]
    have h0 := hper 0
    have h0' := hper' 0
    rw [zero_add] at h0 h0'
    simp only [h0, h0', sub_self]
  · -- `K δ² − m δ̇² = −(d/dt)(m δ̇ δ + D δ²/2)`
    have hH : ∀ t, HasDerivAt (fun t => -(m * (δ' t * δ t) + D / 2 * δ t ^ 2))
        (K t * δ t ^ 2 - m * δ' t ^ 2) t := by
      intro t
      have h := ((((hδ' t).mul (hδ t)).const_mul m).add (((hδ t).pow 2).const_mul (D / 2))).neg
      convert h using 1
      have := heq t
      simp only [Nat.cast_ofNat]
      linear_combination (δ t) * this
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hH t)
      ((by fun_prop : Continuous fun t => K t * δ t ^ 2 - m * δ' t ^ 2).intervalIntegrable _ _)]
    have h0 := hper 0
    have h0' := hper' 0
    rw [zero_add] at h0 h0'
    simp only [h0, h0', sub_self]

/-- The squared core bound: a nonzero `L`-periodic solution with `|K − K̄| ≤ η < K̄` and `D > 0`
has `D² (K̄ − η) ≤ η² m`. -/
@[tmio T, powerlib_foundation] private theorem sq_damping_le (hm : 0 < m) (hη : 0 ≤ η)
    (hηK : η < Kbar) (hL : 0 < L) (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : Continuous K)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0) (hper : Periodic δ L)
    (hne : ∃ t, δ t ≠ 0) (hdev : ∀ t, |K t - Kbar| ≤ η) (hD : 0 < D) :
    D ^ 2 * (Kbar - η) ≤ η ^ 2 * m := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hδ'c : Continuous δ' := continuous_iff_continuousAt.2 fun t => (hδ' t).continuousAt
  obtain ⟨h1, h2⟩ := period_identities hδ hδ' hK heq hper Kbar
  set I0 := ∫ t in (0 : ℝ)..L, δ t ^ 2 with hI0
  set I1 := ∫ t in (0 : ℝ)..L, δ' t ^ 2 with hI1
  have hI0pos : 0 < I0 := Wirtinger.integral_sq_pos_of_ne_zero hL hδc hper hne
  have hint : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f MeasureTheory.volume 0 L :=
    fun f hf => hf.intervalIntegrable _ _
  -- `D I₁ = −∫ (K − K̄) δ δ̇` and `∫ K δ² = m I₁`
  have hDI : D * I1 = -∫ t in (0 : ℝ)..L, (K t - Kbar) * δ t * δ' t := by
    rw [intervalIntegral.integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
      intervalIntegral.integral_const_mul] at h1
    linarith
  have hKI : ∫ t in (0 : ℝ)..L, K t * δ t ^ 2 = m * I1 := by
    rw [intervalIntegral.integral_sub (hint _ (by fun_prop)) (hint _ (by fun_prop)),
      intervalIntegral.integral_const_mul] at h2
    linarith
  -- `(K̄ − η) I₀ ≤ m I₁`
  have hlow : (Kbar - η) * I0 ≤ m * I1 := by
    rw [← hKI, hI0, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hL.le (hint _ (by fun_prop)) (hint _ (by fun_prop))
      fun t _ => ?_
    have := (abs_le.mp (hdev t)).1
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hI1pos : 0 < I1 := by
    have : 0 < (Kbar - η) * I0 := mul_pos (by linarith) hI0pos
    nlinarith
  rcases hη.eq_or_lt with hη0 | hηpos
  · -- no modulation: `D I₁ = 0`
    subst hη0
    have hz : ∫ t in (0 : ℝ)..L, (K t - Kbar) * δ t * δ' t = 0 := by
      have : ∀ t, (K t - Kbar) * δ t * δ' t = 0 := fun t => by
        have := hdev t
        rw [abs_nonpos_iff, sub_eq_zero] at this
        rw [this, sub_self, zero_mul, zero_mul]
      simp [this]
    rw [hz, neg_zero] at hDI
    nlinarith
  · -- AM–GM with the weight `λ = D (K̄ − η) / (η m)`
    set lam := D * (Kbar - η) / (η * m) with hlam
    have hlampos : 0 < lam := by
      have : 0 < Kbar - η := by linarith
      positivity
    have hpt : ∀ t, -((K t - Kbar) * δ t * δ' t) ≤
        η / 2 * (lam * δ t ^ 2 + δ' t ^ 2 / lam) := by
      intro t
      have hab : -((K t - Kbar) * δ t * δ' t) ≤ η * |δ t * δ' t| := by
        calc -((K t - Kbar) * δ t * δ' t) ≤ |(K t - Kbar) * δ t * δ' t| := neg_le_abs _
          _ = |K t - Kbar| * |δ t * δ' t| := by rw [mul_assoc, abs_mul]
          _ ≤ η * |δ t * δ' t| := mul_le_mul_of_nonneg_right (hdev t) (abs_nonneg _)
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
      have := intervalIntegral.integral_mono_on hL.le (hint _ (by fun_prop))
        (hint (fun t => η / 2 * (lam * δ t ^ 2 + δ' t ^ 2 / lam)) (by fun_prop))
        (fun t _ => hpt t)
      refine this.trans_eq ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hint _ (by fun_prop)) (hint _ (by fun_prop)), intervalIntegral.integral_const_mul,
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

/-- **The frequency- and waveform-free bound (absolute deviation).** A nonzero `L`-periodic
solution of `m δ̈ + D δ̇ + K(t) δ = 0` (`m > 0`, `K` continuous, `|K(t) − K̄| ≤ η < K̄`; no
derivative and no periodicity of `K` is needed) forces `D √(K̄ − η) ≤ η √m`. -/
@[tmio T, powerlib_foundation] theorem damping_le_of_abs_le (hm : 0 < m) (hη : 0 ≤ η)
    (hηK : η < Kbar) (hL : 0 < L) (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : Continuous K)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0) (hper : Periodic δ L)
    (hne : ∃ t, δ t ≠ 0) (hdev : ∀ t, |K t - Kbar| ≤ η) :
    D * √(Kbar - η) ≤ η * √m := by
  rcases le_or_gt D 0 with hD | hD
  · have h1 : 0 ≤ η * √m := by positivity
    have h2 : D * √(Kbar - η) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD (Real.sqrt_nonneg _)
    linarith
  · have h := sq_damping_le hm hη hηK hL hδ hδ' hK heq hper hne hdev hD
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hm.le]
    exact h

variable {ε : ℝ}

/-- **The universal threshold.** For `m > 0`, `K̄ > 0`, `0 ≤ ε < 1` and a continuous stiffness
with `|K(t) − K̄| ≤ ε K̄`, a nonzero `L`-periodic solution of `m δ̈ + D δ̇ + K(t) δ = 0` (any
period `L > 0`, any waveform of `K`) forces `D ≤ ε √(m K̄) / √(1 − ε)`, i.e.
`2ξ ≤ ε / √(1 − ε)` with `ξ = D / (2 √(m K̄))`. -/
@[tmio T, powerlib_foundation] theorem damping_le_of_periodic (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hL : 0 < L) (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : Continuous K)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0) (hper : Periodic δ L)
    (hne : ∃ t, δ t ≠ 0) (hdev : ∀ t, |K t - Kbar| ≤ ε * Kbar) :
    D ≤ ε * √(m * Kbar) / √(1 - ε) := by
  have h := damping_le_of_abs_le hm (mul_nonneg hε hKbar.le) (by nlinarith) hL hδ hδ' hK heq
    hper hne hdev
  rw [show Kbar - ε * Kbar = Kbar * (1 - ε) by ring, Real.sqrt_mul hKbar.le] at h
  have hs : 0 < √Kbar := Real.sqrt_pos.mpr hKbar
  have hsq : √Kbar * √Kbar = Kbar := Real.mul_self_sqrt hKbar.le
  rw [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith)), Real.sqrt_mul hm.le]
  refine le_of_mul_le_mul_left ?_ hs
  calc √Kbar * (D * √(1 - ε)) = D * (√Kbar * √(1 - ε)) := by ring
    _ ≤ ε * Kbar * √m := h
    _ = √Kbar * (ε * (√m * √Kbar)) := by
      rw [show ε * Kbar * √m = ε * (√Kbar * √Kbar) * √m by rw [hsq]]; ring

/-- Antiperiodic solutions (multiplier `−1`, sustained oscillation at half the pump frequency)
are `2L`-periodic and obey the same bound `D ≤ ε √(m K̄) / √(1 − ε)`. -/
@[tmio T, powerlib_foundation] theorem damping_le_of_antiperiodic (hm : 0 < m)
    (hKbar : 0 < Kbar) (hε : 0 ≤ ε) (hε1 : ε < 1) (hL : 0 < L) (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : Continuous K)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0) (hanti : Antiperiodic δ L)
    (hne : ∃ t, δ t ≠ 0) (hdev : ∀ t, |K t - Kbar| ≤ ε * Kbar) :
    D ≤ ε * √(m * Kbar) / √(1 - ε) :=
  damping_le_of_periodic hm hKbar hε hε1 (by positivity) hδ hδ' hK heq hanti.periodic_two_mul
    hne hdev

end Bound

/-! ## The stability region for every pump frequency and waveform -/

section Region

variable {m D Kbar ε T : ℝ} {K : ℝ → ℝ}

/-- **Stable at every pump frequency and for every waveform.** Let `m > 0`, `K̄ > 0`,
`0 ≤ ε < 1` and `ε / √(1 − ε) < 2ξ`, `2ξ = D / √(m K̄)`. For every period `T > 0` and every
continuous `T`-periodic stiffness with `|K(t) − K̄| ≤ ε K̄`, every Floquet multiplier of
`m δ̈ + D δ̇ + K(t) δ = 0` (state `(δ, δ̇)`, `oscMatrix (D/(2m)) (K/m)`) lies strictly inside the
unit circle.

Proof: `det M = e^{−DT/m} < 1`, so a multiplier with `|μ| ≥ 1` is real, `μ = r`
(`Periodic.damped_boundary`); its real mode `δ` has `δ(t + T) = r δ(t)` on the whole line
(`Periodic.real_mode_add_period`), and `y = e^{−λt} δ`, `λ = ln |r| / T ≥ 0`, is a nonzero
`2T`-periodic solution of `m ÿ + (D + 2mλ) ẏ + (K + Dλ + mλ²) y = 0`, whose stiffness deviates from
its centre `K̄ + Dλ + mλ²` by at most `εK̄`; the bound `damping_le_of_abs_le` then contradicts the
threshold. No continuation in the modulation depth is needed. -/
@[tmio T, powerlib_foundation] theorem schurStable_of_threshold (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hξ : ε / √(1 - ε) < D / √(m * Kbar)) (hT : 0 < T)
    (hK : Continuous K) (hKP : Periodic K T) (hdev : ∀ t, |K t - Kbar| ≤ ε * Kbar) :
    LTI.SchurStable (monodromy (fun t => oscMatrix (D / (2 * m)) (K t / m)) T 0) := by
  set A : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => oscMatrix (D / (2 * m)) (K t / m) with hAdef
  have hA : Continuous A := by
    simp only [hAdef, oscMatrix]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hP : Periodic A T := fun t => by simp only [hAdef, hKP t]
  have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : 0 < √(m * Kbar) := Real.sqrt_pos.mpr (by positivity)
  have hcross : ε * √(m * Kbar) < D * √(1 - ε) := by
    rw [div_lt_div_iff₀ hs1 hs2] at hξ; linarith
  have hD : 0 < D := by
    have : 0 ≤ ε * √(m * Kbar) := by positivity
    by_contra hD; push Not at hD
    nlinarith
  have hsq : ε ^ 2 * (m * Kbar) < D ^ 2 * (1 - ε) := by
    have h := pow_lt_pow_left₀ hcross (by positivity) two_ne_zero
    rwa [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)] at h
  have hc : 0 < D / (2 * m) := by positivity
  obtain ⟨-, hreal, -, -⟩ := damped_boundary (c := D / (2 * m)) (k := fun t => K t / m)
    (by fun_prop) (fun t => by simp only [hKP t]) hc hT
  intro μ v hv hMv
  by_contra hμ1
  push Not at hμ1
  have hμ : μ ∈ spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) :=
    LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, hMv⟩
  have him := hreal μ hμ hμ1
  set r := μ.re with hr
  have hμr : μ = (r : ℂ) := Complex.ext rfl (by simp [him])
  rw [hμr] at hμ hμ1
  rw [Complex.norm_real, Real.norm_eq_abs] at hμ1
  obtain ⟨w, hw0, hw⟩ := exists_real_eigvec hμ
  have hr0 : r ≠ 0 := by rintro h; rw [h, abs_zero] at hμ1; linarith
  have habs : 0 < |r| := abs_pos.mpr hr0
  set lam := Real.log |r| / T with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (Real.log_nonneg hμ1) hT.le
  -- the real mode and its components
  set x : ℝ → Fin 2 → ℝ := fun t => transition A t 0 *ᵥ w with hxdef
  have hx : ∀ t, HasDerivAt x (A t *ᵥ x t) t := hasDerivAt_transition_mulVec hA w
  have hxT : ∀ t, x (t + T) = r • x t := real_mode_add_period hA hP hT hw
  set δ : ℝ → ℝ := fun t => x t 0
  set δ' : ℝ → ℝ := fun t => x t 1
  set δ'' : ℝ → ℝ := fun t => (A t *ᵥ x t) 1
  have hAx : ∀ t, A t *ᵥ x t = ![δ' t, -(K t / m) * δ t - 2 * (D / (2 * m)) * δ' t] := by
    intro t
    funext i
    fin_cases i
    · simp [hAdef, oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, δ']
    · simp [hAdef, oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, δ, δ']
      ring
  have hδ : ∀ t, HasDerivAt δ (δ' t) t := fun t => by
    have h := (hasDerivAt_pi.1 (hx t)) 0
    rw [hAx t] at h
    simpa using h
  have hδ' : ∀ t, HasDerivAt δ' (δ'' t) t := fun t => (hasDerivAt_pi.1 (hx t)) 1
  have heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0 := by
    intro t
    have h : δ'' t = -(K t / m) * δ t - 2 * (D / (2 * m)) * δ' t := by
      simp only [δ'']; rw [hAx t]; simp
    rw [h]
    field_simp
    ring
  have hne : ∃ t, δ t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : δ = fun _ => 0 := funext hcon
    have hd0 : δ' 0 = 0 := by
      have h := hδ 0
      rw [hzero] at h
      exact h.unique (hasDerivAt_const 0 0)
    apply hw0
    have hx0 : x 0 = w := by simp [hxdef, LinearSystems.stateTransitionMatrix_self]
    funext i
    fin_cases i
    · simpa [δ, hx0] using hcon 0
    · simpa [δ', hx0] using hd0
  -- remove the envelope `e^{λt}`
  set y : ℝ → ℝ := fun t => Real.exp (-(lam * t)) * δ t
  set y' : ℝ → ℝ := fun t => Real.exp (-(lam * t)) * (δ' t - lam * δ t)
  set y'' : ℝ → ℝ := fun t => Real.exp (-(lam * t)) * (δ'' t - 2 * lam * δ' t + lam ^ 2 * δ t)
  have he : ∀ t, HasDerivAt (fun t => Real.exp (-(lam * t))) (-lam * Real.exp (-(lam * t))) t :=
    fun t => by
      have h0 : HasDerivAt (fun t => -(lam * t)) (-lam) t := by
        convert (hasDerivAt_id t).const_mul (-lam) using 1
        · funext s; simp
        · simp
      convert h0.exp using 1
      ring
  have hy : ∀ t, HasDerivAt y (y' t) t := fun t => by
    have h := (he t).mul (hδ t)
    convert h using 1
    simp only [y']; ring
  have hy' : ∀ t, HasDerivAt y' (y'' t) t := fun t => by
    have h := (he t).mul ((hδ' t).sub ((hδ t).const_mul lam))
    convert h using 1
    simp only [y'', Pi.sub_apply]; ring
  have hyeq : ∀ t, m * y'' t + (D + 2 * m * lam) * y' t +
      (K t + D * lam + m * lam ^ 2) * y t = 0 := by
    intro t
    have := heq t
    simp only [y, y', y'']
    linear_combination Real.exp (-(lam * t)) * this
  have hyper : Periodic y (2 * T) := by
    intro t
    have h2 : δ (t + 2 * T) = r ^ 2 * δ t := by
      have h := congrFun (hxT (t + T)) 0
      rw [show t + T + T = t + 2 * T by ring, hxT t] at h
      simp only [δ, h, Pi.smul_apply, smul_eq_mul]
      ring
    have hexp : Real.exp (-(lam * (t + 2 * T))) = Real.exp (-(lam * t)) / r ^ 2 := by
      rw [show -(lam * (t + 2 * T)) = -(lam * t) + -(2 * Real.log |r|) by
        rw [hlam]; field_simp; ring, Real.exp_add, Real.exp_neg (2 * Real.log |r|),
        show 2 * Real.log |r| = Real.log (|r| ^ 2) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity), sq_abs]
      ring
    simp only [y, h2, hexp]
    field_simp
  have hyne : ∃ t, y t ≠ 0 := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, mul_ne_zero (Real.exp_pos _).ne' ht⟩
  -- apply the bound to the shifted oscillator
  have hbound := sq_damping_le (m := m) (D := D + 2 * m * lam)
    (Kbar := Kbar + D * lam + m * lam ^ 2) (η := ε * Kbar) (L := 2 * T)
    (K := fun t => K t + D * lam + m * lam ^ 2) hm (mul_nonneg hε hKbar.le)
    (by nlinarith [mul_nonneg hD.le hlam0, mul_nonneg hm.le (sq_nonneg lam)])
    (by positivity) hy hy' (by fun_prop) hyeq hyper hyne
    (fun t => by
      rw [show K t + D * lam + m * lam ^ 2 - (Kbar + D * lam + m * lam ^ 2) = K t - Kbar by ring]
      exact hdev t)
    (by positivity)
  have h1 : D ^ 2 * (Kbar - ε * Kbar) ≤
      (D + 2 * m * lam) ^ 2 * (Kbar + D * lam + m * lam ^ 2 - ε * Kbar) := by
    have hDD : D ^ 2 ≤ (D + 2 * m * lam) ^ 2 := by
      have : D ≤ D + 2 * m * lam := by nlinarith [mul_nonneg hm.le hlam0]
      exact pow_le_pow_left₀ hD.le this 2
    have hKK : Kbar - ε * Kbar ≤ Kbar + D * lam + m * lam ^ 2 - ε * Kbar := by
      nlinarith [mul_nonneg hD.le hlam0, mul_nonneg hm.le (sq_nonneg lam)]
    exact mul_le_mul hDD hKK (by nlinarith) (sq_nonneg _)
  nlinarith

/-- **The stability region in the modulation depth.** Under `m > 0`, `K̄ > 0`, `0 ≤ ε < 1` and
`ε / √(1 − ε) < D / √(m K̄)` (`= 2ξ`): for every period `T > 0`, every continuous `T`-periodic
waveform `p` with `|p| ≤ 1` and every depth `s ∈ [−ε, ε]`, the system
`m δ̈ + D δ̇ + K̄ (1 + s p(t)) δ = 0` is Floquet stable (all multipliers inside the unit circle). -/
@[tmio T, powerlib_foundation] theorem schurStable_of_threshold_waveform (hm : 0 < m)
    (hKbar : 0 < Kbar) (hε : 0 ≤ ε) (hε1 : ε < 1) (hξ : ε / √(1 - ε) < D / √(m * Kbar)) :
    ∀ T : ℝ, 0 < T → ∀ p : ℝ → ℝ, Continuous p → Periodic p T → (∀ t, |p t| ≤ 1) →
      ∀ s ∈ Icc (-ε) ε,
        LTI.SchurStable (monodromy (fun t => oscMatrix (D / (2 * m)) (Kbar * (1 + s * p t) / m))
          T 0) := by
  intro T hT p hp hpP hp1 s hs
  refine schurStable_of_threshold hm hKbar hε hε1 hξ hT (by fun_prop)
    (fun t => by simp only [hpP t]) (fun t => ?_)
  rw [show Kbar * (1 + s * p t) - Kbar = Kbar * (s * p t) by ring, abs_mul, abs_of_pos hKbar,
    abs_mul, mul_comm ε Kbar]
  refine mul_le_mul_of_nonneg_left ?_ hKbar.le
  calc |s| * |p t| ≤ ε * 1 := mul_le_mul (abs_le.mpr hs) (hp1 t) (abs_nonneg _) hε
    _ = ε := mul_one ε

/-- **Agreement of the levels in the universal region.** Under the threshold of
`schurStable_of_threshold`: the frozen small-signal matrices `oscMatrix (D/(2m)) (K(t)/m)` are
Hurwitz at every instant (`D > 0`, `K(t) ≥ (1 − ε) K̄ > 0`), the Floquet multipliers lie inside the
unit circle, and the periodic system is uniformly exponentially stable,
`‖Φ(t, s)‖ ≤ C e^{−β (t − s)}`
(`Periodic.uniformlyExponentiallyStable_of_spectralRadius_lt_one`). -/
@[tmio T, powerlib_foundation] theorem levels_agree_of_threshold (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hξ : ε / √(1 - ε) < D / √(m * Kbar)) (hT : 0 < T)
    (hK : Continuous K) (hKP : Periodic K T) (hdev : ∀ t, |K t - Kbar| ≤ ε * Kbar) :
    (∀ t, LinearSystems.IsHurwitz (oscMatrix (D / (2 * m)) (K t / m))) ∧
      LTI.SchurStable (monodromy (fun t => oscMatrix (D / (2 * m)) (K t / m)) T 0) ∧
      ∃ C β : ℝ, 0 < β ∧ ∀ s t, s ≤ t →
        ‖transition (fun t => oscMatrix (D / (2 * m)) (K t / m)) t s‖ ≤
          C * Real.exp (-(β * (t - s))) := by
  have hS := schurStable_of_threshold hm hKbar hε hε1 hξ hT hK hKP hdev
  have hD : 0 < D := by
    have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
    have hs2 : 0 < √(m * Kbar) := Real.sqrt_pos.mpr (by positivity)
    have h0 : 0 ≤ ε / √(1 - ε) := by positivity
    have := h0.trans_lt hξ
    exact (div_pos_iff_of_pos_right hs2).mp this
  have hA : Continuous fun t => oscMatrix (D / (2 * m)) (K t / m) := by
    unfold oscMatrix
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine ⟨fun t => ?_, hS, uniformlyExponentiallyStable_of_spectralRadius_lt_one hA
    (fun t => by simp only [hKP t]) hT ((LTI.schurStable_iff_spectralRadius_lt_one _).mp hS)⟩
  rw [Criteria.isHurwitz_fin_two_iff, trace_oscMatrix, det_oscMatrix]
  have hKt : 0 < K t := by
    have := (abs_le.mp (hdev t)).1
    nlinarith
  exact ⟨by have : 0 < D / (2 * m) := by positivity
            linarith, div_pos hKt hm⟩

end Region

/-! ## Comparison with the frequency-specific bounds -/

section Compare

/-- **Sinusoidal modulation: both necessary conditions.** For `K = K̄ (1 + ε cos Ωt)` (`m, K̄,
Ω > 0`, `|ε| < 1`) a nonzero `(2π/Ω)`-antiperiodic solution (a sustained oscillation at `Ω/2`)
satisfies the Wirtinger bound `D Ω / (2K̄) ≤ |ε|` (`Wirtinger.pump_amplitude_cos`) and the
universal bound `D ≤ |ε| √(m K̄) / √(1 − |ε|)`. -/
@[tmio T, powerlib_foundation] theorem sinusoidal_necessary {m D Kbar ε Ω : ℝ}
    {δ δ' δ'' : ℝ → ℝ} (hm : 0 < m) (hKbar : 0 < Kbar) (hΩ : 0 < Ω) (hε1 : |ε| < 1)
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, m * δ'' t + D * δ' t + Kbar * (1 + ε * Real.cos (Ω * t)) * δ t = 0)
    (hanti : Antiperiodic δ (2 * Real.pi / Ω)) (hne : ∃ t, δ t ≠ 0) :
    D * Ω / (2 * Kbar) ≤ |ε| ∧ D ≤ |ε| * √(m * Kbar) / √(1 - |ε|) := by
  refine ⟨Wirtinger.pump_amplitude_cos hΩ hKbar hδ hδ' heq hanti hne, ?_⟩
  refine damping_le_of_antiperiodic (K := fun t => Kbar * (1 + ε * Real.cos (Ω * t))) hm hKbar
    (abs_nonneg ε) hε1 (by positivity) hδ hδ' (by fun_prop) heq hanti hne fun t => ?_
  rw [show Kbar * (1 + ε * Real.cos (Ω * t)) - Kbar = Kbar * (ε * Real.cos (Ω * t)) by ring,
    abs_mul, abs_of_pos hKbar, abs_mul, mul_comm |ε| Kbar]
  refine mul_le_mul_of_nonneg_left ?_ hKbar.le
  calc |ε| * |Real.cos (Ω * t)| ≤ |ε| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg ε)
    _ = |ε| := mul_one _

/-- **Which bound is sharper.** For `0 < ε < 1`, `m, K̄, Ω > 0`, the Wirtinger bound on the
damping of a half-frequency oscillation, `D ≤ 2K̄ε/Ω`, is at most the universal bound
`D ≤ ε √(m K̄)/√(1 − ε)` exactly when `Ω ≥ 2 ω₀ √(1 − ε)`, `ω₀ = √(K̄/m)`: near and above the
principal resonance `Ω = 2ω₀` the frequency-specific bound is sharper, for slow pumps
`Ω < 2ω₀√(1 − ε)` the universal one; only the universal bound covers every waveform and the
periodic (multiplier `+1`) solutions. -/
@[tmio T, powerlib_foundation] theorem wirtinger_le_universal_iff {m Kbar ε Ω : ℝ} (hm : 0 < m)
    (hKbar : 0 < Kbar) (hΩ : 0 < Ω) (hε : 0 < ε) (hε1 : ε < 1) :
    2 * Kbar * ε / Ω ≤ ε * √(m * Kbar) / √(1 - ε) ↔ 2 * √(Kbar / m) * √(1 - ε) ≤ Ω := by
  have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
  have hsm : 0 < √m := Real.sqrt_pos.mpr hm
  have hsK : 0 < √Kbar := Real.sqrt_pos.mpr hKbar
  have hK : √Kbar * √Kbar = Kbar := Real.mul_self_sqrt hKbar.le
  rw [div_le_div_iff₀ hΩ hs1, Real.sqrt_mul hm.le, Real.sqrt_div hKbar.le,
    show 2 * (√Kbar / √m) * √(1 - ε) = 2 * √Kbar * √(1 - ε) / √m by ring, div_le_iff₀ hsm]
  constructor
  · intro h
    have h' : (ε * √Kbar) * (2 * √Kbar * √(1 - ε)) ≤ (ε * √Kbar) * (Ω * √m) := by
      have : 2 * Kbar * ε * √(1 - ε) = (ε * √Kbar) * (2 * √Kbar * √(1 - ε)) := by
        rw [show 2 * Kbar * ε * √(1 - ε) = 2 * (√Kbar * √Kbar) * ε * √(1 - ε) by rw [hK]]; ring
      rw [← this]; linarith
    exact le_of_mul_le_mul_left h' (by positivity)
  · intro h
    have : 2 * Kbar * ε * √(1 - ε) = (ε * √Kbar) * (2 * √Kbar * √(1 - ε)) := by
      rw [show 2 * Kbar * ε * √(1 - ε) = 2 * (√Kbar * √Kbar) * ε * √(1 - ε) by rw [hK]]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ ε * √Kbar)]

/-- **The exact square-wave centre threshold lies above the universal curve.** For the Meissner
oscillator `ẍ + 2c ẋ + ω₀²(1 ± ε) x = 0` (unit mass: `D = 2c`, `K̄ = ω₀²`, `ξ = c/ω₀`) at the
centre of the principal tongue, `Ω = ν₁ + ν₂`, instability requires `π c √(ν₁ν₂) < ε ω₀²`
(`Meissner.centre_threshold_lower`), and when `2c² ≤ ω₀²(1 − ε)` this exact threshold dominates
the universal one: `2 c ω₀ √(1 − ε) ≤ π c √(ν₁ν₂)`, hence `2ξ √(1 − ε) < ε`. -/
@[tmio T, powerlib_foundation] theorem meissner_centre_above_universal {c ω₀ ε T ν₁ ν₂ : ℝ}
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hε1 : ε < 1) (hω : 0 < ω₀)
    (hcs : 2 * c ^ 2 ≤ ω₀ ^ 2 * (1 - ε)) (hT : T = 2 * Real.pi / (ν₁ + ν₂))
    (hu : ∃ μ ∈ spectrum ℂ ((Meissner.meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)),
      1 < ‖μ‖) :
    2 * c * ω₀ * √(1 - ε) ≤ Real.pi * c * √(ν₁ * ν₂) ∧
      Real.pi * c * √(ν₁ * ν₂) < ε * ω₀ ^ 2 := by
  refine ⟨?_, Meissner.centre_threshold_lower hν₁ hν₂ h₁ h₂ hc hε hT hu⟩
  have h21 : ν₂ ≤ ν₁ := by nlinarith
  have hprod : ω₀ ^ 2 * (1 - ε) / 2 ≤ ν₁ * ν₂ := by nlinarith
  have hpi : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hkey : (2 * ω₀ * √(1 - ε)) ^ 2 ≤ (Real.pi * √(ν₁ * ν₂)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg ω₀]
  have h := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hkey
  calc 2 * c * ω₀ * √(1 - ε) = c * (2 * ω₀ * √(1 - ε)) := by ring
    _ ≤ c * (Real.pi * √(ν₁ * ν₂)) := mul_le_mul_of_nonneg_left h hc
    _ = Real.pi * c * √(ν₁ * ν₂) := by ring

end Compare

end powerlib.ParametricResonance.UniversalThreshold
