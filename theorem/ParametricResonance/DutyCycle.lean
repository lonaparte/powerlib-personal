import theorem.ParametricResonance.UniversalThresholdPiecewise

/-! # Square waves of general duty ratio: exact boundary and averaged model

The damped oscillator `ẍ + 2cẋ + k(t)x = 0` whose stiffness is `ω₀²(1 + ε)` on the first fraction
`δ ∈ (0, 1)` of every pump period `T` and `ω₀²(1 − ε')` on the rest generalizes the Meissner
equation (`δ = 1/2`, `ε' = ε`). With `x = e^{−ct}y` each piece is a harmonic oscillator, so the
monodromy is `M = e^{−cT} S R(ν₂, θ₂) R(ν₁, θ₁) S⁻¹`, `θ₁ = ν₁δT`, `θ₂ = ν₂(1 − δ)T`,
`ν₁² = ω₀²(1 + ε) − c²`, `ν₂² = ω₀²(1 − ε') − c²`, with `det M = e^{−2cT}` and
`tr M = e^{−cT} τ`, `τ = 2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂`: the exact boundary is
`|τ| = 2 cosh(cT)`. At the centre of the principal tongue, `θ₁ + θ₂ = π`, the trace is
`−2 − ((ν₁ − ν₂)²/(ν₁ν₂)) sin² θ₁` as for the symmetric wave, now with `θ₁ = ν₁δT ≈ πδ`, so the
exact threshold on the jump is `(ε + ε') sin(πδ) = 2πξ (1 + o(1))`.

The averaged (L2) model sees only the mean `δε − (1 − δ)ε'` (a detuning) and the fundamental of
the wave, of amplitude `m₁ = (2/π) |sin(πδ)| |ε + ε'|`; its threshold at the 2:1 resonance in the
zero-mean normalization `δε = (1 − δ)ε'` is `|ε + ε'| |sin(πδ)| = 2πξ`, the same leading term:
both thresholds on the jump scale with `1/sin(πδ)`, and a wave with a short pulse (`δ → 0`) or a
short gap (`δ → 1`) needs a correspondingly larger jump. The universal stability region of
`theorem/ParametricResonance/UniversalThresholdPiecewise.lean` covers every duty ratio at every
level.

Scope.
* The scalar oscillator in the state `(x, ẋ)`: `ẏ = oscMatrix c (k(t)) y`, constant damping `c`,
  continuous time; `dutyWave ε ε' δ T` (`ε` on `[nT, nT + δT)`, `−ε'` on `[nT + δT, (n + 1)T)`),
  stiffness `ω₀²(1 + dutyWave ε ε' δ T t)`; solutions continuous on `[0, T]` with right
  derivatives on `[0, T)` (`solution_period`). The exact statements use two oscillatory levels
  `k_i = ν_i² + c²`, `ν_i ≠ 0`, any duty ratio and period `T > 0`; the monodromy
  `dutyMonodromy c k₁ k₂ δ T = Averaging.periodMap δ T (oscMatrix c k₁) (oscMatrix c k₂)`.
* L1: multipliers of `dutyMonodromy` (`LTI.SchurStable`, a multiplier of modulus `> 1`). L2: the
  averaged matrix `SquareWave.averagedMatrix` of the rotating frame at half the pump frequency
  `ω = 2π/T`, its characteristic roots and `LinearSystems.IsHurwitz`. L3: the frozen matrices.
* Both normalizations: arbitrary `ε`, `ε'` (the mean enters the L2 detuning) and the zero-mean
  case `δε = (1 − δ)ε'` (`averaged_centre_threshold`). The first-order agreement of L1 and L2 is
  proved at the exact centre of the principal tongue for fixed `δ ∈ (0, 1)` in cone form, and
  the L2 verdict is transferred to L1 for all small modulations in the distinguished scaling
  (damping `μs`, levels `ω²/4 + μa_i`) through the time change of `SquareWave.twoPiece`
  generalized to a switching instant at `δT` (`twoPieceDuty`).
* The generic two-piece averaging theorems concern continuous bounded `G₁`, `G₂` on `[0, δT]` and
  `[δT, T]` (`Periodic.transition`), `δ ∈ (0, 1)`, stated for `ε → 0⁺`.
* Generic mathematics; no model family.

Source: the mechanism of the Meissner equation (Meissner 1918; Richards, *Analysis of
Periodically Time-Varying Systems*, 1983) with the two stiffness intervals of unequal length;
the closed forms
`Meissner.exp_oscMatrix`, `Meissner.shear_neg_mul_shear`; the two-state boundary
`Periodic.exists_one_lt_norm_iff`, `Periodic.schurStable_iff_abs_trace_lt`; the averaged matrix of
an arbitrary waveform `SquareWave.averagedMatrix_eq`, `SquareWave.norm_pump_eq_amp` and the slow
flow branches `Branches.slowFlow_unstable_iff`; the universal threshold
`PiecewiseThreshold.periodMap_schurStable_of_threshold`.

Results.
* `dutyWave`, `dutyMonodromy`, `dutyTrace`; `dutyWave_half`, `dutyMonodromy_half` — duty `1/2`
  is the Meissner square wave, monodromy and reduced trace.
* `dutyMonodromy_eq_exp`, `dutyMonodromy_eq`, `trace_rot_mul_rot`, `det_dutyMonodromy`,
  `trace_dutyMonodromy` — `M = e^{(1−δ)TB₂} e^{δTB₁} = e^{−cT} S R(ν₂, θ₂) R(ν₁, θ₁) S⁻¹`,
  `det M = e^{−2cT}`, `tr M = e^{−cT} τ`.
* `floquet_iff` — Floquet instability iff `2 cosh(cT) < |τ|` (`c ≥ 0`), Schur stability iff
  `|τ| < 2 cosh(cT)` (`c > 0`); `pm_one_mem_spectrum_iff` — `−1` iff `τ = −2 cosh(cT)`, `+1` iff
  `τ = 2 cosh(cT)`.
* `dutyTrace_centre`, `centre_floquet_iff`, `centre_threshold_iff` — at `θ₁ + θ₂ = π`:
  `τ = −2 − ((ν₁ − ν₂)²/(ν₁ν₂)) sin² θ₁`, instability iff
  `2√(ν₁ν₂)(ν₁ + ν₂) sinh(cT/2) < (ε + ε') ω₀² |sin θ₁|`, stability iff the reverse.
* `centre_threshold_ratio` — fixed `δ ∈ (0, 1)`: for every `η > 0` and small `ξ, ε, ε'`,
  `(ε + ε') sin(πδ) > (2π + η)ξ` gives instability and `< (2π − η)ξ` stability at the centre.
* `solution_period` — every right-differentiable solution has `y(T) = M y(0)`, and from every
  initial state there is one.
* `schurStable_of_universal` — `|ε|, |ε'| ≤ η`, `η/√(1 − η) < 2c/ω₀`: Schur stable for every period
  and every duty ratio.
* `intervalIntegrable_dutyWave`, `integral_dutyWave`, `fourier_dutyWave`, `amp_dutyWave` — mean
  `δε − (1 − δ)ε'`, `a₁ = (ε + ε') sin(2πδ)/π`, `b₁ = (ε + ε')(1 − cos 2πδ)/π`,
  `m₁ = (2/π)|sin(πδ)||ε + ε'|`.
* `averagedMatrix_dutyWave`, `averaged_threshold`, `averaged_centre_threshold` — the L2 matrix is
  the 2:1 slow flow; unstable iff `πω√(c² + Δ²) < ω₀²|ε + ε'||sin(πδ)|`; at `ω = 2ω₀`, zero mean:
  `2πξ ≷ |ε + ε'||sin(πδ)|`.
* `levels_agree_of_universal` — in the universal region the frozen matrices are Hurwitz, the
  monodromy is Schur stable for every period, and the L2 matrix is Hurwitz for
  `4ω₀√(1 − η) ≤ πω`.
* `warp`, `reparamOn`, `reparamOnDeriv`, `twoPieceDuty`, `hasDerivAt_reparamOn`,
  `continuous_reparamOn`, `continuous_reparamOnDeriv`, `reparamOn_left`, `reparamOn_right`,
  `reparamOnDeriv_left`, `reparamOnDeriv_right`, `abs_reparamOnDeriv_le`,
  `continuous_twoPieceDuty`, `norm_twoPieceDuty_le`, `integral_twoPieceDuty`,
  `transition_twoPieceDuty` — the time change of each piece onto itself with zero speed at its
  ends: a continuous field with the same average whose transition over `[0, T]` is
  `Φ_{G₂}(T, δT) Φ_{G₁}(δT, 0)`; `twoPieceDuty_averaging` — first-order averaging across a
  switching instant at `δT` (stability and instability).
* `integral_pieces`, `dutyMonodromy_mul_scale` — the average of two frozen levels split at `δT`
  is a 2:1 slow flow; `M D = −D Φ₂(T, δT) Φ₁(δT, 0)` in the rotating frame.
* `averaging_transfer` — in the distinguished scaling the L2 verdict (Hurwitz, or an exponent with
  positive real part) holds for the exact duty-`δ` monodromy for all small `μ > 0`.
-/

noncomputable section
namespace powerlib.ParametricResonance.DutyCycle

open Set Matrix Function Filter Topology MeasureTheory
open powerlib.Periodic (oscMatrix)
open powerlib.ParametricResonance.Meissner (shear rot shear_neg_mul_shear)
open powerlib.SpecialFunctions.PeriodicWaves (squareWave cosCoeff sinCoeff amp)
open scoped Matrix.Norms.Operator

/-! ## The model -/

/-- The duty-`δ` square wave: `ε` on the first fraction `δ` of every period `T`, `−ε'` on the
rest (`[nT, nT + δT)` and `[nT + δT, (n + 1)T)`). -/
def dutyWave (ε ε' δ T t : ℝ) : ℝ := if Int.fract (t / T) < δ then ε else -ε'

/-- The monodromy of `ẍ + 2cẋ + k(t)x = 0` with `k = k₁` on the first fraction `δ` of the period
and `k = k₂` on the rest: the period map `Averaging.periodMap δ T B₁ B₂ = e^{(1−δ)TB₂} e^{δTB₁}`,
`B_i = oscMatrix c k_i`. -/
def dutyMonodromy (c k₁ k₂ δ T : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Averaging.periodMap δ T (oscMatrix c k₁) (oscMatrix c k₂)

/-- The reduced trace `2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂` of two oscillatory
pieces of phases `θ₁ = ν₁δT`, `θ₂ = ν₂(1 − δ)T`. -/
def dutyTrace (ν₁ ν₂ θ₁ θ₂ : ℝ) : ℝ :=
  2 * Real.cos θ₁ * Real.cos θ₂ - (ν₁ / ν₂ + ν₂ / ν₁) * Real.sin θ₁ * Real.sin θ₂

/-- Duty `1/2` and `ε' = ε` is the square wave of the Meissner equation. -/
@[tmio T, powerlib_foundation] theorem dutyWave_half (ε T t : ℝ) :
    dutyWave ε ε (1 / 2) T t = squareWave ε T t := rfl

/-- At duty `1/2` the monodromy is the Meissner monodromy (both levels `ω₀²(1 ± ε)`), and the
reduced trace is `Meissner.reducedTrace` at the half-period phases. -/
@[tmio T, powerlib_foundation] theorem dutyMonodromy_half (c ω₀ ε T ν₁ ν₂ : ℝ) :
    dutyMonodromy c (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε)) (1 / 2) T =
      Meissner.meissnerMonodromy c ω₀ ε T ∧
    dutyTrace ν₁ ν₂ (ν₁ * T / 2) (ν₂ * T / 2) = Meissner.reducedTrace ν₁ ν₂ T :=
  ⟨rfl, rfl⟩

section Exact

variable {c k₁ k₂ δ T ν₁ ν₂ : ℝ}

/-- `M = e^{(1−δ)TB₂} e^{δTB₁}`. -/
@[tmio T, powerlib_foundation] theorem dutyMonodromy_eq_exp (c k₁ k₂ δ T : ℝ) :
    dutyMonodromy c k₁ k₂ δ T = NormedSpace.exp (((1 - δ) * T) • oscMatrix c k₂) *
      NormedSpace.exp ((δ * T) • oscMatrix c k₁) := rfl

/-- `M = e^{−cT} S (R(ν₂, θ₂) R(ν₁, θ₁)) S⁻¹`, `θ₁ = ν₁δT`, `θ₂ = ν₂(1 − δ)T`, for two oscillatory
levels `ν_i² = k_i − c² > 0` (`Meissner.exp_oscMatrix`). -/
@[tmio T, powerlib_foundation] theorem dutyMonodromy_eq (hν₁ : ν₁ ^ 2 = k₁ - c ^ 2)
    (hν₂ : ν₂ ^ 2 = k₂ - c ^ 2) (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    dutyMonodromy c k₁ k₂ δ T = Real.exp (-(c * T)) •
      (shear c * (rot ν₂ (ν₂ * ((1 - δ) * T)) * rot ν₁ (ν₁ * (δ * T))) * shear (-c)) := by
  rw [dutyMonodromy_eq_exp, Meissner.exp_oscMatrix hν₂ h₂, Meissner.exp_oscMatrix hν₁ h₁,
    smul_mul_smul_comm, ← Real.exp_add,
    show -(c * ((1 - δ) * T)) + -(c * (δ * T)) = -(c * T) by ring]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (shear (-c)) (shear c), shear_neg_mul_shear, Matrix.one_mul]

/-- `tr(R(ν₂, θ₂) R(ν₁, θ₁)) = 2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂` for arbitrary
phases. -/
@[tmio T, powerlib_foundation] theorem trace_rot_mul_rot (ν₁ ν₂ θ₁ θ₂ : ℝ) :
    (rot ν₂ θ₂ * rot ν₁ θ₁).trace = dutyTrace ν₁ ν₂ θ₁ θ₂ := by
  simp only [rot, dutyTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- `det M = e^{−2cT}` for every duty ratio and every pair of levels (Liouville,
`Periodic.det_exp_smul`). -/
@[tmio T, powerlib_foundation] theorem det_dutyMonodromy (c k₁ k₂ δ T : ℝ) :
    (dutyMonodromy c k₁ k₂ δ T).det = Real.exp (-(2 * c) * T) := by
  rw [dutyMonodromy_eq_exp, Matrix.det_mul, Periodic.det_exp_smul, Periodic.det_exp_smul,
    Periodic.trace_oscMatrix, Periodic.trace_oscMatrix, ← Real.exp_add]
  ring_nf

/-- `tr M = e^{−cT} τ`, `τ = dutyTrace ν₁ ν₂ (ν₁δT) (ν₂(1 − δ)T)`. -/
@[tmio T, powerlib_foundation] theorem trace_dutyMonodromy (hν₁ : ν₁ ^ 2 = k₁ - c ^ 2)
    (hν₂ : ν₂ ^ 2 = k₂ - c ^ 2) (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    (dutyMonodromy c k₁ k₂ δ T).trace =
      Real.exp (-(c * T)) * dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T)) := by
  rw [dutyMonodromy_eq hν₁ hν₂ h₁ h₂, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, shear_neg_mul_shear, Matrix.one_mul, trace_rot_mul_rot]

@[tmio T, powerlib_foundation] private theorem one_add_exp_eq (c T : ℝ) :
    1 + Real.exp (-(2 * c) * T) = Real.exp (-(c * T)) * (2 * Real.cosh (c * T)) := by
  rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero, mul_add, ← Real.exp_add, ← Real.exp_add,
    show -(c * T) + c * T = 0 by ring, show -(c * T) + -(c * T) = -(2 * c) * T by ring,
    Real.exp_zero]

/-- **The exact boundary for every duty ratio.** For `c ≥ 0`, `T > 0` and two oscillatory levels,
the duty-`δ` system is Floquet unstable iff `2 cosh(cT) < |τ|`,
`τ = 2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂`, `θ₁ = ν₁δT`, `θ₂ = ν₂(1 − δ)T`; for
`c > 0` Schur stable iff `|τ| < 2 cosh(cT)`. -/
@[tmio T, powerlib_foundation] theorem floquet_iff (hν₁ : ν₁ ^ 2 = k₁ - c ^ 2)
    (hν₂ : ν₂ ^ 2 = k₂ - c ^ 2) (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (hc : 0 ≤ c) (hT : 0 < T) :
    ((∃ μ ∈ spectrum ℂ ((dutyMonodromy c k₁ k₂ δ T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      2 * Real.cosh (c * T) < |dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T))|) ∧
    (0 < c → (LTI.SchurStable (dutyMonodromy c k₁ k₂ δ T) ↔
      |dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T))| < 2 * Real.cosh (c * T))) := by
  have hdet := det_dutyMonodromy c k₁ k₂ δ T
  refine ⟨?_, fun hc' => ?_⟩
  · have h0 : 0 < (dutyMonodromy c k₁ k₂ δ T).det := by rw [hdet]; positivity
    have h1 : (dutyMonodromy c k₁ k₂ δ T).det ≤ 1 := by
      rw [hdet, Real.exp_le_one_iff]; nlinarith
    rw [Periodic.exists_one_lt_norm_iff h0 h1, hdet, trace_dutyMonodromy hν₁ hν₂ h₁ h₂,
      abs_mul, abs_of_pos (Real.exp_pos _), one_add_exp_eq]
    exact mul_lt_mul_iff_right₀ (Real.exp_pos _)
  · have h1 : (dutyMonodromy c k₁ k₂ δ T).det < 1 := by
      rw [hdet, Real.exp_lt_one_iff]; nlinarith
    rw [Periodic.schurStable_iff_abs_trace_lt h1, hdet, trace_dutyMonodromy hν₁ hν₂ h₁ h₂,
      abs_mul, abs_of_pos (Real.exp_pos _), one_add_exp_eq]
    exact mul_lt_mul_iff_right₀ (Real.exp_pos _)

/-- The multiplier `−1` (half-frequency boundary) iff `τ = −2 cosh(cT)`, `+1` (harmonic
boundary) iff `τ = 2 cosh(cT)`. -/
@[tmio T, powerlib_foundation] theorem pm_one_mem_spectrum_iff (hν₁ : ν₁ ^ 2 = k₁ - c ^ 2)
    (hν₂ : ν₂ ^ 2 = k₂ - c ^ 2) (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    ((-1 : ℂ) ∈ spectrum ℂ ((dutyMonodromy c k₁ k₂ δ T).map (algebraMap ℝ ℂ)) ↔
      dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T)) = -(2 * Real.cosh (c * T))) ∧
    ((1 : ℂ) ∈ spectrum ℂ ((dutyMonodromy c k₁ k₂ δ T).map (algebraMap ℝ ℂ)) ↔
      dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T)) = 2 * Real.cosh (c * T)) := by
  refine ⟨?_, ?_⟩
  · rw [Periodic.neg_one_mem_spectrum_iff, det_dutyMonodromy,
      trace_dutyMonodromy hν₁ hν₂ h₁ h₂, one_add_exp_eq,
      show -(Real.exp (-(c * T)) * (2 * Real.cosh (c * T))) =
        Real.exp (-(c * T)) * -(2 * Real.cosh (c * T)) by ring]
    exact mul_right_inj' (Real.exp_pos _).ne'
  · rw [Periodic.one_mem_spectrum_iff, det_dutyMonodromy, trace_dutyMonodromy hν₁ hν₂ h₁ h₂,
      one_add_exp_eq]
    exact mul_right_inj' (Real.exp_pos _).ne'

/-- **The centre of the principal tongue for every duty ratio.** If the two phases add up to a
half turn, `θ₁ + θ₂ = π` (pump period `T = π/(ν₁δ + ν₂(1 − δ))`), then
`τ = −2 − ((ν₁ − ν₂)²/(ν₁ν₂)) sin² θ₁`, the formula of `Meissner.reducedTrace_centre` with
`θ₁ = ν₁δT` instead of `ν₁T/2`. -/
@[tmio T, powerlib_foundation] theorem dutyTrace_centre {θ₁ θ₂ : ℝ} (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hθ : θ₁ + θ₂ = Real.pi) :
    dutyTrace ν₁ ν₂ θ₁ θ₂ = -2 - (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin θ₁ ^ 2 := by
  rw [dutyTrace, show θ₂ = Real.pi - θ₁ by linarith, Real.cos_pi_sub, Real.sin_pi_sub]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ₁]

/-- **The centre criterion for every duty ratio.** At `ν₁δT + ν₂(1 − δ)T = π` with `c ≥ 0`:
Floquet instability iff `4ν₁ν₂ sinh²(cT/2) < (ν₁ − ν₂)² sin² θ₁`, `θ₁ = ν₁δT`; for `c > 0`
Schur stability iff the reverse strict inequality holds. -/
@[tmio T, powerlib_foundation] theorem centre_floquet_iff (hν₁ : ν₁ ^ 2 = k₁ - c ^ 2)
    (hν₂ : ν₂ ^ 2 = k₂ - c ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) (hc : 0 ≤ c) (hT : 0 < T)
    (hθ : ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi) :
    ((∃ μ ∈ spectrum ℂ ((dutyMonodromy c k₁ k₂ δ T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      4 * (ν₁ * ν₂) * Real.sinh (c * T / 2) ^ 2 <
        (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * (δ * T)) ^ 2) ∧
    (0 < c → (LTI.SchurStable (dutyMonodromy c k₁ k₂ δ T) ↔
      (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * (δ * T)) ^ 2 <
        4 * (ν₁ * ν₂) * Real.sinh (c * T / 2) ^ 2)) := by
  obtain ⟨hU, hS⟩ := floquet_iff (δ := δ) hν₁ hν₂ h₁.ne' h₂.ne' hc hT
  have hp : 0 < ν₁ * ν₂ := mul_pos h₁ h₂
  set Q := (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * (δ * T)) ^ 2
  set S := Real.sinh (c * T / 2) ^ 2
  have habs : |dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T))| = 2 + Q / (ν₁ * ν₂) := by
    rw [dutyTrace_centre h₁ h₂ hθ]
    have hnn : 0 ≤ Q / (ν₁ * ν₂) := by positivity
    rw [show -2 - (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * (δ * T)) ^ 2 =
        -(2 + Q / (ν₁ * ν₂)) by simp only [Q]; ring, abs_neg, abs_of_nonneg (by positivity)]
  have hcosh : 2 * Real.cosh (c * T) = 2 + 4 * S := by
    rw [show c * T = 2 * (c * T / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
    simp only [S]; ring
  rw [habs, hcosh] at hU hS
  refine ⟨hU.trans ?_, fun hc' => (hS hc').trans ?_⟩
  · rw [add_lt_add_iff_left, lt_div_iff₀ hp]; constructor <;> intro h <;> linarith
  · rw [add_lt_add_iff_left, div_lt_iff₀ hp]; constructor <;> intro h <;> linarith

end Exact

/-! ## Solutions of the duty-cycle oscillator -/

section Solutions

variable {c ω₀ ε ε' δ T : ℝ}

@[tmio T, powerlib_foundation] private theorem dutyWave_of_mem (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Ico 0 T) : dutyWave ε ε' δ T t = if t < δ * T then ε else -ε' := by
  have hf : Int.fract (t / T) = t / T := by
    rw [Int.fract_eq_self]; exact ⟨div_nonneg ht.1 hT.le, (div_lt_one hT).mpr ht.2⟩
  have hiff : t / T < δ ↔ t < δ * T := div_lt_iff₀ hT
  simp only [dutyWave, hf]
  by_cases h : t < δ * T
  · simp [h, hiff.mpr h]
  · simp [h, mt hiff.mp h]

/-- **The monodromy maps the initial state to the state after one period.** Every solution of
`ẍ + 2cẋ + ω₀²(1 + p(t))x = 0`, `p = dutyWave ε ε' δ T` (`δ ∈ [0, 1]`, `T > 0`), continuous on
`[0, T]` with right derivatives on `[0, T)`, has `y(T) = M y(0)` (uniqueness on the two pieces,
`Meissner.eq_exp_mulVec_of_rightDeriv`); and from every initial state there is such a solution
(`PiecewiseThreshold.exists_switched_solution`). -/
@[tmio T, powerlib_foundation] theorem solution_period (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 0 < T) :
    (∀ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Icc 0 T) →
      (∀ t ∈ Ico 0 T, HasDerivWithinAt y
        (oscMatrix c (ω₀ ^ 2 * (1 + dutyWave ε ε' δ T t)) *ᵥ y t) (Ici t) t) →
      y T = dutyMonodromy c (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T *ᵥ y 0) ∧
    ∀ w : Fin 2 → ℝ, ∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, HasDerivWithinAt y
        (oscMatrix c (ω₀ ^ 2 * (1 + dutyWave ε ε' δ T t)) *ᵥ y t) (Ici t) t) ∧
      y 0 = w ∧ y T = dutyMonodromy c (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T *ᵥ w := by
  have hdT : δ * T ≤ T := by nlinarith
  have hdT0 : 0 ≤ δ * T := by positivity
  have hk : ∀ t ∈ Ico 0 T, oscMatrix c (ω₀ ^ 2 * (1 + dutyWave ε ε' δ T t)) =
      if t < δ * T then oscMatrix c (ω₀ ^ 2 * (1 + ε)) else oscMatrix c (ω₀ ^ 2 * (1 - ε')) := by
    intro t ht
    rw [dutyWave_of_mem hT ht]
    split_ifs
    · rfl
    · rw [show ω₀ ^ 2 * (1 + -ε') = ω₀ ^ 2 * (1 - ε') by ring]
  refine ⟨fun y hc hy => ?_, fun w => ?_⟩
  · have e1 := Meissner.eq_exp_mulVec_of_rightDeriv (oscMatrix c (ω₀ ^ 2 * (1 + ε)))
      (hc.mono (Icc_subset_Icc le_rfl hdT)) (fun t ht => by
        have h := hy t ⟨ht.1, ht.2.trans_le hdT⟩
        rw [hk t ⟨ht.1, ht.2.trans_le hdT⟩] at h
        simpa [ht.2] using h) (δ * T) ⟨hdT0, le_rfl⟩
    have e2 := Meissner.eq_exp_mulVec_of_rightDeriv (oscMatrix c (ω₀ ^ 2 * (1 - ε')))
      (hc.mono (Icc_subset_Icc hdT0 le_rfl)) (fun t ht => by
        have h := hy t ⟨hdT0.trans ht.1, ht.2⟩
        rw [hk t ⟨hdT0.trans ht.1, ht.2⟩] at h
        simpa [not_lt.mpr ht.1] using h) T ⟨hdT, le_rfl⟩
    rw [e2, e1, Matrix.mulVec_mulVec, sub_zero, show T - δ * T = (1 - δ) * T by ring]
    rfl
  · obtain ⟨y, hyc, hyd, hy0, hyT⟩ := PiecewiseThreshold.exists_switched_solution hδ0 hδ1 hT
      (oscMatrix c (ω₀ ^ 2 * (1 + ε))) (oscMatrix c (ω₀ ^ 2 * (1 - ε'))) w
    exact ⟨y, hyc, fun t ht => by rw [hk t ht]; exact hyd t ht, hy0, hyT⟩

end Solutions

/-! ## The universal threshold for every duty ratio -/

section Universal

variable {c ω₀ ε ε' η δ T : ℝ}

/-- **Below the universal curve the duty-`δ` oscillator is stable at every pump frequency.** With
`ω₀ > 0`, both depths `|ε|, |ε'| ≤ η < 1` and `η / √(1 − η) < 2c/ω₀` (`= 2ξ`), the monodromy of
the duty-`δ` square-wave oscillator is Schur stable for every period `T > 0` and every duty ratio
`δ ∈ [0, 1]` (`PiecewiseThreshold.periodMap_schurStable_of_threshold`; the stiffness jumps). -/
@[tmio T, powerlib_foundation] theorem schurStable_of_universal (hω : 0 < ω₀) (hη1 : η < 1)
    (hε : |ε| ≤ η) (hε' : |ε'| ≤ η) (hξ : η / √(1 - η) < 2 * c / ω₀) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hT : 0 < T) :
    LTI.SchurStable (dutyMonodromy c (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T) := by
  have hη : 0 ≤ η := (abs_nonneg ε).trans hε
  have hdev : ∀ σ : ℝ, |σ| ≤ η → |ω₀ ^ 2 * (1 + σ) - ω₀ ^ 2| ≤ η * ω₀ ^ 2 := fun σ hσ => by
    rw [show ω₀ ^ 2 * (1 + σ) - ω₀ ^ 2 = ω₀ ^ 2 * σ by ring, abs_mul, abs_of_pos (by positivity),
      mul_comm]
    exact mul_le_mul_of_nonneg_right hσ (by positivity)
  exact PiecewiseThreshold.periodMap_schurStable_of_threshold (by positivity) hη hη1
    (by rwa [Real.sqrt_sq hω.le]) (hdev ε hε)
    (by rw [show ω₀ ^ 2 * (1 - ε') = ω₀ ^ 2 * (1 + -ε') by ring]; exact hdev (-ε') (by rwa [abs_neg]))
    hδ0 hδ1 hT

end Universal

/-! ## The averaged (L2) model of the duty-`δ` wave -/

section Averaged

variable {ε ε' δ T : ℝ}

@[tmio T, powerlib_foundation] theorem intervalIntegrable_dutyWave (ε ε' δ T a b : ℝ) :
    IntervalIntegrable (dutyWave ε ε' δ T) volume a b := by
  have hm : Measurable (dutyWave ε ε' δ T) := by
    unfold dutyWave
    exact Measurable.ite (measurableSet_lt ((measurable_fract).comp
      (measurable_id.div_const T)) measurable_const) measurable_const measurable_const
  have hb : ∀ t, ‖dutyWave ε ε' δ T t‖ ≤ |ε| + |ε'| := fun t => by
    unfold dutyWave
    split_ifs
    · simp only [Real.norm_eq_abs]; linarith [abs_nonneg ε']
    · simp only [Real.norm_eq_abs, abs_neg]; linarith [abs_nonneg ε]
  exact ⟨IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable _
    (Filter.Eventually.of_forall hb), IntegrableOn.of_bound measure_Ioc_lt_top
    hm.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)⟩

@[tmio T, powerlib_foundation] private theorem integral_dutyWave_mul (hT : 0 < T) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t in (0 : ℝ)..T, dutyWave ε ε' δ T t * g t =
      ε * (∫ t in (0 : ℝ)..δ * T, g t) - ε' * ∫ t in δ * T..T, g t := by
  have hdT : δ * T ≤ T := by nlinarith
  have hdT0 : 0 ≤ δ * T := by positivity
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => dutyWave ε ε' δ T t * g t) volume a b :=
    fun a b => (intervalIntegrable_dutyWave ε ε' δ T a b).mul_continuousOn hg.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := δ * T) (hi _ _) (hi _ _),
    intervalIntegral.integral_congr_Ioo_of_le (g := fun t => ε * g t) hdT0 (fun t ht => by
      simp only
      rw [dutyWave_of_mem hT ⟨ht.1.le, ht.2.trans_le hdT⟩]
      simp [ht.2]),
    intervalIntegral.integral_congr_Ioo_of_le (g := fun t => -ε' * g t) hdT (fun t ht => by
      simp only
      rw [dutyWave_of_mem hT ⟨hdT0.trans ht.1.le, ht.2⟩]
      simp [not_lt.mpr ht.1.le]),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- The mean of the duty-`δ` wave over a period: `(1/T) ∫₀ᵀ p = δε − (1 − δ)ε'` (zero exactly in
the zero-mean normalization `δε = (1 − δ)ε'`). -/
@[tmio T, powerlib_foundation] theorem integral_dutyWave (hT : 0 < T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ t in (0 : ℝ)..T, dutyWave ε ε' δ T t = T * (δ * ε - (1 - δ) * ε') := by
  have h := integral_dutyWave_mul (ε := ε) (ε' := ε') hT hδ0 hδ1 (g := fun _ => (1 : ℝ))
    continuous_const
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at h
  rw [h]
  ring

@[tmio T, powerlib_foundation] private theorem integral_trig (hT : 0 < T) (a b : ℝ) :
    (∫ t in a..b, Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * t / T)) =
      T / (2 * Real.pi) * (Real.sin (2 * Real.pi * b / T) - Real.sin (2 * Real.pi * a / T)) ∧
    (∫ t in a..b, Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * t / T)) =
      T / (2 * Real.pi) * (Real.cos (2 * Real.pi * a / T) - Real.cos (2 * Real.pi * b / T)) := by
  have hk : (2 * Real.pi / T) ≠ 0 := by have := Real.pi_pos; positivity
  have ec : (fun t => Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * t / T)) =
      fun t => Real.cos ((2 * Real.pi / T) * t) := by funext t; congr 1; push_cast; ring
  have es : (fun t => Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * t / T)) =
      fun t => Real.sin ((2 * Real.pi / T) * t) := by funext t; congr 1; push_cast; ring
  have ma : 2 * Real.pi / T * a = 2 * Real.pi * a / T := by ring
  have mb : 2 * Real.pi / T * b = 2 * Real.pi * b / T := by ring
  refine ⟨?_, ?_⟩
  · rw [ec, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk, integral_cos, ma, mb,
      smul_eq_mul, inv_div]
  · rw [es, intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hk, integral_sin, ma, mb,
      smul_eq_mul, inv_div]

/-- **The fundamental of the duty-`δ` wave.** `a₁ = (ε + ε') sin(2πδ)/π`,
`b₁ = (ε + ε')(1 − cos(2πδ))/π`; for `δ = 1/2`, `ε' = ε` the square-wave values `0`, `4ε/π`. -/
@[tmio T, powerlib_foundation] theorem fourier_dutyWave (hT : 0 < T) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    cosCoeff T (dutyWave ε ε' δ T) 1 = (ε + ε') * Real.sin (2 * Real.pi * δ) / Real.pi ∧
      sinCoeff T (dutyWave ε ε' δ T) 1 =
        (ε + ε') * (1 - Real.cos (2 * Real.pi * δ)) / Real.pi := by
  have hπ := Real.pi_pos
  have e0 : 2 * Real.pi * 0 / T = 0 := by simp
  have eδ : 2 * Real.pi * (δ * T) / T = 2 * Real.pi * δ := by field_simp
  have eT : 2 * Real.pi * T / T = 2 * Real.pi := by field_simp
  refine ⟨?_, ?_⟩
  · rw [SpecialFunctions.PeriodicWaves.cosCoeff, integral_dutyWave_mul hT hδ0 hδ1
      (by fun_prop), (integral_trig hT _ _).1, (integral_trig hT _ _).1, e0, eδ, eT,
      Real.sin_zero, Real.sin_two_pi]
    field_simp
    ring
  · rw [SpecialFunctions.PeriodicWaves.sinCoeff, integral_dutyWave_mul hT hδ0 hδ1
      (by fun_prop), (integral_trig hT _ _).2, (integral_trig hT _ _).2, e0, eδ, eT,
      Real.cos_zero, Real.cos_two_pi]
    field_simp
    ring

/-- **The amplitude of the fundamental.** `m₁ = (2/π) |sin(πδ)| |ε + ε'|`: the pump seen by the
averaged model; `4|ε|/π` for the symmetric square wave, `→ 0` as `δ → 0` or `δ → 1`. -/
@[tmio T, powerlib_foundation] theorem amp_dutyWave (hT : 0 < T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    amp hT (dutyWave ε ε' δ T) 1 = 2 * |Real.sin (Real.pi * δ)| * |ε + ε'| / Real.pi := by
  have hπ := Real.pi_pos
  obtain ⟨ha, hb⟩ := fourier_dutyWave (ε := ε) (ε' := ε') hT hδ0 hδ1
  rw [SpecialFunctions.PeriodicWaves.amp_eq_sqrt hT (intervalIntegrable_dutyWave _ _ _ _ _ _), ha,
    hb]
  have hs : Real.sin (2 * Real.pi * δ) = 2 * Real.sin (Real.pi * δ) * Real.cos (Real.pi * δ) := by
    rw [show 2 * Real.pi * δ = 2 * (Real.pi * δ) by ring, Real.sin_two_mul]
  have hc : Real.cos (2 * Real.pi * δ) = 1 - 2 * Real.sin (Real.pi * δ) ^ 2 := by
    rw [show 2 * Real.pi * δ = 2 * (Real.pi * δ) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  have e : ((ε + ε') * Real.sin (2 * Real.pi * δ) / Real.pi) ^ 2 +
      ((ε + ε') * (1 - Real.cos (2 * Real.pi * δ)) / Real.pi) ^ 2 =
      (2 * |Real.sin (Real.pi * δ)| * |ε + ε'| / Real.pi) ^ 2 := by
    have h2 : (2 * |Real.sin (Real.pi * δ)| * |ε + ε'| / Real.pi) ^ 2 =
        4 * Real.sin (Real.pi * δ) ^ 2 * (ε + ε') ^ 2 / Real.pi ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, sq_abs, sq_abs]; ring
    rw [h2, hs, hc]
    field_simp
    linear_combination (4 * Real.sin (Real.pi * δ) ^ 2 * (ε + ε') ^ 2) *
      Real.sin_sq_add_cos_sq (Real.pi * δ)
  rw [e, Real.sqrt_sq (by positivity)]

variable {c ω₀ ω : ℝ}

open SquareWave (averagedMatrix) in
/-- **The L2 model of the duty-`δ` oscillator.** For `ẍ + 2cẋ + ω₀²(1 + p(t))x = 0`,
`p = dutyWave ε ε' δ T`, `T = 2π/ω`: the averaged matrix is the 2:1 slow flow with damping `c`,
detuning `Δ = (ω²/4 − ω₀²(1 + δε − (1 − δ)ε'))/ω` and pump
`g = ω₀² (b₁ + j a₁)/(2ω)` from the fundamental of `fourier_dutyWave`
(`SquareWave.averagedMatrix_eq`). -/
@[tmio T, powerlib_foundation] theorem averagedMatrix_dutyWave (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    averagedMatrix c ω₀ ω T (dutyWave ε ε' δ T) = slowFlowMatrix c
      ((ω ^ 2 / 4 - ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε'))) / ω)
      ⟨ω₀ ^ 2 * ((ε + ε') * (1 - Real.cos (2 * Real.pi * δ)) / Real.pi) / (2 * ω),
        ω₀ ^ 2 * ((ε + ε') * Real.sin (2 * Real.pi * δ) / Real.pi) / (2 * ω)⟩ := by
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨ha, hb⟩ := fourier_dutyWave (ε := ε) (ε' := ε') hT0 hδ0 hδ1
  rw [SquareWave.averagedMatrix_eq c ω₀ hω hT (intervalIntegrable_dutyWave _ _ _ _ _ _),
    integral_dutyWave hT0 hδ0 hδ1, ha, hb, inv_mul_cancel_left₀ hT0.ne']

open SquareWave (averagedMatrix) in
/-- **The L2 threshold of the duty-`δ` wave.** With `c ≥ 0` the averaged model has an exponent
with positive real part iff `πω √(c² + Δ²) < ω₀² |ε + ε'| |sin(πδ)|`, and with `c > 0` it is
Hurwitz iff `ω₀² |ε + ε'| |sin(πδ)| < πω √(c² + Δ²)`, `Δ = (ω²/4 − ω₀²(1 + δε − (1 − δ)ε'))/ω`:
only the fundamental `m₁ = (2/π)|sin(πδ)||ε + ε'|` enters, so the L2 threshold on the jump
`ε + ε'` scales with `1/|sin(πδ)|`. -/
@[tmio T, powerlib_foundation] theorem averaged_threshold (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (0 ≤ c → ((∃ μ : ℂ, (Linear.characteristicMatrix
        (averagedMatrix c ω₀ ω T (dutyWave ε ε' δ T)) μ).det = 0 ∧ 0 < μ.re) ↔
      Real.pi * ω * √(c ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε'))) / ω) ^ 2) <
        ω₀ ^ 2 * |ε + ε'| * |Real.sin (Real.pi * δ)|)) ∧
    (0 < c → (LinearSystems.IsHurwitz (averagedMatrix c ω₀ ω T (dutyWave ε ε' δ T)) ↔
      ω₀ ^ 2 * |ε + ε'| * |Real.sin (Real.pi * δ)| <
        Real.pi * ω * √(c ^ 2 + ((ω ^ 2 / 4 - ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε'))) / ω) ^ 2))) := by
  have hT0 : 0 < T := by rw [hT]; positivity
  set Δ := (ω ^ 2 / 4 - ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε'))) / ω
  set g : ℂ := ⟨ω₀ ^ 2 * ((ε + ε') * (1 - Real.cos (2 * Real.pi * δ)) / Real.pi) / (2 * ω),
    ω₀ ^ 2 * ((ε + ε') * Real.sin (2 * Real.pi * δ) / Real.pi) / (2 * ω)⟩ with hgdef
  have hg : ‖g‖ = ω₀ ^ 2 * |ε + ε'| * |Real.sin (Real.pi * δ)| / (Real.pi * ω) := by
    obtain ⟨ha, hb⟩ := fourier_dutyWave (ε := ε) (ε' := ε') hT0 hδ0 hδ1
    have h := SquareWave.norm_pump_eq_amp ω₀ hω hT0 (intervalIntegrable_dutyWave ε ε' δ T 0 T)
    rw [ha, hb, amp_dutyWave hT0 hδ0 hδ1] at h
    rw [hgdef, h]
    field_simp
  have hpω : 0 < Real.pi * ω := by positivity
  have key : ∀ r : ℝ, 0 ≤ r → (r ^ 2 < ‖g‖ ^ 2 ↔
      Real.pi * ω * r < ω₀ ^ 2 * |ε + ε'| * |Real.sin (Real.pi * δ)|) := by
    intro r hr
    rw [hg, pow_lt_pow_iff_left₀ hr (by positivity) two_ne_zero, lt_div_iff₀ hpω, mul_comm]
  have key' : ∀ r : ℝ, 0 ≤ r → (‖g‖ ^ 2 < r ^ 2 ↔
      ω₀ ^ 2 * |ε + ε'| * |Real.sin (Real.pi * δ)| < Real.pi * ω * r) := by
    intro r hr
    rw [hg, pow_lt_pow_iff_left₀ (by positivity) hr two_ne_zero, div_lt_iff₀ hpω, mul_comm r]
  have hsq : √(c ^ 2 + Δ ^ 2) ^ 2 = c ^ 2 + Δ ^ 2 := Real.sq_sqrt (by positivity)
  rw [averagedMatrix_dutyWave hω hT hδ0 hδ1, ← hgdef]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [Branches.slowFlow_unstable_iff, ← key _ (Real.sqrt_nonneg _), hsq]
    constructor
    · rintro (⟨h, -⟩ | ⟨⟨-, h⟩, -⟩)
      · exact absurd hc (not_le.mpr h)
      · exact h
    · intro h; exact Or.inr ⟨⟨hc, h⟩, not_lt.mpr hc⟩
  · rw [Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix, det_slowFlowMatrix,
      ← key' _ (Real.sqrt_nonneg _), hsq]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩

open SquareWave (averagedMatrix) in
/-- **The L2 threshold at the 2:1 resonance, zero-mean normalization.** With `δε = (1 − δ)ε'`
(the stiffness has mean `ω₀²`), `c = ξω₀` and the pump at `ω = 2ω₀` (`Δ = 0`): the averaged model
is unstable iff `2πξ < |ε + ε'| |sin(πδ)|` (`ξ ≥ 0`) and Hurwitz iff `|ε + ε'| |sin(πδ)| < 2πξ`
(`ξ > 0`). For `δ = 1/2`, `ε' = ε` this is `ε ≷ πξ` (`SquareWave.averaged_centre_threshold`). -/
@[tmio T, powerlib_foundation] theorem averaged_centre_threshold {ξ : ℝ} (hω₀ : 0 < ω₀)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmean : δ * ε = (1 - δ) * ε') :
    (0 ≤ ξ → ((∃ μ : ℂ, (Linear.characteristicMatrix (averagedMatrix (ξ * ω₀) ω₀ (2 * ω₀)
        (2 * Real.pi / (2 * ω₀)) (dutyWave ε ε' δ (2 * Real.pi / (2 * ω₀)))) μ).det = 0 ∧
          0 < μ.re) ↔ 2 * Real.pi * ξ < |ε + ε'| * |Real.sin (Real.pi * δ)|)) ∧
    (0 < ξ → (LinearSystems.IsHurwitz (averagedMatrix (ξ * ω₀) ω₀ (2 * ω₀)
        (2 * Real.pi / (2 * ω₀)) (dutyWave ε ε' δ (2 * Real.pi / (2 * ω₀)))) ↔
      |ε + ε'| * |Real.sin (Real.pi * δ)| < 2 * Real.pi * ξ)) := by
  obtain ⟨hU, hS⟩ := averaged_threshold (c := ξ * ω₀) (ω₀ := ω₀) (ε := ε) (ε' := ε')
    (by positivity : (0 : ℝ) < 2 * ω₀) rfl hδ0 hδ1
  have hΔ : ((2 * ω₀) ^ 2 / 4 - ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε'))) / (2 * ω₀) = 0 := by
    rw [hmean]; ring_nf
  rw [hΔ] at hU hS
  have e : ∀ ξ' : ℝ, 0 ≤ ξ' → Real.pi * (2 * ω₀) * √((ξ' * ω₀) ^ 2 + 0 ^ 2) =
      (2 * Real.pi * ξ') * ω₀ ^ 2 := fun ξ' h => by
    rw [show (ξ' * ω₀) ^ 2 + (0 : ℝ) ^ 2 = (ξ' * ω₀) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    ring
  have e' : ω₀ ^ 2 * |ε + ε'| * |Real.sin (Real.pi * δ)| =
      (|ε + ε'| * |Real.sin (Real.pi * δ)|) * ω₀ ^ 2 := by ring
  have h2 : (0 : ℝ) < ω₀ ^ 2 := by positivity
  refine ⟨fun hξ => ?_, fun hξ => ?_⟩
  · rw [hU (by positivity), e ξ hξ, e', mul_lt_mul_iff_left₀ h2]
  · rw [hS (by positivity), e ξ hξ.le, e', mul_lt_mul_iff_left₀ h2]

end Averaged

/-! ## All levels agree below the universal curve -/

section Levels

variable {c ω₀ ε ε' η δ : ℝ}

open SquareWave (averagedMatrix) in
/-- **The universal region at every level, for every duty ratio.** Let `ω₀ > 0`, both depths
`|ε|, |ε'| ≤ η < 1` and `η / √(1 − η) < 2c/ω₀` (`= 2ξ`), `δ ∈ [0, 1]`. Then:
* L3: both frozen matrices `oscMatrix c (ω₀²(1 + ε))`, `oscMatrix c (ω₀²(1 − ε'))` are Hurwitz;
* L1: the exact monodromy is Schur stable for every period `T > 0`;
* L2: the averaged matrix is Hurwitz at every pump frequency `ω` with `4ω₀√(1 − η) ≤ πω`, since
  `ω₀² |ε + ε'| |sin(πδ)| ≤ 2ηω₀² < 4cω₀√(1 − η) ≤ πωc ≤ πω√(c² + Δ²)`. -/
@[tmio T, powerlib_foundation] theorem levels_agree_of_universal (hω : 0 < ω₀) (hη1 : η < 1)
    (hε : |ε| ≤ η) (hε' : |ε'| ≤ η) (hξ : η / √(1 - η) < 2 * c / ω₀) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    LinearSystems.IsHurwitz (oscMatrix c (ω₀ ^ 2 * (1 + ε))) ∧
      LinearSystems.IsHurwitz (oscMatrix c (ω₀ ^ 2 * (1 - ε'))) ∧
      (∀ T : ℝ, 0 < T →
        LTI.SchurStable (dutyMonodromy c (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T)) ∧
      ∀ ω T : ℝ, 0 < ω → T = 2 * Real.pi / ω → 4 * ω₀ * √(1 - η) ≤ Real.pi * ω →
        LinearSystems.IsHurwitz (averagedMatrix c ω₀ ω T (dutyWave ε ε' δ T)) := by
  have hη : 0 ≤ η := (abs_nonneg ε).trans hε
  have hr : 0 < √(1 - η) := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 < c := by
    have h0 : 0 ≤ η / √(1 - η) := by positivity
    have := h0.trans_lt hξ
    have h2 : 0 < 2 * c := (div_pos_iff_of_pos_right hω).mp this
    linarith
  have hfrozen : ∀ σ : ℝ, |σ| ≤ η → LinearSystems.IsHurwitz (oscMatrix c (ω₀ ^ 2 * (1 + σ))) := by
    intro σ hσ
    rw [Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix, Periodic.det_oscMatrix]
    have := (abs_le.mp hσ).1
    exact ⟨by linarith, by have : 0 < 1 + σ := by linarith
                           positivity⟩
  refine ⟨hfrozen ε hε, ?_, fun T hT => schurStable_of_universal hω hη1 hε hε' hξ hδ0 hδ1 hT,
    fun ω T hω' hT hΩ => ?_⟩
  · rw [show ω₀ ^ 2 * (1 - ε') = ω₀ ^ 2 * (1 + -ε') by ring]
    exact hfrozen (-ε') (by rwa [abs_neg])
  · rw [(averaged_threshold hω' hT hδ0 hδ1).2 hc]
    set Δ := (ω ^ 2 / 4 - ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε'))) / ω
    have h1 : η * ω₀ < 2 * c * √(1 - η) := by
      rw [div_lt_div_iff₀ hr hω] at hξ; linarith
    have hsum : |ε + ε'| * |Real.sin (Real.pi * δ)| ≤ 2 * η := by
      have h3 : |ε + ε'| ≤ 2 * η := (abs_add_le ε ε').trans (by linarith)
      have h4 : |Real.sin (Real.pi * δ)| ≤ 1 := Real.abs_sin_le_one _
      nlinarith [abs_nonneg (ε + ε'), abs_nonneg (Real.sin (Real.pi * δ))]
    have h2 : c ≤ √(c ^ 2 + Δ ^ 2) :=
      calc c = √(c ^ 2) := (Real.sqrt_sq hc.le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Δ])
    calc ω₀ ^ 2 * |ε + ε'| * |Real.sin (Real.pi * δ)|
        = ω₀ ^ 2 * (|ε + ε'| * |Real.sin (Real.pi * δ)|) := by ring
      _ ≤ ω₀ ^ 2 * (2 * η) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * ω₀ * (η * ω₀) := by ring
      _ < 2 * ω₀ * (2 * c * √(1 - η)) := mul_lt_mul_of_pos_left h1 (by positivity)
      _ = (4 * ω₀ * √(1 - η)) * c := by ring
      _ ≤ (Real.pi * ω) * c := mul_le_mul_of_nonneg_right hΩ hc.le
      _ ≤ Real.pi * ω * √(c ^ 2 + Δ ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)

end Levels

/-! ## First-order agreement at the centre of the general-duty tongue -/

section Cone

@[tmio T, powerlib_foundation] private theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have h1 : ∫ t in (0 : ℝ)..x, Real.cosh t = Real.sinh x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.sinh)
      (fun t _ => Real.hasDerivAt_sinh t) (Real.continuous_cosh.intervalIntegrable _ _),
      Real.sinh_zero, sub_zero]
  have h2 : ∫ t in (0 : ℝ)..x, Real.cosh t ≤ ∫ _ in (0 : ℝ)..x, Real.cosh x :=
    intervalIntegral.integral_mono_on hx (Real.continuous_cosh.intervalIntegrable _ _)
      intervalIntegrable_const (fun t ht => Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg ht.1, abs_of_nonneg hx]; exact ht.2))
  rw [h1, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h2
  exact h2

variable {c ω₀ ε ε' δ T ν₁ ν₂ : ℝ}

/-- **The centre threshold for every duty ratio, in the depth.** At `ν₁δT + ν₂(1 − δ)T = π`
(levels `ω₀²(1 + ε)`, `ω₀²(1 − ε')`, `ε + ε' ≥ 0`, `c ≥ 0`): Floquet instability iff
`2√(ν₁ν₂)(ν₁ + ν₂) sinh(cT/2) < (ε + ε') ω₀² |sin θ₁|`, `θ₁ = ν₁δT`, and for `c > 0` Schur
stability iff the reverse strict inequality holds; at `δ = 1/2`, `ε' = ε` this is
`Meissner.centre_threshold_iff` (`cT/2 = πc/(ν₁ + ν₂)`). -/
@[tmio T, powerlib_foundation] theorem centre_threshold_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε') - c ^ 2)
    (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) (hc : 0 ≤ c) (hT : 0 < T) (hεε : 0 ≤ ε + ε')
    (hθ : ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi) :
    ((∃ μ ∈ spectrum ℂ ((dutyMonodromy c (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T).map
        (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      2 * √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (c * T / 2) <
        (ε + ε') * ω₀ ^ 2 * |Real.sin (ν₁ * (δ * T))|) ∧
    (0 < c → (LTI.SchurStable (dutyMonodromy c (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T) ↔
      (ε + ε') * ω₀ ^ 2 * |Real.sin (ν₁ * (δ * T))| <
        2 * √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (c * T / 2))) := by
  obtain ⟨hU, hS⟩ := centre_floquet_iff hν₁ hν₂ h₁ h₂ hc hT hθ
  have hs : 0 < ν₁ + ν₂ := by linarith
  have hp : 0 < ν₁ * ν₂ := mul_pos h₁ h₂
  have hdiff : ν₁ - ν₂ = (ε + ε') * ω₀ ^ 2 / (ν₁ + ν₂) := by
    field_simp; nlinarith
  have hsh : 0 ≤ Real.sinh (c * T / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq : √(ν₁ * ν₂) ^ 2 = ν₁ * ν₂ := Real.sq_sqrt hp.le
  set L := 2 * √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (c * T / 2)
  set R := (ε + ε') * ω₀ ^ 2 * |Real.sin (ν₁ * (δ * T))|
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by positivity
  have e1 : 4 * (ν₁ * ν₂) * Real.sinh (c * T / 2) ^ 2 = L ^ 2 / (ν₁ + ν₂) ^ 2 := by
    simp only [L]; rw [mul_pow, mul_pow, mul_pow, hsq]; field_simp; ring
  have e2 : (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * (δ * T)) ^ 2 = R ^ 2 / (ν₁ + ν₂) ^ 2 := by
    simp only [R]; rw [hdiff, mul_pow, mul_pow, sq_abs]; field_simp
  rw [e1, e2, div_lt_div_iff_of_pos_right (by positivity)] at hU
  refine ⟨hU.trans (pow_lt_pow_iff_left₀ hL hR two_ne_zero), fun hc' => ?_⟩
  rw [(hS hc'), e1, e2, div_lt_div_iff_of_pos_right (by positivity)]
  exact pow_lt_pow_iff_left₀ hR hL two_ne_zero

/-- **First-order agreement at the centre of the duty-`δ` tongue: the threshold
`(ε + ε') sin(πδ) = 2πξ`.** Fix `δ ∈ (0, 1)`. For every `η > 0` there is `ρ > 0` such that for
`ω₀ > 0`, damping `c = ξω₀` with `0 < ξ < ρ`, depths `0 ≤ ε, ε' < ρ`, both levels oscillatory and
the pump at the centre `ν₁δT + ν₂(1 − δ)T = π`:
* `(2π + η)ξ < (ε + ε') sin(πδ)` gives Floquet instability;
* `(ε + ε') sin(πδ) < (2π − η)ξ` gives Schur stability.
The exact threshold on the jump `ε + ε'` is `2πξ/sin(πδ) (1 + o(1))`, the L2 value of
`averaged_centre_threshold`; for `δ = 1/2`, `ε' = ε` it is `SquareWave.centre_threshold_ratio`. -/
@[tmio T, powerlib_foundation] theorem centre_threshold_ratio {η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ ω₀ ξ ε ε' ν₁ ν₂ T : ℝ, 0 < ω₀ → 0 < ξ → ξ < ρ → 0 ≤ ε → ε < ρ → 0 ≤ ε' →
      ε' < ρ → ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 →
      ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2 → 0 < ν₁ → 0 < ν₂ →
      ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi →
      ((2 * Real.pi + η) * ξ < (ε + ε') * Real.sin (Real.pi * δ) →
        ∃ μ ∈ spectrum ℂ ((dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ
          T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ∧
      ((ε + ε') * Real.sin (Real.pi * δ) < (2 * Real.pi - η) * ξ →
        LTI.SchurStable (dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T)) := by
  have hπ := Real.pi_pos
  have hsinδ : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  set κ := η / (4 * Real.pi + η) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one (by positivity)]; linarith
  have hκη : κ * (4 * Real.pi + η) = η := by rw [hκ]; field_simp
  -- the normalized factors as functions of `q = (ξ, ε, ε')`
  obtain ⟨A, hA⟩ : ∃ A : ℝ × ℝ × ℝ → ℝ, A = fun q => √(1 + q.2.1 - q.1 ^ 2) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ × ℝ × ℝ → ℝ, B = fun q => √(1 - q.2.2 - q.1 ^ 2) := ⟨_, rfl⟩
  obtain ⟨Mf, hMf⟩ : ∃ Mf : ℝ × ℝ × ℝ → ℝ, Mf = fun q => A q * δ + B q * (1 - δ) := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : ℝ × ℝ × ℝ → ℝ,
      F₁ = fun q => |Real.sin (Real.pi * A q * δ / Mf q)| := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : ℝ × ℝ × ℝ → ℝ, F₂ = fun q =>
      √(A q * B q) * (A q + B q) * Real.cosh (Real.pi * q.1 / (2 * Mf q)) / Mf q := ⟨_, rfl⟩
  obtain ⟨F₃, hF₃⟩ : ∃ F₃ : ℝ × ℝ × ℝ → ℝ, F₃ = fun q => √(A q * B q) * (A q + B q) / Mf q :=
    ⟨_, rfl⟩
  have hA0 : A 0 = 1 := by rw [hA]; simp
  have hB0 : B 0 = 1 := by rw [hB]; simp
  have hM0 : Mf 0 = 1 := by rw [hMf]; simp only [hA0, hB0]; ring
  have cA : Continuous A := by rw [hA]; fun_prop
  have cB : Continuous B := by rw [hB]; fun_prop
  have cM : Continuous Mf := by rw [hMf]; fun_prop
  have hMne : Mf 0 ≠ 0 := by rw [hM0]; norm_num
  have cF₁ : ContinuousAt F₁ 0 := by
    have h : ContinuousAt (fun q => Real.pi * A q * δ / Mf q) 0 :=
      (((continuous_const.mul cA).mul continuous_const).continuousAt).div cM.continuousAt hMne
    rw [hF₁]
    exact (Real.continuous_sin.continuousAt.comp h).abs
  have cF₃ : ContinuousAt F₃ 0 := by
    have h0 : Continuous fun q => √(A q * B q) * (A q + B q) :=
      ((cA.mul cB).sqrt).mul (cA.add cB)
    rw [hF₃]
    exact h0.continuousAt.div cM.continuousAt hMne
  have cF₂ : ContinuousAt F₂ 0 := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ × ℝ => Real.pi * q.1 / (2 * Mf q)) 0 :=
      (continuous_const.mul continuous_fst).continuousAt.div
        (continuous_const.mul cM).continuousAt (by rw [hM0]; norm_num)
    have h2 : ContinuousAt (fun q : ℝ × ℝ × ℝ => Real.cosh (Real.pi * q.1 / (2 * Mf q))) 0 :=
      Real.continuous_cosh.continuousAt.comp h1
    have h0 : Continuous fun q => √(A q * B q) * (A q + B q) :=
      ((cA.mul cB).sqrt).mul (cA.add cB)
    rw [hF₂]
    exact (h0.continuousAt.mul h2).div cM.continuousAt hMne
  have v₁ : F₁ 0 = Real.sin (Real.pi * δ) := by
    rw [hF₁]; simp only [hA0, hM0, mul_one, div_one]; exact abs_of_pos hsinδ
  have v₂ : F₂ 0 = 2 := by rw [hF₂]; simp only [hA0, hB0, hM0]; norm_num
  have v₃ : F₃ 0 = 2 := by rw [hF₃]; simp only [hA0, hB0, hM0]; norm_num
  have ev : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ × ℝ),
      dist (F₁ q) (F₁ 0) < κ * Real.sin (Real.pi * δ) ∧ F₂ q < 2 * (1 + κ) ∧
        2 * (1 - κ) < F₃ q := by
    refine (Metric.tendsto_nhds.mp cF₁.tendsto _ (by positivity)).and
      ((cF₂.tendsto.eventually_lt_const (by rw [v₂]; linarith)).and
        (cF₃.tendsto.eventually_const_lt (by rw [v₃]; linarith)))
  obtain ⟨ρ, hρ, hP⟩ := Metric.eventually_nhds_iff.mp ev
  refine ⟨ρ, hρ, fun ω₀ ξ ε ε' ν₁ ν₂ T hω hξ hξρ hε hερ hε' hε'ρ hν₁ hν₂ h₁ h₂ hθ => ?_⟩
  set q : ℝ × ℝ × ℝ := (ξ, ε, ε')
  obtain ⟨b₁, b₂, b₃⟩ := hP (y := q) (by
    simp only [q, Prod.dist_eq, Real.dist_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
    exact max_lt (by rw [abs_of_pos hξ]; exact hξρ)
      (max_lt (by rw [abs_of_nonneg hε]; exact hερ) (by rw [abs_of_nonneg hε']; exact hε'ρ)))
  rw [v₁, Real.dist_eq] at b₁
  -- the normalized frequencies
  obtain ⟨a, hadef⟩ : ∃ a, a = A q := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = B q := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = Mf q := ⟨_, rfl⟩
  have ha : ν₁ = ω₀ * a := by
    rw [hadef, hA]
    simp only [q]
    rw [← Real.sqrt_sq h₁.le, hν₁, show ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 =
      ω₀ ^ 2 * (1 + ε - ξ ^ 2) by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω.le]
  have hb : ν₂ = ω₀ * b := by
    rw [hbdef, hB]
    simp only [q]
    rw [← Real.sqrt_sq h₂.le, hν₂, show ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2 =
      ω₀ ^ 2 * (1 - ε' - ξ ^ 2) by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω.le]
  have ha0 : 0 < a := by have := h₁; rw [ha] at this; exact pos_of_mul_pos_right this hω.le
  have hb0 : 0 < b := by have := h₂; rw [hb] at this; exact pos_of_mul_pos_right this hω.le
  have hm : m = a * δ + b * (1 - δ) := by rw [hmdef, hMf, hadef, hbdef]
  have hF₁q : F₁ q = |Real.sin (Real.pi * a * δ / m)| := by rw [hF₁, hadef, hmdef]
  have hF₂q : F₂ q = √(a * b) * (a + b) * Real.cosh (Real.pi * ξ / (2 * m)) / m := by
    rw [hF₂, hadef, hbdef, hmdef]
  have hF₃q : F₃ q = √(a * b) * (a + b) / m := by rw [hF₃, hadef, hbdef, hmdef]
  have hm0 : 0 < m := by rw [hm]; nlinarith
  have hTm : T = Real.pi / (ω₀ * m) := by
    rw [eq_div_iff (by positivity), hm]
    rw [ha, hb] at hθ; linarith
  have hT : 0 < T := by rw [hTm]; positivity
  -- the two sides of the exact criterion, divided by `ω₀²`
  obtain ⟨x, hxdef⟩ : ∃ x, x = Real.pi * ξ / (2 * m) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hcT : ξ * ω₀ * T / 2 = x := by rw [hTm, hxdef]; field_simp
  have hθ₁ : ν₁ * (δ * T) = Real.pi * a * δ / m := by rw [hTm, ha]; field_simp
  have hroot : √(ν₁ * ν₂) = ω₀ * √(a * b) := by
    rw [ha, hb, show ω₀ * a * (ω₀ * b) = ω₀ ^ 2 * (a * b) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hω.le]
  have hLe : 2 * √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (ξ * ω₀ * T / 2) =
      ω₀ ^ 2 * (2 * √(a * b) * (a + b) * Real.sinh x) := by
    rw [hroot, hcT, ha, hb]; ring
  have hRe : (ε + ε') * ω₀ ^ 2 * |Real.sin (ν₁ * (δ * T))| = ω₀ ^ 2 * ((ε + ε') * F₁ q) := by
    rw [hθ₁, hF₁q]; ring
  have hab : 0 ≤ √(a * b) * (a + b) := by positivity
  have hup : 2 * √(a * b) * (a + b) * Real.sinh x ≤ Real.pi * ξ * F₂ q := by
    have := mul_le_mul_of_nonneg_left (sinh_le_mul_cosh hx0) (by positivity :
      (0 : ℝ) ≤ 2 * √(a * b) * (a + b))
    calc 2 * √(a * b) * (a + b) * Real.sinh x ≤ 2 * √(a * b) * (a + b) * (x * Real.cosh x) := this
      _ = Real.pi * ξ * F₂ q := by rw [hF₂q, hxdef]; field_simp
  have hlo : Real.pi * ξ * F₃ q ≤ 2 * √(a * b) * (a + b) * Real.sinh x := by
    have := mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr hx0) (by positivity :
      (0 : ℝ) ≤ 2 * √(a * b) * (a + b))
    calc Real.pi * ξ * F₃ q = 2 * √(a * b) * (a + b) * x := by rw [hF₃q, hxdef]; field_simp
      _ ≤ _ := this
  have hω2 : 0 < ω₀ ^ 2 := by positivity
  have hεε : 0 ≤ ε + ε' := by linarith
  obtain ⟨hU, hS⟩ := centre_threshold_iff (c := ξ * ω₀) hν₁ hν₂ h₁ h₂ (by positivity) hT hεε hθ
  refine ⟨fun h => hU.mpr ?_, fun h => (hS (by positivity)).mpr ?_⟩
  · rw [hLe, hRe, mul_lt_mul_iff_right₀ hω2]
    refine hup.trans_lt ?_
    have hεpos : 0 < ε + ε' := by
      by_contra hn; push Not at hn
      have : (ε + ε') * Real.sin (Real.pi * δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn hsinδ.le
      have : 0 < (2 * Real.pi + η) * ξ := by positivity
      linarith
    have hF₁lo : Real.sin (Real.pi * δ) * (1 - κ) ≤ F₁ q := by
      have := (abs_lt.mp b₁).1; linarith
    calc Real.pi * ξ * F₂ q ≤ Real.pi * ξ * (2 * (1 + κ)) :=
          mul_le_mul_of_nonneg_left b₂.le (by positivity)
      _ ≤ (2 * Real.pi + η) * ξ * (1 - κ) := by
          have e : (2 * Real.pi + η) * ξ * (1 - κ) - Real.pi * ξ * (2 * (1 + κ)) =
              ξ * (η - κ * (4 * Real.pi + η)) := by ring
          rw [hκη, sub_self, mul_zero] at e
          linarith
      _ < (ε + ε') * Real.sin (Real.pi * δ) * (1 - κ) :=
          mul_lt_mul_of_pos_right h (by linarith)
      _ = (ε + ε') * (Real.sin (Real.pi * δ) * (1 - κ)) := by ring
      _ ≤ (ε + ε') * F₁ q := mul_le_mul_of_nonneg_left hF₁lo hεpos.le
  · rw [hLe, hRe, mul_lt_mul_iff_right₀ hω2]
    refine lt_of_lt_of_le ?_ hlo
    have hF₁hi : F₁ q ≤ Real.sin (Real.pi * δ) * (1 + κ) := by
      have := (abs_lt.mp b₁).2; linarith
    calc (ε + ε') * F₁ q ≤ (ε + ε') * (Real.sin (Real.pi * δ) * (1 + κ)) :=
          mul_le_mul_of_nonneg_left hF₁hi hεε
      _ = (ε + ε') * Real.sin (Real.pi * δ) * (1 + κ) := by ring
      _ ≤ (2 * Real.pi - η) * ξ * (1 + κ) := mul_le_mul_of_nonneg_right h.le (by linarith)
      _ < Real.pi * ξ * (2 * (1 - κ)) := by
          have e : Real.pi * ξ * (2 * (1 - κ)) - (2 * Real.pi - η) * ξ * (1 + κ) =
              ξ * (η - κ * (4 * Real.pi + η)) + 2 * η * κ * ξ := by ring
          rw [hκη, sub_self, mul_zero, zero_add] at e
          have : 0 < 2 * η * κ * ξ := by positivity
          linarith
      _ < Real.pi * ξ * F₃ q := mul_lt_mul_of_pos_left b₃ (by positivity)

end Cone

/-! ## Averaging across a switching instant at `δT`: the L2 verdict predicts L1 -/

section TwoPiece

/-- The warp `φ(s) = s − sin(2πs)/(2π)` of `[0, 1]`: `φ(0) = 0`, `φ(1) = 1`, `φ' = 1 − cos(2πs)`
vanishes at both ends. -/
def warp (s : ℝ) : ℝ := s - Real.sin (2 * Real.pi * s) / (2 * Real.pi)

/-- The time change of the piece `[a, a + L]`: `τ(t) = a + L φ((t − a)/L)`, with
`τ(a) = a`, `τ(a + L) = a + L` and `τ'(a) = τ'(a + L) = 0`. -/
def reparamOn (a L t : ℝ) : ℝ := a + L * warp ((t - a) / L)

/-- `τ'(t) = 1 − cos(2π(t − a)/L)`. -/
def reparamOnDeriv (a L t : ℝ) : ℝ := 1 - Real.cos (2 * Real.pi * ((t - a) / L))

/-- The two-piece field with the switching instant at `δT`, run with the time changes of the two
pieces: `τ₁'(t) G₁(τ₁(t))` on `[0, δT]`, `τ₂'(t) G₂(τ₂(t))` after; continuous because both
`τ'` vanish at `δT`. For `δ = 1/2` this is the construction of `SquareWave.twoPiece`. -/
def twoPieceDuty (G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (δ T t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  if t ≤ δ * T then reparamOnDeriv 0 (δ * T) t • G₁ (reparamOn 0 (δ * T) t)
  else reparamOnDeriv (δ * T) ((1 - δ) * T) t • G₂ (reparamOn (δ * T) ((1 - δ) * T) t)

section Reparam

variable {a L : ℝ}

@[tmio T, powerlib_foundation] theorem hasDerivAt_reparamOn (hL : 0 < L) (t : ℝ) :
    HasDerivAt (reparamOn a L) (reparamOnDeriv a L t) t := by
  have hπ := Real.pi_pos
  have h1 : HasDerivAt (fun t => 2 * Real.pi * ((t - a) / L)) (2 * Real.pi / L) t := by
    have := (((hasDerivAt_id t).sub_const a).div_const L).const_mul (2 * Real.pi)
    convert this using 1
    · funext s; simp
    · ring
  have h2 : HasDerivAt (fun t => (t - a) / L) (1 / L) t := by
    simpa using ((hasDerivAt_id t).sub_const a).div_const L
  have h3 := (h2.sub ((Real.hasDerivAt_sin _).comp t h1 |>.div_const (2 * Real.pi))).const_mul L
  have h4 := h3.const_add a
  convert h4 using 1
  · funext s; simp [reparamOn, warp]
  · simp only [reparamOnDeriv]; field_simp

@[tmio T, powerlib_foundation] theorem continuous_reparamOn : Continuous (reparamOn a L) := by
  unfold reparamOn warp; fun_prop

@[tmio T, powerlib_foundation] theorem continuous_reparamOnDeriv :
    Continuous (reparamOnDeriv a L) := by
  unfold reparamOnDeriv; fun_prop

@[tmio T, powerlib_foundation] theorem reparamOn_left : reparamOn a L a = a := by
  simp [reparamOn, warp]

@[tmio T, powerlib_foundation] theorem reparamOn_right (hL : 0 < L) :
    reparamOn a L (a + L) = a + L := by
  rw [reparamOn, warp, add_sub_cancel_left, div_self hL.ne']
  simp

@[tmio T, powerlib_foundation] theorem reparamOnDeriv_left : reparamOnDeriv a L a = 0 := by
  simp [reparamOnDeriv]

@[tmio T, powerlib_foundation] theorem reparamOnDeriv_right (hL : 0 < L) :
    reparamOnDeriv a L (a + L) = 0 := by
  rw [reparamOnDeriv, add_sub_cancel_left, div_self hL.ne']
  simp

@[tmio T, powerlib_foundation] theorem abs_reparamOnDeriv_le (t : ℝ) :
    |reparamOnDeriv a L t| ≤ 2 := by
  have := Real.neg_one_le_cos (2 * Real.pi * ((t - a) / L))
  have := Real.cos_le_one (2 * Real.pi * ((t - a) / L))
  unfold reparamOnDeriv
  rw [abs_le]; constructor <;> linarith

end Reparam

variable {δ T : ℝ} {G₁ G₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ}

@[tmio T, powerlib_foundation] private theorem pieces (hδ0 : 0 < δ) (hδ1 : δ < 1) (hT : 0 < T) :
    0 < δ * T ∧ 0 < (1 - δ) * T ∧ δ * T + (1 - δ) * T = T ∧ (0 : ℝ) + δ * T = δ * T := by
  refine ⟨by positivity, mul_pos (by linarith) hT, by ring, by ring⟩

@[tmio T, powerlib_foundation] theorem continuous_twoPieceDuty (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT : 0 < T) (h₁ : Continuous G₁) (h₂ : Continuous G₂) :
    Continuous (twoPieceDuty G₁ G₂ δ T) := by
  obtain ⟨hp, hq, _, h0⟩ := pieces hδ0 hδ1 hT
  refine Continuous.if_le (continuous_reparamOnDeriv.smul (h₁.comp continuous_reparamOn))
    (continuous_reparamOnDeriv.smul (h₂.comp continuous_reparamOn)) continuous_id continuous_const
    ?_
  intro t ht
  have ht' : t = δ * T := ht
  have e1 : reparamOnDeriv 0 (δ * T) t = 0 := by
    rw [ht']; have := reparamOnDeriv_right (a := 0) hp; rwa [h0] at this
  have e2 : reparamOnDeriv (δ * T) ((1 - δ) * T) t = 0 := by rw [ht']; exact reparamOnDeriv_left
  rw [e1, e2, zero_smul, zero_smul]

@[tmio T, powerlib_foundation] theorem norm_twoPieceDuty_le {M : ℝ} (hM₁ : ∀ t, ‖G₁ t‖ ≤ M)
    (hM₂ : ∀ t, ‖G₂ t‖ ≤ M) (t : ℝ) : ‖twoPieceDuty G₁ G₂ δ T t‖ ≤ 2 * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hM₁ 0)
  unfold twoPieceDuty
  split_ifs
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_reparamOnDeriv_le t) (hM₁ _) (norm_nonneg _) (by norm_num)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_reparamOnDeriv_le t) (hM₂ _) (norm_nonneg _) (by norm_num)

/-- `∫₀ᵀ F = ∫₀^{δT} G₁ + ∫_{δT}^T G₂`: the time changes keep the averages of both pieces. -/
@[tmio T, powerlib_foundation] theorem integral_twoPieceDuty (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT : 0 < T) (h₁ : Continuous G₁) (h₂ : Continuous G₂) :
    ∫ t in (0 : ℝ)..T, twoPieceDuty G₁ G₂ δ T t =
      (∫ t in (0 : ℝ)..δ * T, G₁ t) + ∫ t in δ * T..T, G₂ t := by
  obtain ⟨hp, hq, hs, h0⟩ := pieces hδ0 hδ1 hT
  have hc := continuous_twoPieceDuty hδ0 hδ1 hT h₁ h₂
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := δ * T) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in (0 : ℝ)..δ * T, twoPieceDuty G₁ G₂ δ T t =
      ∫ t in (0 : ℝ)..δ * T, reparamOnDeriv 0 (δ * T) t • (G₁ ∘ reparamOn 0 (δ * T)) t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hp.le] at ht
    simp only [twoPieceDuty, ht.2, ↓reduceIte, Function.comp]
  have e2 : ∫ t in δ * T..T, twoPieceDuty G₁ G₂ δ T t =
      ∫ t in δ * T..T, reparamOnDeriv (δ * T) ((1 - δ) * T) t •
        (G₂ ∘ reparamOn (δ * T) ((1 - δ) * T)) t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith)] at ht
    rcases ht.1.eq_or_lt with h | h
    · subst h
      have e : reparamOnDeriv 0 (δ * T) (δ * T) = 0 := by
        have := reparamOnDeriv_right (a := 0) hp; rwa [h0] at this
      simp only [twoPieceDuty, le_refl, ↓reduceIte, e, reparamOnDeriv_left, zero_smul]
    · simp only [twoPieceDuty, not_le.mpr h, ↓reduceIte, Function.comp]
  rw [e1, e2, intervalIntegral.integral_deriv_smul_comp (fun t _ => hasDerivAt_reparamOn hp t)
      continuous_reparamOnDeriv.continuousOn h₁,
    intervalIntegral.integral_deriv_smul_comp (fun t _ => hasDerivAt_reparamOn hq t)
      continuous_reparamOnDeriv.continuousOn h₂, reparamOn_left, reparamOn_left]
  have r1 : reparamOn 0 (δ * T) (δ * T) = δ * T := by
    have := reparamOn_right (a := 0) hp; rwa [h0] at this
  have r2 : reparamOn (δ * T) ((1 - δ) * T) T = T := by
    have := reparamOn_right (a := δ * T) hq; rwa [hs] at this
  rw [r1, r2]

/-- **The time changes realize the switched transition at `δT`.** For continuous bounded `G₁`,
`G₂` and `δ ∈ (0, 1)`: the transition matrix of the continuous field `twoPieceDuty G₁ G₂ δ T`
over `[0, T]` is `Φ_{G₂}(T, δT) Φ_{G₁}(δT, 0)`. -/
@[tmio T, powerlib_foundation] theorem transition_twoPieceDuty (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT : 0 < T) {M : ℝ} (h₁ : Continuous G₁) (h₂ : Continuous G₂) (hM₁ : ∀ t, ‖G₁ t‖ ≤ M)
    (hM₂ : ∀ t, ‖G₂ t‖ ≤ M) :
    Periodic.transition (twoPieceDuty G₁ G₂ δ T) T 0 =
      Periodic.transition G₂ T (δ * T) * Periodic.transition G₁ (δ * T) 0 := by
  obtain ⟨hp, hq, hs, h0⟩ := pieces hδ0 hδ1 hT
  set a := δ * T with ha
  set C := Periodic.transition G₁ a 0
  set Y₁ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => Periodic.transition G₁ (reparamOn 0 a t) 0
  set Y₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => Periodic.transition G₂ (reparamOn a ((1 - δ) * T) t) a * C
  set Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => if t ≤ a then Y₁ t else Y₂ t
  have r1 : reparamOn 0 a a = a := by have := reparamOn_right (a := 0) hp; rwa [h0] at this
  have r2 : reparamOn a ((1 - δ) * T) a = a := reparamOn_left
  have d1z : reparamOnDeriv 0 a a = 0 := by
    have := reparamOnDeriv_right (a := 0) hp; rwa [h0] at this
  have d2z : reparamOnDeriv a ((1 - δ) * T) a = 0 := reparamOnDeriv_left
  have d₁ : ∀ t, HasDerivAt Y₁ (reparamOnDeriv 0 a t • (G₁ (reparamOn 0 a t) * Y₁ t)) t := fun t =>
    (Dynamics.stm_hasDerivAt h₁ (reparamOn 0 a t) 0).scomp t (hasDerivAt_reparamOn hp t)
  have d₂ : ∀ t, HasDerivAt Y₂ (reparamOnDeriv a ((1 - δ) * T) t • (G₂ (reparamOn a ((1 - δ) * T) t) * Y₂ t)) t :=
    fun t => by
      have h := ((Dynamics.stm_hasDerivAt h₂ (reparamOn a ((1 - δ) * T) t) a).scomp t
        (hasDerivAt_reparamOn hq t)).mul_const C
      have e : (reparamOnDeriv a ((1 - δ) * T) t • (G₂ (reparamOn a ((1 - δ) * T) t) *
          LinearSystems.stateTransitionMatrix G₂ (reparamOn a ((1 - δ) * T) t) a)) * C =
          reparamOnDeriv a ((1 - δ) * T) t • (G₂ (reparamOn a ((1 - δ) * T) t) * Y₂ t) := by
        simp only [Y₂, smul_mul_assoc, Matrix.mul_assoc]
      exact h.congr_deriv e
  have hjoin : Y₁ a = Y₂ a := by
    simp only [Y₁, Y₂, C, r1, r2, LinearSystems.stateTransitionMatrix_self, Matrix.one_mul]
  have hd : ∀ t, HasDerivAt Y (twoPieceDuty G₁ G₂ δ T t * Y t) t := by
    intro t
    rcases lt_trichotomy t a with h | h | h
    · have hev : Y =ᶠ[𝓝 t] Y₁ := by
        filter_upwards [Iio_mem_nhds h] with u hu
        simp only [Y, (mem_Iio.mp hu).le, ↓reduceIte]
      have e : twoPieceDuty G₁ G₂ δ T t * Y t =
          reparamOnDeriv 0 a t • (G₁ (reparamOn 0 a t) * Y₁ t) := by
        simp only [twoPieceDuty, Y, ← ha, h.le, ↓reduceIte, smul_mul_assoc]
      rw [e]
      exact (d₁ t).congr_of_eventuallyEq hev
    · subst h
      have hz : twoPieceDuty G₁ G₂ δ T a * Y a = 0 := by
        simp only [twoPieceDuty, ← ha, le_refl, ↓reduceIte, d1z, zero_smul, Matrix.zero_mul]
      rw [hz]
      have hl : HasDerivWithinAt Y 0 (Iic a) a := by
        have h := (d₁ a).hasDerivWithinAt (s := Iic a)
        rw [d1z, zero_smul] at h
        exact h.congr (fun u hu => by simp only [Y, mem_Iic.mp hu, ↓reduceIte])
          (by simp only [Y, le_refl, ↓reduceIte])
      have hr : HasDerivWithinAt Y 0 (Ici a) a := by
        have h := (d₂ a).hasDerivWithinAt (s := Ici a)
        rw [d2z, zero_smul] at h
        refine h.congr (fun u hu => ?_) (by simp only [Y, le_refl, ↓reduceIte, hjoin])
        rcases (mem_Ici.mp hu).eq_or_lt with h' | h'
        · subst h'; simp only [Y, le_refl, ↓reduceIte, hjoin]
        · simp only [Y, not_le.mpr h', ↓reduceIte]
      have := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · have hev : Y =ᶠ[𝓝 t] Y₂ := by
        filter_upwards [Ioi_mem_nhds h] with u hu
        simp only [Y, not_le.mpr (mem_Ioi.mp hu), ↓reduceIte]
      have e : twoPieceDuty G₁ G₂ δ T t * Y t =
          reparamOnDeriv a ((1 - δ) * T) t • (G₂ (reparamOn a ((1 - δ) * T) t) * Y₂ t) := by
        simp only [twoPieceDuty, Y, ← ha, not_le.mpr h, ↓reduceIte, smul_mul_assoc]
      rw [e]
      exact (d₂ t).congr_of_eventuallyEq hev
  have hF := continuous_twoPieceDuty hδ0 hδ1 hT h₁ h₂
  have hY : IsIntegralCurveOn Y (Periodic.matField (twoPieceDuty G₁ G₂ δ T)) (Ici 0) :=
    fun t _ => (hd t).hasDerivWithinAt
  have h := Periodic.transition_unique hF (norm_twoPieceDuty_le hM₁ hM₂) hY T hT.le
  have hY0 : Y 0 = 1 := by
    simp only [Y, Y₁, hp.le, ↓reduceIte, reparamOn_left,
      LinearSystems.stateTransitionMatrix_self]
  have hYT : Y T = Periodic.transition G₂ T a * C := by
    have r3 : reparamOn a ((1 - δ) * T) T = T := by
      have := reparamOn_right (a := a) hq; rwa [hs] at this
    simp only [Y, Y₂, not_le.mpr (by linarith : a < T), ↓reduceIte, r3]
  rw [hY0, Matrix.mul_one, hYT] at h
  exact h.symm

@[tmio T, powerlib_foundation] private theorem twoPieceDuty_smul (μ : ℝ) :
    (fun t => μ • twoPieceDuty G₁ G₂ δ T t) =
      twoPieceDuty (fun t => μ • G₁ t) (fun t => μ • G₂ t) δ T := by
  funext t
  simp only [twoPieceDuty]
  split_ifs <;> rw [smul_comm]

/-- **First-order averaging across a switching instant at `δT`.** For continuous bounded `G₁`,
`G₂`, `δ ∈ (0, 1)`, `T > 0` and `Ḡ = (1/T)(∫₀^{δT} G₁ + ∫_{δT}^T G₂)`: if `tr Ḡ < 0 < det Ḡ`
the switched period map `Φ_{εG₂}(T, δT) Φ_{εG₁}(δT, 0)` is Schur stable for all small `ε > 0`; if
`tr Ḡ > 0` or `det Ḡ < 0` it has a multiplier outside the unit circle for all small `ε > 0`
(`Averaging.averaging_schurStable`, `Averaging.averaging_floquetUnstable` applied to the
continuous field `twoPieceDuty`). -/
@[tmio T, powerlib_foundation] theorem twoPieceDuty_averaging (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT : 0 < T) {M : ℝ} (h₁ : Continuous G₁) (h₂ : Continuous G₂) (hM₁ : ∀ t, ‖G₁ t‖ ≤ M)
    (hM₂ : ∀ t, ‖G₂ t‖ ≤ M) {Gbar : Matrix (Fin 2) (Fin 2) ℝ}
    (havg : (∫ t in (0 : ℝ)..δ * T, G₁ t) + ∫ t in δ * T..T, G₂ t = T • Gbar) :
    (Gbar.trace < 0 → 0 < Gbar.det → ∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable
      (Periodic.transition (fun t => ε • G₂ t) T (δ * T) *
        Periodic.transition (fun t => ε • G₁ t) (δ * T) 0)) ∧
    (0 < Gbar.trace ∨ Gbar.det < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ρ ∈ spectrum ℂ
      ((Periodic.transition (fun t => ε • G₂ t) T (δ * T) *
        Periodic.transition (fun t => ε • G₁ t) (δ * T) 0).map (algebraMap ℝ ℂ)), 1 < ‖ρ‖) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM₁ 0)
  have hav := (integral_twoPieceDuty hδ0 hδ1 hT h₁ h₂).trans havg
  have hε₁ : ∀ ε : ℝ, ∀ t, ‖ε • G₁ t‖ ≤ |ε| * M := fun ε t => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM₁ t) (abs_nonneg ε)
  have hε₂ : ∀ ε : ℝ, ∀ t, ‖ε • G₂ t‖ ≤ |ε| * M := fun ε t => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM₂ t) (abs_nonneg ε)
  refine ⟨fun htr hdet => ?_, fun h => ?_⟩
  · have hb := Averaging.averaging_schurStable (continuous_twoPieceDuty hδ0 hδ1 hT h₁ h₂)
      (norm_twoPieceDuty_le hM₁ hM₂) (by positivity) hT hav htr hdet
    filter_upwards [hb] with ε hε'
    rw [Periodic.monodromy, zero_add, twoPieceDuty_smul] at hε'
    have e := transition_twoPieceDuty hδ0 hδ1 hT (h₁.const_smul ε) (h₂.const_smul ε)
      (hε₁ ε) (hε₂ ε)
    exact e ▸ hε'
  · have hb := Averaging.averaging_floquetUnstable (continuous_twoPieceDuty hδ0 hδ1 hT h₁ h₂)
      (norm_twoPieceDuty_le hM₁ hM₂) (by positivity) hT hav h
    filter_upwards [hb] with ε hε'
    unfold Periodic.FloquetUnstable at hε'
    rw [Periodic.monodromy, zero_add, twoPieceDuty_smul] at hε'
    have e := transition_twoPieceDuty hδ0 hδ1 hT (h₁.const_smul ε) (h₂.const_smul ε)
      (hε₁ ε) (hε₂ ε)
    exact e ▸ hε'

end TwoPiece

/-! ## The duty-`δ` oscillator: the L2 verdict predicts L1 for small modulation -/

section Transfer

open SquareWave (frameField frame scale scaleInv)
open powerlib.ParametricResonance.NormalForm (quarter)
open powerlib.ParametricResonance.TwoToOne (refl1 refl2)

@[tmio T, powerlib_foundation] private theorem integral_trig_duty {ω T δ : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) :
    (∫ t in (0 : ℝ)..δ * T, Real.cos (ω * t)) = Real.sin (2 * Real.pi * δ) / ω ∧
    (∫ t in (0 : ℝ)..δ * T, Real.sin (ω * t)) = (1 - Real.cos (2 * Real.pi * δ)) / ω ∧
    (∫ t in δ * T..T, Real.cos (ω * t)) = -(Real.sin (2 * Real.pi * δ) / ω) ∧
    (∫ t in δ * T..T, Real.sin (ω * t)) = -((1 - Real.cos (2 * Real.pi * δ)) / ω) := by
  have e1 : ω * (δ * T) = 2 * Real.pi * δ := by rw [hT]; field_simp
  have e2 : ω * T = 2 * Real.pi := by rw [hT]; field_simp
  have hc := fun a b => intervalIntegral.integral_comp_mul_left (a := a) (b := b)
    (fun x => Real.cos x) hω.ne'
  have hs := fun a b => intervalIntegral.integral_comp_mul_left (a := a) (b := b)
    (fun x => Real.sin x) hω.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc, integral_cos, mul_zero, e1]; simp [div_eq_inv_mul]
  · rw [hs, integral_sin, mul_zero, e1]; simp [div_eq_inv_mul]
  · rw [hc, integral_cos, e1, e2]; simp [div_eq_inv_mul]
  · rw [hs, integral_sin, e1, e2]; simp [div_eq_inv_mul]; ring

/-- **The average of two frozen levels split at `δT`.** For `T = 2π/ω`:
`∫₀^{δT} G_{k₁} + ∫_{δT}^T G_{k₂} = T · slowFlowMatrix c Δ g`, `Δ = (ω²/4 − (δk₁ + (1 − δ)k₂))/ω`,
`g = (k₁ − k₂)((1 − cos 2πδ) + j sin 2πδ)/(2πω)`; at `δ = 1/2` this is
`SquareWave.integral_halves`. -/
@[tmio T, powerlib_foundation] theorem integral_pieces (c k₁ k₂ : ℝ) {ω T δ : ℝ} (hω : 0 < ω)
    (hT : T = 2 * Real.pi / ω) :
    (∫ t in (0 : ℝ)..δ * T, frameField c ω (fun _ => k₁) t) +
        ∫ t in δ * T..T, frameField c ω (fun _ => k₂) t =
      T • slowFlowMatrix c ((ω ^ 2 / 4 - (δ * k₁ + (1 - δ) * k₂)) / ω)
        ⟨(k₁ - k₂) * (1 - Real.cos (2 * Real.pi * δ)) / (2 * Real.pi * ω),
          (k₁ - k₂) * Real.sin (2 * Real.pi * δ) / (2 * Real.pi * ω)⟩ := by
  obtain ⟨c1, s1, c2, s2⟩ := integral_trig_duty (δ := δ) hω hT
  rw [SquareWave.integral_frameField_const, SquareWave.integral_frameField_const, c1, s1, c2, s2]
  have hπ := Real.pi_pos
  subst hT
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [slowFlowMatrix, quarter, refl1, refl2] <;> field_simp <;> ring

/-- **The duty-`δ` monodromy in the rotating frame.** For `ω > 0`, `T = 2π/ω`, `δ ∈ [0, 1]`:
`M D = −D Φ₂(T, δT) Φ₁(δT, 0)`, `D = scale ω`, `Φ_i` the transition matrices of the rotating-frame
fields of the two levels (`SquareWave.exp_mul_frame`). -/
@[tmio T, powerlib_foundation] theorem dutyMonodromy_mul_scale (c k₁ k₂ : ℝ) {ω T δ : ℝ}
    (hω : 0 < ω) (hT : T = 2 * Real.pi / ω) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    dutyMonodromy c k₁ k₂ δ T * scale ω =
      -(scale ω * (Periodic.transition (frameField c ω (fun _ => k₂)) T (δ * T) *
        Periodic.transition (frameField c ω (fun _ => k₁)) (δ * T) 0)) := by
  have hT0 : 0 < T := by rw [hT]; positivity
  have hf0 : frame ω 0 = scale ω := by simp [frame, NormalForm.rot]
  have hfT : frame ω T = -scale ω := by
    have : ω * T / 2 = Real.pi := by rw [hT]; field_simp
    simp [frame, NormalForm.rot, this]
  have e1 := SquareWave.exp_mul_frame (c := c) hω.ne' k₁ (a := 0) (t := δ * T) (by positivity)
  have e2 := SquareWave.exp_mul_frame (c := c) hω.ne' k₂ (a := δ * T) (t := T) (by nlinarith)
  rw [sub_zero] at e1
  rw [show T - δ * T = (1 - δ) * T by ring] at e2
  rw [dutyMonodromy_eq_exp]
  conv_lhs => rw [← hf0, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, e2, hfT]
  rw [Matrix.mul_assoc, Matrix.neg_mul]

@[tmio T, powerlib_foundation] private theorem frameField_scaled (μ s a ω : ℝ) (hω : 0 < ω) :
    frameField (μ * s) ω (fun _ => ω ^ 2 / 4 + μ * a) =
      fun t => μ • frameField s ω (fun _ => ω ^ 2 / 4 + a) t := by
  have hres : SquareWave.residual (μ * s) (ω ^ 2 / 4 + μ * a) ω =
      μ • SquareWave.residual s (ω ^ 2 / 4 + a) ω := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [SquareWave.residual]
    all_goals (try field_simp)
    all_goals ring
  funext t
  rw [frameField, frameField, hres, Matrix.mul_smul, Matrix.smul_mul]

@[tmio T, powerlib_foundation] private theorem bound_pieces (ω s k₁ k₂ : ℝ) :
    ∃ M, (∀ t, ‖frameField s ω (fun _ => k₁) t‖ ≤ M) ∧
      ∀ t, ‖frameField s ω (fun _ => k₂) t‖ ≤ M := by
  set R := ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + ‖quarter‖
  refine ⟨R * max ‖SquareWave.residual s k₁ ω‖ ‖SquareWave.residual s k₂ ω‖ * R,
    fun t => ?_, fun t => ?_⟩
  · refine (SquareWave.norm_frameField_const_le s ω k₁ t).trans ?_
    gcongr; exact le_max_left _ _
  · refine (SquareWave.norm_frameField_const_le s ω k₂ t).trans ?_
    gcongr; exact le_max_right _ _

/-- **The L2 verdict predicts L1 for the duty-`δ` square wave.** Pump frequency `ω > 0`,
period `T = 2π/ω`, duty `δ ∈ (0, 1)`, and the distinguished scaling: damping `c = μs` and both
stiffness levels within `O(μ)` of the 2:1 resonance, `k_i = ω²/4 + μ a_i`. The averaged model is
`μ · slowFlowMatrix s Δ g`, `Δ = −(δa₁ + (1 − δ)a₂)/ω`,
`|g| = |a₁ − a₂| |sin(πδ)|/(πω)` (`integral_pieces`). If it is Hurwitz
(`s > 0`, `(a₁ − a₂)² sin²(πδ) < π²(s²ω² + (δa₁ + (1 − δ)a₂)²)`), the exact monodromy is Schur
stable for all small `μ > 0`; if it has an exponent with positive real part (`s < 0`, or the
reverse strict inequality), the exact system has a multiplier outside the unit circle for all
small `μ > 0`, although the stiffness jumps at `δT` (time change `twoPieceDuty`). -/
@[tmio T, powerlib_foundation] theorem averaging_transfer {ω s a₁ a₂ δ : ℝ} (hω : 0 < ω)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (0 < s → (a₁ - a₂) ^ 2 * Real.sin (Real.pi * δ) ^ 2 <
        Real.pi ^ 2 * (s ^ 2 * ω ^ 2 + (δ * a₁ + (1 - δ) * a₂) ^ 2) →
      ∀ᶠ μ in 𝓝[>] (0 : ℝ), LTI.SchurStable (dutyMonodromy (μ * s) (ω ^ 2 / 4 + μ * a₁)
        (ω ^ 2 / 4 + μ * a₂) δ (2 * Real.pi / ω))) ∧
    (s < 0 ∨ Real.pi ^ 2 * (s ^ 2 * ω ^ 2 + (δ * a₁ + (1 - δ) * a₂) ^ 2) <
        (a₁ - a₂) ^ 2 * Real.sin (Real.pi * δ) ^ 2 →
      ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∃ ρ ∈ spectrum ℂ ((dutyMonodromy (μ * s) (ω ^ 2 / 4 + μ * a₁)
        (ω ^ 2 / 4 + μ * a₂) δ (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)), 1 < ‖ρ‖) := by
  have hπ := Real.pi_pos
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨M, hM₁, hM₂⟩ := bound_pieces ω s (ω ^ 2 / 4 + a₁) (ω ^ 2 / 4 + a₂)
  have havg := integral_pieces s (ω ^ 2 / 4 + a₁) (ω ^ 2 / 4 + a₂) (δ := δ) hω hTdef
  set g : ℂ := ⟨(ω ^ 2 / 4 + a₁ - (ω ^ 2 / 4 + a₂)) * (1 - Real.cos (2 * Real.pi * δ)) /
      (2 * Real.pi * ω), (ω ^ 2 / 4 + a₁ - (ω ^ 2 / 4 + a₂)) * Real.sin (2 * Real.pi * δ) /
      (2 * Real.pi * ω)⟩ with hg
  set Δ := (ω ^ 2 / 4 - (δ * (ω ^ 2 / 4 + a₁) + (1 - δ) * (ω ^ 2 / 4 + a₂))) / ω with hΔ
  obtain ⟨hS, hU⟩ := twoPieceDuty_averaging hδ0 hδ1 hT (SquareWave.continuous_frameField_const _ _ _)
    (SquareWave.continuous_frameField_const _ _ _) hM₁ hM₂ havg
  have hg2 : ‖g‖ ^ 2 = (a₁ - a₂) ^ 2 * Real.sin (Real.pi * δ) ^ 2 / (Real.pi ^ 2 * ω ^ 2) := by
    have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi * δ)
    have hc : Real.cos (2 * Real.pi * δ) = 1 - 2 * Real.sin (Real.pi * δ) ^ 2 := by
      rw [show 2 * Real.pi * δ = 2 * (Real.pi * δ) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    have h1 : (1 - Real.cos (2 * Real.pi * δ)) ^ 2 + Real.sin (2 * Real.pi * δ) ^ 2 =
        4 * Real.sin (Real.pi * δ) ^ 2 := by linear_combination hsc - 2 * hc
    rw [hg, Complex.sq_norm, Complex.normSq_mk]
    have e : (ω ^ 2 / 4 + a₁ - (ω ^ 2 / 4 + a₂)) * (1 - Real.cos (2 * Real.pi * δ)) /
          (2 * Real.pi * ω) * ((ω ^ 2 / 4 + a₁ - (ω ^ 2 / 4 + a₂)) *
          (1 - Real.cos (2 * Real.pi * δ)) / (2 * Real.pi * ω)) +
        (ω ^ 2 / 4 + a₁ - (ω ^ 2 / 4 + a₂)) * Real.sin (2 * Real.pi * δ) / (2 * Real.pi * ω) *
          ((ω ^ 2 / 4 + a₁ - (ω ^ 2 / 4 + a₂)) * Real.sin (2 * Real.pi * δ) /
          (2 * Real.pi * ω)) = ((a₁ - a₂) / (2 * Real.pi * ω)) ^ 2 *
        ((1 - Real.cos (2 * Real.pi * δ)) ^ 2 + Real.sin (2 * Real.pi * δ) ^ 2) := by ring
    rw [e, h1]
    field_simp
    ring
  have hΔ2 : Δ ^ 2 = (δ * a₁ + (1 - δ) * a₂) ^ 2 / ω ^ 2 := by
    rw [hΔ]; field_simp; ring
  have hdet : (slowFlowMatrix s Δ g).det = (Real.pi ^ 2 * (s ^ 2 * ω ^ 2 +
      (δ * a₁ + (1 - δ) * a₂) ^ 2) - (a₁ - a₂) ^ 2 * Real.sin (Real.pi * δ) ^ 2) /
      (Real.pi ^ 2 * ω ^ 2) := by
    rw [det_slowFlowMatrix, hg2, hΔ2]; field_simp
  -- transfer through the rotating frame
  have transfer : ∀ μ : ℝ,
      dutyMonodromy (μ * s) (ω ^ 2 / 4 + μ * a₁) (ω ^ 2 / 4 + μ * a₂) δ T * scale ω =
        -(scale ω * (Periodic.transition (fun t => μ • frameField s ω (fun _ => ω ^ 2 / 4 + a₂) t)
          T (δ * T) * Periodic.transition (fun t => μ • frameField s ω
            (fun _ => ω ^ 2 / 4 + a₁) t) (δ * T) 0)) := fun μ => by
    rw [dutyMonodromy_mul_scale _ _ _ hω hTdef hδ0.le hδ1.le, frameField_scaled μ s a₁ ω hω,
      frameField_scaled μ s a₂ ω hω]
  refine ⟨fun hs h => ?_, fun h => ?_⟩
  · have hb := hS (by rw [trace_slowFlowMatrix]; linarith)
      (by rw [hdet]; exact div_pos (by linarith) (by positivity))
    filter_upwards [hb] with μ hμ
    exact ((SquareWave.schurStable_iff_of_mul_eq_neg (SquareWave.scaleInv_mul_scale hω.ne')
      (SquareWave.scale_mul_scaleInv hω.ne') (transfer μ)).1).mpr hμ
  · have hb := hU (by
      rw [trace_slowFlowMatrix, hdet]
      rcases h with h | h
      · left; linarith
      · right; exact div_neg_of_neg_of_pos (by linarith) (by positivity))
    filter_upwards [hb] with μ hμ
    exact (SquareWave.schurStable_iff_of_mul_eq_neg (SquareWave.scaleInv_mul_scale hω.ne')
      (SquareWave.scale_mul_scaleInv hω.ne') (transfer μ)).2 hμ

end Transfer

end powerlib.ParametricResonance.DutyCycle
