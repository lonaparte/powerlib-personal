import theorem.Frequency.SwingGovernor
import theorem.LTI.Oscillator2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Frequency nadir of the swing + governor model (exact closed form)

The exact time and value of the frequency nadir of the underdamped swing + governor model after a
load step, without Laplace inversion; the nadir magnitude, which the note leaves to "Kundur
§11.1.6", is derived here.

Model boundary.
* Exactly the plant of `Frequency.SwingGovernor` (`SwingGovernor.plant`; state `(Δω, ΔP_m)`,
  continuous time, linear, Kundur per-unit, load step `ΔP_L` applied at `t = 0` to the system
  at rest `x(0) = 0`; no turbine/reheat, AGC, dead-band, rate limit, PLL, delay or PWM).
* Parameters: `0 < M`, `0 < T_g`, `0 ≤ D`, `0 < K_R + D`, a load *increase* `0 < ΔP_L`, and the
  underdamped case `ζ_n < 1`. The conclusions are trajectory-level (every trajectory of the
  model with `x(0) = 0`).
* Notation (`σ = ζ_n ω_n`, `ω_d = ω_n √(1 − ζ_n²)`, the §1.7 `ω_n`, `ζ_n`):
  `nadirTime = atan2(ω_d, σ − 1/T_g)/ω_d`, with `atan2(y, x) := Complex.arg (x + j y)`;
  `nadirValue = −ΔP_L/(K_R + D) · [1 + √(1 − 2σT_g + ω_n²T_g²) · e^{−σ t_nadir}]`.

Source: work-sync `theory/T-frequency-stability.md` §1.7 (boxed `t_nadir` with atan2 and the
step response `Δω(t) = −ΔP_L/(K_R + D)[1 − e^{−σt}(cos ω_d t − α sin ω_d t)]`).

Results.
* `nadir` (implementation evidence, private): `0 < t_nadir`; `Δω` is strictly decreasing on
  `[0, t_nadir]`; `Δω(t_nadir)` is the minimum of `Δω` over all `t ≥ 0`; and it equals
  `nadirValue`.
* `nadirValue_lt` (foundation): the nadir lies strictly below the quasi-steady state
  `−ΔP_L/(K_R + D)` (overshoot is unavoidable in the underdamped case).
* `nadir_successive` (implementation evidence, private): at `t_nadir + kπ/ω_d` the derivative
  vanishes again and the deviation from the quasi-steady state is multiplied by
  `(−e^{−σπ/ω_d})^k`.

Family and connection conclusions.
* This module adds no family: the model is the swing + governor family of
  `Frequency.SwingGovernor`. The scalar core (`respC`, `rateC`, `tCrit`, …), the closed-form
  identity `osc2_freq` (the first component of the explicit solution from rest is `respC`, a
  static identity of closed forms), `respC_nadirTime` and `nadirValue_lt` are foundation.
* The nadir statements quantify over forward solutions and their extrema in time, which the
  sentence language does not express: `trajectory_freq_eq`, `nadir` and `nadir_successive` are
  private implementation evidence (Rules §3a). Modules that need a nadir of a forward solution
  re-derive it from the generic `LTI.trajectory_eq_osc2`, `osc2_freq` and the scalar core.

Proof outline (no Laplace inversion is assumed).
* The explicit closed form `osc2` solves the state equations (`hasDerivAt_osc2`), trajectory
  uniqueness identifies it with every trajectory (`trajectory_eq_osc2`); its first component is
  the scalar `respC`, whose derivative is `−(ΔP_L ρ/(M ω_d)) e^{−σt} sin(θ − ω_d t)` with
  `θ = ω_d t_nadir`, `ρ = |σ − 1/T_g + j ω_d|`; this gives the first critical point and the
  strict decrease before it. After it, the critical-point shift identity `damped_shift` writes
  the deviation as `(Δω(t_nadir) − Δω^∞)·e^{−σu}(cos ω_d u + (σ/ω_d) sin ω_d u)`, which is
  bounded by its first value via `one_add_ratio_sin_le_exp`.
-/

noncomputable section
namespace powerlib.Frequency.SwingGovernor
open Set Filter Matrix LinearSystems
open scoped Topology

/-! ## Scalar core

`respC c σ ω_d T_g` is the closed-form frequency deviation written with `c = ΔP_L/(K_R + D)`
and `ω_n² = σ² + ω_d²` (so that `ΔP_L/M = c ω_n² T_g`); `rateC` is its derivative. -/

/-- Closed-form `Δω(t)` in terms of `c`, `σ`, `ω_d`, `T_g`. -/
def respC (c σ ωd Tg t : ℝ) : ℝ :=
  -c + Real.exp (-(σ * t)) * (c * Real.cos (ωd * t) +
    (σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) / ωd * Real.sin (ωd * t))

/-- Closed-form `Δω̇(t)`. -/
def rateC (c σ ωd Tg t : ℝ) : ℝ :=
  -(c * (σ ^ 2 + ωd ^ 2) * Tg / ωd) * Real.exp (-(σ * t)) *
    (ωd * Real.cos (ωd * t) - (σ - 1 / Tg) * Real.sin (ωd * t))

@[tmio M, powerlib_foundation] theorem hasDerivAt_respC {c σ ωd Tg : ℝ} (hωd : ωd ≠ 0) (hTg : Tg ≠ 0)
    (t : ℝ) : HasDerivAt (respC c σ ωd Tg) (rateC c σ ωd Tg t) t := by
  have he : HasDerivAt (fun s => Real.exp (-(σ * s))) (Real.exp (-(σ * t)) * (-σ)) t := by
    have := ((hasDerivAt_id t).const_mul σ).neg.exp
    simpa using this
  have hc : HasDerivAt (fun s => Real.cos (ωd * s)) (-Real.sin (ωd * t) * ωd) t := by
    have := ((hasDerivAt_id t).const_mul ωd).cos
    simpa using this
  have hs : HasDerivAt (fun s => Real.sin (ωd * s)) (Real.cos (ωd * t) * ωd) t := by
    have := ((hasDerivAt_id t).const_mul ωd).sin
    simpa using this
  have h := (he.mul ((hc.const_mul c).add
    (hs.const_mul ((σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) / ωd)))).const_add (-c)
  convert h using 1
  · funext s; simp only [respC, Pi.mul_apply, Pi.add_apply]
  unfold rateC
  simp only [Pi.add_apply]
  field_simp
  ring

/-- `rateC` as the derivative bracket of `e^{−σt}(a cos ω_d t + b sin ω_d t)`. -/
@[powerlib_foundation] theorem rateC_eq_bracket {c σ ωd Tg : ℝ} (hωd : ωd ≠ 0) (hTg : Tg ≠ 0)
    (t : ℝ) :
    rateC c σ ωd Tg t = Real.exp (-(σ * t)) *
      (-σ * (c * Real.cos (ωd * t) + (σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) / ωd *
        Real.sin (ωd * t)) + ωd * ((σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) / ωd *
          Real.cos (ωd * t) - c * Real.sin (ωd * t))) := by
  unfold rateC
  field_simp
  ring

/-- Critical-point shift: if `t ↦ e^{−σt}(a cos ω_d t + b sin ω_d t)` has zero derivative at
`T`, then its value at `T + u` is its value at `T` times
`e^{−σu}(cos ω_d u + (σ/ω_d) sin ω_d u)`. -/
@[powerlib_foundation] theorem damped_shift {σ ωd a b T : ℝ} (hωd : ωd ≠ 0)
    (hcrit : -σ * (a * Real.cos (ωd * T) + b * Real.sin (ωd * T)) +
      ωd * (b * Real.cos (ωd * T) - a * Real.sin (ωd * T)) = 0) (u : ℝ) :
    Real.exp (-(σ * (T + u))) * (a * Real.cos (ωd * (T + u)) + b * Real.sin (ωd * (T + u))) =
      Real.exp (-(σ * T)) * (a * Real.cos (ωd * T) + b * Real.sin (ωd * T)) *
        (Real.exp (-(σ * u)) * (Real.cos (ωd * u) + σ / ωd * Real.sin (ωd * u))) := by
  have hk : b * Real.cos (ωd * T) - a * Real.sin (ωd * T) =
      σ / ωd * (a * Real.cos (ωd * T) + b * Real.sin (ωd * T)) := by
    field_simp
    linarith
  rw [show ωd * (T + u) = ωd * T + ωd * u by ring, Real.cos_add, Real.sin_add,
    show -(σ * (T + u)) = -(σ * T) + -(σ * u) by ring, Real.exp_add]
  linear_combination (Real.exp (-(σ * T)) * Real.exp (-(σ * u)) * Real.sin (ωd * u)) * hk

/-- Facts about `θ = atan2(ω_d, b) = arg (b + j ω_d)` for `ω_d > 0`. -/
@[powerlib_foundation] theorem arg_facts {b ωd : ℝ} (hωd : 0 < ωd) :
    0 < Complex.arg ⟨b, ωd⟩ ∧ Complex.arg ⟨b, ωd⟩ < Real.pi ∧
      Real.cos (Complex.arg ⟨b, ωd⟩) = b / ‖(⟨b, ωd⟩ : ℂ)‖ ∧
      Real.sin (Complex.arg ⟨b, ωd⟩) = ωd / ‖(⟨b, ωd⟩ : ℂ)‖ ∧
      0 < ‖(⟨b, ωd⟩ : ℂ)‖ ∧ ‖(⟨b, ωd⟩ : ℂ)‖ ^ 2 = b ^ 2 + ωd ^ 2 := by
  have hz : (⟨b, ωd⟩ : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hn : 0 < ‖(⟨b, ωd⟩ : ℂ)‖ := norm_pos_iff.2 hz
  have hsin : Real.sin (Complex.arg ⟨b, ωd⟩) = ωd / ‖(⟨b, ωd⟩ : ℂ)‖ := Complex.sin_arg _
  have hsinpos : 0 < Real.sin (Complex.arg ⟨b, ωd⟩) := by rw [hsin]; positivity
  have hnn : 0 ≤ Complex.arg ⟨b, ωd⟩ := Complex.arg_nonneg_iff.2 hωd.le
  have hle : Complex.arg ⟨b, ωd⟩ ≤ Real.pi := Complex.arg_le_pi _
  refine ⟨?_, ?_, Complex.cos_arg hz, hsin, hn, ?_⟩
  · rcases hnn.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.sin_zero] at hsinpos; exact absurd hsinpos (lt_irrefl 0)
  · rcases hle.lt_or_eq with h | h
    · exact h
    · rw [h, Real.sin_pi] at hsinpos; exact absurd hsinpos (lt_irrefl 0)
  · rw [Complex.sq_norm, Complex.normSq_mk]; ring

/-- `rateC` in phase form: `−(c ω_n² T_g/ω_d) e^{−σt} ρ sin(θ − ω_d t)`. -/
@[powerlib_foundation] theorem rateC_eq_sin {c σ ωd Tg : ℝ} (hωd : 0 < ωd) (t : ℝ) :
    rateC c σ ωd Tg t = -(c * (σ ^ 2 + ωd ^ 2) * Tg / ωd) * Real.exp (-(σ * t)) *
      (‖(⟨σ - 1 / Tg, ωd⟩ : ℂ)‖ *
        Real.sin (Complex.arg ⟨σ - 1 / Tg, ωd⟩ - ωd * t)) := by
  obtain ⟨-, -, hcos, hsin, hn, -⟩ := arg_facts (b := σ - 1 / Tg) hωd
  rw [Real.sin_sub, hcos, hsin]
  unfold rateC
  field_simp

section Core

variable {c σ ωd Tg : ℝ}

/-- `t_nadir` of the scalar core: `arg (σ − 1/T_g + j ω_d)/ω_d`. -/
def tCrit (σ ωd Tg : ℝ) : ℝ := Complex.arg ⟨σ - 1 / Tg, ωd⟩ / ωd

@[powerlib_foundation] theorem tCrit_pos (hωd : 0 < ωd) : 0 < tCrit σ ωd Tg :=
  div_pos (arg_facts hωd).1 hωd

@[powerlib_foundation] theorem mul_tCrit (hωd : 0 < ωd) :
    ωd * tCrit σ ωd Tg = Complex.arg ⟨σ - 1 / Tg, ωd⟩ := by
  unfold tCrit; field_simp

@[powerlib_foundation] theorem rateC_tCrit (hωd : 0 < ωd) :
    rateC c σ ωd Tg (tCrit σ ωd Tg) = 0 := by
  rw [rateC_eq_sin hωd, mul_tCrit hωd, sub_self, Real.sin_zero]
  ring

@[powerlib_foundation] theorem rateC_neg (hωd : 0 < ωd) (hTg : 0 < Tg) (hc : 0 < c) {t : ℝ}
    (ht : t ∈ Ico 0 (tCrit σ ωd Tg)) : rateC c σ ωd Tg t < 0 := by
  obtain ⟨hθ0, hθπ, -, -, hn, -⟩ := arg_facts (b := σ - 1 / Tg) hωd
  rw [rateC_eq_sin hωd]
  have h1 : ωd * t < Complex.arg ⟨σ - 1 / Tg, ωd⟩ := by
    rw [← mul_tCrit hωd]; exact mul_lt_mul_of_pos_left ht.2 hωd
  have h2 : 0 ≤ ωd * t := mul_nonneg hωd.le ht.1
  have hsin : 0 < Real.sin (Complex.arg ⟨σ - 1 / Tg, ωd⟩ - ωd * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hk : 0 < c * (σ ^ 2 + ωd ^ 2) * Tg / ωd := by positivity
  have := mul_pos (mul_pos hk (Real.exp_pos (-(σ * t)))) (mul_pos hn hsin)
  linarith [this]

@[powerlib_foundation] theorem respC_tCrit (hωd : 0 < ωd) (hTg : 0 < Tg) :
    respC c σ ωd Tg (tCrit σ ωd Tg) =
      -c - c * (Tg * ‖(⟨σ - 1 / Tg, ωd⟩ : ℂ)‖) * Real.exp (-(σ * tCrit σ ωd Tg)) := by
  obtain ⟨-, -, hcos, hsin, hn, hsq⟩ := arg_facts (b := σ - 1 / Tg) hωd
  unfold respC
  rw [mul_tCrit hωd, hcos, hsin]
  generalize ‖(⟨σ - 1 / Tg, ωd⟩ : ℂ)‖ = ρ at hn hsq ⊢
  generalize Real.exp (-(σ * tCrit σ ωd Tg)) = E
  have e1 : (σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) / ωd * (ωd / ρ) =
      (σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) / ρ := by
    field_simp
  have e2 : c * ((σ - 1 / Tg) / ρ) + (σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) / ρ =
      (c * (σ - 1 / Tg) + (σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg)) / ρ := by ring
  have e3 : c * (σ - 1 / Tg) + (σ * c - c * (σ ^ 2 + ωd ^ 2) * Tg) = -(c * Tg) * ρ ^ 2 := by
    rw [hsq]; field_simp; ring
  rw [e1, e2, e3]
  field_simp
  ring

@[powerlib_foundation] theorem tg_mul_norm (hTg : 0 < Tg) (hωd : 0 < ωd) :
    Tg * ‖(⟨σ - 1 / Tg, ωd⟩ : ℂ)‖ =
      Real.sqrt (1 - 2 * σ * Tg + (σ ^ 2 + ωd ^ 2) * Tg ^ 2) := by
  obtain ⟨-, -, -, -, hn, hsq⟩ := arg_facts (b := σ - 1 / Tg) hωd
  rw [show 1 - 2 * σ * Tg + (σ ^ 2 + ωd ^ 2) * Tg ^ 2 = (Tg * ‖(⟨σ - 1 / Tg, ωd⟩ : ℂ)‖) ^ 2 by
    rw [mul_pow, hsq]; field_simp; ring]
  exact (Real.sqrt_sq (by positivity)).symm

@[powerlib_foundation] theorem respC_strictAntiOn (hωd : 0 < ωd) (hTg : 0 < Tg) (hc : 0 < c) :
    StrictAntiOn (respC c σ ωd Tg) (Icc 0 (tCrit σ ωd Tg)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun t _ => (hasDerivAt_respC hωd.ne' hTg.ne' t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_respC hωd.ne' hTg.ne' t).deriv]
    exact rateC_neg hωd hTg hc ⟨ht.1.le, ht.2⟩

@[powerlib_foundation] theorem respC_shift (hωd : 0 < ωd) (hTg : 0 < Tg) (u : ℝ) :
    respC c σ ωd Tg (tCrit σ ωd Tg + u) + c =
      (respC c σ ωd Tg (tCrit σ ωd Tg) + c) *
        (Real.exp (-(σ * u)) * (Real.cos (ωd * u) + σ / ωd * Real.sin (ωd * u))) := by
  have hcrit := rateC_tCrit (c := c) hωd (Tg := Tg) (σ := σ)
  rw [rateC_eq_bracket hωd.ne' hTg.ne'] at hcrit
  have hcrit' := (mul_eq_zero.1 hcrit).resolve_left (Real.exp_pos _).ne'
  have h := damped_shift hωd.ne' hcrit' u
  unfold respC
  simp only [neg_add_cancel_comm]
  rw [h]

@[powerlib_foundation] theorem respC_tCrit_add_c_neg (hωd : 0 < ωd) (hTg : 0 < Tg) (hc : 0 < c) :
    respC c σ ωd Tg (tCrit σ ωd Tg) + c < 0 := by
  rw [respC_tCrit hωd hTg]
  obtain ⟨-, -, -, -, hn, -⟩ := arg_facts (b := σ - 1 / Tg) hωd
  have := mul_pos (mul_pos hc (mul_pos hTg hn)) (Real.exp_pos (-(σ * tCrit σ ωd Tg)))
  linarith

@[powerlib_foundation] theorem respC_isMinOn (hωd : 0 < ωd) (hTg : 0 < Tg) (hσ : 0 ≤ σ)
    (hc : 0 < c) : IsMinOn (respC c σ ωd Tg) (Ici 0) (tCrit σ ωd Tg) := by
  intro t ht
  simp only [Set.mem_ofPred_eq]
  rcases le_total t (tCrit σ ωd Tg) with h | h
  · exact (respC_strictAntiOn hωd hTg hc).antitoneOn ⟨ht, h⟩
      ⟨(tCrit_pos hωd).le, le_rfl⟩ h
  · have hs := respC_shift (c := c) (σ := σ) hωd hTg (t - tCrit σ ωd Tg)
    rw [add_sub_cancel] at hs
    have hG := LTI.one_add_ratio_sin_le_exp hσ hωd (sub_nonneg.2 h)
    have hneg := respC_tCrit_add_c_neg (σ := σ) hωd hTg hc
    nlinarith

@[powerlib_foundation] theorem respC_add_half_period (hωd : 0 < ωd) (t : ℝ) :
    respC c σ ωd Tg (t + Real.pi / ωd) + c =
      -Real.exp (-(σ * (Real.pi / ωd))) * (respC c σ ωd Tg t + c) := by
  have harg : ωd * (t + Real.pi / ωd) = ωd * t + Real.pi := by field_simp
  have hexp : Real.exp (-(σ * (t + Real.pi / ωd))) =
      Real.exp (-(σ * (Real.pi / ωd))) * Real.exp (-(σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  unfold respC
  rw [harg, hexp, Real.cos_add_pi, Real.sin_add_pi]
  ring

@[powerlib_foundation] theorem rateC_tCrit_add (hωd : 0 < ωd) (k : ℕ) :
    rateC c σ ωd Tg (tCrit σ ωd Tg + k * (Real.pi / ωd)) = 0 := by
  have harg : ωd * (tCrit σ ωd Tg + k * (Real.pi / ωd)) =
      Complex.arg ⟨σ - 1 / Tg, ωd⟩ + k * Real.pi := by
    rw [mul_add, mul_tCrit hωd]; field_simp
  rw [rateC_eq_sin hωd, harg, show ∀ a b : ℝ, a - (a + b) = -b from fun a b => by ring,
    Real.sin_neg, Real.sin_nat_mul_pi]
  ring

end Core

/-! ## The swing + governor model -/

/-- `σ = ζ_n ω_n`. -/
def decayRate (M D K Tg : ℝ) : ℝ := dampingRatio M D K Tg * natFreq M D K Tg

/-- `ω_d = ω_n √(1 − ζ_n²)`. -/
def dampedFreq (M D K Tg : ℝ) : ℝ :=
  natFreq M D K Tg * Real.sqrt (1 - dampingRatio M D K Tg ^ 2)

/-- `t_nadir = atan2(ω_d, ζ_n ω_n − 1/T_g)/ω_d`, `atan2(y, x) = arg (x + j y)`. -/
def nadirTime (M D K Tg : ℝ) : ℝ :=
  Complex.arg ⟨decayRate M D K Tg - 1 / Tg, dampedFreq M D K Tg⟩ / dampedFreq M D K Tg

/-- `−ΔP_L/(K_R + D)·[1 + √(1 − 2σT_g + ω_n²T_g²) e^{−σ t_nadir}]`, `σ = ζ_n ω_n`. -/
def nadirValue (M D K Tg ΔPL : ℝ) : ℝ :=
  -ΔPL / (K + D) * (1 + Real.sqrt (1 - 2 * decayRate M D K Tg * Tg +
      natFreq M D K Tg ^ 2 * Tg ^ 2) * Real.exp (-(decayRate M D K Tg * nadirTime M D K Tg)))

variable {M D K Tg ΔPL : ℝ}

@[powerlib_foundation] theorem dampingRatio_pos (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) : 0 < dampingRatio M D K Tg := by
  unfold dampingRatio
  have : 0 < M * Tg * (D + K) := mul_pos (mul_pos hM hTg) (by linarith)
  exact div_pos (by nlinarith) (by positivity)

@[powerlib_foundation] theorem decayRate_eq (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 < K + D) :
    decayRate M D K Tg = (M + D * Tg) / (2 * (M * Tg)) := by
  have h := two_mul_dampingRatio_mul_natFreq hM hTg (by linarith : 0 < D + K)
  unfold decayRate
  rw [show dampingRatio M D K Tg * natFreq M D K Tg =
    (2 * dampingRatio M D K Tg * natFreq M D K Tg) / 2 by ring, h]
  field_simp

@[powerlib_foundation] theorem decayRate_nonneg (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) : 0 ≤ decayRate M D K Tg := by
  rw [decayRate_eq hM hTg hKD]
  have : 0 ≤ D * Tg := mul_nonneg hD hTg.le
  positivity

@[powerlib_foundation] theorem dampedFreq_pos (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) : 0 < dampedFreq M D K Tg := by
  have hz := dampingRatio_pos hM hTg hD hKD
  exact mul_pos (natFreq_pos hM hTg (by linarith))
    (Real.sqrt_pos.2 (by nlinarith))

@[powerlib_foundation] theorem decayRate_sq_add_dampedFreq_sq (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) :
    decayRate M D K Tg ^ 2 + dampedFreq M D K Tg ^ 2 = natFreq M D K Tg ^ 2 := by
  have hz := dampingRatio_pos hM hTg hD hKD
  unfold decayRate dampedFreq
  rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
  ring

@[powerlib_foundation] theorem trace_A (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 < K + D) :
    (plant M D K Tg).A.trace = -2 * decayRate M D K Tg := by
  rw [decayRate_eq hM hTg hKD, trace_plant]
  field_simp
  ring

@[powerlib_foundation] theorem det_A (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) :
    (plant M D K Tg).A.det = decayRate M D K Tg ^ 2 + dampedFreq M D K Tg ^ 2 := by
  rw [decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ, natFreq_sq hM hTg (by linarith),
    det_plant hM.ne' hTg.ne']
  ring

@[powerlib_foundation] theorem A_mulVec (v : Fin 2 → ℝ) :
    (plant M D K Tg).A *ᵥ v = ![-D / M * v 0 + 1 / M * v 1, -K / Tg * v 0 + -1 / Tg * v 1] := by
  ext i; fin_cases i <;> simp [plant, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The first component of the explicit solution from rest under the load step is the scalar
closed form `respC`. A static identity of closed forms. -/
@[powerlib_foundation] theorem osc2_freq (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) (t : ℝ) :
    (steadyState D K ΔPL + WithLp.toLp 2 (LTI.osc2 (plant M D K Tg).A (decayRate M D K Tg)
      (dampedFreq M D K Tg) (WithLp.ofLp (0 - steadyState D K ΔPL)) t)) 0 =
      respC (ΔPL / (K + D)) (decayRate M D K Tg) (dampedFreq M D K Tg) Tg t := by
  have hsum := decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ
  rw [natFreq_sq hM hTg (by linarith)] at hsum
  have hωd := (dampedFreq_pos hM hTg hD hKD hζ).ne'
  unfold respC
  rw [hsum]
  simp only [LTI.osc2, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, A_mulVec]
  simp [steadyState]
  field_simp
  ring

/-- The closed form at the nadir time is the nadir value. -/
@[powerlib_foundation] theorem respC_nadirTime (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) :
    respC (ΔPL / (K + D)) (decayRate M D K Tg) (dampedFreq M D K Tg) Tg (nadirTime M D K Tg) =
      nadirValue M D K Tg ΔPL := by
  have hωd := dampedFreq_pos hM hTg hD hKD hζ
  have hT : nadirTime M D K Tg = tCrit (decayRate M D K Tg) (dampedFreq M D K Tg) Tg := rfl
  rw [hT, respC_tCrit hωd hTg, tg_mul_norm hTg hωd, ← hT]
  unfold nadirValue
  rw [← decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ]
  ring

/-- The nadir is strictly below the quasi-steady state `−ΔP_L/(K_R + D)`. -/
@[powerlib_foundation] theorem nadirValue_lt (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hP : 0 < ΔPL) (hζ : dampingRatio M D K Tg < 1) :
    nadirValue M D K Tg ΔPL < -ΔPL / (K + D) := by
  have hωd := dampedFreq_pos hM hTg hD hKD hζ
  have hR : 0 < Real.sqrt (1 - 2 * decayRate M D K Tg * Tg + natFreq M D K Tg ^ 2 * Tg ^ 2) := by
    rw [← decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ, ← tg_mul_norm hTg hωd]
    exact mul_pos hTg (arg_facts hωd).2.2.2.2.1
  have hc : 0 < ΔPL / (K + D) := div_pos hP hKD
  unfold nadirValue
  have := mul_pos (mul_pos hc hR) (Real.exp_pos (-(decayRate M D K Tg * nadirTime M D K Tg)))
  rw [neg_div]
  nlinarith

/-! ## Implementation evidence (private, trajectory level) -/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Every forward solution from rest is the closed form `respC` on `t ≥ 0`. -/
private theorem trajectory_freq_eq (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    x t 0 = respC (ΔPL / (K + D)) (decayRate M D K Tg) (dampedFreq M D K Tg) Tg t := by
  rw [LTI.trajectory_eq_osc2 (plant M D K Tg) (steadyState_isEquilibrium hM.ne' hTg.ne' hKD.ne')
    (trace_A hM hTg hKD) (det_A hM hTg hD hKD hζ) (dampedFreq_pos hM hTg hD hKD hζ).ne' hx ht,
    h0]
  exact osc2_freq hM hTg hD hKD hζ t

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.7 frequency nadir, exact: first critical time, strict decrease before it, global minimum over
`t ≥ 0`, and the closed-form value. -/
private theorem nadir (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D) (hKD : 0 < K + D)
    (hP : 0 < ΔPL) (hζ : dampingRatio M D K Tg < 1) {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) :
    0 < nadirTime M D K Tg ∧
      StrictAntiOn (fun t => x t 0) (Icc 0 (nadirTime M D K Tg)) ∧
      IsMinOn (fun t => x t 0) (Ici 0) (nadirTime M D K Tg) ∧
      x (nadirTime M D K Tg) 0 = nadirValue M D K Tg ΔPL := by
  have hωd := dampedFreq_pos hM hTg hD hKD hζ
  have hσ := decayRate_nonneg hM hTg hD hKD
  have hc : 0 < ΔPL / (K + D) := div_pos hP hKD
  have hT : nadirTime M D K Tg = tCrit (decayRate M D K Tg) (dampedFreq M D K Tg) Tg := rfl
  have hfreq := fun {t : ℝ} (ht : 0 ≤ t) => trajectory_freq_eq hM hTg hD hKD hζ hx h0 ht
  have hT0 : 0 < nadirTime M D K Tg := hT ▸ tCrit_pos hωd
  refine ⟨hT0, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only
    rw [hfreq ha.1, hfreq hb.1]
    exact respC_strictAntiOn hωd hTg hc (hT ▸ ha) (hT ▸ hb) hab
  · intro t ht
    simp only [Set.mem_ofPred_eq]
    rw [hfreq ht, hfreq hT0.le, hT]
    exact respC_isMinOn hωd hTg hσ hc ht
  · rw [hfreq hT0.le]
    exact respC_nadirTime hM hTg hD hKD hζ

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Successive extrema: at `t_nadir + kπ/ω_d` the frequency derivative vanishes and the deviation
from the quasi-steady state is multiplied by `(−e^{−σπ/ω_d})^k`. -/
private theorem nadir_successive (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) (k : ℕ) :
    HasDerivWithinAt (fun t => x t 0) 0 (Ici 0)
        (nadirTime M D K Tg + k * (Real.pi / dampedFreq M D K Tg)) ∧
      x (nadirTime M D K Tg + k * (Real.pi / dampedFreq M D K Tg)) 0 + ΔPL / (K + D) =
        (-Real.exp (-(decayRate M D K Tg * (Real.pi / dampedFreq M D K Tg)))) ^ k *
          (x (nadirTime M D K Tg) 0 + ΔPL / (K + D)) := by
  have hωd := dampedFreq_pos hM hTg hD hKD hζ
  have hT : nadirTime M D K Tg = tCrit (decayRate M D K Tg) (dampedFreq M D K Tg) Tg := rfl
  have hT0 : 0 < nadirTime M D K Tg := hT ▸ tCrit_pos hωd
  have hfreq := fun {t : ℝ} (ht : 0 ≤ t) => trajectory_freq_eq hM hTg hD hKD hζ hx h0 ht
  have hpt : ∀ j : ℕ, 0 ≤ nadirTime M D K Tg + j * (Real.pi / dampedFreq M D K Tg) :=
    fun j => by have := Real.pi_pos; positivity
  refine ⟨?_, ?_⟩
  · have hd := (hasDerivAt_respC (c := ΔPL / (K + D)) (σ := decayRate M D K Tg) hωd.ne'
      hTg.ne' (nadirTime M D K Tg + k * (Real.pi / dampedFreq M D K Tg))).hasDerivWithinAt
      (s := Ici 0)
    rw [hT, rateC_tCrit_add hωd, ← hT] at hd
    exact hd.congr (fun y hy => hfreq hy) (hfreq (hpt k))
  · rw [hfreq (hpt k), hfreq hT0.le]
    induction k with
    | zero => simp
    | succ j ih =>
      have := respC_add_half_period (c := ΔPL / (K + D)) (σ := decayRate M D K Tg) (Tg := Tg)
        hωd (nadirTime M D K Tg + j * (Real.pi / dampedFreq M D K Tg))
      rw [show nadirTime M D K Tg + ((j + 1 : ℕ) : ℝ) * (Real.pi / dampedFreq M D K Tg) =
        nadirTime M D K Tg + j * (Real.pi / dampedFreq M D K Tg) +
          Real.pi / dampedFreq M D K Tg by push_cast; ring, this, ih, pow_succ]
      ring

end powerlib.Frequency.SwingGovernor
