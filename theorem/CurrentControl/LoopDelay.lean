import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import theorem.Attributes

/-! # Phase margin of the IMC current loop with a transport delay (foundation)

Model: one axis of the IMC-tuned current loop of `Drives.CascadeControl` (RL plant `1/(Ls + R)`,
PI `K_p = Lα`, `K_i = Rα`, so the delay-free open loop is exactly `α/s`), in series with a pure
transport delay `τ ≥ 0` lumping computation and PWM delay (`τ_d ≈ 1.5 T_s`).  Open-loop
frequency response `L(jω) = (α/(jω)) e^{−jωτ}`, `α > 0`, continuous time, linear, no
saturation.  The phase margin is `PM = π + arg L(jω_c)` at the unique gain crossover `ω_c`.
These are frequency-domain identities only (no closed-loop stability statement for the delay
system is claimed).

Results.
* `imcDelayLoop_norm`, `imcDelayLoop_norm_eq_one_iff`: `|L(jω)| = α/ω`, so the gain
  crossover is exactly `ω_c = α` (the bandwidth `ω_b`).
* `imcDelayLoop_arg_crossover`: for `ατ < π/2`, `arg L(jα) = −π/2 − ατ`, i.e.
  `PM = π/2 − ατ`.
* `imcDelayLoop_pm60_iff`: `PM ≥ 60°` (with `ατ < π/2`) iff `ω_b = α ≤ π/(6τ)`.
* `imcDelayLoop_noteBound_pm`: at the note's bound `ω_b = π/(3τ)` the phase margin is
  `π/6` (30°), not 60°.

Source: work-sync theory/T-field-oriented-control.md §2.4 ("严格 60° PM 上限
`ω_b ≤ π/(3τ_d)`"), theory/T-control-delay.md §1.6.

Correction: the "strict 60° phase-margin bound `ω_b τ_d ≤ π/3`" is not the 60° bound of the
FOC current loop: with the IMC loop `α/s` (phase `−π/2`) the delay may only use
`π/2 − π/3 = π/6`, so the strict bound is `ω_b ≤ π/(6τ_d)` (≈ 3.5 krad/s at
`τ_d = 150 µs`), and `ω_b = π/(3τ_d)` yields only 30° (`imcDelayLoop_noteBound_pm`).
-/

noncomputable section
namespace powerlib.CurrentControl.LoopDelay

open Complex

/-- Open-loop frequency response `L(jω) = (α/(jω)) e^{−jωτ}`. -/
def imcDelayLoop (α τ ω : ℝ) : ℂ := (α : ℂ) / (I * ω) * exp (-(I * ω * τ))

@[powerlib_foundation] theorem norm_exp_neg_I_mul (ω τ : ℝ) : ‖exp (-(I * ω * τ))‖ = 1 := by
  rw [show -(I * ω * τ) = ((-(ω * τ) : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- `|L(jω)| = α/ω` for `α, ω > 0`. -/
@[powerlib_foundation] theorem imcDelayLoop_norm {α τ ω : ℝ} (hα : 0 < α) (hω : 0 < ω) :
    ‖imcDelayLoop α τ ω‖ = α / ω := by
  rw [imcDelayLoop, norm_mul, norm_exp_neg_I_mul, mul_one, norm_div, norm_mul, norm_I, one_mul,
    norm_real, norm_real, Real.norm_of_nonneg hα.le, Real.norm_of_nonneg hω.le]

/-- The gain crossover of the delayed IMC loop is exactly `ω_c = α`. -/
@[powerlib_foundation] theorem imcDelayLoop_norm_eq_one_iff {α τ ω : ℝ} (hα : 0 < α)
    (hω : 0 < ω) : ‖imcDelayLoop α τ ω‖ = 1 ↔ ω = α := by
  rw [imcDelayLoop_norm hα hω, div_eq_one_iff_eq hω.ne']
  exact eq_comm

/-- At the crossover, `L(jα) = e^{j(−π/2 − ατ)}`. -/
@[powerlib_foundation] theorem imcDelayLoop_crossover_eq {α τ : ℝ} (hα : 0 < α) :
    imcDelayLoop α τ α = exp (((-(Real.pi / 2) - α * τ) : ℝ) * I) := by
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have h1 : (α : ℂ) / (I * α) = exp (((-(Real.pi / 2)) : ℝ) * I) := by
    rw [show (((-(Real.pi / 2)) : ℝ) : ℂ) * I = -(↑(Real.pi / 2) * I) by push_cast; ring,
      exp_neg, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    field_simp
    simp
  rw [imcDelayLoop, h1, ← exp_add]
  congr 1
  push_cast
  ring

/-- **Phase at crossover**: for `ατ < π/2`, `arg L(jα) = −π/2 − ατ`; hence the phase margin
is `PM = π + arg L(jα) = π/2 − ατ`. -/
@[powerlib_foundation] theorem imcDelayLoop_arg_crossover {α τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (hsmall : α * τ < Real.pi / 2) :
    arg (imcDelayLoop α τ α) = -(Real.pi / 2) - α * τ := by
  rw [imcDelayLoop_crossover_eq hα, arg_exp_mul_I, toIocMod_eq_self]
  have h0 : 0 ≤ α * τ := mul_nonneg hα.le hτ
  constructor <;> linarith [Real.pi_pos]

/-- **60° phase margin bound**: `PM ≥ π/3` with `ατ < π/2` iff `α ≤ π/(6τ)`. -/
@[powerlib_foundation] theorem imcDelayLoop_pm60_iff {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) :
    (α * τ < Real.pi / 2 ∧ Real.pi / 3 ≤ Real.pi + arg (imcDelayLoop α τ α)) ↔
      α ≤ Real.pi / (6 * τ) := by
  rw [le_div_iff₀ (by positivity)]
  constructor
  · rintro ⟨hs, hpm⟩
    rw [imcDelayLoop_arg_crossover hα hτ.le hs] at hpm
    linarith
  · intro h
    have hs : α * τ < Real.pi / 2 := by nlinarith [Real.pi_pos]
    refine ⟨hs, ?_⟩
    rw [imcDelayLoop_arg_crossover hα hτ.le hs]
    nlinarith [Real.pi_pos]

/-- **The note's bound `ω_b = π/(3τ)` gives only a 30° phase margin.** -/
@[powerlib_foundation] theorem imcDelayLoop_noteBound_pm {τ : ℝ} (hτ : 0 < τ) :
    Real.pi + arg (imcDelayLoop (Real.pi / (3 * τ)) τ (Real.pi / (3 * τ))) = Real.pi / 6 := by
  have hα : 0 < Real.pi / (3 * τ) := by positivity
  have hατ : Real.pi / (3 * τ) * τ = Real.pi / 3 := by field_simp
  rw [imcDelayLoop_arg_crossover hα hτ.le (by rw [hατ]; linarith [Real.pi_pos]), hατ]
  ring

end powerlib.CurrentControl.LoopDelay
