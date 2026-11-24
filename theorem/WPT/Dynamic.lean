import theorem.WPT.Compensation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Quasi-static dynamic (in-motion) inductive power transfer

A receiver coil moves along a track of transmitter coils. Its position `x` along the track sets the
mutual inductance `M x` of the coil pair through a given coupling profile `M : ℝ → ℝ`; every other
parameter of the link is fixed. Read quasi-statically, the link at position `x` is the stationary
link of `theorem/WPT/Link.lean` and `theorem/WPT/Compensation.lean` with mutual inductance `M x`.
Two design facts of the track follow. On a series–series (SS) track with lossy windings, every
operating point with a nonzero primary current, at every position, runs at most at the maximum
efficiency `η_max` of the peak coupling `M̄ ≥ |M x|`. A tuned double-sided LCC track with a
lossless secondary winding delivers at position `x` the power `R_L (ωM(x))² |V|²/(X₁X₂)²`: the
power profile along the track is `M(x)²` times a factor that does not depend on the position, and
the load enters only that factor, so the shape of the profile is the same for every load. The time
integral of the profile over a pass along `[a, b]` at constant speed `v > 0` is
`R_L (ω|V|/(X₁X₂))² (1/v) ∫_a^b M(x)² dx`.

Model boundary.
* Track: the receiver position `x : ℝ` along the track; a coupling profile `M : ℝ → ℝ` gives the
  mutual inductance `M x` of the coil pair at `x` (`trackCoils`, `trackLCC`). The winding
  resistances, self-inductances, compensation elements, load, angular frequency `ω` and source
  voltage `V` are fixed and do not depend on the position.
* Quasi-static: at every position the link is in sinusoidal steady state, the phasor equations
  `Link.Solves` of the SS link `ssLink` or `LCC.Solves` of the double-sided LCC network at the
  mutual inductance `M x`. This reading presumes motion much slower than the electrical
  dynamics; no hypothesis of the theorems expresses or checks that. The
  boundaries of `theorem/WPT/Link.lean` and `theorem/WPT/Compensation.lean` apply at each position
  (ideal sinusoidal voltage source, resistive load, linear coils; no inverter, rectifier,
  harmonics or control).
* Excluded: the switching transients of energizing and de-energizing track segments, the
  electrical dynamics of the resonant tanks during the motion, speed-induced effects, and the
  parametric excitation of the circuit by a fast-varying coupling `M(x(t))`.
* SS track: positive winding resistances, `ω ≠ 0`, load `R_L ≥ 0`, operating points with nonzero
  primary current. LCC track: tuning `LCC.Tuned X₁ X₂` (it does not involve `M`), lossless
  secondary winding, `ω, X₁, X₂ ≠ 0`.
* The pass: constant speed `v > 0`, position `a + v t` at time `t`, the times `0 ≤ t ≤ (b − a)/v`
  for `a ≤ b`; its energy is read as the time integral of the quasi-static power profile
  `lccPower`. The identity is one of Mathlib interval integrals and holds for every coupling
  profile (a non-integrable integrand has integral zero on both sides); it is a statement about
  the energy only when `M²` is interval integrable on `[a, b]`.

Source: roadway-powered and in-motion inductive power transfer for transportation (Covic and Boys,
*IEEE J. Emerg. Sel. Topics Power Electron.* 1 (2013) 28–41; Choi, Gu, Jeong and Rim, *IEEE J.
Emerg. Sel. Topics Power Electron.* 3 (2015) 18–36); the stationary SS and double-sided LCC links
of `theorem/WPT/Link.lean` and `theorem/WPT/Compensation.lean`.

Results.
* The track: `trackCoils` (the coil pair with mutual inductance `M x`), `trackLCC` (the LCC
  network whose coil pair has mutual inductance `M x`).
* SS track: `ssTrack_efficiency_le` (with `|M x| ≤ M̄` for every `x`, every operating point with
  nonzero primary current at every position has efficiency at most `η_max` at `(ωM̄)²`, from
  `ssLink_efficiency_le` and `Link.maxEfficiency_strictMono`).
* LCC track: `lccTrack_outputPower` (the output power at position `x` is
  `R_L (ωM(x))² |V|²/(X₁X₂)²`, from `LCC.outputCurrent_eq`), `lccPower` (this power profile),
  `lccPower_eq` (`lccPower = R_L (ω|V|/(X₁X₂))² M(x)²`: proportional to `M(x)²` with a factor
  independent of the position), `lccPower_passEnergy` (the time integral of `lccPower` over a pass
  along `[a, b]` at speed `v > 0` is `R_L (ω|V|/(X₁X₂))² (1/v) ∫_a^b M(x)² dx`).
-/

noncomputable section

namespace powerlib.WPT.Dynamic

open Complex

/-- The coil pair of `w` at track position `x`: the windings of `w` with mutual inductance
`M x`. -/
def trackCoils (w : Passive.Coupled) (M : ℝ → ℝ) (x : ℝ) : Passive.Coupled :=
  ⟨w.primary, w.secondary, M x⟩

/-- The double-sided LCC network `c` at track position `x`: only the mutual inductance of its coil
pair changes, to `M x`. -/
def trackLCC (c : LCC) (M : ℝ → ℝ) (x : ℝ) : LCC :=
  { c with coils := trackCoils c.coils M x }

/-! ## The series–series track -/

/-- The maximum efficiency is monotone in the squared mutual reactance `a = (ωM)²`. -/
@[tmio M, powerlib_domain] private theorem maxEfficiency_mono {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Link.maxEfficiency r₁ r₂ a ≤ Link.maxEfficiency r₁ r₂ b := by
  rcases hab.lt_or_eq with h | h
  · exact (Link.maxEfficiency_strictMono h₁ h₂ ha h).le
  · rw [h]

/-- On an SS track with lossy windings whose coupling never exceeds `M̄` in magnitude, every
operating point with a nonzero primary current, at every position `x`, runs at most at the maximum
efficiency `η_max` of the peak coupling `M̄`. -/
@[tmio M, powerlib_domain] theorem ssTrack_efficiency_le (w : Passive.Coupled) (M : ℝ → ℝ)
    {Mbar RL ω : ℝ} (hω : ω ≠ 0) (hR₁ : 0 < w.primary.R) (hR₂ : 0 < w.secondary.R)
    (hRL : 0 ≤ RL) (hM : ∀ x, |M x| ≤ Mbar) (x : ℝ) {V I₁ I₂ : ℂ}
    (h : (ssLink (trackCoils w M x) RL ω).Solves V I₁ I₂) (hI₁ : I₁ ≠ 0) :
    (ssLink (trackCoils w M x) RL ω).efficiency V I₁ I₂ ≤
      Link.maxEfficiency w.primary.R w.secondary.R ((ω * Mbar) ^ 2) := by
  have hsq : (ω * M x) ^ 2 ≤ (ω * Mbar) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (sq_le_sq' (abs_le.mp (hM x)).1 (abs_le.mp (hM x)).2) (sq_nonneg ω)
  by_cases hMx : ω * M x = 0
  · -- no coupling at `x`: the secondary current and the efficiency vanish
    have hX := tuned_reactance w.secondary.R w.secondary.L hω
    rw [Link.solves_iff] at h
    have h2 := h.2
    simp only [ssLink, tunedCoils, trackCoils, Link.mutualReactance, Link.Z₂,
      Passive.SeriesRLC.impedance_jω, hX, hMx, ofReal_zero, zero_mul, zero_add, add_zero] at h2
    have hR : ((w.secondary.R + RL : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (by linarith : w.secondary.R + RL ≠ 0)
    have hI₂ : I₂ = 0 := by
      refine (mul_eq_zero.mp (?_ : ((w.secondary.R + RL : ℝ) : ℂ) * I₂ = 0)).resolve_left hR
      push_cast
      linear_combination -h2
    rw [Link.efficiency, Link.outputPower, hI₂, map_zero, mul_zero, zero_div]
    unfold Link.maxEfficiency Link.optimalLoad
    positivity
  · exact (ssLink_efficiency_le (trackCoils w M x) hω hR₁ hR₂ hMx hRL h hI₁).trans
      (maxEfficiency_mono hR₁ hR₂ (sq_nonneg _) hsq)

/-! ## The double-sided LCC track -/

/-- On a tuned double-sided LCC track with a lossless secondary winding, the output power at
position `x` is `R_L |I_o|² = R_L (ωM(x))² |V|²/(X₁X₂)²`. -/
@[tmio M, powerlib_domain] theorem lccTrack_outputPower (c : LCC) (M : ℝ → ℝ) {X₁ X₂ : ℝ}
    (ht : c.Tuned X₁ X₂) (hω : c.freq ≠ 0) (hX₁ : X₁ ≠ 0) (hX₂ : X₂ ≠ 0)
    (hR₂ : c.coils.secondary.R = 0) (x : ℝ) {V Iin I₁ I₂ Io VA VB : ℂ}
    (h : (trackLCC c M x).Solves V Iin I₁ I₂ Io VA VB) :
    c.load * normSq Io = c.load * (c.freq * M x) ^ 2 * normSq V / (X₁ * X₂) ^ 2 := by
  have hIo : Io = -(I * (c.freq * M x : ℝ) * V) / (X₁ * X₂ : ℝ) :=
    (trackLCC c M x).outputCurrent_eq ht hω hX₁ hX₂ hR₂ h
  rw [hIo, normSq_div, normSq_neg, normSq_mul, normSq_mul, normSq_I, normSq_ofReal,
    normSq_ofReal]
  ring

/-- The power profile of the LCC track: the output power `R_L (ωM(x))² |V|²/(X₁X₂)²` at
position `x` (`lccTrack_outputPower`). -/
def lccPower (c : LCC) (M : ℝ → ℝ) (X₁ X₂ : ℝ) (V : ℂ) (x : ℝ) : ℝ :=
  c.load * (c.freq * M x) ^ 2 * normSq V / (X₁ * X₂) ^ 2

/-- The LCC power profile is `R_L (ω|V|/(X₁X₂))² M(x)²`: proportional to `M(x)²`, with a factor
that does not depend on the position. -/
@[tmio M, powerlib_domain] theorem lccPower_eq (c : LCC) (M : ℝ → ℝ) (X₁ X₂ : ℝ) (V : ℂ)
    (x : ℝ) :
    lccPower c M X₁ X₂ V x = c.load * (c.freq * ‖V‖ / (X₁ * X₂)) ^ 2 * M x ^ 2 := by
  rw [lccPower, ← Complex.sq_norm]
  ring

/-- The energy of a pass over `[a, b]` at constant speed `v > 0`: the time integral of the LCC
power profile along the position `a + v t` is `R_L (ω|V|/(X₁X₂))² (1/v) ∫_a^b M(x)² dx`. -/
@[tmio M, powerlib_domain] theorem lccPower_passEnergy (c : LCC) (M : ℝ → ℝ) (X₁ X₂ : ℝ)
    (V : ℂ) (a b : ℝ) {v : ℝ} (hv : 0 < v) :
    ∫ t in (0 : ℝ)..(b - a) / v, lccPower c M X₁ X₂ V (a + v * t) =
      c.load * (c.freq * ‖V‖ / (X₁ * X₂)) ^ 2 * (1 / v) * ∫ x in a..b, M x ^ 2 := by
  rw [intervalIntegral.integral_comp_add_mul _ hv.ne', mul_zero, add_zero,
    mul_div_cancel₀ _ hv.ne', add_sub_cancel]
  simp only [lccPower_eq]
  rw [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

end powerlib.WPT.Dynamic
