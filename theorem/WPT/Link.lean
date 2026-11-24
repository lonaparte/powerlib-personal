import theorem.Passive.Coupled

/-! # The two-coil inductive power link in sinusoidal steady state

The coil pair of an inductive wireless power link, each coil a series RLC branch (winding
resistance, self-inductance and its series compensation capacitor), the secondary loaded by a
resistor, driven by a sinusoidal primary voltage. The phasor equations are the coupled pair of
`theorem/Passive/Coupled.lean` at `s = jω` terminated by the load; the currents, the power balance,
the efficiency and the delivered power are derived from them, and the design targets of the link
are theorems about these derived quantities: the secondary tuned to resonance maximizes the
efficiency for every load, the efficiency is bounded by `η_max = U²/(1 + √(1 + U²))²` with the
figure of merit `U² = (ωM)²/(R₁R₂) = k² Q₁ Q₂`, attained exactly at the load
`R_opt = R₂ √(1 + U²)`; the load that maximizes the delivered power is `R₂ + (ωM)²/R₁ = R₂(1 + U²)`,
always heavier than `R_opt`, and it delivers that power below 50 % efficiency.

Model boundary.
* Two coupled coils `coils : Passive.Coupled` (primary `(R₁, L₁, S₁)`, secondary
  `(R₂, L₂, S₂)`, `S_k = 1/C_k` the series compensation capacitors, mutual inductance `M`), a
  resistive load `R_L` (`load`) in series with the secondary, one angular frequency `ω` (`freq`).
  The compensation is series–series (SS); `S_k = 0` is an uncompensated coil.
* Sinusoidal steady state with RMS phasors: the primary voltage `V`, the primary current `I₁` and
  the secondary current `I₂` satisfy `V = Z₁(jω) I₁ + jωM I₂`, `0 = jωM I₁ + (Z₂(jω) + R_L) I₂`
  (`Solves`, the terminated two-port `Grid.TwoPort.Terminated` of `Passive.Coupled.impedanceMatrix`
  at `s = jω`).
* The source is an ideal sinusoidal voltage: no inverter, harmonics, dead time or DC link; the
  load is an ideal resistor: no rectifier, filter or battery. Linear coils with constant
  parameters (the boundary of `Passive.Coupled`). Transients, control and frequency tracking are
  excluded (`theorem/WPT/Resonator.lean`, `theorem/WPT/Tracking.lean`).
* The figure of merit and the optima are stated for positive winding resistances and a nonzero
  mutual reactance `ωM`; the efficiency is the ratio of the load power to the real input power.

Source: the series–series compensated two-coil link (Wang, Covic and Stielau, *IEEE Trans. Ind.
Electron.* 51 (2004) 148–157; Zhang and Mi, *IEEE Trans. Veh. Technol.* 65 (2016) 4768–4778); the
maximum efficiency `η_max = U²/(1 + √(1 + U²))²` at `R_L = R₂ √(1 + U²)` with
`U = ωM/√(R₁R₂) = k √(Q₁Q₂)` (Zhong and Hui, *IEEE Trans. Power Electron.* 30 (2015) 4025–4034;
Kurs et al., *Science* 317 (2007) 83–86, for the coupled-mode figure of merit); the reflected
impedance of `theorem/Passive/Coupled.lean`.

Results.
* The model: `Link` (`coils`, `load`, `freq`), `Solves`, `determinant`
  (`Z₁(Z₂ + R_L) + (ωM)²`), `inputPower` (`Re(V Ī₁)`), `outputPower` (`R_L |I₂|²`),
  `efficiency`, `quality` (`Q = ωL/R`).
* Solutions: `currents_eq` (with a nonzero determinant every solution is
  `I₁ = (Z₂ + R_L) V/Δ`, `I₂ = −jωM V/Δ`), `solves_currents` (and these solve the equations);
  `inputPower_eq` (power balance: `Re(V Ī₁) = R₁|I₁|² + (R₂ + R_L)|I₂|²`).
* Efficiency: `eta` (`R a/(R₁((R₂ + R)² + X₂²) + (R₂ + R) a)`, `a = (ωM)²`), `efficiency_eq` (the
  efficiency of every solution with `I₁ ≠ 0` is `eta` at the secondary reactance `X₂(ω)`; it does not
  depend on the primary reactance or the source), `eta_le_resonant` (tuning the secondary to
  resonance, `X₂ = 0`, maximizes the efficiency for every load).
* The optimal load: `fomSq` (`U²`), `optimalLoad`, `maxEfficiency`; `eta_le_maxEfficiency`,
  `eta_eq_maxEfficiency_iff` (the resonant efficiency never exceeds `η_max` and reaches it exactly
  at `R_opt`), `optimalLoad_eq_fom` (`R_opt = R₂ √(1 + U²)`), `maxEfficiency_eq_fom`
  (`η_max = U²/(1 + √(1 + U²))²`), `maxEfficiency_eq_fom'` (`(√(1 + U²) − 1)/(√(1 + U²) + 1)`),
  `maxEfficiency_lt_one`, `maxEfficiency_strictMono` (the bound grows strictly with `U²`),
  `fomSq_eq` (`U² = k² Q₁ Q₂`).
* The maximum power: `outputPower_resonant` (with both coils resonant, `R_L |I₂|² =
  R_L a |V|²/(R₁(R₂ + R_L) + a)²`), `deliveredPower` and `deliveredPower_le`,
  `deliveredPower_eq_max_iff` (the delivered power is largest exactly at `R_L = R₂ + a/R₁`),
  `eta_maxPowerLoad` (there the efficiency is `a/(2(2R₁R₂ + a)) = U²/(2(U² + 2))`),
  `eta_maxPowerLoad_lt_half`, `optimalLoad_lt_maxPowerLoad` (`R_opt < R₂ + a/R₁`).
* Resonant operation: `inputImpedance_resonant` (both coils resonant: the input impedance is the
  real `R₁ + a/(R₂ + R_L)`, zero phase angle for every load), `secondaryCurrent_of_lossless_primary`
  (a resonant lossless primary, `Z₁(jω) = 0`, gives the load-independent output current
  `I₂ = −jV/(ωM)`, whatever the secondary and the load).
-/

noncomputable section

namespace powerlib.WPT

open ComplexConjugate

/-- A two-coil inductive link: the coil pair, the load resistance and the angular frequency. -/
@[ext] structure Link where
  /-- The coil pair with its series compensation capacitors. -/
  coils : Passive.Coupled
  /-- The load resistance `R_L` in series with the secondary. -/
  load : ℝ
  /-- The angular frequency `ω`. -/
  freq : ℝ

namespace Link

variable (l : Link)

/-- The phasor equations: `V = Z₁(jω) I₁ + jωM I₂`, `0 = jωM I₁ + (Z₂(jω) + R_L) I₂`. -/
def Solves (V I₁ I₂ : ℂ) : Prop :=
  Grid.TwoPort.Terminated (l.coils.impedanceMatrix (l.freq * Complex.I)) l.load V I₁ I₂

/-- The primary impedance `Z₁(jω)`. -/
abbrev Z₁ : ℂ := l.coils.primary.impedance (l.freq * Complex.I)

/-- The secondary impedance `Z₂(jω)`. -/
abbrev Z₂ : ℂ := l.coils.secondary.impedance (l.freq * Complex.I)

/-- The mutual reactance `ωM`. -/
abbrev mutualReactance : ℝ := l.freq * l.coils.M

/-- The determinant `Δ = Z₁ (Z₂ + R_L) + (ωM)²` of the phasor equations. -/
def determinant : ℂ := l.Z₁ * (l.Z₂ + l.load) + (l.mutualReactance : ℂ) ^ 2

/-- The real input power `Re(V Ī₁)`. -/
def inputPower (V I₁ : ℂ) : ℝ := (V * conj I₁).re

/-- The load power `R_L |I₂|²`. -/
def outputPower (I₂ : ℂ) : ℝ := l.load * Complex.normSq I₂

/-- The efficiency: the load power over the real input power. -/
def efficiency (V I₁ I₂ : ℂ) : ℝ := l.outputPower I₂ / inputPower V I₁

/-- The quality factor `Q = ωL/R` of a coil at `ω`. -/
def quality (ω : ℝ) (b : Passive.SeriesRLC) : ℝ := ω * b.L / b.R

/-- The phasor equations written out. -/
@[tmio M, powerlib_domain] theorem solves_iff (V I₁ I₂ : ℂ) :
    l.Solves V I₁ I₂ ↔ V = l.Z₁ * I₁ + (l.mutualReactance * Complex.I : ℂ) * I₂ ∧
      -(l.load * I₂) = (l.mutualReactance * Complex.I : ℂ) * I₁ + l.Z₂ * I₂ := by
  have e : (l.coils.M : ℂ) * (l.freq * Complex.I) = (l.mutualReactance * Complex.I : ℂ) := by
    push_cast
    ring
  simp only [Solves, Grid.TwoPort.Terminated, Grid.TwoPort.Equations,
    Passive.Coupled.impedanceMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, e]

/-! ## Solutions and the power balance -/

/-- With a nonzero determinant every solution is `I₁ = (Z₂ + R_L) V/Δ`, `I₂ = −jωM V/Δ`. -/
@[tmio M, powerlib_domain] theorem currents_eq {V I₁ I₂ : ℂ} (h : l.Solves V I₁ I₂)
    (hΔ : l.determinant ≠ 0) :
    I₁ = (l.Z₂ + l.load) * V / l.determinant ∧
      I₂ = -((l.mutualReactance * Complex.I : ℂ) * V) / l.determinant := by
  rw [solves_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  constructor
  · rw [eq_div_iff hΔ, determinant]
    linear_combination (-(l.Z₂ + l.load)) * h1 + (l.mutualReactance * Complex.I : ℂ) * h2 +
      (l.mutualReactance : ℂ) ^ 2 * I₁ * hI
  · rw [eq_div_iff hΔ, determinant]
    linear_combination (l.mutualReactance * Complex.I : ℂ) * h1 + (-l.Z₁) * h2 +
      (l.mutualReactance : ℂ) ^ 2 * I₂ * hI

/-- The currents `I₁ = (Z₂ + R_L) V/Δ`, `I₂ = −jωM V/Δ` solve the phasor equations. -/
@[tmio M, powerlib_domain] theorem solves_currents (V : ℂ) (hΔ : l.determinant ≠ 0) :
    l.Solves V ((l.Z₂ + l.load) * V / l.determinant)
      (-((l.mutualReactance * Complex.I : ℂ) * V) / l.determinant) := by
  rw [solves_iff]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  constructor
  · field_simp
    rw [determinant]
    linear_combination ((l.mutualReactance : ℂ) ^ 2 * V) * hI
  · field_simp
    ring

/-- Power balance: the real input power is dissipated in the two windings and the load,
`Re(V Ī₁) = R₁|I₁|² + (R₂ + R_L)|I₂|²`. -/
@[tmio M, powerlib_domain] theorem inputPower_eq {V I₁ I₂ : ℂ} (h : l.Solves V I₁ I₂) :
    inputPower V I₁ = l.coils.primary.R * Complex.normSq I₁ +
      (l.coils.secondary.R + l.load) * Complex.normSq I₂ := by
  rw [solves_iff, Z₁, Z₂, Passive.SeriesRLC.impedance_jω, Passive.SeriesRLC.impedance_jω] at h
  obtain ⟨h1, h2⟩ := h
  have h2r := congrArg Complex.re h2
  have h2i := congrArg Complex.im h2
  rw [inputPower, h1]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.neg_re, Complex.neg_im] at h2r h2i ⊢
  linear_combination (I₂.re) * h2r + (I₂.im) * h2i

/-! ## The efficiency -/

/-- The efficiency of the link as a function of the primary resistance `r₁`, the secondary
resistance `r₂`, the secondary reactance `x`, the squared mutual reactance `a = (ωM)²` and the
load `R`: `R a/(r₁((r₂ + R)² + x²) + (r₂ + R) a)`. -/
def eta (r₁ r₂ x a R : ℝ) : ℝ := R * a / (r₁ * ((r₂ + R) ^ 2 + x ^ 2) + (r₂ + R) * a)

/-- The efficiency of every solution with a nonzero primary current is `eta` at the secondary
reactance: it depends neither on the primary reactance nor on the source. -/
@[tmio M, powerlib_domain] theorem efficiency_eq {V I₁ I₂ : ℂ} (h : l.Solves V I₁ I₂)
    (hI₁ : I₁ ≠ 0) (hZ : l.Z₂ + l.load ≠ 0) :
    l.efficiency V I₁ I₂ = eta l.coils.primary.R l.coils.secondary.R
      (l.coils.secondary.reactance l.freq) (l.mutualReactance ^ 2) l.load := by
  have hP := l.inputPower_eq h
  rw [solves_iff] at h
  have hI2 := Grid.TwoPort.terminated_current
    (Z := !![l.Z₁, (l.mutualReactance * Complex.I : ℂ); (l.mutualReactance * Complex.I : ℂ), l.Z₂])
    (ZL := l.load) (v₁ := V) (i₁ := I₁) (i₂ := I₂) (by simpa [Grid.TwoPort.Terminated,
      Grid.TwoPort.Equations] using h) (by simpa using hZ)
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hI2
  set N := (l.coils.secondary.R + l.load) ^ 2 + l.coils.secondary.reactance l.freq ^ 2 with hN
  have hNZ : Complex.normSq (l.Z₂ + l.load) = N := by
    rw [Z₂, Passive.SeriesRLC.impedance_jω, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [hN]
    ring
  have hN0 : N ≠ 0 := by
    rw [← hNZ]
    exact (Complex.normSq_pos.mpr hZ).ne'
  have hsq : Complex.normSq I₂ = l.mutualReactance ^ 2 * Complex.normSq I₁ / N := by
    rw [hI2, Complex.normSq_div, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_mul,
      hNZ, Complex.normSq_I, Complex.normSq_ofReal]
    ring
  have hn1 : Complex.normSq I₁ ≠ 0 := (Complex.normSq_pos.mpr hI₁).ne'
  rw [efficiency, outputPower, hP, hsq, eta]
  have hc : Complex.normSq I₁ / N ≠ 0 := div_ne_zero hn1 hN0
  rw [show l.load * (l.mutualReactance ^ 2 * Complex.normSq I₁ / N) =
      Complex.normSq I₁ / N * (l.load * l.mutualReactance ^ 2) by ring,
    show l.coils.primary.R * Complex.normSq I₁ + (l.coils.secondary.R + l.load) *
      (l.mutualReactance ^ 2 * Complex.normSq I₁ / N) = Complex.normSq I₁ / N *
        (l.coils.primary.R * N + (l.coils.secondary.R + l.load) * l.mutualReactance ^ 2) by
      field_simp,
    mul_div_mul_left _ _ hc]

/-- Tuning the secondary to resonance (`X₂ = 0`) maximizes the efficiency for every load. -/
@[tmio M, powerlib_domain] theorem eta_le_resonant {r₁ r₂ a R : ℝ} (h₁ : 0 ≤ r₁) (ha : 0 < a)
    (hR : 0 ≤ R) (h₂ : 0 < r₂ + R) (x : ℝ) : eta r₁ r₂ x a R ≤ eta r₁ r₂ 0 a R := by
  unfold eta
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [mul_nonneg h₁ (sq_nonneg x)]

/-! ## The optimal load and the maximum efficiency -/

/-- The squared figure of merit `U² = a/(r₁ r₂)`. -/
def fomSq (r₁ r₂ a : ℝ) : ℝ := a / (r₁ * r₂)

/-- The efficiency-optimal load `R_opt = √(r₂ (r₂ + a/r₁))`. -/
def optimalLoad (r₁ r₂ a : ℝ) : ℝ := Real.sqrt (r₂ * (r₂ + a / r₁))

/-- The maximum efficiency `(a/r₁)/(2 r₂ + 2 R_opt + a/r₁)`. -/
def maxEfficiency (r₁ r₂ a : ℝ) : ℝ := (a / r₁) / (2 * r₂ + 2 * optimalLoad r₁ r₂ a + a / r₁)

/-- The resonant efficiency `R c/((r₂ + R)(r₂ + R + c))` with `c = a/r₁`. -/
@[tmio M, powerlib_domain] theorem eta_resonant_eq {r₁ r₂ a R : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (ha : 0 ≤ a) (hR : 0 ≤ R) :
    eta r₁ r₂ 0 a R = R * (a / r₁) / ((r₂ + R) * (r₂ + R + a / r₁)) := by
  unfold eta
  have : 0 < r₂ + R := by linarith
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem optimalLoad_sq {r₁ r₂ a : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (ha : 0 ≤ a) : optimalLoad r₁ r₂ a ^ 2 = r₂ * (r₂ + a / r₁) := by
  unfold optimalLoad
  rw [Real.sq_sqrt (by positivity)]

/-- The resonant efficiency never exceeds `η_max`. -/
@[tmio M, powerlib_domain] theorem eta_le_maxEfficiency {r₁ r₂ a R : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (ha : 0 < a) (hR : 0 ≤ R) : eta r₁ r₂ 0 a R ≤ maxEfficiency r₁ r₂ a := by
  rw [eta_resonant_eq h₁ h₂ ha.le hR, maxEfficiency]
  have hc0 : 0 < a / r₁ := div_pos ha h₁
  have hs0 : 0 ≤ optimalLoad r₁ r₂ a := Real.sqrt_nonneg _
  have hss := optimalLoad_sq h₁ h₂ ha.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (R - optimalLoad r₁ r₂ a)]

/-- The resonant efficiency reaches `η_max` exactly at the optimal load. -/
@[tmio M, powerlib_domain] theorem eta_eq_maxEfficiency_iff {r₁ r₂ a R : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (ha : 0 < a) (hR : 0 ≤ R) :
    eta r₁ r₂ 0 a R = maxEfficiency r₁ r₂ a ↔ R = optimalLoad r₁ r₂ a := by
  rw [eta_resonant_eq h₁ h₂ ha.le hR, maxEfficiency]
  have hc0 : 0 < a / r₁ := div_pos ha h₁
  have hs0 : 0 ≤ optimalLoad r₁ r₂ a := Real.sqrt_nonneg _
  have hss := optimalLoad_sq h₁ h₂ ha.le
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    have h0 : a / r₁ * (R - optimalLoad r₁ r₂ a) ^ 2 = 0 := by nlinarith
    have := (mul_eq_zero.mp h0).resolve_left hc0.ne'
    nlinarith [pow_eq_zero_iff (n := 2) (a := R - optimalLoad r₁ r₂ a) two_ne_zero |>.mp this]
  · rintro rfl
    nlinarith

/-- `R_opt = r₂ √(1 + U²)`. -/
@[tmio M, powerlib_domain] theorem optimalLoad_eq_fom {r₁ r₂ a : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    optimalLoad r₁ r₂ a = r₂ * Real.sqrt (1 + fomSq r₁ r₂ a) := by
  unfold optimalLoad fomSq
  rw [show r₂ * Real.sqrt (1 + a / (r₁ * r₂)) = Real.sqrt (r₂ ^ 2 * (1 + a / (r₁ * r₂))) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h₂.le]]
  congr 1
  field_simp

/-- `η_max = U²/(1 + √(1 + U²))²`. -/
@[tmio M, powerlib_domain] theorem maxEfficiency_eq_fom {r₁ r₂ a : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (ha : 0 ≤ a) :
    maxEfficiency r₁ r₂ a = fomSq r₁ r₂ a / (1 + Real.sqrt (1 + fomSq r₁ r₂ a)) ^ 2 := by
  have hq : 0 ≤ Real.sqrt (1 + fomSq r₁ r₂ a) := Real.sqrt_nonneg _
  have hqq : Real.sqrt (1 + fomSq r₁ r₂ a) ^ 2 = 1 + a / (r₁ * r₂) := by
    rw [Real.sq_sqrt (by unfold fomSq; positivity)]; rfl
  rw [maxEfficiency, optimalLoad_eq_fom h₁ h₂]
  unfold fomSq at *
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp at hqq ⊢
  nlinarith [hqq]

/-- `η_max = (√(1 + U²) − 1)/(√(1 + U²) + 1)`. -/
@[tmio M, powerlib_domain] theorem maxEfficiency_eq_fom' {r₁ r₂ a : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (ha : 0 ≤ a) :
    maxEfficiency r₁ r₂ a =
      (Real.sqrt (1 + fomSq r₁ r₂ a) - 1) / (Real.sqrt (1 + fomSq r₁ r₂ a) + 1) := by
  rw [maxEfficiency_eq_fom h₁ h₂ ha]
  have hU : 0 ≤ fomSq r₁ r₂ a := by unfold fomSq; positivity
  have hq : 0 ≤ Real.sqrt (1 + fomSq r₁ r₂ a) := Real.sqrt_nonneg _
  have hqq : Real.sqrt (1 + fomSq r₁ r₂ a) ^ 2 = 1 + fomSq r₁ r₂ a := Real.sq_sqrt (by linarith)
  rw [div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [hqq]

/-- The maximum efficiency is below one. -/
@[tmio M, powerlib_domain] theorem maxEfficiency_lt_one {r₁ r₂ a : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (ha : 0 ≤ a) : maxEfficiency r₁ r₂ a < 1 := by
  rw [maxEfficiency_eq_fom' h₁ h₂ ha]
  have hq : 0 ≤ Real.sqrt (1 + fomSq r₁ r₂ a) := Real.sqrt_nonneg _
  rw [div_lt_one (by positivity)]
  linarith

/-- The maximum efficiency grows strictly with the squared figure of merit: at fixed winding
resistances, `η_max` is strictly increasing in `a = (ωM)²`. -/
@[tmio M, powerlib_domain] theorem maxEfficiency_strictMono {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    maxEfficiency r₁ r₂ a < maxEfficiency r₁ r₂ b := by
  rw [maxEfficiency_eq_fom' h₁ h₂ ha, maxEfficiency_eq_fom' h₁ h₂ (ha.trans hab.le)]
  have hU : fomSq r₁ r₂ a < fomSq r₁ r₂ b := by
    unfold fomSq
    exact div_lt_div_of_pos_right hab (mul_pos h₁ h₂)
  have hUa : 0 ≤ fomSq r₁ r₂ a := by unfold fomSq; positivity
  have hs : Real.sqrt (1 + fomSq r₁ r₂ a) < Real.sqrt (1 + fomSq r₁ r₂ b) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hq : 0 ≤ Real.sqrt (1 + fomSq r₁ r₂ a) := Real.sqrt_nonneg _
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The figure of merit of the coil pair is `U² = (ωM)²/(R₁R₂) = k² Q₁ Q₂`. -/
@[tmio M, powerlib_domain] theorem fomSq_eq (ω : ℝ) (w : Passive.Coupled)
    (hL : 0 < w.primary.L * w.secondary.L) (hR₁ : w.primary.R ≠ 0) (hR₂ : w.secondary.R ≠ 0) :
    fomSq w.primary.R w.secondary.R ((ω * w.M) ^ 2) =
      w.coupling ^ 2 * quality ω w.primary * quality ω w.secondary := by
  rw [Passive.Coupled.coupling_sq hL, fomSq, quality, quality]
  have h1 : w.primary.L ≠ 0 := by
    intro h; rw [h, zero_mul] at hL; exact lt_irrefl 0 hL
  have h2 : w.secondary.L ≠ 0 := by
    intro h; rw [h, mul_zero] at hL; exact lt_irrefl 0 hL
  field_simp

/-! ## The maximum delivered power -/

/-- With both coils resonant (`Z₁ = R₁`, `Z₂ = R₂`), the load power of a solution is
`R_L a |V|²/(R₁(R₂ + R_L) + a)²`. -/
@[tmio M, powerlib_domain] theorem outputPower_resonant {V I₁ I₂ : ℂ} (h : l.Solves V I₁ I₂)
    (hX₁ : l.coils.primary.reactance l.freq = 0) (hX₂ : l.coils.secondary.reactance l.freq = 0)
    (hΔ : l.determinant ≠ 0) :
    l.outputPower I₂ = l.load * l.mutualReactance ^ 2 * Complex.normSq V /
      (l.coils.primary.R * (l.coils.secondary.R + l.load) + l.mutualReactance ^ 2) ^ 2 := by
  have hD : l.determinant = ((l.coils.primary.R * (l.coils.secondary.R + l.load) +
      l.mutualReactance ^ 2 : ℝ) : ℂ) := by
    rw [determinant, Z₁, Z₂, Passive.SeriesRLC.impedance_jω, Passive.SeriesRLC.impedance_jω, hX₁,
      hX₂]
    push_cast
    ring
  rw [outputPower, (l.currents_eq h hΔ).2, Complex.normSq_div, Complex.normSq_neg,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, hD,
    Complex.normSq_ofReal]
  ring

/-- The resonant load power `R a/(r₁(r₂ + R) + a)²` per unit `|V|²`. -/
def deliveredPower (r₁ r₂ a R : ℝ) : ℝ := R * a / (r₁ * (r₂ + R) + a) ^ 2

/-- The delivered power never exceeds `a/(4 r₁ (r₁ r₂ + a))`. -/
@[tmio M, powerlib_domain] theorem deliveredPower_le {r₁ r₂ a R : ℝ} (h₁ : 0 < r₁) (h₂ : 0 ≤ r₂)
    (ha : 0 < a) (hR : 0 ≤ R) :
    deliveredPower r₁ r₂ a R ≤ a / (4 * r₁ * (r₁ * r₂ + a)) := by
  unfold deliveredPower
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (r₁ * R - (r₁ * r₂ + a)), mul_pos h₁ ha]

/-- The delivered power is largest exactly at the load `R₂ + a/R₁`. -/
@[tmio M, powerlib_domain] theorem deliveredPower_eq_max_iff {r₁ r₂ a R : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 ≤ r₂) (ha : 0 < a) (hR : 0 ≤ R) :
    deliveredPower r₁ r₂ a R = a / (4 * r₁ * (r₁ * r₂ + a)) ↔ R = r₂ + a / r₁ := by
  unfold deliveredPower
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    have h0 : a * (r₁ * R - (r₁ * r₂ + a)) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp h0).resolve_left ha.ne')
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- At the maximum-power load the efficiency is `a/(2(2 r₁ r₂ + a)) = U²/(2(U² + 2))`. -/
@[tmio M, powerlib_domain] theorem eta_maxPowerLoad {r₁ r₂ a : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (ha : 0 < a) : eta r₁ r₂ 0 a (r₂ + a / r₁) = a / (2 * (2 * r₁ * r₂ + a)) := by
  unfold eta
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-- Maximum power is delivered below 50 % efficiency. -/
@[tmio M, powerlib_domain] theorem eta_maxPowerLoad_lt_half {r₁ r₂ a : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (ha : 0 < a) : eta r₁ r₂ 0 a (r₂ + a / r₁) < 1 / 2 := by
  rw [eta_maxPowerLoad h₁ h₂ ha, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h₁ h₂]

/-- The efficiency-optimal load is lighter than the maximum-power load: `R_opt < R₂ + a/R₁`. -/
@[tmio M, powerlib_domain] theorem optimalLoad_lt_maxPowerLoad {r₁ r₂ a : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (ha : 0 < a) : optimalLoad r₁ r₂ a < r₂ + a / r₁ := by
  have hc : 0 < a / r₁ := div_pos ha h₁
  have hss := optimalLoad_sq h₁ h₂ ha.le
  have hs0 : 0 ≤ optimalLoad r₁ r₂ a := Real.sqrt_nonneg _
  nlinarith

/-! ## Resonant operation -/

/-- With both coils resonant the input impedance is the real `R₁ + a/(R₂ + R_L)`: zero phase
angle for every load. -/
@[tmio M, powerlib_domain] theorem inputImpedance_resonant
    (hX₁ : l.coils.primary.reactance l.freq = 0) (hX₂ : l.coils.secondary.reactance l.freq = 0) :
    l.coils.inputImpedance l.load (l.freq * Complex.I) =
      ((l.coils.primary.R + l.mutualReactance ^ 2 / (l.coils.secondary.R + l.load) : ℝ) : ℂ) := by
  rw [Passive.Coupled.inputImpedance_jω, Passive.SeriesRLC.impedance_jω,
    Passive.SeriesRLC.impedance_jω, hX₁, hX₂]
  push_cast
  ring

/-- A resonant lossless primary (`Z₁(jω) = 0`) gives the load-independent output current
`I₂ = −jV/(ωM)`, whatever the secondary and the load. -/
@[tmio M, powerlib_domain] theorem secondaryCurrent_of_lossless_primary {V I₁ I₂ : ℂ}
    (h : l.Solves V I₁ I₂) (hZ₁ : l.Z₁ = 0) (hM : l.mutualReactance ≠ 0) :
    I₂ = -(Complex.I * V) / (l.mutualReactance : ℂ) := by
  rw [solves_iff, hZ₁, zero_mul, zero_add] at h
  have hm : (l.mutualReactance : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [eq_div_iff hm]
  linear_combination Complex.I * h.1 + (l.mutualReactance : ℂ) * I₂ * Complex.I_sq

end Link

end powerlib.WPT
