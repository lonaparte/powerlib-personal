import theorem.WPT.Compensation

/-! # Primary-side identification of the coupling and the load of the series–series link

What input-impedance values of the series–series link determine about its secondary side. The
coil pair is known (winding resistances and self-inductances of both coils, both series
capacitors tuned at the design frequency `ω₀`); the unknowns are the mutual inductance `M` and the
load `R_L`, with `R = R₂ + R_L` the total secondary resistance. The input impedance is
`Z_in(jω) = Z₁(jω) + Z_r(ω)` with the reflected impedance `Z_r(ω) = (ωM)²/(R + jX₂(ω))`
(`Passive.Coupled.inputImpedance_jω`). Primary-side, communication-free estimation of the load
and of the misalignment (a change of `M`) reads `M` and `R_L` from `Z_r`.

At the resonant frequency `X₂(ω₀) = 0` and `Z_in(jω₀) = R₁ + (ω₀M)²/R` (`ssLink_inputImpedance`)
is real: it depends on `(M, R_L)` only through `(ω₀M)²/R`, so doubling `M` and quadrupling `R`
leaves it unchanged, and one resonant value cannot separate a coupling change from a load change.
At a frequency with `X₂(ω) ≠ 0` the complex value `Z_r(ω)` gives two real equations, and with
`M ≠ 0` it determines `R_L` and `M²`, through the explicit formulas `R = −X₂ Re Z_r/Im Z_r` and
`(ωM)² = Re Z_r (R² + X₂²)/R`. The sign of `M` is never determined: `Z_in` depends on `M` only
through `M²`.

Model boundary.
* The coil pair `tunedCoils ⟨w.primary, w.secondary, M⟩ ω₀` (`theorem/WPT/Compensation.lean`):
  the known windings `w.primary = (R₁, L₁, ·)`, `w.secondary = (R₂, L₂, ·)` with the series
  capacitors `S_k = ω₀² L_k`, the candidate mutual inductance `M`, the secondary terminated by the
  candidate load resistance `R_L` (`Candidate`), at an angular frequency `ω`, in sinusoidal steady
  state (the boundary of `theorem/Passive/Coupled.lean` and `theorem/WPT/Link.lean`).
* The input-impedance values are exact complex numbers: no measurement noise, tolerance,
  harmonics, inverter or rectifier. The module states what equal input impedances imply about the
  candidates and how the candidate is recovered from its reflected impedance; it defines no
  measurement record or I–O relation.
* A foreign object or a misalignment is not modelled as such; only its effect on the candidate
  parameters `(M, R_L)` of this model is covered. No estimator dynamics, convergence or detection
  threshold.

Source: the reflected impedance `(ωM)²/(Z₂(jω) + Z_L)` of `theorem/Passive/Coupled.lean`
(`Passive.Coupled.inputImpedance_jω`) and the resonant input impedance of the series–series link
of `theorem/WPT/Compensation.lean` (`ssLink_inputImpedance`); the identification algebra is
derived here from these.

Results.
* The model: `Candidate` (`M`, `load`), `Candidate.coils`, `Candidate.inputImpedance`,
  `Candidate.resistance` (`R = R₂ + R_L`), `Candidate.reflected` (`Z_r = Z_in − Z₁`).
* The reflected impedance: `Candidate.reflected_eq` (`Z_r(ω) = (ωM)²/(R + jX₂(ω))`),
  `Candidate.reflected_re` (`Re Z_r = (ωM)² R/(R² + X₂²)`), `Candidate.reflected_im`
  (`Im Z_r = −(ωM)² X₂/(R² + X₂²)`).
* Non-identifiability: `Candidate.inputImpedance_resonant_eq` (two candidates with equal
  `(ω₀M)²/R` have equal input impedance at `ω₀`), `Candidate.inputImpedance_resonant_rescale`
  (the explicit witness: `2M` and the load `3R₂ + 4R_L`, i.e. `4R`, give the same value at `ω₀`,
  with a different load when `R ≠ 0`), `Candidate.inputImpedance_neg` (`−M` gives the same input
  impedance at every frequency).
* Identifiability: `Candidate.load_eq_of_inputImpedance_eq` (equal input impedances at one
  frequency with `X₂(ω) ≠ 0`, and `M ≠ 0`, force equal loads and equal `M²`).
* Recovery: `Candidate.resistance_eq_reflected` (`R = −X₂ Re Z_r/Im Z_r` when `X₂ ≠ 0`,
  `ωM ≠ 0`), `Candidate.mutualReactance_sq_eq_reflected` (`(ωM)² = Re Z_r (R² + X₂²)/R` when
  `R ≠ 0`).
-/

noncomputable section

namespace powerlib.WPT.Identification

open Complex

/-- The unknowns of primary-side identification: the mutual inductance `M` and the load
resistance `R_L`. -/
@[ext] structure Candidate where
  /-- The mutual inductance `M`. -/
  M : ℝ
  /-- The load resistance `R_L`. -/
  load : ℝ

namespace Candidate

variable (w : Passive.Coupled) (ω₀ : ℝ)

/-- The coil pair of a candidate: the known windings of `w` with the candidate's mutual
inductance, both series capacitors tuned at `ω₀`. -/
def coils (c : Candidate) : Passive.Coupled := tunedCoils ⟨w.primary, w.secondary, c.M⟩ ω₀

/-- The input impedance `Z_in(jω)` of a candidate, the secondary terminated by its load. -/
def inputImpedance (c : Candidate) (ω : ℝ) : ℂ := (c.coils w ω₀).inputImpedance c.load (ω * I)

/-- The total secondary resistance `R = R₂ + R_L` of a candidate. -/
def resistance (c : Candidate) : ℝ := w.secondary.R + c.load

/-- The reflected impedance `Z_r(ω) = Z_in(jω) − Z₁(jω)`, `Z₁` the impedance of the known tuned
primary. -/
def reflected (c : Candidate) (ω : ℝ) : ℂ :=
  c.inputImpedance w ω₀ ω - (tunedCoils w ω₀).primary.impedance (ω * I)

/-! ## The reflected impedance -/

/-- The reflected impedance of a candidate is `Z_r(ω) = (ωM)²/(R + jX₂(ω))`, `R = R₂ + R_L` and
`X₂` the reactance of the tuned secondary. -/
@[tmio M, powerlib_domain] theorem reflected_eq (c : Candidate) (ω : ℝ) :
    c.reflected w ω₀ ω = (((ω * c.M) ^ 2 : ℝ) : ℂ) /
      ((c.resistance w : ℂ) + ((tunedCoils w ω₀).secondary.reactance ω : ℂ) * I) := by
  rw [reflected, inputImpedance, coils, Passive.Coupled.inputImpedance_jω]
  change (tunedCoils w ω₀).primary.impedance (ω * I) + _ - _ = _
  rw [add_sub_cancel_left, Passive.SeriesRLC.impedance_jω]
  simp only [tunedCoils, resistance]
  push_cast
  ring

/-- `Re Z_r(ω) = (ωM)² R/(R² + X₂²)`. -/
@[tmio M, powerlib_domain] theorem reflected_re (c : Candidate) (ω : ℝ) :
    (c.reflected w ω₀ ω).re = (ω * c.M) ^ 2 * c.resistance w /
      (c.resistance w ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2) := by
  rw [reflected_eq]
  simp only [Complex.div_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `Im Z_r(ω) = −(ωM)² X₂/(R² + X₂²)`. -/
@[tmio M, powerlib_domain] theorem reflected_im (c : Candidate) (ω : ℝ) :
    (c.reflected w ω₀ ω).im = -((ω * c.M) ^ 2 * (tunedCoils w ω₀).secondary.reactance ω /
      (c.resistance w ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2)) := by
  rw [reflected_eq]
  simp only [Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-! ## The resonant frequency: non-identifiability -/

/-- At the resonant frequency the input impedance of a candidate is the real
`R₁ + (ω₀M)²/(R₂ + R_L)` (`ssLink_inputImpedance`). -/
@[tmio M, powerlib_domain] private theorem inputImpedance_resonant (c : Candidate)
    (hω₀ : ω₀ ≠ 0) :
    c.inputImpedance w ω₀ ω₀ = ((w.primary.R + (ω₀ * c.M) ^ 2 / c.resistance w : ℝ) : ℂ) :=
  ssLink_inputImpedance ⟨w.primary, w.secondary, c.M⟩ c.load hω₀

/-- At the resonant frequency the input impedance depends on the candidate only through
`(ω₀M)²/(R₂ + R_L)`: two candidates with equal `(ω₀M)²/(R₂ + R_L)` have equal input impedance
at `ω₀`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_resonant_eq {c c' : Candidate} (hω₀ : ω₀ ≠ 0)
    (h : (ω₀ * c.M) ^ 2 / c.resistance w = (ω₀ * c'.M) ^ 2 / c'.resistance w) :
    c.inputImpedance w ω₀ ω₀ = c'.inputImpedance w ω₀ ω₀ := by
  rw [inputImpedance_resonant w ω₀ c hω₀, inputImpedance_resonant w ω₀ c' hω₀, h]

/-- The explicit witness: doubling the mutual inductance and quadrupling `R₂ + R_L` (the load
`3R₂ + 4R_L`) leaves the input impedance at `ω₀` unchanged, and with `R₂ + R_L ≠ 0` the load is
different. One value of the input impedance at the resonant frequency does not separate a change
of the coupling from a change of the load. -/
@[tmio M, powerlib_domain] theorem inputImpedance_resonant_rescale (c : Candidate)
    (hω₀ : ω₀ ≠ 0) (hR : c.resistance w ≠ 0) :
    3 * w.secondary.R + 4 * c.load ≠ c.load ∧
      (⟨2 * c.M, 3 * w.secondary.R + 4 * c.load⟩ : Candidate).inputImpedance w ω₀ ω₀ =
        c.inputImpedance w ω₀ ω₀ := by
  refine ⟨fun h => hR ?_, inputImpedance_resonant_eq w ω₀ hω₀ ?_⟩
  · rw [resistance]
    linarith
  · have e : resistance w ⟨2 * c.M, 3 * w.secondary.R + 4 * c.load⟩ = 4 * c.resistance w := by
      simp only [resistance]
      ring
    rw [e]
    field_simp
    ring

/-- The input impedance depends on the mutual inductance only through `M²`: the candidate with
`−M` and the same load has the same input impedance at every frequency. -/
@[tmio M, powerlib_domain] theorem inputImpedance_neg (c : Candidate) (ω : ℝ) :
    (⟨-c.M, c.load⟩ : Candidate).inputImpedance w ω₀ ω = c.inputImpedance w ω₀ ω := by
  simp only [inputImpedance, coils, Passive.Coupled.inputImpedance_jω, tunedCoils]
  push_cast
  ring

/-! ## Away from resonance: identifiability -/

/-- A nonzero secondary reactance forces a nonzero frequency. -/
@[tmio M, powerlib_domain] private theorem ne_zero_of_reactance {ω : ℝ}
    (hX : (tunedCoils w ω₀).secondary.reactance ω ≠ 0) : ω ≠ 0 := by
  rintro rfl
  simp [Passive.SeriesRLC.reactance] at hX

/-- The denominator `R + jX₂` of the reflected impedance is nonzero where `X₂ ≠ 0`. -/
@[tmio M, powerlib_domain] private theorem denominator_ne_zero (c : Candidate) {ω : ℝ}
    (hX : (tunedCoils w ω₀).secondary.reactance ω ≠ 0) :
    (c.resistance w : ℂ) + ((tunedCoils w ω₀).secondary.reactance ω : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.zero_im] at this
  exact hX (by linarith)

/-- Identifiability away from resonance: if two candidates have the same input impedance at a
frequency `ω` where the tuned secondary has a nonzero reactance `X₂(ω)`, and the first has
`M ≠ 0`, then they have the same load and the same `M²`. The value at `ω` alone determines `R_L`
and `M²`; a second value, at `ω₀`, is not needed for this. -/
@[tmio M, powerlib_domain] theorem load_eq_of_inputImpedance_eq {c c' : Candidate} {ω : ℝ}
    (hX : (tunedCoils w ω₀).secondary.reactance ω ≠ 0) (hM : c.M ≠ 0)
    (h : c.inputImpedance w ω₀ ω = c'.inputImpedance w ω₀ ω) :
    c.load = c'.load ∧ c.M ^ 2 = c'.M ^ 2 := by
  have hω := ne_zero_of_reactance w ω₀ hX
  have hr : c.reflected w ω₀ ω = c'.reflected w ω₀ ω := by rw [reflected, reflected, h]
  rw [reflected_eq, reflected_eq,
    div_eq_div_iff (denominator_ne_zero w ω₀ c hX) (denominator_ne_zero w ω₀ c' hX)] at hr
  have hre := congrArg Complex.re hr
  have him := congrArg Complex.im hr
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
  have ha : (ω * c.M) ^ 2 = (ω * c'.M) ^ 2 := by
    apply mul_right_cancel₀ hX
    linear_combination him
  have ha0 : (ω * c.M) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hω hM)
  have hR : c'.resistance w = c.resistance w := by
    apply mul_left_cancel₀ ha0
    linear_combination hre - c.resistance w * ha
  refine ⟨?_, ?_⟩
  · simp only [resistance] at hR
    linarith
  · have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω
    apply mul_left_cancel₀ hω2
    linear_combination ha

/-! ## Recovery from the reflected impedance -/

/-- Recovery of the secondary resistance: where `X₂(ω) ≠ 0` and `ωM ≠ 0`,
`R₂ + R_L = −X₂ Re Z_r/Im Z_r`. -/
@[tmio M, powerlib_domain] theorem resistance_eq_reflected (c : Candidate) {ω : ℝ}
    (hX : (tunedCoils w ω₀).secondary.reactance ω ≠ 0) (hM : ω * c.M ≠ 0) :
    c.resistance w = -(tunedCoils w ω₀).secondary.reactance ω * (c.reflected w ω₀ ω).re /
      (c.reflected w ω₀ ω).im := by
  rw [reflected_re, reflected_im]
  have hω : ω ≠ 0 := left_ne_zero_of_mul hM
  have hM' : c.M ≠ 0 := right_ne_zero_of_mul hM
  have hN : c.resistance w ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2 ≠ 0 := by
    positivity
  field_simp

/-- Recovery of the mutual reactance: with `R₂ + R_L ≠ 0`, `(ωM)² = Re Z_r (R² + X₂²)/R`. -/
@[tmio M, powerlib_domain] theorem mutualReactance_sq_eq_reflected (c : Candidate) (ω : ℝ)
    (hR : c.resistance w ≠ 0) :
    (ω * c.M) ^ 2 = (c.reflected w ω₀ ω).re *
      (c.resistance w ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2) / c.resistance w := by
  rw [reflected_re]
  have hN : c.resistance w ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2 ≠ 0 := by
    positivity
  field_simp

end Candidate

end powerlib.WPT.Identification
