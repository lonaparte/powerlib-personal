import theorem.Passive.Branch
import theorem.Passive.Shunt

/-! # Elements at a fixed frequency: reactances and the phasor branch `R + jX`

At a fixed angular frequency `ω` the series RL branch is the phasor impedance `R + jωL` and the
capacitance of a shunt element contributes the reactance `−1/(ωC)`. A quasi-static model that
works with phasors carries its series branch as a `Passive.RX` (resistance `R`, reactance `X`)
and uses the laws stated here; a lossless one (`R = 0`) says so explicitly.

Model boundary.
* One lumped series branch read at one frequency (sinusoidal steady state); `R`, `X` real.
* `RL.reactance`, `GC.reactance` are the reactances of the inductance and of the capacitance; the
  latter is the whole phasor impedance of a lossless shunt element (`G = 0`).
* No source, network or power flow: a line between two sources is `theorem/Grid/PowerFlow.lean`.

Source: phasor impedance of R, L, C elements (work-sync `theory/T-impedance-modeling.md`,
`theory/T-droop-control.md` §1.2).

Results.
* `RX`, `RX.impedance` (`R + jX`), `RX.absSq` (`R² + X²`).
* `RX.normSq_impedance`, `RX.norm_sq_impedance`: `|R + jX|² = R² + X²`;
  `RX.impedance_ne_zero_iff`: the impedance vanishes only for `R = X = 0`.
* `RX.series`, `RX.parallel` (`RX.series_impedance`: `Z₁ + Z₂`, `RX.parallel_impedance`:
  `Z₁ Z₂/(Z₁ + Z₂)`); `RX.parallel_lossless`: `jX₁ ∥ jX₂ = j X₁X₂/(X₁ + X₂)`.
* `RL.reactance` (`ωL`), `GC.reactance` (`−1/(ωC)`), `RL.phasor` (the branch at `ω`, `R + jωL`);
  `RL.phasor_impedance`: it is the branch impedance at `s = jω`.
-/

noncomputable section

namespace powerlib.Passive

/-- A series branch at a fixed frequency: resistance `R` and reactance `X`, impedance
`R + jX`. -/
@[ext] structure RX where
  /-- The resistance. -/
  R : ℝ
  /-- The reactance. -/
  X : ℝ

namespace RX

variable (z : RX)

/-- The phasor impedance `R + jX`. -/
def impedance : ℂ := z.R + z.X * Complex.I

/-- The squared magnitude `R² + X²` of the impedance. -/
def absSq : ℝ := z.R ^ 2 + z.X ^ 2

/-- `|R + jX|² = R² + X²` (as `Complex.normSq`). -/
@[tmio M, powerlib_domain] theorem normSq_impedance : Complex.normSq z.impedance = z.absSq := by
  simp [impedance, absSq, Complex.normSq_apply, sq]

/-- `‖R + jX‖² = R² + X²`. -/
@[tmio M, powerlib_domain] theorem norm_sq_impedance : ‖z.impedance‖ ^ 2 = z.absSq := by
  rw [Complex.sq_norm, normSq_impedance]

/-- The impedance vanishes exactly when the resistance and the reactance both do. -/
@[tmio M, powerlib_domain] theorem absSq_eq_zero_iff : z.absSq = 0 ↔ z.R = 0 ∧ z.X = 0 := by
  unfold absSq
  constructor
  · intro h
    exact ⟨by nlinarith [sq_nonneg z.R, sq_nonneg z.X], by nlinarith [sq_nonneg z.R, sq_nonneg z.X]⟩
  · rintro ⟨hR, hX⟩
    simp [hR, hX]

/-- The impedance is nonzero exactly when `R² + X² ≠ 0`. -/
@[tmio M, powerlib_domain] theorem impedance_ne_zero_iff : z.impedance ≠ 0 ↔ z.absSq ≠ 0 := by
  rw [← normSq_impedance, ne_eq, ne_eq, Complex.normSq_eq_zero]

/-- A phasor impedance read back as a branch. -/
def ofImpedance (w : ℂ) : RX := ⟨w.re, w.im⟩

@[tmio M, powerlib_domain] theorem impedance_ofImpedance (w : ℂ) : (ofImpedance w).impedance = w := by
  simp [ofImpedance, impedance, Complex.re_add_im]

/-- Two branches in series, `Z₁ + Z₂`. -/
def series (z₁ z₂ : RX) : RX := ⟨z₁.R + z₂.R, z₁.X + z₂.X⟩

/-- Two branches in parallel, `Z₁ Z₂ / (Z₁ + Z₂)`. -/
def parallel (z₁ z₂ : RX) : RX :=
  ofImpedance (z₁.impedance * z₂.impedance / (z₁.impedance + z₂.impedance))

/-- The impedance of a series connection is the sum of the impedances. -/
@[tmio M, powerlib_domain] theorem series_impedance (z₁ z₂ : RX) :
    (z₁.series z₂).impedance = z₁.impedance + z₂.impedance := by
  simp only [series, impedance]
  push_cast
  ring

/-- The impedance of a parallel connection is `Z₁ Z₂ / (Z₁ + Z₂)`. -/
@[tmio M, powerlib_domain] theorem parallel_impedance (z₁ z₂ : RX) :
    (z₁.parallel z₂).impedance = z₁.impedance * z₂.impedance / (z₁.impedance + z₂.impedance) :=
  impedance_ofImpedance _

/-- Two lossless branches in parallel are the lossless branch `X₁ X₂ / (X₁ + X₂)`. -/
@[tmio M, powerlib_domain] theorem parallel_lossless (X₁ X₂ : ℝ) :
    (⟨0, X₁⟩ : RX).parallel ⟨0, X₂⟩ = ⟨0, X₁ * X₂ / (X₁ + X₂)⟩ := by
  have hw : (impedance ⟨0, X₁⟩ * impedance ⟨0, X₂⟩ / (impedance ⟨0, X₁⟩ + impedance ⟨0, X₂⟩)) =
      ((X₁ * X₂ / (X₁ + X₂) : ℝ) : ℂ) * Complex.I := by
    simp only [impedance, Complex.ofReal_zero, zero_add]
    by_cases h : X₁ + X₂ = 0
    · have h' : (X₁ : ℂ) * Complex.I + X₂ * Complex.I = 0 := by
        rw [← add_mul, ← Complex.ofReal_add, h, Complex.ofReal_zero, zero_mul]
      rw [h', div_zero, h, div_zero, Complex.ofReal_zero, zero_mul]
    · have h' : (X₁ : ℂ) + X₂ ≠ 0 := by exact_mod_cast h
      have hI : (X₁ : ℂ) * Complex.I + X₂ * Complex.I = ((X₁ : ℂ) + X₂) * Complex.I := by ring
      rw [hI]
      push_cast
      field_simp
  change ofImpedance _ = _
  rw [hw]
  apply RX.ext <;>
    simp only [ofImpedance, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;> ring

end RX

/-- The reactance `ωL` of the branch inductance at `ω`. -/
def RL.reactance (b : RL) (ω : ℝ) : ℝ := ω * b.L

/-- The reactance `−1/(ωC)` of the element capacitance at `ω`. -/
def GC.reactance (e : GC) (ω : ℝ) : ℝ := -1 / (ω * e.C)

/-- The branch at `ω`: resistance `R`, reactance `ωL`. -/
def RL.phasor (b : RL) (ω : ℝ) : RX := ⟨b.R, b.reactance ω⟩

/-- The phasor impedance of the branch is its impedance at `s = jω`. -/
@[tmio M, powerlib_domain] theorem RL.phasor_impedance (b : RL) (ω : ℝ) :
    (b.phasor ω).impedance = b.impedance (ω * Complex.I) := by
  simp only [RX.impedance, phasor, reactance, impedance]
  push_cast
  ring

end powerlib.Passive
