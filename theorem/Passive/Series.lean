import theorem.Attributes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # The series RLC element

A series resistor–inductor–capacitor element is the triple `(R, L, S)` with `S = 1/C` the
elastance of the series capacitor (`S = 0`: no capacitor, the plain R–L branch). With current `i`,
capacitor charge `q` (`q' = i`) and terminal voltage `v` it obeys `L i' = v − R i − S q`; its
impedance is `R + L s + S/s`. Every series combination of R, L and C in the library — a single
branch, the filter or line of a converter, the link of a machine, the branches of a network, the
series RLC loop, the series part of a line's unit length, the line of a phasor model — is a
`Passive.SeriesRLC`; its dual, the parallel combination, is `Passive.ParallelRLC`
(`theorem/Passive/Parallel.lean`). A model whose branch has no capacitor (first-order) or no
resistance states it as an explicit field (`S = 0`, `R = 0`).

Model boundary.
* One lumped series R–L–C element; `R`, `L`, `S` real (a physical element has `R ≥ 0`, `L > 0`,
  `S ≥ 0`); each law states what it needs.
* At a fixed angular frequency `ω` (sinusoidal steady state) the element is the phasor impedance
  `R + jX`, `X = ωL − S/ω` (`reactance`, `impedance_jω`).
* No rotating frame, controller or interconnection: the dq forms are `theorem/Passive/Dq.lean`,
  networks are `theorem/Grid/`.

Source: the element equation `L i' = v − R i − S q` of a series RLC circuit and its phasor
impedance (work-sync `theory/T-impedance-modeling.md`, `theory/T-park-transformation.md` §1.4,
`theory/T-droop-control.md` §1.2).

Results.
* `SeriesRLC` (`R`, `L`, `S = 1/C`), `impedance` (`R + L s + S/s`), `decay` (`R/L`),
  `reactance` (`ωL − S/ω`), `absSq` (`R² + X²`), the energies `inductorEnergy` (`L i²/2`),
  `capacitorEnergy` (`S q²/2`), `energy`, and the series connection `series`.
* `decay_pos_iff`, `decay_neg_iff`: with `L > 0` the decay rate `R/L` has the sign of `R`;
  `impedance_of_noCap`, `impedance_eq`: without a capacitor `Z = R + L s = L (s + R/L)`.
* `impedance_jω`, `normSq_impedance_jω`, `norm_sq_impedance_jω`: `Z(jω) = R + jX`,
  `|Z(jω)|² = R² + X²`; `series_impedance`, `series_reactance`: impedances and reactances add in
  series; `parallel_inductors`: two inductors in parallel are the inductor `L₁L₂/(L₁ + L₂)`.
* `inductorEnergy_nonneg`, `inductorEnergy_pos`, `capacitorEnergy_nonneg`, `energy_nonneg`;
  `power_balance`, `hasDerivAt_energy`: along the element equation the stored energy changes at
  `v i − R i²`, the supplied power less the dissipated one.
-/

noncomputable section

namespace powerlib.Passive

/-- A series resistor–inductor–capacitor element: resistance `R`, inductance `L`, elastance
`S = 1/C` (`S = 0`: no capacitor); `L i' = v − R i − S q`, `q' = i`. -/
@[ext] structure SeriesRLC where
  /-- The resistance. -/
  R : ℝ
  /-- The inductance. -/
  L : ℝ
  /-- The elastance `1/C` of the series capacitor (`0`: no capacitor). -/
  S : ℝ

namespace SeriesRLC

variable (b : SeriesRLC)

/-- The impedance `R + L s + S/s`. -/
def impedance (s : ℂ) : ℂ := b.R + b.L * s + b.S / s

/-- The decay rate `R / L` of the current of the R–L part. -/
def decay : ℝ := b.R / b.L

/-- The reactance `ωL − S/ω` at the angular frequency `ω`. -/
def reactance (ω : ℝ) : ℝ := ω * b.L - b.S / ω

/-- The squared impedance magnitude `R² + X²` at `ω`. -/
def absSq (ω : ℝ) : ℝ := b.R ^ 2 + b.reactance ω ^ 2

/-- The magnetic energy `L i² / 2`. -/
def inductorEnergy (i : ℝ) : ℝ := b.L * i ^ 2 / 2

/-- The electric energy `S q² / 2 = q²/(2C)` of the series capacitor at charge `q`. -/
def capacitorEnergy (q : ℝ) : ℝ := b.S * q ^ 2 / 2

/-- The stored energy at current `i` and capacitor charge `q`. -/
def energy (i q : ℝ) : ℝ := b.inductorEnergy i + b.capacitorEnergy q

/-- Two elements in series: resistances, inductances and elastances add. -/
def series (a b : SeriesRLC) : SeriesRLC := ⟨a.R + b.R, a.L + b.L, a.S + b.S⟩

/-- With a positive inductance the decay rate is positive exactly when the resistance is. -/
@[tmio M, powerlib_domain] theorem decay_pos_iff {b : SeriesRLC} (hL : 0 < b.L) :
    0 < b.decay ↔ 0 < b.R :=
  div_pos_iff_of_pos_right hL

/-- With a positive inductance the decay rate is negative exactly when the resistance is. -/
@[tmio M, powerlib_domain] theorem decay_neg_iff {b : SeriesRLC} (hL : 0 < b.L) :
    b.decay < 0 ↔ b.R < 0 := by
  unfold decay
  constructor
  · intro h
    by_contra hR
    exact absurd h (not_lt.mpr (div_nonneg (not_lt.mp hR) hL.le))
  · intro hR
    exact div_neg_of_neg_of_pos hR hL

/-- Without a capacitor the impedance is `R + L s`. -/
@[tmio M, powerlib_domain] theorem impedance_of_noCap {b : SeriesRLC} (hS : b.S = 0) (s : ℂ) :
    b.impedance s = b.R + b.L * s := by
  simp [impedance, hS]

/-- Without a capacitor the impedance factors through the decay rate. -/
@[tmio M, powerlib_domain] theorem impedance_eq {b : SeriesRLC} (hS : b.S = 0) (hL : b.L ≠ 0)
    (s : ℂ) : b.impedance s = b.L * (s + b.decay) := by
  have hL' : (b.L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  rw [impedance_of_noCap hS]
  simp only [decay, Complex.ofReal_div]
  field_simp
  ring

/-- At `s = jω` the impedance is `R + jX`. -/
@[tmio M, powerlib_domain] theorem impedance_jω (ω : ℝ) :
    b.impedance (ω * Complex.I) = b.R + b.reactance ω * Complex.I := by
  simp only [impedance, reactance]
  rcases eq_or_ne ω 0 with h | h
  · subst h; simp
  · have h' : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
    push_cast
    field_simp
    linear_combination ((b.S : ℝ) : ℂ) * Complex.I_sq

/-- `|Z(jω)|² = R² + X²` (as `Complex.normSq`). -/
@[tmio M, powerlib_domain] theorem normSq_impedance_jω (ω : ℝ) :
    Complex.normSq (b.impedance (ω * Complex.I)) = b.absSq ω := by
  rw [impedance_jω]
  simp [absSq, Complex.normSq_apply, sq]

/-- `‖Z(jω)‖² = R² + X²`. -/
@[tmio M, powerlib_domain] theorem norm_sq_impedance_jω (ω : ℝ) :
    ‖b.impedance (ω * Complex.I)‖ ^ 2 = b.absSq ω := by
  rw [Complex.sq_norm, normSq_impedance_jω]

/-- Impedances add in series. -/
@[tmio M, powerlib_domain] theorem series_impedance (a b : SeriesRLC) (s : ℂ) :
    (a.series b).impedance s = a.impedance s + b.impedance s := by
  simp only [series, impedance]
  push_cast
  ring

/-- Reactances add in series. -/
@[tmio M, powerlib_domain] theorem series_reactance (a b : SeriesRLC) (ω : ℝ) :
    (a.series b).reactance ω = a.reactance ω + b.reactance ω := by
  simp only [series, reactance]
  ring

/-- Two inductors in parallel are the inductor `L₁L₂/(L₁ + L₂)`:
`Z₁ Z₂/(Z₁ + Z₂)` at every `s`. -/
@[tmio M, powerlib_domain] theorem parallel_inductors (L₁ L₂ : ℝ) (s : ℂ) :
    (⟨0, L₁, 0⟩ : SeriesRLC).impedance s * (⟨0, L₂, 0⟩ : SeriesRLC).impedance s /
        ((⟨0, L₁, 0⟩ : SeriesRLC).impedance s + (⟨0, L₂, 0⟩ : SeriesRLC).impedance s) =
      (⟨0, L₁ * L₂ / (L₁ + L₂), 0⟩ : SeriesRLC).impedance s := by
  simp only [impedance, Complex.ofReal_zero, zero_add, zero_div, add_zero]
  rcases eq_or_ne s 0 with hs | hs
  · simp [hs]
  rcases eq_or_ne (L₁ + L₂) 0 with h | h
  · have h' : (L₁ : ℂ) * s + L₂ * s = 0 := by
      rw [← add_mul, ← Complex.ofReal_add, h, Complex.ofReal_zero, zero_mul]
    rw [h', div_zero, h, div_zero, Complex.ofReal_zero, zero_mul]
  · have h' : (L₁ : ℂ) + L₂ ≠ 0 := by exact_mod_cast h
    have hI : (L₁ : ℂ) * s + L₂ * s = ((L₁ : ℂ) + L₂) * s := by ring
    rw [hI]
    push_cast
    field_simp

/-- An element with a nonnegative inductance stores a nonnegative magnetic energy. -/
@[tmio M, powerlib_domain] theorem inductorEnergy_nonneg {b : SeriesRLC} (hL : 0 ≤ b.L) (i : ℝ) :
    0 ≤ b.inductorEnergy i := by
  unfold inductorEnergy
  positivity

/-- An element with a positive inductance stores a positive magnetic energy at every nonzero
current. -/
@[tmio M, powerlib_domain] theorem inductorEnergy_pos {b : SeriesRLC} (hL : 0 < b.L) {i : ℝ}
    (hi : i ≠ 0) : 0 < b.inductorEnergy i := by
  unfold inductorEnergy
  positivity

/-- An element with a nonnegative elastance stores a nonnegative electric energy. -/
@[tmio M, powerlib_domain] theorem capacitorEnergy_nonneg {b : SeriesRLC} (hS : 0 ≤ b.S) (q : ℝ) :
    0 ≤ b.capacitorEnergy q := by
  unfold capacitorEnergy
  positivity

/-- A physical element stores a nonnegative energy. -/
@[tmio M, powerlib_domain] theorem energy_nonneg {b : SeriesRLC} (hL : 0 ≤ b.L) (hS : 0 ≤ b.S)
    (i q : ℝ) : 0 ≤ b.energy i q :=
  add_nonneg (inductorEnergy_nonneg hL i) (capacitorEnergy_nonneg hS q)

/-- Power balance: along `L i' = v − R i − S q`, `q' = i` the stored energy changes at
`v i − R i²`. -/
@[tmio M, powerlib_domain] theorem power_balance {b : SeriesRLC} (hL : b.L ≠ 0) (i v q : ℝ) :
    b.L * i * ((v - b.R * i - b.S * q) / b.L) + b.S * q * i = v * i - b.R * i ^ 2 := by
  field_simp
  ring

/-- Energy balance along a trajectory: if `L i' = v − R i − S q` and `q' = i` at `t`, the stored
energy has derivative `v i − R i²` there. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_energy {b : SeriesRLC} {i q : ℝ → ℝ} {v t i' : ℝ}
    (hi : HasDerivAt i i' t) (hq : HasDerivAt q (i t) t)
    (hkvl : b.L * i' = v - b.R * i t - b.S * q t) :
    HasDerivAt (fun τ => b.energy (i τ) (q τ)) (v * i t - b.R * i t ^ 2) t := by
  show HasDerivAt (fun τ => b.L * i τ ^ 2 / 2 + b.S * q τ ^ 2 / 2) _ t
  have h1 : HasDerivAt (fun τ => b.L * i τ ^ 2 / 2) (b.L * (↑2 * i t ^ (2 - 1) * i') / 2) t :=
    ((hi.fun_pow 2).const_mul b.L).div_const 2
  have h2 : HasDerivAt (fun τ => b.S * q τ ^ 2 / 2) (b.S * (↑2 * q t ^ (2 - 1) * i t) / 2) t :=
    ((hq.fun_pow 2).const_mul b.S).div_const 2
  refine (h1.add h2).congr_deriv ?_
  norm_num
  linear_combination (i t) * hkvl

end SeriesRLC

end powerlib.Passive
