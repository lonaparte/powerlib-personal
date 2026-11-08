import theorem.Attributes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # The parallel RLC element

A parallel conductance–capacitor–inductor element across one node is the triple `(G, C, Γ)` with
`Γ = 1/L` the reciprocal inductance of the shunt inductor (`Γ = 0`: no inductor, the plain G–C
shunt). With voltage `v`, inductor flux `φ` (`φ' = v`) and injected current `i` it obeys
`C v' = i − G v − Γ φ`; its admittance is `G + C s + Γ/s`. It is the dual of the series element
`Passive.SeriesRLC` (`theorem/Passive/Series.lean`): conductance for resistance, capacitance for
inductance, reciprocal inductance for elastance, voltage for current. Every parallel combination
of G, C and L in the library — a DC-link capacitor with its loss conductance, the node of a
network, the filter capacitor or the resistive load at a converter's terminal, the shunt part of
a line's unit length — is a `Passive.ParallelRLC`; a model whose element has no inductor or no
conductance states it as an explicit field (`Γ = 0`, `G = 0`).

Model boundary.
* One lumped parallel G–C–L element; `G`, `C`, `Γ` real (a physical element has `G ≥ 0`, `C > 0`,
  `Γ ≥ 0`); each law states what it needs.
* At a fixed angular frequency `ω` the element is the phasor admittance `G + jB`,
  `B = ωC − Γ/ω` (`susceptance`, `admittance_jω`).
* No rotating frame, controller or interconnection: the dq forms are `theorem/Passive/Dq.lean`,
  networks are `theorem/Grid/`.

Source: the node equation `C v' = i − G v − Γ φ` of a parallel RLC circuit and its phasor
admittance (work-sync `theory/T-impedance-modeling.md`, `theory/T-park-transformation.md` §1.4).

Results.
* `ParallelRLC` (`G`, `C`, `Γ = 1/L`), `admittance` (`G + C s + Γ/s`), `decay` (`G/C`),
  `susceptance` (`ωC − Γ/ω`), the energies `capacitorEnergy` (`C v²/2`), `inductorEnergy`
  (`Γ φ²/2`), `energy`, and the parallel connection `parallel`.
* `decay_pos_iff`, `decay_neg_iff`: with `C > 0` the decay rate `G/C` has the sign of `G`;
  `admittance_of_noInd`, `admittance_eq`: without an inductor `Y = G + C s = C (s + G/C)`.
* `admittance_jω`: `Y(jω) = G + jB`; `parallel_admittance`, `parallel_susceptance`: admittances
  and susceptances add in parallel.
* `capacitorEnergy_nonneg`, `capacitorEnergy_pos`, `inductorEnergy_nonneg`, `energy_nonneg`;
  `power_balance`, `hasDerivAt_energy`: along the node equation the stored energy changes at
  `v i − G v²`, the supplied power less the dissipated one.
-/

noncomputable section

namespace powerlib.Passive

/-- A parallel conductance–capacitor–inductor element: conductance `G`, capacitance `C`,
reciprocal inductance `Γ = 1/L` (`Γ = 0`: no inductor); `C v' = i − G v − Γ φ`, `φ' = v`. -/
@[ext] structure ParallelRLC where
  /-- The conductance. -/
  G : ℝ
  /-- The capacitance. -/
  C : ℝ
  /-- The reciprocal inductance `1/L` of the shunt inductor (`0`: no inductor). -/
  Γ : ℝ

namespace ParallelRLC

variable (e : ParallelRLC)

/-- The admittance `G + C s + Γ/s`. -/
def admittance (s : ℂ) : ℂ := e.G + e.C * s + e.Γ / s

/-- The decay rate `G / C` of the voltage of the G–C part. -/
def decay : ℝ := e.G / e.C

/-- The susceptance `ωC − Γ/ω` at the angular frequency `ω`. -/
def susceptance (ω : ℝ) : ℝ := ω * e.C - e.Γ / ω

/-- The electric energy `C v² / 2`. -/
def capacitorEnergy (v : ℝ) : ℝ := e.C * v ^ 2 / 2

/-- The magnetic energy `Γ φ² / 2 = φ²/(2L)` of the shunt inductor at flux `φ`. -/
def inductorEnergy (φ : ℝ) : ℝ := e.Γ * φ ^ 2 / 2

/-- The stored energy at voltage `v` and inductor flux `φ`. -/
def energy (v φ : ℝ) : ℝ := e.capacitorEnergy v + e.inductorEnergy φ

/-- Two elements in parallel: conductances, capacitances and reciprocal inductances add. -/
def parallel (a b : ParallelRLC) : ParallelRLC := ⟨a.G + b.G, a.C + b.C, a.Γ + b.Γ⟩

/-- With a positive capacitance the decay rate is positive exactly when the conductance is. -/
@[tmio M, powerlib_domain] theorem decay_pos_iff {e : ParallelRLC} (hC : 0 < e.C) :
    0 < e.decay ↔ 0 < e.G :=
  div_pos_iff_of_pos_right hC

/-- With a positive capacitance the decay rate is negative exactly when the conductance is. -/
@[tmio M, powerlib_domain] theorem decay_neg_iff {e : ParallelRLC} (hC : 0 < e.C) :
    e.decay < 0 ↔ e.G < 0 := by
  unfold decay
  constructor
  · intro h
    by_contra hG
    exact absurd h (not_lt.mpr (div_nonneg (not_lt.mp hG) hC.le))
  · intro hG
    exact div_neg_of_neg_of_pos hG hC

/-- Without an inductor the admittance is `G + C s`. -/
@[tmio M, powerlib_domain] theorem admittance_of_noInd {e : ParallelRLC} (hΓ : e.Γ = 0) (s : ℂ) :
    e.admittance s = e.G + e.C * s := by
  simp [admittance, hΓ]

/-- Without an inductor the admittance factors through the decay rate. -/
@[tmio M, powerlib_domain] theorem admittance_eq {e : ParallelRLC} (hΓ : e.Γ = 0) (hC : e.C ≠ 0)
    (s : ℂ) : e.admittance s = e.C * (s + e.decay) := by
  have hC' : (e.C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC
  rw [admittance_of_noInd hΓ]
  simp only [decay, Complex.ofReal_div]
  field_simp
  ring

/-- At `s = jω` the admittance is `G + jB`. -/
@[tmio M, powerlib_domain] theorem admittance_jω (ω : ℝ) :
    e.admittance (ω * Complex.I) = e.G + e.susceptance ω * Complex.I := by
  simp only [admittance, susceptance]
  rcases eq_or_ne ω 0 with h | h
  · subst h; simp
  · have h' : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
    push_cast
    field_simp
    linear_combination ((e.Γ : ℝ) : ℂ) * Complex.I_sq

/-- Admittances add in parallel. -/
@[tmio M, powerlib_domain] theorem parallel_admittance (a b : ParallelRLC) (s : ℂ) :
    (a.parallel b).admittance s = a.admittance s + b.admittance s := by
  simp only [parallel, admittance]
  push_cast
  ring

/-- Susceptances add in parallel. -/
@[tmio M, powerlib_domain] theorem parallel_susceptance (a b : ParallelRLC) (ω : ℝ) :
    (a.parallel b).susceptance ω = a.susceptance ω + b.susceptance ω := by
  simp only [parallel, susceptance]
  ring

/-- An element with a nonnegative capacitance stores a nonnegative electric energy. -/
@[tmio M, powerlib_domain] theorem capacitorEnergy_nonneg {e : ParallelRLC} (hC : 0 ≤ e.C)
    (v : ℝ) : 0 ≤ e.capacitorEnergy v := by
  unfold capacitorEnergy
  positivity

/-- An element with a positive capacitance stores a positive electric energy at every nonzero
voltage. -/
@[tmio M, powerlib_domain] theorem capacitorEnergy_pos {e : ParallelRLC} (hC : 0 < e.C) {v : ℝ}
    (hv : v ≠ 0) : 0 < e.capacitorEnergy v := by
  unfold capacitorEnergy
  positivity

/-- An element with a nonnegative reciprocal inductance stores a nonnegative magnetic energy. -/
@[tmio M, powerlib_domain] theorem inductorEnergy_nonneg {e : ParallelRLC} (hΓ : 0 ≤ e.Γ)
    (φ : ℝ) : 0 ≤ e.inductorEnergy φ := by
  unfold inductorEnergy
  positivity

/-- A physical element stores a nonnegative energy. -/
@[tmio M, powerlib_domain] theorem energy_nonneg {e : ParallelRLC} (hC : 0 ≤ e.C) (hΓ : 0 ≤ e.Γ)
    (v φ : ℝ) : 0 ≤ e.energy v φ :=
  add_nonneg (capacitorEnergy_nonneg hC v) (inductorEnergy_nonneg hΓ φ)

/-- Power balance: along `C v' = i − G v − Γ φ`, `φ' = v` the stored energy changes at
`v i − G v²`. -/
@[tmio M, powerlib_domain] theorem power_balance {e : ParallelRLC} (hC : e.C ≠ 0) (v i φ : ℝ) :
    e.C * v * ((i - e.G * v - e.Γ * φ) / e.C) + e.Γ * φ * v = v * i - e.G * v ^ 2 := by
  field_simp
  ring

/-- Energy balance along a trajectory: if `C v' = i − G v − Γ φ` and `φ' = v` at `t`, the stored
energy has derivative `v i − G v²` there. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_energy {e : ParallelRLC} {v φ : ℝ → ℝ} {i t v' : ℝ}
    (hv : HasDerivAt v v' t) (hφ : HasDerivAt φ (v t) t)
    (hnode : e.C * v' = i - e.G * v t - e.Γ * φ t) :
    HasDerivAt (fun τ => e.energy (v τ) (φ τ)) (v t * i - e.G * v t ^ 2) t := by
  show HasDerivAt (fun τ => e.C * v τ ^ 2 / 2 + e.Γ * φ τ ^ 2 / 2) _ t
  have h1 : HasDerivAt (fun τ => e.C * v τ ^ 2 / 2) (e.C * (↑2 * v t ^ (2 - 1) * v') / 2) t :=
    ((hv.fun_pow 2).const_mul e.C).div_const 2
  have h2 : HasDerivAt (fun τ => e.Γ * φ τ ^ 2 / 2) (e.Γ * (↑2 * φ t ^ (2 - 1) * v t) / 2) t :=
    ((hφ.fun_pow 2).const_mul e.Γ).div_const 2
  refine (h1.add h2).congr_deriv ?_
  norm_num
  linear_combination (v t) * hnode

end ParallelRLC

end powerlib.Passive
