import theorem.Attributes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The GC shunt

A shunt conductance–capacitor element is the pair `(G, C)` across one node; under the injected
current `i` its voltage `v` obeys `C v' = i − G v`. It is the dual of the RL branch
(`theorem/Passive/Branch.lean`): conductance for resistance, capacitance for inductance, voltage
for current. The properties of the element itself are stated here once: the decay rate `G / C`
of its voltage and the sign of that rate, the admittance `G + C s`, and the stored energy
`C v² / 2` with its power balance. A model that contains such an element — a DC-link capacitor
with its loss conductance, the node of an RL network, the filter capacitor or the resistive
load at a converter's terminal, the shunt of a line — carries it as a `Passive.GC` and uses these
facts.

Model boundary.
* One lumped shunt `G ∥ C`. `G` and `C` are real; a physical element has `C > 0` and `G ≥ 0`,
  and each law states what it needs. A resistive load `R_l ∥ C` is the element with
  `G = 1 / R_l`.
* No rotating frame, controller or interconnection: those belong to the models that contain the
  element (`theorem/Passive/Dq.lean` for the rotating frame, `theorem/Grid/` for networks).

Source: the node equation `C v' = i − G v` of a shunt RC element (work-sync
`theory/T-impedance-modeling.md`, `theory/T-park-transformation.md` §1.4).

Results.
* `GC` (conductance `G`, capacitance `C`), `GC.decay` (`G / C`), `GC.admittance` (`G + C s`),
  `GC.energy` (`C v² / 2`).
* `GC.decay_pos_iff`, `GC.decay_neg_iff`: with `C > 0` the decay rate has the sign of `G`.
* `GC.admittance_eq`: `G + C s = C (s + G / C)` for `C ≠ 0`.
* `GC.energy_nonneg`, `GC.energy_pos`: the stored energy of a physical element.
* `GC.power_balance`, `GC.hasDerivAt_energy`: along the node equation the stored energy changes
  at `v i − G v²`, the supplied power less the dissipated one (pointwise, and along a
  trajectory).
-/

noncomputable section

namespace powerlib.Passive

/-- A shunt conductance–capacitor element: conductance `G`, capacitance `C`, voltage equation
`C v' = i − G v`. -/
@[ext] structure GC where
  /-- The conductance. -/
  G : ℝ
  /-- The capacitance. -/
  C : ℝ

namespace GC

variable (e : GC)

/-- The decay rate `G / C` of the element voltage. -/
def decay : ℝ := e.G / e.C

/-- The admittance `G + C s`. -/
def admittance (s : ℂ) : ℂ := e.G + e.C * s

/-- The stored electric energy `C v² / 2`. -/
def energy (v : ℝ) : ℝ := e.C * v ^ 2 / 2

/-- With a positive capacitance the decay rate is positive exactly when the conductance is. -/
@[tmio M, powerlib_domain] theorem decay_pos_iff {e : GC} (hC : 0 < e.C) :
    0 < e.decay ↔ 0 < e.G :=
  div_pos_iff_of_pos_right hC

/-- With a positive capacitance the decay rate is negative exactly when the conductance is. -/
@[tmio M, powerlib_domain] theorem decay_neg_iff {e : GC} (hC : 0 < e.C) :
    e.decay < 0 ↔ e.G < 0 := by
  unfold decay
  constructor
  · intro h
    by_contra hG
    exact absurd h (not_lt.mpr (div_nonneg (not_lt.mp hG) hC.le))
  · intro hG
    exact div_neg_of_neg_of_pos hG hC

/-- The admittance factors through the decay rate. -/
@[tmio M, powerlib_domain] theorem admittance_eq {e : GC} (hC : e.C ≠ 0) (s : ℂ) :
    e.admittance s = e.C * (s + e.decay) := by
  have hC' : (e.C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC
  simp only [admittance, decay, Complex.ofReal_div]
  field_simp
  ring

/-- An element with a nonnegative capacitance stores a nonnegative energy. -/
@[tmio M, powerlib_domain] theorem energy_nonneg {e : GC} (hC : 0 ≤ e.C) (v : ℝ) :
    0 ≤ e.energy v := by
  unfold energy
  positivity

/-- An element with a positive capacitance stores a positive energy at every nonzero voltage. -/
@[tmio M, powerlib_domain] theorem energy_pos {e : GC} (hC : 0 < e.C) {v : ℝ} (hv : v ≠ 0) :
    0 < e.energy v := by
  unfold energy
  positivity

/-- Power balance: along `C v' = i − G v` the stored energy changes at `v i − G v²`. -/
@[tmio M, powerlib_domain] theorem power_balance {e : GC} (hC : e.C ≠ 0) (v i : ℝ) :
    e.C * v * ((i - e.G * v) / e.C) = v * i - e.G * v ^ 2 := by
  field_simp

/-- Energy balance along a trajectory: if `C v' = i − G v` at `t`, the stored energy has
derivative `v i − G v²` there. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_energy {e : GC} {v : ℝ → ℝ} {i t v' : ℝ}
    (hv : HasDerivAt v v' t) (hnode : e.C * v' = i - e.G * v t) :
    HasDerivAt (fun τ => e.energy (v τ)) (v t * i - e.G * v t ^ 2) t := by
  show HasDerivAt (fun τ => e.C * v τ ^ 2 / 2) _ t
  have h := ((hv.fun_pow 2).const_mul e.C).div_const 2
  convert h using 1
  push_cast
  linear_combination (-(v t)) * hnode

end GC

end powerlib.Passive
