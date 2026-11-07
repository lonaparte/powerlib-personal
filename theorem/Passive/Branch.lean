import theorem.Attributes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The RL branch

A series resistor–inductor branch is the pair `(R, L)`; under the terminal voltage `v` its current
`i` obeys `L i' = v − R i`. The properties of the branch itself are stated here once: the decay
rate `R / L` of its current and the sign of that rate, the impedance `R + L s`, and the stored
energy `L i² / 2` with its power balance. A model that contains an RL branch — the single branch
and its dq form, the plant of a current loop, the filter or line of a converter, the link of a
machine, the branches of a network, the series RLC loop, the unit length of a transmission line —
carries it as a `Passive.RL` and uses these facts. Its dual, the shunt G–C element, is
`Passive.GC` (`theorem/Passive/Shunt.lean`); both read in a rotating frame are in
`theorem/Passive/Dq.lean`.

Model boundary.
* One lumped series R–L branch. `R` and `L` are real; a physical branch has `L > 0` and `R ≥ 0`,
  and each law states what it needs.
* No rotating frame, controller or interconnection: those belong to the models that contain the
  branch (`theorem/Passive/Dq.lean` and `theorem/Passive/DqRL.lean` for the rotating frame,
  `theorem/Grid/` for networks).

Source: the branch equation `L i' = v − R i` of a series RL circuit (work-sync
`theory/T-impedance-modeling.md`, `theory/T-park-transformation.md` §1.4).

Results.
* `RL` (resistance `R`, inductance `L`), `RL.decay` (`R / L`), `RL.impedance` (`R + L s`),
  `RL.energy` (`L i² / 2`).
* `RL.decay_pos_iff`, `RL.decay_neg_iff`: with `L > 0` the decay rate has the sign of `R`.
* `RL.impedance_eq`: `R + L s = L (s + R / L)` for `L ≠ 0`.
* `RL.energy_nonneg`, `RL.energy_pos`: the stored energy of a physical branch.
* `RL.power_balance`, `RL.hasDerivAt_energy`: along the branch equation the stored energy
  changes at `v i − R i²`, the supplied power less the dissipated one (pointwise, and along a
  trajectory).
-/

noncomputable section

namespace powerlib.Passive

/-- A series resistor–inductor branch: resistance `R`, inductance `L`, current equation
`L i' = v − R i`. -/
@[ext] structure RL where
  /-- The resistance. -/
  R : ℝ
  /-- The inductance. -/
  L : ℝ

namespace RL

variable (b : RL)

/-- The decay rate `R / L` of the branch current. -/
def decay : ℝ := b.R / b.L

/-- The impedance `R + L s`. -/
def impedance (s : ℂ) : ℂ := b.R + b.L * s

/-- The stored magnetic energy `L i² / 2`. -/
def energy (i : ℝ) : ℝ := b.L * i ^ 2 / 2

/-- With a positive inductance the decay rate is positive exactly when the resistance is. -/
@[tmio M, powerlib_domain] theorem decay_pos_iff {b : RL} (hL : 0 < b.L) :
    0 < b.decay ↔ 0 < b.R :=
  div_pos_iff_of_pos_right hL

/-- With a positive inductance the decay rate is negative exactly when the resistance is. -/
@[tmio M, powerlib_domain] theorem decay_neg_iff {b : RL} (hL : 0 < b.L) :
    b.decay < 0 ↔ b.R < 0 := by
  unfold decay
  constructor
  · intro h
    by_contra hR
    exact absurd h (not_lt.mpr (div_nonneg (not_lt.mp hR) hL.le))
  · intro hR
    exact div_neg_of_neg_of_pos hR hL

/-- The impedance factors through the decay rate. -/
@[tmio M, powerlib_domain] theorem impedance_eq {b : RL} (hL : b.L ≠ 0) (s : ℂ) :
    b.impedance s = b.L * (s + b.decay) := by
  have hL' : (b.L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  simp only [impedance, decay, Complex.ofReal_div]
  field_simp
  ring

/-- A branch with a nonnegative inductance stores a nonnegative energy. -/
@[tmio M, powerlib_domain] theorem energy_nonneg {b : RL} (hL : 0 ≤ b.L) (i : ℝ) :
    0 ≤ b.energy i := by
  unfold energy
  positivity

/-- A branch with a positive inductance stores a positive energy at every nonzero current. -/
@[tmio M, powerlib_domain] theorem energy_pos {b : RL} (hL : 0 < b.L) {i : ℝ} (hi : i ≠ 0) :
    0 < b.energy i := by
  unfold energy
  positivity

/-- Power balance: along `L i' = v − R i` the stored energy changes at `v i − R i²`. -/
@[tmio M, powerlib_domain] theorem power_balance {b : RL} (hL : b.L ≠ 0) (i v : ℝ) :
    b.L * i * ((v - b.R * i) / b.L) = v * i - b.R * i ^ 2 := by
  field_simp

/-- Energy balance along a trajectory: if `L i' = v − R i` at `t`, the stored energy has
derivative `v i − R i²` there. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_energy {b : RL} {i : ℝ → ℝ} {v t i' : ℝ}
    (hi : HasDerivAt i i' t) (hbranch : b.L * i' = v - b.R * i t) :
    HasDerivAt (fun τ => b.energy (i τ)) (v * i t - b.R * i t ^ 2) t := by
  show HasDerivAt (fun τ => b.L * i τ ^ 2 / 2) _ t
  have h := ((hi.fun_pow 2).const_mul b.L).div_const 2
  convert h using 1
  push_cast
  linear_combination (-(i t)) * hbranch

end RL

end powerlib.Passive
