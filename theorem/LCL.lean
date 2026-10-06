import theorem.RL
import theorem.generated.LCLConversion

/-! Canonical continuous-time LCL plant with two series RL branches and an ideal
shunt capacitor. Both terminal voltages are external inputs. No controller,
PLL, PWM, sampling delay, or additional grid state is included. Coordinates are
the stationary scalar phase variables (converter current, capacitor voltage,
grid current). The plant is linear, so perturbations about any constant-input
equilibrium satisfy the same homogeneous continuous-time dynamics. Inductances
and capacitance are strictly positive; resistances may have either sign unless
Passivity is assumed. Stability means all internal state-matrix poles are in
the open left half-plane, with terminal input perturbations held at zero. -/
noncomputable section
namespace powerlib.LCL

@[ext] structure Circuit where
  first : powerlib.Impedance
  second : powerlib.Impedance
  capacitance : powerlib.Positive

@[ext] structure StateSpace where
  first : powerlib.StateSpace
  second : powerlib.StateSpace
  capacitorGain : powerlib.Positive

def toStateSpace (m : Circuit) : StateSpace :=
  let y := generated.convertLCL (fun a (b : powerlib.Positive) => a * b.val)
    powerlib.reciprocal
    (((m.first.resistance, m.first.inductance), (m.second.resistance, m.second.inductance)),
      m.capacitance)
  ⟨⟨y.1.1.1, y.1.1.2⟩, ⟨y.1.2.1, y.1.2.2⟩, y.2⟩

def toCircuit (m : StateSpace) : Circuit :=
  let y := generated.convertLCL (fun a (b : powerlib.Positive) => a * b.val)
    powerlib.reciprocal
    (((m.first.decay, m.first.inputGain), (m.second.decay, m.second.inputGain)),
      m.capacitorGain)
  ⟨⟨y.1.1.1, y.1.1.2⟩, ⟨y.1.2.1, y.1.2.2⟩, y.2⟩

@[simp, powerlib_foundation] theorem circuit_roundtrip (m : Circuit) : toCircuit (toStateSpace m) = m := by
  apply Circuit.ext
  · exact powerlib.impedance_roundtrip m.first
  · exact powerlib.impedance_roundtrip m.second
  · exact powerlib.reciprocal_involutive m.capacitance

@[simp, powerlib_foundation] theorem state_roundtrip (m : StateSpace) : toStateSpace (toCircuit m) = m := by
  apply StateSpace.ext
  · exact powerlib.state_roundtrip m.first
  · exact powerlib.state_roundtrip m.second
  · exact powerlib.reciprocal_involutive m.capacitorGain

def modelEquiv : Circuit ≃ StateSpace where
  toFun := toStateSpace
  invFun := toCircuit
  left_inv := circuit_roundtrip
  right_inv := state_roundtrip

def StateSpace.field (m : StateSpace) (i1 vc i2 u vg : ℝ) : ℝ × ℝ × ℝ :=
  (-m.first.decay * i1 - m.first.inputGain.val * vc + m.first.inputGain.val * u,
    m.capacitorGain.val * (i1 - i2),
    m.second.inputGain.val * vc - m.second.decay * i2 - m.second.inputGain.val * vg)

@[powerlib_foundation] theorem same_dynamics (m : Circuit) (i1 vc i2 u vg : ℝ) :
    (toStateSpace m).field i1 vc i2 u vg =
      ((u - m.first.resistance * i1 - vc) / m.first.inductance.val,
        (i1 - i2) / m.capacitance.val,
        (vc - m.second.resistance * i2 - vg) / m.second.inductance.val) := by
  dsimp [StateSpace.field, toStateSpace, generated.convertLCL, powerlib.reciprocal]
  ext <;> field_simp [ne_of_gt m.first.inductance.property,
    ne_of_gt m.second.inductance.property, ne_of_gt m.capacitance.property]
  ring

def Circuit.a3 (m : Circuit) : ℝ :=
  m.first.inductance.val * m.second.inductance.val * m.capacitance.val
def Circuit.a2 (m : Circuit) : ℝ :=
  m.capacitance.val * (m.first.resistance * m.second.inductance.val +
    m.second.resistance * m.first.inductance.val)
def Circuit.a1 (m : Circuit) : ℝ :=
  m.first.inductance.val + m.second.inductance.val +
    m.capacitance.val * m.first.resistance * m.second.resistance
def Circuit.a0 (m : Circuit) : ℝ := m.first.resistance + m.second.resistance

def Circuit.frequency (m : Circuit) (s : ℂ) : ℂ :=
  (m.a3 : ℂ) * s ^ 3 + (m.a2 : ℂ) * s ^ 2 + (m.a1 : ℂ) * s + (m.a0 : ℂ)

-- This is the denominator of the internal three-state dynamics.
@[powerlib_foundation] theorem characteristic_identity (m : Circuit) (s : ℂ) :
    m.frequency s =
      ((m.first.inductance.val : ℂ) * s + (m.first.resistance : ℂ)) *
        ((m.capacitance.val : ℂ) * s *
          ((m.second.inductance.val : ℂ) * s + (m.second.resistance : ℂ)) + 1) +
      (m.second.inductance.val : ℂ) * s + (m.second.resistance : ℂ) := by
  simp [Circuit.frequency, Circuit.a3, Circuit.a2, Circuit.a1, Circuit.a0]
  ring

def Circuit.Stable (m : Circuit) : Prop := ∀ s : ℂ, m.frequency s = 0 → s.re < 0

def StateSpace.matrix (m : StateSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![-m.first.decay, -m.first.inputGain.val, 0],
    ![m.capacitorGain.val, 0, -m.capacitorGain.val],
    ![0, m.second.inputGain.val, -m.second.decay]]

-- The matrix is constructed from, and agrees with, the physical vector field.
@[powerlib_foundation] theorem StateSpace.matrix_mulVec (m : StateSpace) (x y z : ℝ) :
    m.matrix.mulVec ![x, y, z] =
      ![(m.field x y z 0 0).1, (m.field x y z 0 0).2.1,
        (m.field x y z 0 0).2.2] := by
  ext i
  fin_cases i <;>
    simp [StateSpace.matrix, StateSpace.field, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

@[powerlib_foundation] theorem StateSpace.perturbation (m : StateSpace) (x y z dx dy dz u vg : ℝ) :
    let f := m.field (x + dx) (y + dy) (z + dz) u vg
    let base := m.field x y z u vg
    (f.1 - base.1, f.2.1 - base.2.1, f.2.2 - base.2.2) = m.field dx dy dz 0 0 := by
  dsimp [StateSpace.field]
  ext <;> ring

def StateSpace.characteristic (m : StateSpace) (s : ℂ) : ℂ :=
  Matrix.det (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - m.matrix.map (fun r => (r : ℂ)))

@[powerlib_foundation] theorem same_characteristic (m : Circuit) (s : ℂ) :
    (toStateSpace m).characteristic s = m.frequency s / (m.a3 : ℂ) := by
  have hL1 : (m.first.inductance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.first.inductance.property
  have hL2 : (m.second.inductance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.second.inductance.property
  have hC : (m.capacitance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.capacitance.property
  simp [StateSpace.characteristic, StateSpace.matrix, Matrix.map, Matrix.of_apply,
    Matrix.det_fin_three,
    toStateSpace, generated.convertLCL, powerlib.reciprocal, Circuit.frequency,
    Circuit.a3, Circuit.a2, Circuit.a1, Circuit.a0]
  field_simp [hL1, hL2, hC]
  ring_nf

def StateSpace.Stable (m : StateSpace) : Prop :=
  ∀ s : ℂ, m.characteristic s = 0 → s.re < 0

@[simp, powerlib_foundation] theorem stability_agrees (m : Circuit) : (toStateSpace m).Stable ↔ m.Stable := by
  have hn : (m.a3 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (mul_pos (mul_pos m.first.inductance.property
      m.second.inductance.property) m.capacitance.property)
  simp only [StateSpace.Stable, Circuit.Stable, same_characteristic, div_eq_zero_iff,
    hn, or_false]

def Circuit.Passive (m : Circuit) : Prop :=
  0 ≤ m.first.resistance ∧ 0 ≤ m.second.resistance
@[simp] def Circuit.Damped (m : Circuit) : Prop :=
  m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0

@[powerlib_foundation] theorem hurwitz_gap (m : Circuit) : m.a2 * m.a1 - m.a3 * m.a0 =
    m.capacitance.val * (m.first.resistance * m.second.inductance.val ^ 2 +
      m.second.resistance * m.first.inductance.val ^ 2 +
      m.capacitance.val * m.first.resistance * m.second.resistance *
        (m.first.resistance * m.second.inductance.val +
          m.second.resistance * m.first.inductance.val)) := by
  dsimp [Circuit.a3, Circuit.a2, Circuit.a1, Circuit.a0]
  ring

-- A direct complex-root proof of the strict cubic Hurwitz sufficient condition.
@[powerlib_foundation] theorem cubic_hurwitz (a3 a2 a1 a0 : ℝ) (h3 : 0 < a3) (h2 : 0 < a2)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : 0 < a2 * a1 - a3 * a0)
    (s : ℂ) (hs : (a3 : ℂ)*s^3 + (a2 : ℂ)*s^2 + (a1 : ℂ)*s + (a0 : ℂ) = 0) :
    s.re < 0 := by
  by_contra hn
  have hx : 0 ≤ s.re := le_of_not_gt hn
  have hr : a3*(s.re^3-3*s.re*s.im^2) + a2*(s.re^2-s.im^2) + a1*s.re + a0 = 0 := by
    have h := congrArg Complex.re hs
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at h
    nlinarith [h]
  have hi : s.im*(a3*(3*s.re^2-s.im^2)+2*a2*s.re+a1) = 0 := by
    have h := congrArg Complex.im hs
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at h
    nlinarith [h]
  by_cases hy : s.im = 0
  · have hp : 0 < a3*s.re^3 + a2*s.re^2 + a1*s.re + a0 := by positivity
    simp only [hy] at hr
    linarith
  · have hf : a3*(3*s.re^2-s.im^2)+2*a2*s.re+a1 = 0 := (mul_eq_zero.mp hi).resolve_left hy
    have hz : 8*a3^2*s.re^3 + 8*a3*a2*s.re^2 +
        2*(a3*a1+a2^2)*s.re + (a2*a1-a3*a0) = 0 := by
      linear_combination -a3 * hr + (3*a3*s.re+a2) * hf
    have hp : 0 < 8*a3^2*s.re^3 + 8*a3*a2*s.re^2 +
        2*(a3*a1+a2^2)*s.re + (a2*a1-a3*a0) := by positivity
    linarith

@[powerlib_domain, aesop unsafe 90% apply] theorem stable_of_hurwitz (m : Circuit) (h2 : 0 < m.a2) (h1 : 0 < m.a1)
    (h0 : 0 < m.a0) (hg : 0 < m.a2*m.a1-m.a3*m.a0) : m.Stable := by
  have h3 : 0 < m.a3 := mul_pos (mul_pos m.first.inductance.property
    m.second.inductance.property) m.capacitance.property
  exact fun s hs => cubic_hurwitz m.a3 m.a2 m.a1 m.a0 h3 h2 h1 h0 hg s hs

@[powerlib_foundation, aesop unsafe 80% apply] theorem passive_hurwitz (m : Circuit) (hp : m.Passive) (hd : m.Damped) :
    0 < m.a2 ∧ 0 < m.a1 ∧ 0 < m.a0 ∧ 0 < m.a2*m.a1-m.a3*m.a0 := by
  rcases hp with ⟨hr1, hr2⟩
  have hL1 := m.first.inductance.property
  have hL2 := m.second.inductance.property
  have hC := m.capacitance.property
  have hpos : 0 < m.first.resistance ∨ 0 < m.second.resistance := by
    rcases hd with h | h
    · left; exact lt_of_le_of_ne hr1 (Ne.symm h)
    · right; exact lt_of_le_of_ne hr2 (Ne.symm h)
  have h0 : 0 < m.a0 := by dsimp [Circuit.a0]; rcases hpos with h | h <;> linarith
  have h1 : 0 < m.a1 := by dsimp [Circuit.a1]; positivity
  have h2 : 0 < m.a2 := by
    dsimp [Circuit.a2]
    rcases hpos with h | h <;> positivity
  have hg : 0 < m.a2*m.a1-m.a3*m.a0 := by
    rw [hurwitz_gap]
    rcases hpos with h | h <;> positivity
  exact ⟨h2, h1, h0, hg⟩

-- With passive resistances, strict stability is exactly "not both zero".
@[simp, powerlib_domain] theorem passive_stable_iff (m : Circuit) (hp : m.Passive) : m.Stable ↔ m.Damped := by
  constructor
  · intro hs
    by_contra hn
    have hz : m.first.resistance = 0 ∧ m.second.resistance = 0 := by
      simpa [Circuit.Damped] using hn
    have hf : m.frequency 0 = 0 := by
      simp [Circuit.frequency, Circuit.a0, hz.1, hz.2]
    have h := hs 0 hf
    simp at h
  · intro hd
    rcases passive_hurwitz m hp hd with ⟨h2, h1, h0, hg⟩
    exact stable_of_hurwitz m h2 h1 h0 hg

@[ext] structure SymmetricMatrix where
  p11 : ℝ
  p12 : ℝ
  p13 : ℝ
  p22 : ℝ
  p23 : ℝ
  p33 : ℝ

def SymmetricMatrix.minor2 (p : SymmetricMatrix) : ℝ := p.p11*p.p22-p.p12^2
def SymmetricMatrix.det (p : SymmetricMatrix) : ℝ :=
  p.p11*(p.p22*p.p33-p.p23^2) - p.p12*(p.p12*p.p33-p.p23*p.p13) +
    p.p13*(p.p12*p.p23-p.p22*p.p13)

def energy (p : SymmetricMatrix) (x y z : ℝ) : ℝ :=
  p.p11*x^2 + 2*p.p12*x*y + 2*p.p13*x*z + p.p22*y^2 + 2*p.p23*y*z + p.p33*z^2

def energyDerivative (p : SymmetricMatrix) (x y z dx dy dz : ℝ) : ℝ :=
  2*(p.p11*x+p.p12*y+p.p13*z)*dx +
    2*(p.p12*x+p.p22*y+p.p23*z)*dy + 2*(p.p13*x+p.p23*y+p.p33*z)*dz

@[powerlib_foundation, aesop unsafe 75% apply] theorem energy_positive (p : SymmetricMatrix) (h1 : 0 < p.p11)
    (h2 : 0 < p.minor2) (h3 : 0 < p.det) (x y z : ℝ)
    (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < energy p x y z := by
  have he : energy p x y z =
      p.p11*(x+p.p12/p.p11*y+p.p13/p.p11*z)^2 +
      (p.minor2/p.p11)*(y+(p.p11*p.p23-p.p12*p.p13)/p.minor2*z)^2 +
      (p.det/p.minor2)*z^2 := by
    field_simp [ne_of_gt h1, ne_of_gt h2]
    dsimp [energy, SymmetricMatrix.minor2, SymmetricMatrix.det]
    ring
  by_cases hz : z = 0
  · subst z
    by_cases hy : y = 0
    · subst y
      have hx : x ≠ 0 := by simpa using hn
      simpa [energy] using mul_pos h1 (sq_pos_of_ne_zero hx)
    · have he' : energy p x y 0 =
          p.p11*(x+p.p12/p.p11*y)^2 + (p.minor2/p.p11)*y^2 := by simpa using he
      rw [he']
      exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt h1) (sq_nonneg _))
        (mul_pos (div_pos h2 h1) (sq_pos_of_ne_zero hy))
  · rw [he]
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg (le_of_lt h1) (sq_nonneg _))
        (mul_nonneg (le_of_lt (div_pos h2 h1)) (sq_nonneg _)))
      (mul_pos (div_pos h3 h2) (sq_pos_of_ne_zero hz))

structure Accepted (m : Circuit) where
  p : SymmetricMatrix
  p11_pos : 0 < p.p11
  minor2_pos : 0 < p.minor2
  det_pos : 0 < p.det
  a2_pos : 0 < m.a2
  a1_pos : 0 < m.a1
  a0_pos : 0 < m.a0
  gap_pos : 0 < m.a2*m.a1-m.a3*m.a0
  eq11 : -2*(toStateSpace m).first.decay*p.p11 + 2*(toStateSpace m).capacitorGain.val*p.p12 = -1
  eq12 : -(toStateSpace m).first.inputGain.val*p.p11 - (toStateSpace m).first.decay*p.p12 +
    (toStateSpace m).capacitorGain.val*p.p22 + (toStateSpace m).second.inputGain.val*p.p13 = 0
  eq13 : -((toStateSpace m).first.decay+(toStateSpace m).second.decay)*p.p13 -
    (toStateSpace m).capacitorGain.val*p.p12 + (toStateSpace m).capacitorGain.val*p.p23 = 0
  eq22 : -2*(toStateSpace m).first.inputGain.val*p.p12 + 2*(toStateSpace m).second.inputGain.val*p.p23 = -1
  eq23 : -(toStateSpace m).first.inputGain.val*p.p13 - (toStateSpace m).capacitorGain.val*p.p22 -
    (toStateSpace m).second.decay*p.p23 + (toStateSpace m).second.inputGain.val*p.p33 = 0
  eq33 : -2*(toStateSpace m).capacitorGain.val*p.p23 - 2*(toStateSpace m).second.decay*p.p33 = -1

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Accepted.stable {m : Circuit} (c : Accepted m) : (toStateSpace m).Stable :=
  (stability_agrees m).mpr (stable_of_hurwitz m c.a2_pos c.a1_pos c.a0_pos c.gap_pos)

@[powerlib_domain, aesop norm simp] theorem Accepted.positive {m : Circuit} (c : Accepted m) (x y z : ℝ)
    (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < energy c.p x y z :=
  energy_positive c.p c.p11_pos c.minor2_pos c.det_pos x y z hn

@[powerlib_domain, aesop norm simp] theorem Accepted.dissipation {m : Circuit} (c : Accepted m) (x y z : ℝ) :
    let f := (toStateSpace m).field x y z 0 0
    energyDerivative c.p x y z f.1 f.2.1 f.2.2 = -(x^2+y^2+z^2) := by
  dsimp [StateSpace.field, energyDerivative]
  linear_combination x^2*c.eq11 + 2*x*y*c.eq12 + 2*x*z*c.eq13 +
    y^2*c.eq22 + 2*y*z*c.eq23 + z^2*c.eq33

end powerlib.LCL

namespace powerlib

-- Public theorem for the passive canonical LCL plant's internal poles.
@[simp, powerlib_domain] theorem lcl_stable_iff (m : LCL.Circuit) (hp : m.Passive) :
    (LCL.toStateSpace m).Stable ↔ m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 :=
  (LCL.stability_agrees m).trans (LCL.passive_stable_iff m hp)

end powerlib
