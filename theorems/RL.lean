import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import theorems.generated.Conversion

/-! A canonical single-port RL family: i' = -a*i + b*v and Z(s) = R + L*s.
The input gain and inductance are positive. Resistance may have either sign.
This fixes the state coordinate to physical current; no hidden states are allowed. -/
noncomputable section
namespace powerlib

abbrev Positive := {x : ℝ // 0 < x}

def reciprocal (x : Positive) : Positive := ⟨x.val⁻¹, inv_pos.mpr x.property⟩

theorem reciprocal_involutive (x : Positive) : reciprocal (reciprocal x) = x := by
  apply Subtype.ext
  simp [reciprocal]

theorem scale_cancel (x : ℝ) (y : Positive) : (x * (reciprocal y).val) * y.val = x := by
  dsimp [reciprocal]
  field_simp [ne_of_gt y.property]

@[ext] structure StateSpace where
  decay : ℝ
  inputGain : Positive

@[ext] structure Impedance where
  resistance : ℝ
  inductance : Positive

-- Both descriptions use the SAME Agda-generated executable conversion.
def toImpedance (m : StateSpace) : Impedance :=
  let y := generated.convert (fun a (b : Positive) => a * b.val) reciprocal (m.decay, m.inputGain)
  ⟨y.1, y.2⟩

def toStateSpace (m : Impedance) : StateSpace :=
  let y := generated.convert (fun a (b : Positive) => a * b.val) reciprocal (m.resistance, m.inductance)
  ⟨y.1, y.2⟩

theorem state_roundtrip (m : StateSpace) : toStateSpace (toImpedance m) = m := by
  apply StateSpace.ext
  · exact (by simpa [toStateSpace, toImpedance, generated.convert, reciprocal] using
      scale_cancel m.decay m.inputGain)
  · exact reciprocal_involutive m.inputGain

theorem impedance_roundtrip (m : Impedance) : toImpedance (toStateSpace m) = m := by
  apply Impedance.ext
  · exact (by simpa [toStateSpace, toImpedance, generated.convert, reciprocal] using
      scale_cancel m.resistance m.inductance)
  · exact reciprocal_involutive m.inductance

def modelEquiv : StateSpace ≃ Impedance where
  toFun := toImpedance
  invFun := toStateSpace
  left_inv := state_roundtrip
  right_inv := impedance_roundtrip

def StateSpace.field (m : StateSpace) (current voltage : ℝ) : ℝ :=
  -m.decay * current + m.inputGain.val * voltage

theorem same_dynamics (m : Impedance) (current voltage : ℝ) :
    (toStateSpace m).field current voltage =
      (voltage - m.resistance * current) / m.inductance.val := by
  dsimp [StateSpace.field, toStateSpace, generated.convert, reciprocal]
  field_simp [ne_of_gt m.inductance.property]
  ring

def Impedance.frequency (m : Impedance) (s : ℂ) : ℂ :=
  (m.resistance : ℂ) + (m.inductance.val : ℂ) * s

-- This equation pins the port interpretation: voltage is impedance times current.
theorem same_port_relation (m : Impedance) (s current voltage : ℂ) :
    (s + ((toStateSpace m).decay : ℂ)) * current =
        ((toStateSpace m).inputGain.val : ℂ) * voltage ↔
      voltage = m.frequency s * current := by
  have hL : (m.inductance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.inductance.property
  dsimp [toStateSpace, generated.convert, reciprocal, Impedance.frequency]
  push_cast
  constructor
  · intro h
    have hh := congrArg (fun z : ℂ => (m.inductance.val : ℂ) * z) h
    field_simp [hL] at hh
    linear_combination -hh
  · intro h
    rw [h]
    field_simp [hL]
    ring_nf
    simp

def StateSpace.Stable (m : StateSpace) : Prop := 0 < m.decay

-- Voltage is the input: zeros of Z(s) are poles of the admittance 1/Z(s).
def Impedance.Stable (m : Impedance) : Prop :=
  ∀ s : ℂ, m.frequency s = 0 → s.re < 0

theorem frequency_zero_iff (m : Impedance) (s : ℂ) :
    m.frequency s = 0 ↔ s = ((-(m.resistance / m.inductance.val) : ℝ) : ℂ) := by
  have hL : (m.inductance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.inductance.property
  dsimp [Impedance.frequency]
  push_cast
  constructor
  · intro h
    rw [← neg_div]
    apply (eq_div_iff hL).mpr
    linear_combination h
  · intro h
    rw [h]
    field_simp [hL]
    ring

theorem impedance_stable_iff (m : Impedance) : m.Stable ↔ 0 < m.resistance := by
  constructor
  · intro h
    have hr := h ((-(m.resistance / m.inductance.val) : ℝ) : ℂ)
      ((frequency_zero_iff m _).mpr rfl)
    have hp : 0 < m.resistance / m.inductance.val := by simpa using hr
    exact (div_pos_iff_of_pos_right m.inductance.property).mp hp
  · intro h s hs
    rw [(frequency_zero_iff m s).mp hs]
    simp only [Complex.ofReal_re, neg_lt_zero]
    exact div_pos h m.inductance.property

theorem stability_agrees (m : Impedance) : (toStateSpace m).Stable ↔ m.Stable := by
  rw [impedance_stable_iff]
  change 0 < m.resistance * m.inductance.val⁻¹ ↔ 0 < m.resistance
  rw [← div_eq_mul_inv]
  exact div_pos_iff_of_pos_right m.inductance.property

-- A certificate must be about the exact submitted impedance model.
structure Accepted (m : Impedance) where
  p : ℝ
  rate : ℝ
  p_pos : 0 < p
  rate_pos : 0 < rate
  lyapunov_identity : 2 * (toStateSpace m).decay * p = 1
  rate_exact : rate = 2 * (toStateSpace m).decay

def energy (p current : ℝ) : ℝ := p * current ^ 2

theorem Accepted.stable {m : Impedance} (c : Accepted m) : m.Stable := by
  apply (stability_agrees m).mp
  change 0 < (toStateSpace m).decay
  nlinarith [c.p_pos, c.lyapunov_identity]

theorem Accepted.dissipation {m : Impedance} (c : Accepted m) (current : ℝ) :
    2 * c.p * current * (toStateSpace m).field current 0 = -current ^ 2 := by
  dsimp [StateSpace.field]
  nlinarith [c.lyapunov_identity]

-- The autonomous response exists for every initial current and every real time.
def response (m : Impedance) (initial t : ℝ) : ℝ :=
  initial * Real.exp (-(toStateSpace m).decay * t)

theorem response_initial (m : Impedance) (initial : ℝ) : response m initial 0 = initial := by
  simp [response]

theorem response_solves (m : Impedance) (initial t : ℝ) :
    HasDerivAt (response m initial) ((toStateSpace m).field (response m initial t) 0) t := by
  convert (((hasDerivAt_id t).const_mul (-(toStateSpace m).decay)).exp.const_mul initial) using 1
  simp [response, StateSpace.field]
  ring

theorem Accepted.decay_bound {m : Impedance} (c : Accepted m) (initial t : ℝ) :
    (response m initial t) ^ 2 = initial ^ 2 * Real.exp (-c.rate * t) := by
  rw [response, mul_pow, ← Real.exp_nat_mul, c.rate_exact]
  congr 2
  ring

end powerlib
