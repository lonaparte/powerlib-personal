import theorem.TMIO.ClaimElab
import theorem.Linear.Family
import theorem.Linear.Realization
import theorem.Port.Linear
import theorem.generated.Conversion

/-! # The RL branch

Model boundary: one series resistor–inductor branch driven by its terminal voltage, in continuous
time: `L i' = v - R i`. State: the branch current `i` (one state, stationary frame, no dq
transformation). Port: input voltage `v`, output current `i`. Inductance `L > 0`; resistance `R`
real, of either sign. No controller, PLL, PWM, delay, switching or discretization.

Two representations — impedance parameters `(R, L)` and state-space parameters
`(a, b) = (R / L, 1 / L)` — are related by the Agda-generated conversion, an equivalence. The
plant map sends the state-space parameters to `i' = -a i + b v`; the family reads every branch as
the port system of its plant, so every sentence denotes the single semantics pulled back.

The family is faithful: its translation chain is its semantics connection
(`chain_eq_semantics`). Every sentence — the stability sentences, decay at a rate, sampled
contraction, conservation and passivity — is carved out exactly by a condition on the resistance
and the time constant. -/

noncomputable section

namespace powerlib.Circuits.RL

open Matrix LinearSystems TMIO

/-- Positive reals. -/
abbrev Positive := {x : ℝ // 0 < x}

/-- The reciprocal of a positive real. -/
def reciprocal (x : Positive) : Positive := ⟨x.val⁻¹, inv_pos.mpr x.property⟩

@[simp, powerlib_foundation] theorem reciprocal_involutive (x : Positive) :
    reciprocal (reciprocal x) = x := by
  apply Subtype.ext
  simp [reciprocal]

@[simp, powerlib_foundation] theorem scale_cancel (x : ℝ) (y : Positive) :
    (x * (reciprocal y).val) * y.val = x := by
  dsimp [reciprocal]
  field_simp [ne_of_gt y.property]

/-- Impedance parameters `Z(s) = R + L s`. -/
@[ext] structure Impedance where
  resistance : ℝ
  inductance : Positive

/-- State-space parameters of `i' = -a i + b v`. -/
@[ext] structure StateSpace where
  decay : ℝ
  inputGain : Positive

/-- The Agda-generated conversion, from state-space to impedance parameters. -/
def toImpedance (m : StateSpace) : Impedance :=
  let y := generated.convert (fun a (b : Positive) => a * b.val) reciprocal (m.decay, m.inputGain)
  ⟨y.1, y.2⟩

/-- The same generated conversion, from impedance to state-space parameters. -/
def toStateSpace (m : Impedance) : StateSpace :=
  let y := generated.convert (fun a (b : Positive) => a * b.val) reciprocal
    (m.resistance, m.inductance)
  ⟨y.1, y.2⟩

@[simp, powerlib_foundation] theorem state_roundtrip (m : StateSpace) :
    toStateSpace (toImpedance m) = m := by
  apply StateSpace.ext
  · exact (by simpa [toStateSpace, toImpedance, generated.convert, reciprocal] using
      scale_cancel m.decay m.inputGain)
  · exact reciprocal_involutive m.inputGain

@[simp, powerlib_foundation] theorem impedance_roundtrip (m : Impedance) :
    toImpedance (toStateSpace m) = m := by
  apply Impedance.ext
  · exact (by simpa [toStateSpace, toImpedance, generated.convert, reciprocal] using
      scale_cancel m.resistance m.inductance)
  · exact reciprocal_involutive m.inductance

/-- The two representations are equivalent. -/
def modelEquiv : StateSpace ≃ Impedance where
  toFun := toImpedance
  invFun := toStateSpace
  left_inv := state_roundtrip
  right_inv := impedance_roundtrip

@[simp, powerlib_foundation] theorem toStateSpace_decay (m : Impedance) :
    (toStateSpace m).decay = m.resistance / m.inductance.val := by
  simp [toStateSpace, generated.convert, reciprocal, div_eq_mul_inv]

@[simp, powerlib_foundation] theorem toStateSpace_inputGain (m : Impedance) :
    (toStateSpace m).inputGain.val = (m.inductance.val)⁻¹ := by
  simp [toStateSpace, generated.convert, reciprocal]

/-! ## The plant map -/

/-- The plant `i' = -a i + b v`, `y = i`. -/
def StateSpace.plant (m : StateSpace) : Linear.Plant 1 1 :=
  ⟨!![-m.decay], !![m.inputGain.val], !![1], 0⟩

/-- The plant of the impedance representation, through the conversion. -/
def Impedance.plant (m : Impedance) : Linear.Plant 1 1 := (toStateSpace m).plant

/-- Both representations have the same plant. -/
@[simp, powerlib_foundation] theorem plant_toImpedance (m : StateSpace) :
    (toImpedance m).plant = m.plant := by
  simp [Impedance.plant]

/-- The RL plant is Hurwitz exactly when the resistance is positive. -/
@[simp, powerlib_foundation] theorem isHurwitz_iff (m : Impedance) :
    IsHurwitz m.plant.A ↔ 0 < m.resistance := by
  simp only [Impedance.plant, StateSpace.plant, toStateSpace_decay]
  rw [Linear.isHurwitz_one_iff, neg_lt_zero, div_pos_iff_of_pos_right m.inductance.property]

/-! ## Certificates -/

/-- Synthesis: the closed-form Lyapunov certificate `P = L / (2 R)` for a positive resistance. -/
def synthesize (m : Impedance) (hR : 0 < m.resistance) : Linear.Certificate m.plant.A where
  P := !![1 / (2 * (toStateSpace m).decay)]
  symmetric := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  positive x hx := by
    have ha : 0 < (toStateSpace m).decay := by
      rw [toStateSpace_decay]
      exact div_pos hR m.inductance.property
    have h0 : x 0 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i
      exact h
    have hc : 0 < 1 / (2 * (toStateSpace m).decay) := by positivity
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [mul_pos hc (mul_self_pos.mpr h0)]
  lyapunov := by
    have hL : m.inductance.val ≠ 0 := m.inductance.property.ne'
    have hR' : m.resistance ≠ 0 := hR.ne'
    ext i j
    fin_cases i
    fin_cases j
    simp [Impedance.plant, StateSpace.plant, Matrix.mul_apply]
    field_simp
    ring

/-- The physical energy `L i² / 2` is a KYP certificate for a nonnegative resistance. -/
def kyp (m : Impedance) (hR : 0 ≤ m.resistance) : Linear.KYP m.plant where
  P := !![m.inductance.val]
  symmetric := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  nonneg x := by
    simp [dotProduct, Matrix.mulVec]
    nlinarith [mul_nonneg m.inductance.property.le (mul_self_nonneg (x 0))]
  dissipation x := by
    have hL := m.inductance.property
    simp [Impedance.plant, StateSpace.plant, dotProduct, Matrix.mulVec, Matrix.mul_apply]
    field_simp
    nlinarith [mul_self_nonneg (x 0)]
  output := by
    have hL := m.inductance.property
    ext i j
    fin_cases i
    fin_cases j
    simp [Impedance.plant, StateSpace.plant, Matrix.mul_apply]
    field_simp
  feedthrough u := by simp [Impedance.plant, StateSpace.plant]

/-! ## The frequency domain -/

/-- The transfer function from terminal voltage to branch current is the admittance
`1 / (R + L s)`, at every complex frequency (both sides vanish at the pole). -/
@[powerlib_foundation] theorem transfer_eq (m : Impedance) (s : ℂ) :
    Linear.transfer m.plant s = !![((m.resistance : ℂ) + m.inductance.val * s)⁻¹] := by
  have hL : (m.inductance.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr m.inductance.property.ne'
  ext i j
  fin_cases i
  fin_cases j
  simp [Linear.transfer, Linear.characteristicMatrix, Impedance.plant, StateSpace.plant,
    Ring.inverse_eq_inv', Matrix.mul_apply]
  rw [show (m.resistance : ℂ) + m.inductance.val * s =
      m.inductance.val * (s + m.resistance / m.inductance.val) by field_simp; ring, mul_inv]
  ring

/-- The branch has no hidden mode. -/
@[powerlib_foundation] theorem minimal (m : Impedance) : m.plant.Minimal := by
  have hL : (m.inductance.val : ℝ) ≠ 0 := m.inductance.property.ne'
  refine ⟨fun x => ⟨fun _ _ => x 0 / (toStateSpace m).inputGain.val, ?_⟩, fun x hx => ?_⟩
  · funext i
    fin_cases i
    simp [Impedance.plant, StateSpace.plant, dotProduct]
    field_simp
  · have h0 := congrFun (hx 0) 0
    funext i
    fin_cases i
    simpa [Impedance.plant, StateSpace.plant, Matrix.mulVec, dotProduct] using h0

/-! ## Requirements and the faithful family -/

/-- Engineering requirements on the RL parameters. -/
inductive Requirement
  | positiveResistance
  | nonnegativeResistance
  | negativeResistance
  | lossless
  | decayRateAtLeast (a : ℝ)
  | resistanceAtLeast (r : ℝ)
  | resistanceAtMost (r : ℝ)
  | inductanceAtLeast (l : ℝ)
  | inductanceAtMost (l : ℝ)

/-- Satisfaction of a requirement by a complete RL model. -/
def Meets (m : Impedance) : Requirement → Prop
  | .positiveResistance => 0 < m.resistance
  | .nonnegativeResistance => 0 ≤ m.resistance
  | .negativeResistance => m.resistance < 0
  | .lossless => m.resistance = 0
  | .decayRateAtLeast a => a ≤ m.resistance / m.inductance.val
  | .resistanceAtLeast r => r ≤ m.resistance
  | .resistanceAtMost r => m.resistance ≤ r
  | .inductanceAtLeast l => l ≤ m.inductance.val
  | .inductanceAtMost l => m.inductance.val ≤ l

/-- The translation of the sentences into requirements. -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable => {.nonnegativeResistance}
  | .flow .unstable => {.negativeResistance}
  | .flow (.decay a) => {.decayRateAtLeast a}
  | .flow .conservative => {.lossless}
  | .flow _ => {.positiveResistance}
  | .passive => {.nonnegativeResistance}

/-- The RL family: every branch read as the port system of its plant, the requirement language
and the translation table. -/
def family : Family Impedance Requirement 1 1 := ⟨fun m => m.plant.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear Impedance.plant := fun _ => rfl

@[powerlib_foundation] theorem plant_A (m : Impedance) :
    m.plant.A = !![-(m.resistance / m.inductance.val)] := by
  simp [Impedance.plant, StateSpace.plant, toStateSpace_decay]

/-- The physical energy `L i² / 2` is positive on every nonzero current. -/
@[powerlib_foundation] theorem energy_pos (m : Impedance) (hR : 0 ≤ m.resistance)
    (x : Fin 1 → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ ((kyp m hR).P *ᵥ x) := by
  have h0 : x 0 ≠ 0 := by
    intro h
    apply hx
    funext i
    fin_cases i
    exact h
  simp [kyp, dotProduct, Matrix.mulVec]
  nlinarith [mul_pos m.inductance.property (mul_self_pos.mpr h0)]

/-- A constant current `c` held by the terminal voltage `R c` draws the power `R c²`. -/
@[powerlib_foundation] theorem field_hold (m : Impedance) (c : ℝ) :
    m.plant.system.field (WithLp.toLp 2 ![c]) ![m.resistance * c] = 0 := by
  have hL := m.inductance.property.ne'
  ext i
  fin_cases i
  simp [Impedance.plant, StateSpace.plant, Linear.Plant.system, dotProduct, toStateSpace_decay]
  field_simp
  ring

@[powerlib_foundation] theorem supply_hold (m : Impedance) (c : ℝ) :
    m.plant.system.supply (WithLp.toLp 2 ![c]) ![m.resistance * c] = m.resistance * c ^ 2 := by
  simp [Port.System.supply, Impedance.plant, StateSpace.plant, Linear.Plant.system, dotProduct]
  ring

/-- The RL family is faithful: its translation chain is its semantics connection. Every sentence
is carved out exactly by its requirement — Lyapunov stability and passivity by a nonnegative
resistance, the attractive sentences and sampled contraction by a positive one, instability by a
negative one, conservation by a lossless branch, and decay at the rate `a` by a time constant
`L / R` with `a ≤ R / L`. -/
@[powerlib_domain] theorem chain_eq_semantics :
    connection% (family.chain = family.semantics) := by
  unfold powerlib.TMIO.Statement
  have hLS : ∀ m : Impedance,
      LyapunovStable (affineLinearVectorField m.plant.A 0) 0 ↔ 0 ≤ m.resistance := by
    intro m
    refine ⟨fun h => ?_, fun hR => (kyp m hR).lyapunovStable_of_pos (energy_pos m hR)⟩
    by_contra hR
    refine Linear.unstable_of_eigenvalue 0 (μ := ((-(toStateSpace m).decay : ℝ) : ℂ))
      (v := fun _ => 1) (by simp [funext_iff]) ?_ ?_ h
    · funext i
      fin_cases i
      simp [Impedance.plant, StateSpace.plant, Matrix.mulVec, dotProduct]
    · simp only [Complex.ofReal_re, toStateSpace_decay, neg_pos]
      exact div_neg_of_neg_of_pos (not_le.mp hR) m.inductance.property
  have hhur : ∀ {P : Flow.Property}, P.Attractive ∨ P = .contractive → ∀ m : Impedance,
      P.holds (affineLinearVectorField m.plant.A 0) 0 ↔ 0 < m.resistance := by
    intro P hP m
    rw [← family_isLinear.mem_den_flow, family_isLinear.den_hurwitz hP, Set.mem_ofPred_eq,
      isHurwitz_iff]
  refine Family.chain_eq_semantics_iff.mpr fun s => ?_
  ext m
  rw [Family.mem_den, mem_realize]
  change (∀ q ∈ translate s, Meets m q) ↔ s.holds m.plant.system
  rcases s with P | _
  · rw [Sentence.holds_flow, Linear.Plant.system_zeroInput]
    cases P
    case lyapunovStable => simpa [translate, Meets, Flow.Property.holds] using (hLS m).symm
    case unstable =>
      simp only [translate, Set.mem_singleton_iff, forall_eq, Meets, Flow.Property.holds,
        Unstable, hLS, not_le]
    case decay a =>
      simp only [translate, Set.mem_singleton_iff, forall_eq, Meets, Flow.Property.holds]
      rw [plant_A, Linear.decay_scalar_iff]
    case conservative =>
      simp only [translate, Set.mem_singleton_iff, forall_eq, Meets, Flow.Property.holds]
      constructor
      · intro hR
        have hA : m.plant.A = 0 := by
          rw [plant_A, hR, zero_div, neg_zero]
          ext i j
          fin_cases i
          fin_cases j
          rfl
        refine Linear.conservative_of_quadratic (P := 1) (by simp) (fun v hv => ?_) (by simp [hA])
        have h0 : v 0 ≠ 0 := by
          intro h
          apply hv
          funext i
          fin_cases i
          exact h
        simpa [dotProduct] using mul_self_pos.mpr h0
      · intro h
        have hnn := (hLS m).mp h.lyapunovStable
        have hnh := family_isLinear.not_isHurwitz_of_mem_den_conservative one_pos
          (family_isLinear.mem_den_flow.mpr h)
        rw [isHurwitz_iff] at hnh
        exact le_antisymm (not_lt.mp hnh) hnn
    case locallyAsymptoticallyStable =>
      simpa [translate, Meets] using
        (hhur (P := .locallyAsymptoticallyStable) (Or.inl trivial) m).symm
    case locallyExponentiallyStable =>
      simpa [translate, Meets] using
        (hhur (P := .locallyExponentiallyStable) (Or.inl trivial) m).symm
    case globallyAsymptoticallyStable =>
      simpa [translate, Meets] using
        (hhur (P := .globallyAsymptoticallyStable) (Or.inl trivial) m).symm
    case globallyExponentiallyStable =>
      simpa [translate, Meets] using
        (hhur (P := .globallyExponentiallyStable) (Or.inl trivial) m).symm
    case contractive => simpa [translate, Meets] using (hhur (P := .contractive) (Or.inr rfl) m).symm
  · simp only [translate, Set.mem_singleton_iff, forall_eq, Meets, Sentence.holds_passive]
    constructor
    · intro hR
      exact ⟨_, (kyp m hR).passiveWith⟩
    · intro h
      by_contra hR
      exact m.plant.system.not_passive_of_equilibrium (field_hold m 1)
        (by rw [supply_hold]; linarith [not_le.mp hR]) h

end powerlib.Circuits.RL
