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
plant map sends the state-space parameters to `i' = -a i + b v`. Every behavioural sentence is the
Flow semantics pulled back along the plant map; this module proves only the RL facts: which
resistance condition carves out each sentence, the closed-form Lyapunov certificate, and the
physical energy as a KYP certificate. -/

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
@[simp, powerlib_domain] theorem isHurwitz_iff (m : Impedance) :
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

/-- A nonnegative resistance makes the zero-input RL branch Lyapunov stable. -/
@[powerlib_domain] theorem lyapunovStable_of_nonneg (m : Impedance) (hR : 0 ≤ m.resistance) :
    LyapunovStable (affineLinearVectorField m.plant.A 0) 0 := by
  apply (kyp m hR).lyapunovStable_of_pos
  intro x hx
  have h0 : x 0 ≠ 0 := by
    intro h
    apply hx
    funext i
    fin_cases i
    exact h
  simp [kyp, dotProduct, Matrix.mulVec]
  nlinarith [mul_pos m.inductance.property (mul_self_pos.mpr h0)]

/-- A negative resistance makes the RL branch unstable (LeanForControl's instability theorem). -/
@[powerlib_domain] theorem unstable_of_neg (m : Impedance) (hR : m.resistance < 0) :
    Unstable (affineLinearVectorField m.plant.A 0) 0 := by
  apply Linear.unstable_of_eigenvalue 0 (μ := ((-(toStateSpace m).decay : ℝ) : ℂ))
    (v := fun _ => 1) (by simp [funext_iff])
  · funext i
    fin_cases i
    simp [Impedance.plant, StateSpace.plant, Matrix.mulVec, dotProduct]
  · simp only [Complex.ofReal_re, toStateSpace_decay, neg_pos]
    exact div_neg_of_neg_of_pos hR m.inductance.property

/-! ## Responses -/

/-- Every current trajectory of the branch field centred at `e` is the exponential
`i(t) - e = e^{-(R/L)(t - t₀)} (i(t₀) - e)` on its whole segment, whatever the sign of `R`. -/
@[powerlib_domain] theorem trajectory_eq (m : Impedance) {e : EuclideanSpace ℝ (Fin 1)}
    {φ : ℝ → EuclideanSpace ℝ (Fin 1)} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ (affineLinearVectorField m.plant.A e) t₀ t₁) :
    ∀ t ∈ Set.Icc t₀ t₁,
      φ t = e + Real.exp (-(m.resistance / m.inductance.val) * (t - t₀)) • (φ t₀ - e) := by
  intro t ht
  have h : m.plant.A = !![-(toStateSpace m).decay] := rfl
  rw [h] at hφ
  rw [Linear.trajectory_eq_scalar hφ t ht, toStateSpace_decay]

/-- Under a constant terminal voltage with equilibrium current `e`, every trajectory relaxes to
`e` with time constant `L / R`. -/
@[powerlib_domain] theorem input_trajectory_eq (m : Impedance) {v : Fin 1 → ℝ}
    {e : EuclideanSpace ℝ (Fin 1)} (he : IsEquilibrium (m.plant.inputField v) e)
    {φ : ℝ → EuclideanSpace ℝ (Fin 1)} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ (m.plant.inputField v) t₀ t₁) :
    ∀ t ∈ Set.Icc t₀ t₁,
      φ t = e + Real.exp (-(m.resistance / m.inductance.val) * (t - t₀)) • (φ t₀ - e) := by
  rw [m.plant.inputField_eq he] at hφ
  exact trajectory_eq m hφ

/-- The distance to the equilibrium is exactly exponential. -/
@[powerlib_domain] theorem norm_trajectory_eq (m : Impedance) {e : EuclideanSpace ℝ (Fin 1)}
    {φ : ℝ → EuclideanSpace ℝ (Fin 1)} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ (affineLinearVectorField m.plant.A e) t₀ t₁) :
    ∀ t ∈ Set.Icc t₀ t₁,
      ‖φ t - e‖ = Real.exp (-(m.resistance / m.inductance.val) * (t - t₀)) * ‖φ t₀ - e‖ := by
  intro t ht
  rw [trajectory_eq m hφ t ht, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-! ## The frequency domain -/

/-- The transfer function from terminal voltage to branch current is the admittance
`1 / (R + L s)`, at every complex frequency (both sides vanish at the pole). -/
@[powerlib_domain] theorem transfer_eq (m : Impedance) (s : ℂ) :
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

/-- An impedance measurement certifies the branch: among all minimal one-state plants, the
branch's transfer function certifies every sentence the branch satisfies. -/
@[powerlib_domain] theorem transfer_certified (m : Impedance) {P : Flow.Property}
    (h : m ∈ Linear.den Impedance.plant P) :
    Linear.transfer m.plant ∈ TMIO.certify
      (Function.graph fun M : {M : Linear.Plant 1 1 // M.Minimal} => Linear.transfer M.1)
      {M | P.holds (affineLinearVectorField M.1.A 0) 0} :=
  Linear.transfer_certified (minimal m) h

/-! ## Requirements and their exact translations -/

/-- Engineering requirements on the RL parameters. -/
inductive Requirement
  | positiveResistance
  | nonnegativeResistance
  | negativeResistance
  | resistanceAtLeast (r : ℝ)
  | resistanceAtMost (r : ℝ)
  | inductanceAtLeast (l : ℝ)
  | inductanceAtMost (l : ℝ)

/-- Satisfaction of a requirement by a complete RL model. -/
def Meets (m : Impedance) : Requirement → Prop
  | .positiveResistance => 0 < m.resistance
  | .nonnegativeResistance => 0 ≤ m.resistance
  | .negativeResistance => m.resistance < 0
  | .resistanceAtLeast r => r ≤ m.resistance
  | .resistanceAtMost r => m.resistance ≤ r
  | .inductanceAtLeast l => l ≤ m.inductance.val
  | .inductanceAtMost l => m.inductance.val ≤ l

/-- The translation of the behavioural sentences into requirements. -/
def translate : Flow.Property → Set Requirement
  | .lyapunovStable => {.nonnegativeResistance}
  | .unstable => {.negativeResistance}
  | _ => {.positiveResistance}

/-- The RL family: the plant map, the requirement language and the translation table. -/
def family : Linear.Family Impedance Requirement 1 1 := ⟨Impedance.plant, Meets, translate⟩

@[powerlib_foundation] theorem realize_positiveResistance :
    realize Meets {Requirement.positiveResistance} = {m | IsHurwitz m.plant.A} := by
  ext m
  simp [Meets, isHurwitz_iff]

/-- Zero-input Lyapunov stability of the RL branch is exactly a nonnegative resistance. -/
@[simp, powerlib_domain] theorem lyapunovStable_iff (m : Impedance) :
    LyapunovStable (affineLinearVectorField m.plant.A 0) 0 ↔ 0 ≤ m.resistance := by
  refine ⟨fun h => ?_, lyapunovStable_of_nonneg m⟩
  by_contra hR
  exact unstable_of_neg m (not_le.mp hR) h

/-- Every behavioural sentence has an exact translation into RL requirements
(`family.Exact P`). -/
@[powerlib_domain] theorem realize_translate (P : Flow.Property) :
    realize Meets (translate P) = Linear.den Impedance.plant P := by
  cases P with
  | lyapunovStable =>
    ext m
    simp [translate, Meets, Linear.den, Flow.Property.holds, lyapunovStable_iff]
  | unstable =>
    ext m
    simp [translate, Meets, Linear.den, Flow.Property.holds, Unstable, lyapunovStable_iff]
  | locallyAsymptoticallyStable =>
    exact Linear.realize_eq_den realize_positiveResistance trivial
  | locallyExponentiallyStable =>
    exact Linear.realize_eq_den realize_positiveResistance trivial
  | globallyAsymptoticallyStable =>
    exact Linear.realize_eq_den realize_positiveResistance trivial
  | globallyExponentiallyStable =>
    exact Linear.realize_eq_den realize_positiveResistance trivial

/-- At every terminal voltage and every equilibrium current, an attractive sentence holds exactly
for a positive resistance. -/
@[powerlib_domain] theorem holds_input_iff (m : Impedance) {v : Fin 1 → ℝ}
    {e : EuclideanSpace ℝ (Fin 1)} (he : IsEquilibrium (m.plant.inputField v) e)
    {P : Flow.Property} (hP : P.Attractive) :
    P.holds (m.plant.inputField v) e ↔ 0 < m.resistance := by
  rw [Linear.holds_input_iff m.plant he hP, isHurwitz_iff]

end powerlib.Circuits.RL
