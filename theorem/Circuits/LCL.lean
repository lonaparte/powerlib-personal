import theorem.Circuits.RL
import theorem.generated.LCLConversion

/-! # The LCL filter

Model boundary: a converter-side series RL branch `(R₁, L₁)`, an ideal shunt capacitor `C`, and
a grid-side series RL branch `(R₂, L₂)`, in continuous time. States, in order: converter current
`i₁`, capacitor voltage `v_C`, grid current `i₂`, as stationary scalar phase variables (no dq
transformation). Ports: the converter terminal voltage `u` with port current `i₁`, and the grid
terminal voltage `v_g` with port current `-i₂`. Inductances and capacitance are positive;
resistances are real, of either sign, unless passivity is required. No controller, PLL, PWM,
sampling delay or further grid state.

The circuit parameters and the state-space parameters are related by the Agda-generated
conversion (the RL conversion on each branch, the reciprocal on the capacitance). The plant map
sends the state-space parameters to the three-state plant; behaviour is the hub's, pulled back. -/

noncomputable section

namespace powerlib.Circuits.LCL

open Matrix LinearSystems TMIO

/-- The circuit parameters. -/
@[ext] structure Circuit where
  first : RL.Impedance
  second : RL.Impedance
  capacitance : RL.Positive

/-- The state-space parameters. -/
@[ext] structure StateSpace where
  first : RL.StateSpace
  second : RL.StateSpace
  capacitorGain : RL.Positive

/-- The Agda-generated conversion from circuit to state-space parameters. -/
def toStateSpace (m : Circuit) : StateSpace :=
  let y := generated.convertLCL (fun a (b : RL.Positive) => a * b.val) RL.reciprocal
    (((m.first.resistance, m.first.inductance), (m.second.resistance, m.second.inductance)),
      m.capacitance)
  ⟨⟨y.1.1.1, y.1.1.2⟩, ⟨y.1.2.1, y.1.2.2⟩, y.2⟩

/-- The same generated conversion, back to circuit parameters. -/
def toCircuit (m : StateSpace) : Circuit :=
  let y := generated.convertLCL (fun a (b : RL.Positive) => a * b.val) RL.reciprocal
    (((m.first.decay, m.first.inputGain), (m.second.decay, m.second.inputGain)),
      m.capacitorGain)
  ⟨⟨y.1.1.1, y.1.1.2⟩, ⟨y.1.2.1, y.1.2.2⟩, y.2⟩

@[simp, powerlib_foundation] theorem circuit_roundtrip (m : Circuit) :
    toCircuit (toStateSpace m) = m := by
  apply Circuit.ext
  · exact RL.impedance_roundtrip m.first
  · exact RL.impedance_roundtrip m.second
  · exact RL.reciprocal_involutive m.capacitance

@[simp, powerlib_foundation] theorem state_roundtrip (m : StateSpace) :
    toStateSpace (toCircuit m) = m := by
  apply StateSpace.ext
  · exact RL.state_roundtrip m.first
  · exact RL.state_roundtrip m.second
  · exact RL.reciprocal_involutive m.capacitorGain

/-- The two representations are equivalent. -/
def modelEquiv : Circuit ≃ StateSpace where
  toFun := toStateSpace
  invFun := toCircuit
  left_inv := circuit_roundtrip
  right_inv := state_roundtrip

/-! ## The plant map -/

/-- The three-state, two-port plant. -/
def StateSpace.plant (m : StateSpace) : Linear.Plant 3 2 where
  A := !![-m.first.decay, -m.first.inputGain.val, 0;
          m.capacitorGain.val, 0, -m.capacitorGain.val;
          0, m.second.inputGain.val, -m.second.decay]
  B := !![m.first.inputGain.val, 0; 0, 0; 0, -m.second.inputGain.val]
  C := !![1, 0, 0; 0, 0, -1]
  D := 0

/-- The plant of the circuit representation, through the conversion. -/
def Circuit.plant (m : Circuit) : Linear.Plant 3 2 := (toStateSpace m).plant

@[simp, powerlib_foundation] theorem plant_toCircuit (m : StateSpace) :
    (toCircuit m).plant = m.plant := by
  simp [Circuit.plant]

/-! ## Poles -/

def Circuit.a3 (m : Circuit) : ℝ :=
  m.first.inductance.val * m.second.inductance.val * m.capacitance.val
def Circuit.a2 (m : Circuit) : ℝ :=
  m.capacitance.val * (m.first.resistance * m.second.inductance.val +
    m.second.resistance * m.first.inductance.val)
def Circuit.a1 (m : Circuit) : ℝ :=
  m.first.inductance.val + m.second.inductance.val +
    m.capacitance.val * m.first.resistance * m.second.resistance
def Circuit.a0 (m : Circuit) : ℝ := m.first.resistance + m.second.resistance

/-- The pole polynomial. -/
def Circuit.frequency (m : Circuit) (s : ℂ) : ℂ :=
  (m.a3 : ℂ) * s ^ 3 + (m.a2 : ℂ) * s ^ 2 + (m.a1 : ℂ) * s + (m.a0 : ℂ)

/-- All poles in the open left half plane. -/
def Circuit.Stable (m : Circuit) : Prop := ∀ s : ℂ, m.frequency s = 0 → s.re < 0

@[powerlib_foundation] theorem a3_pos (m : Circuit) : 0 < m.a3 :=
  mul_pos (mul_pos m.first.inductance.property m.second.inductance.property)
    m.capacitance.property

/-- The characteristic polynomial of the plant is the pole polynomial over `a₃`. -/
@[powerlib_foundation] theorem det_characteristicMatrix (m : Circuit) (s : ℂ) :
    (Linear.characteristicMatrix m.plant.A s).det = m.frequency s / (m.a3 : ℂ) := by
  have hL1 : (m.first.inductance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.first.inductance.property
  have hL2 : (m.second.inductance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.second.inductance.property
  have hC : (m.capacitance.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt m.capacitance.property
  simp [Linear.characteristicMatrix, Circuit.plant, StateSpace.plant, Matrix.det_fin_three,
    toStateSpace, generated.convertLCL, RL.reciprocal, Circuit.frequency,
    Circuit.a3, Circuit.a2, Circuit.a1, Circuit.a0]
  field_simp
  ring

/-- The plant is Hurwitz exactly when all poles lie in the open left half plane. -/
@[powerlib_domain] theorem isHurwitz_iff_stable (m : Circuit) :
    IsHurwitz m.plant.A ↔ m.Stable := by
  rw [← Linear.spectrallyStable_iff_isHurwitz]
  have ha3 : (m.a3 : ℂ) ≠ 0 := by exact_mod_cast (a3_pos m).ne'
  simp only [Linear.SpectrallyStable, Circuit.Stable, det_characteristicMatrix, div_eq_zero_iff,
    ha3, or_false]

/-! ## Routh–Hurwitz and passivity -/

/-- Both resistances nonnegative. -/
def Circuit.Passive (m : Circuit) : Prop := 0 ≤ m.first.resistance ∧ 0 ≤ m.second.resistance

/-- Some resistance nonzero. -/
def Circuit.Damped (m : Circuit) : Prop := m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0

@[powerlib_foundation] theorem hurwitz_gap (m : Circuit) : m.a2 * m.a1 - m.a3 * m.a0 =
    m.capacitance.val * (m.first.resistance * m.second.inductance.val ^ 2 +
      m.second.resistance * m.first.inductance.val ^ 2 +
      m.capacitance.val * m.first.resistance * m.second.resistance *
        (m.first.resistance * m.second.inductance.val +
          m.second.resistance * m.first.inductance.val)) := by
  dsimp [Circuit.a3, Circuit.a2, Circuit.a1, Circuit.a0]
  ring

/-- The strict cubic Routh–Hurwitz condition places every root in the open left half plane. -/
@[powerlib_foundation] theorem cubic_hurwitz (a3 a2 a1 a0 : ℝ) (h3 : 0 < a3) (h2 : 0 < a2)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : 0 < a2 * a1 - a3 * a0)
    (s : ℂ) (hs : (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.re < 0 := by
  by_contra hn
  have hx : 0 ≤ s.re := le_of_not_gt hn
  have hr : a3 * (s.re ^ 3 - 3 * s.re * s.im ^ 2) + a2 * (s.re ^ 2 - s.im ^ 2) + a1 * s.re +
      a0 = 0 := by
    have h := congrArg Complex.re hs
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at h
    nlinarith [h]
  have hi : s.im * (a3 * (3 * s.re ^ 2 - s.im ^ 2) + 2 * a2 * s.re + a1) = 0 := by
    have h := congrArg Complex.im hs
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at h
    nlinarith [h]
  by_cases hy : s.im = 0
  · have hp : 0 < a3 * s.re ^ 3 + a2 * s.re ^ 2 + a1 * s.re + a0 := by positivity
    simp only [hy] at hr
    linarith
  · have hf : a3 * (3 * s.re ^ 2 - s.im ^ 2) + 2 * a2 * s.re + a1 = 0 :=
      (mul_eq_zero.mp hi).resolve_left hy
    have hz : 8 * a3 ^ 2 * s.re ^ 3 + 8 * a3 * a2 * s.re ^ 2 +
        2 * (a3 * a1 + a2 ^ 2) * s.re + (a2 * a1 - a3 * a0) = 0 := by
      linear_combination -a3 * hr + (3 * a3 * s.re + a2) * hf
    have hp : 0 < 8 * a3 ^ 2 * s.re ^ 3 + 8 * a3 * a2 * s.re ^ 2 +
        2 * (a3 * a1 + a2 ^ 2) * s.re + (a2 * a1 - a3 * a0) := by positivity
    linarith

/-- The Routh–Hurwitz coefficient condition. -/
def Circuit.RouthHurwitz (m : Circuit) : Prop :=
  0 < m.a2 ∧ 0 < m.a1 ∧ 0 < m.a0 ∧ 0 < m.a2 * m.a1 - m.a3 * m.a0

@[powerlib_foundation] theorem stable_of_routhHurwitz (m : Circuit) (h : m.RouthHurwitz) :
    m.Stable :=
  fun s hs => cubic_hurwitz m.a3 m.a2 m.a1 m.a0 (a3_pos m) h.1 h.2.1 h.2.2.1 h.2.2.2 s hs

@[powerlib_foundation] theorem routhHurwitz_of_passive (m : Circuit) (hp : m.Passive)
    (hd : m.Damped) : m.RouthHurwitz := by
  rcases hp with ⟨hr1, hr2⟩
  have hL1 := m.first.inductance.property
  have hL2 := m.second.inductance.property
  have hC := m.capacitance.property
  have hpos : 0 < m.first.resistance ∨ 0 < m.second.resistance := by
    rcases hd with h | h
    · exact Or.inl (lt_of_le_of_ne hr1 (Ne.symm h))
    · exact Or.inr (lt_of_le_of_ne hr2 (Ne.symm h))
  have h0 : 0 < m.a0 := by dsimp [Circuit.a0]; rcases hpos with h | h <;> linarith
  have h1 : 0 < m.a1 := by dsimp [Circuit.a1]; positivity
  have h2 : 0 < m.a2 := by
    dsimp [Circuit.a2]
    rcases hpos with h | h <;> positivity
  have hg : 0 < m.a2 * m.a1 - m.a3 * m.a0 := by
    rw [hurwitz_gap]
    rcases hpos with h | h <;> positivity
  exact ⟨h2, h1, h0, hg⟩

/-- With passive resistances, pole stability is exactly damping. -/
@[powerlib_domain] theorem passive_stable_iff (m : Circuit) (hp : m.Passive) :
    m.Stable ↔ m.Damped := by
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
    exact stable_of_routhHurwitz m (routhHurwitz_of_passive m hp hd)

/-! ## Behaviour -/

@[simp, powerlib_foundation] theorem toStateSpace_first (m : Circuit) :
    (toStateSpace m).first = RL.toStateSpace m.first := rfl

@[simp, powerlib_foundation] theorem toStateSpace_second (m : Circuit) :
    (toStateSpace m).second = RL.toStateSpace m.second := rfl

@[simp, powerlib_foundation] theorem toStateSpace_capacitorGain (m : Circuit) :
    (toStateSpace m).capacitorGain.val = (m.capacitance.val)⁻¹ := rfl

/-- At every pair of terminal voltages and every equilibrium, an attractive sentence holds
exactly when all poles lie in the open left half plane. -/
@[powerlib_domain] theorem holds_input_iff (m : Circuit) {u : Fin 2 → ℝ}
    {e : EuclideanSpace ℝ (Fin 3)} (he : IsEquilibrium (m.plant.inputField u) e)
    {P : Flow.Property} (hP : P.Attractive) :
    P.holds (m.plant.inputField u) e ↔ m.Stable := by
  rw [Linear.holds_input_iff m.plant he hP, isHurwitz_iff_stable]

/-- A pole in the open right half plane makes the circuit unstable (LeanForControl). -/
@[powerlib_domain] theorem unstable_of_pole (m : Circuit) {s : ℂ} (hs : m.frequency s = 0)
    (hre : 0 < s.re) : Unstable (affineLinearVectorField m.plant.A 0) 0 := by
  refine Linear.unstable_of_root 0 ?_ hre
  rw [det_characteristicMatrix, hs, zero_div]

/-- The physical energy matrix `diag(L₁, C, L₂)`. -/
def energyMatrix (m : Circuit) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![m.first.inductance.val, 0, 0; 0, m.capacitance.val, 0; 0, 0, m.second.inductance.val]

@[powerlib_foundation] theorem energy_identity (m : Circuit) :
    m.plant.Aᵀ * energyMatrix m + energyMatrix m * m.plant.A =
      !![-2 * m.first.resistance, 0, 0; 0, 0, 0; 0, 0, -2 * m.second.resistance] := by
  have hL1 := m.first.inductance.property.ne'
  have hL2 := m.second.inductance.property.ne'
  have hC := m.capacitance.property.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Circuit.plant, StateSpace.plant, energyMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- The physical energy is a KYP certificate for a passive circuit. -/
def kyp (m : Circuit) (hp : m.Passive) : Linear.KYP m.plant where
  P := energyMatrix m
  symmetric := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  nonneg x := by
    have hL1 := m.first.inductance.property
    have hL2 := m.second.inductance.property
    have hC := m.capacitance.property
    simp [energyMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    nlinarith [mul_nonneg hL1.le (mul_self_nonneg (x 0)), mul_nonneg hC.le (mul_self_nonneg (x 1)),
      mul_nonneg hL2.le (mul_self_nonneg (x 2))]
  dissipation x := by
    rw [energy_identity]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    nlinarith [mul_nonneg hp.1 (mul_self_nonneg (x 0)), mul_nonneg hp.2 (mul_self_nonneg (x 2))]
  output := by
    have hL1 := m.first.inductance.property.ne'
    have hL2 := m.second.inductance.property.ne'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Circuit.plant, StateSpace.plant, energyMatrix, Matrix.mul_apply, Fin.sum_univ_three,
        inv_mul_cancel₀ hL1, inv_mul_cancel₀ hL2]
  feedthrough u := by simp [Circuit.plant, StateSpace.plant]

@[powerlib_foundation] theorem energy_pos (m : Circuit) (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (energyMatrix m *ᵥ x) := by
  have hL1 := m.first.inductance.property
  have hL2 := m.second.inductance.property
  have hC := m.capacitance.property
  have hsome : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  simp [energyMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  rcases hsome with h | h | h
  · nlinarith [mul_pos hL1 (mul_self_pos.mpr h), mul_nonneg hC.le (mul_self_nonneg (x 1)),
      mul_nonneg hL2.le (mul_self_nonneg (x 2))]
  · nlinarith [mul_pos hC (mul_self_pos.mpr h), mul_nonneg hL1.le (mul_self_nonneg (x 0)),
      mul_nonneg hL2.le (mul_self_nonneg (x 2))]
  · nlinarith [mul_pos hL2 (mul_self_pos.mpr h), mul_nonneg hL1.le (mul_self_nonneg (x 0)),
      mul_nonneg hC.le (mul_self_nonneg (x 1))]

/-- A passive circuit is Lyapunov stable with its ports held at zero. -/
@[powerlib_domain] theorem lyapunovStable_of_passive (m : Circuit) (hp : m.Passive) :
    LyapunovStable (affineLinearVectorField m.plant.A 0) 0 :=
  (kyp m hp).lyapunovStable_of_pos (energy_pos m)

/-- A lossless circuit is Lyapunov stable but satisfies no attractive sentence. -/
@[powerlib_domain] theorem lossless (m : Circuit) (h1 : m.first.resistance = 0)
    (h2 : m.second.resistance = 0) {P : Flow.Property} (hP : P.Attractive) :
    LyapunovStable (affineLinearVectorField m.plant.A 0) 0 ∧
      ¬ P.holds (affineLinearVectorField m.plant.A 0) 0 := by
  have hp : m.Passive := ⟨h1.ge, h2.ge⟩
  refine ⟨lyapunovStable_of_passive m hp, fun h => ?_⟩
  have hs := (isHurwitz_iff_stable m).mp ((Linear.holds_iff_isHurwitz 0 hP).mp h)
  have hd := (passive_stable_iff m hp).mp hs
  rcases hd with h | h
  · exact h h1
  · exact h h2

/-- A lossless circuit conserves its physical energy `(L₁ i₁² + C v² + L₂ i₂²) / 2` along every
zero-input solution segment. -/
@[powerlib_domain] theorem lossless_energy_conserved (m : Circuit) (h1 : m.first.resistance = 0)
    (h2 : m.second.resistance = 0) {x : ℝ → EuclideanSpace ℝ (Fin 3)} {t₀ t₁ : ℝ}
    (hx : IsTrajectoryOn x (affineLinearVectorField m.plant.A 0) t₀ t₁) :
    ∀ t ∈ Set.Icc t₀ t₁,
      (kyp m ⟨h1.ge, h2.ge⟩).storage (x t) = (kyp m ⟨h1.ge, h2.ge⟩).storage (x t₀) := by
  have hl : m.plant.Aᵀ * energyMatrix m + energyMatrix m * m.plant.A = 0 := by
    rw [energy_identity, h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact (kyp m ⟨h1.ge, h2.ge⟩).storage_conserved hl hx

/-! ## Requirements and translations -/

/-- Engineering requirements on the LCL parameters. -/
inductive Requirement
  | poleStable
  | routhHurwitz
  | passive
  | damped
  | rightHalfPlanePole

/-- Satisfaction of a requirement by a complete LCL circuit. -/
def Meets (m : Circuit) : Requirement → Prop
  | .poleStable => m.Stable
  | .routhHurwitz => m.RouthHurwitz
  | .passive => m.Passive
  | .damped => m.Damped
  | .rightHalfPlanePole => ∃ s : ℂ, m.frequency s = 0 ∧ 0 < s.re

/-- The translation of the behavioural sentences into requirements. -/
def translate : Flow.Property → Set Requirement
  | .lyapunovStable => {.passive}
  | .unstable => {.rightHalfPlanePole}
  | _ => {.poleStable}

/-- The LCL family: the plant map, the requirement language and the translation table. -/
def family : Linear.Family Circuit Requirement 3 2 := ⟨Circuit.plant, Meets, translate⟩

@[powerlib_foundation] theorem realize_poleStable :
    realize Meets {Requirement.poleStable} = {m | IsHurwitz m.plant.A} := by
  ext m
  simp [Meets, isHurwitz_iff_stable]

/-- Pole stability is an exact translation of every attractive sentence, for every circuit. -/
@[powerlib_domain] theorem realize_translate_attractive {P : Flow.Property} (hP : P.Attractive) :
    realize Meets (translate P) = Linear.den Circuit.plant P := by
  have h : translate P = {Requirement.poleStable} := by
    cases P <;> first | rfl | exact absurd hP id
  rw [h]
  exact Linear.realize_eq_den realize_poleStable hP

/-- The Routh–Hurwitz condition is a sound translation of every attractive sentence. -/
@[powerlib_domain] theorem realize_routhHurwitz_subset {P : Flow.Property} (hP : P.Attractive) :
    realize Meets {Requirement.routhHurwitz} ⊆ Linear.den Circuit.plant P := by
  intro m hm
  rw [Linear.den_attractive _ hP]
  exact (isHurwitz_iff_stable m).mpr (stable_of_routhHurwitz m (by simpa [Meets] using hm))

/-- Damping is an exact translation of every attractive sentence relative to passivity. -/
@[powerlib_domain] theorem exactUnder_damped {P : Flow.Property} (hP : P.Attractive) :
    ExactUnder Meets {Requirement.passive} {Requirement.damped} (Linear.den Circuit.plant P) := by
  apply Linear.exactUnder_den _ hP
  ext m
  simp only [mem_realize, Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff,
    Set.mem_ofPred_eq, forall_eq_or_imp, forall_eq, Meets, isHurwitz_iff_stable]
  constructor
  · rintro ⟨hd, hp⟩
    exact ⟨(passive_stable_iff m hp).mpr hd, hp⟩
  · rintro ⟨hs, hp⟩
    exact ⟨(passive_stable_iff m hp).mp hs, hp⟩

/-- Passivity is a sound translation of Lyapunov stability. -/
@[powerlib_domain] theorem realize_passive_subset :
    realize Meets (translate .lyapunovStable) ⊆ Linear.den Circuit.plant .lyapunovStable := by
  intro m hm
  exact lyapunovStable_of_passive m (by simpa [translate, Meets] using hm)

/-- A right-half-plane pole is a sound translation of instability. -/
@[powerlib_domain] theorem realize_pole_subset :
    realize Meets (translate .unstable) ⊆ Linear.den Circuit.plant .unstable := by
  intro m hm
  obtain ⟨s, hs, hre⟩ : ∃ s : ℂ, m.frequency s = 0 ∧ 0 < s.re := by
    simpa [translate, Meets] using hm
  exact unstable_of_pole m hs hre

/-- Every behavioural sentence has a sound translation into LCL requirements: exact for the
attractive sentences, passivity for Lyapunov stability, a right-half-plane pole for
instability. -/
@[powerlib_domain] theorem sound (P : Flow.Property) : family.Sound P := by
  by_cases hP : P.Attractive
  · exact (realize_translate_attractive hP).le
  · cases P with
    | lyapunovStable => exact realize_passive_subset
    | unstable => exact realize_pole_subset
    | _ => exact absurd trivial hP

end powerlib.Circuits.LCL
