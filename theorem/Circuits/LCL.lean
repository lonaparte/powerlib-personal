import theorem.TMIO.ClaimElab
import theorem.Linear.Jordan
import theorem.Linear.Rate
import theorem.Circuits.RL
import theorem.Criteria.Routh3
import theorem.generated.LCLConversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The LCL filter

The circuit parameters and the state-space parameters are related by the Agda-generated
conversion (the RL conversion on each branch, the reciprocal on the capacitance). The family reads
every circuit as the port system of its three-state plant.

Model boundary.
* A converter-side series RL branch `(R₁, L₁)`, an ideal shunt capacitor `C`, and a grid-side
  series RL branch `(R₂, L₂)`, in continuous time.
* States, in order: converter current `i₁`, capacitor voltage `v_C`, grid current `i₂`, as
  stationary scalar phase variables (no dq transformation). Ports: the converter terminal voltage
  `u` with port current `i₁`, and the grid terminal voltage `v_g` with port current `-i₂`.
* Inductances and capacitance are positive; resistances are real, of either sign, unless
  passivity is required.
* No controller, PLL, PWM, sampling delay or further grid state.

Source: scaffold `theorem/LCLConversion.agda` (circuit parameters ↔ state-space parameters), its
generated conversion `theorem/generated/LCLConversion.lean`; the RL branch
(`theorem/Circuits/RL.lean`); the linear family laws (`theorem/Linear/Family.lean`), rate margins
(`theorem/Linear/Rate.lean`) and zero Jordan chains (`theorem/Linear/Jordan.lean`); the cubic
Routh–Hurwitz criterion.

Results.
* Representations: `Circuit`, `StateSpace`, `toStateSpace`, `toCircuit`, `circuit_roundtrip`,
  `state_roundtrip`, `modelEquiv`, `StateSpace.plant`, `Circuit.plant`, `plant_toCircuit`.
* Poles: the coefficients `Circuit.a3`, `Circuit.a2`, `Circuit.a1`, `Circuit.a0`, the pole
  polynomial `Circuit.frequency`, `Circuit.Stable`, `a3_pos`, `det_characteristicMatrix`,
  `isHurwitz_iff_stable`.
* Routh–Hurwitz and passivity: `Circuit.Passive`, `Circuit.Damped`, `hurwitz_gap`,
  `Circuit.RouthHurwitz`, `stable_of_routhHurwitz` (from the cubic criterion
  `Criteria.cubic_hurwitz`, `theorem/Criteria/Routh3.lean`), `routhHurwitz_of_passive`,
  `passive_stable_iff` (with passive resistances, pole stability is exactly damping).
* Energy: `toStateSpace_first`, `toStateSpace_second`, `toStateSpace_capacitorGain`,
  `energyMatrix` (`diag(L₁, C, L₂)`), `energy_identity`, `kyp` (a KYP certificate for a passive
  circuit), `energy_pos`, `energy_lossless`, `energyMatrix_symmetric`.
* Static evidence: `family_isLinear`, `not_stable_of_conservative`,
  `hasDerivAt_three`, `integral_cycle`; the circuits `negativeCircuit`, `balancedCircuit`,
  `balancedEnergy`, `jordanCircuit` with `negativeCircuit_routhHurwitz`,
  `balancedEnergy_conserved`, `balancedEnergy_pos`, `jordanCircuit_frequency`.

Family and connection conclusions.
* `Circuits.LCL.family : Family Circuit Requirement 3 2`: requirements `poleStable`,
  `routhHurwitz`, `passive`, `damped`, `lossless`, `rightHalfPlanePole` and `rate a`. Lyapunov
  stability and passivity translate into `passive`, the attractive sentences and sampled
  contraction into `poleStable`, instability into `rightHalfPlanePole`, decay at `a` into
  `rate a` (a strict margin on the state matrix), conservation into `lossless`.
* `realize_univ`: no circuit has all poles in the open left half plane and one in the open right
  half plane; the whole requirement language is inconsistent.
* Its translation chain lies below its semantics connection everywhere (`chain_le_semantics`)
  and agrees with it on the attractive sentences and sampled contraction, whose translation is
  pole stability (`exact_hurwitz`), and on passivity, whose translation is the passivity of both
  resistances (`exact_passive`: a negative resistance is exposed by a closed cycle along which the
  ports deliver net energy). Within passive circuits, conservation is exactly losslessness
  (`exactUnder_conservative`); the requirement equivalences of Routh and Hurwitz are evaluations
  of the satisfaction connection (`realize_routhHurwitz`, `realize_passive_damped`).
* Two circuits mark where the connections part: a Hurwitz circuit with a negative resistance is
  Lyapunov stable but not passive, and a circuit with opposite resistances conserves an energy
  without being lossless (`not_exact_lyapunovStable`, `not_exact_conservative`). The
  right-half-plane pole translation misses polynomial growth at a zero Jordan block
  (`not_exact_unstable`, the circuit `jordanCircuit`).
-/

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

@[tmio M, simp, powerlib_foundation] theorem circuit_roundtrip (m : Circuit) :
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
@[simp, powerlib_foundation] theorem isHurwitz_iff_stable (m : Circuit) :
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

/-- The Routh–Hurwitz coefficient condition. -/
def Circuit.RouthHurwitz (m : Circuit) : Prop :=
  0 < m.a2 ∧ 0 < m.a1 ∧ 0 < m.a0 ∧ 0 < m.a2 * m.a1 - m.a3 * m.a0

@[powerlib_foundation, aesop unsafe 70% apply]
theorem stable_of_routhHurwitz (m : Circuit) (h : m.RouthHurwitz) :
    m.Stable :=
  fun s hs => Criteria.cubic_hurwitz m.a3 m.a2 m.a1 m.a0 (a3_pos m) h.1 h.2.1 h.2.2.1 h.2.2.2 s
    hs

@[powerlib_foundation, aesop unsafe 70% apply]
theorem routhHurwitz_of_passive (m : Circuit) (hp : m.Passive)
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
@[powerlib_foundation] theorem passive_stable_iff (m : Circuit) (hp : m.Passive) :
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

/-- With both resistances zero the plant conserves the physical energy. -/
@[powerlib_foundation] theorem energy_lossless (m : Circuit) (h1 : m.first.resistance = 0)
    (h2 : m.second.resistance = 0) :
    m.plant.Aᵀ * energyMatrix m + energyMatrix m * m.plant.A = 0 := by
  rw [energy_identity, h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[powerlib_foundation] theorem energyMatrix_symmetric (m : Circuit) :
    (energyMatrix m)ᵀ = energyMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Requirements and the family -/

/-- Engineering requirements on the LCL parameters. -/
inductive Requirement
  | poleStable
  | routhHurwitz
  | passive
  | damped
  | lossless
  | rightHalfPlanePole
  | rate (a : ℝ)

/-- Satisfaction of a requirement by a complete LCL circuit. -/
def Meets (m : Circuit) : Requirement → Prop
  | .poleStable => m.Stable
  | .routhHurwitz => m.RouthHurwitz
  | .passive => m.Passive
  | .damped => m.Damped
  | .lossless => m.first.resistance = 0 ∧ m.second.resistance = 0
  | .rate a => Linear.RateMargin m.plant.A a
  | .rightHalfPlanePole => ∃ s : ℂ, m.frequency s = 0 ∧ 0 < s.re

/-- The translation of the sentences into static requirements. A strict margin on the state
matrix is the sound rate requirement; equality at the spectral boundary is not claimed exact. -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable => {.passive}
  | .flow .unstable => {.rightHalfPlanePole}
  | .flow (.decay a) => {.rate a}
  | .flow .conservative => {.lossless}
  | .flow _ => {.poleStable}
  | .passive => {.passive}
  | .envelope _ => ∅

/-- The LCL family: every circuit read as the port system of its plant, the requirement language
and the translation table. -/
def family : Family Circuit Requirement 3 2 := ⟨fun m => m.plant.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear Circuit.plant := fun _ => rfl

/-- No circuit has both all poles in the open left half plane and one in the open right half
plane: the whole requirement language is inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨s, hs, hre⟩ := h .rightHalfPlanePole
  exact absurd (h .poleStable s hs) (not_lt.mpr hre.le)

/-- A conserving circuit is not pole-stable: every solution of a Hurwitz plant converges. -/
@[powerlib_foundation] theorem not_stable_of_conservative {m : Circuit}
    (h : m ∈ family.den (.flow .conservative)) : ¬ m.Stable := by
  rw [← isHurwitz_iff_stable]
  exact family_isLinear.not_isHurwitz_of_mem_den_conservative (by norm_num) h

/-! ## Faithfulness -/

/-- Every translation of the LCL family is sound: the translation chain lies below the semantics
connection. Pole stability proves the attractive sentences and sampled contraction, passivity
proves Lyapunov stability and passivity through the physical energy, losslessness proves
conservation of that energy, and a right-half-plane pole proves instability. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  rcases s with P | _ | E
  · cases P
    case lyapunovStable =>
      have hp : m.Passive := hm .passive rfl
      exact family_isLinear.mem_den_flow.mpr
        ((kyp m hp).lyapunovStable_of_pos (energy_pos m))
    case unstable =>
      obtain ⟨s, hs, hre⟩ := hm .rightHalfPlanePole rfl
      refine family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 ?_ hre)
      rw [det_characteristicMatrix, hs, zero_div]
    case decay a =>
      exact family_isLinear.mem_den_decay_of_rateMargin (hm (.rate a) rfl)
    case conservative =>
      obtain ⟨h1, h2⟩ := hm .lossless rfl
      exact family_isLinear.mem_den_conservative (energyMatrix_symmetric m) (energy_pos m)
        (energy_lossless m h1 h2)
    all_goals
      rw [family_isLinear.den_hurwitz (by simp), Set.mem_ofPred_eq, isHurwitz_iff_stable]
      exact hm .poleStable rfl
  · exact family_isLinear.mem_den_passive (kyp m (hm .passive rfl))
  · rw [family_isLinear.den_envelope]
    trivial

/-- On the attractive sentences and sampled contraction the chain agrees with the semantics: pole
stability is their exact translation, for every circuit, passive or not. -/
@[tmio TM, powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have ht : translate (.flow P) = {.poleStable} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact absurd hP id
    · rfl
  unfold Family.Exact
  change realize Meets (translate (.flow P)) = _
  rw [ht, family_isLinear.den_hurwitz hP]
  ext m
  simp [Meets, isHurwitz_iff_stable]

/-- Within passive circuits, conservation is exactly losslessness: a damped passive circuit is
pole-stable, so its solutions converge. -/
@[tmio TM, powerlib_domain] theorem exactUnder_conservative :
    connection% (family.ExactUnder {.passive} (.flow .conservative)) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [mem_realize, Set.mem_union, Set.mem_inter_iff]
  constructor
  · intro h
    have hm : m ∈ realize Meets (translate (.flow .conservative)) :=
      (mem_realize _ _ _).mpr fun q hq => h q (Or.inl hq)
    refine ⟨Family.chain_le_semantics_iff.mp chain_le_semantics _ hm, fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hc, hp⟩ q hq
    have hpass : m.Passive := hp .passive rfl
    rcases hq with hq | hq
    · have hq' : q = .lossless := hq
      subst hq'
      have hnd : ¬ m.Damped := fun hd => not_stable_of_conservative hc
        ((passive_stable_iff m hpass).mpr hd)
      show m.first.resistance = 0 ∧ m.second.resistance = 0
      simpa [Circuit.Damped] using hnd
    · exact hp q hq

/-! ## Passivity -/

/-- A curve in three states from its components. -/
@[powerlib_foundation] theorem hasDerivAt_three {f₀ f₁ f₂ : ℝ → ℝ} {d₀ d₁ d₂ t : ℝ}
    (h₀ : HasDerivAt f₀ d₀ t) (h₁ : HasDerivAt f₁ d₁ t) (h₂ : HasDerivAt f₂ d₂ t) :
    HasDerivAt (fun t => WithLp.toLp 2 ![f₀ t, f₁ t, f₂ t] : ℝ → EuclideanSpace ℝ (Fin 3))
      (WithLp.toLp 2 ![d₀, d₁, d₂]) t := by
  have hpi : HasDerivAt (fun t => ![f₀ t, f₁ t, f₂ t]) ![d₀, d₁, d₂] t := by
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa using h₀
    · simpa using h₁
    · simpa using h₂
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t
    hpi

/-- Over one period the power `r c² cos² t + q sin t cos t` delivers the energy `r c² π`. -/
@[powerlib_foundation] theorem integral_cycle (r c q : ℝ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), (r * c ^ 2 * Real.cos t ^ 2 + q * (Real.sin t * Real.cos t)) =
      r * c ^ 2 * Real.pi := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_mul_cos₁]
  · simp
  · exact (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  · exact
      (continuous_const.mul (Real.continuous_sin.mul Real.continuous_cos)).intervalIntegrable _ _

/-- Passivity of the port behaviour is exactly the passivity of both resistances. A passive
circuit stores its physical energy; with a negative resistance in one branch, the other branch
idle and the capacitor exchanging energy with the active branch over one period, the state returns
to its start while the ports deliver the net energy `-R C² π`. -/
@[tmio TM, powerlib_domain] theorem exact_passive :
    connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [Family.mem_den, mem_realize]
  change (∀ q ∈ translate .passive, Meets m q) ↔ m.plant.system.Passive
  simp only [translate, Set.mem_singleton_iff, forall_eq, Meets]
  refine ⟨fun hp => ⟨_, (kyp m hp).passiveWith⟩, fun h => ?_⟩
  have hL₁ : (m.first.inductance.val : ℝ) ≠ 0 := m.first.inductance.property.ne'
  have hL₂ : (m.second.inductance.val : ℝ) ≠ 0 := m.second.inductance.property.ne'
  have hC : (m.capacitance.val : ℝ) ≠ 0 := m.capacitance.property.ne'
  have hcycle : ∀ (u : ℝ → Fin 2 → ℝ) (x : ℝ → EuclideanSpace ℝ (Fin 3)) (r q : ℝ), r < 0 →
      m.plant.system.IsTrajectoryOn u x 0 (2 * Real.pi) → x (2 * Real.pi) = x 0 →
      (∀ t, m.plant.system.supply (x t) (u t) = r * m.capacitance.val ^ 2 * Real.cos t ^ 2 +
        q * (Real.sin t * Real.cos t)) → False := by
    intro u x r q hr hx hclose hsupply
    refine m.plant.system.not_passive_of_cycle (by positivity) hx hclose ?_ ?_ h
    · refine (Continuous.intervalIntegrable ?_ _ _)
      simp only [hsupply]
      fun_prop
    · simp only [hsupply, integral_cycle]
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hr (by positivity)) Real.pi_pos
  by_contra hp
  simp only [Circuit.Passive, not_and_or, not_le] at hp
  rcases hp with h₁ | h₂
  · -- Converter current `C cos t`, capacitor voltage `sin t`, no grid current.
    let x : ℝ → EuclideanSpace ℝ (Fin 3) := fun t =>
      WithLp.toLp 2 ![m.capacitance.val * Real.cos t, Real.sin t, 0]
    let u : ℝ → Fin 2 → ℝ := fun t =>
      ![m.first.inductance.val * -(m.capacitance.val * Real.sin t) +
        m.first.resistance * (m.capacitance.val * Real.cos t) + Real.sin t, Real.sin t]
    have hfield : ∀ t, m.plant.system.field (x t) (u t) =
        WithLp.toLp 2 ![m.capacitance.val * -Real.sin t, Real.cos t, 0] := by
      intro t
      ext i
      fin_cases i <;>
        simp [x, u, Circuit.plant, StateSpace.plant, Linear.Plant.system, dotProduct,
          Fin.sum_univ_three, Fin.sum_univ_two, RL.toStateSpace_decay] <;>
        field_simp <;> ring
    refine hcycle u x m.first.resistance
      (m.capacitance.val - m.first.inductance.val * m.capacitance.val ^ 2) h₁ (fun t _ => ?_)
      (by simp [x]) fun t => ?_
    · change HasDerivWithinAt x (m.plant.system.field (x t) (u t)) _ t
      rw [hfield]
      exact (hasDerivAt_three ((Real.hasDerivAt_cos t).const_mul m.capacitance.val)
        (Real.hasDerivAt_sin t) (hasDerivAt_const t 0)).hasDerivWithinAt
    · simp [Port.System.supply, x, u, Circuit.plant, StateSpace.plant, Linear.Plant.system,
        dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
      ring
  · -- Grid current `C cos t`, capacitor voltage `-sin t`, no converter current.
    let x : ℝ → EuclideanSpace ℝ (Fin 3) := fun t =>
      WithLp.toLp 2 ![0, -Real.sin t, m.capacitance.val * Real.cos t]
    let u : ℝ → Fin 2 → ℝ := fun t =>
      ![-Real.sin t, -Real.sin t - m.second.resistance * (m.capacitance.val * Real.cos t) +
        m.second.inductance.val * (m.capacitance.val * Real.sin t)]
    have hfield : ∀ t, m.plant.system.field (x t) (u t) =
        WithLp.toLp 2 ![0, -Real.cos t, m.capacitance.val * -Real.sin t] := by
      intro t
      ext i
      fin_cases i <;>
        simp [x, u, Circuit.plant, StateSpace.plant, Linear.Plant.system, dotProduct,
          Fin.sum_univ_three, Fin.sum_univ_two, RL.toStateSpace_decay] <;>
        field_simp <;> ring
    refine hcycle u x m.second.resistance
      (m.capacitance.val - m.second.inductance.val * m.capacitance.val ^ 2) h₂ (fun t _ => ?_)
      (by simp [x]) fun t => ?_
    · change HasDerivWithinAt x (m.plant.system.field (x t) (u t)) _ t
      rw [hfield]
      exact (hasDerivAt_three (hasDerivAt_const t 0) (Real.hasDerivAt_sin t).neg
        ((Real.hasDerivAt_cos t).const_mul m.capacitance.val)).hasDerivWithinAt
    · simp [Port.System.supply, x, u, Circuit.plant, StateSpace.plant, Linear.Plant.system,
        dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
      ring

/-! ## Requirement equivalences -/

/-- The Routh–Hurwitz condition entails pole stability. -/
@[tmio M, powerlib_domain] theorem realize_routhHurwitz :
    connection% (realize Meets {.routhHurwitz} ⊆ realize Meets {.poleStable}) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  simp only [mem_realize, Set.mem_singleton_iff, forall_eq, Meets] at hm ⊢
  exact stable_of_routhHurwitz m hm

/-- Within passive circuits, pole stability is exactly damping. -/
@[tmio M, powerlib_domain] theorem realize_passive_damped :
    connection% (realize Meets {.passive, .damped} = realize Meets {.passive, .poleStable}) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [mem_realize, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    Meets]
  exact ⟨fun ⟨hp, hd⟩ => ⟨hp, (passive_stable_iff m hp).mpr hd⟩,
    fun ⟨hp, hs⟩ => ⟨hp, (passive_stable_iff m hp).mp hs⟩⟩

/-! ## Where the connections part -/

/-- A circuit with a negative converter-side resistance: `R₁ = -1/10`, `R₂ = 2`,
`L₁ = L₂ = C = 1`. -/
def negativeCircuit : Circuit := ⟨⟨-1 / 10, ⟨1, one_pos⟩⟩, ⟨2, ⟨1, one_pos⟩⟩, ⟨1, one_pos⟩⟩

/-- Opposite resistances: `R₁ = 1`, `R₂ = -1`, `L₁ = L₂ = C = 1`. -/
def balancedCircuit : Circuit := ⟨⟨1, ⟨1, one_pos⟩⟩, ⟨-1, ⟨1, one_pos⟩⟩, ⟨1, one_pos⟩⟩

/-- The energy `xᵀ Q x` conserved by the balanced circuit. -/
def balancedEnergy : Matrix (Fin 3) (Fin 3) ℝ := !![2, 2, 1; 2, 3, 2; 1, 2, 2]

@[powerlib_foundation] theorem negativeCircuit_routhHurwitz : negativeCircuit.RouthHurwitz := by
  norm_num [Circuit.RouthHurwitz, negativeCircuit, Circuit.a3, Circuit.a2, Circuit.a1,
    Circuit.a0]

@[powerlib_foundation] theorem balancedEnergy_conserved :
    balancedCircuit.plant.Aᵀ * balancedEnergy + balancedEnergy * balancedCircuit.plant.A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedCircuit, balancedEnergy, Circuit.plant, StateSpace.plant, Matrix.mul_apply,
      Fin.sum_univ_three, RL.toStateSpace_decay]

@[powerlib_foundation] theorem balancedEnergy_pos (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (balancedEnergy *ᵥ v) := by
  have hform : v ⬝ᵥ (balancedEnergy *ᵥ v) =
      2 * (v 0 + v 1 + v 2 / 2) ^ 2 + (v 1 + v 2) ^ 2 + v 2 ^ 2 / 2 := by
    simp [balancedEnergy, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  rw [hform]
  by_contra hle
  push Not at hle
  have q₀ := sq_nonneg (v 0 + v 1 + v 2 / 2)
  have q₁ := sq_nonneg (v 1 + v 2)
  have q₂ := sq_nonneg (v 2)
  have e₂ : v 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith)
  have e₁ : v 1 + v 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith)
  have e₀ : v 0 + v 1 + v 2 / 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith)
  apply hv
  funext i
  fin_cases i <;> simp <;> linarith

/-- Passivity is a sound but not exact translation of Lyapunov stability: the negative-resistance
circuit is pole-stable, hence Lyapunov stable, without being passive. -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hs : negativeCircuit.Stable := stable_of_routhHurwitz _ negativeCircuit_routhHurwitz
  have hmem : negativeCircuit ∈ family.den (.flow .lyapunovStable) :=
    family_isLinear.mem_den_flow.mpr
      (Linear.lyapunovStable_of_isHurwitz 0 ((isHurwitz_iff_stable _).mpr hs))
  rw [← h, mem_realize] at hmem
  have hp : negativeCircuit.Passive := hmem .passive rfl
  have := hp.1
  norm_num [negativeCircuit] at this

/-- Losslessness is a sound but not exact translation of conservation: the balanced circuit
conserves the energy `balancedEnergy` with both resistances nonzero. Passivity is the context in
which the translation is exact (`exactUnder_conservative`). -/
@[tmio TM, powerlib_domain] theorem not_exact_conservative :
    connection% (¬ family.Exact (.flow .conservative)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem : balancedCircuit ∈ family.den (.flow .conservative) :=
    family_isLinear.mem_den_conservative (P := balancedEnergy)
      (by ext i j; fin_cases i <;> fin_cases j <;> rfl) balancedEnergy_pos
      balancedEnergy_conserved
  rw [← h, mem_realize] at hmem
  have hl := (hmem .lossless rfl).1
  norm_num [balancedCircuit] at hl

/-- Opposite unit resistances with `L₁ = L₂ = 1` and `C = 2`: the state matrix has a
nontrivial Jordan chain at zero, while its frequency polynomial is `2 s³`. -/
def jordanCircuit : Circuit :=
  ⟨⟨1, ⟨1, one_pos⟩⟩, ⟨-1, ⟨1, one_pos⟩⟩, ⟨2, by norm_num⟩⟩

@[powerlib_foundation] theorem jordanCircuit_frequency (s : ℂ) :
    jordanCircuit.frequency s = 2 * s ^ 3 := by
  norm_num [Circuit.frequency, Circuit.a3, Circuit.a2, Circuit.a1, Circuit.a0, jordanCircuit]

/-- The right-half-plane pole translation misses polynomial growth at a zero Jordan block.
This is a proved failure of exactness, not an unfinished equivalence. -/
@[tmio TM, powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro hexact
  let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, -1, 1]
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![0, -1, 2]
  have hv : v ≠ 0 := by intro h; have := congrArg (fun x => x 0) h; norm_num [v] at this
  have hAv : Linear.op jordanCircuit.plant.A v = 0 := by
    ext i
    fin_cases i <;> norm_num [v, Linear.op, Circuit.plant, StateSpace.plant,
      jordanCircuit, RL.toStateSpace_decay, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hAw : Linear.op jordanCircuit.plant.A w = v := by
    ext i
    fin_cases i <;> norm_num [v, w, Linear.op, Circuit.plant, StateSpace.plant,
      jordanCircuit, RL.toStateSpace_decay, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hmem : jordanCircuit ∈ family.den (.flow .unstable) :=
    family_isLinear.mem_den_flow.mpr (Linear.unstable_of_zero_jordan_chain hv hAv hAw)
  rw [← hexact, mem_realize] at hmem
  obtain ⟨s, hs, hre⟩ := hmem .rightHalfPlanePole rfl
  rw [jordanCircuit_frequency] at hs
  have hz : s = 0 := by
    have : s ^ 3 = 0 := (mul_eq_zero.mp hs).resolve_left (by norm_num)
    exact (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp this
  simp [hz] at hre

end powerlib.Circuits.LCL
