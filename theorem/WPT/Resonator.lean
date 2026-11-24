import theorem.Passive.Coupled
import theorem.PH.Composition
import theorem.Criteria.Routh4

/-! # Coupled resonators: the dynamics of the inductive link

The two series-compensated coils of an inductive link in the time domain: two series RLC
resonators coupled by the mutual inductance, read as a linear port-Hamiltonian plant with the two
terminal voltages as ports. Its energy is the magnetic energy of the coil pair and the electric
energy of the two capacitors, so it is passive and Lyapunov stable for every physical pair (the
generic laws of `Port.PortHamiltonian`). Its characteristic polynomial is the quartic
`det(s² L + s R + S) / det L`, and the Routh–Hurwitz criterion decides exactly when the free
oscillation decays: when both resonators are lossy, or when they are coupled and one of them is
lossy — a lossless resonator is damped by its lossy partner through the coupling, and only through
it. Without losses the energy is conserved and two identical resonators ring at the split
frequencies `ω₀/√(1 ± k)`. At every complex frequency that is not a pole the transfer matrix of the
plant is the inverse of the impedance matrix of the coil pair: the phasor equations of
`theorem/WPT/Link.lean` are the frequency response of this plant.

Model boundary.
* Two coils `coils : Passive.Coupled` with their series capacitors: inductances `L₁, L₂ > 0`,
  elastances `S₁, S₂ > 0` (capacitances `1/S_k`), resistances `R₁, R₂ ≥ 0`, mutual inductance `M`
  with `M² < L₁ L₂` (`|k| < 1`). A resistive load in series with a coil is part of its resistance.
* State `x = (φ₁, φ₂, q₁, q₂)`, in this order: the flux linkages `φ = L i` of the coil pair
  (`φ₁ = L₁ i₁ + M i₂`, `φ₂ = M i₁ + L₂ i₂`) and the capacitor charges. Ports: the terminal
  voltages `u = (v₁, v₂)`; outputs: the coil currents `y = (i₁, i₂)`. Continuous time, constant
  parameters, the boundary of `Passive.Coupled`: no inverter, rectifier, switching, control or
  frequency tracking.
* Port-Hamiltonian data: `J = [[0, −I], [I, 0]]`, `R = diag(R₁, R₂, 0, 0)`,
  `Q = blkdiag(L⁻¹, S₁, S₂)` with `L⁻¹ = [[L₂, −M], [−M, L₁]]/(L₁L₂ − M²)`, `B = [I; 0]`; the
  stored energy `xᵀ Q x / 2` is the magnetic energy of the pair plus the capacitor energies.

Source: the coupled-resonator model of inductive and magnetic-resonance power transfer (Kurs et al.,
*Science* 317 (2007) 83–86; Hui, Zhong and Lee, *IEEE Trans. Power Electron.* 29 (2014)
4500–4511, frequency splitting of two coupled resonators); the linear port-Hamiltonian family
(`theorem/Port/PortHamiltonian.lean`, `theorem/PH/Composition.lean`); the quartic Routh–Hurwitz
criterion (`theorem/Criteria/Routh4.lean`); the coil pair of `theorem/Passive/Coupled.lean`.

Results.
* `Resonator` (the coil pair with its sign conditions), `inductanceDet` (`L₁L₂ − M²`), `ph` (the
  plant as `Port.PortHamiltonian 4 2`), `stateMatrix` (`A = (J − R) Q` written out).
* `energy_eq` (`xᵀ Q x` at the state of the currents `i` and charges `q` is twice the magnetic
  energy of the pair plus the capacitor energies), `charpoly_eq` (`det(sI − A)` is the monic
  quartic with the coefficients `(L₁R₂ + L₂R₁)/D`, `(L₁S₂ + L₂S₁ + R₁R₂)/D`, `(R₁S₂ + R₂S₁)/D`,
  `S₁S₂/D`), `hurwitzDet_eq` (its third Hurwitz determinant times `D³` is
  `R₁R₂((L₁S₂ − L₂S₁)² + (L₁R₂ + L₂R₁)(R₁S₂ + R₂S₁)) + M²(R₁S₂ + R₂S₁)²`), `isHurwitz_iff`.
* `splitting` (two identical lossless resonators: `jω` is a characteristic root exactly when
  `(L + M) ω² = S` or `(L − M) ω² = S`), `impedanceMatrix_mul_transfer` (`Z(s) G(s) = I` off the
  poles, `s ≠ 0`).

Family and connection conclusions.
* No new family: the resonator is a member of `Port.PortHamiltonian.family` through `ph`, whose
  system map reads the plant as its port system; passivity and Lyapunov stability of every physical
  resonator are the generic `Port.PortHamiltonian.mem_den_passive`,
  `Port.PortHamiltonian.mem_den_lyapunovStable`, not restated here.
* `mem_den_iff`: every attractive sentence and sampled contraction hold **iff** both resonators are
  lossy, or they are coupled (`M ≠ 0`) and one of them is lossy; `mem_den_conservative` (lossless
  resonators conserve their energy, `PH.mem_den_conservative_of_lossless`).
-/

noncomputable section

namespace powerlib.WPT

open Matrix LinearSystems Complex

/-- Two series-compensated coils with the sign conditions of a physical pair. -/
structure Resonator where
  /-- The coil pair with the series capacitors. -/
  coils : Passive.Coupled
  L₁_pos : 0 < coils.primary.L
  S₁_pos : 0 < coils.primary.S
  S₂_pos : 0 < coils.secondary.S
  R₁_nonneg : 0 ≤ coils.primary.R
  R₂_nonneg : 0 ≤ coils.secondary.R
  coupling_lt : coils.M ^ 2 < coils.primary.L * coils.secondary.L

namespace Resonator

variable (r : Resonator)

/-- The determinant `D = L₁ L₂ − M²` of the inductance matrix. -/
def inductanceDet : ℝ := r.coils.primary.L * r.coils.secondary.L - r.coils.M ^ 2

@[tmio M, powerlib_domain] theorem inductanceDet_pos : 0 < r.inductanceDet := by
  have := r.coupling_lt
  unfold inductanceDet
  linarith

@[tmio M, powerlib_domain] theorem L₂_pos : 0 < r.coils.secondary.L := by
  have h := r.coupling_lt
  have h1 := r.L₁_pos
  by_contra h2
  have : r.coils.primary.L * r.coils.secondary.L ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1.le (not_lt.mp h2)
  nlinarith [sq_nonneg r.coils.M]

/-- The energy matrix `blkdiag(L⁻¹, S₁, S₂)`. -/
def energyMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![r.coils.secondary.L / r.inductanceDet, -(r.coils.M / r.inductanceDet), 0, 0;
    -(r.coils.M / r.inductanceDet), r.coils.primary.L / r.inductanceDet, 0, 0;
    0, 0, r.coils.primary.S, 0;
    0, 0, 0, r.coils.secondary.S]

/-- The quadratic form of the energy matrix. -/
@[tmio M, powerlib_domain] theorem energyMatrix_quadratic (x : Fin 4 → ℝ) :
    x ⬝ᵥ (r.energyMatrix *ᵥ x) =
      (r.coils.secondary.L * x 0 ^ 2 - 2 * r.coils.M * x 0 * x 1 +
          r.coils.primary.L * x 1 ^ 2) / r.inductanceDet +
        r.coils.primary.S * x 2 ^ 2 + r.coils.secondary.S * x 3 ^ 2 := by
  have hD := r.inductanceDet_pos.ne'
  simp [energyMatrix, dotProduct, mulVec, Fin.sum_univ_four]
  field_simp
  ring

/-- The coupled resonators as a linear port-Hamiltonian plant: state `(φ₁, φ₂, q₁, q₂)`, ports
`(v₁, v₂)`. -/
def ph : Port.PortHamiltonian 4 2 where
  J := !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0]
  R := !![r.coils.primary.R, 0, 0, 0; 0, r.coils.secondary.R, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
  Q := r.energyMatrix
  B := !![1, 0; 0, 1; 0, 0; 0, 0]
  skew := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  dissipation_symmetric := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  dissipation_nonneg x := by
    have h1 := r.R₁_nonneg
    have h2 := r.R₂_nonneg
    simp [dotProduct, mulVec, Fin.sum_univ_four]
    nlinarith [mul_nonneg h1 (mul_self_nonneg (x 0)), mul_nonneg h2 (mul_self_nonneg (x 1))]
  energy_symmetric := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [energyMatrix]
  energy_pos x hx := by
    rw [r.energyMatrix_quadratic]
    have hD := r.inductanceDet_pos
    have hL₂ := r.L₂_pos
    have hS₁ := r.S₁_pos
    have hS₂ := r.S₂_pos
    have key : r.coils.secondary.L * (r.coils.secondary.L * x 0 ^ 2 -
        2 * r.coils.M * x 0 * x 1 + r.coils.primary.L * x 1 ^ 2) =
        (r.coils.secondary.L * x 0 - r.coils.M * x 1) ^ 2 + r.inductanceDet * x 1 ^ 2 := by
      unfold inductanceDet
      ring
    have hm : 0 ≤ (r.coils.secondary.L * x 0 ^ 2 - 2 * r.coils.M * x 0 * x 1 +
        r.coils.primary.L * x 1 ^ 2) / r.inductanceDet := by
      apply div_nonneg _ hD.le
      nlinarith [sq_nonneg (r.coils.secondary.L * x 0 - r.coils.M * x 1),
        mul_nonneg hD.le (sq_nonneg (x 1))]
    by_cases h01 : x 0 = 0 ∧ x 1 = 0
    · have h23 : x 2 ≠ 0 ∨ x 3 ≠ 0 := by
        by_contra h
        obtain ⟨h2, h3⟩ := not_or.mp h
        apply hx
        funext i
        fin_cases i
        exacts [h01.1, h01.2, not_not.mp h2, not_not.mp h3]
      rcases h23 with h | h
      · have : 0 < r.coils.primary.S * x 2 ^ 2 := by positivity
        nlinarith [mul_nonneg hS₂.le (sq_nonneg (x 3))]
      · have : 0 < r.coils.secondary.S * x 3 ^ 2 := by positivity
        nlinarith [mul_nonneg hS₁.le (sq_nonneg (x 2))]
    · have hpos : 0 < r.coils.secondary.L * x 0 ^ 2 - 2 * r.coils.M * x 0 * x 1 +
          r.coils.primary.L * x 1 ^ 2 := by
        rcases not_and_or.mp h01 with h | h
        · by_cases h1 : x 1 = 0
          · have : 0 < r.coils.secondary.L * x 0 ^ 2 := by positivity
            rw [h1]
            nlinarith
          · have : 0 < r.inductanceDet * x 1 ^ 2 := by positivity
            nlinarith [sq_nonneg (r.coils.secondary.L * x 0 - r.coils.M * x 1)]
        · have : 0 < r.inductanceDet * x 1 ^ 2 := by positivity
          nlinarith [sq_nonneg (r.coils.secondary.L * x 0 - r.coils.M * x 1)]
      have : 0 < (r.coils.secondary.L * x 0 ^ 2 - 2 * r.coils.M * x 0 * x 1 +
          r.coils.primary.L * x 1 ^ 2) / r.inductanceDet := div_pos hpos hD
      nlinarith [mul_nonneg hS₁.le (sq_nonneg (x 2)), mul_nonneg hS₂.le (sq_nonneg (x 3))]

/-- The stored energy at the state of the coil currents `i` and the capacitor charges `q`: the
flux linkages are `φ = L i`, and `xᵀ Q x` is twice the magnetic energy of the pair plus the
capacitor energies. -/
@[tmio M, powerlib_domain] theorem energy_eq (i₁ i₂ q₁ q₂ : ℝ) :
    ![r.coils.primary.L * i₁ + r.coils.M * i₂, r.coils.M * i₁ + r.coils.secondary.L * i₂, q₁, q₂] ⬝ᵥ
        (r.ph.Q *ᵥ ![r.coils.primary.L * i₁ + r.coils.M * i₂,
          r.coils.M * i₁ + r.coils.secondary.L * i₂, q₁, q₂]) =
      2 * (r.coils.magneticEnergy i₁ i₂ + r.coils.primary.capacitorEnergy q₁ +
        r.coils.secondary.capacitorEnergy q₂) := by
  have hD := r.inductanceDet_pos.ne'
  change _ ⬝ᵥ (r.energyMatrix *ᵥ _) = _
  rw [r.energyMatrix_quadratic]
  simp [Passive.Coupled.magneticEnergy, Passive.SeriesRLC.capacitorEnergy]
  field_simp
  unfold inductanceDet
  ring

/-- The state matrix `A = (J − R) Q`. -/
@[tmio M, powerlib_domain] theorem stateMatrix :
    r.ph.plant.A =
      !![-(r.coils.primary.R * r.coils.secondary.L / r.inductanceDet),
          r.coils.primary.R * r.coils.M / r.inductanceDet, -r.coils.primary.S, 0;
        r.coils.secondary.R * r.coils.M / r.inductanceDet,
          -(r.coils.secondary.R * r.coils.primary.L / r.inductanceDet), 0, -r.coils.secondary.S;
        r.coils.secondary.L / r.inductanceDet, -(r.coils.M / r.inductanceDet), 0, 0;
        -(r.coils.M / r.inductanceDet), r.coils.primary.L / r.inductanceDet, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Port.PortHamiltonian.plant, ph, energyMatrix] <;>
    ring

/-! ## The characteristic polynomial -/

/-- The coefficient `a₃ = (L₁R₂ + L₂R₁)/D`. -/
def a3 : ℝ := (r.coils.primary.L * r.coils.secondary.R + r.coils.secondary.L * r.coils.primary.R) /
  r.inductanceDet

/-- The coefficient `a₂ = (L₁S₂ + L₂S₁ + R₁R₂)/D`. -/
def a2 : ℝ := (r.coils.primary.L * r.coils.secondary.S + r.coils.secondary.L * r.coils.primary.S +
  r.coils.primary.R * r.coils.secondary.R) / r.inductanceDet

/-- The coefficient `a₁ = (R₁S₂ + R₂S₁)/D`. -/
def a1 : ℝ := (r.coils.primary.R * r.coils.secondary.S + r.coils.secondary.R * r.coils.primary.S) /
  r.inductanceDet

/-- The coefficient `a₀ = S₁S₂/D`. -/
def a0 : ℝ := r.coils.primary.S * r.coils.secondary.S / r.inductanceDet

/-- The characteristic polynomial of the resonators is the monic quartic
`det(s² L + s R + S)/det L`. -/
@[tmio M, powerlib_domain] theorem charpoly_eq (s : ℂ) :
    (Linear.characteristicMatrix r.ph.plant.A s).det =
      s ^ 4 + (r.a3 : ℂ) * s ^ 3 + (r.a2 : ℂ) * s ^ 2 + (r.a1 : ℂ) * s + (r.a0 : ℂ) := by
  have hD : r.coils.primary.L * r.coils.secondary.L - r.coils.M ^ 2 ≠ 0 := r.inductanceDet_pos.ne'
  have htr : r.ph.plant.A.trace = -r.a3 := by
    rw [stateMatrix]
    simp [Matrix.trace, Fin.sum_univ_four, a3, inductanceDet]
    field_simp
    ring
  have hm2 : Criteria.principalMinorSum2Fin4 r.ph.plant.A = r.a2 := by
    rw [stateMatrix]
    simp [Criteria.principalMinorSum2Fin4, a2, inductanceDet]
    field_simp
    ring
  have hm3 : Criteria.principalMinorSum3Fin4 r.ph.plant.A = -r.a1 := by
    rw [stateMatrix]
    simp [Criteria.principalMinorSum3Fin4, a1, inductanceDet]
    field_simp
    ring
  have hdet : r.ph.plant.A.det = r.a0 := by
    rw [stateMatrix, Criteria.det_fin_four]
    simp [a0, inductanceDet]
    field_simp
  rw [Criteria.det_characteristicMatrix_fin_four, htr, hm2, hm3, hdet]
  push_cast
  ring

/-- The third Hurwitz determinant of the quartic, cleared of `D³`:
`(a₃a₂a₁ − a₁² − a₃²a₀) D³ = R₁R₂((L₁S₂ − L₂S₁)² + (L₁R₂ + L₂R₁)(R₁S₂ + R₂S₁)) + M²(R₁S₂ + R₂S₁)²`. -/
@[tmio M, powerlib_domain] theorem hurwitzDet_eq :
    (r.a3 * r.a2 * r.a1 - r.a1 ^ 2 - r.a3 ^ 2 * r.a0) * r.inductanceDet ^ 3 =
      r.coils.primary.R * r.coils.secondary.R *
          ((r.coils.primary.L * r.coils.secondary.S - r.coils.secondary.L * r.coils.primary.S) ^ 2 +
            (r.coils.primary.L * r.coils.secondary.R + r.coils.secondary.L * r.coils.primary.R) *
              (r.coils.primary.R * r.coils.secondary.S +
                r.coils.secondary.R * r.coils.primary.S)) +
        r.coils.M ^ 2 * (r.coils.primary.R * r.coils.secondary.S +
          r.coils.secondary.R * r.coils.primary.S) ^ 2 := by
  have hD : r.coils.primary.L * r.coils.secondary.L - r.coils.M ^ 2 ≠ 0 := r.inductanceDet_pos.ne'
  simp only [a3, a2, a1, a0, inductanceDet]
  field_simp
  ring

/-- The resonators are Hurwitz **iff** both are lossy, or they are coupled and one is lossy. -/
@[tmio TM, powerlib_domain] theorem isHurwitz_iff :
    IsHurwitz r.ph.plant.A ↔
      (0 < r.coils.primary.R ∧ 0 < r.coils.secondary.R) ∨
        (r.coils.M ≠ 0 ∧ (0 < r.coils.primary.R ∨ 0 < r.coils.secondary.R)) := by
  rw [Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _ r.charpoly_eq]
  have hD := r.inductanceDet_pos
  have hL₁ := r.L₁_pos
  have hL₂ := r.L₂_pos
  have hS₁ := r.S₁_pos
  have hS₂ := r.S₂_pos
  have hR₁ := r.R₁_nonneg
  have hR₂ := r.R₂_nonneg
  have hH := r.hurwitzDet_eq
  have ha0 : 0 < r.a0 := by unfold a0; positivity
  have hD3 : 0 < r.inductanceDet ^ 3 := by positivity
  -- the Hurwitz determinant condition is the sign of the cleared determinant
  have hdet : r.a1 ^ 2 + r.a3 ^ 2 * r.a0 < r.a3 * r.a2 * r.a1 ↔
      0 < (r.a3 * r.a2 * r.a1 - r.a1 ^ 2 - r.a3 ^ 2 * r.a0) * r.inductanceDet ^ 3 := by
    rw [mul_pos_iff_of_pos_right hD3]
    constructor <;> intro h <;> linarith
  have ha3 : 0 < r.a3 ↔ 0 < r.coils.primary.R ∨ 0 < r.coils.secondary.R := by
    unfold a3
    rw [div_pos_iff_of_pos_right hD]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      have h1 : r.coils.primary.R = 0 := le_antisymm h'.1 hR₁
      have h2 : r.coils.secondary.R = 0 := le_antisymm h'.2 hR₂
      simp [h1, h2] at h
    · rintro (h | h) <;> positivity
  have ha1 : 0 < r.a1 ↔ 0 < r.coils.primary.R ∨ 0 < r.coils.secondary.R := by
    unfold a1
    rw [div_pos_iff_of_pos_right hD]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      have h1 : r.coils.primary.R = 0 := le_antisymm h'.1 hR₁
      have h2 : r.coils.secondary.R = 0 := le_antisymm h'.2 hR₂
      simp [h1, h2] at h
    · rintro (h | h) <;> positivity
  rw [hdet, hH, ha3, ha1]
  constructor
  · rintro ⟨h3, -, -, hpos⟩
    by_cases hb : 0 < r.coils.primary.R ∧ 0 < r.coils.secondary.R
    · exact Or.inl hb
    · right
      refine ⟨fun hM => ?_, h3⟩
      have h0 : r.coils.primary.R * r.coils.secondary.R = 0 := by
        rcases not_and_or.mp hb with h | h
        · rw [le_antisymm (not_lt.mp h) hR₁, zero_mul]
        · rw [le_antisymm (not_lt.mp h) hR₂, mul_zero]
      rw [h0, hM] at hpos
      simp at hpos
  · rintro (⟨h1, h2⟩ | ⟨hM, h⟩)
    · refine ⟨Or.inl h1, Or.inl h1, ha0, ?_⟩
      have : 0 < r.coils.primary.R * r.coils.secondary.R *
          ((r.coils.primary.L * r.coils.secondary.S - r.coils.secondary.L * r.coils.primary.S) ^ 2 +
          (r.coils.primary.L * r.coils.secondary.R + r.coils.secondary.L * r.coils.primary.R) *
            (r.coils.primary.R * r.coils.secondary.S +
              r.coils.secondary.R * r.coils.primary.S)) := by positivity
      have : 0 ≤ r.coils.M ^ 2 * (r.coils.primary.R * r.coils.secondary.S +
          r.coils.secondary.R * r.coils.primary.S) ^ 2 := by positivity
      linarith
    · refine ⟨h, h, ha0, ?_⟩
      have hc : 0 < r.coils.primary.R * r.coils.secondary.S +
          r.coils.secondary.R * r.coils.primary.S := by
        rcases h with h | h <;> positivity
      have : 0 < r.coils.M ^ 2 * (r.coils.primary.R * r.coils.secondary.S +
          r.coils.secondary.R * r.coils.primary.S) ^ 2 := by positivity
      have : 0 ≤ r.coils.primary.R * r.coils.secondary.R *
          ((r.coils.primary.L * r.coils.secondary.S - r.coils.secondary.L * r.coils.primary.S) ^ 2 +
          (r.coils.primary.L * r.coils.secondary.R + r.coils.secondary.L * r.coils.primary.R) *
            (r.coils.primary.R * r.coils.secondary.S +
              r.coils.secondary.R * r.coils.primary.S)) := by positivity
      linarith

/-- Every attractive sentence and sampled contraction hold for the free resonators **iff** both are
lossy, or they are coupled and one of them is lossy. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (r.ph ∈ Port.PortHamiltonian.family.den (.flow P) ↔
      (0 < r.coils.primary.R ∧ 0 < r.coils.secondary.R) ∨
        (r.coils.M ≠ 0 ∧ (0 < r.coils.primary.R ∨ 0 < r.coils.secondary.R))) := by
  unfold TMIO.Statement
  rw [Port.PortHamiltonian.family_isLinear.den_hurwitz hP, Set.mem_ofPred_eq]
  exact r.isHurwitz_iff

/-- Lossless resonators conserve their energy. -/
@[tmio TM, powerlib_domain] theorem mem_den_conservative (h₁ : r.coils.primary.R = 0)
    (h₂ : r.coils.secondary.R = 0) :
    connection% (r.ph ∈ Port.PortHamiltonian.family.den (.flow .conservative)) := by
  refine PH.mem_den_conservative_of_lossless _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ph, h₁, h₂]

/-- Frequency splitting: two identical lossless resonators (`L₁ = L₂ = L`, `S₁ = S₂ = S`) have the
characteristic root `jω` exactly when `(L + M) ω² = S` or `(L − M) ω² = S`, i.e. at
`ω₀/√(1 + k)` and `ω₀/√(1 − k)` with `ω₀² = S/L`, `k = M/L`. -/
@[tmio M, powerlib_domain] theorem splitting (h₁ : r.coils.primary.R = 0)
    (h₂ : r.coils.secondary.R = 0) (hL : r.coils.secondary.L = r.coils.primary.L)
    (hS : r.coils.secondary.S = r.coils.primary.S) (ω : ℝ) :
    (Linear.characteristicMatrix r.ph.plant.A (ω * I)).det = 0 ↔
      (r.coils.primary.L + r.coils.M) * ω ^ 2 = r.coils.primary.S ∨
        (r.coils.primary.L - r.coils.M) * ω ^ 2 = r.coils.primary.S := by
  have hD := r.inductanceDet_pos
  have key : (Linear.characteristicMatrix r.ph.plant.A (ω * I)).det =
      ((((r.coils.primary.L + r.coils.M) * ω ^ 2 - r.coils.primary.S) *
        ((r.coils.primary.L - r.coils.M) * ω ^ 2 - r.coils.primary.S) / r.inductanceDet : ℝ) :
        ℂ) := by
    have h3 : r.a3 = 0 := by simp [a3, h₁, h₂]
    have h1' : r.a1 = 0 := by simp [a1, h₁, h₂]
    have e2 : ((ω : ℂ) * I) ^ 2 = -(ω : ℂ) ^ 2 := by rw [mul_pow, I_sq]; ring
    have e4 : ((ω : ℂ) * I) ^ 4 = (ω : ℂ) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2]; ring
    have hD' : (r.coils.primary.L : ℂ) * r.coils.primary.L - r.coils.M ^ 2 ≠ 0 := by
      have : r.coils.primary.L * r.coils.primary.L - r.coils.M ^ 2 ≠ 0 := by
        have := hD.ne'; rwa [inductanceDet, hL] at this
      exact_mod_cast this
    have hD'' : (r.coils.primary.L : ℂ) ^ 2 - r.coils.M ^ 2 ≠ 0 := by rw [sq]; exact hD'
    rw [charpoly_eq, h3, h1', e4, e2]
    simp only [a2, a0, inductanceDet, hL, hS, h₁, h₂, mul_zero, add_zero]
    push_cast
    field_simp
    ring
  rw [key, Complex.ofReal_eq_zero, div_eq_zero_iff, or_iff_left hD.ne', mul_eq_zero, sub_eq_zero,
    sub_eq_zero]

/-! ## The frequency response -/

/-- The transfer matrix of the resonators is the inverse of the impedance matrix of the coil pair:
at every complex frequency `s ≠ 0` that is not a pole, `Z(s) G(s) = I`. The phasor equations of
the link (`theorem/WPT/Link.lean`) are therefore the frequency response of this plant. -/
@[tmio M, powerlib_domain] theorem impedanceMatrix_mul_transfer {s : ℂ} (hs : s ≠ 0)
    (hdet : (Linear.characteristicMatrix r.ph.plant.A s).det ≠ 0) :
    r.coils.impedanceMatrix s * Linear.transfer r.ph.plant s = 1 := by
  set K := Linear.characteristicMatrix r.ph.plant.A s with hKdef
  have hK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K (isUnit_iff_ne_zero.mpr hdet)
  set X := K⁻¹ * Linear.complexify r.ph.plant.B with hXdef
  have hX : K * X = Linear.complexify r.ph.plant.B := by
    rw [hXdef, ← Matrix.mul_assoc, hK, Matrix.one_mul]
  have hT : Linear.transfer r.ph.plant s = Linear.complexify r.ph.plant.C * X := by
    rw [Linear.transfer, hXdef, ← hKdef, Matrix.mul_assoc]
    simp [Port.PortHamiltonian.plant]
  rw [hT]
  have hD : (r.inductanceDet : ℂ) ≠ 0 := by exact_mod_cast r.inductanceDet_pos.ne'
  have e : ∀ i j, (K * X) i j = Linear.complexify r.ph.plant.B i j := fun i j => by rw [hX]
  ext i j
  have e0 := e 0 j
  have e1 := e 1 j
  have e2 := e 2 j
  have e3 := e 3 j
  simp only [hKdef, Linear.characteristicMatrix, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, Linear.complexify,
    Port.PortHamiltonian.plant, ph, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e0 e1 e2 e3
  have hDD : ((r.coils.primary.L : ℂ) * r.coils.secondary.L - (r.coils.M : ℂ) ^ 2) /
      r.inductanceDet = 1 := by
    rw [div_eq_one_iff_eq hD]
    push_cast [inductanceDet]
    ring
  have hs' : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  fin_cases i <;> fin_cases j <;>
    simp [Passive.Coupled.impedanceMatrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
      Port.PortHamiltonian.plant, ph, energyMatrix, Passive.SeriesRLC.impedance] at e0 e1 e2 e3 ⊢
  · linear_combination e0 - (r.coils.primary.S / s) * e2 + (s * X 0 0) * hDD +
      (r.coils.primary.S * X 2 0) * hs'
  · linear_combination e0 - (r.coils.primary.S / s) * e2 + (s * X 0 1) * hDD +
      (r.coils.primary.S * X 2 1) * hs'
  · linear_combination e1 - (r.coils.secondary.S / s) * e3 + (s * X 1 0) * hDD +
      (r.coils.secondary.S * X 3 0) * hs'
  · linear_combination e1 - (r.coils.secondary.S / s) * e3 + (s * X 1 1) * hDD +
      (r.coils.secondary.S * X 3 1) * hs'

end Resonator

end powerlib.WPT
