import theorem.TMIO.ClaimElab
import theorem.Circuits.LCL
import theorem.Linear.Synthesis

/-! # Synthesis of LCL Lyapunov certificates

Two synthesizers produce ordinary `Linear.Certificate`s for the exact plant; what a certificate
proves is the hub's, not restated here.

Rational submissions form the LCL family read through the submitted parameters, its requirement
language extended by acceptance (`rationalFamily`). Acceptance is related to the circuit
requirements by an evaluation of the satisfaction connection (`realize_accepted`); the sentences
keep their exact translations by the generic extension theorems.

Model boundary.
* The LCL filter of `theorem/Circuits/LCL.lean`, unchanged.
* For a passive, damped circuit, a closed-form symbolic witness built from the model
  coefficients; every endpoint is checked by the Lean kernel.
* For circuits submitted with rational parameters, the generic rational synthesizer of
  `Linear.Synthesis`, run by the kernel on the exact rational plant matrix. It needs neither
  passivity nor damping: a circuit with a negative resistance is certified whenever its plant is
  Hurwitz.

Source: the LCL family and its state-space parameters (`theorem/Circuits/LCL.lean`); the
certificates of `theorem/Linear/Certificate.lean`; the rational synthesizer
(`theorem/Linear/Synthesis.lean`); requirement extensions (`Family.extend`,
`theorem/Family/Basic.lean`).

Results.
* Symmetric matrices: `SymmetricMatrix`, `SymmetricMatrix.minor2`, `SymmetricMatrix.det`,
  `SymmetricMatrix.toMatrix`, `SymmetricMatrix.form_pos` (positive leading minors make the form
  positive).
* The symbolic witness (`PassiveWitness`): `coupling`, `gap`, `denominator`, the numerators
  `n11` … `n33`, `minorNumerator`, `detNumerator`, `matrix`; positivity (`coupling_pos`,
  `gap_pos`, `n11_pos`, `minorNumerator_pos`, `detNumerator_pos`), the minor and determinant
  identities (`minor_identity`, `det_identity`) and the Lyapunov equations entry by entry (`eq11`,
  `eq12`, `eq13`, `eq22`, `eq23`, `eq33`).
* Closed-form synthesis: `synthesizeState` (nonnegative decays, not both zero), `synthesize` (a
  passive, damped circuit).
* Rational synthesis: `RationalCircuit`, `RationalCircuit.circuit`, `RationalCircuit.matrix`,
  `RationalCircuit.real_matrix` (the exact rational matrix is the circuit's plant matrix),
  `RationalCircuit.certificate`, `Synthesis`, `rationalFamily_isLinear`.

Family and connection conclusions.
* `Circuits.LCL.rationalFamily : Family RationalCircuit (Requirement ⊕ Synthesis) 3 2`: the LCL
  family read through the submitted parameters (`family.extend`), with the circuit requirements
  and acceptance by the generic synthesizer run on the exact rational plant matrix; the sentences
  keep the LCL translations.
* `realize_accepted`: acceptance by the synthesizer entails pole stability (the accepted
  certificate proves the plant Hurwitz).
-/

noncomputable section

namespace powerlib.Circuits.LCL

open Matrix TMIO

/-- A symmetric 3 × 3 matrix by its upper triangle. -/
@[ext] structure SymmetricMatrix where
  p11 : ℝ
  p12 : ℝ
  p13 : ℝ
  p22 : ℝ
  p23 : ℝ
  p33 : ℝ

def SymmetricMatrix.minor2 (p : SymmetricMatrix) : ℝ := p.p11 * p.p22 - p.p12 ^ 2

def SymmetricMatrix.det (p : SymmetricMatrix) : ℝ :=
  p.p11 * (p.p22 * p.p33 - p.p23 ^ 2) - p.p12 * (p.p12 * p.p33 - p.p23 * p.p13) +
    p.p13 * (p.p12 * p.p23 - p.p22 * p.p13)

/-- The matrix of a symmetric upper triangle. -/
def SymmetricMatrix.toMatrix (p : SymmetricMatrix) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![p.p11, p.p12, p.p13; p.p12, p.p22, p.p23; p.p13, p.p23, p.p33]

/-- Positive leading minors make the quadratic form positive. -/
@[powerlib_foundation] theorem SymmetricMatrix.form_pos (p : SymmetricMatrix) (h1 : 0 < p.p11)
    (h2 : 0 < p.minor2) (h3 : 0 < p.det) (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (p.toMatrix *ᵥ x) := by
  have hform : x ⬝ᵥ (p.toMatrix *ᵥ x) =
      p.p11 * (x 0 + p.p12 / p.p11 * x 1 + p.p13 / p.p11 * x 2) ^ 2 +
      (p.minor2 / p.p11) * (x 1 + (p.p11 * p.p23 - p.p12 * p.p13) / p.minor2 * x 2) ^ 2 +
      (p.det / p.minor2) * x 2 ^ 2 := by
    simp only [SymmetricMatrix.toMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp [ne_of_gt h1, ne_of_gt h2]
    dsimp [SymmetricMatrix.minor2, SymmetricMatrix.det]
    ring
  rw [hform]
  by_cases hz : x 2 = 0
  · by_cases hy : x 1 = 0
    · have h0 : x 0 ≠ 0 := by
        intro h
        apply hx
        funext i
        fin_cases i
        · exact h
        · exact hy
        · exact hz
      simp only [hz, hy, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      exact mul_pos h1 (sq_pos_of_ne_zero h0)
    · simp only [hz, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt h1) (sq_nonneg _))
        (mul_pos (div_pos h2 h1) (sq_pos_of_ne_zero hy))
  · exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg (le_of_lt h1) (sq_nonneg _))
        (mul_nonneg (le_of_lt (div_pos h2 h1)) (sq_nonneg _)))
      (mul_pos (div_pos h3 h2) (sq_pos_of_ne_zero hz))

namespace PassiveWitness

-- A symbolic witness generated from model coefficients, with every endpoint
-- independently checked below. No submitted Lyapunov matrix is required.
def coupling (a d b e : ℝ) : ℝ := a*e+b*d
def gap (a d b e k : ℝ) : ℝ := a*d*(a+d)+k*(a*b+d*e)
def denominator (a d b e k : ℝ) : ℝ := 2*k*coupling a d b e*gap a d b e k

def n11 (a d b e k : ℝ) : ℝ :=
  a ^ 2 * d * e * k + a * d ^ 2 * b * k + a * d ^ 2 * e * k + a * d ^ 2 * k ^ 2 +
    a * b * e * k ^ 2 + a * e ^ 2 * k ^ 2 + a * e * k ^ 3 + d ^ 3 * b * k + d ^ 3 * k ^ 2 +
    d * b * k ^ 3 +
    d * k ^ 2 * ((b-e)^2 + b*e + e^2)

def n12 (a d b e k : ℝ) : ℝ :=
  a ^ 2 * d ^ 2 * k + a ^ 2 * e ^ 2 * k + a ^ 2 * e * k ^ 2 + a * d ^ 3 * k - a * d * b * e * k +
    a * d * b * k ^ 2 + a * d * e ^ 2 * k - d ^ 2 * b * e * k

def n13 (a d b e k : ℝ) : ℝ :=
  - a ^ 2 * d * k ^ 2 - a * d ^ 2 * k ^ 2 +
    a * b * e * k ^ 2 - a * e ^ 2 * k ^ 2 - a * e * k ^ 3 - d * b ^ 2 * k ^ 2 +
    d * b * e * k ^ 2 - d * b * k ^ 3

def n22 (a d b e k : ℝ) : ℝ :=
  a ^ 3 * d ^ 2 + a ^ 3 * e ^ 2 + a ^ 3 * e * k + a ^ 2 * d ^ 3 + a ^ 2 * d * b * k +
    a ^ 2 * d * e ^ 2 + a ^ 2 * d * e * k + a * d ^ 2 * b ^ 2 + a * d ^ 2 * b * k +
    a * d ^ 2 * e * k + a * b ^ 2 * e * k + a * b * e * k ^ 2 + a * e ^ 3 * k + a * e ^ 2 * k ^ 2 +
    d ^ 3 * b ^ 2 + d ^ 3 * b * k + d * b ^ 3 * k + d * b ^ 2 * k ^ 2 + d * b * e ^ 2 * k +
    d * b * e * k ^ 2

def n23 (a d b e k : ℝ) : ℝ :=
  - a ^ 3 * d * k - a ^ 2 * d ^ 2 * k + a ^ 2 * b * e * k - a * d * b ^ 2 * k +
    a * d * b * e * k - a * d * e * k ^ 2 - d ^ 2 * b ^ 2 * k - d ^ 2 * b * k ^ 2

def n33 (a d b e k : ℝ) : ℝ :=
  a ^ 3 * e * k + a ^ 3 * k ^ 2 + a ^ 2 * d * b * k + a ^ 2 * d * e * k + a ^ 2 * d * k ^ 2 +
    a * d ^ 2 * b * k + 2 * a * b ^ 2 * k ^ 2 - a * b * e * k ^ 2 + a * e ^ 2 * k ^ 2 +
    a * e * k ^ 3 + d * b ^ 2 * k ^ 2 + d * b * e * k ^ 2 + d * b * k ^ 3

def minorNumerator (a d b e k : ℝ) : ℝ :=
  a ^ 4 * d ^ 3 + a ^ 4 * d * e ^ 2 + a ^ 4 * d * e * k + 2 * a ^ 3 * d ^ 4 +
    2 * a ^ 3 * d ^ 2 * b * k + 2 * a ^ 3 * d ^ 2 * e ^ 2 + 2 * a ^ 3 * d ^ 2 * e * k +
    a ^ 3 * b * e ^ 2 * k + a ^ 3 * b * e * k ^ 2 + a ^ 2 * d ^ 5 + a ^ 2 * d ^ 3 * b ^ 2 +
    4 * a ^ 2 * d ^ 3 * b * k + a ^ 2 * d ^ 3 * e ^ 2 + 3 * a ^ 2 * d ^ 3 * e * k +
    a ^ 2 * d ^ 3 * k ^ 2 + a ^ 2 * d * b ^ 2 * e * k + a ^ 2 * d * b ^ 2 * k ^ 2 +
    2 * a ^ 2 * d * b * e ^ 2 * k + 3 * a ^ 2 * d * b * e * k ^ 2 + 2 * a ^ 2 * d * e ^ 3 * k +
    3 * a ^ 2 * d * e ^ 2 * k ^ 2 + a ^ 2 * d * e * k ^ 3 + 2 * a * d ^ 4 * b ^ 2 +
    4 * a * d ^ 4 * b * k + 2 * a * d ^ 4 * e * k + 2 * a * d ^ 4 * k ^ 2 +
    2 * a * d ^ 2 * b ^ 3 * k + 4 * a * d ^ 2 * b ^ 2 * k ^ 2 + 3 * a * d ^ 2 * b * e ^ 2 * k +
    4 * a * d ^ 2 * b * e * k ^ 2 + 2 * a * d ^ 2 * b * k ^ 3 + 2 * a * d ^ 2 * e ^ 3 * k +
    5 * a * d ^ 2 * e ^ 2 * k ^ 2 + 2 * a * d ^ 2 * e * k ^ 3 + a * b ^ 3 * e * k ^ 2 +
    a * b ^ 2 * e ^ 2 * k ^ 2 + 2 * a * b ^ 2 * e * k ^ 3 + a * b * e ^ 3 * k ^ 2 +
    2 * a * b * e ^ 2 * k ^ 3 + a * b * e * k ^ 4 + a * e ^ 4 * k ^ 2 + 2 * a * e ^ 3 * k ^ 3 +
    a * e ^ 2 * k ^ 4 + d ^ 5 * b ^ 2 + 2 * d ^ 5 * b * k + d ^ 5 * k ^ 2 +
    4 * d ^ 3 * b ^ 2 * k ^ 2 + 2 * d ^ 3 * b * k ^ 3 + 3 * d ^ 3 * e ^ 2 * k ^ 2 +
    d ^ 3 * e * k ^ 3 + 2 * d * b ^ 3 * k ^ 3 + d * b ^ 2 * k ^ 4 + 2 * d * b * e ^ 2 * k ^ 3 +
    d * b * e * k ^ 4 + 2 * d * e ^ 3 * k ^ 3 + d ^ 3 * b * k * ((b-e)^2 + b^2 + b*e + e^2) +
    d * k ^ 2 * ((b-e)^2 * (b^2+e^2) + b^3*e + b^2*e^2 + b*e^3 + e^4)

def detNumerator (a d b e k : ℝ) : ℝ :=
  a ^ 4 * d ^ 2 + a ^ 4 * e ^ 2 + 2 * a ^ 4 * e * k + a ^ 4 * k ^ 2 + 2 * a ^ 3 * d ^ 3 +
    2 * a ^ 3 * d * b * k + 2 * a ^ 3 * d * e ^ 2 + 4 * a ^ 3 * d * e * k + 2 * a ^ 3 * d * k ^ 2 +
    a ^ 2 * d ^ 4 + a ^ 2 * d ^ 2 * b ^ 2 + 4 * a ^ 2 * d ^ 2 * b * k + a ^ 2 * d ^ 2 * e ^ 2 +
    4 * a ^ 2 * d ^ 2 * e * k + 2 * a ^ 2 * d ^ 2 * k ^ 2 + 2 * a ^ 2 * b ^ 2 * e * k +
    3 * a ^ 2 * b ^ 2 * k ^ 2 + 2 * a ^ 2 * b * e * k ^ 2 + 2 * a ^ 2 * b * k ^ 3 +
    2 * a ^ 2 * e ^ 3 * k + 5 * a ^ 2 * e ^ 2 * k ^ 2 + 4 * a ^ 2 * e * k ^ 3 +
    2 * a * d ^ 3 * b ^ 2 + 4 * a * d ^ 3 * b * k + 2 * a * d ^ 3 * e * k + 2 * a * d ^ 3 * k ^ 2 +
    2 * a * d * b ^ 3 * k + 2 * a * d * b ^ 2 * e * k + 6 * a * d * b ^ 2 * k ^ 2 +
    2 * a * d * b * e ^ 2 * k + 4 * a * d * b * e * k ^ 2 + 2 * a * d * b * k ^ 3 +
    2 * a * d * e ^ 3 * k + 6 * a * d * e ^ 2 * k ^ 2 + 2 * a * d * e * k ^ 3 + d ^ 4 * b ^ 2 +
    2 * d ^ 4 * b * k + d ^ 4 * k ^ 2 + 2 * d ^ 2 * b ^ 3 * k + 5 * d ^ 2 * b ^ 2 * k ^ 2 +
    2 * d ^ 2 * b * e ^ 2 * k + 2 * d ^ 2 * b * e * k ^ 2 + 4 * d ^ 2 * b * k ^ 3 +
    3 * d ^ 2 * e ^ 2 * k ^ 2 + 2 * d ^ 2 * e * k ^ 3 + 2 * b ^ 4 * k ^ 2 + 4 * b ^ 3 * k ^ 3 +
    4 * b ^ 2 * e ^ 2 * k ^ 2 + 4 * b ^ 2 * e * k ^ 3 + 2 * b ^ 2 * k ^ 4 + 4 * b * e ^ 2 * k ^ 3 +
    4 * b * e * k ^ 4 + 2 * e ^ 4 * k ^ 2 + 4 * e ^ 3 * k ^ 3 + 2 * e ^ 2 * k ^ 4 + (a-d)^2 * k^4

def matrix (a d b e k : ℝ) : SymmetricMatrix :=
  let q := denominator a d b e k
  ⟨n11 a d b e k / q, n12 a d b e k / q, n13 a d b e k / q,
    n22 a d b e k / q, n23 a d b e k / q, n33 a d b e k / q⟩

@[powerlib_foundation] theorem coupling_pos {a d b e : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (had : 0 < a ∨ 0 < d) :
    0 < coupling a d b e := by
  rcases had with ha' | hd' <;> dsimp [coupling] <;> positivity

@[powerlib_foundation] theorem gap_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k)
    (had : 0 < a ∨ 0 < d) : 0 < gap a d b e k := by
  rcases had with ha' | hd' <;> dsimp [gap] <;> positivity

@[powerlib_foundation] theorem n11_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k)
    (had : 0 < a ∨ 0 < d) : 0 < n11 a d b e k := by
  rcases had with ha' | hd' <;> dsimp [n11] <;> positivity

@[powerlib_foundation] theorem minorNumerator_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k)
    (had : 0 < a ∨ 0 < d) : 0 < minorNumerator a d b e k := by
  rcases had with ha' | hd' <;> dsimp [minorNumerator] <;> positivity

@[powerlib_foundation] theorem detNumerator_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k) :
    0 < detNumerator a d b e k := by
  dsimp [detNumerator]
  positivity

set_option maxHeartbeats 4000000 in
@[powerlib_foundation] theorem minor_identity (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    (matrix a d b e k).minor2 =
      k * coupling a d b e * minorNumerator a d b e k / (denominator a d b e k)^2 := by
  dsimp [matrix, SymmetricMatrix.minor2]
  field_simp [hq]
  dsimp [n11,n12,n22,coupling,minorNumerator]
  ring

set_option maxHeartbeats 4000000 in
@[powerlib_foundation] theorem det_identity (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    (matrix a d b e k).det =
      k^2 * (coupling a d b e)^2 * gap a d b e k * detNumerator a d b e k /
        (denominator a d b e k)^3 := by
  dsimp [matrix, SymmetricMatrix.det]
  field_simp [hq]
  dsimp [n11, n12, n13, n22, n23, n33, coupling, gap, detNumerator]
  ring

@[powerlib_foundation] theorem eq11 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    -2 * a * (matrix a d b e k).p11 + 2 * k * (matrix a d b e k).p12 = -1 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11, n12, n13, n22, n23, n33, denominator, coupling, gap]
  ring

@[powerlib_foundation] theorem eq12 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    -b * (matrix a d b e k).p11 - a * (matrix a d b e k).p12 + k * (matrix a d b e k).p22 +
      e * (matrix a d b e k).p13 = 0 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11, n12, n13, n22, n23, n33, denominator, coupling, gap]
  ring

@[powerlib_foundation] theorem eq13 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    -(a + d) * (matrix a d b e k).p13 - k * (matrix a d b e k).p12 +
      k * (matrix a d b e k).p23 = 0 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11, n12, n13, n22, n23, n33, denominator, coupling, gap]
  ring

@[powerlib_foundation] theorem eq22 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    -2 * b * (matrix a d b e k).p12 + 2 * e * (matrix a d b e k).p23 = -1 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11, n12, n13, n22, n23, n33, denominator, coupling, gap]
  ring

@[powerlib_foundation] theorem eq23 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    -b * (matrix a d b e k).p13 - k * (matrix a d b e k).p22 - d * (matrix a d b e k).p23 +
      e * (matrix a d b e k).p33 = 0 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11, n12, n13, n22, n23, n33, denominator, coupling, gap]
  ring

@[powerlib_foundation] theorem eq33 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    -2 * k * (matrix a d b e k).p23 - 2 * d * (matrix a d b e k).p33 = -1 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11, n12, n13, n22, n23, n33, denominator, coupling, gap]
  ring

end PassiveWitness

/-- Synthesis on the state-space parameters: nonnegative decays, not both zero. -/
def synthesizeState (s : StateSpace) (ha : 0 ≤ s.first.decay) (hd : 0 ≤ s.second.decay)
    (had : 0 < s.first.decay ∨ 0 < s.second.decay) : Linear.Certificate s.plant.A := by
  let a := s.first.decay
  let d := s.second.decay
  let b := s.first.inputGain.val
  let e := s.second.inputGain.val
  let k := s.capacitorGain.val
  have hb : 0 < b := s.first.inputGain.property
  have he : 0 < e := s.second.inputGain.property
  have hk : 0 < k := s.capacitorGain.property
  have hJ := PassiveWitness.coupling_pos ha hd hb he had
  have hG := PassiveWitness.gap_pos ha hd hb he hk had
  have hq : 0 < PassiveWitness.denominator a d b e k := by
    dsimp [PassiveWitness.denominator]
    positivity
  have hn := ne_of_gt hq
  let p := PassiveWitness.matrix a d b e k
  have h1 : 0 < p.p11 := div_pos (PassiveWitness.n11_pos ha hd hb he hk had) hq
  have h2 : 0 < p.minor2 := by
    rw [PassiveWitness.minor_identity a d b e k hn]
    exact div_pos (mul_pos (mul_pos hk hJ)
      (PassiveWitness.minorNumerator_pos ha hd hb he hk had)) (pow_pos hq 2)
  have h3 : 0 < p.det := by
    rw [PassiveWitness.det_identity a d b e k hn]
    exact div_pos (mul_pos (mul_pos (mul_pos (pow_pos hk 2) (pow_pos hJ 2)) hG)
      (PassiveWitness.detNumerator_pos ha hd hb he hk)) (pow_pos hq 3)
  have e11 := PassiveWitness.eq11 a d b e k hn
  have e12 := PassiveWitness.eq12 a d b e k hn
  have e13 := PassiveWitness.eq13 a d b e k hn
  have e22 := PassiveWitness.eq22 a d b e k hn
  have e23 := PassiveWitness.eq23 a d b e k hn
  have e33 := PassiveWitness.eq33 a d b e k hn
  exact {
    P := p.toMatrix
    symmetric := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    positive := p.form_pos h1 h2 h3
    lyapunov := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [StateSpace.plant, SymmetricMatrix.toMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
        linarith }

/-- Synthesis for a passive, damped circuit, without a supplied witness. -/
def synthesize (m : Circuit) (hp : m.Passive) (hd : m.Damped) : Linear.Certificate m.plant.A :=
  synthesizeState (toStateSpace m)
    (by
      simp only [toStateSpace_first, RL.toStateSpace_decay]
      exact div_nonneg hp.1 m.first.inductance.property.le)
    (by
      simp only [toStateSpace_second, RL.toStateSpace_decay]
      exact div_nonneg hp.2 m.second.inductance.property.le)
    (by
      simp only [toStateSpace_first, toStateSpace_second, RL.toStateSpace_decay]
      rcases hd with hr | hr
      · exact Or.inl (div_pos (lt_of_le_of_ne hp.1 (Ne.symm hr)) m.first.inductance.property)
      · exact Or.inr (div_pos (lt_of_le_of_ne hp.2 (Ne.symm hr)) m.second.inductance.property))

/-! ## Generic synthesis from rational parameters -/

/-- Circuit parameters as submitted, in exact rationals. -/
structure RationalCircuit where
  firstResistance : ℚ
  firstInductance : ℚ
  capacitance : ℚ
  secondResistance : ℚ
  secondInductance : ℚ
  firstInductance_pos : 0 < firstInductance
  capacitance_pos : 0 < capacitance
  secondInductance_pos : 0 < secondInductance

/-- The circuit described by the parameters. -/
def RationalCircuit.circuit (r : RationalCircuit) : Circuit :=
  ⟨⟨r.firstResistance, ⟨r.firstInductance, by exact_mod_cast r.firstInductance_pos⟩⟩,
    ⟨r.secondResistance, ⟨r.secondInductance, by exact_mod_cast r.secondInductance_pos⟩⟩,
    ⟨r.capacitance, by exact_mod_cast r.capacitance_pos⟩⟩

/-- The plant matrix computed exactly from the parameters. -/
def RationalCircuit.matrix (r : RationalCircuit) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-(r.firstResistance / r.firstInductance), -(1 / r.firstInductance), 0;
     1 / r.capacitance, 0, -(1 / r.capacitance);
     0, 1 / r.secondInductance, -(r.secondResistance / r.secondInductance)]

/-- The exact rational matrix is the circuit's plant matrix. -/
@[powerlib_foundation] theorem RationalCircuit.real_matrix (r : RationalCircuit) :
    Linear.Synthesis.real r.matrix = r.circuit.plant.A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RationalCircuit.matrix, RationalCircuit.circuit, Circuit.plant, StateSpace.plant,
      RL.toStateSpace_decay, div_eq_mul_inv]

/-- The certificate the kernel synthesizes from the parameters alone. -/
def RationalCircuit.certificate (r : RationalCircuit)
    (h : Linear.Synthesis.accepts r.matrix = true) : Linear.Certificate r.circuit.plant.A :=
  r.real_matrix ▸ Linear.Synthesis.certificateOf r.matrix h

/-- Requirements a rational submission can meet besides those of the circuit. -/
inductive Synthesis
  | accepted

/-- The LCL family on rational submissions: the circuit requirements, and acceptance by the
generic synthesizer run on the exact rational plant matrix. -/
def rationalFamily : Family RationalCircuit (Requirement ⊕ Synthesis) 3 2 :=
  family.extend RationalCircuit.circuit fun r _ => Linear.Synthesis.accepts r.matrix = true

@[powerlib_foundation] theorem rationalFamily_isLinear :
    rationalFamily.IsLinear (Circuit.plant ∘ RationalCircuit.circuit) :=
  family_isLinear.extend _ _

/-- Acceptance by the synthesizer entails pole stability: the accepted certificate proves the
plant Hurwitz. -/
@[tmio M]
@[powerlib_domain] theorem realize_accepted :
    connection% (realize rationalFamily.meets {.inr .accepted} ⊆
      realize rationalFamily.meets {.inl .poleStable}) := by
  unfold powerlib.TMIO.Statement
  intro r hr
  simp only [mem_realize, Set.mem_singleton_iff, forall_eq] at hr ⊢
  change Linear.Synthesis.accepts r.matrix = true at hr
  change r.circuit.Stable
  exact (isHurwitz_iff_stable _).mp (r.certificate hr).isHurwitz

end powerlib.Circuits.LCL
