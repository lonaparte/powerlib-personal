import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# Constructive first-order normal-form algebra

For a diagonal constant generator, the Fourier homological equation is solved
entry by entry on a selected set of nonresonant channels. The coefficients and
their time derivatives are constructed; the homological equation is not assumed.

The final exact change-of-generator identities retain the entire second-order
remainder. They do not claim a finite-time error estimate, periodic-orbit
existence, or a Floquet-exponent approximation.
-/

noncomputable section

namespace Powerlib.Parametric.NormalForm

variable {ι : Type*}

/-- Fourier coefficient to remove. Channels outside `removed` are retained. -/
def removedCoefficient (C : Matrix ι ι ℂ) (removed : ι → ι → Prop) : Matrix ι ι ℂ := by
  classical
  exact fun j r => if removed j r then C j r else 0

/-- Construct the homological coefficient, with zero on retained channels.
For a pump harmonic take `β = Complex.I * (ν * ω : ℝ)`. -/
def homologicalCoefficient (β : ℂ) (lam : ι → ℂ) (C : Matrix ι ι ℂ)
    (removed : ι → ι → Prop) : Matrix ι ι ℂ := by
  classical
  exact fun j r => if removed j r then C j r / (β - lam j + lam r) else 0

/-- Nonresonance is needed only for channels actually removed. -/
theorem homologicalCoefficient_mul_denominator
    (β : ℂ) (lam : ι → ℂ) (C : Matrix ι ι ℂ) (removed : ι → ι → Prop)
    (hgap : ∀ j r, removed j r → β - lam j + lam r ≠ 0) (j r : ι) :
    (β - lam j + lam r) * homologicalCoefficient β lam C removed j r =
      removedCoefficient C removed j r := by
  classical
  simp only [homologicalCoefficient, removedCoefficient]
  split_ifs with h
  · field_simp [hgap j r h]
  · simp

/-- The scalar homological equation satisfied by the explicitly constructed
Fourier coefficient. -/
theorem homologicalCoefficient_equation
    (β : ℂ) (lam : ι → ℂ) (C : Matrix ι ι ℂ) (removed : ι → ι → Prop)
    (hgap : ∀ j r, removed j r → β - lam j + lam r ≠ 0) (j r : ι) :
    β * homologicalCoefficient β lam C removed j r =
      lam j * homologicalCoefficient β lam C removed j r -
        homologicalCoefficient β lam C removed j r * lam r +
        removedCoefficient C removed j r := by
  linear_combination homologicalCoefficient_mul_denominator β lam C removed hgap j r

/-- A quantitative nonresonant gap bounds each coordinate correction. -/
theorem norm_homologicalCoefficient_le
    (β : ℂ) (lam : ι → ℂ) (C : Matrix ι ι ℂ) (removed : ι → ι → Prop)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ j r, removed j r → γ ≤ ‖β - lam j + lam r‖) (j r : ι) :
    ‖homologicalCoefficient β lam C removed j r‖ ≤ ‖C j r‖ / γ := by
  classical
  simp only [homologicalCoefficient]
  split_ifs with h
  · rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hγ (hgap j r h)
  · simpa only [norm_zero] using div_nonneg (norm_nonneg (C j r)) hγ.le

/-- A single complex Fourier mode of a matrix-valued function. -/
def fourierMode (β : ℂ) (C : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  fun j r => C j r * Complex.exp (β * (t : ℂ))

/-- Periodicity follows from the scalar harmonic's period. -/
theorem fourierMode_periodic (β : ℂ) (C : Matrix ι ι ℂ) (T : ℝ)
    (hperiod : Complex.exp (β * (T : ℂ)) = 1) :
    Function.Periodic (fourierMode β C) T := by
  intro t
  funext j r
  simp only [fourierMode, Complex.ofReal_add, mul_add, Complex.exp_add, hperiod, mul_one]

/-- The positive pump harmonic has period `2π / ω`. -/
theorem pump_fourierMode_periodic (ω : ℝ) (hω : ω ≠ 0) (C : Matrix ι ι ℂ) :
    Function.Periodic (fourierMode (Complex.I * (ω : ℂ)) C) (2 * Real.pi / ω) := by
  apply fourierMode_periodic
  have hw : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have hexponent :
      Complex.I * (ω : ℂ) * ((2 * Real.pi / ω : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    calc
      Complex.I * (ω : ℂ) * (2 * (Real.pi : ℂ) / ω) =
          (2 * (Real.pi : ℂ) * Complex.I) * ((ω : ℂ) / ω) := by ring
      _ = 2 * (Real.pi : ℂ) * Complex.I := by rw [div_self hw, mul_one]
  rw [hexponent]
  exact Complex.exp_two_pi_mul_I

/-- A purely imaginary harmonic has unit modulus, so coefficient bounds hold
uniformly for all real times. -/
theorem norm_pump_fourierMode_entry (ω : ℝ) (C : Matrix ι ι ℂ) (t : ℝ) (j r : ι) :
    ‖fourierMode (Complex.I * (ω : ℂ)) C t j r‖ = ‖C j r‖ := by
  simp [fourierMode, Complex.norm_exp]

/-- Actual real-time differentiation of a Fourier matrix entry. -/
theorem hasDerivAt_fourierMode_entry
    (β : ℂ) (C : Matrix ι ι ℂ) (j r : ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fourierMode β C s j r)
      (β * fourierMode β C t j r) t := by
  have hlin : HasDerivAt (fun s : ℝ => β * (s : ℂ)) β t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.const_mul β)
  convert hlin.cexp.const_mul (C j r) using 1
  ring

/-- The constructed Fourier correction solves the differential homological
equation, entry by entry, for the diagonal generator. -/
theorem hasDerivAt_homological_entry
    [Fintype ι] [DecidableEq ι]
    (β : ℂ) (lam : ι → ℂ) (C : Matrix ι ι ℂ) (removed : ι → ι → Prop)
    (hgap : ∀ j r, removed j r → β - lam j + lam r ≠ 0) (j r : ι) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => fourierMode β (homologicalCoefficient β lam C removed) s j r)
      ((Matrix.diagonal lam * fourierMode β (homologicalCoefficient β lam C removed) t -
        fourierMode β (homologicalCoefficient β lam C removed) t * Matrix.diagonal lam +
        fourierMode β (removedCoefficient C removed) t) j r) t := by
  convert hasDerivAt_fourierMode_entry β (homologicalCoefficient β lam C removed) j r t
      using 1
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    fourierMode]
  have hc := homologicalCoefficient_equation β lam C removed hgap j r
  linear_combination -Complex.exp (β * (t : ℂ)) * hc

/-- The entrywise construction also gives a matrix-valued derivative. -/
theorem hasDerivAt_homological
    [Fintype ι] [DecidableEq ι]
    (β : ℂ) (lam : ι → ℂ) (C : Matrix ι ι ℂ) (removed : ι → ι → Prop)
    (hgap : ∀ j r, removed j r → β - lam j + lam r ≠ 0) (t : ℝ) :
    HasDerivAt (fourierMode β (homologicalCoefficient β lam C removed))
      (Matrix.diagonal lam * fourierMode β (homologicalCoefficient β lam C removed) t -
        fourierMode β (homologicalCoefficient β lam C removed) t * Matrix.diagonal lam +
        fourierMode β (removedCoefficient C removed) t) t := by
  apply hasDerivAt_pi.mpr
  intro j
  apply hasDerivAt_pi.mpr
  intro r
  exact hasDerivAt_homological_entry β lam C removed hgap j r t

/-- Sum two solved homological equations, allowing the positive and negative
pump harmonics to retain different channel masks. -/
theorem hasDerivAt_two_harmonic_correction_entry
    [Fintype ι] [DecidableEq ι]
    (β₁ β₂ : ℂ) (lam : ι → ℂ) (C₁ C₂ : Matrix ι ι ℂ)
    (removed₁ removed₂ : ι → ι → Prop)
    (hgap₁ : ∀ j r, removed₁ j r → β₁ - lam j + lam r ≠ 0)
    (hgap₂ : ∀ j r, removed₂ j r → β₂ - lam j + lam r ≠ 0)
    (j r : ι) (t : ℝ) :
    let S₁ := fourierMode β₁ (homologicalCoefficient β₁ lam C₁ removed₁)
    let S₂ := fourierMode β₂ (homologicalCoefficient β₂ lam C₂ removed₂)
    let H₁ := fourierMode β₁ (removedCoefficient C₁ removed₁)
    let H₂ := fourierMode β₂ (removedCoefficient C₂ removed₂)
    HasDerivAt (fun s : ℝ => (S₁ s + S₂ s) j r)
      ((Matrix.diagonal lam * (S₁ t + S₂ t) -
        (S₁ t + S₂ t) * Matrix.diagonal lam + (H₁ t + H₂ t)) j r) t := by
  dsimp only
  convert
    (hasDerivAt_homological_entry β₁ lam C₁ removed₁ hgap₁ j r t).add
      (hasDerivAt_homological_entry β₂ lam C₂ removed₂ hgap₂ j r t) using 1
  simp only [mul_add, add_mul, Matrix.add_apply, Matrix.sub_apply]
  abel

section RingIdentity

variable {R : Type*} [Ring R]

/-- Exact algebra behind the near-identity transformation. No error term has
been discarded: the right-hand side is precisely the transformed residual
before applying the inverse coordinate map. -/
theorem nearIdentity_residual_identity (D H Hres S R₂ : R) :
    (D + H + R₂) * (1 + S) -
        (D * S - S * D + H - Hres) -
        (1 + S) * (D + Hres) =
      H * S - S * Hres + R₂ * (1 + S) := by
  noncomm_ring

/-- Exact transformed-generator formula with an explicitly supplied left
inverse. The inverse hypothesis concerns only a finite-dimensional coordinate
map; no approximation theorem is hidden in it. -/
theorem transformed_generator_identity (D H Hres S R₂ U : R)
    (hleft : U * (1 + S) = 1) :
    U * ((D + H + R₂) * (1 + S) - (D * S - S * D + H - Hres)) =
      D + Hres + U * (H * S - S * Hres + R₂ * (1 + S)) := by
  have hres := nearIdentity_residual_identity D H Hres S R₂
  have hsplit :
      (D + H + R₂) * (1 + S) - (D * S - S * D + H - Hres) =
        (1 + S) * (D + Hres) + (H * S - S * Hres + R₂ * (1 + S)) := by
    exact (sub_eq_iff_eq_add.mp hres).trans (add_comm _ _)
  rw [hsplit, mul_add, ← mul_assoc, hleft, one_mul]

/-- The reverse algebraic identity reconstructs the original generator from
the transformed generator and the coordinate derivative. -/
theorem reconstruct_generator_identity (D H Hres S R₂ U : R)
    (hright : (1 + S) * U = 1) :
    (1 + S) * (D + Hres + U * (H * S - S * Hres + R₂ * (1 + S))) +
        (D * S - S * D + H - Hres) =
      (D + H + R₂) * (1 + S) := by
  have hres := nearIdentity_residual_identity D H Hres S R₂
  have hsplit :
      (D + H + R₂) * (1 + S) - (D * S - S * D + H - Hres) =
        (1 + S) * (D + Hres) + (H * S - S * Hres + R₂ * (1 + S)) :=
    (sub_eq_iff_eq_add.mp hres).trans (add_comm _ _)
  rw [mul_add, ← mul_assoc, hright, one_mul]
  exact (sub_eq_iff_eq_add.mp hsplit).symm

end RingIdentity

section TrajectoryIdentity

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Exact reconstruction of a trajectory (or a fundamental-matrix solution).
Here `S` and the perturbation coefficients include their amplitude factors.
The homological derivative premise is supplied by the constructive Fourier
lemmas above; the transformed dynamics retains its full residual.

This product-rule statement connects the generator identity to actual
time-domain solutions. It does not assume an error estimate. -/
theorem hasDerivAt_nearIdentity_mul
    (S Y : ℝ → R) (D H Hres R₂ U : R) (t : ℝ)
    (hS : HasDerivAt S (D * S t - S t * D + H - Hres) t)
    (hY : HasDerivAt Y
      ((D + Hres + U * (H * S t - S t * Hres + R₂ * (1 + S t))) * Y t) t)
    (hright : (1 + S t) * U = 1) :
    HasDerivAt (fun s : ℝ => (1 + S s) * Y s)
      ((D + H + R₂) * ((1 + S t) * Y t)) t := by
  have hproduct := ((hasDerivAt_const t (1 : R)).add hS).mul hY
  convert hproduct using 1
  simp only [zero_add]
  rw [← mul_assoc, ← reconstruct_generator_identity D H Hres (S t) R₂ U hright]
  noncomm_ring

end TrajectoryIdentity

section VectorTrajectoryIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The corresponding exact reconstruction for state-vector trajectories,
using continuous linear operators with their operator norm. -/
theorem hasDerivAt_nearIdentity_apply
    (S : ℝ → E →L[ℝ] E) (y : ℝ → E)
    (D H Hres R₂ U : E →L[ℝ] E) (t : ℝ)
    (hS : HasDerivAt S (D * S t - S t * D + H - Hres) t)
    (hy : HasDerivAt y
      ((D + Hres + U * (H * S t - S t * Hres + R₂ * (1 + S t))) (y t)) t)
    (hright : (1 + S t) * U = 1) :
    HasDerivAt (fun s : ℝ => (1 + S s) (y s))
      ((D + H + R₂) ((1 + S t) (y t))) t := by
  have hproduct := ((hasDerivAt_const t (1 : E →L[ℝ] E)).add hS).clm_apply hy
  convert hproduct using 1
  simp only [zero_add]
  have hg := congrArg (fun A : E →L[ℝ] E => A (y t))
    (reconstruct_generator_identity D H Hres (S t) R₂ U hright)
  change (1 + S t)
      ((D + Hres + U * (H * S t - S t * Hres + R₂ * (1 + S t))) (y t)) +
      (D * S t - S t * D + H - Hres) (y t) =
    (D + H + R₂) ((1 + S t) (y t)) at hg
  exact hg.symm.trans (add_comm _ _)

end VectorTrajectoryIdentity

section ScaledIdentity

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The unscaled remainder after a first-order coordinate change. -/
def transformedRemainder (ε : ℝ) (H Hres S R₂ U : R) : R :=
  U * (H * S - S * Hres + R₂ * (1 + ε • S))

/-- The exact residual has a factor `ε²`; this proves the order of the
algebraic remainder without asserting bounds on its coefficient. -/
theorem scaled_residual_identity (ε : ℝ) (D H Hres S R₂ : R) :
    (D + ε • H + ε ^ 2 • R₂) * (1 + ε • S) -
        ε • (D * S - S * D + H - Hres) -
        (1 + ε • S) * (D + ε • Hres) =
      ε ^ 2 • (H * S - S * Hres + R₂ * (1 + ε • S)) := by
  simp only [mul_add, add_mul, mul_one, one_mul,
    smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
  module

/-- Exact transformed generator `D + ε Hres + ε² Rtilde`. Invertibility and
coefficient bounds can be established separately before using this identity. -/
theorem scaled_transformed_generator_identity (ε : ℝ) (D H Hres S R₂ U : R)
    (hleft : U * (1 + ε • S) = 1) :
    U * ((D + ε • H + ε ^ 2 • R₂) * (1 + ε • S) -
        ε • (D * S - S * D + H - Hres)) =
      D + ε • Hres + ε ^ 2 • transformedRemainder ε H Hres S R₂ U := by
  have hres := scaled_residual_identity ε D H Hres S R₂
  have hsplit :
      (D + ε • H + ε ^ 2 • R₂) * (1 + ε • S) -
          ε • (D * S - S * D + H - Hres) =
        (1 + ε • S) * (D + ε • Hres) +
          ε ^ 2 • (H * S - S * Hres + R₂ * (1 + ε • S)) := by
    exact (sub_eq_iff_eq_add.mp hres).trans (add_comm _ _)
  rw [hsplit, mul_add, ← mul_assoc, hleft, one_mul, mul_smul_comm]
  rfl

end ScaledIdentity

section NormBounds

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- A direct bound on the coefficient of the exact quadratic residual. -/
theorem norm_transformedRemainder_le (ε : ℝ) (H Hres S R₂ U : R) :
    ‖transformedRemainder ε H Hres S R₂ U‖ ≤
      ‖U‖ * (‖H‖ * ‖S‖ + ‖S‖ * ‖Hres‖ + ‖R₂‖ * (‖(1 : R)‖ + ‖ε • S‖)) := by
  have hsum :
      ‖H * S - S * Hres + R₂ * (1 + ε • S)‖ ≤
        ‖H * S‖ + ‖S * Hres‖ + ‖R₂ * (1 + ε • S)‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hproducts :
      ‖H * S‖ + ‖S * Hres‖ + ‖R₂ * (1 + ε • S)‖ ≤
        ‖H‖ * ‖S‖ + ‖S‖ * ‖Hres‖ + ‖R₂‖ * (‖(1 : R)‖ + ‖ε • S‖) :=
    add_le_add (add_le_add (norm_mul_le H S) (norm_mul_le S Hres))
      ((norm_mul_le R₂ (1 + ε • S)).trans
        (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg R₂)))
  exact (norm_mul_le U _).trans
    (mul_le_mul_of_nonneg_left (hsum.trans hproducts) (norm_nonneg U))

/-- The smallness condition ensures an actual two-sided inverse by the
convergent Neumann series. This is not an assumed inverse matrix. -/
theorem exists_inverse_nearIdentity [CompleteSpace R] (ε : ℝ) (S : R)
    (hsmall : ‖ε • S‖ < 1) :
    ∃ U : R, U * (1 + ε • S) = 1 ∧ (1 + ε • S) * U = 1 := by
  have hneg : ‖-(ε • S)‖ < 1 := by simpa only [norm_neg] using hsmall
  have hunit : IsUnit (1 + ε • S) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hneg
  rcases hunit with ⟨u, hu⟩
  refine ⟨↑(u⁻¹), ?_, ?_⟩
  · rw [← hu]
    simp
  · rw [← hu]
    simp

/-- The conventional half-unit smallness bound gives a uniform inverse bound. -/
theorem norm_inverse_nearIdentity_le_two [NormOneClass R]
    (ε : ℝ) (S U : R) (hleft : U * (1 + ε • S) = 1)
    (hsmall : ‖ε • S‖ ≤ 1 / 2) : ‖U‖ ≤ 2 := by
  have heq : U = 1 - U * (ε • S) := by
    have h := hleft
    rw [mul_add, mul_one] at h
    exact eq_sub_of_add_eq h
  have hnorm : ‖U‖ ≤ 1 + ‖U‖ * ‖ε • S‖ := by
    calc
      ‖U‖ = ‖1 - U * (ε • S)‖ := congrArg norm heq
      _ ≤ ‖(1 : R)‖ + ‖U * (ε • S)‖ := norm_sub_le _ _
      _ ≤ 1 + ‖U‖ * ‖ε • S‖ := by
        simpa only [norm_one] using
          add_le_add (le_refl ‖(1 : R)‖) (norm_mul_le U (ε • S))
  have hprod := mul_le_mul_of_nonneg_left hsmall (norm_nonneg U)
  nlinarith

end NormBounds

end Powerlib.Parametric.NormalForm
