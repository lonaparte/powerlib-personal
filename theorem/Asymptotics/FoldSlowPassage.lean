import theorem.Asymptotics.GaussianMoments

/-! # Fold slow passage: the inner Riccati problem and its solvability condition

Foundation layer. The objects are the rescaled scalar inner problems of the fold slow-passage
note, written as explicit real ODEs in the inner time `τ`:
* grazing (quadratic-tangency) inner problem `X' = λ - τ² + X²` (`riccatiGraze`);
* constant-rate ramp inner problem `X' = λ + τ + X²` (`riccatiRamp`).

`λ` is the rescaled margin parameter (not an eigenvalue), `X` the rescaled fast variable.
These are formal scalar ODEs; their derivation from a particular converter fold, the
`ν`-expansion `ε_c/ε_qs = 1 + ν + C₂ ν² + O(ν³)`, the value `C₂ = 3/8` and the claim that
`λ = 1` is the escape threshold are **not** formalized here.

Results:
* `X = τ` solves the grazing problem iff `λ = 1` (`id_solves_riccatiGraze_iff`).
* Exact linearization along the separatrix: `X = τ + η` solves it iff
  `η' = 2τη + (λ - 1) + η²` (so in the pure inner problem `φ = η²`).
* The adjoint weight `ζ = e^{-τ²}` solves `ζ' = -2τζ`, `∫ e^{-τ²} = √π`.
* The solvability functional `λ* = 1 - π^{-1/2} ∫ e^{-τ²} φ(τ) dτ`: equals `1` for every odd
  `φ`, equals `1/2` for `φ = τ²`.
* Constant-rate ramp: time translation `τ ↦ τ + λ` maps solutions of `X' = τ + X²` onto
  solutions of `X' = λ + τ + X²` and back, so `λ` cannot act as a threshold parameter.
* Riccati–Schrödinger link: if `u ≠ 0` solves `-u'' + τ² u = λ u`, then `X = -u'/u` solves the
  grazing problem; the ground state `u = e^{-τ²/2}` has `λ = 1` and gives `X = τ`.

Source: work-sync theory/T-fold-slow-passage.md §1.1–§1.3, §2.3;
projects/basin-guard/notes/concepts/fold-slow-passage.md §2 and "作用域 (a)".
The note's error-propagation remark (§1.5: a 0.2 % error on `F ≈ 1.1` at `ν = 0.1`) is
arithmetic, not a theorem; it is not stated here.
-/

noncomputable section
namespace powerlib.Asymptotics

open Real MeasureTheory

/-- Right-hand side of the grazing inner problem `X' = λ - τ² + X²`. -/
def riccatiGraze (lam τ X : ℝ) : ℝ := lam - τ ^ 2 + X ^ 2

/-- Right-hand side of the constant-rate ramp inner problem `X' = λ + τ + X²`. -/
def riccatiRamp (lam τ X : ℝ) : ℝ := lam + τ + X ^ 2

/-- Solvability shift `λ* = 1 - π^{-1/2} ∫ e^{-τ²} φ(τ) dτ` of a perturbation `φ`
evaluated on the separatrix. -/
def solvabilityShift (φ : ℝ → ℝ) : ℝ :=
  1 - (Real.sqrt π)⁻¹ * ∫ τ : ℝ, Real.exp (-τ ^ 2) * φ τ

/-- The unperturbed separatrix `X = τ` is an exact solution exactly when `λ = 1`. -/
@[powerlib_foundation] theorem id_solves_riccatiGraze_iff (lam : ℝ) :
    (∀ τ, HasDerivAt (fun τ : ℝ => τ) (riccatiGraze lam τ τ) τ) ↔ lam = 1 := by
  constructor
  · intro h
    have h0 := (h 0).unique (hasDerivAt_id' 0)
    simpa [riccatiGraze] using h0
  · rintro rfl τ
    simpa [riccatiGraze] using hasDerivAt_id' τ

/-- Exact linearization along the separatrix: `X = τ + η` solves `X' = λ - τ² + X²` at `τ`
iff `η' = 2τη + (λ - 1) + η²` there. -/
@[powerlib_foundation] theorem riccatiGraze_shift_iff (lam : ℝ) {η : ℝ → ℝ} {η' τ : ℝ} :
    HasDerivAt (fun s => s + η s) (riccatiGraze lam τ (τ + η τ)) τ ∧ HasDerivAt η η' τ ↔
      HasDerivAt η η' τ ∧ η' = 2 * τ * η τ + (lam - 1) + η τ ^ 2 := by
  constructor
  · rintro ⟨hX, hη⟩
    refine ⟨hη, ?_⟩
    have h2 := (hasDerivAt_id' τ).add hη
    have := hX.unique h2
    simp only [riccatiGraze] at this
    linarith
  · rintro ⟨hη, rfl⟩
    refine ⟨?_, hη⟩
    have h2 := (hasDerivAt_id' τ).add hη
    convert h2 using 1
    simp only [riccatiGraze]
    ring

/-- The adjoint of `η' = 2τη` is solved by the Gaussian weight: `ζ = e^{-τ²}`, `ζ' = -2τζ`. -/
@[powerlib_foundation] theorem hasDerivAt_adjointWeight (τ : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2)) (-2 * τ * Real.exp (-τ ^ 2)) τ := by
  have h := ((hasDerivAt_pow 2 τ).neg).exp
  convert h using 1
  simp; ring

/-- Parity: every odd perturbation leaves the threshold at `λ* = 1`. -/
@[powerlib_foundation] theorem solvabilityShift_odd {φ : ℝ → ℝ} (hφ : ∀ τ, φ (-τ) = -φ τ) :
    solvabilityShift φ = 1 := by
  rw [solvabilityShift, integral_exp_neg_sq_mul_odd hφ, mul_zero, sub_zero]

/-- The even test perturbation `φ = τ²` gives `λ* = 1/2`. -/
@[powerlib_foundation] theorem solvabilityShift_sq :
    solvabilityShift (fun τ => τ ^ 2) = 1 / 2 := by
  have h : ∫ τ : ℝ, Real.exp (-τ ^ 2) * τ ^ 2 = Real.sqrt π / 2 := by
    rw [← integral_sq_mul_exp_neg_sq]
    congr 1
    funext τ
    ring
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  rw [solvabilityShift, h]
  field_simp
  ring

/-- A constant perturbation `φ = c` shifts the threshold by exactly `-c`
(normalization `∫ e^{-τ²} = √π`). -/
@[powerlib_foundation] theorem solvabilityShift_const (c : ℝ) :
    solvabilityShift (fun _ => c) = 1 - c := by
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  rw [solvabilityShift, integral_mul_const, integral_exp_neg_sq]
  field_simp

/-- Constant-rate ramp: if `X` solves `X' = τ + X²`, then `Y(τ) = X(τ + λ)` solves
`Y' = λ + τ + Y²`. The margin parameter is absorbed by a time translation. -/
@[powerlib_foundation] theorem riccatiRamp_shift {X : ℝ → ℝ}
    (hX : ∀ τ, HasDerivAt X (riccatiRamp 0 τ (X τ)) τ) (lam : ℝ) :
    ∀ τ, HasDerivAt (fun s => X (s + lam)) (riccatiRamp lam τ (X (τ + lam))) τ := by
  intro τ
  have h := (hX (τ + lam)).comp τ ((hasDerivAt_id' τ).add_const lam)
  rw [show riccatiRamp lam τ (X (τ + lam)) = riccatiRamp 0 (τ + lam) (X (τ + lam)) * 1 by
    simp only [riccatiRamp]; ring]
  exact h

/-- Converse of `riccatiRamp_shift`: every solution of the ramp problem with parameter `λ` is
a time translate of a solution with `λ = 0`. -/
@[powerlib_foundation] theorem riccatiRamp_unshift {Y : ℝ → ℝ} (lam : ℝ)
    (hY : ∀ τ, HasDerivAt Y (riccatiRamp lam τ (Y τ)) τ) :
    ∀ τ, HasDerivAt (fun s => Y (s - lam)) (riccatiRamp 0 τ (Y (τ - lam))) τ := by
  intro τ
  have h := (hY (τ - lam)).comp τ ((hasDerivAt_id' τ).sub_const lam)
  rw [show riccatiRamp 0 τ (Y (τ - lam)) = riccatiRamp lam (τ - lam) (Y (τ - lam)) * 1 by
    simp only [riccatiRamp]; ring]
  exact h

/-- Riccati–Schrödinger link: a nonvanishing solution of `-u'' + τ² u = λ u` gives the
solution `X = -u'/u` of the grazing inner problem. -/
@[powerlib_foundation] theorem riccatiGraze_of_schrodinger {lam : ℝ} {u u' : ℝ → ℝ} {τ : ℝ}
    (hu : ∀ s, HasDerivAt u (u' s) s) (hu' : HasDerivAt u' ((τ ^ 2 - lam) * u τ) τ)
    (hne : u τ ≠ 0) :
    HasDerivAt (fun s => -u' s / u s) (riccatiGraze lam τ (-u' τ / u τ)) τ := by
  have h := (hu'.neg).div (hu τ) hne
  convert h using 1
  simp only [riccatiGraze, Pi.neg_apply]
  field_simp
  ring

/-- The Gaussian ground state `u = e^{-τ²/2}` solves `-u'' + τ² u = u` (eigenvalue `λ = 1`). -/
@[powerlib_foundation] theorem groundState_schrodinger (τ : ℝ) :
    HasDerivAt (fun s : ℝ => -s * Real.exp (-s ^ 2 / 2))
      ((τ ^ 2 - 1) * Real.exp (-τ ^ 2 / 2)) τ ∧
    (∀ s, HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2)) (-s * Real.exp (-s ^ 2 / 2)) s) := by
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2))
      (-s * Real.exp (-s ^ 2 / 2)) s := by
    intro s
    have h := (((hasDerivAt_pow 2 s).neg).div_const 2).exp
    convert h using 1
    simp; ring
  refine ⟨?_, hg⟩
  have h := ((hasDerivAt_id' τ).neg).mul (hg τ)
  convert h using 1
  simp; ring

/-- The ground state reproduces the separatrix: `-u'/u = τ` for `u = e^{-τ²/2}`. -/
@[powerlib_foundation] theorem groundState_logDeriv (τ : ℝ) :
    -(-τ * Real.exp (-τ ^ 2 / 2)) / Real.exp (-τ ^ 2 / 2) = τ := by
  have := Real.exp_pos (-τ ^ 2 / 2)
  field_simp

end powerlib.Asymptotics
