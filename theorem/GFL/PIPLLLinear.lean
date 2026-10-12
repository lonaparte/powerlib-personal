import theorem.GFL.PIPLL

/-! # Linearization structure of the PI-PLL with general phase detector (foundation)

Matrix-level facts about the Jacobian `J = [[K_p g, K_i], [g, 0]]` (`g = h'(θ*)`) of
`piPLLField h K_p K_i δω` (`theorem/GFL/PIPLL.lean`), and their transfer to the Jacobian of the
field itself through `fderiv`. These are linearization facts (static foundation); the model boundary is
the one of `theorem/GFL/PIPLL.lean`. The module states no behaviour: the family and its connection
conclusions are in `theorem/GFL/PIPLLFamily.lean`. Every result here is static evidence on the
model, not a connection conclusion.

* Node / focus: for `g < 0`, `K_p ≠ 0`, all eigenvalues are real iff `|g| ≥ 4 K_i / K_p²`
  (discriminant `tr² − 4 det = K_p² g² + 4 K_i g`); otherwise there is a non-real eigenvalue.
* No nonzero purely imaginary eigenvalue (`K_p ≠ 0`), at every equilibrium and in fact at every
  point of the state space. With `K_p = 0` this fails: `K_i g < 0` gives `± j √(−K_i g)`.
* `tr J = 0 ∧ det J > 0` has no solution (`K_p ≠ 0`): the parameter image of the linearization
  never meets the Hopf curve, because `tr J = K_p g` and `det J = −K_i g` are both proportional
  to `g`.

Source: work-sync `theory/T-gfl-dynamics.md` §1.10 (node/focus table), §1.12 (`Σ_DOC`), §1.13
("no Hopf in form B"); `theory/T-bogdanov-takens-bifurcation.md` §1.5–§1.6;
`projects/vsc-stochastic-stability/notes/concepts/equilibria-and-bifurcation.md` §3.
Correction (precondition): the "no Hopf / no purely imaginary eigenvalue" claim needs
`K_p ≠ 0`; the notes leave it implicit (`K_p > 0` throughout). The absence of Hopf is shown here
only at the level of the linearization (no eigenvalue crossing at `± jω`, `ω ≠ 0`); nothing is
claimed about limit cycles of the nonlinear field.
-/

noncomputable section
namespace powerlib.GFL
open Matrix
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Characteristic equation `μ² − K_p g μ − K_i g = 0` of every eigenvalue of the Jacobian. -/
@[powerlib_foundation] theorem piPLLJacobian_eigenvalue_char {Kp Ki g : ℝ} {μ : ℂ}
    {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heig : (piPLLJacobian Kp Ki g).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ ^ 2 - (Kp * g : ℝ) * μ - (Ki * g : ℝ) = 0 := by
  have h := Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _ hv heig
  rw [Criteria.det_characteristicMatrix_fin_two, piPLLJacobian_trace, piPLLJacobian_det] at h
  push_cast at h ⊢
  linear_combination h

/-- Discriminant of the Jacobian: `tr² − 4 det = K_p² g² + 4 K_i g`. -/
@[powerlib_foundation] theorem piPLLJacobian_discriminant (Kp Ki g : ℝ) :
    (piPLLJacobian Kp Ki g).trace ^ 2 - 4 * (piPLLJacobian Kp Ki g).det =
      Kp ^ 2 * g ^ 2 + 4 * Ki * g := by
  simp only [piPLLJacobian_trace, piPLLJacobian_det]
  ring

/-- Node/focus split at a slope `g < 0`: all eigenvalues are real (node) iff
`|g| ≥ 4 K_i / K_p²`. -/
@[powerlib_foundation] theorem piPLLJacobian_eigenvalues_real_iff {Kp Ki g : ℝ} (hKp : Kp ≠ 0)
    (hg : g < 0) :
    (∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
        (piPLLJacobian Kp Ki g).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.im = 0) ↔
      4 * Ki / Kp ^ 2 ≤ |g| := by
  rw [Criteria.eigenvalues_real_iff_discriminant_nonneg, piPLLJacobian_discriminant,
    abs_of_neg hg]
  have hK2 : 0 < Kp ^ 2 := by positivity
  rw [div_le_iff₀ hK2]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Focus: some eigenvalue is non-real iff `|g| < 4 K_i / K_p²` (for `g < 0`, `K_p ≠ 0`). -/
@[powerlib_foundation] theorem piPLLJacobian_exists_nonreal_eigenvalue_iff {Kp Ki g : ℝ}
    (hKp : Kp ≠ 0) (hg : g < 0) :
    (∃ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧
        (piPLLJacobian Kp Ki g).map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ μ.im ≠ 0) ↔
      |g| < 4 * Ki / Kp ^ 2 := by
  rw [← not_le, ← piPLLJacobian_eigenvalues_real_iff hKp hg]
  constructor
  · rintro ⟨μ, v, hv, heig, him⟩ H
    exact him (H μ v hv heig)
  · intro H
    by_contra hc
    apply H
    intro μ v hv heig
    by_contra him
    exact hc ⟨μ, v, hv, heig, him⟩

/-- No nonzero purely imaginary eigenvalue (`K_p ≠ 0`), for every slope `g`. -/
@[powerlib_foundation] theorem piPLLJacobian_imaginary_eigenvalue_eq_zero {Kp Ki g : ℝ}
    (hKp : Kp ≠ 0) {μ : ℂ} {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heig : (piPLLJacobian Kp Ki g).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) (hre : μ.re = 0) :
    μ = 0 := by
  have hc := piPLLJacobian_eigenvalue_char hv heig
  have hr := congrArg Complex.re hc
  have hi := congrArg Complex.im hc
  simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.sub_im, Complex.mul_im, Complex.zero_im, hre] at hr hi
  -- `hr : −ω² − K_i g = 0`, `hi : −K_p g ω = 0` with `ω = μ.im`
  have hω : μ.im = 0 := by
    rcases mul_eq_zero.mp (show (Kp * g) * μ.im = 0 by linarith) with h | h
    · have hg : g = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hKp
        · exact h'
      rw [hg] at hr
      nlinarith [sq_nonneg μ.im]
    · exact h
  exact Complex.ext hre hω

/-- The Hopf condition `tr J = 0 ∧ det J > 0` is never met (`K_p ≠ 0`). -/
@[powerlib_foundation] theorem piPLLJacobian_not_hopf {Kp Ki g : ℝ} (hKp : Kp ≠ 0) :
    ¬ ((piPLLJacobian Kp Ki g).trace = 0 ∧ 0 < (piPLLJacobian Kp Ki g).det) := by
  rintro ⟨htr, hdet⟩
  rw [piPLLJacobian_trace] at htr
  rw [piPLLJacobian_det] at hdet
  rcases mul_eq_zero.mp htr with h | h
  · exact hKp h
  · rw [h, mul_zero, neg_zero] at hdet
    exact lt_irrefl _ hdet

/-- `K_p ≠ 0` is necessary: with `K_p = 0` and `K_i g < 0` the Jacobian has the purely
imaginary eigenvalue `j √(−K_i g)`. -/
@[powerlib_foundation] theorem piPLLJacobian_imaginary_eigenvalue_of_Kp_zero {Ki g : ℝ}
    (h : Ki * g < 0) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (piPLLJacobian 0 Ki g).map (algebraMap ℝ ℂ) *ᵥ v =
        (⟨0, Real.sqrt (-(Ki * g))⟩ : ℂ) • v := by
  apply Criteria.exists_eigenpair_of_quadratic_fin_two
  rw [piPLLJacobian_trace, piPLLJacobian_det]
  have hs := Real.sq_sqrt (show 0 ≤ -(Ki * g) by linarith)
  apply Complex.ext
  · simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re]
    nlinarith
  · simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_im]
    ring

/-! ## Transfer to the Jacobian of the field (`fderiv`) -/

@[powerlib_foundation] theorem toEuclideanCLM_injective_fin_two :
    Function.Injective (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) :=
  Matrix.toEuclideanCLM.injective

/-- Any matrix representing the Jacobian `fderiv` of the PI-PLL field at a point is
`piPLLJacobian K_p K_i (h'(θ))`. -/
@[powerlib_foundation] theorem piPLL_jacobian_matrix_eq {h : ℝ → ℝ} {Kp Ki δω g : ℝ}
    {x : ℝ²} (hh : HasDerivAt h g (x 0)) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : fderiv ℝ (piPLLField h Kp Ki δω) x = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) :
    A = piPLLJacobian Kp Ki g :=
  toEuclideanCLM_injective_fin_two (by
    change Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki g)
    rw [← hA, fderiv_piPLLField hh])

/-- At every point (in particular every equilibrium) of the PI-PLL field with `K_p ≠ 0` and `h`
differentiable there, the linearization has no nonzero purely imaginary eigenvalue. -/
@[powerlib_foundation] theorem piPLL_linearization_no_imaginary_eigenvalue {h : ℝ → ℝ}
    {Kp Ki δω g : ℝ} {x : ℝ²} (hKp : Kp ≠ 0) (hh : HasDerivAt h g (x 0))
    {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : fderiv ℝ (piPLLField h Kp Ki δω) x = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A)
    {μ : ℂ} {v : Fin 2 → ℂ} (hv : v ≠ 0) (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hre : μ.re = 0) : μ = 0 := by
  rw [piPLL_jacobian_matrix_eq hh hA] at heig
  exact piPLLJacobian_imaginary_eigenvalue_eq_zero hKp hv heig hre

/-- The linearization of the PI-PLL field at any point never satisfies the Hopf condition
`tr = 0 ∧ det > 0` (`K_p ≠ 0`). -/
@[powerlib_foundation] theorem piPLL_linearization_not_hopf {h : ℝ → ℝ} {Kp Ki δω g : ℝ}
    {x : ℝ²} (hKp : Kp ≠ 0) (hh : HasDerivAt h g (x 0)) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : fderiv ℝ (piPLLField h Kp Ki δω) x = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) :
    ¬ (A.trace = 0 ∧ 0 < A.det) := by
  rw [piPLL_jacobian_matrix_eq hh hA]
  exact piPLLJacobian_not_hopf hKp

end powerlib.GFL
