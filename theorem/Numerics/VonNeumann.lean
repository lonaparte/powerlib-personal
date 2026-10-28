import theorem.Attributes
import dependencies.Mathlib

/-! # Von Neumann (Fourier) analysis of two explicit finite-difference schemes

Growth factors of the FTCS heat scheme and the first-order upwind advection scheme, derived from
the stencils, and the von Neumann conditions under which no Fourier mode is amplified.

Model boundary.
* Schemes act on complex grid functions `u : ℤ → ℂ` (infinite uniform grid, no boundary), one
  explicit time step:
  * FTCS for `u_t = ν u_xx`: `u_j ↦ u_j + λ (u_{j+1} - 2u_j + u_{j-1})`, `λ = νΔt/Δx²`;
  * first-order upwind for `u_t + c u_x = 0`, `c > 0`: `u_j ↦ u_j - σ (u_j - u_{j-1})`,
    `σ = cΔt/Δx`.
* Fourier modes `e^{ijθ}` are eigenfunctions; the growth factors are derived from the stencils
  (`ftcs_mode`, `upwind_mode`), not assumed. The von Neumann conditions characterize when no
  mode is amplified; the `ℓ²`-norm stability of the full scheme (Parseval) is not formalized.

Source: work-sync theory/T-method-of-lines.md §1.5.4 (examples 1 and 2).

Results.
* `ftcs_growthFactor_bound_iff` — `(∀ θ, |ξ(θ)| ≤ 1) ↔ 0 ≤ λ ≤ 1/2`, `ξ = 1 - 4λ sin²(θ/2)`.
* `upwind_growthFactor_bound_iff` — `(∀ θ, ‖ξ(θ)‖ ≤ 1) ↔ 0 ≤ σ ≤ 1`, with
  `‖ξ‖² = 1 - 2σ(1-σ)(1 - cos θ)`.
* `ftcs_iterate_mode`, `upwind_iterate_mode` — `n` steps multiply a mode by `ξⁿ`.
-/

noncomputable section
namespace powerlib.Numerics
open Complex

/-- The Fourier mode `j ↦ e^{ijθ}`. -/
def fourierMode (θ : ℝ) (j : ℤ) : ℂ := exp (((j : ℝ) * θ : ℝ) * I)

/-- One FTCS step for the heat equation. -/
def ftcs (lam : ℝ) (u : ℤ → ℂ) (j : ℤ) : ℂ := u j + lam * (u (j + 1) - 2 * u j + u (j - 1))

/-- One first-order upwind step for the advection equation. -/
def upwind (σ : ℝ) (u : ℤ → ℂ) (j : ℤ) : ℂ := u j - σ * (u j - u (j - 1))

def ftcsFactor (lam θ : ℝ) : ℝ := 1 - 4 * lam * Real.sin (θ / 2) ^ 2

def upwindFactor (σ θ : ℝ) : ℂ := 1 - σ * (1 - exp ((-θ : ℝ) * I))

@[powerlib_foundation] private lemma fourierMode_shift (θ : ℝ) (j : ℤ) (d : ℤ) :
    fourierMode θ (j + d) = fourierMode θ j * exp (((d : ℝ) * θ : ℝ) * I) := by
  simp only [fourierMode, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem ftcs_mode (lam θ : ℝ) :
    ftcs lam (fourierMode θ) = fun j => (ftcsFactor lam θ : ℂ) * fourierMode θ j := by
  funext j
  have h1 : fourierMode θ (j + 1) = fourierMode θ j * exp (θ * I) := by
    rw [fourierMode_shift]; simp
  have h2 : fourierMode θ (j - 1) = fourierMode θ j * exp (-θ * I) := by
    rw [sub_eq_add_neg, fourierMode_shift]; simp
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_sq_add_sin_sq (θ / 2)
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    simp only [show 2 * (θ / 2) / 2 = θ / 2 by ring]
    linarith
  have hc : exp (θ * I) + exp (-θ * I) = 2 * (1 - 2 * Complex.sin ((θ : ℂ) / 2) ^ 2) := by
    have h := Complex.cos.eq_1 (θ : ℂ)
    rw [← Complex.ofReal_cos, hcos] at h
    push_cast at h
    linear_combination -2 * h
  simp only [ftcs]
  rw [h1, h2, ftcsFactor]
  push_cast
  linear_combination (↑lam * fourierMode θ j) * hc

@[powerlib_foundation] theorem upwind_mode (σ θ : ℝ) :
    upwind σ (fourierMode θ) = fun j => upwindFactor σ θ * fourierMode θ j := by
  funext j
  have h2 := fourierMode_shift θ j (-1)
  simp only [upwind]
  rw [sub_eq_add_neg j 1, h2, upwindFactor]
  push_cast
  ring_nf

@[powerlib_foundation] theorem ftcs_iterate_mode (lam θ : ℝ) (n : ℕ) :
    (ftcs lam)^[n] (fourierMode θ) = fun j => (ftcsFactor lam θ : ℂ) ^ n * fourierMode θ j := by
  induction n with
  | zero => funext j; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext j
    simp only [ftcs]
    have := congrFun (ftcs_mode lam θ) j
    simp only [ftcs] at this
    linear_combination (↑(ftcsFactor lam θ) : ℂ) ^ n * this

@[powerlib_foundation] theorem upwind_iterate_mode (σ θ : ℝ) (n : ℕ) :
    (upwind σ)^[n] (fourierMode θ) = fun j => upwindFactor σ θ ^ n * fourierMode θ j := by
  induction n with
  | zero => funext j; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext j
    have := congrFun (upwind_mode σ θ) j
    simp only [upwind] at this ⊢
    linear_combination upwindFactor σ θ ^ n * this

/-- Parabolic CFL condition: FTCS amplifies no Fourier mode iff `0 ≤ λ ≤ 1/2`. -/
@[powerlib_foundation] theorem ftcs_growthFactor_bound_iff (lam : ℝ) :
    (∀ θ : ℝ, |ftcsFactor lam θ| ≤ 1) ↔ 0 ≤ lam ∧ lam ≤ 1 / 2 := by
  constructor
  · intro h
    have hπ := h Real.pi
    rw [ftcsFactor, Real.sin_pi_div_two, abs_le] at hπ
    constructor <;> nlinarith [hπ.1, hπ.2]
  · rintro ⟨h0, h1⟩ θ
    have hs0 : 0 ≤ Real.sin (θ / 2) ^ 2 := sq_nonneg _
    have hs1 : Real.sin (θ / 2) ^ 2 ≤ 1 := Real.sin_sq_le_one _
    rw [ftcsFactor, abs_le]
    constructor <;> nlinarith

@[powerlib_foundation] theorem upwindFactor_normSq (σ θ : ℝ) :
    normSq (upwindFactor σ θ) = 1 - 2 * σ * (1 - σ) * (1 - Real.cos θ) := by
  have hre : (upwindFactor σ θ).re = 1 - σ * (1 - Real.cos θ) := by
    simp [upwindFactor, Complex.exp_re, Complex.mul_re]
  have him : (upwindFactor σ θ).im = -(σ * Real.sin θ) := by
    simp [upwindFactor, Complex.exp_im, Complex.mul_im]
  rw [normSq_apply, hre, him]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination σ ^ 2 * this

/-- Hyperbolic CFL condition: first-order upwind amplifies no Fourier mode iff
`0 ≤ σ ≤ 1`. -/
@[powerlib_foundation] theorem upwind_growthFactor_bound_iff (σ : ℝ) :
    (∀ θ : ℝ, ‖upwindFactor σ θ‖ ≤ 1) ↔ 0 ≤ σ ∧ σ ≤ 1 := by
  have key : ∀ θ, ‖upwindFactor σ θ‖ ≤ 1 ↔ 0 ≤ σ * (1 - σ) * (1 - Real.cos θ) := by
    intro θ
    rw [← sq_le_one_iff₀ (norm_nonneg _), ← normSq_eq_norm_sq, upwindFactor_normSq]
    constructor <;> intro h <;> linarith
  simp only [key]
  constructor
  · intro h
    have hπ := h Real.pi
    rw [Real.cos_pi] at hπ
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩ θ
    have hc : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    have : 0 ≤ σ * (1 - σ) := mul_nonneg h0 (by linarith)
    exact mul_nonneg this hc

end powerlib.Numerics
