import theorem.Information.Finite
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Maximum caliber on finite path spaces, tilted transition matrices, OU action

Source: work-sync `theory/T-maximum-caliber.md` — boxed path MaxEnt form (head), §1.1 (finite
path enumeration with reference `P₀`), §1.2 (Onsager–Machlup action, OU example), §1.3
(transfer-matrix construction of the MaxCal transition matrix).

Foundation (general probability / calculus), not an engineering result.

Model boundary.
* Path MaxEnt: a *finite* path space `Γ = Fin (n+1) → S` with `S` finite, a strictly positive
  reference path weight `P₀`, a path functional `F` and multiplier `λ`. The caliber is
  `-klSum P P₀`. Continuous-time path measures (Wiener measure, Girsanov densities) are not
  formalised.
* Transfer matrix: `T i j ≥ 0`, a strictly positive right eigenvector `T u = ρ u`, `ρ > 0`
  (Perron–Frobenius existence is *assumed*, not proved). `tiltedTransition` is
  `P i j = T i j u j / (ρ u i)`.
* OU: deterministic scalar path `x(t) = x₀ e^{-θ t}` of `ẋ = -θ x`, Girsanov Lagrangian
  `(ẋ - μ(x))² / (2σ²)` with `μ(x) = -θ x`, tube (Jacobian-corrected) Lagrangian adds
  `μ'(x)/2 = -θ/2`. Time horizon `[0, T]`, continuous time. No stochastic integral appears: the
  action is evaluated on the deterministic mean path only.
-/

noncomputable section
namespace powerlib.Information
open Real Finset

section PathMaxEnt

variable {S : Type*} [Fintype S] {n : ℕ}

/-- Tilted path weight `P₀[Γ] exp(-λ F[Γ]) / 𝒵` on the finite path space `Fin (n+1) → S`. -/
def tiltedPath (P₀ : (Fin (n + 1) → S) → ℝ) (F : (Fin (n + 1) → S) → ℝ) (lam : ℝ) :
    (Fin (n + 1) → S) → ℝ :=
  gibbsVec P₀ fun Γ => -lam * F Γ

/-- **Maximum caliber on a finite path space.** Among all path distributions with the same mean
path functional `⟨F⟩`, the tilted path weight has the largest caliber `-KL(P‖P₀)`, uniquely. -/
@[powerlib_foundation] theorem tiltedPath_maxCaliber [Nonempty S]
    {P₀ F : (Fin (n + 1) → S) → ℝ} {lam : ℝ} (hP₀ : ∀ Γ, 0 < P₀ Γ)
    {P : (Fin (n + 1) → S) → ℝ} (hP : ∀ Γ, 0 ≤ P Γ) (hP1 : ∑ Γ, P Γ = 1)
    (hF : ∑ Γ, P Γ * F Γ = ∑ Γ, tiltedPath P₀ F lam Γ * F Γ) :
    -klSum P P₀ ≤ -klSum (tiltedPath P₀ F lam) P₀ ∧
      (-klSum P P₀ = -klSum (tiltedPath P₀ F lam) P₀ ↔ P = tiltedPath P₀ F lam) := by
  have hmom : ∑ Γ, P Γ * (-lam * F Γ) = ∑ Γ, tiltedPath P₀ F lam Γ * (-lam * F Γ) := by
    simp only [mul_left_comm _ (-lam), ← Finset.mul_sum, hF]
  refine ⟨neg_le_neg (klSum_gibbsVec_le hP₀ hP hP1 hmom), ?_⟩
  rw [neg_inj]
  exact klSum_eq_klSum_gibbsVec_iff hP₀ hP hP1 hmom

end PathMaxEnt

section Transfer

variable {S : Type*}

/-- MaxCal transition matrix from a tilted transfer matrix and its Perron data. -/
def tiltedTransition (T : S → S → ℝ) (u : S → ℝ) (ρ : ℝ) (i j : S) : ℝ :=
  T i j * u j / (ρ * u i)

/-- `P(λ)` is a stochastic matrix. -/
@[powerlib_foundation] theorem tiltedTransition_stochastic [Fintype S] {T : S → S → ℝ} {u : S → ℝ} {ρ : ℝ}
    (hT : ∀ i j, 0 ≤ T i j) (hu : ∀ i, 0 < u i) (hρ : 0 < ρ)
    (heig : ∀ i, ∑ j, T i j * u j = ρ * u i) :
    (∀ i j, 0 ≤ tiltedTransition T u ρ i j) ∧ ∀ i, ∑ j, tiltedTransition T u ρ i j = 1 := by
  refine ⟨fun i j => div_nonneg (mul_nonneg (hT i j) (hu j).le) (mul_pos hρ (hu i)).le,
    fun i => ?_⟩
  simp only [tiltedTransition, ← Finset.sum_div, heig]
  exact div_self (mul_pos hρ (hu i)).ne'

/-- Path probabilities of `P(λ)` are the tilted path weights up to the boundary factor
`u(s_n) / (ρⁿ u(s_0))`. -/
@[powerlib_foundation] theorem prod_tiltedTransition {T : S → S → ℝ} {u : S → ℝ} {ρ : ℝ}
    (hu : ∀ i, 0 < u i) (hρ : 0 < ρ) (s : ℕ → S) (n : ℕ) :
    ∏ k ∈ range n, tiltedTransition T u ρ (s k) (s (k + 1)) =
      (∏ k ∈ range n, T (s k) (s (k + 1))) * u (s n) / (ρ ^ n * u (s 0)) := by
  induction n with
  | zero => simp [div_self (hu (s 0)).ne']
  | succ n ih =>
    rw [prod_range_succ, ih, prod_range_succ, tiltedTransition]
    have h1 := (hu (s n)).ne'
    have h2 := (hu (s 0)).ne'
    have h3 := hρ.ne'
    field_simp
    ring

end Transfer

section OU

/-- Girsanov (path-measure) Onsager–Machlup Lagrangian `(v - μ(x))² / (2σ²)`. -/
def girsanovLagrangian (μ : ℝ → ℝ) (σ : ℝ) (x v : ℝ) : ℝ := (v - μ x) ^ 2 / (2 * σ ^ 2)

@[powerlib_foundation] theorem girsanovLagrangian_nonneg (μ : ℝ → ℝ) (σ x v : ℝ) :
    0 ≤ girsanovLagrangian μ σ x v := by
  unfold girsanovLagrangian; positivity

@[powerlib_foundation] theorem girsanovLagrangian_eq_zero_iff (μ : ℝ → ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (x v : ℝ) : girsanovLagrangian μ σ x v = 0 ↔ v = μ x := by
  unfold girsanovLagrangian
  rw [div_eq_zero_iff, or_iff_left (by positivity), pow_eq_zero_iff two_ne_zero, sub_eq_zero]

/-- OU mean path `x(t) = x₀ e^{-θ t}`. -/
def ouMean (θ x₀ : ℝ) (t : ℝ) : ℝ := x₀ * exp (-θ * t)

@[powerlib_foundation] theorem hasDerivAt_ouMean (θ x₀ t : ℝ) :
    HasDerivAt (ouMean θ x₀) (-θ * ouMean θ x₀ t) t := by
  have h := ((hasDerivAt_id t).const_mul (-θ)).exp.const_mul x₀
  convert h using 1
  · ext s; simp [ouMean]
  · simp [ouMean]; ring

/-- On the OU mean path the Girsanov action vanishes. -/
@[powerlib_foundation] theorem ou_girsanovAction_mean (θ σ x₀ T : ℝ) :
    ∫ t in (0 : ℝ)..T, girsanovLagrangian (fun x => -θ * x) σ (ouMean θ x₀ t)
      (deriv (ouMean θ x₀) t) = 0 := by
  have : ∀ t, girsanovLagrangian (fun x => -θ * x) σ (ouMean θ x₀ t)
      (deriv (ouMean θ x₀) t) = 0 := by
    intro t
    rw [(hasDerivAt_ouMean θ x₀ t).deriv, girsanovLagrangian]
    simp
  simp only [this, intervalIntegral.integral_zero]

/-- **OU tube action** (Jacobian term `μ'(x)/2 = -θ/2` included): `S = -θ T / 2` on the mean
path. -/
@[powerlib_foundation] theorem ou_tubeAction_mean (θ σ x₀ T : ℝ) :
    ∫ t in (0 : ℝ)..T, (girsanovLagrangian (fun x => -θ * x) σ (ouMean θ x₀ t)
      (deriv (ouMean θ x₀) t) + deriv (fun x => -θ * x) (ouMean θ x₀ t) / 2) = -θ * T / 2 := by
  have : ∀ t, girsanovLagrangian (fun x => -θ * x) σ (ouMean θ x₀ t)
      (deriv (ouMean θ x₀) t) + deriv (fun x => -θ * x) (ouMean θ x₀ t) / 2 = -θ / 2 := by
    intro t
    rw [(hasDerivAt_ouMean θ x₀ t).deriv, girsanovLagrangian]
    simp
  simp only [this, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

end OU

end powerlib.Information
