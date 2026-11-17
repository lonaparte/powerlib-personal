import theorem.Information.Finite
import theorem.Stochastic.OUMoments
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Maximum caliber on finite path spaces, tilted transition matrices, OU action

Maximum caliber on a finite path space, the MaxCal transition matrix built from a tilted
transfer matrix, and the Onsager–Machlup action of the OU mean path.

Model boundary.
* General probability / calculus, not an engineering result.
* Path MaxEnt: a *finite* path space `Γ = Fin (n+1) → S` with `S` finite, a strictly positive
  reference path weight `P₀`, a path functional `F` and multiplier `λ`. The caliber is
  `-klSum P P₀`. Continuous-time path measures (Wiener measure, Girsanov densities) are not
  formalised.
* Transfer matrix: `T i j ≥ 0`, a strictly positive right eigenvector `T u = ρ u`, `ρ > 0`
  (Perron–Frobenius existence is *assumed*, not proved). `tiltedTransition` is
  `P i j = T i j u j / (ρ u i)`.
* OU: deterministic scalar mean path `x(t) = x₀ e^{-θ t}` of `ẋ = -θ x` (the OU mean
  `ouMean θ 0 x₀`, `theorem/Stochastic/OUMoments.lean`), Girsanov Lagrangian
  `(ẋ - μ(x))² / (2σ²)` with `μ(x) = -θ x`, tube (Jacobian-corrected) Lagrangian adds
  `μ'(x)/2 = -θ/2`. Time horizon `[0, T]`, continuous time. No stochastic integral appears: the
  action is evaluated on the deterministic mean path only.

Source: work-sync theory/T-maximum-caliber.md — boxed path MaxEnt form (head), §1.1 (finite
path enumeration with reference `P₀`), §1.2 (Onsager–Machlup action, OU example), §1.3
(transfer-matrix construction of the MaxCal transition matrix).

Results.
* `tiltedPath` — the tilted path weight is the Gibbs vector of `P₀` with log-tilt `-λ F`, so
  maximum caliber (among all path distributions with the same mean path functional `⟨F⟩` it
  has the largest caliber, uniquely) is `klSum_gibbsVec_le` and `klSum_eq_klSum_gibbsVec_iff`
  of `theorem/Information/Finite.lean` at `g = -λ F`.
* `tiltedTransition_stochastic`, `prod_tiltedTransition` — `P(λ)` is a stochastic matrix, and
  its path probabilities are the tilted path weights up to the boundary factor
  `u(s_n) / (ρⁿ u(s_0))`.
* `ou_girsanovAction_mean`, `ou_tubeAction_mean` — on the OU mean path the Girsanov action
  vanishes, and the tube action (Jacobian term `μ'(x)/2 = -θ/2` included) is `S = -θ T / 2`.
-/

noncomputable section
namespace powerlib.Information
open Real Finset

section PathMaxEnt

variable {S : Type*} [Fintype S] {n : ℕ}

/-- Tilted path weight `P₀[Γ] exp(-λ F[Γ]) / 𝒵` on the finite path space `Fin (n+1) → S`: the
Gibbs vector of `P₀` with log-tilt `-λ F`. Maximum caliber on the finite path space (the tilted
weight has the largest caliber `-KL(P‖P₀)` among the path distributions with its mean `⟨F⟩`,
uniquely) is `klSum_gibbsVec_le` and `klSum_eq_klSum_gibbsVec_iff` at `g = -λ F`. -/
def tiltedPath (P₀ : (Fin (n + 1) → S) → ℝ) (F : (Fin (n + 1) → S) → ℝ) (lam : ℝ) :
    (Fin (n + 1) → S) → ℝ :=
  gibbsVec P₀ fun Γ => -lam * F Γ

end PathMaxEnt

section Transfer

variable {S : Type*}

/-- MaxCal transition matrix from a tilted transfer matrix and its Perron data. -/
def tiltedTransition (T : S → S → ℝ) (u : S → ℝ) (ρ : ℝ) (i j : S) : ℝ :=
  T i j * u j / (ρ * u i)

/-- `P(λ)` is a stochastic matrix. -/
@[tmio T, powerlib_foundation] theorem tiltedTransition_stochastic [Fintype S] {T : S → S → ℝ} {u : S → ℝ}
    {ρ : ℝ} (hT : ∀ i j, 0 ≤ T i j) (hu : ∀ i, 0 < u i) (hρ : 0 < ρ)
    (heig : ∀ i, ∑ j, T i j * u j = ρ * u i) :
    (∀ i j, 0 ≤ tiltedTransition T u ρ i j) ∧ ∀ i, ∑ j, tiltedTransition T u ρ i j = 1 := by
  refine ⟨fun i j => div_nonneg (mul_nonneg (hT i j) (hu j).le) (mul_pos hρ (hu i)).le,
    fun i => ?_⟩
  simp only [tiltedTransition, ← Finset.sum_div, heig]
  exact div_self (mul_pos hρ (hu i)).ne'

/-- Path probabilities of `P(λ)` are the tilted path weights up to the boundary factor
`u(s_n) / (ρⁿ u(s_0))`. -/
@[tmio T, powerlib_foundation] theorem prod_tiltedTransition {T : S → S → ℝ} {u : S → ℝ} {ρ : ℝ}
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

open powerlib.Stochastic.OU (ouMean ouMean_hasDerivAt)

/-- Girsanov (path-measure) Onsager–Machlup Lagrangian `(v - μ(x))² / (2σ²)`. -/
def girsanovLagrangian (μ : ℝ → ℝ) (σ : ℝ) (x v : ℝ) : ℝ := (v - μ x) ^ 2 / (2 * σ ^ 2)

@[tmio T, powerlib_foundation] theorem girsanovLagrangian_nonneg (μ : ℝ → ℝ) (σ x v : ℝ) :
    0 ≤ girsanovLagrangian μ σ x v := by
  unfold girsanovLagrangian; positivity

@[tmio T, powerlib_foundation] theorem girsanovLagrangian_eq_zero_iff (μ : ℝ → ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (x v : ℝ) : girsanovLagrangian μ σ x v = 0 ↔ v = μ x := by
  unfold girsanovLagrangian
  rw [div_eq_zero_iff, or_iff_left (by positivity), pow_eq_zero_iff two_ne_zero, sub_eq_zero]

/-- On the OU mean path the Girsanov action vanishes. -/
@[tmio T, powerlib_foundation] theorem ou_girsanovAction_mean (θ σ x₀ T : ℝ) :
    ∫ t in (0 : ℝ)..T, girsanovLagrangian (fun x => -θ * x) σ (ouMean θ 0 x₀ t)
      (deriv (ouMean θ 0 x₀) t) = 0 := by
  have : ∀ t, girsanovLagrangian (fun x => -θ * x) σ (ouMean θ 0 x₀ t)
      (deriv (ouMean θ 0 x₀) t) = 0 := by
    intro t
    rw [(ouMean_hasDerivAt θ 0 x₀ t).deriv, girsanovLagrangian]
    simp
  simp only [this, intervalIntegral.integral_zero]

/-- **OU tube action** (Jacobian term `μ'(x)/2 = -θ/2` included): `S = -θ T / 2` on the mean
path. -/
@[tmio T, powerlib_foundation] theorem ou_tubeAction_mean (θ σ x₀ T : ℝ) :
    ∫ t in (0 : ℝ)..T, (girsanovLagrangian (fun x => -θ * x) σ (ouMean θ 0 x₀ t)
      (deriv (ouMean θ 0 x₀) t) + deriv (fun x => -θ * x) (ouMean θ 0 x₀ t) / 2) = -θ * T / 2 := by
  have : ∀ t, girsanovLagrangian (fun x => -θ * x) σ (ouMean θ 0 x₀ t)
      (deriv (ouMean θ 0 x₀) t) + deriv (fun x => -θ * x) (ouMean θ 0 x₀ t) / 2 = -θ / 2 := by
    intro t
    rw [(ouMean_hasDerivAt θ 0 x₀ t).deriv, girsanovLagrangian]
    simp
  simp only [this, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

end OU

end powerlib.Information
