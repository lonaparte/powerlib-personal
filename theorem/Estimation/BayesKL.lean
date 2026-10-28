import dependencies.Mathlib
import theorem.Attributes
import theorem.Information.Finite
import Mathlib.Probability.Kernel.Invariance

/-! # Bayesian information identities and Metropolis–Hastings on a finite parameter space

The information gain of a Bayesian update, the ELBO identity of variational inference, and
invariance of the posterior under the Metropolis–Hastings chain, on a finite parameter space.

Scope.
* Probability theory, not an engineering result.
* Finite parameter set `Θ` (`Fintype ι`), strictly positive prior `π` (`Σ π = 1`) and
  likelihood values `L θ = p(D | θ) > 0` at the observed data; evidence `Z = Σ π L`, posterior
  `post = π L / Z`. `klSum` is the discrete relative entropy of
  `theorem/Information/Finite.lean`. The Metropolis–Hastings chain is a stochastic matrix on `ι`.

Source: work-sync theory/T-bayesian-inference.md §1.12 (information gain
`KL(p(θ|D) ‖ p(θ)) = E_{θ|D}[log p(D|θ)] − log p(D)`), §1.14 (a) Metropolis–Hastings acceptance
`α = min{1, p(θ*|D) q(θ|θ*) / (p(θ|D) q(θ*|θ))}`, chain invariant measure = posterior;
(b) variational inference: `ELBO(q) = E_q[log p(θ, D)] − E_q[log q]`, `ELBO ≤ log p(D)`,
gap `= KL(q ‖ p(θ|D))`.

Results.
* `kl_posterior_prior` — `KL(post ‖ π) = Σ post log L − log Z` (§1.12).
* `elbo_add_kl` — `log Z = ELBO(q) + KL(q ‖ post)` for every probability vector `q`;
  `elbo_le_log_evidence`, `elbo_eq_log_evidence_iff`: `ELBO ≤ log Z` with equality iff
  `q = post` (§1.14 (b)).
* `invariant_of_detailedBalance` — detailed balance `π_i P_ij = π_j P_ji` of a stochastic matrix
  implies invariance `Σ_i π_i P_ij = π_j`; `mh_detailedBalance`, `mh_stochastic`,
  `mh_invariant`: the Metropolis–Hastings matrix built from any stochastic proposal satisfies
  detailed balance w.r.t. a positive target, hence leaves it invariant (§1.14 (a)).
* `reversible_invariant` — wrapper of Mathlib `ProbabilityTheory.Kernel.IsReversible.invariant`:
  the same implication for general Markov kernels.
-/

noncomputable section
namespace powerlib.Estimation

open Real Finset powerlib.Information

variable {ι : Type*} [Fintype ι]

/-- Evidence `Z = Σ_θ π(θ) L(θ)`. -/
def finEvidence (p₀ L : ι → ℝ) : ℝ := ∑ i, p₀ i * L i

/-- Posterior `π L / Z`. -/
def finPost (p₀ L : ι → ℝ) (i : ι) : ℝ := p₀ i * L i / finEvidence p₀ L

variable {p₀ L : ι → ℝ}

@[tmio T, powerlib_foundation] theorem finEvidence_pos [Nonempty ι] (hp₀ : ∀ i, 0 < p₀ i)
    (hL : ∀ i, 0 < L i) : 0 < finEvidence p₀ L :=
  sum_pos (fun i _ => mul_pos (hp₀ i) (hL i)) univ_nonempty

@[tmio T, powerlib_foundation] theorem finPost_pos [Nonempty ι] (hp₀ : ∀ i, 0 < p₀ i) (hL : ∀ i, 0 < L i)
    (i : ι) : 0 < finPost p₀ L i :=
  div_pos (mul_pos (hp₀ i) (hL i)) (finEvidence_pos hp₀ hL)

@[tmio T, powerlib_foundation] theorem sum_finPost [Nonempty ι] (hp₀ : ∀ i, 0 < p₀ i) (hL : ∀ i, 0 < L i) :
    ∑ i, finPost p₀ L i = 1 := by
  simp only [finPost, ← sum_div]
  exact div_self (finEvidence_pos hp₀ hL).ne'

/-- **Information gain (§1.12)**: `KL(post ‖ prior) = E_post[log L] − log Z`. -/
@[tmio T, powerlib_foundation] theorem kl_posterior_prior [Nonempty ι] (hp₀ : ∀ i, 0 < p₀ i)
    (hL : ∀ i, 0 < L i) :
    klSum (finPost p₀ L) p₀ = ∑ i, finPost p₀ L i * log (L i) - log (finEvidence p₀ L) := by
  have hZ := finEvidence_pos hp₀ hL
  have h : ∀ i, finPost p₀ L i * log (finPost p₀ L i / p₀ i) =
      finPost p₀ L i * log (L i) - finPost p₀ L i * log (finEvidence p₀ L) := by
    intro i
    rw [show finPost p₀ L i / p₀ i = L i / finEvidence p₀ L by
      simp only [finPost]; field_simp [(hp₀ i).ne'],
      log_div (hL i).ne' hZ.ne']
    ring
  simp only [klSum, h, sum_sub_distrib, ← sum_mul, sum_finPost hp₀ hL, one_mul]

/-- Evidence lower bound `ELBO(q) = Σ q log(π L) − Σ q log q`. -/
def elbo (p₀ L q : ι → ℝ) : ℝ := ∑ i, q i * log (p₀ i * L i) - ∑ i, q i * log (q i)

/-- **ELBO decomposition (§1.14 (b))**: `log Z = ELBO(q) + KL(q ‖ post)` for every probability
vector `q` (`0 log 0 = 0`). -/
@[tmio T, powerlib_foundation] theorem elbo_add_kl [Nonempty ι] (hp₀ : ∀ i, 0 < p₀ i) (hL : ∀ i, 0 < L i)
    {q : ι → ℝ} (hq1 : ∑ i, q i = 1) :
    elbo p₀ L q + klSum q (finPost p₀ L) = log (finEvidence p₀ L) := by
  have hZ := finEvidence_pos hp₀ hL
  have h : ∀ i, q i * log (p₀ i * L i) - q i * log (q i) + q i * log (q i / finPost p₀ L i) =
      q i * log (finEvidence p₀ L) := by
    intro i
    by_cases hqi : q i = 0
    · simp [hqi]
    have hpl : 0 < p₀ i * L i := mul_pos (hp₀ i) (hL i)
    rw [show q i / finPost p₀ L i = q i * finEvidence p₀ L / (p₀ i * L i) by
      simp only [finPost]; field_simp,
      log_div (mul_ne_zero hqi hZ.ne') hpl.ne', log_mul hqi hZ.ne']
    ring
  have hs : elbo p₀ L q + klSum q (finPost p₀ L) =
      ∑ i, (q i * log (p₀ i * L i) - q i * log (q i) + q i * log (q i / finPost p₀ L i)) := by
    simp only [elbo, klSum, sum_add_distrib, sum_sub_distrib]
  rw [hs]
  simp only [h, ← sum_mul, hq1, one_mul]

/-- **`ELBO ≤ log p(D)`**. -/
@[tmio T, powerlib_foundation] theorem elbo_le_log_evidence [Nonempty ι] (hp₀ : ∀ i, 0 < p₀ i)
    (hL : ∀ i, 0 < L i) {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    elbo p₀ L q ≤ log (finEvidence p₀ L) := by
  have := klSum_nonneg hq (finPost_pos hp₀ hL) hq1 (sum_finPost hp₀ hL)
  linarith [elbo_add_kl hp₀ hL hq1]

/-- Equality in the ELBO bound exactly at the posterior: maximizing the ELBO is minimizing
`KL(q ‖ post)`. -/
@[tmio T, powerlib_foundation] theorem elbo_eq_log_evidence_iff [Nonempty ι] (hp₀ : ∀ i, 0 < p₀ i)
    (hL : ∀ i, 0 < L i) {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    elbo p₀ L q = log (finEvidence p₀ L) ↔ q = finPost p₀ L := by
  rw [← klSum_eq_zero_iff hq (finPost_pos hp₀ hL) hq1 (sum_finPost hp₀ hL)]
  have := elbo_add_kl hp₀ hL hq1
  constructor <;> intro h <;> linarith

/-! ## Metropolis–Hastings (§1.14 (a)) -/

/-- Detailed balance `π_i P_ij = π_j P_ji`. -/
def DetailedBalance (p₀ : ι → ℝ) (P : ι → ι → ℝ) : Prop := ∀ i j, p₀ i * P i j = p₀ j * P j i

/-- **Detailed balance ⇒ invariance** for a row-stochastic matrix. -/
@[tmio T, powerlib_foundation] theorem invariant_of_detailedBalance {P : ι → ι → ℝ}
    (hrow : ∀ i, ∑ j, P i j = 1) (hdb : DetailedBalance p₀ P) (j : ι) :
    ∑ i, p₀ i * P i j = p₀ j := by
  simp_rw [hdb _ j, ← mul_sum, hrow, mul_one]

variable [DecidableEq ι]

/-- Metropolis–Hastings acceptance probability `min{1, π_j Q_ji / (π_i Q_ij)}` (zero if the move
is never proposed). -/
def mhAccept (p₀ : ι → ℝ) (Q : ι → ι → ℝ) (i j : ι) : ℝ :=
  if Q i j = 0 then 0 else min 1 (p₀ j * Q j i / (p₀ i * Q i j))

/-- Metropolis–Hastings transition matrix: off-diagonal `Q_ij α_ij`, diagonal = rejection mass. -/
def mhMatrix (p₀ : ι → ℝ) (Q : ι → ι → ℝ) (i j : ι) : ℝ :=
  if i = j then 1 - ∑ k ∈ univ.erase i, Q i k * mhAccept p₀ Q i k else Q i j * mhAccept p₀ Q i j

omit [Fintype ι] [DecidableEq ι] in
/-- The probability flux of an accepted move is symmetric:
`π_i Q_ij α_ij = min(π_i Q_ij, π_j Q_ji)`. -/
@[tmio T, powerlib_foundation] theorem mh_flux {Q : ι → ι → ℝ} (hp₀ : ∀ i, 0 < p₀ i)
    (hQ : ∀ i j, 0 ≤ Q i j) (i j : ι) :
    p₀ i * (Q i j * mhAccept p₀ Q i j) = min (p₀ i * Q i j) (p₀ j * Q j i) := by
  unfold mhAccept
  by_cases h : Q i j = 0
  · simp [h, (mul_nonneg (hp₀ j).le (hQ j i))]
  · simp only [h, ↓reduceIte]
    have hpos : 0 < p₀ i * Q i j := mul_pos (hp₀ i) (lt_of_le_of_ne (hQ i j) (Ne.symm h))
    rw [← mul_assoc, mul_min_of_nonneg _ _ hpos.le, mul_one, mul_div_cancel₀ _ hpos.ne']

/-- **MH detailed balance** with respect to any positive target. -/
@[tmio T, powerlib_foundation] theorem mh_detailedBalance {Q : ι → ι → ℝ} (hp₀ : ∀ i, 0 < p₀ i)
    (hQ : ∀ i j, 0 ≤ Q i j) : DetailedBalance p₀ (mhMatrix p₀ Q) := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · simp only [mhMatrix, hij, Ne.symm hij, ↓reduceIte]
    rw [mh_flux hp₀ hQ, mh_flux hp₀ hQ, min_comm]

/-- Rows of the MH matrix sum to one. -/
@[tmio T, powerlib_foundation] theorem mh_stochastic (Q : ι → ι → ℝ) (i : ι) :
    ∑ j, mhMatrix p₀ Q i j = 1 := by
  rw [← add_sum_erase _ _ (mem_univ i)]
  have h1 : mhMatrix p₀ Q i i = 1 - ∑ k ∈ univ.erase i, Q i k * mhAccept p₀ Q i k := by
    simp [mhMatrix]
  have h2 : ∑ x ∈ univ.erase i, mhMatrix p₀ Q i x =
      ∑ k ∈ univ.erase i, Q i k * mhAccept p₀ Q i k := by
    refine sum_congr rfl fun x hx => ?_
    simp only [mhMatrix, Ne.symm (ne_of_mem_erase hx), ↓reduceIte]
  rw [h1, h2]; ring

/-- **The posterior is invariant for the MH chain** (target = any positive vector, e.g. the
unnormalized posterior `π L`). -/
@[tmio T, powerlib_foundation] theorem mh_invariant {Q : ι → ι → ℝ} (hp₀ : ∀ i, 0 < p₀ i)
    (hQ : ∀ i j, 0 ≤ Q i j) (j : ι) : ∑ i, p₀ i * mhMatrix p₀ Q i j = p₀ j :=
  invariant_of_detailedBalance (mh_stochastic Q) (mh_detailedBalance hp₀ hQ) j

omit [Fintype ι] [DecidableEq ι] in
/-- Acceptance probabilities lie in `[0, 1]` for a nonnegative proposal and positive target, so
the off-diagonal entries are bounded by the proposal. -/
@[tmio T, powerlib_foundation] theorem mhAccept_mem {Q : ι → ι → ℝ} (hp₀ : ∀ i, 0 < p₀ i)
    (hQ : ∀ i j, 0 ≤ Q i j) (i j : ι) : 0 ≤ mhAccept p₀ Q i j ∧ mhAccept p₀ Q i j ≤ 1 := by
  unfold mhAccept
  split_ifs
  · simp
  · exact ⟨le_min zero_le_one (div_nonneg (mul_nonneg (hp₀ j).le (hQ j i))
      (mul_nonneg (hp₀ i).le (hQ i j))), min_le_left _ _⟩

/-- General kernels (Mathlib `ProbabilityTheory.Kernel.IsReversible.invariant`): a reversible
Markov kernel leaves its reference measure invariant. -/
@[tmio T, powerlib_foundation] theorem reversible_invariant {α : Type*} [MeasurableSpace α]
    {κ : ProbabilityTheory.Kernel α α} [ProbabilityTheory.IsMarkovKernel κ]
    {μ : MeasureTheory.Measure α} (h : κ.IsReversible μ) : κ.Invariant μ :=
  h.invariant

end powerlib.Estimation
