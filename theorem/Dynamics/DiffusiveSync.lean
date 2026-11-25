import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Synchronization of diffusively coupled nodes with a one-sided Lipschitz node field

Identical nodes `ẋₖ = f(xₖ) − σ ∑ⱼ Lₖⱼ xⱼ` whose node field expands pairwise distances at most at
the rate `c` (`⟪x − y, f x − f y⟫ ≤ c ‖x − y‖²`) and whose coupling contracts the disagreement at
the rate `λ` synchronize exponentially as soon as `σ λ > c`: the disagreement
`W = ∑ₖ ∑ⱼ ‖xₖ − xⱼ‖²` obeys `W(t) ≤ e^{2(c − σλ) t} W(0)`.

Scope.
* Generic: nodes indexed by a finite type `ι`, node states in a real inner product space `E`,
  node field `f : E → E` (no smoothness), real coupling matrix `L`, coupling strength `σ ≥ 0`.
  Continuous time; a global solution is a curve `X : ℝ → ι → E` with
  `∀ t, HasDerivAt X (netField f L σ (X t)) t`; the behaviour is written out in the statement.
* The coupling hypothesis is the coercivity of the coupling on the disagreement,
  `λ W(X) ≤ ∑ₖ ∑ⱼ ⟪Xₖ − Xⱼ, (L X)ₖ − (L X)ⱼ⟫`; for a symmetric Laplacian it holds with the
  algebraic connectivity `λ = λ₂` (from `⟪u, L u⟫ ≥ λ₂ (‖u‖² − (∑ u)²/N)` and zero column sums).
  It is a hypothesis here.

Source: work-sync `theory/T-synchronization-manifold.md` §1.1–§1.5 (diffusive coupling, the
synchronization manifold and the threshold `σ μ₂ > a`; here for a nonlinear node with a
one-sided Lipschitz bound, the QUAD condition); W. Lu and T. Chen, *Physica D* 213 (2006) 214–230
(QUAD-type synchronization criterion).

Results.
* `hasDerivAt_disagreement`: along a solution, `Ẇ = 2 ∑ₖ ∑ⱼ ⟪Xₖ − Xⱼ, Ẋₖ − Ẋⱼ⟫`.
* `disagreement_le`: `W(X(t)) ≤ e^{2(c − σλ) t} W(X(0))` for `t ≥ 0`; in particular every solution
  synchronizes exponentially when `σ λ > c`.
-/

noncomputable section
namespace powerlib.Dynamics.DiffusiveSync

open scoped RealInnerProductSpace

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coupled field `(F X)ₖ = f(Xₖ) − σ ∑ⱼ Lₖⱼ Xⱼ`. -/
def netField (f : E → E) (L : Matrix ι ι ℝ) (σ : ℝ) (X : ι → E) : ι → E :=
  fun k => f (X k) - σ • ∑ j, L k j • X j

/-- The disagreement `W(X) = ∑ₖ ∑ⱼ ‖Xₖ − Xⱼ‖²`. -/
def disagreement (X : ι → E) : ℝ := ∑ k, ∑ j, ‖X k - X j‖ ^ 2

/-- The derivative of the disagreement along a differentiable curve. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_disagreement {X : ℝ → ι → E} {X' : ι → E}
    {t : ℝ} (hX : HasDerivAt X X' t) :
    HasDerivAt (fun s => disagreement (X s))
      (2 * ∑ k, ∑ j, ⟪X t k - X t j, X' k - X' j⟫) t := by
  have hc : ∀ k, HasDerivAt (fun s => X s k) (X' k) t := fun k => hasDerivAt_pi.mp hX k
  have hterm : ∀ k j, HasDerivAt (fun s => ‖X s k - X s j‖ ^ 2)
      (2 * ⟪X t k - X t j, X' k - X' j⟫) t := by
    intro k j
    exact HasDerivAt.norm_sq ((hc k).sub (hc j))
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hterm k j
  simp only [disagreement]
  convert h using 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]

/-- **Exponential synchronization of diffusively coupled nodes.** If the node field expands
pairwise distances at most at the rate `c` and the coupling contracts the disagreement at the rate
`λ` (`σ ≥ 0`), every global solution of `ẋₖ = f(xₖ) − σ ∑ⱼ Lₖⱼ xⱼ` satisfies
`W(X(t)) ≤ e^{2(c − σλ) t} W(X(0))` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem disagreement_le {f : E → E} {L : Matrix ι ι ℝ}
    {σ c lam : ℝ} (hσ : 0 ≤ σ) (hf : ∀ x y, ⟪x - y, f x - f y⟫ ≤ c * ‖x - y‖ ^ 2)
    (hL : ∀ X : ι → E, lam * disagreement X ≤
      ∑ k, ∑ j, ⟪X k - X j, ∑ l, L k l • X l - ∑ l, L j l • X l⟫)
    {X : ℝ → ι → E} (hX : ∀ t, HasDerivAt X (netField f L σ (X t)) t) {t : ℝ} (ht : 0 ≤ t) :
    disagreement (X t) ≤ Real.exp (2 * (c - σ * lam) * t) * disagreement (X 0) := by
  set a := 2 * (c - σ * lam)
  set g : ℝ → ℝ := fun s => Real.exp (-(a * s)) * disagreement (X s) with hg
  have hderiv : ∀ s, HasDerivAt g (Real.exp (-(a * s)) *
      (-a * disagreement (X s) +
        2 * ∑ k, ∑ j, ⟪X s k - X s j, netField f L σ (X s) k - netField f L σ (X s) j⟫)) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-(a * s))) (Real.exp (-(a * s)) * -a) s := by
      have := ((hasDerivAt_id s).const_mul a).neg.exp
      simpa using this
    convert he.mul (hasDerivAt_disagreement (hX s)) using 1
    ring
  have hle : ∀ s, Real.exp (-(a * s)) *
      (-a * disagreement (X s) +
        2 * ∑ k, ∑ j, ⟪X s k - X s j, netField f L σ (X s) k - netField f L σ (X s) j⟫) ≤ 0 := by
    intro s
    refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
    have hsplit : ∀ k j, ⟪X s k - X s j, netField f L σ (X s) k - netField f L σ (X s) j⟫ =
        ⟪X s k - X s j, f (X s k) - f (X s j)⟫ -
          σ * ⟪X s k - X s j, ∑ l, L k l • X s l - ∑ l, L j l • X s l⟫ := by
      intro k j
      simp only [netField]
      rw [show f (X s k) - σ • ∑ l, L k l • X s l - (f (X s j) - σ • ∑ l, L j l • X s l) =
          (f (X s k) - f (X s j)) - σ • (∑ l, L k l • X s l - ∑ l, L j l • X s l) by
        rw [smul_sub]; abel, inner_sub_right, real_inner_smul_right]
    have hnode : ∑ k, ∑ j, ⟪X s k - X s j, f (X s k) - f (X s j)⟫ ≤ c * disagreement (X s) := by
      rw [disagreement, Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => hf _ _
    have hcoup := hL (X s)
    simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hcoup hσ]
  have hanti : Antitone g := by
    refine antitone_of_deriv_nonpos (fun s => (hderiv s).differentiableAt) fun s => ?_
    rw [(hderiv s).deriv]
    exact hle s
  have h0 := hanti ht
  simp only [hg, mul_zero, neg_zero, Real.exp_zero, one_mul] at h0
  have hpos := Real.exp_pos (a * t)
  calc disagreement (X t) = Real.exp (a * t) * (Real.exp (-(a * t)) * disagreement (X t)) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (a * t) * disagreement (X 0) := mul_le_mul_of_nonneg_left h0 hpos.le

end powerlib.Dynamics.DiffusiveSync
