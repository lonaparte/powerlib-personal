import theorem.Dynamics.HopfCycle

/-! # Hopf cycles of a family whose equilibrium moves with the parameter

`Dynamics.HopfCycle.exists_hopfCycle` (`theorem/Dynamics/HopfCycle.lean`) reads a family
`ẋ = F(x, μ)` with `F(0, μ) = 0`: the equilibrium does not move. Along a family whose equilibrium
moves on a smooth branch, `F(x*(μ), μ) = 0`, the re-centred family `F̃(z, μ) = F(z + x*(μ), μ)`
keeps the origin, has at `μ = 0` the Hopf data of `F(·, 0)` at `x*(0)` (the critical pair, the
characteristic polynomial and `ℓ₁` are invariant under the translation), and its linear part
along the parameter is `D_x F(x*(μ), μ)`: the transversality is that of the Jacobian along the
branch.

Scope.
* A family of autonomous ODEs `ẋ = F(x, μ)` on `State n`, `μ ∈ ℝ` constant, and an equilibrium
  branch `x* : ℝ → State n` with `F(x*(μ), μ) = 0` for every `μ`; `x*` of class `C¹` and analytic
  at `0`, the augmented field `augField F : (x, μ) ↦ (F(x, μ), 0)` of class `C¹` and analytic at
  `(x*(0), 0)`. At `μ = 0`: a critical pair `(q, p)` of `F(·, 0)` at `x*(0)` and frequency
  `ω > 0`, the other eigenvalues in the open left half-plane, `ℓ₁ ≠ 0`, and transversality:
  `μ ↦ D_x F(x*(μ), μ)` has the derivative `B` at `0` with `τ = tr (critπ p ∘ B ∘ critι q) ≠ 0`.
  The branch is an argument (no implicit-function theorem is used: a model supplies its branch).
* Periodic orbits are written out in the statements, as in `theorem/Dynamics/HopfCycle.lean`.
  Existence and the amplitude bound in the critical coordinates of `x − x*(μ)` are proved;
  uniqueness, orbital stability and the absence of cycles for the other sign of `μ` are not.
* Generic foundation, independent of any model; no model family is defined.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4 (Theorem 3.3; the
equilibrium branch `x₀(α)` is shifted to the origin before the normal form is computed) and §5.4;
Hassard–Kazarinoff–Wan, *Theory and Applications of Hopf Bifurcation* (1981), Ch. 1; the fixed
equilibrium law `Dynamics.HopfCycle.exists_hopfCycle` and the translation invariance
`NormalForm.LyapunovCoefficient.isCriticalPair_comp_add`, `jacobianC_comp_add`,
`firstLyapunov_comp_add` (`theorem/NormalForm/LyapunovCoefficient.lean`).

Results.
* `augField_recentre`: the augmented field of `F̃` is that of `F` composed with the shift
  `w ↦ w + (x*(μ), 0)`; hence `contDiff_augField_recentre`, `analyticAt_augField_recentre`.
* `paramTrace_comp_add_smul`: the transversality coefficient is linear in the parameter derivative
  (`τ` of a direction `(a, b)` of a two-parameter plane is `a τ₁ + b τ₂`).
* **`exists_hopfCycle_of_branch`**: for every small `μ` with `μ τ ℓ₁ < 0`, a nonconstant periodic
  orbit of `F(·, μ)`, period at most `4π/ω`, with `ν/8 ≤ ‖critπ p (x(t) − x*(μ))‖² ≤ 8ν`,
  `ν = −μτ/(ω ℓ₁)`: the cycles of `exists_hopfCycle` around the moving equilibrium.
-/

noncomputable section
namespace powerlib.Dynamics.HopfCycle
open Polynomial
open powerlib.Dynamics.CenterManifold (critπ critι)
open powerlib.NormalForm.LyapunovCoefficient (IsCriticalPair firstLyapunov jacobianC
  isCriticalPair_comp_add jacobianC_comp_add firstLyapunov_comp_add)

variable {n : ℕ} {F : State n → ℝ → State n} {xs : ℝ → State n}

/-- **The re-centred augmented field**: `(z, μ) ↦ (F(z + x*(μ), μ), 0)` is the augmented field of
`F` at `(z, μ) + (x*(μ), 0)`. -/
@[tmio T, powerlib_foundation] theorem augField_recentre :
    augField (fun x μ => F (x + xs μ) μ) = fun w => augField F (w + xin (xs (mpart w))) := by
  funext w
  simp [augField, map_add]

/-- The re-centred augmented field is as smooth as `F` and the branch. -/
@[tmio T, powerlib_foundation] theorem contDiff_augField_recentre {k : WithTop ℕ∞}
    (hF : ContDiff ℝ k (augField F)) (hxs : ContDiff ℝ k xs) :
    ContDiff ℝ k (augField fun x μ => F (x + xs μ) μ) := by
  rw [augField_recentre]
  exact hF.comp (contDiff_id.add (xin.contDiff.comp (hxs.comp mpart.contDiff)))

/-- The re-centred augmented field is analytic at `0` when `F` is analytic at `(x*(0), 0)` and
the branch at `0`. -/
@[tmio T, powerlib_foundation] theorem analyticAt_augField_recentre
    (hF : AnalyticAt ℝ (augField F) (xin (xs 0))) (hxs : AnalyticAt ℝ xs 0) :
    AnalyticAt ℝ (augField fun x μ => F (x + xs μ) μ) 0 := by
  rw [augField_recentre]
  have hm : AnalyticAt ℝ (fun w : State (n + 1) => xs (mpart w)) 0 :=
    hxs.comp_of_eq (mpart.analyticAt 0) (map_zero _)
  have hφ : AnalyticAt ℝ (fun w : State (n + 1) => w + xin (xs (mpart w))) 0 :=
    analyticAt_id.add ((xin.analyticAt _).comp hm)
  exact hF.comp_of_eq hφ (by simp)

/-- **The transversality coefficient is linear in the parameter derivative.** -/
@[tmio T, powerlib_foundation] theorem paramTrace_comp_add_smul (p q : Fin n → ℂ)
    (B₁ B₂ : State n →L[ℝ] State n) (a b : ℝ) :
    PlanarHopf.paramTrace ((critπ p).comp ((a • B₁ + b • B₂).comp (critι q))) =
      a * PlanarHopf.paramTrace ((critπ p).comp (B₁.comp (critι q))) +
        b * PlanarHopf.paramTrace ((critπ p).comp (B₂.comp (critι q))) := by
  simp only [PlanarHopf.paramTrace, PlanarHopf.m00, PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **The Hopf cycles of a family with a moving equilibrium.** Let `ẋ = F(x, μ)` on `ℝⁿ` with an
equilibrium branch `F(x*(μ), μ) = 0`, `x*` of class `C¹` and analytic at `0`, the augmented field
`(x, μ) ↦ (F(x, μ), 0)` of class `C¹` and analytic at `(x*(0), 0)`, a critical pair `(q, p)` of
`F(·, 0)` at `x*(0)` and the frequency `ω` with the remaining eigenvalues in the open left
half-plane, first Lyapunov coefficient `ℓ₁ ≠ 0` there, and transversality along the branch:
`μ ↦ D_x F(x*(μ), μ)` has derivative `B` at `0` with `τ = tr (critπ p ∘ B ∘ critι q) ≠ 0`. Then
for every small `μ` with `μ τ ℓ₁ < 0` the field `F(·, μ)` has a nonconstant periodic orbit,
defined for all time, of period at most `4π/ω`, whose critical coordinates about the moving
equilibrium satisfy `ν/8 ≤ ‖critπ p (x(t) − x*(μ))‖² ≤ 8ν`, `ν = −μτ/(ω ℓ₁) > 0`
(`exists_hopfCycle` for the re-centred family `F(z + x*(μ), μ)`). -/
@[tmio T, powerlib_foundation] theorem exists_hopfCycle_of_branch {ω : ℝ} {q p : Fin n → ℂ}
    (hF : ContDiff ℝ 1 (augField F)) (ha : AnalyticAt ℝ (augField F) (xin (xs 0)))
    (hxs : ContDiff ℝ 1 xs) (hxa : AnalyticAt ℝ xs 0) (hF0 : ∀ μ, F (xs μ) μ = 0)
    (hcp : IsCriticalPair (fun x => F x 0) (xs 0) ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) (xs 0)).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) (xs μ)) B 0)
    (hτ : PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) ≠ 0)
    (hl : firstLyapunov (fun x => F x 0) (xs 0) ω q p ≠ 0) :
    ∃ δ > 0, ∀ μ, |μ| < δ →
      μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) *
        firstLyapunov (fun x => F x 0) (xs 0) ω q p < 0 →
      ∃ x : ℝ → State n, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
        (∀ t, HasDerivAt x (F (x t) μ) t) ∧ (∀ t, x (t + T) = x t) ∧ (∃ t, x t ≠ x 0) ∧
        ∀ t, -(μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q)))) /
            (ω * firstLyapunov (fun x => F x 0) (xs 0) ω q p) / 8 ≤
              ‖critπ p (x t - xs μ)‖ ^ 2 ∧
          ‖critπ p (x t - xs μ)‖ ^ 2 ≤ 8 * (-(μ * PlanarHopf.paramTrace
            ((critπ p).comp (B.comp (critι q)))) /
              (ω * firstLyapunov (fun x => F x 0) (xs 0) ω q p)) := by
  have hl' : firstLyapunov (fun z => F (z + xs 0) 0) 0 ω q p =
      firstLyapunov (fun x => F x 0) (xs 0) ω q p :=
    firstLyapunov_comp_add (fun x => F x 0) (xs 0) ω q p
  have hB' : HasDerivAt (fun μ => fderiv ℝ (fun z => F (z + xs μ) μ) 0) B 0 := by
    have e : (fun μ => fderiv ℝ (fun z => F (z + xs μ) μ) 0) =
        fun μ => fderiv ℝ (fun x => F x μ) (xs μ) := by
      funext μ
      rw [fderiv_comp_add_right (f := fun x => F x μ), zero_add]
    rw [e]
    exact hB
  have hchar' : (jacobianC (fun z => F (z + xs 0) 0) 0).charpoly =
      (X ^ 2 + C ((ω : ℂ) ^ 2)) * r := by
    rw [jacobianC_comp_add (fun x => F x 0) (xs 0)]
    exact hchar
  obtain ⟨δ, hδ, hcyc⟩ := exists_hopfCycle (F := fun z μ => F (z + xs μ) μ)
    (contDiff_augField_recentre hF hxs) (analyticAt_augField_recentre ha hxa)
    (fun μ => by simpa using hF0 μ) (isCriticalPair_comp_add.mpr hcp) hchar' hr hB' hτ
    (hl'.symm ▸ hl)
  refine ⟨δ, hδ, fun μ hμ hs => ?_⟩
  rw [← hl'] at hs
  obtain ⟨z, T, hT0, hT, hz, hzT, hznc, hamp⟩ := hcyc μ hμ hs
  refine ⟨fun t => z t + xs μ, T, hT0, hT, fun t => (hz t).add_const (xs μ),
    fun t => by simp only [hzT], ?_, fun t => ?_⟩
  · obtain ⟨t, ht⟩ := hznc
    exact ⟨t, fun h => ht (add_right_cancel h)⟩
  · simp only [add_sub_cancel_right]
    rw [← hl']
    exact hamp t

end powerlib.Dynamics.HopfCycle
