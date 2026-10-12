import theorem.Periodic.Transition

/-! # A periodic orbit of an autonomous system has the Floquet multiplier `1`

Foundation layer.

Model boundary. Autonomous ODE `ẋ = f(x)` on `ℝ^X` (`X → ℝ`, sup norm), `f` of class `C¹`
(globally), continuous time. `x_p` is a global solution with period `T > 0`
(`x_p(t + T) = x_p(t)`). The variational (first-variation) equation along `x_p` is
`ẏ = A(t) y` with `A(t) = Df(x_p(t))` written as a matrix (`variationalMatrix`); it is continuous
and `T`-periodic, so its transition and monodromy matrices are those of
`Periodic/Transition.lean`.

Results.
* `variationalMatrix_continuous`, `variationalMatrix_periodic`: the hypotheses of the Floquet
  theory hold for `A(t)`.
* `velocity_solves_variational`: the velocity `y(t) = ẋ_p(t) = f(x_p(t))` solves the variational
  equation (chain rule).
* `monodromy_mulVec_velocity`: `Φ(T, 0) f(x_p(0)) = f(x_p(0))`.
* `one_mem_spectrum_monodromy`: if the orbit is not an equilibrium (`f(x_p(0)) ≠ 0`), `1` is a
  Floquet multiplier (an eigenvalue of the complexified monodromy matrix).

Source: work-sync projects/basin-guard/notes/concepts/guard-object.md (trivial multiplier of an
autonomous periodic orbit); projects/vsc-parametric-oscillation/references/
gfm-driven-gfl-parametric-resonance/notes/concepts/coupled-parametric-resonance.md §2
(`Φ' = JΦ`, `Φ(0) = I`).
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The variational matrix `A(t) = Df(x_p(t))`. -/
def variationalMatrix (f : (X → ℝ) → X → ℝ) (xp : ℝ → X → ℝ) (t : ℝ) : Matrix X X ℝ :=
  LinearMap.toMatrix' (fderiv ℝ f (xp t)).toLinearMap

variable {f : (X → ℝ) → X → ℝ} {xp : ℝ → X → ℝ}

@[powerlib_foundation] theorem variationalMatrix_mulVec (t : ℝ) (v : X → ℝ) :
    variationalMatrix f xp t *ᵥ v = fderiv ℝ f (xp t) v := by
  rw [variationalMatrix, LinearMap.toMatrix'_mulVec]
  rfl

@[powerlib_foundation] theorem variationalMatrix_continuous (hf : ContDiff ℝ 1 f)
    (hxp : Continuous xp) : Continuous (variationalMatrix f xp) := by
  have hD : Continuous fun t => fderiv ℝ f (xp t) :=
    (hf.continuous_fderiv one_ne_zero).comp hxp
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t => variationalMatrix f xp t i j) =
      fun t => fderiv ℝ f (xp t) (Pi.single j 1) i := by
    funext t
    simp [variationalMatrix, LinearMap.toMatrix'_apply]
  rw [this]
  exact (continuous_apply i).comp
    ((ContinuousLinearMap.apply ℝ (X → ℝ) (Pi.single j 1)).continuous.comp hD)

@[powerlib_foundation] theorem variationalMatrix_periodic {T : ℝ} (hper : Periodic xp T) :
    Periodic (variationalMatrix f xp) T := by
  intro t
  simp only [variationalMatrix, hper t]

/-- The velocity `f(x_p(t))` solves the variational equation `ẏ = A(t) y`. -/
@[powerlib_foundation] theorem velocity_solves_variational (hf : ContDiff ℝ 1 f)
    (hsol : ∀ t, HasDerivAt xp (f (xp t)) t) (s : Set ℝ) :
    IsIntegralCurveOn (fun t => f (xp t)) (vecField (variationalMatrix f xp)) s := by
  intro t _
  have hd : HasFDerivAt f (fderiv ℝ f (xp t)) (xp t) :=
    ((hf.differentiable one_ne_zero) (xp t)).hasFDerivAt
  have h := hd.comp_hasDerivAt t (hsol t)
  rw [vecField, variationalMatrix_mulVec]
  exact h.hasDerivWithinAt

/-- `Φ(T, 0) f(x_p(0)) = f(x_p(0))`: the velocity is a Floquet eigenvector with multiplier `1`. -/
@[powerlib_foundation] theorem monodromy_mulVec_velocity (hf : ContDiff ℝ 1 f)
    (hsol : ∀ t, HasDerivAt xp (f (xp t)) t) {T : ℝ} (hT : 0 < T) (hper : Periodic xp T) :
    monodromy (variationalMatrix f xp) T 0 *ᵥ f (xp 0) = f (xp 0) := by
  have hxp : Continuous xp := continuous_iff_continuousAt.mpr fun t => (hsol t).continuousAt
  have hA := variationalMatrix_continuous hf hxp
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA (variationalMatrix_periodic hper) hT
  have h := trajectory_eq hA hM (velocity_solves_variational hf hsol (Ici 0)) T hT.le
  rw [monodromy, zero_add, ← h]
  have : xp T = xp 0 := by simpa using hper 0
  rw [this]

/-- A non-equilibrium periodic orbit has the Floquet multiplier `1`. -/
@[powerlib_foundation] theorem one_mem_spectrum_monodromy (hf : ContDiff ℝ 1 f)
    (hsol : ∀ t, HasDerivAt xp (f (xp t)) t) {T : ℝ} (hT : 0 < T) (hper : Periodic xp T)
    (hne : f (xp 0) ≠ 0) :
    (1 : ℂ) ∈ spectrum ℂ ((monodromy (variationalMatrix f xp) T 0).map (algebraMap ℝ ℂ)) := by
  set Mo := monodromy (variationalMatrix f xp) T 0
  have hv := monodromy_mulVec_velocity hf hsol hT hper
  have hdet : (Matrix.scalar X (1 : ℝ) - Mo).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨f (xp 0), hne, ?_⟩
    rw [Matrix.sub_mulVec, show Mo *ᵥ f (xp 0) = f (xp 0) from hv]
    simp
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
  have hroot : Mo.charpoly.IsRoot 1 := by
    rw [Polynomial.IsRoot, Matrix.eval_charpoly, hdet]
  simpa using hroot.map (f := algebraMap ℝ ℂ)

end powerlib.Periodic
