import theorem.Dynamics.Defs
import Mathlib.Analysis.ODE.ExistUnique

/-! # Slow manifolds as invariant graphs: the invariance equation, `h₁`, and `M₀`

Foundation layer (category B).

Sources: work-sync `theory/T-slow-manifold.md` §1.1 (`ẋ = f(x,y)`, `εẏ = g(x,y)`), §1.4 (claimed
strict invariance of `M₀ = {g = 0}`), §1.6 (first-order correction `h₁`);
`theory/T-singular-perturbation.md` §1.3, §1.8.

Model boundary: autonomous slow–fast system on real normed spaces, slow state `x ∈ E`, fast
state `y ∈ F`, fixed `ε > 0` unless stated; continuous time; classical (everywhere
differentiable) solutions. The implicit construction of `h` itself (Mathlib implicit function
theorem) is in `theorem/DAE/Nonlinear.lean` (`implicitMap`, `hasStrictFDerivAt_implicitMap`).

Results.
* `graph_lift` / `graph_invariant_of_eq`: if `H` satisfies the invariance equation
  `ε DH(x)·f(x, H x) = g(x, H x)` (`IsInvariantGraph`), every solution of the reduced equation
  `ẋ = f(x, H x)` lifts to a solution `(x, H x)` of the full system; with a globally Lipschitz
  full field, every full solution starting on the graph stays on it.
* `invarianceEq_of_solution_on_graph`: conversely, if a full solution stays on the graph
  `y = H(x)` near `t₀`, the invariance equation holds at `x(t₀)`; hence a graph that is invariant
  through every point satisfies the equation everywhere (`isInvariantGraph_of_forall`).
* `h1_equation`: if a family of invariant graphs `H(ε, ·)` is differentiable in `ε` at `0`
  (`H(0,·) = h₀`, `∂_ε H(0,·) = h₁`) and the derivative of `H` in `x` is continuous in `ε`, then
  `∂_y g · h₁ + ∂_ε g = Dh₀ · f(x, h₀ x)`, i.e. `A_y h₁ = ∂ₓh₀·f − ∂_ε g` (`T-slow-manifold` §1.6,
  autonomous case; conditional on the existence of such a family).
* Correction (`T-slow-manifold` §1.4: "`M₀` 严格不变"): false. For `ẋ = 1`, `εẏ = x − y`
  (`h(x) = x`, `∂g/∂t = 0`), the solution from `(0, 0) ∈ M₀` is `x = t`,
  `y = t − ε(1 − e^{−t/ε})`, and `y − h(x) = −ε(1 − e^{−t/ε}) ≠ 0` for `t ≠ 0`
  (`M0_not_invariant`): the note's own computation `d(y − h)/dt = −∂h/∂x · f_s` does not vanish.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Full slow–fast field `(f, g/ε)` on `E × F`. -/
def spField (ε : ℝ) (f : E × F → E) (g : E × F → F) (z : E × F) : E × F := (f z, ε⁻¹ • g z)

/-- The graph of `H` satisfies the invariance equation `ε DH(x) f(x, H x) = g(x, H x)`. -/
def IsInvariantGraph (ε : ℝ) (f : E × F → E) (g : E × F → F) (H : E → F) : Prop :=
  ∀ x, DifferentiableAt ℝ H x ∧ ε • fderiv ℝ H x (f (x, H x)) = g (x, H x)

/-- A reduced solution lifts to a full solution on the graph. -/
@[powerlib_foundation] theorem graph_lift {ε : ℝ} (hε : ε ≠ 0) {f : E × F → E} {g : E × F → F}
    {H : E → F} (hH : IsInvariantGraph ε f g H) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (f (x t, H (x t))) t) (t : ℝ) :
    HasDerivAt (fun τ => (x τ, H (x τ))) (spField ε f g (x t, H (x t))) t := by
  obtain ⟨hd, heq⟩ := hH (x t)
  have hy : HasDerivAt (fun τ => H (x τ)) (fderiv ℝ H (x t) (f (x t, H (x t)))) t :=
    hd.hasFDerivAt.comp_hasDerivAt t (hx t)
  have hval : fderiv ℝ H (x t) (f (x t, H (x t))) = ε⁻¹ • g (x t, H (x t)) := by
    rw [← heq, smul_smul, inv_mul_cancel₀ hε, one_smul]
  rw [hval] at hy
  exact (hx t).prodMk hy

/-- **Invariance of the graph** (globally Lipschitz full field): a full solution that starts on
the graph coincides with the lifted reduced solution through the same point. -/
@[powerlib_foundation] theorem graph_invariant_of_eq {ε : ℝ} (hε : ε ≠ 0) {f : E × F → E}
    {g : E × F → F} {H : E → F} (hH : IsInvariantGraph ε f g H) {K : NNReal}
    (hL : LipschitzWith K (spField ε f g)) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (f (x t, H (x t))) t) {z : ℝ → E × F}
    (hz : ∀ t, HasDerivAt z (spField ε f g (z t)) t) (h0 : z 0 = (x 0, H (x 0))) :
    ∀ t, (z t).2 = H ((z t).1) := by
  have heq : z = fun τ => (x τ, H (x τ)) :=
    ODE_solution_unique_univ (v := fun _ => spField ε f g) (s := fun _ => Set.univ) (t₀ := 0)
      (fun _ => hL.lipschitzOnWith) (fun t => ⟨hz t, trivial⟩)
      (fun t => ⟨graph_lift hε hH hx t, trivial⟩) h0
  intro t
  rw [heq]

/-- A full solution that stays on the graph near `t₀` forces the invariance equation at
`x(t₀)`. -/
@[powerlib_foundation] theorem invarianceEq_of_solution_on_graph {ε : ℝ} {f : E × F → E}
    {g : E × F → F} {H : E → F} {x : ℝ → E} {y : ℝ → F} {t₀ : ℝ}
    (hx : HasDerivAt x (f (x t₀, y t₀)) t₀) (hy : HasDerivAt y (ε⁻¹ • g (x t₀, y t₀)) t₀)
    (hon : ∀ᶠ t in 𝓝 t₀, y t = H (x t)) (hH : DifferentiableAt ℝ H (x t₀)) (hε : ε ≠ 0) :
    ε • fderiv ℝ H (x t₀) (f (x t₀, H (x t₀))) = g (x t₀, H (x t₀)) := by
  have hy0 : y t₀ = H (x t₀) := hon.self_of_nhds
  have hcomp : HasDerivAt (fun t => H (x t)) (fderiv ℝ H (x t₀) (f (x t₀, y t₀))) t₀ :=
    hH.hasFDerivAt.comp_hasDerivAt t₀ hx
  have hy' : HasDerivAt (fun t => H (x t)) (ε⁻¹ • g (x t₀, y t₀)) t₀ :=
    hy.congr_of_eventuallyEq (hon.mono fun t ht => ht.symm)
  have := hcomp.unique hy'
  rw [hy0] at this
  rw [this, smul_smul, mul_inv_cancel₀ hε, one_smul]

/-- If through every point of the graph there passes a full solution that stays on the graph,
the graph satisfies the invariance equation everywhere. -/
@[powerlib_foundation] theorem isInvariantGraph_of_forall {ε : ℝ} (hε : ε ≠ 0) {f : E × F → E}
    {g : E × F → F} {H : E → F} (hH : Differentiable ℝ H)
    (hsol : ∀ x₀, ∃ z : ℝ → E × F, z 0 = (x₀, H x₀) ∧
      HasDerivAt z (spField ε f g (z 0)) 0 ∧ ∀ᶠ t in 𝓝 0, (z t).2 = H ((z t).1)) :
    IsInvariantGraph ε f g H := by
  intro x₀
  refine ⟨hH x₀, ?_⟩
  obtain ⟨z, hz0, hz, hon⟩ := hsol x₀
  have h1 := hz.fst
  have h2 := hz.snd
  simp only [spField] at h1 h2
  have := invarianceEq_of_solution_on_graph (x := fun t => (z t).1) (y := fun t => (z t).2)
    (H := H) (f := f) (g := g) (ε := ε) h1 h2 hon (hH _) hε
  simpa [hz0] using this

/-- **First-order slow manifold (`h₁` equation)**, autonomous case, at a fixed slow point `x`.
Let `H(ε, ·)` be a family of invariant graphs (`ε DₓH(ε, x) f(x, H(ε,x)) = g(x, H(ε,x), ε)` for
`ε` near `0`), `H(0, x) = h₀ x`, `∂_ε H(0, x) = h₁`, with `DₓH(ε, x)` continuous in `ε` at `0`.
If `(y, ε) ↦ g(x, y, ε)` has derivative `D` at `(h₀ x, 0)`, then `D(h₁, 1) = Dₓh₀ · f(x, h₀ x)`,
i.e. `∂_y g · h₁ + ∂_ε g = ∂ₓh₀ · f`. -/
@[powerlib_foundation] theorem h1_equation {f : E × F → E} {gx : F × ℝ → F} {H : ℝ → E → F}
    {x : E} {h1 : F} {D : F × ℝ →L[ℝ] F} {DH : ℝ → E →L[ℝ] F}
    (hinv : ∀ᶠ ε in 𝓝 0, ε • DH ε (f (x, H ε x)) = gx (H ε x, ε))
    (hHε : HasDerivAt (fun ε => H ε x) h1 0)
    (hDH : ContinuousAt (fun ε => DH ε (f (x, H ε x))) 0)
    (hg : HasFDerivAt gx D (H 0 x, 0)) :
    D (h1, 1) = DH 0 (f (x, H 0 x)) := by
  -- derivative of the left-hand side `ε ↦ ε • Φ(ε)` at `0` is `Φ(0)`
  have hL : HasDerivAt (fun ε : ℝ => ε • DH ε (f (x, H ε x))) (DH 0 (f (x, H 0 x))) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have : Tendsto (fun t : ℝ => DH (0 + t) (f (x, H (0 + t) x))) (𝓝[≠] 0)
        (𝓝 (DH 0 (f (x, H 0 x)))) := by
      simpa using hDH.tendsto.mono_left nhdsWithin_le_nhds
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, zero_smul, sub_zero, smul_smul]
    rw [inv_mul_cancel₀ ht, one_smul]
  -- derivative of the right-hand side by the chain rule
  have hpair : HasDerivAt (fun ε : ℝ => (H ε x, ε)) (h1, 1) 0 := hHε.prodMk (hasDerivAt_id 0)
  have hR : HasDerivAt (fun ε => gx (H ε x, ε)) (D (h1, 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := gx) (f := fun ε : ℝ => (H ε x, ε)) 0 hg hpair
  have hL' : HasDerivAt (fun ε => gx (H ε x, ε)) (DH 0 (f (x, H 0 x))) 0 :=
    hL.congr_of_eventuallyEq (hinv.mono fun ε h => h.symm)
  exact hR.unique hL'

/-! ## Correction: `M₀` is not invariant -/

/-- Solution of `ẋ = 1`, `εẏ = x − y` from `(0, 0)`: `x = t`, `y = t − ε(1 − e^{−t/ε})`. -/
def exampleY (ε t : ℝ) : ℝ := t - ε * (1 - Real.exp (-t / ε))

@[powerlib_foundation] theorem exampleY_solves {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (exampleY ε) (ε⁻¹ * (t - exampleY ε t)) t := by
  show HasDerivAt (fun t => t - ε * (1 - Real.exp (-t / ε))) _ t
  have h := ((hasDerivAt_neg t).div_const ε).exp
  have h2 := (h.const_sub 1).const_mul ε
  have h3 := (hasDerivAt_id' t).sub h2
  convert h3 using 1
  simp only [exampleY]
  field_simp
  ring

@[powerlib_foundation] theorem exampleY_zero (ε : ℝ) : exampleY ε 0 = 0 := by
  simp [exampleY]

/-- Correction to `T-slow-manifold` §1.4: starting on `M₀ = {y = x}` (where `g = x − y = 0`), the
solution leaves `M₀` immediately: `y(t) − h(x(t)) = −ε(1 − e^{−t/ε}) ≠ 0` for `t ≠ 0`. -/
@[powerlib_foundation] theorem M0_not_invariant {ε t : ℝ} (hε : 0 < ε) (ht : t ≠ 0) :
    exampleY ε t - t ≠ 0 := by
  simp only [exampleY]
  intro h
  have : Real.exp (-t / ε) = 1 := by
    have : ε * (1 - Real.exp (-t / ε)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hε.ne'
    · linarith
  rw [Real.exp_eq_one_iff] at this
  apply ht
  have := div_eq_zero_iff.mp this
  rcases this with h1 | h1
  · linarith
  · exact absurd h1 hε.ne'

/-- On `M₀` the note's own derivative `d(y − h)/dt = −∂h/∂x · f_s` equals `−1 ≠ 0` here. -/
@[powerlib_foundation] theorem M0_drift {ε : ℝ} (hε : ε ≠ 0) :
    HasDerivAt (fun t => exampleY ε t - t) (ε⁻¹ * (0 - exampleY ε 0) - 1) 0 := by
  exact (exampleY_solves hε 0).sub (hasDerivAt_id 0)

end powerlib.SingularPerturbation
