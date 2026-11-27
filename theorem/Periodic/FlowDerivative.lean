import theorem.Periodic.OrbitMultiplier
import theorem.Periodic.MeanTrace

/-! # Differentiability of the flow in the initial state: the first variation

The solution `x(t; s, ξ)` of `ẋ = G(t, x)`, `x(s) = ξ`, depends strictly (Fréchet)
differentiably on the initial state, and its derivative is the transition matrix `Φ_ξ(t, s)` of
the variational equation `ẏ = D_xG(t, x(t; s, ξ)) y` along it. For a periodic solution `x_*` the
period map `P(ξ) = x(T; 0, ξ)` therefore has the strict derivative `Φ(T, 0)`, the monodromy matrix
of the linearization along `x_*` (`Periodic.monodromy`, the Floquet multipliers of
`theorem/Periodic/Transition.lean`).

The proof is a Grönwall estimate. For three solutions `x₀, x₁, x₂` on `[s, t]` and the transition
matrix `Φ` of `A(r) = D_xG(r, x₀(r))`, the deviation `z = x₁ − x₂ − Φ(·, s)(x₁(s) − x₂(s))` solves
`ż = [G(x₁) − G(x₂) − A(x₁ − x₂)] + A z`, and the bracket is at most `η ‖x₁ − x₂‖` by the mean
value theorem when `D_xG` varies by at most `η` on the tube of radius `ρ` around `x₀` that both
solutions stay in. This two-point estimate gives strict differentiability (the modulus `η → 0` as
`ρ → 0`, by uniform continuity of `D_xG` near the compact trajectory) and, for a Lipschitz
derivative, the quadratic remainder.

Scope.
* `ẋ = G(t, x)` on `ℝ^X` (`X → ℝ`, finite `X`, sup norm, operator `L∞` norm on matrices, as in
  `theorem/Periodic/Transition.lean`), continuous time, forward solutions on segments `[s, t]`
  (Mathlib `IsIntegralCurveOn`). `G(t, ·)` is differentiable with `D_xG` (`fderiv ℝ (G t)`) jointly
  continuous in `(t, x)` and `G(t, ·)` is `K`-Lipschitz uniformly in `t` (global form; a local
  field is reduced to it by a cut-off, e.g. `Periodic.clampField`, before the theorems apply).
* The derivative is stated for any continuous matrix function `A` that equals `D_xG` along the
  reference solution on `[s, t]` (`A r *ᵥ v = D_xG(r, x₀ r) v`); along a continuous curve the
  canonical choice is `jacobianAlong G x`, which for an autonomous field is the
  `variationalMatrix` of `theorem/Periodic/OrbitMultiplier.lean` (`jacobianAlong_const`, by
  definition).
* The solutions are any family `φ ξ` with `φ ξ s = ξ` solving the equation on `[s, t]`; for a
  continuous field one such family is `flow` (LeanForControl's Picard–Lindelöf theorem
  `exists_isIntegralCurveOn_Ici`, chosen), and `periodMap` is `ξ ↦ flow 0 ξ T`.
* Generic mathematics; no model family. Neither Mathlib nor LeanForControl differentiates ODE
  solutions with respect to the initial state; this module supplies it.

Source: the first-variation theorem for ODEs (Hartman, *Ordinary Differential Equations*, Ch. V,
Thm. 3.1: differentiability with respect to initial conditions, the derivative solving the
variational equation; Coddington–Levinson, Ch. 1, Thm. 7.2), proved here by the Grönwall
inequality (Mathlib `norm_le_gronwallBound_of_norm_deriv_right_le`) and the mean value
inequality (Mathlib `Convex.norm_image_sub_le_of_norm_fderiv_le'`); the open item of
`theorem/Periodic/FlipReduction.lean` (Scope: the period map's `DP(x_*(0)) = Φ(T, 0)` was a
hypothesis there).

Results.
* `norm_le_of_hasDerivWithinAt` — Grönwall: `‖w(s)‖ ≤ δ`, `‖ẇ‖ ≤ K‖w‖ + ε` on `[s, t]` gives
  `‖w(r)‖ ≤ (δ + ε (t − s)) e^{K(t − s)}` on `[s, t]`.
* `jacobianAlong`, `jacobianAlong_mulVec`, `jacobianAlong_const`, `continuous_jacobianAlong` —
  the matrix `A(t) = D_xG(t, x(t))`.
* `norm_sub_sub_transition_le` — the two-point first-variation estimate
  `‖x₁(t) − x₂(t) − Φ(t, s)(x₁(s) − x₂(s))‖ ≤ η (t − s) e^{2K(t − s)} ‖x₁(s) − x₂(s)‖`.
* `exists_radius_fderiv_le` — the modulus of continuity of `D_xG` along a compact trajectory.
* `hasStrictFDerivAt_solution` — `ξ ↦ φ ξ t` has the strict derivative `Φ(t, s)` at `ξ₀`.
* `norm_solution_sub_le_sq` — for `D_xG` Lipschitz with constant `L₂`:
  `‖x₁(t) − x₀(t) − Φ(t, s) e‖ ≤ L₂ (t − s) e^{3K(t − s)} ‖e‖²`, `e = x₁(s) − x₀(s)`.
* `flow`, `flow_start`, `flow_solution`, `flow_eq`, `hasStrictFDerivAt_flow` — the solution
  family of a continuous field and its strict derivative.
* `periodMap`, `periodMap_fixed`, `hasStrictFDerivAt_periodMap` — for a solution `x_*` the period
  map has the strict derivative `monodromy (jacobianAlong G x_*) T 0` at `x_*(0)`, and fixes
  `x_*(0)` when `x_*` is `T`-periodic; `hasStrictFDerivAt_periodMap_autonomous` — the same with
  `monodromy (variationalMatrix f x_*) T 0` for an autonomous field.

Corrections.
None: an extension (the derivative of the period map, a hypothesis of
`theorem/Periodic/FlipReduction.lean`, derived from the field).

Family and connection conclusions.
None: static evidence on nonautonomous ODEs (differentiable dependence on the initial state).
-/

noncomputable section
namespace powerlib.Periodic.FlowDerivative

open Set Matrix Function Filter Topology Asymptotics
open scoped Matrix.Norms.Operator

/-! ## A Grönwall bound with a source term -/

section Gronwall

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Grönwall with a source.** If `w` has derivative `w'` within `[s, t]`, `‖w'‖ ≤ K ‖w‖ + ε`
on `[s, t)` and `‖w(s)‖ ≤ δ`, then `‖w(r)‖ ≤ (δ + ε (t − s)) e^{K (t − s)}` on `[s, t]`. -/
@[tmio T, powerlib_foundation] theorem norm_le_of_hasDerivWithinAt {w w' : ℝ → F}
    {s t K ε δ : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hw : ∀ r ∈ Icc s t, HasDerivWithinAt w (w' r) (Icc s t) r)
    (hb : ∀ r ∈ Ico s t, ‖w' r‖ ≤ K * ‖w r‖ + ε) (h0 : ‖w s‖ ≤ δ) :
    ∀ r ∈ Icc s t, ‖w r‖ ≤ (δ + ε * (t - s)) * Real.exp (K * (t - s)) := by
  intro r hr
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h0
  have hc : ContinuousOn w (Icc s t) := fun q hq => (hw q hq).continuousWithinAt
  have hd : ∀ q ∈ Ico s t, HasDerivWithinAt w (w' q) (Ici q) q := fun q hq =>
    (hw q (Ico_subset_Icc_self hq)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hq)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc hd h0 hb r hr
  have hx : 0 ≤ r - s := sub_nonneg.2 hr.1
  have hxt : r - s ≤ t - s := by linarith [hr.2]
  have key : gronwallBound δ K ε (r - s) ≤ (δ + ε * (r - s)) * Real.exp (K * (r - s)) := by
    rcases hK.eq_or_lt with h | hKpos
    · subst h
      simp [gronwallBound_K0]
    · rw [gronwallBound_of_K_ne_0 hKpos.ne']
      have h1 : Real.exp (K * (r - s)) - 1 ≤ K * (r - s) * Real.exp (K * (r - s)) := by
        have h := Real.add_one_le_exp (-(K * (r - s)))
        have hexp : Real.exp (-(K * (r - s))) * Real.exp (K * (r - s)) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [mul_le_mul_of_nonneg_right h (Real.exp_pos (K * (r - s))).le]
      have h2 : ε / K * (Real.exp (K * (r - s)) - 1) ≤ ε * (r - s) * Real.exp (K * (r - s)) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
        nlinarith [mul_le_mul_of_nonneg_left h1 hε]
      show δ * Real.exp (K * (r - s)) + ε / K * (Real.exp (K * (r - s)) - 1) ≤ _
      nlinarith
  refine hg.trans (key.trans ?_)
  have he : Real.exp (K * (r - s)) ≤ Real.exp (K * (t - s)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxt hK)
  have hpos : 0 ≤ δ + ε * (r - s) := by positivity
  calc (δ + ε * (r - s)) * Real.exp (K * (r - s))
      ≤ (δ + ε * (t - s)) * Real.exp (K * (r - s)) := by
        gcongr
    _ ≤ (δ + ε * (t - s)) * Real.exp (K * (t - s)) := by
        gcongr
        nlinarith

end Gronwall

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The variational matrix along a curve -/

/-- The variational matrix `A(t) = D_xG(t, x(t))` of `ẋ = G(t, x)` along a curve `x`. -/
def jacobianAlong (G : ℝ → (X → ℝ) → X → ℝ) (x : ℝ → X → ℝ) (t : ℝ) : Matrix X X ℝ :=
  LinearMap.toMatrix' (fderiv ℝ (G t) (x t) : (X → ℝ) →ₗ[ℝ] X → ℝ)

@[tmio T, powerlib_foundation] theorem jacobianAlong_mulVec (G : ℝ → (X → ℝ) → X → ℝ)
    (x : ℝ → X → ℝ) (t : ℝ) (v : X → ℝ) :
    jacobianAlong G x t *ᵥ v = fderiv ℝ (G t) (x t) v := by
  rw [jacobianAlong, LinearMap.toMatrix'_mulVec]
  rfl

/-- For an autonomous field the variational matrix along `x` is `variationalMatrix f x`. -/
@[tmio T, powerlib_foundation] theorem jacobianAlong_const (f : (X → ℝ) → X → ℝ)
    (x : ℝ → X → ℝ) : jacobianAlong (fun _ => f) x = variationalMatrix f x := rfl

@[tmio T, powerlib_foundation] theorem continuous_jacobianAlong {G : ℝ → (X → ℝ) → X → ℝ}
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) {x : ℝ → X → ℝ}
    (hx : Continuous x) : Continuous (jacobianAlong G x) := by
  have hc : Continuous fun t => fderiv ℝ (G t) (x t) := hD.comp (continuous_id.prodMk hx)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t => jacobianAlong G x t i j) = fun t => fderiv ℝ (G t) (x t) (Pi.single j 1) i := by
    funext t
    simp [jacobianAlong, LinearMap.toMatrix'_apply]
  rw [this]
  exact (continuous_apply i).comp
    ((ContinuousLinearMap.apply ℝ (X → ℝ) (Pi.single j 1)).continuous.comp hc)

/-! ## The first-variation estimate -/

/-- `t ↦ Φ(t, s) v` solves `ẏ = A(t) y` on all of `ℝ`, from any initial time `s` (the case
`s = 0` is `Periodic.hasDerivAt_transition_mulVec` of `theorem/Periodic/MeanTrace.lean`). -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transition_mulVec {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) (s : ℝ) (v : X → ℝ) (r : ℝ) :
    HasDerivAt (fun r => transition A r s *ᵥ v) (A r *ᵥ (transition A r s *ᵥ v)) r := by
  set L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip v) with hL
  have hL_apply : ∀ M' : Matrix X X ℝ, L M' = M' *ᵥ v := fun M' => rfl
  have h := L.hasFDerivAt.comp_hasDerivAt r (Dynamics.stm_hasDerivAt hA r s)
  convert h using 1
  · funext q
    exact (hL_apply _).symm
  · show A r *ᵥ (transition A r s *ᵥ v) = (A r * transition A r s) *ᵥ v
    exact Matrix.mulVec_mulVec _ _ _

/-- **The two-point first-variation estimate.** Let `x₀, x₁, x₂` solve `ẋ = G(t, x)` on
`[s, t]`, let `A` be continuous with `A(r) = D_xG(r, x₀(r))` there, and let `D_xG` vary by at most
`η` from its value on `x₀` within the tube of radius `ρ` around `x₀`, which `x₁` and `x₂` do not
leave (`‖x_i(s) − x₀(s)‖ e^{K(t − s)} ≤ ρ`). Then the deviation from the linear prediction is
`‖x₁(t) − x₂(t) − Φ(t, s)(x₁(s) − x₂(s))‖ ≤ η (t − s) e^{2K(t − s)} ‖x₁(s) − x₂(s)‖`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_sub_transition_le
    {G : ℝ → (X → ℝ) → X → ℝ} {K : NNReal}
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x) (hK : ∀ t, LipschitzWith K (G t))
    {A : ℝ → Matrix X X ℝ} (hAc : Continuous A) {s t : ℝ} (hst : s ≤ t)
    {x₀ x₁ x₂ : ℝ → X → ℝ}
    (hA : ∀ r ∈ Icc s t, ∀ v, A r *ᵥ v = fderiv ℝ (G r) (x₀ r) v)
    (h₀ : IsIntegralCurveOn x₀ G (Icc s t)) (h₁ : IsIntegralCurveOn x₁ G (Icc s t))
    (h₂ : IsIntegralCurveOn x₂ G (Icc s t)) {ρ η : ℝ}
    (hη : ∀ r ∈ Icc s t, ∀ ζ, ‖ζ - x₀ r‖ ≤ ρ →
      ‖fderiv ℝ (G r) ζ - fderiv ℝ (G r) (x₀ r)‖ ≤ η)
    (hρ₁ : ‖x₁ s - x₀ s‖ * Real.exp (K * (t - s)) ≤ ρ)
    (hρ₂ : ‖x₂ s - x₀ s‖ * Real.exp (K * (t - s)) ≤ ρ) :
    ‖x₁ t - x₂ t - transition A t s *ᵥ (x₁ s - x₂ s)‖ ≤
      η * (t - s) * Real.exp (2 * (K * (t - s))) * ‖x₁ s - x₂ s‖ := by
  set E := Real.exp (K * (t - s)) with hE
  set Δ := x₁ s - x₂ s with hΔ
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hρ : 0 ≤ ρ := le_trans (by positivity) hρ₁
  have hη0 : 0 ≤ η :=
    (norm_nonneg _).trans (hη s ⟨le_rfl, hst⟩ (x₀ s) (by simpa using hρ))
  have hexp : ∀ r ∈ Icc s t, Real.exp (K * (r - s)) ≤ E := fun r hr =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hr.2]) K.2)
  -- the solutions stay in the tube
  have htube : ∀ {y : ℝ → X → ℝ}, IsIntegralCurveOn y G (Icc s t) → ‖y s - x₀ s‖ * E ≤ ρ →
      ∀ r ∈ Icc s t, ‖y r - x₀ r‖ ≤ ρ := by
    intro y hy hyρ r hr
    have h := dist_le_of_isIntegralCurveOn_Icc hK hy h₀ r hr
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hexp r hr) (norm_nonneg _)).trans hyρ)
  have hsep : ∀ r ∈ Icc s t, ‖x₁ r - x₂ r‖ ≤ ‖Δ‖ * E := by
    intro r hr
    have h := dist_le_of_isIntegralCurveOn_Icc hK h₁ h₂ r hr
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hexp r hr) (norm_nonneg _))
  -- the deviation from the linear prediction
  set z : ℝ → X → ℝ := fun r => x₁ r - x₂ r - transition A r s *ᵥ Δ with hz
  have hzd : ∀ r ∈ Icc s t, HasDerivWithinAt z
      (G r (x₁ r) - G r (x₂ r) - A r *ᵥ (transition A r s *ᵥ Δ)) (Icc s t) r :=
    fun r hr => ((h₁ r hr).sub (h₂ r hr)).sub
      (hasDerivAt_transition_mulVec hAc s Δ r).hasDerivWithinAt
  have hz0 : ‖z s‖ ≤ 0 := by
    simp [hz, hΔ, LinearSystems.stateTransitionMatrix_self]
  have hbound : ∀ r ∈ Ico s t, ‖G r (x₁ r) - G r (x₂ r) - A r *ᵥ (transition A r s *ᵥ Δ)‖ ≤
      K * ‖z r‖ + η * ‖Δ‖ * E := by
    intro r hr
    have hr' : r ∈ Icc s t := Ico_subset_Icc_self hr
    set φ := fderiv ℝ (G r) (x₀ r) with hφ
    have hmv : ‖G r (x₁ r) - G r (x₂ r) - φ (x₁ r - x₂ r)‖ ≤ η * ‖x₁ r - x₂ r‖ :=
      (convex_closedBall (x₀ r) ρ).norm_image_sub_le_of_norm_fderiv_le'
        (fun ζ _ => hGd r ζ)
        (fun ζ hζ => hη r hr' ζ (by rwa [Metric.mem_closedBall, dist_eq_norm] at hζ))
        (by rw [Metric.mem_closedBall, dist_eq_norm]; exact htube h₂ hρ₂ r hr')
        (by rw [Metric.mem_closedBall, dist_eq_norm]; exact htube h₁ hρ₁ r hr')
    have he : G r (x₁ r) - G r (x₂ r) - A r *ᵥ (transition A r s *ᵥ Δ) =
        (G r (x₁ r) - G r (x₂ r) - φ (x₁ r - x₂ r)) + φ (z r) := by
      rw [hA r hr']
      simp only [hz, map_sub]
      abel
    rw [he]
    have hφz : ‖φ (z r)‖ ≤ K * ‖z r‖ :=
      (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitz ℝ (hK r)) (norm_nonneg _))
    have h3 := mul_le_mul_of_nonneg_left (hsep r hr') hη0
    calc _ ≤ ‖G r (x₁ r) - G r (x₂ r) - φ (x₁ r - x₂ r)‖ + ‖φ (z r)‖ := norm_add_le _ _
      _ ≤ K * ‖z r‖ + η * ‖Δ‖ * E := by nlinarith
  have h := norm_le_of_hasDerivWithinAt K.2 (by positivity) hzd hbound hz0 t ⟨hst, le_rfl⟩
  have hE2 : Real.exp (2 * (K * (t - s))) = E * E := by
    rw [hE, ← Real.exp_add]; ring_nf
  calc ‖z t‖ ≤ (0 + η * ‖Δ‖ * E * (t - s)) * E := h
    _ = η * (t - s) * Real.exp (2 * (K * (t - s))) * ‖Δ‖ := by rw [hE2]; ring

omit [DecidableEq X] in
/-- **The modulus of continuity of `D_xG` along a trajectory.** For `D_xG` jointly continuous
and a curve `x₀` continuous on `[s, t]`, every `η > 0` has a radius `ρ > 0` with
`‖D_xG(r, ζ) − D_xG(r, x₀(r))‖ ≤ η` whenever `r ∈ [s, t]` and `‖ζ − x₀(r)‖ ≤ ρ`. -/
@[tmio T, powerlib_foundation] theorem exists_radius_fderiv_le {G : ℝ → (X → ℝ) → X → ℝ}
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) {x₀ : ℝ → X → ℝ} {s t : ℝ}
    (hx : ContinuousOn x₀ (Icc s t)) {η : ℝ} (hη : 0 < η) :
    ∃ ρ, 0 < ρ ∧ ∀ r ∈ Icc s t, ∀ ζ, ‖ζ - x₀ r‖ ≤ ρ →
      ‖fderiv ℝ (G r) ζ - fderiv ℝ (G r) (x₀ r)‖ ≤ η := by
  set S := (fun r => (r, x₀ r)) '' Icc s t with hSdef
  have hS : IsCompact S := isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hx)
  have hU := hS.uniformContinuousAt_of_continuousAt
    (fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) (fun p _ => hD.continuousAt)
    (Metric.dist_mem_uniformity hη)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.1 hU
  refine ⟨δ / 2, half_pos hδ, fun r hr ζ hζ => ?_⟩
  have hd : dist (r, x₀ r) (r, ζ) < δ := by
    rw [Prod.dist_eq, dist_self, dist_comm, dist_eq_norm]
    exact max_lt hδ (by linarith)
  have h := hδU hd ⟨r, hr, rfl⟩
  simp only [Set.mem_ofPred_eq] at h
  rw [dist_comm, dist_eq_norm] at h
  exact h.le

/-- **The flow is strictly differentiable in the initial state.** Let `φ ξ` solve
`ẋ = G(t, x)` on `[s, t]` with `φ ξ s = ξ` for every `ξ`, where `G(r, ·)` is differentiable with
`D_xG` jointly continuous and `G(r, ·)` is `K`-Lipschitz. Then `ξ ↦ φ ξ t` has at `ξ₀` the strict
derivative `Φ(t, s)`, the transition matrix of the variational equation `ẏ = A(r) y` along
`φ ξ₀` (`A` continuous, `A(r) = D_xG(r, φ ξ₀ r)` on `[s, t]`). -/
@[tmio T, powerlib_foundation] theorem hasStrictFDerivAt_solution
    {G : ℝ → (X → ℝ) → X → ℝ} {K : NNReal} (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {s t : ℝ} (hst : s ≤ t)
    {φ : (X → ℝ) → ℝ → X → ℝ} (hφs : ∀ ξ, φ ξ s = ξ)
    (hφ : ∀ ξ, IsIntegralCurveOn (φ ξ) G (Icc s t)) {ξ₀ : X → ℝ} {A : ℝ → Matrix X X ℝ}
    (hAc : Continuous A) (hA : ∀ r ∈ Icc s t, ∀ v, A r *ᵥ v = fderiv ℝ (G r) (φ ξ₀ r) v) :
    HasStrictFDerivAt (fun ξ => φ ξ t)
      (Matrix.toLin' (transition A t s)).toContinuousLinearMap ξ₀ := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  set E := Real.exp (K * (t - s)) with hE
  set C := (t - s) * Real.exp (2 * (K * (t - s))) with hC
  have hC0 : 0 ≤ C := by positivity
  set η := c / (C + 1) with hηdef
  have hη : 0 < η := div_pos hc (by linarith)
  obtain ⟨ρ, hρ, hρη⟩ := exists_radius_fderiv_le hD (hφ ξ₀).continuousOn hη
  have hcont : Continuous fun p : (X → ℝ) × (X → ℝ) =>
      max (‖p.1 - ξ₀‖ * E) (‖p.2 - ξ₀‖ * E) := by fun_prop
  have hball : ∀ᶠ p : (X → ℝ) × (X → ℝ) in 𝓝 (ξ₀, ξ₀),
      max (‖p.1 - ξ₀‖ * E) (‖p.2 - ξ₀‖ * E) < ρ :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hρ)
  filter_upwards [hball] with p hp
  have h1 : ‖φ p.1 s - φ ξ₀ s‖ * E ≤ ρ := by
    rw [hφs, hφs]; exact (le_max_left _ _).trans hp.le
  have h2 : ‖φ p.2 s - φ ξ₀ s‖ * E ≤ ρ := by
    rw [hφs, hφs]; exact (le_max_right _ _).trans hp.le
  have h := norm_sub_sub_transition_le hGd hK hAc hst hA (hφ ξ₀) (hφ p.1) (hφ p.2) hρη h1 h2
  rw [hφs, hφs] at h
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
  have hηC : η * C ≤ c := by
    rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  calc ‖φ p.1 t - φ p.2 t - transition A t s *ᵥ (p.1 - p.2)‖
      ≤ η * (t - s) * Real.exp (2 * (K * (t - s))) * ‖p.1 - p.2‖ := h
    _ = η * C * ‖p.1 - p.2‖ := by rw [hC]; ring
    _ ≤ c * ‖p.1 - p.2‖ := mul_le_mul_of_nonneg_right hηC (norm_nonneg _)

/-- **Quadratic remainder for a Lipschitz derivative.** If `D_xG(r, ·)` is `L₂`-Lipschitz on
`[s, t]`, two solutions `x₀, x₁` with `e = x₁(s) − x₀(s)` satisfy
`‖x₁(t) − x₀(t) − Φ(t, s) e‖ ≤ L₂ (t − s) e^{3K(t − s)} ‖e‖²`, `Φ` the transition matrix along
`x₀`. -/
@[tmio T, powerlib_foundation] theorem norm_solution_sub_le_sq
    {G : ℝ → (X → ℝ) → X → ℝ} {K : NNReal}
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x) (hK : ∀ t, LipschitzWith K (G t))
    {A : ℝ → Matrix X X ℝ} (hAc : Continuous A) {s t : ℝ} (hst : s ≤ t) {x₀ x₁ : ℝ → X → ℝ}
    (hA : ∀ r ∈ Icc s t, ∀ v, A r *ᵥ v = fderiv ℝ (G r) (x₀ r) v)
    (h₀ : IsIntegralCurveOn x₀ G (Icc s t)) (h₁ : IsIntegralCurveOn x₁ G (Icc s t)) {L₂ : NNReal}
    (hL : ∀ r ∈ Icc s t, ∀ ζ ζ', ‖fderiv ℝ (G r) ζ - fderiv ℝ (G r) ζ'‖ ≤ L₂ * ‖ζ - ζ'‖) :
    ‖x₁ t - x₀ t - transition A t s *ᵥ (x₁ s - x₀ s)‖ ≤
      L₂ * (t - s) * Real.exp (3 * (K * (t - s))) * ‖x₁ s - x₀ s‖ ^ 2 := by
  set E := Real.exp (K * (t - s)) with hE
  set ρ := ‖x₁ s - x₀ s‖ * E with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hη : ∀ r ∈ Icc s t, ∀ ζ, ‖ζ - x₀ r‖ ≤ ρ →
      ‖fderiv ℝ (G r) ζ - fderiv ℝ (G r) (x₀ r)‖ ≤ L₂ * ρ := fun r hr ζ hζ =>
    (hL r hr ζ (x₀ r)).trans (mul_le_mul_of_nonneg_left hζ L₂.2)
  have h := norm_sub_sub_transition_le hGd hK hAc hst hA h₀ h₁ h₀ hη le_rfl
    (by simpa using hρ0)
  have hE3 : Real.exp (3 * (K * (t - s))) = Real.exp (2 * (K * (t - s))) * E := by
    rw [hE, ← Real.exp_add]; ring_nf
  calc _ ≤ L₂ * ρ * (t - s) * Real.exp (2 * (K * (t - s))) * ‖x₁ s - x₀ s‖ := h
    _ = L₂ * (t - s) * Real.exp (3 * (K * (t - s))) * ‖x₁ s - x₀ s‖ ^ 2 := by
      rw [hE3, hρ]; ring

/-! ## The flow of a continuous field and the period map -/

section Flow

variable {G : ℝ → (X → ℝ) → X → ℝ} {K : NNReal}

/-- The solution of `ẋ = G(t, x)` with `x(s) = ξ` on `[s, ∞)`: LeanForControl's Picard–Lindelöf
theorem `exists_isIntegralCurveOn_Ici` for a continuous, globally Lipschitz field (chosen; every
other solution agrees with it on `[s, ∞)`, `flow_eq`). -/
def flow (hGc : Continuous (uncurry G)) (hK : ∀ t, LipschitzWith K (G t)) (s : ℝ)
    (ξ : X → ℝ) : ℝ → X → ℝ :=
  (exists_isIntegralCurveOn_Ici hGc hK s ξ).choose

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem flow_start (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) (s : ℝ) (ξ : X → ℝ) : flow hGc hK s ξ s = ξ :=
  (exists_isIntegralCurveOn_Ici hGc hK s ξ).choose_spec.1

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem flow_solution (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) (s : ℝ) (ξ : X → ℝ) :
    IsIntegralCurveOn (flow hGc hK s ξ) G (Ici s) :=
  (exists_isIntegralCurveOn_Ici hGc hK s ξ).choose_spec.2.1

omit [DecidableEq X] in
/-- Every solution on `[s, t]` from `ξ` is the flow there. -/
@[tmio T, powerlib_foundation] theorem flow_eq (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {s t : ℝ} {ξ : X → ℝ} {β : ℝ → X → ℝ} (hβ0 : β s = ξ)
    (hβ : IsIntegralCurveOn β G (Icc s t)) : ∀ r ∈ Icc s t, β r = flow hGc hK s ξ r :=
  fun _ hr => eqOn_of_isIntegralCurveOn_Icc hK hβ
    ((flow_solution hGc hK s ξ).mono Icc_subset_Ici_self) (hβ0.trans (flow_start hGc hK s ξ).symm)
    hr

/-- **The derivative of the flow.** `ξ ↦ x(t; s, ξ)` has at `ξ₀` the strict derivative
`Φ(t, s)` of the variational equation along `x(·; s, ξ₀)`. -/
@[tmio T, powerlib_foundation] theorem hasStrictFDerivAt_flow (hGc : Continuous (uncurry G))
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {s t : ℝ} (hst : s ≤ t) {ξ₀ : X → ℝ}
    {A : ℝ → Matrix X X ℝ} (hAc : Continuous A)
    (hA : ∀ r ∈ Icc s t, ∀ v, A r *ᵥ v = fderiv ℝ (G r) (flow hGc hK s ξ₀ r) v) :
    HasStrictFDerivAt (fun ξ => flow hGc hK s ξ t)
      (Matrix.toLin' (transition A t s)).toContinuousLinearMap ξ₀ :=
  hasStrictFDerivAt_solution hGd hD hK hst (flow_start hGc hK s)
    (fun ξ => (flow_solution hGc hK s ξ).mono Icc_subset_Ici_self) hAc hA

/-- The period map `P(ξ) = x(T; 0, ξ)`. -/
def periodMap (hGc : Continuous (uncurry G)) (hK : ∀ t, LipschitzWith K (G t)) (T : ℝ) :
    (X → ℝ) → X → ℝ :=
  fun ξ => flow hGc hK 0 ξ T

omit [DecidableEq X] in
/-- A solution with `x_*(T) = x_*(0)` (a `T`-periodic solution) starts at a fixed point of the
period map. -/
@[tmio T, powerlib_foundation] theorem periodMap_fixed (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {xs : ℝ → X → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {T : ℝ} (hT : 0 ≤ T) (hper : xs T = xs 0) :
    periodMap hGc hK T (xs 0) = xs 0 := by
  rw [periodMap, ← flow_eq hGc hK rfl (fun r _ => (hxs r).hasDerivWithinAt) T ⟨hT, le_rfl⟩, hper]

/-- **The derivative of the period map is the monodromy.** For a global solution `x_*` the
period map has at `x_*(0)` the strict derivative `Φ(T, 0) = monodromy (jacobianAlong G x_*) T 0`,
the monodromy matrix of the variational equation along `x_*`. -/
@[tmio T, powerlib_foundation] theorem hasStrictFDerivAt_periodMap
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {xs : ℝ → X → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {T : ℝ} (hT : 0 ≤ T) :
    HasStrictFDerivAt (periodMap hGc hK T)
      (Matrix.toLin' (monodromy (jacobianAlong G xs) T 0)).toContinuousLinearMap (xs 0) := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have h := hasStrictFDerivAt_flow hGc hGd hD hK hT (ξ₀ := xs 0)
    (continuous_jacobianAlong hD hxc) fun r hr v => by
      rw [jacobianAlong_mulVec,
        ← flow_eq hGc hK rfl (fun q _ => (hxs q).hasDerivWithinAt) r hr]
  rw [monodromy, zero_add]
  exact h

/-- **Autonomous fields.** For `ẋ = f(x)` with `f` of class `C¹` and globally Lipschitz, the
period map has at `x_*(0)` the strict derivative `monodromy (variationalMatrix f x_*) T 0`. -/
@[tmio T, powerlib_foundation] theorem hasStrictFDerivAt_periodMap_autonomous
    {f : (X → ℝ) → X → ℝ} (hf : ContDiff ℝ 1 f) (hfK : LipschitzWith K f) {xs : ℝ → X → ℝ}
    (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 ≤ T) :
    HasStrictFDerivAt
      (periodMap (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) T)
      (Matrix.toLin' (monodromy (variationalMatrix f xs) T 0)).toContinuousLinearMap (xs 0) :=
  hasStrictFDerivAt_periodMap (G := fun _ => f) _ (fun _ => hf.differentiable one_ne_zero)
    ((hf.continuous_fderiv one_ne_zero).comp continuous_snd) (fun _ => hfK) hxs hT

end Flow

end powerlib.Periodic.FlowDerivative
