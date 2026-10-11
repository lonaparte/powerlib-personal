import theorem.Hurwitz

/-! # One-dimensional vector fields as `State 1` systems

Foundation layer for the scalar normal forms (fold, transcritical, pitchfork).

A scalar autonomous ODE `ẋ = g x`, `x ∈ ℝ`, is represented on the powerlib state space
`State 1 = EuclideanSpace ℝ (Fin 1)` by the lifted field `lift g x = single 0 (g (x 0))`.
The only state variable is the coordinate `x 0`. Time is continuous; there is no input,
delay, PWM, PLL, saturation or noise. All stability predicates below are the powerlib /
LeanForControl trajectory predicates for the lifted field.

Contents.
* `embed`, `lift`: the embedding `ℝ → State 1` and the lifted field; norms and trajectories
  of the lifted system are exactly those of the scalar ODE (`isTrajectoryOn_lift_iff`).
* Jacobian of the lifted field: `fderiv ℝ (lift g) (embed r) = toEuclideanCLM !![g' r]`.
* Scalar linearization wrappers: `g r = 0`, `deriv g r < 0` ⇒ local exponential stability;
  `deriv g r > 0` ⇒ instability. They only repackage
  `powerlib.Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian` and
  `powerlib.Dynamics.unstable_of_jacobian_eigenvalue_re_pos` for `n = 1`.
* One-dimensional saddle-node hypersurface: `SaddleNodeCondition g ↔ ∃ x, g x = 0 ∧ deriv g x = 0`.

Source: work-sync theory/T-bifurcation.md §1.1–1.2, theory/T-bifurcation-hypersurfaces.md §1.2
(the 1D `Σ_SN` statement), theory/T-fold-bifurcation.md §1.2.
-/

noncomputable section
namespace powerlib.NormalForm
open Set Filter Topology Matrix
open powerlib.Dynamics (State)

/-- The embedding `r ↦ (r)` of the real line as the one-dimensional state space. -/
def embed (r : ℝ) : State 1 := EuclideanSpace.single 0 r

/-- The scalar field `g` lifted to `State 1`: the only coordinate evolves as `ẋ = g x`. -/
def lift (g : ℝ → ℝ) (x : State 1) : State 1 := embed (g (x 0))

@[simp, powerlib_foundation] theorem embed_apply (r : ℝ) (i : Fin 1) : embed r i = r := by
  fin_cases i
  simp [embed]

@[simp, powerlib_foundation] theorem embed_coord (x : State 1) : embed (x 0) = x := by
  ext i
  fin_cases i
  simp

@[powerlib_foundation] theorem embed_injective : Function.Injective embed := by
  intro r s h
  simpa using congrArg (fun x : State 1 => x 0) h

@[simp, powerlib_foundation] theorem embed_eq_iff {r s : ℝ} : embed r = embed s ↔ r = s :=
  embed_injective.eq_iff

@[simp, powerlib_foundation] theorem embed_zero : embed 0 = 0 := by
  ext i
  simp

@[powerlib_foundation] theorem embed_sub (r s : ℝ) : embed r - embed s = embed (r - s) := by
  ext i
  simp

@[simp, powerlib_foundation] theorem norm_embed (r : ℝ) : ‖embed r‖ = |r| := by
  simp [embed]

@[powerlib_foundation] theorem norm_state1 (x : State 1) : ‖x‖ = |x 0| := by
  rw [← embed_coord x, norm_embed, embed_apply]

@[simp, powerlib_foundation] theorem lift_apply (g : ℝ → ℝ) (x : State 1) (i : Fin 1) :
    lift g x i = g (x 0) := by
  simp [lift]

@[powerlib_foundation] theorem lift_embed (g : ℝ → ℝ) (r : ℝ) : lift g (embed r) = embed (g r) := by
  simp [lift]

@[powerlib_foundation] theorem lift_eq_zero_iff (g : ℝ → ℝ) (r : ℝ) :
    lift g (embed r) = 0 ↔ g r = 0 := by
  rw [lift_embed, ← embed_zero, embed_eq_iff]

/-- The scalar embedding as a continuous linear map. -/
def embedCLM : ℝ →L[ℝ] State 1 := (ContinuousLinearMap.id ℝ ℝ).smulRight (embed 1)

@[simp, powerlib_foundation] theorem embedCLM_apply (r : ℝ) : embedCLM r = embed r := by
  ext i
  simp [embedCLM]

/-- The coordinate of the one-dimensional state as a continuous linear functional. -/
def coordCLM : State 1 →L[ℝ] ℝ := EuclideanSpace.proj 0

@[simp, powerlib_foundation] theorem coordCLM_apply (x : State 1) : coordCLM x = x 0 := rfl

@[powerlib_foundation] theorem lift_eq_comp (g : ℝ → ℝ) :
    lift g = embedCLM ∘ g ∘ coordCLM := by
  funext x
  simp [lift]

@[powerlib_foundation] theorem lift_contDiff {g : ℝ → ℝ} {k : WithTop ℕ∞} (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (lift g) := by
  rw [lift_eq_comp]
  exact embedCLM.contDiff.comp (hg.comp coordCLM.contDiff)

/-- The Jacobian of the lifted scalar field is the `1 × 1` matrix of the scalar derivative. -/
@[powerlib_foundation] theorem hasFDerivAt_lift {g : ℝ → ℝ} {a : ℝ} {x : State 1}
    (hg : HasDerivAt g a (x 0)) :
    HasFDerivAt (lift g) (Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) !![a]) x := by
  have h1 : HasFDerivAt (fun y : State 1 => g (coordCLM y)) (a • coordCLM) x :=
    hg.comp_hasFDerivAt x coordCLM.hasFDerivAt
  have h2 := embedCLM.hasFDerivAt.comp x h1
  have hfun : (embedCLM ∘ fun y : State 1 => g (coordCLM y)) = lift g := by
    rw [lift_eq_comp]; rfl
  rw [hfun] at h2
  convert h2 using 1
  ext v i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]

@[powerlib_foundation] theorem fderiv_lift {g : ℝ → ℝ} {x : State 1}
    (hg : DifferentiableAt ℝ g (x 0)) :
    fderiv ℝ (lift g) x =
      Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) !![deriv g (x 0)] :=
  (hasFDerivAt_lift hg.hasDerivAt).fderiv

/-- A `1 × 1` real matrix is Hurwitz iff its entry is negative. -/
@[powerlib_foundation] theorem isHurwitz_one_iff (a : ℝ) :
    LinearSystems.IsHurwitz (!![a] : Matrix (Fin 1) (Fin 1) ℝ) ↔ a < 0 := by
  constructor
  · intro h
    have := h (a : ℂ) (fun _ => 1) (by intro h0; simpa using congrFun h0 0)
      (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct])
    simpa using this
  · intro ha μ v hv heig
    have hv0 : v 0 ≠ 0 := by
      intro h0; apply hv; ext i; fin_cases i; simpa using h0
    have h := congrFun heig 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Pi.smul_apply, smul_eq_mul] at h
    have hμ : μ = (a : ℂ) := (mul_right_cancel₀ hv0 h).symm
    rw [hμ]; simpa using ha

/-- The `1 × 1` matrix `(a)` with `a > 0` has the eigenpair `(a, 1)`. -/
@[powerlib_foundation] theorem exists_eigenpair_one_of_pos {a : ℝ} (ha : 0 < a) :
    ∃ (μ : ℂ) (v : Fin 1 → ℂ), v ≠ 0 ∧
      (!![a] : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re :=
  ⟨a, fun _ => 1, by intro h0; simpa using congrFun h0 0,
    by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct], by simpa using ha⟩

/-- Scalar linearization: an equilibrium with negative slope is locally exponentially stable. -/
@[powerlib_foundation] theorem lift_locallyExponentiallyStable {g : ℝ → ℝ} {r : ℝ}
    (hg : ContDiff ℝ 1 g) (h0 : g r = 0) (hslope : deriv g r < 0) :
    Dynamics.LocallyExponentiallyStable (lift g) (embed r) := by
  have hd : DifferentiableAt ℝ g r := hg.differentiable (by norm_num) r
  refine Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian !![deriv g r] (lift_contDiff hg)
    ((lift_eq_zero_iff g r).mpr h0) ?_ ((isHurwitz_one_iff _).mpr hslope)
  have := fderiv_lift (g := g) (x := embed r) (by simpa using hd)
  simpa using this

/-- Scalar linearization: an equilibrium with positive slope is unstable. -/
@[powerlib_foundation] theorem lift_unstable {g : ℝ → ℝ} {r : ℝ}
    (hg : ContDiff ℝ 1 g) (h0 : g r = 0) (hslope : 0 < deriv g r) :
    Dynamics.Unstable (lift g) (embed r) := by
  have hd : DifferentiableAt ℝ g r := hg.differentiable (by norm_num) r
  refine Dynamics.unstable_of_jacobian_eigenvalue_re_pos !![deriv g r] (lift_contDiff hg)
    ((lift_eq_zero_iff g r).mpr h0) ?_ (exists_eigenpair_one_of_pos hslope)
  have := fderiv_lift (g := g) (x := embed r) (by simpa using hd)
  simpa using this

/-- Lifting a scalar solution gives a solution of the lifted field. -/
@[powerlib_foundation] theorem hasDerivWithinAt_embed {ψ : ℝ → ℝ} {g : ℝ → ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt ψ (g (ψ t)) s t) :
    HasDerivWithinAt (fun τ => embed (ψ τ)) (lift g (embed (ψ t))) s t := by
  have := embedCLM.hasFDerivAt.comp_hasDerivWithinAt t h
  simpa [lift_embed, Function.comp_def] using this

/-- Trajectories of the lifted field are exactly the scalar solutions in the coordinate `x 0`. -/
@[powerlib_foundation] theorem isIntegralCurveOn_lift_iff {g : ℝ → ℝ} {φ : ℝ → State 1}
    {s : Set ℝ} :
    Dynamics.IsIntegralCurveOn φ (fun _ x => lift g x) s ↔
      Dynamics.IsIntegralCurveOn (fun t => φ t 0) (fun _ r => g r) s := by
  constructor
  · intro h t ht
    have := coordCLM.hasFDerivAt.comp_hasDerivWithinAt t (h t ht)
    simpa [Function.comp_def] using this
  · intro h t ht
    have := hasDerivWithinAt_embed (g := g) (h t ht)
    simpa using this

@[powerlib_foundation] theorem isTrajectoryOn_lift_iff {g : ℝ → ℝ} {φ : ℝ → State 1} {a b : ℝ} :
    Dynamics.IsTrajectoryOn φ (lift g) a b ↔
      Dynamics.IsIntegralCurveOn (fun t => φ t 0) (fun _ r => g r) (Icc a b) :=
  isIntegralCurveOn_lift_iff

@[powerlib_foundation] theorem isTrajectoryOn_embed {g : ℝ → ℝ} {ψ : ℝ → ℝ} {a b : ℝ}
    (h : Dynamics.IsIntegralCurveOn ψ (fun _ r => g r) (Icc a b)) :
    Dynamics.IsTrajectoryOn (fun t => embed (ψ t)) (lift g) a b :=
  isTrajectoryOn_lift_iff.mpr (by simpa only [embed_apply] using h)

/-- The one-dimensional saddle-node condition `Σ_SN`: some equilibrium has zero Jacobian. -/
def SaddleNodeCondition (g : ℝ → ℝ) : Prop :=
  ∃ x : State 1, lift g x = 0 ∧ fderiv ℝ (lift g) x = 0

/-- In one dimension `Σ_SN` is exactly `f = f_x = 0` at a common point. -/
@[powerlib_foundation] theorem saddleNodeCondition_iff {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    SaddleNodeCondition g ↔ ∃ r, g r = 0 ∧ deriv g r = 0 := by
  constructor
  · rintro ⟨x, hx, hJ⟩
    refine ⟨x 0, ?_, ?_⟩
    · have := congrFun (congrArg (fun y : State 1 => (y : Fin 1 → ℝ)) hx) 0
      simpa using this
    · rw [fderiv_lift (hg _)] at hJ
      have := congrArg (fun L : State 1 →L[ℝ] State 1 => (L (embed 1)) 0) hJ
      simpa [Matrix.mulVec, dotProduct] using this
  · rintro ⟨r, h0, h1⟩
    refine ⟨embed r, (lift_eq_zero_iff g r).mpr h0, ?_⟩
    rw [fderiv_lift (by simpa using hg r)]
    ext v i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, h1]

/-! ## Scalar solutions cannot reach an equilibrium in finite time -/

/-- A scalar solution of a `C¹` field that reaches the equilibrium `0` was already at `0`
(backward uniqueness, Mathlib `ODE_solution_unique_of_mem_Icc_left`). -/
@[powerlib_foundation] theorem eq_zero_of_eq_zero_later {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg0 : g 0 = 0) {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : Dynamics.IsIntegralCurveOn ψ (fun _ r => g r) (Icc a b))
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a b) (hz : ψ t₁ = 0) : ψ a = 0 := by
  rcases eq_or_lt_of_le ht₁.1 with h | hlt
  · rw [h]; exact hz
  have hsub : Icc a t₁ ⊆ Icc a b := Icc_subset_Icc_right ht₁.2
  have hcont : ContinuousOn ψ (Icc a t₁) := (hψ.continuousOn).mono hsub
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := t₁)).exists_bound_of_continuousOn hcont
  set R := max M 0
  obtain ⟨K, hK⟩ := (hg.contDiffOn (s := Metric.closedBall (0 : ℝ) R)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall 0 R) (isCompact_closedBall 0 R)
  have hderiv : ∀ t ∈ Ioc a t₁, HasDerivWithinAt ψ (g (ψ t)) (Iic t) t := by
    intro t ht
    have hmem : t ∈ Icc a b := ⟨ht.1.le, ht.2.trans ht₁.2⟩
    have h1 : HasDerivWithinAt ψ (g (ψ t)) (Icc a t) t :=
      (hψ t hmem).mono (Icc_subset_Icc_right (ht.2.trans ht₁.2))
    exact h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE ht.1)
  have heq := ODE_solution_unique_of_mem_Icc_left (v := fun _ r => g r)
    (s := fun _ => Metric.closedBall (0 : ℝ) R) (K := K) (f := ψ) (g := fun _ => (0 : ℝ))
    (fun _ _ => hK) hcont hderiv
    (fun t ht => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hM t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _))
    continuousOn_const
    (fun t _ => by simpa [hg0] using (hasDerivWithinAt_const t (Iic t) (0 : ℝ)))
    (fun _ _ => by simp [R])
    hz
  exact heq ⟨le_rfl, hlt.le⟩

/-- A scalar solution of a `C¹` field with equilibrium `0` keeps the sign of its initial value. -/
@[powerlib_foundation] theorem pos_of_pos {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hg0 : g 0 = 0)
    {ψ : ℝ → ℝ} {a b : ℝ} (hψ : Dynamics.IsIntegralCurveOn ψ (fun _ r => g r) (Icc a b))
    (ha : 0 < ψ a) : ∀ t ∈ Icc a b, 0 < ψ t := by
  intro t ht
  by_contra hle
  push Not at hle
  have hcont : ContinuousOn ψ (Icc a t) :=
    hψ.continuousOn.mono (Icc_subset_Icc_right ht.2)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' ht.1 hcont ⟨hle, ha.le⟩
  have := eq_zero_of_eq_zero_later hg hg0 hψ ⟨hc.1, hc.2.trans ht.2⟩ hc0
  linarith

@[powerlib_foundation] theorem neg_of_neg {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hg0 : g 0 = 0)
    {ψ : ℝ → ℝ} {a b : ℝ} (hψ : Dynamics.IsIntegralCurveOn ψ (fun _ r => g r) (Icc a b))
    (ha : ψ a < 0) : ∀ t ∈ Icc a b, ψ t < 0 := by
  have hg' : ContDiff ℝ 1 (fun r => -g (-r)) := (hg.comp contDiff_neg).neg
  have hψ' : Dynamics.IsIntegralCurveOn (fun t => -ψ t) (fun _ r => -g (-r)) (Icc a b) := by
    intro t ht
    have h := (hψ t ht).neg
    simp only [neg_neg]
    exact h
  intro t ht
  have := pos_of_pos hg' (by simp [hg0]) hψ' (by linarith) t ht
  linarith

/-- A real function with zero one-sided derivative along `Icc a b` is constant there. -/
@[powerlib_foundation] theorem eq_of_hasDerivWithinAt_zero {F : ℝ → ℝ} {a b : ℝ}
    (h : ∀ t ∈ Icc a b, HasDerivWithinAt F 0 (Icc a b) t) : ∀ t ∈ Icc a b, F t = F a := by
  apply constant_of_has_deriv_right_zero
  · intro t ht
    exact (h t ht).continuousWithinAt
  · intro t ht
    have h1 : HasDerivWithinAt F 0 (Icc t b) t :=
      (h t (Ico_subset_Icc_self ht)).mono (Icc_subset_Icc_left ht.1)
    exact h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ht.2)

end powerlib.NormalForm
