import theorem.Flow.Linearization
import theorem.Dynamics.State
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Shared infrastructure for the GFL parametric-oscillation models

Foundation layer only (plus thin generic corollaries of the linearization principle).
Nothing in this file concerns a particular converter; it supplies the plumbing used by the
model files in `theorem/GFLParametric/`.

* `lift F`: a field on coordinates `Fin n → ℝ` transported to the Euclidean state space
  `Dynamics.State n`; its Fréchet derivative is `toEuclideanCLM A` whenever the coordinate
  field has derivative `toLin' A` (`hasFDerivAt_lift`).
* Locality of the local stability predicates: two vector fields that agree on a ball around
  an equilibrium are simultaneously locally exponentially stable / Lyapunov stable /
  unstable there (`locallyExponentiallyStable_of_eqOn_ball`, `unstable_of_eqOn_ball`).
  The proof is the usual first-exit (bootstrap) argument on finite solution segments.
  This is what lets a model with a `1 / V` nonlinearity (not globally `C¹`) use the
  global-`C¹` linearization theorems of `theorem/Flow/Linearization.lean`: they are applied to a
  globally smooth field that coincides with the physical one near the equilibrium, and the
  conclusion is transported back.
* `invExt`: a globally smooth function equal to `V⁻¹` for `V ≥ 1/2`.

Family and connection conclusions. Nothing here concerns a model, so the module has no Family.
The two linearization-through-extension statements
(`locallyExponentiallyStable_of_isHurwitz_jacobian_of_eqOn_ball`,
`unstable_of_jacobian_eigenvalue_re_pos_of_eqOn_ball`), formerly domain-labelled, are generic
implications for an arbitrary field and are foundation results; the model families of this
directory use them inside their soundness proofs.

Source: infrastructure for work-sync `projects/vsc-parametric-oscillation` and
`projects/gfl-gfm-stability-tree` (no engineering content).
-/

noncomputable section
namespace powerlib.GFLParametric
open Set Filter Topology Matrix

variable {n : ℕ}

/-! ## Coordinates on the Euclidean state space -/

/-- A field on plain coordinates, transported to `Dynamics.State n`. -/
def lift (F : (Fin n → ℝ) → (Fin n → ℝ)) (x : Dynamics.State n) : Dynamics.State n :=
  WithLp.toLp 2 (F (WithLp.ofLp x))

@[simp, powerlib_foundation] theorem lift_toLp (F : (Fin n → ℝ) → (Fin n → ℝ))
    (v : Fin n → ℝ) : lift F (WithLp.toLp 2 v) = WithLp.toLp 2 (F v) := rfl

@[powerlib_foundation] theorem lift_toLp_eq_zero {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {v : Fin n → ℝ} (h : F v = 0) : lift F (WithLp.toLp 2 v) = 0 := by
  rw [lift_toLp, h]
  rfl

@[powerlib_foundation] theorem hasFDerivAt_lift {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} {x : Dynamics.State n}
    (h : HasFDerivAt F (Matrix.toLin' A).toContinuousLinearMap (WithLp.ofLp x)) :
    HasFDerivAt (lift F) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have h1 : HasFDerivAt (fun y : Dynamics.State n => F (e y))
      ((Matrix.toLin' A).toContinuousLinearMap.comp (e : Dynamics.State n →L[ℝ] (Fin n → ℝ)))
      x := h.comp x e.hasFDerivAt
  have h2 := (e.symm.hasFDerivAt (x := F (e x))).comp x h1
  have hfun : lift F = (⇑e.symm ∘ fun y => F (e y)) := rfl
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext v i
  simp [e]
  rfl

@[powerlib_foundation] theorem fderiv_lift {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} {x : Dynamics.State n}
    (h : HasFDerivAt F (Matrix.toLin' A).toContinuousLinearMap (WithLp.ofLp x)) :
    fderiv ℝ (lift F) x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A :=
  (hasFDerivAt_lift h).fderiv

@[powerlib_foundation] theorem contDiff_lift {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {k : WithTop ℕ∞} (h : ContDiff ℝ k F) : ContDiff ℝ k (lift F) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  exact e.symm.contDiff.comp (h.comp e.contDiff)

/-- Replace a function and its derivative by provably equal ones. -/
@[powerlib_foundation] theorem hasFDerivAt_of_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g g' : E → ℝ} {L L' : E →L[ℝ] ℝ} {y : E} (h : HasFDerivAt g L y)
    (hg : ∀ z, g' z = g z) (hL : L = L') : HasFDerivAt g' L' y := by
  rw [show g' = g from funext hg, ← hL]
  exact h

@[powerlib_foundation] theorem hasFDerivAt_coord (i : Fin n) (y : Fin n → ℝ) :
    HasFDerivAt (fun z : Fin n → ℝ => z i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) y :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt

@[powerlib_foundation] theorem abs_coord_sub_le (x y : Dynamics.State n) (i : Fin n) :
    |y i - x i| ≤ ‖y - x‖ := by
  have := PiLp.norm_apply_le (y - x) i
  simpa [Real.norm_eq_abs] using this

/-! ## Locality of local stability -/

/-- First-exit (bootstrap) argument: a continuous curve that starts inside the open ball of
radius `R`, and that stays in the half-radius ball as long as it has stayed in the full ball,
never leaves the full ball. -/
@[powerlib_foundation] theorem forall_norm_sub_lt_of_bootstrap {E : Type*}
    [NormedAddCommGroup E] {φ : ℝ → E} {x : E} {t₀ t₁ R : ℝ}
    (hc : ContinuousOn φ (Icc t₀ t₁)) (h0 : ‖φ t₀ - x‖ < R)
    (hboot : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ < R) → ‖φ s - x‖ ≤ R / 2) :
    ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ < R := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) h0
  have hcn : ContinuousOn (fun s => ‖φ s - x‖) (Icc t₀ t₁) := (hc.sub continuousOn_const).norm
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, hRt⟩ := hcon
  set S : Set ℝ := Icc t₀ t₁ ∩ (fun s => ‖φ s - x‖) ⁻¹' Ici R with hSdef
  have hS_closed : IsClosed S := hcn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS_ne : S.Nonempty := ⟨t, ht, hRt⟩
  have hS_bdd : BddBelow S := ⟨t₀, fun s hs => hs.1.1⟩
  have hτ : sInf S ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  set τ := sInf S with hτdef
  have hτR : R ≤ ‖φ τ - x‖ := hτ.2
  have hτ0 : t₀ < τ := by
    refine lt_of_le_of_ne hτ.1.1 fun h => ?_
    rw [← h] at hτR
    linarith
  have hbefore : ∀ s ∈ Ico t₀ τ, ‖φ s - x‖ ≤ R / 2 := by
    intro s hs
    apply hboot s ⟨hs.1, hs.2.le.trans hτ.1.2⟩
    intro u hu
    by_contra hu'
    push Not at hu'
    have hmem : u ∈ S := ⟨⟨hu.1, hu.2.trans (hs.2.le.trans hτ.1.2)⟩, hu'⟩
    have : τ ≤ u := csInf_le hS_bdd hmem
    linarith [hu.2, hs.2]
  have hT : IsClosed (Icc t₀ t₁ ∩ (fun s => ‖φ s - x‖) ⁻¹' Iic (R / 2)) :=
    hcn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ico t₀ τ ⊆ Icc t₀ t₁ ∩ (fun s => ‖φ s - x‖) ⁻¹' Iic (R / 2) :=
    fun s hs => ⟨⟨hs.1, hs.2.le.trans hτ.1.2⟩, hbefore s hs⟩
  have hcl := hT.closure_subset_iff.mpr hsub
  rw [closure_Ico hτ0.ne] at hcl
  have hle : ‖φ τ - x‖ ≤ R / 2 := (hcl ⟨hτ0.le, le_rfl⟩).2
  linarith

/-- A solution segment of `f` along which `f` and `g` coincide is a solution segment of `g`. -/
@[powerlib_foundation] theorem isTrajectoryOn_of_eqOn {f g : Dynamics.State n → Dynamics.State n}
    {φ : ℝ → Dynamics.State n} {a b : ℝ} (hφ : IsTrajectoryOn φ f a b)
    (h : ∀ t ∈ Icc a b, f (φ t) = g (φ t)) : IsTrajectoryOn φ g a b := by
  intro t ht
  show HasDerivWithinAt φ (g (φ t)) (Icc a b) t
  rw [← h t ht]
  exact hφ t ht

/-- Local exponential stability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n} {ρ : ℝ} (hρ : 0 < ρ)
    (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) (hg : LocallyExponentiallyStable g x) :
    LocallyExponentiallyStable f x := by
  obtain ⟨r, C, a, hr, hC, ha, hbound⟩ := hg
  have hCpos : 0 < C := by linarith
  refine ⟨min r (ρ / (2 * C)), C, a, lt_min hr (by positivity), hC, ha, ?_⟩
  intro t₀ t₁ φ hφ hφ0
  have hφr : ‖φ t₀ - x‖ < r := hφ0.trans_le (min_le_left _ _)
  have hφC : C * ‖φ t₀ - x‖ ≤ ρ / 2 := by
    have h1 : ‖φ t₀ - x‖ < ρ / (2 * C) := hφ0.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hstay : ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ < ρ := by
    refine forall_norm_sub_lt_of_bootstrap (φ := φ) hφ.continuousOn ?_ ?_
    · have : 1 * ‖φ t₀ - x‖ ≤ C * ‖φ t₀ - x‖ :=
        mul_le_mul_of_nonneg_right hC (norm_nonneg _)
      linarith
    · intro s hs hin
      have hgs : IsTrajectoryOn φ g t₀ s :=
        isTrajectoryOn_of_eqOn (hφ.mono (Icc_subset_Icc le_rfl hs.2))
          (fun u hu => hfg _ (hin u hu))
      have hb := hbound t₀ s φ hgs hφr s ⟨hs.1, le_rfl⟩
      have hexp : Real.exp (-a * (s - t₀)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ s - t₀ := by linarith [hs.1]
        nlinarith
      have : C * Real.exp (-a * (s - t₀)) * ‖φ t₀ - x‖ ≤ C * ‖φ t₀ - x‖ := by
        have h0 : 0 ≤ C * ‖φ t₀ - x‖ := by positivity
        calc C * Real.exp (-a * (s - t₀)) * ‖φ t₀ - x‖
            = Real.exp (-a * (s - t₀)) * (C * ‖φ t₀ - x‖) := by ring
          _ ≤ 1 * (C * ‖φ t₀ - x‖) := mul_le_mul_of_nonneg_right hexp h0
          _ = C * ‖φ t₀ - x‖ := one_mul _
      linarith
  exact hbound t₀ t₁ φ (isTrajectoryOn_of_eqOn hφ fun u hu => hfg _ (hstay u hu)) hφr

/-- Lyapunov stability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem lyapunovStable_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n} {ρ : ℝ} (hρ : 0 < ρ)
    (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) (hg : LyapunovStable g x) :
    LyapunovStable f x := by
  intro ε hε
  have hε' : 0 < min ε ρ := lt_min hε hρ
  obtain ⟨δ, hδ, hδb⟩ := hg (min ε ρ / 2) (by positivity)
  refine ⟨min δ (min ε ρ / 2), lt_min hδ (by positivity), ?_⟩
  intro t₀ t₁ φ hφ hφ0 t ht
  have hstay : ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ < min ε ρ := by
    refine forall_norm_sub_lt_of_bootstrap (φ := φ) hφ.continuousOn ?_ ?_
    · have := hφ0.trans_le (min_le_right _ _)
      linarith
    · intro s hs hin
      have hgs : IsTrajectoryOn φ g t₀ s :=
        isTrajectoryOn_of_eqOn (hφ.mono (Icc_subset_Icc le_rfl hs.2))
          (fun u hu => hfg _ ((hin u hu).trans_le (min_le_right _ _)))
      exact (hδb t₀ s φ hgs (hφ0.trans_le (min_le_left _ _)) s ⟨hs.1, le_rfl⟩).le
  exact (hstay t ht).trans_le (min_le_left _ _)

/-- Instability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem unstable_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n} {ρ : ℝ} (hρ : 0 < ρ)
    (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) (hg : Unstable g x) :
    Unstable f x :=
  fun hf => hg (lyapunovStable_of_eqOn_ball hρ (fun y hy => (hfg y hy).symm) hf)

/-- Linearization through a local `C¹` extension: if `f` agrees near `x_eq` with a globally
`C¹` field `g` whose Jacobian at `x_eq` is Hurwitz, then `f` is locally exponentially stable. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_isHurwitz_jacobian_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x_eq : Dynamics.State n} {ρ : ℝ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hρ : 0 < ρ) (hfg : ∀ y, ‖y - x_eq‖ < ρ → f y = g y)
    (hg : ContDiff ℝ 1 g) (heq : g x_eq = 0)
    (hJac : fderiv ℝ g x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : LinearSystems.IsHurwitz A) : LocallyExponentiallyStable f x_eq :=
  locallyExponentiallyStable_of_eqOn_ball hρ hfg
    (Flow.locallyExponentiallyStable_of_isHurwitz_jacobian A hg heq hJac hA)

/-- Instability through a local `C¹` extension (eigenvalue with positive real part). -/
@[powerlib_foundation] theorem unstable_of_jacobian_eigenvalue_re_pos_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x_eq : Dynamics.State n} {ρ : ℝ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hρ : 0 < ρ) (hfg : ∀ y, ‖y - x_eq‖ < ρ → f y = g y)
    (hg : ContDiff ℝ 1 g) (heq : g x_eq = 0)
    (hJac : fderiv ℝ g x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re) :
    Unstable f x_eq :=
  unstable_of_eqOn_ball hρ hfg
    (Flow.unstable_of_jacobian_eigenvalue_re_pos A hg heq hJac hunstable)

/-! ## A smooth extension of `V ↦ V⁻¹` away from `V = 0` -/

/-- The smooth denominator: equal to `V` for `V ≥ 1/2` and at least `1/4` everywhere. -/
def invDen (V : ℝ) : ℝ := 1 / 4 + (V - 1 / 4) * Real.smoothTransition (4 * V - 1)

/-- A globally smooth function equal to `V⁻¹` for `V ≥ 1/2`. -/
def invExt (V : ℝ) : ℝ := (invDen V)⁻¹

@[powerlib_foundation] theorem invDen_ge (V : ℝ) : 1 / 4 ≤ invDen V := by
  unfold invDen
  rcases le_or_gt V (1 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · have := Real.smoothTransition.nonneg (4 * V - 1)
    have : 0 ≤ (V - 1 / 4) * Real.smoothTransition (4 * V - 1) :=
      mul_nonneg (by linarith) this
    linarith

@[powerlib_foundation] theorem invDen_pos (V : ℝ) : 0 < invDen V :=
  lt_of_lt_of_le (by norm_num) (invDen_ge V)

@[powerlib_foundation] theorem invDen_eq {V : ℝ} (h : 1 / 2 ≤ V) : invDen V = V := by
  unfold invDen
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

@[powerlib_foundation] theorem invExt_eq {V : ℝ} (h : 1 / 2 ≤ V) : invExt V = V⁻¹ := by
  rw [invExt, invDen_eq h]

@[powerlib_foundation] theorem contDiff_invDen {k : ℕ∞} : ContDiff ℝ k invDen := by
  unfold invDen
  have hs : ContDiff ℝ k (fun V : ℝ => Real.smoothTransition (4 * V - 1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  fun_prop

@[powerlib_foundation] theorem contDiff_invExt {k : ℕ∞} : ContDiff ℝ k invExt := by
  unfold invExt
  exact contDiff_invDen.inv fun V => (invDen_pos V).ne'

end powerlib.GFLParametric
