import theorem.Hurwitz
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Nonlinear index-1 DAEs: implicit slow manifold, Schur-complement Jacobian, local stability

System (continuous time, autonomous, inputs fixed and absorbed into `f`, `g`):
```
ẋ = f(x, y),      0 = g(x, y),      x ∈ ℝⁿ (differential), y ∈ ℝᵐ (algebraic),
```
`f : ℝⁿ × ℝᵐ → ℝⁿ`, `g : ℝⁿ × ℝᵐ → ℝᵐ` globally `C¹` (`Dynamics.State k` =
`EuclideanSpace ℝ (Fin k)`), with an equilibrium `u = (x₀, y₀)`: `f u = 0`, `g u = 0`, and the
index-1 condition: `∂g/∂y (u)` is invertible. State order: `x` then `y`. No delay, PWM,
switching or limiter is part of the abstract model; any controller must be inside `f`, `g`.

Foundation results (categories B/C).
* `implicitMap`: the local solution `y = h(x)` of `g(x, y) = 0` through `u` (Mathlib
  `ContDiffAt.implicitFunction`), with `h x₀ = y₀`, `C¹` at `x₀`, local uniqueness
  (`g v = 0 ↔ h v.1 = v.2` near `u`) and derivative `Dh(x₀) = -(∂g/∂y)⁻¹ ∂g/∂x` — thin
  wrappers of the upstream theorems.
* "Eliminate first, then linearize = Schur complement": the reduced field
  `F(x) = f(x, h(x))` has derivative `∂f/∂x - ∂f/∂y (∂g/∂y)⁻¹ ∂g/∂x` at `x₀`
  (`hasFDerivAt_reducedField`); `schurMatrix` is its matrix in the standard basis.
* `locallyExponentiallyStable_of_eqOn_ball`: local exponential stability depends only on the
  field near the equilibrium (bootstrap with `exp_bound_of_local`).

Domain results (category A; general semi-explicit index-1 DAEs such as network-constrained
power-system models, as in the source notes).
* `reducedODE_locallyExponentiallyStable`: if `schurMatrix` is Hurwitz, the reduced ODE
  `ẋ = f(x, h(x))` is locally exponentially stable at `x₀`. The reduced field is only
  meaningful near `x₀`; the proof applies the linearization theorem to a `C¹` field equal to
  `F` on a ball (smooth bump cutoff) and transfers the estimate back.
* `dae_locallyExponentiallyStable`: the same estimate holds for the DAE itself: there is a
  neighbourhood `V` of `y₀` (the selected algebraic branch) such that every DAE solution
  segment with `y(t) ∈ V` and `x(t₀)` close to `x₀` satisfies
  `‖x(t) - x₀‖ ≤ C e^{-a (t - t₀)} ‖x(t₀) - x₀‖`, and `y(t) = h(x(t))`. Solutions on another
  branch of `g = 0` are excluded by `V`.

Conclusions are equilibrium-level (local, small-signal); nothing is claimed about large
disturbances or about index ≥ 2 systems.

Source: work-sync theory/T-small-signal-stability.md §1.1–§1.4 (nonlinear DAE, index-1
reduction, Schur complement); theory/T-dae-systems.md §1.3–§1.4, §1.9;
theory/T-slow-manifold.md §1.1, §1.3 (implicit construction of `h` and `∂h/∂x`);
theory/T-singular-perturbation.md §1.3.
-/

noncomputable section
namespace powerlib.DAE
open Set Filter Topology Metric
open powerlib.Dynamics (State)

variable {n m : ℕ}

/-! ## Local exponential stability is a local property of the field -/

/-- Bootstrap: an exponential estimate for `G` transfers to every curve that solves
`ẋ = G x` while it stays in the ball of radius `R`. -/
@[powerlib_foundation] theorem exp_bound_of_local {G : State n → State n} {x₀ : State n}
    {r C a R : ℝ} (hC : 1 ≤ C) (ha : 0 < a)
    (hG : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), Dynamics.IsTrajectoryOn φ G t₀ t₁ →
      ‖φ t₀ - x₀‖ < r → ∀ t ∈ Icc t₀ t₁,
        ‖φ t - x₀‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x₀‖)
    {φ : ℝ → State n} {t₀ t₁ : ℝ} (hcont : ContinuousOn φ (Icc t₀ t₁))
    (hder : ∀ t ∈ Icc t₀ t₁, ‖φ t - x₀‖ < R → HasDerivWithinAt φ (G (φ t)) (Icc t₀ t₁) t)
    (h0 : ‖φ t₀ - x₀‖ < min r (R / C)) :
    ∀ t ∈ Icc t₀ t₁, ‖φ t - x₀‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x₀‖ := by
  have hCpos : 0 < C := by linarith
  have h0r : ‖φ t₀ - x₀‖ < r := lt_of_lt_of_le h0 (min_le_left _ _)
  have hK : C * ‖φ t₀ - x₀‖ < R := by
    have := lt_of_lt_of_le h0 (min_le_right _ _)
    rw [lt_div_iff₀ hCpos] at this
    linarith
  have hn0 := norm_nonneg (φ t₀ - x₀)
  have hsub : ∀ s, s ≤ t₁ → (∀ τ ∈ Icc t₀ s, ‖φ τ - x₀‖ < R) →
      Dynamics.IsTrajectoryOn φ G t₀ s := by
    intro s hs hin τ hτ
    have hτ' : τ ∈ Icc t₀ t₁ := ⟨hτ.1, hτ.2.trans hs⟩
    exact (hder τ hτ' (hin τ hτ)).mono (Icc_subset_Icc le_rfl hs)
  have hcontN : ContinuousOn (fun s => ‖φ s - x₀‖) (Icc t₀ t₁) :=
    (hcont.sub continuousOn_const).norm
  have hstay : ∀ t ∈ Icc t₀ t₁, ‖φ t - x₀‖ < R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht, htR⟩ := hcon
    let S := Icc t₀ t₁ ∩ (fun s => ‖φ s - x₀‖) ⁻¹' Ici R
    have hSc : IsClosed S := hcontN.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSne : S.Nonempty := ⟨t, ht, htR⟩
    have hSbdd : BddBelow S := ⟨t₀, fun y hy => hy.1.1⟩
    have hsS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
    have hsR : R ≤ ‖φ (sInf S) - x₀‖ := hsS.2
    have hs0 : t₀ < sInf S := by
      rcases eq_or_lt_of_le hsS.1.1 with h | h
      · exfalso
        rw [← h] at hsR
        nlinarith
      · exact h
    have hbelow : ∀ τ ∈ Ico t₀ (sInf S), ‖φ τ - x₀‖ < R := by
      intro τ hτ
      by_contra hτR
      push Not at hτR
      have hmem : τ ∈ S := ⟨⟨hτ.1, hτ.2.le.trans hsS.1.2⟩, hτR⟩
      have := csInf_le hSbdd hmem
      linarith [hτ.2]
    have hbound : ∀ τ ∈ Ico t₀ (sInf S), ‖φ τ - x₀‖ ≤ C * ‖φ t₀ - x₀‖ := by
      intro τ hτ
      have htraj := hsub τ (hτ.2.le.trans hsS.1.2)
        (fun σ hσ => hbelow σ ⟨hσ.1, lt_of_le_of_lt hσ.2 hτ.2⟩)
      have hb := hG t₀ τ φ htraj h0r τ ⟨hτ.1, le_rfl⟩
      have hexp : Real.exp (-a * (τ - t₀)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hτ.1])
      calc ‖φ τ - x₀‖ ≤ C * Real.exp (-a * (τ - t₀)) * ‖φ t₀ - x₀‖ := hb
        _ ≤ C * 1 * ‖φ t₀ - x₀‖ := by gcongr
        _ = C * ‖φ t₀ - x₀‖ := by ring
    let T := Icc t₀ t₁ ∩ (fun s => ‖φ s - x₀‖) ⁻¹' Iic (C * ‖φ t₀ - x₀‖)
    have hTc : IsClosed T := hcontN.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hsub2 : Ico t₀ (sInf S) ⊆ T := fun τ hτ =>
      ⟨⟨hτ.1, hτ.2.le.trans hsS.1.2⟩, hbound τ hτ⟩
    have hsT : sInf S ∈ T := by
      have := closure_minimal hsub2 hTc
      rw [closure_Ico hs0.ne] at this
      exact this ⟨hs0.le, le_rfl⟩
    have h2 : ‖φ (sInf S) - x₀‖ ≤ C * ‖φ t₀ - x₀‖ := hsT.2
    linarith
  exact hG t₀ t₁ φ (hsub t₁ le_rfl hstay) h0r

/-- Two fields that agree on a ball around `x₀` have the same local exponential stability. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_eqOn_ball {F G : State n → State n}
    {x₀ : State n} {R : ℝ} (hR : 0 < R) (hFG : ∀ x, ‖x - x₀‖ < R → F x = G x)
    (hG : Dynamics.LocallyExponentiallyStable G x₀) :
    Dynamics.LocallyExponentiallyStable F x₀ := by
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ := hG
  refine ⟨min r (R / C), C, a, lt_min hr (div_pos hR (by linarith)), hC, ha, ?_⟩
  intro t₀ t₁ φ hφ h0 t ht
  exact exp_bound_of_local hC ha hb hφ.continuousOn
    (fun τ hτ hτR => by rw [← hFG _ hτR]; exact hφ τ hτ) h0 t ht

/-! ## The implicit (slow-manifold) map and the Schur-complement Jacobian -/

variable (f : State n × State m → State n) (g : State n × State m → State m)
  (u : State n × State m)

/-- `∂g/∂y (u)`. -/
def partialY : State m →L[ℝ] State m := fderiv ℝ g u ∘L .inr ℝ (State n) (State m)

/-- `∂g/∂x (u)`. -/
def partialX : State n →L[ℝ] State m := fderiv ℝ g u ∘L .inl ℝ (State n) (State m)

/-- The implicit solution `y = h(x)` of `g(x, y) = g(u)` near `u`. -/
def implicitMap (hg : ContDiff ℝ 1 g) (hinv : (partialY g u).IsInvertible) : State n → State m :=
  (hg.contDiffAt (x := u)).implicitFunction one_ne_zero hinv

/-- Reduced (eliminated) field `F(x) = f(x, h(x))`. -/
def reducedField (hg : ContDiff ℝ 1 g) (hinv : (partialY g u).IsInvertible) :
    State n → State n :=
  fun x => f (x, implicitMap g u hg hinv x)

/-- Schur complement `∂f/∂x - ∂f/∂y (∂g/∂y)⁻¹ ∂g/∂x` as a continuous linear map. -/
def schurCLM : State n →L[ℝ] State n :=
  fderiv ℝ f u ∘L .inl ℝ (State n) (State m) -
    (fderiv ℝ f u ∘L .inr ℝ (State n) (State m)) ∘L (partialY g u).inverse ∘L partialX g u

/-- Matrix of the Schur complement in the standard basis. -/
def schurMatrix : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (schurCLM f g u)

variable {f g u}

@[powerlib_foundation] theorem implicitMap_self (hg : ContDiff ℝ 1 g)
    (hinv : (partialY g u).IsInvertible) : implicitMap g u hg hinv u.1 = u.2 :=
  ContDiffAt.implicitFunction_apply_self _ _ _

/-- `g(x, h(x)) = 0` near `x₀` (wrapper of `ContDiffAt.eventually_apply_implicitFunction`). -/
@[powerlib_foundation] theorem implicitMap_spec (hg : ContDiff ℝ 1 g)
    (hinv : (partialY g u).IsInvertible) (hu : g u = 0) :
    ∀ᶠ x in 𝓝 u.1, g (x, implicitMap g u hg hinv x) = 0 := by
  have := ContDiffAt.eventually_apply_implicitFunction (hg.contDiffAt (x := u)) one_ne_zero hinv
  rwa [hu] at this

/-- Local uniqueness of the algebraic branch (wrapper of
`ContDiffAt.eventually_apply_eq_iff_implicitFunction`). -/
@[powerlib_foundation] theorem implicitMap_unique (hg : ContDiff ℝ 1 g)
    (hinv : (partialY g u).IsInvertible) (hu : g u = 0) :
    ∀ᶠ v in 𝓝 u, g v = 0 ↔ implicitMap g u hg hinv v.1 = v.2 := by
  have := ContDiffAt.eventually_apply_eq_iff_implicitFunction (hg.contDiffAt (x := u))
    one_ne_zero hinv
  rwa [hu] at this

/-- `Dh(x₀) = -(∂g/∂y)⁻¹ ∂g/∂x` (wrapper of `ContDiffAt.hasStrictFDerivAt_implicitFunction`). -/
@[powerlib_foundation] theorem hasStrictFDerivAt_implicitMap (hg : ContDiff ℝ 1 g)
    (hinv : (partialY g u).IsInvertible) :
    HasStrictFDerivAt (implicitMap g u hg hinv) (-(partialY g u).inverse ∘L partialX g u) u.1 :=
  ContDiffAt.hasStrictFDerivAt_implicitFunction _ _ _

@[powerlib_foundation] theorem contDiffAt_implicitMap (hg : ContDiff ℝ 1 g)
    (hinv : (partialY g u).IsInvertible) : ContDiffAt ℝ 1 (implicitMap g u hg hinv) u.1 :=
  ContDiffAt.contDiffAt_implicitFunction _ _ _

/-- Eliminating `y` and then linearizing gives the Schur complement. -/
@[powerlib_foundation] theorem hasFDerivAt_reducedField (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hinv : (partialY g u).IsInvertible) :
    HasFDerivAt (reducedField f g u hg hinv) (schurCLM f g u) u.1 := by
  have hh := (hasStrictFDerivAt_implicitMap hg hinv).hasFDerivAt
  have hpair := (hasFDerivAt_id u.1).prodMk hh
  have hpt : (u.1, implicitMap g u hg hinv u.1) = u := by rw [implicitMap_self]
  have hfd : HasFDerivAt f (fderiv ℝ f u) (u.1, implicitMap g u hg hinv u.1) := by
    rw [hpt]; exact (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hcomp := hfd.comp u.1 hpair
  have hS : schurCLM f g u = fderiv ℝ f u ∘L
      ((ContinuousLinearMap.id ℝ (State n)).prod (-(partialY g u).inverse ∘L partialX g u)) := by
    ext1 v
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_inl_add_comp_inr]
    simp [schurCLM, sub_eq_add_neg]
    rw [← map_neg, Prod.neg_mk, neg_zero]
  rw [hS]
  exact hcomp

@[powerlib_foundation] theorem contDiffAt_reducedField (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hinv : (partialY g u).IsInvertible) :
    ContDiffAt ℝ 1 (reducedField f g u hg hinv) u.1 :=
  hf.contDiffAt.comp u.1 (contDiffAt_id.prodMk (contDiffAt_implicitMap hg hinv))

@[powerlib_foundation] theorem reducedField_self (hg : ContDiff ℝ 1 g)
    (hinv : (partialY g u).IsInvertible) (hfu : f u = 0) :
    reducedField f g u hg hinv u.1 = 0 := by
  simp only [reducedField, implicitMap_self]
  exact hfu

/-! ## Local exponential stability -/

/-- A globally `C¹` field equal to the reduced field on a ball around `x₀`. -/
@[powerlib_foundation] theorem exists_contDiff_extension (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hinv : (partialY g u).IsInvertible) :
    ∃ R > 0, ∃ G : State n → State n, ContDiff ℝ 1 G ∧
      ∀ x, ‖x - u.1‖ < R → G x = reducedField f g u hg hinv x := by
  set F := reducedField f g u hg hinv
  have hev : ∀ᶠ y in 𝓝 u.1, ContDiffAt ℝ 1 F y :=
    (contDiffAt_reducedField hf hg hinv).eventually (by norm_num)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let b : ContDiffBump u.1 := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  refine ⟨ρ / 4, by positivity, fun x => b x • F x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : dist x u.1 < ρ
    · exact (b.contDiff.contDiffAt).smul (hball hx)
    · have hnot : x ∉ tsupport b := by
        rw [b.tsupport_eq, mem_closedBall]
        intro h
        apply hx
        have : b.rOut = ρ / 2 := rfl
        linarith
      have hz : (fun x => b x • F x) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro x hx
    have : b x = 1 := b.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_eq_norm]
      exact hx.le)
    simp [this]

/-- **Reduced ODE stability.** For an index-1 equilibrium with Hurwitz Schur complement, the
eliminated ODE `ẋ = f(x, h(x))` is locally exponentially stable at `x₀`. -/
@[powerlib_domain] theorem reducedODE_locallyExponentiallyStable (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hinv : (partialY g u).IsInvertible) (hfu : f u = 0)
    (hH : LinearSystems.IsHurwitz (schurMatrix f g u)) :
    Dynamics.LocallyExponentiallyStable (reducedField f g u hg hinv) u.1 := by
  obtain ⟨R, hR, G, hGc, hGF⟩ := exists_contDiff_extension hf hg hinv
  have hGF' : G =ᶠ[𝓝 u.1] reducedField f g u hg hinv := by
    filter_upwards [Metric.ball_mem_nhds u.1 hR] with x hx
    exact hGF x (by rwa [mem_ball, dist_eq_norm] at hx)
  have hGeq : G u.1 = 0 := by
    rw [hGF u.1 (by simpa using hR), reducedField_self hg hinv hfu]
  have hJac : fderiv ℝ G u.1 =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (schurMatrix f g u) := by
    rw [hGF'.fderiv_eq, (hasFDerivAt_reducedField hf hg hinv).fderiv, schurMatrix,
      StarAlgEquiv.apply_symm_apply]
  have hG := Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian _ hGc hGeq hJac hH
  exact locallyExponentiallyStable_of_eqOn_ball hR (fun x hx => (hGF x hx).symm) hG

/-- Solution segment of the semi-explicit DAE `ẋ = f(x, y)`, `0 = g(x, y)` on `[t₀, t₁]`. -/
def IsDAESolutionOn (f : State n × State m → State n) (g : State n × State m → State m)
    (x : ℝ → State n) (y : ℝ → State m) (t₀ t₁ : ℝ) : Prop :=
  ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt x (f (x t, y t)) (Icc t₀ t₁) t ∧ g (x t, y t) = 0

/-- **DAE stability.** Under the hypotheses of `reducedODE_locallyExponentiallyStable`, every
DAE solution segment on the branch selected by a neighbourhood `V` of `y₀` and starting close
to `x₀` decays exponentially, and its algebraic part is `y = h(x)`. -/
@[powerlib_domain] theorem dae_locallyExponentiallyStable (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hinv : (partialY g u).IsInvertible) (hfu : f u = 0) (hgu : g u = 0)
    (hH : LinearSystems.IsHurwitz (schurMatrix f g u)) :
    ∃ V ∈ 𝓝 u.2, ∃ r C a : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < a ∧
      ∀ (t₀ t₁ : ℝ) (x : ℝ → State n) (y : ℝ → State m), IsDAESolutionOn f g x y t₀ t₁ →
        (∀ t ∈ Icc t₀ t₁, y t ∈ V) → ‖x t₀ - u.1‖ < r → ∀ t ∈ Icc t₀ t₁,
          ‖x t - u.1‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖x t₀ - u.1‖ ∧
            y t = implicitMap g u hg hinv (x t) := by
  obtain ⟨R₀, hR₀, G, hGc, hGF⟩ := exists_contDiff_extension hf hg hinv
  have hGF' : G =ᶠ[𝓝 u.1] reducedField f g u hg hinv := by
    filter_upwards [Metric.ball_mem_nhds u.1 hR₀] with x hx
    exact hGF x (by rwa [mem_ball, dist_eq_norm] at hx)
  have hGeq : G u.1 = 0 := by
    rw [hGF u.1 (by simpa using hR₀), reducedField_self hg hinv hfu]
  have hJac : fderiv ℝ G u.1 =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (schurMatrix f g u) := by
    rw [hGF'.fderiv_eq, (hasFDerivAt_reducedField hf hg hinv).fderiv, schurMatrix,
      StarAlgEquiv.apply_symm_apply]
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ :=
    Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian _ hGc hGeq hJac hH
  have huniq : ∀ᶠ v in 𝓝 u.1 ×ˢ 𝓝 u.2, g v = 0 ↔ implicitMap g u hg hinv v.1 = v.2 := by
    rw [← nhds_prod_eq]
    exact implicitMap_unique hg hinv hgu
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.mp huniq
  obtain ⟨R₁, hR₁, hR₁pa⟩ := Metric.eventually_nhds_iff.mp hpa
  set R := min R₀ R₁ with hRdef
  have hR : 0 < R := lt_min hR₀ hR₁
  have hCpos : 0 < C := by linarith
  refine ⟨{y | pb y}, hpb, min r (R / C), C, a, lt_min hr (div_pos hR hCpos), hC, ha, ?_⟩
  intro t₀ t₁ x y hsol hyV h0
  have hcont : ContinuousOn x (Icc t₀ t₁) := fun t ht => (hsol t ht).1.continuousWithinAt
  have hbranch : ∀ t ∈ Icc t₀ t₁, ‖x t - u.1‖ < R → y t = implicitMap g u hg hinv (x t) := by
    intro t ht hxt
    have hpa' : pa (x t) := hR₁pa (by
      rw [dist_eq_norm]; exact lt_of_lt_of_le hxt (min_le_right _ _))
    exact ((hall hpa' (hyV t ht)).mp (hsol t ht).2).symm
  have hder : ∀ t ∈ Icc t₀ t₁, ‖x t - u.1‖ < R →
      HasDerivWithinAt x (G (x t)) (Icc t₀ t₁) t := by
    intro t ht hxt
    rw [hGF (x t) (lt_of_lt_of_le hxt (min_le_left _ _))]
    have := (hsol t ht).1
    rwa [hbranch t ht hxt] at this
  have hbound := exp_bound_of_local hC ha hb hcont hder h0
  intro t ht
  refine ⟨hbound t ht, hbranch t ht ?_⟩
  have hK : C * ‖x t₀ - u.1‖ < R := by
    have := lt_of_lt_of_le h0 (min_le_right _ _)
    rw [lt_div_iff₀ hCpos] at this
    linarith
  have hexp : Real.exp (-a * (t - t₀)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  have hn := norm_nonneg (x t₀ - u.1)
  calc ‖x t - u.1‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖x t₀ - u.1‖ := hbound t ht
    _ ≤ C * 1 * ‖x t₀ - u.1‖ := by gcongr
    _ < R := by linarith

end powerlib.DAE
