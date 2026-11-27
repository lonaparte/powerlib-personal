import theorem.Periodic.FlipOrbit
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-! # The Poincaré section of a periodic orbit of an autonomous system

For `ẋ = f(x)` and a nonconstant `T`-periodic orbit `x_*` with `p = x_*(0)` and velocity
`v = f(p) ≠ 0`, the hyperplane `Σ = {ξ : v ⬝ (ξ − p) = 0}` through `p` orthogonal to the velocity
is transverse to the orbit. Solutions starting near `p` cross `Σ` again near the time `T`: the
**return time** `τ(ξ)` solves `g(ξ, τ(ξ)) = 0` for `g(ξ, t) = v ⬝ (x(t; ξ) − p)`, and near
`(p, T)` the zero set of `g` is exactly the graph of `τ`. This is the implicit function theorem
(Mathlib `HasStrictFDerivAt.implicitFunctionOfProdDomain`): the flow is strictly differentiable
jointly in the initial state and the time, with derivative `(e, s) ↦ Φ(t₀, 0) e + s f(x(t₀))`
(`hasStrictFDerivAt_flow_prod`, from the first-variation estimate of
`theorem/Periodic/FlowDerivative.lean` and `∂ₜx = f(x)`), and `∂ₜg(p, T) = v ⬝ v ≠ 0`. The
**Poincaré map** `Π(ξ) = x(τ(ξ); ξ)` takes values in `Σ`, fixes `p`, and has the strict
derivative `DΠ(p) e = M e − ((v ⬝ M e)/(v ⬝ v)) v` (`sectionMatrix`), the monodromy `M` followed by
the projection along the orbit onto `v^⊥`, since `Dτ(p) e = −(v ⬝ M e)/(v ⬝ v)`.

`DΠ(p) = M − v uᵀ` with `u = Mᵀ v/(v ⬝ v)` and `u ⬝ v = 1`, a **deflation** of `M`
(`M v = v`, `OrbitMultiplier.monodromy_mulVec_velocity`). For every deflation `M − v wᵀ`,
`w ⬝ v = 1`, Brauer's identity `χ_{M − v wᵀ}(X) (X − 1) = X χ_M(X)` holds (`charpoly_deflate`):
the trivial multiplier `1` of `M` on the velocity is replaced by `0`, and the other eigenvalues,
the **nontrivial multipliers**, are kept with their multiplicities. So the eigenvalues of `DΠ(p)`
on `Σ` are the nontrivial multipliers, its eigenvalue `0` belongs to the direction `v` along the
orbit, and `M − v wᵀ` is Schur stable (for one, equivalently every, such `w`) exactly when `1` is a
simple root of `χ_M` and every other multiplier lies strictly inside the unit circle
(`schurStable_deflate_iff`, `schurStable_sectionMatrix_iff`) — the hypothesis of the
Andronov–Witt theorem (`theorem/Periodic/AndronovWitt.lean`).

Scope.
* `ẋ = f(x)` on `ℝ^{Fin n}` with the sup norm, continuous time; `f` of class `C¹` and globally
  `K`-Lipschitz (the flow of `theorem/Periodic/FlowDerivative.lean`, `FlowDerivative.flow`, on
  `[0, ∞)`; a field that is only locally Lipschitz would first be cut off near the orbit as in
  `theorem/Periodic/LocalField.lean`, which is not done here). `x_*` is a global solution,
  `T`-periodic with `T > 0` and `f(x_*(0)) ≠ 0`; `T` need not be the minimal period (for
  `T = m T₀` the map `Π` is the `m`-th return map).
* The section is the hyperplane through `x_*(0)` orthogonal to the velocity. The return time is
  the implicit function of Mathlib, a total function that is meaningful on the box
  `‖ξ − p‖ < r`, `|t − T| < s` (`s ≤ T/2`) where the zero set of `g` is its graph; `Π` is read as
  a map of the whole space whose values near `p` lie in `Σ`. It need not be the first return
  (crossings of `Σ` far from the time `T` are not excluded).
* The spectral statements are about real matrices and their complex spectra (multipliers);
  multiplicities are those of the characteristic polynomial.
* Generic mathematics; no model family.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §1.5 (the Poincaré map of a
cycle, its fixed point and the multipliers: the monodromy has the trivial multiplier `1`, the other
`n − 1` multipliers are the eigenvalues of the Jacobian of the Poincaré map); Hartman, *Ordinary
Differential Equations*, Ch. V (differentiability of the flow); Hirsch, Smale and Devaney,
*Differential Equations, Dynamical Systems, and an Introduction to Chaos*, Ch. 10 (local sections
and the return time by the implicit function theorem); A. Brauer, "Limits for the characteristic
roots of a matrix IV", Duke Math. J. 19 (1952) (the deflation `M − v wᵀ`); the open item of
`theorem/Periodic/FoldOrbit.lean` (Scope: "orbital asymptotic stability of autonomous orbits is not
treated", "Orbital asymptotic stability, through a Poincaré section transverse to the orbit, is not
treated here").

Results.
* `hasStrictFDerivAt_flow_prod` — the flow `(ξ, t) ↦ x(t; ξ)` of an autonomous `C¹` field is
  strictly differentiable at `(x₀(0), t₀)`, `t₀ > 0`, with derivative
  `(e, s) ↦ Φ(t₀, 0) e + s f(x₀(t₀))`.
* `exists_returnTime` — the return time `τ`, `τ(p) = T`, `Dτ(p) = −(v ⬝ M ·)/(v ⬝ v)`, the crossing
  `v ⬝ (x(τ(ξ); ξ) − p) = 0` near `p` and its uniqueness for times near `T`.
* Deflation: `charpoly_deflate` (Brauer: `χ_{M − v wᵀ}(X) (X − 1) = X χ_M(X)`),
  `mem_spectrum_deflate_iff` (a multiplier `μ ∉ {0, 1}` of `M` is an eigenvalue of the deflation
  and conversely), `one_mem_spectrum_deflate_iff` (`1` is an eigenvalue of the deflation exactly
  when it is a multiple root of `χ_M`), `schurStable_deflate_iff` (Schur stability of the
  deflation ⇔ `1` simple, all other multipliers inside the unit circle).
* The Poincaré map: `sectionMatrix`, `sectionMatrix_mulVec`, `sectionVec_dotProduct`,
  `sectionMatrix_maps` (`DΠ` maps into `v^⊥` and kills `v`), `schurStable_sectionMatrix_iff`;
  `poincareMap`, `poincareMap_eq` (it reads every solution at the return time);
  **the theorem** `exists_poincareMap` (return time, section, fixed point, strict derivative
  `sectionMatrix M v`, and `χ_{DΠ(p)}(X) (X − 1) = X χ_M(X)`).

Corrections.
None: an extension (the Poincaré section of an autonomous periodic orbit, which the period-map
modules do not provide).

Family and connection conclusions.
None: static evidence on autonomous ODEs (the Poincaré map of a periodic orbit).
-/

noncomputable section
namespace powerlib.Periodic.PoincareSection

open Set Matrix Function Filter Topology Asymptotics
open scoped Matrix.Norms.Operator
open FlowDerivative FlipOrbit

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

/-! ## The flow as a function of the initial state and the time -/

/-- **The flow is strictly differentiable in the initial state and the time jointly.** For
`ẋ = f(x)` with `f` of class `C¹` and globally `K`-Lipschitz, and a global solution `x₀`, the flow
`(ξ, t) ↦ x(t; 0, ξ)` has at `(x₀(0), t₀)`, `t₀ > 0`, the strict derivative
`(e, s) ↦ Φ(t₀, 0) e + s f(x₀(t₀))`, `Φ` the transition matrix of the variational equation along
`x₀`. -/
@[tmio T, powerlib_foundation] theorem hasStrictFDerivAt_flow_prod (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {x₀ : ℝ → Fin n → ℝ} (hx₀ : ∀ t, HasDerivAt x₀ (f (x₀ t)) t)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasStrictFDerivAt
      (fun q : (Fin n → ℝ) × ℝ =>
        flow (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) 0 q.1 q.2)
      ((Matrix.toLin' (transition (variationalMatrix f x₀) t₀ 0)).toContinuousLinearMap.comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ) +
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight (f (x₀ t₀))) (x₀ 0, t₀) := by
  set hGc : Continuous (uncurry fun _ : ℝ => f) := hfK.continuous.comp continuous_snd
  set Fl := flow (G := fun _ => f) hGc (fun _ => hfK) 0 with hFl
  set A := variationalMatrix f x₀ with hA
  set p := x₀ 0 with hp
  set v := f (x₀ t₀) with hv
  have hx₀c : Continuous x₀ := continuous_iff_continuousAt.2 fun t => (hx₀ t).continuousAt
  have hAc : Continuous A := variationalMatrix_continuous hf hx₀c
  have hGd : ∀ (t : ℝ) x, DifferentiableAt ℝ ((fun _ : ℝ => f) t) x :=
    fun _ x => (hf.differentiable one_ne_zero) x
  have hD : Continuous fun q : ℝ × (Fin n → ℝ) => fderiv ℝ ((fun _ : ℝ => f) q.1) q.2 :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_snd
  have hsol : ∀ ξ, IsIntegralCurveOn (Fl ξ) (fun _ => f) (Ici 0) :=
    fun ξ => flow_solution hGc (fun _ => hfK) 0 ξ
  have hstart : ∀ ξ, Fl ξ 0 = ξ := fun ξ => flow_start hGc (fun _ => hfK) 0 ξ
  have hx₀I : ∀ s t : ℝ, IsIntegralCurveOn x₀ (fun _ => f) (Icc s t) :=
    fun _ _ r _ => (hx₀ r).hasDerivWithinAt
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set T₁ := t₀ + 1 with hT₁
  have hT₁0 : 0 ≤ T₁ := by linarith
  set E := Real.exp (K * T₁) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg K.2 hT₁0)
  -- the first-variation term
  set C₁ := T₁ * Real.exp (2 * (K * T₁)) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set η := c / (3 * (C₁ + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨ρ, hρ, hρη⟩ :=
    exists_radius_fderiv_le (G := fun _ => f) hD (s := 0) (t := T₁) hx₀c.continuousOn hη
  -- the transition matrix is continuous in time
  have hΦc : ContinuousAt (fun t => transition A t 0) t₀ :=
    (Dynamics.stm_hasDerivAt hAc t₀ 0).continuousAt
  obtain ⟨δΦ, hδΦ, hΦδ⟩ := Metric.continuousAt_iff.1 hΦc (c / 3) (by positivity)
  -- the velocity term
  set κ := c / (6 * (K + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨δx, hδx, hxδ⟩ := Metric.continuousAt_iff.1 hx₀c.continuousAt κ hκ0
  -- the radii
  set b := min (min (t₀ / 2) 1) (min δΦ (δx / 2)) with hb
  have hb0 : 0 < b := by positivity
  set a := min (ρ / E) (κ / E) with ha
  have ha0 : 0 < a := by positivity
  set r := min a b with hr
  have hr0 : 0 < r := lt_min ha0 hb0
  filter_upwards [Metric.ball_mem_nhds ((p, t₀), (p, t₀)) hr0] with q hq
  obtain ⟨⟨ξ₁, t₁⟩, ⟨ξ₂, t₂⟩⟩ := q
  rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff,
    max_lt_iff] at hq
  obtain ⟨⟨hξ₁, ht₁⟩, ⟨hξ₂, ht₂⟩⟩ := hq
  rw [dist_eq_norm] at hξ₁ hξ₂
  rw [Real.dist_eq] at ht₁ ht₂
  have hrb : r ≤ b := min_le_right _ _
  have hra : r ≤ a := min_le_left _ _
  have hbt : b ≤ t₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hb1 : b ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hbΦ : b ≤ δΦ := (min_le_right _ _).trans (min_le_left _ _)
  have hbx : b ≤ δx / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have haρ : a ≤ ρ / E := min_le_left _ _
  have haκ : a ≤ κ / E := min_le_right _ _
  have ht₁0 : 0 ≤ t₁ := by have := abs_lt.1 ht₁; linarith
  have ht₁T : t₁ ≤ T₁ := by have := abs_lt.1 ht₁; linarith
  have hexp₁ : Real.exp (K * t₁) ≤ E := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht₁T K.2)
  simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLin'_apply]
  -- the three terms
  have hD1 : ‖Fl ξ₁ t₁ - Fl ξ₂ t₁ - transition A t₁ 0 *ᵥ (ξ₁ - ξ₂)‖ ≤ c / 3 * ‖ξ₁ - ξ₂‖ := by
    have hρi : ∀ ξ : Fin n → ℝ, ‖ξ - p‖ < r → ‖Fl ξ 0 - x₀ 0‖ * Real.exp (K * (t₁ - 0)) ≤ ρ := by
      intro ξ hξ
      rw [hstart, sub_zero]
      have h1 : ‖ξ - p‖ * E ≤ ρ := by
        have := (hξ.trans_le (hra.trans haρ)).le
        rwa [le_div_iff₀ (by positivity)] at this
      calc ‖ξ - x₀ 0‖ * Real.exp (K * t₁) ≤ ‖ξ - p‖ * E :=
            mul_le_mul_of_nonneg_left hexp₁ (norm_nonneg _)
        _ ≤ ρ := h1
    have h := norm_sub_sub_transition_le (G := fun _ => f) hGd (fun _ => hfK) hAc ht₁0
      (x₀ := x₀) (x₁ := Fl ξ₁) (x₂ := Fl ξ₂)
      (fun r _ v => variationalMatrix_mulVec r v) (hx₀I 0 t₁)
      ((hsol ξ₁).mono Icc_subset_Ici_self) ((hsol ξ₂).mono Icc_subset_Ici_self)
      (fun r hr ζ hζ => hρη r ⟨hr.1, hr.2.trans ht₁T⟩ ζ hζ) (hρi ξ₁ hξ₁) (hρi ξ₂ hξ₂)
    rw [hstart, hstart, sub_zero] at h
    refine h.trans ?_
    have hC : t₁ * Real.exp (2 * (K * t₁)) ≤ C₁ := by
      rw [hC₁]
      gcongr
    have hηC : η * C₁ ≤ c / 3 := by
      rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    calc η * t₁ * Real.exp (2 * (K * t₁)) * ‖ξ₁ - ξ₂‖
        = η * (t₁ * Real.exp (2 * (K * t₁))) * ‖ξ₁ - ξ₂‖ := by ring
      _ ≤ η * C₁ * ‖ξ₁ - ξ₂‖ := by gcongr
      _ ≤ c / 3 * ‖ξ₁ - ξ₂‖ := by gcongr
  have hD2 : ‖(transition A t₁ 0 - transition A t₀ 0) *ᵥ (ξ₁ - ξ₂)‖ ≤ c / 3 * ‖ξ₁ - ξ₂‖ := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    gcongr
    have := hΦδ (show dist t₁ t₀ < δΦ by rw [Real.dist_eq]; linarith)
    rw [dist_eq_norm] at this
    exact this.le
  have hD3 : ‖Fl ξ₂ t₁ - Fl ξ₂ t₂ - (t₁ - t₂) • v‖ ≤ c / 3 * |t₁ - t₂| := by
    set S := Icc (t₀ - b) (t₀ + b) with hS
    have hSpos : ∀ s ∈ S, 0 ≤ s := fun s hs => by
      have := hs.1; linarith
    have hderiv : ∀ s ∈ S, HasDerivWithinAt (fun s => Fl ξ₂ s - s • v) (f (Fl ξ₂ s) - v) S s := by
      intro s hs
      have h1 : HasDerivWithinAt (Fl ξ₂) (f (Fl ξ₂ s)) S s :=
        (hsol ξ₂ s (hSpos s hs)).mono fun u hu => hSpos u hu
      have h2 : HasDerivWithinAt (fun s : ℝ => s • v) ((1 : ℝ) • v) S s :=
        ((hasDerivAt_id s).smul_const v).hasDerivWithinAt
      have h3 := h1.sub h2
      rwa [one_smul] at h3
    have hbound : ∀ s ∈ S, ‖f (Fl ξ₂ s) - v‖ ≤ c / 3 := by
      intro s hs
      have hs0 := hSpos s hs
      have hsT : s ≤ T₁ := by have := hs.2; linarith
      have hdist := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK)
        ((hsol ξ₂).mono (Icc_subset_Ici_self : Icc 0 s ⊆ Ici 0)) (hx₀I 0 s) s ⟨hs0, le_rfl⟩
      rw [dist_eq_norm, dist_eq_norm, hstart, sub_zero] at hdist
      have h1 : ‖Fl ξ₂ s - x₀ s‖ ≤ κ := by
        refine hdist.trans ?_
        have h2 : ‖ξ₂ - p‖ * E ≤ κ := by
          have := (hξ₂.trans_le (hra.trans haκ)).le
          rwa [le_div_iff₀ (by positivity)] at this
        calc ‖ξ₂ - x₀ 0‖ * Real.exp (K * s) ≤ ‖ξ₂ - p‖ * E :=
              mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsT K.2)) (norm_nonneg _)
          _ ≤ κ := h2
      have h3 : ‖x₀ s - x₀ t₀‖ ≤ κ := by
        have := hxδ (show dist s t₀ < δx by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
        rw [dist_eq_norm] at this
        exact this.le
      have h4 : ‖f (Fl ξ₂ s) - v‖ ≤ K * (κ + κ) := by
        have := hfK.dist_le_mul (Fl ξ₂ s) (x₀ t₀)
        rw [dist_eq_norm, dist_eq_norm] at this
        refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
        calc ‖Fl ξ₂ s - x₀ t₀‖ = ‖(Fl ξ₂ s - x₀ s) + (x₀ s - x₀ t₀)‖ := by abel_nf
          _ ≤ ‖Fl ξ₂ s - x₀ s‖ + ‖x₀ s - x₀ t₀‖ := norm_add_le _ _
          _ ≤ κ + κ := add_le_add h1 h3
      refine h4.trans ?_
      rw [hκ]
      have hK0 : (0 : ℝ) ≤ K := K.2
      rw [show (K : ℝ) * (c / (6 * (K + 1)) + c / (6 * (K + 1))) = c / 3 * (K / (K + 1)) by
        field_simp; ring]
      have : (K : ℝ) / (K + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    have hmem : ∀ t, |t - t₀| < r → t ∈ S := fun t ht => by
      have := abs_lt.1 (ht.trans_le hrb); constructor <;> linarith
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc _ _)
      (hmem t₂ ht₂) (hmem t₁ ht₁)
    rw [Real.norm_eq_abs] at h
    calc ‖Fl ξ₂ t₁ - Fl ξ₂ t₂ - (t₁ - t₂) • v‖ = ‖Fl ξ₂ t₁ - t₁ • v - (Fl ξ₂ t₂ - t₂ • v)‖ := by
          rw [sub_smul]; abel_nf
      _ ≤ c / 3 * |t₁ - t₂| := h
  -- assembling
  have hsplit : Fl ξ₁ t₁ - Fl ξ₂ t₂ - (transition A t₀ 0 *ᵥ (ξ₁ - ξ₂) + (t₁ - t₂) • v) =
      (Fl ξ₁ t₁ - Fl ξ₂ t₁ - transition A t₁ 0 *ᵥ (ξ₁ - ξ₂)) +
        (transition A t₁ 0 - transition A t₀ 0) *ᵥ (ξ₁ - ξ₂) +
        (Fl ξ₂ t₁ - Fl ξ₂ t₂ - (t₁ - t₂) • v) := by
    rw [Matrix.sub_mulVec]; abel
  have hn : ‖((ξ₁, t₁) - (ξ₂, t₂) : (Fin n → ℝ) × ℝ)‖ = max ‖ξ₁ - ξ₂‖ |t₁ - t₂| := by
    rw [Prod.norm_def]; rfl
  rw [hn]
  have hm1 : ‖ξ₁ - ξ₂‖ ≤ max ‖ξ₁ - ξ₂‖ |t₁ - t₂| := le_max_left _ _
  have hm2 : |t₁ - t₂| ≤ max ‖ξ₁ - ξ₂‖ |t₁ - t₂| := le_max_right _ _
  show ‖Fl ξ₁ t₁ - Fl ξ₂ t₂ - (transition A t₀ 0 *ᵥ (ξ₁ - ξ₂) + (t₁ - t₂) • v)‖ ≤ _
  rw [hsplit]
  calc _ ≤ ‖Fl ξ₁ t₁ - Fl ξ₂ t₁ - transition A t₁ 0 *ᵥ (ξ₁ - ξ₂)‖ +
        ‖(transition A t₁ 0 - transition A t₀ 0) *ᵥ (ξ₁ - ξ₂)‖ +
        ‖Fl ξ₂ t₁ - Fl ξ₂ t₂ - (t₁ - t₂) • v‖ := norm_add₃_le
    _ ≤ c / 3 * ‖ξ₁ - ξ₂‖ + c / 3 * ‖ξ₁ - ξ₂‖ + c / 3 * |t₁ - t₂| := by gcongr
    _ ≤ c / 3 * max ‖ξ₁ - ξ₂‖ |t₁ - t₂| + c / 3 * max ‖ξ₁ - ξ₂‖ |t₁ - t₂| +
        c / 3 * max ‖ξ₁ - ξ₂‖ |t₁ - t₂| := by gcongr
    _ = c * max ‖ξ₁ - ξ₂‖ |t₁ - t₂| := by ring

/-! ## The return time -/

@[tmio T, powerlib_foundation] private theorem dot_self_pos {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
    (Ne.symm (dotProduct_self_eq_zero.not.2 hv))

/-- **The return time to the transversal section**, by the implicit function theorem. For a
nonconstant periodic orbit `x_*` (`x_*(T) = x_*(0)`, `v = f(x_*(0)) ≠ 0`) there is a return time
`τ` with `τ(p) = T` and strict derivative `−(v ⬝ M ·)/(v ⬝ v)` at `p = x_*(0)`, and radii `r`,
`s ≤ T/2` such that for `‖ξ − p‖ < r` the solution from `ξ` crosses the hyperplane
`v ⬝ (x − p) = 0` at the time `τ(ξ)`, `|τ(ξ) − T| < s`, and at no other time `t` with
`|t − T| < s`. -/
@[tmio T, powerlib_foundation] theorem exists_returnTime (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : xs T = xs 0) (hne : f (xs 0) ≠ 0) :
    ∃ τ : (Fin n → ℝ) → ℝ, τ (xs 0) = T ∧
      HasStrictFDerivAt τ (-(f (xs 0) ⬝ᵥ f (xs 0))⁻¹ •
        dotCLM (f (xs 0) ᵥ* monodromy (variationalMatrix f xs) T 0)) (xs 0) ∧
      ∃ r s : ℝ, 0 < r ∧ 0 < s ∧ s ≤ T / 2 ∧
        (∀ ξ, ‖ξ - xs 0‖ < r → |τ ξ - T| < s ∧ f (xs 0) ⬝ᵥ
          (flow (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) 0 ξ (τ ξ) -
            xs 0) = 0) ∧
        ∀ ξ t, ‖ξ - xs 0‖ < r → |t - T| < s → f (xs 0) ⬝ᵥ
          (flow (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) 0 ξ t -
            xs 0) = 0 → t = τ ξ := by
  set hGc : Continuous (uncurry fun _ : ℝ => f) := hfK.continuous.comp continuous_snd
  set Fl := flow (G := fun _ => f) hGc (fun _ => hfK) 0 with hFl
  set p := xs 0 with hp
  set v := f (xs 0) with hv
  set M := monodromy (variationalMatrix f xs) T 0 with hM
  have hvT : f (xs T) = v := by rw [hper]
  have hFlp : Fl p T = p := by
    have h := flow_eq hGc (fun _ => hfK) (β := xs) rfl (fun r _ => (hxs r).hasDerivWithinAt) T
      ⟨hT.le, le_rfl⟩
    exact h.symm.trans hper
  have hcv := dot_self_pos hne
  set cv := v ⬝ᵥ v with hcvdef
  -- the section functional and its strict derivative
  set L := (Matrix.toLin' M).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ) +
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight v with hL
  have hFlD : HasStrictFDerivAt (fun q : (Fin n → ℝ) × ℝ => Fl q.1 q.2) L (p, T) := by
    have h := hasStrictFDerivAt_flow_prod hf hfK hxs hT
    rw [hvT] at h
    rw [hL, hM, monodromy, zero_add]
    exact h
  set g : (Fin n → ℝ) × ℝ → ℝ := fun q => v ⬝ᵥ (Fl q.1 q.2 - p) with hg
  set D := (dotCLM v).comp L with hD
  have hgD : HasStrictFDerivAt g D (p, T) :=
    (dotCLM v).hasStrictFDerivAt.comp (p, T) (hFlD.sub_const p)
  have hD2 : D.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ) =
      cv • ContinuousLinearMap.id ℝ ℝ := by
    ext1
    simp [hD, hL, dotCLM_apply, hcvdef]
  have hinv : (D.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)).IsInvertible := by
    rw [hD2]
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := cv⁻¹ • ContinuousLinearMap.id ℝ ℝ)
      ?_ ?_ <;> ext1 <;> simp [hcv.ne']
  have hinverse : (D.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)).inverse =
      cv⁻¹ • ContinuousLinearMap.id ℝ ℝ := by
    rw [hD2]
    exact ContinuousLinearMap.inverse_eq (by ext1; simp [hcv.ne']) (by ext1; simp [hcv.ne'])
  set τ := hgD.implicitFunctionOfProdDomain hinv with hτ
  have hg0 : g (p, T) = 0 := by simp [hg, hFlp]
  have hiff := hgD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  rw [hg0] at hiff
  have hτp : τ p = T := (hiff.self_of_nhds.1 hg0)
  have hτD := hgD.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  refine ⟨τ, hτp, ?_, ?_⟩
  · refine hτD.congr_fderiv ?_
    rw [hinverse]
    ext1 e
    simp [hD, hL, dotCLM_apply, Matrix.dotProduct_mulVec]
  -- the radii
  obtain ⟨ε, hε, hεiff⟩ := Metric.eventually_nhds_iff.1 hiff
  set s := min (ε / 2) (T / 2) with hs
  have hs0 : 0 < s := by positivity
  have hτc : ContinuousAt τ p := hτD.continuousAt
  have hsec := hgD.eventually_apply_implicitFunctionOfProdDomain hinv
  rw [hg0] at hsec
  have hev : ∀ᶠ ξ in 𝓝 p, |τ ξ - T| < s ∧ g (ξ, τ ξ) = 0 := by
    have h1 : ∀ᶠ ξ in 𝓝 p, dist (τ ξ) (τ p) < s := Metric.eventually_nhds_iff.2
      (Metric.continuousAt_iff.1 hτc s hs0)
    filter_upwards [h1, hsec] with ξ h1 h2
    rw [Real.dist_eq, hτp] at h1
    exact ⟨h1, h2⟩
  obtain ⟨r₁, hr₁, hr₁ev⟩ := Metric.eventually_nhds_iff.1 hev
  set r := min r₁ (ε / 2) with hr
  have hr0 : 0 < r := by positivity
  refine ⟨r, s, hr0, hs0, min_le_right _ _, fun ξ hξ => ?_, fun ξ t hξ ht hgt => ?_⟩
  · have := hr₁ev (show dist ξ p < r₁ by
      rw [dist_eq_norm]; exact hξ.trans_le (min_le_left _ _))
    exact this
  · have hq : dist (ξ, t) (p, T) < ε := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, Real.dist_eq]
      constructor
      · exact hξ.trans_le ((min_le_right _ _).trans (by linarith))
      · exact ht.trans_le ((min_le_left _ _).trans (by linarith))
    exact ((hεiff hq).1 hgt).symm

/-! ## The deflated monodromy and the nontrivial multipliers -/

section Deflation

open Polynomial

variable {M : Matrix (Fin n) (Fin n) ℝ} {v w : Fin n → ℝ}

/-- **Brauer's deflation.** If `M v = v` and `w ⬝ v = 1`, the characteristic polynomials of `M`
and of the deflated matrix `M − v wᵀ` satisfy `χ_{M − v wᵀ}(X) (X − 1) = X χ_M(X)`: the
eigenvalue `1` of `M` on `v` is replaced by `0`, the others (with multiplicity) are kept. -/
@[tmio T, powerlib_foundation] theorem charpoly_deflate (hMv : M *ᵥ v = v) (hwv : w ⬝ᵥ v = 1) :
    (M - vecMulVec v w).charpoly * (X - 1) = X * M.charpoly := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hfin : {z : ℝ | z = 1 ∨ M.charpoly.IsRoot z}.Finite :=
    (Set.finite_singleton 1).union (finite_setOfPred_isRoot (Matrix.charpoly_monic M).ne_zero)
  refine Set.Infinite.mono ?_ hfin.infinite_compl
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, IsRoot.def] at hz
  obtain ⟨hz1, hzM⟩ := hz
  simp only [Set.mem_ofPred_eq, IsRoot.def, eval_sub, eval_mul, eval_X, eval_one,
    Matrix.eval_charpoly]
  rw [Matrix.eval_charpoly] at hzM
  set A := Matrix.scalar (Fin n) z - M with hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hzM
  have hAv : A *ᵥ v = (z - 1) • v := by
    ext i
    simp [hA, Matrix.sub_mulVec, hMv, sub_mul]
  have hAinv : A⁻¹ *ᵥ v = (z - 1)⁻¹ • v := by
    have h1 : A⁻¹ *ᵥ (A *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hAu, Matrix.one_mulVec]
    rw [hAv, Matrix.mulVec_smul] at h1
    calc A⁻¹ *ᵥ v = (z - 1)⁻¹ • ((z - 1) • A⁻¹ *ᵥ v) := by
          rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hz1), one_smul]
      _ = (z - 1)⁻¹ • v := by rw [h1]
  have hsplit : Matrix.scalar (Fin n) z - (M - vecMulVec v w) =
      A + replicateCol Unit v * replicateRow Unit w := by
    rw [hA, ← Matrix.vecMulVec_eq]; abel
  rw [hsplit, Matrix.det_add_replicateCol_mul_replicateRow hAu, ← Matrix.replicateRow_vecMul,
    Matrix.replicateRow_mul_replicateCol, Matrix.det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
  rw [← Matrix.dotProduct_mulVec, hAinv, dotProduct_smul, hwv, smul_eq_mul, mul_one]
  field_simp [sub_ne_zero.2 hz1]
  ring

/-- The complex characteristic polynomials: `χ_{M − v wᵀ}(μ) (μ − 1) = μ χ_M(μ)` for `μ ∈ ℂ`. -/
@[tmio T, powerlib_foundation] private theorem eval_charpoly_deflate (hMv : M *ᵥ v = v)
    (hwv : w ⬝ᵥ v = 1) (μ : ℂ) :
    ((M - vecMulVec v w).map (algebraMap ℝ ℂ)).charpoly.eval μ * (μ - 1) =
      μ * (M.map (algebraMap ℝ ℂ)).charpoly.eval μ := by
  have h := congrArg (fun P : ℝ[X] => (P.map (algebraMap ℝ ℂ)).eval μ) (charpoly_deflate hMv hwv)
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one,
    eval_mul, eval_sub, eval_X, eval_one] at h
  rw [Matrix.charpoly_map, Matrix.charpoly_map]
  exact h

/-- **The nontrivial multipliers are the eigenvalues of the deflation.** For `M v = v`,
`w ⬝ v = 1` and a complex `μ ∉ {0, 1}`: `μ` is an eigenvalue of `M − v wᵀ` exactly when it is
an eigenvalue (a Floquet multiplier) of `M`. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_deflate_iff (hMv : M *ᵥ v = v)
    (hwv : w ⬝ᵥ v = 1) {μ : ℂ} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) :
    μ ∈ spectrum ℂ ((M - vecMulVec v w).map (algebraMap ℝ ℂ)) ↔
      μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    IsRoot.def, IsRoot.def]
  have h := eval_charpoly_deflate hMv hwv μ
  constructor
  · intro h0
    rw [h0, zero_mul] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hμ0
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hμ1)

/-- **The trivial multiplier is simple exactly when the deflation does not have it.** For
`M v = v` and `w ⬝ v = 1`, `1` is an eigenvalue of `M − v wᵀ` exactly when it is a multiple root
of the characteristic polynomial of `M`. -/
@[tmio T, powerlib_foundation] theorem one_mem_spectrum_deflate_iff (hMv : M *ᵥ v = v)
    (hwv : w ⬝ᵥ v = 1) :
    (1 : ℂ) ∈ spectrum ℂ ((M - vecMulVec v w).map (algebraMap ℝ ℂ)) ↔
      (X - 1 : ℝ[X]) ^ 2 ∣ M.charpoly := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map, IsRoot.def,
    show (1 : ℂ) = algebraMap ℝ ℂ 1 from (map_one _).symm, Polynomial.eval_map_algebraMap,
    Polynomial.aeval_algebraMap_apply, map_eq_zero_iff _ (algebraMap ℝ ℂ).injective, aeval_def,
    Algebra.algebraMap_self, eval₂_id, ← IsRoot.def, ← dvd_iff_isRoot, ← map_one C]
  have hcop : IsCoprime ((X - C 1 : ℝ[X]) ^ 2) X := by
    refine IsCoprime.pow_left ⟨-1, 1, ?_⟩
    rw [map_one]; ring
  have h := charpoly_deflate hMv hwv
  rw [← map_one C] at h
  constructor
  · rintro ⟨q, hq⟩
    refine hcop.dvd_of_dvd_mul_left ⟨q, ?_⟩
    rw [← h, hq]; ring
  · intro hd
    have h1 : (X - C 1 : ℝ[X]) ^ 2 ∣ (M - vecMulVec v w).charpoly * (X - C 1) := by
      rw [h]; exact Dvd.dvd.mul_left hd X
    rw [pow_two] at h1
    exact (mul_dvd_mul_iff_right (X_sub_C_ne_zero 1)).1 h1

/-- **Schur stability of the deflation is the Andronov–Witt condition.** For `M v = v`,
`v ≠ 0` and `w ⬝ v = 1`: the deflated matrix `M − v wᵀ` is Schur stable exactly when `1` is a
simple root of the characteristic polynomial of `M` and every other complex multiplier lies
strictly inside the unit circle. In particular the condition does not depend on `w`. -/
@[tmio T, powerlib_foundation] theorem schurStable_deflate_iff (hMv : M *ᵥ v = v) (hv : v ≠ 0)
    (hwv : w ⬝ᵥ v = 1) :
    LTI.SchurStable (M - vecMulVec v w) ↔
      M.charpoly.rootMultiplicity 1 = 1 ∧
        ∀ μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), μ ≠ 1 → ‖μ‖ < 1 := by
  have hroot : M.charpoly.IsRoot 1 := by
    rw [IsRoot.def, Matrix.eval_charpoly]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv, ?_⟩
    ext i
    simp [Matrix.sub_mulVec, hMv]
  have hM0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hmult : M.charpoly.rootMultiplicity 1 = 1 ↔ ¬ (X - 1 : ℝ[X]) ^ 2 ∣ M.charpoly := by
    rw [← map_one C, le_rootMultiplicity_iff hM0 |>.symm.not]
    have h1 : 0 < M.charpoly.rootMultiplicity 1 := (rootMultiplicity_pos hM0).2 hroot
    omega
  have hspec : ∀ {Φ : Matrix (Fin n) (Fin n) ℝ}, LTI.SchurStable Φ ↔
      ∀ μ ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)), ‖μ‖ < 1 := fun {Φ} => by
    refine ⟨fun h μ hμ => ?_, fun h μ z hz hΦz => h μ ?_⟩
    · obtain ⟨z, hz, hΦz⟩ := LTI.mem_spectrum_iff_exists_eigvec.1 hμ
      exact h μ z hz hΦz
    · exact LTI.mem_spectrum_iff_exists_eigvec.2 ⟨z, hz, hΦz⟩
  rw [hspec, hmult, ← one_mem_spectrum_deflate_iff hMv hwv]
  constructor
  · intro h
    refine ⟨fun h1 => by simpa using h 1 h1, fun μ hμ hμ1 => ?_⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp
    · exact h μ ((mem_spectrum_deflate_iff hMv hwv hμ0 hμ1).2 hμ)
  · rintro ⟨h1, h⟩ μ hμ
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp
    rcases eq_or_ne μ 1 with rfl | hμ1
    · exact absurd hμ h1
    · exact h μ ((mem_spectrum_deflate_iff hMv hwv hμ0 hμ1).1 hμ) hμ1

end Deflation

/-! ## The Poincaré map and its derivative -/

/-- **The Jacobian of the Poincaré map**, `M − v uᵀ` with `u = Mᵀ v/|v|²`: the monodromy `M`
followed by the projection along the velocity `v` onto the hyperplane `v^⊥` of the section,
`e ↦ M e − ((v ⬝ M e)/(v ⬝ v)) v`. -/
def sectionMatrix (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  M - vecMulVec v ((v ⬝ᵥ v)⁻¹ • (v ᵥ* M))

@[tmio T, powerlib_foundation] theorem sectionMatrix_mulVec (M : Matrix (Fin n) (Fin n) ℝ)
    (v e : Fin n → ℝ) :
    sectionMatrix M v *ᵥ e = M *ᵥ e - ((v ⬝ᵥ (M *ᵥ e)) / (v ⬝ᵥ v)) • v := by
  rw [sectionMatrix, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
    ← Matrix.dotProduct_mulVec, smul_eq_mul, inv_mul_eq_div]

/-- The section vector `u = Mᵀ v/|v|²` satisfies `u ⬝ v = 1` when `M v = v`, `v ≠ 0`: the
Jacobian of the Poincaré map is a deflation of the monodromy. -/
@[tmio T, powerlib_foundation] theorem sectionVec_dotProduct {M : Matrix (Fin n) (Fin n) ℝ}
    {v : Fin n → ℝ} (hMv : M *ᵥ v = v) (hv : v ≠ 0) :
    ((v ⬝ᵥ v)⁻¹ • (v ᵥ* M)) ⬝ᵥ v = 1 := by
  rw [smul_dotProduct, ← Matrix.dotProduct_mulVec, hMv, smul_eq_mul,
    inv_mul_cancel₀ (dot_self_pos hv).ne']

/-- The Poincaré map takes values in the section: `v ⬝ (DΠ e) = 0`, and kills the velocity:
`DΠ v = 0` when `M v = v`. -/
@[tmio T, powerlib_foundation] theorem sectionMatrix_maps {M : Matrix (Fin n) (Fin n) ℝ}
    {v : Fin n → ℝ} (hv : v ≠ 0) :
    (∀ e, v ⬝ᵥ (sectionMatrix M v *ᵥ e) = 0) ∧ (M *ᵥ v = v → sectionMatrix M v *ᵥ v = 0) := by
  refine ⟨fun e => ?_, fun hMv => ?_⟩
  · rw [sectionMatrix_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      div_mul_cancel₀ _ (dot_self_pos hv).ne', sub_self]
  · rw [sectionMatrix_mulVec, hMv, div_self (dot_self_pos hv).ne', one_smul, sub_self]

/-- **Schur stability of the Poincaré Jacobian is the Andronov–Witt condition**: for `M v = v`,
`v ≠ 0`, `sectionMatrix M v` is Schur stable exactly when `M − v wᵀ` is, for any `w` with
`w ⬝ v = 1`, exactly when `1` is a simple multiplier and every other multiplier lies strictly
inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem schurStable_sectionMatrix_iff
    {M : Matrix (Fin n) (Fin n) ℝ} {v w : Fin n → ℝ} (hMv : M *ᵥ v = v) (hv : v ≠ 0)
    (hwv : w ⬝ᵥ v = 1) :
    (LTI.SchurStable (sectionMatrix M v) ↔ LTI.SchurStable (M - vecMulVec v w)) ∧
      (LTI.SchurStable (sectionMatrix M v) ↔ M.charpoly.rootMultiplicity 1 = 1 ∧
        ∀ μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), μ ≠ 1 → ‖μ‖ < 1) := by
  have h := schurStable_deflate_iff hMv hv (sectionVec_dotProduct hMv hv)
  rw [← sectionMatrix] at h
  exact ⟨h.trans (schurStable_deflate_iff hMv hv hwv).symm, h⟩

/-- The Poincaré map `Π(ξ) = x(τ(ξ); ξ)` of a return time `τ`: the flow from `ξ` read at the
time `τ(ξ)`. -/
def poincareMap (hfK : LipschitzWith K f) (τ : (Fin n → ℝ) → ℝ) (ξ : Fin n → ℝ) : Fin n → ℝ :=
  flow (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) 0 ξ (τ ξ)

/-- The Poincaré map reads every solution from `ξ` at the return time. -/
@[tmio T, powerlib_foundation] theorem poincareMap_eq (hfK : LipschitzWith K f)
    (τ : (Fin n → ℝ) → ℝ) {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    (hτ : 0 ≤ τ (x 0)) : poincareMap hfK τ (x 0) = x (τ (x 0)) :=
  (flow_eq _ (fun _ => hfK) rfl (hx.mono Icc_subset_Ici_self) _ ⟨hτ, le_rfl⟩).symm

/-- **The Poincaré map of a periodic orbit.** Let `x_*` be a nonconstant `T`-periodic orbit of
`ẋ = f(x)` (`f` of class `C¹`, globally `K`-Lipschitz, `f(x_*(0)) ≠ 0`), `M` its monodromy
matrix and `Σ = {ξ : f(x_*(0)) ⬝ (ξ − x_*(0)) = 0}` the hyperplane through `p = x_*(0)`
transverse to the orbit. There is a return time `τ` with `τ(p) = T` such that, near `p`, the
solutions of `f(p) ⬝ (x(t; ξ) − p) = 0` with `t` near `T` are exactly `t = τ(ξ)`, and the Poincaré
map `Π(ξ) = x(τ(ξ); ξ)` takes values in `Σ`, fixes `p` and has the strict derivative
`sectionMatrix M f(p) = M − f(p) uᵀ`, `u = Mᵀ f(p)/|f(p)|²`. This Jacobian maps into `f(p)^⊥`,
kills `f(p)` and has the characteristic polynomial `χ_M(X) X/(X − 1)`: its eigenvalues on the
section are the nontrivial multipliers, with multiplicity, and its remaining eigenvalue `0` is
that of the direction `f(p)` along the orbit. -/
@[tmio T, powerlib_foundation] theorem exists_poincareMap (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) :
    ∃ τ : (Fin n → ℝ) → ℝ, τ (xs 0) = T ∧
      HasStrictFDerivAt τ (-(f (xs 0) ⬝ᵥ f (xs 0))⁻¹ •
        dotCLM (f (xs 0) ᵥ* monodromy (variationalMatrix f xs) T 0)) (xs 0) ∧
      (∃ r s : ℝ, 0 < r ∧ 0 < s ∧ s ≤ T / 2 ∧
        (∀ ξ, ‖ξ - xs 0‖ < r →
          |τ ξ - T| < s ∧ f (xs 0) ⬝ᵥ (poincareMap hfK τ ξ - xs 0) = 0) ∧
        ∀ ξ t, ‖ξ - xs 0‖ < r → |t - T| < s → f (xs 0) ⬝ᵥ
          (flow (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) 0 ξ t -
            xs 0) = 0 → t = τ ξ) ∧
      poincareMap hfK τ (xs 0) = xs 0 ∧
      HasStrictFDerivAt (poincareMap hfK τ)
        (Matrix.toLin' (sectionMatrix (monodromy (variationalMatrix f xs) T 0)
          (f (xs 0)))).toContinuousLinearMap (xs 0) ∧
      monodromy (variationalMatrix f xs) T 0 *ᵥ f (xs 0) = f (xs 0) ∧
      (∀ e, f (xs 0) ⬝ᵥ
        (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)) *ᵥ e) = 0) ∧
      sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0)) *ᵥ f (xs 0) = 0 ∧
      (sectionMatrix (monodromy (variationalMatrix f xs) T 0) (f (xs 0))).charpoly *
        (Polynomial.X - 1) = Polynomial.X * (monodromy (variationalMatrix f xs) T 0).charpoly := by
  have hfix : xs T = xs 0 := by simpa using hper 0
  obtain ⟨τ, hτp, hτD, hsec⟩ := exists_returnTime hf hfK hxs hT hfix hne
  set hGc : Continuous (uncurry fun _ : ℝ => f) := hfK.continuous.comp continuous_snd
  set p := xs 0 with hp
  set v := f (xs 0) with hv
  set M := monodromy (variationalMatrix f xs) T 0 with hM
  have hMv : M *ᵥ v = v := monodromy_mulVec_velocity hf hxs hT hper
  have hPp : poincareMap hfK τ p = p := by
    have h := flow_eq hGc (fun _ => hfK) (β := xs) rfl (fun r _ => (hxs r).hasDerivWithinAt) T
      ⟨hT.le, le_rfl⟩
    show flow hGc (fun _ => hfK) 0 p (τ p) = p
    rw [hτp]
    exact h.symm.trans hfix
  -- the derivative: the flow along `ξ ↦ (ξ, τ ξ)`
  have hFlD := hasStrictFDerivAt_flow_prod hf hfK hxs hT
  rw [show f (xs T) = v by rw [hfix]] at hFlD
  have hpair : HasStrictFDerivAt (fun ξ : Fin n → ℝ => (ξ, τ ξ))
      ((ContinuousLinearMap.id ℝ (Fin n → ℝ)).prod
        (-(v ⬝ᵥ v)⁻¹ • dotCLM (v ᵥ* M))) p := (hasStrictFDerivAt_id p).prodMk hτD
  have hcomp := HasStrictFDerivAt.comp p (hτp ▸ hFlD : HasStrictFDerivAt
    (fun q : (Fin n → ℝ) × ℝ =>
      flow (G := fun _ => f) hGc (fun _ => hfK) 0 q.1 q.2) _ (p, τ p)) hpair
  have hPD : HasStrictFDerivAt (poincareMap hfK τ)
      (Matrix.toLin' (sectionMatrix M v)).toContinuousLinearMap p := by
    refine hcomp.congr_fderiv ?_
    ext1 e
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, _root_.add_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, _root_.smul_apply,
      dotCLM_apply, smul_eq_mul]
    have hMT : transition (variationalMatrix f xs) T 0 = M := by rw [hM, monodromy, zero_add]
    rw [hτp, hMT, sectionMatrix_mulVec, ← Matrix.dotProduct_mulVec, div_eq_inv_mul,
      sub_eq_add_neg, ← neg_smul, neg_mul]
  obtain ⟨r, s, hr, hs, hsT, hsec1, huniq⟩ := hsec
  have hmaps := sectionMatrix_maps (M := M) hne
  refine ⟨τ, hτp, hτD, ⟨r, s, hr, hs, hsT, hsec1, huniq⟩, hPp, hPD, hMv, hmaps.1,
    hmaps.2 hMv, ?_⟩
  have h := charpoly_deflate hMv (sectionVec_dotProduct hMv hne)
  rwa [← sectionMatrix] at h

end powerlib.Periodic.PoincareSection
