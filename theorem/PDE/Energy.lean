import theorem.PDE.Partial
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Energy method: uniqueness for the heat equation, energy conservation for the wave equation

Energy identities for classical solutions of the one-dimensional heat and lossless wave equations
with homogeneous Dirichlet data.

Model boundary.
* One space dimension, `x ∈ [0, ℓ]` (`ℓ > 0`), homogeneous Dirichlet data
  `u(0,t) = u(ℓ,t) = 0`, constant coefficients `ν > 0`, `c`; classical solutions that extend to
  `C²` functions on the whole plane (`ContDiff ℝ 2` on `ℝ × ℝ`, coordinates `(x, t)`); partial
  derivatives `dx`, `dt` from `theorem/PDE/Partial.lean`; the PDE is required on the closed
  strip `[0, ℓ] × [0, ∞)` (heat) or `[0, ℓ] × ℝ` (wave).
* Canonical PDEs, not an engineering model: no model family; foundation results.

Source: work-sync `theory/T-pde-systems.md` §1.8.2 (heat equation: `E(t) = ½∫u²`,
`Ė = −ν∫u_x² ≤ 0` ⇒ uniqueness), §1.8.3 (lossless wave equation: `E(t) = ½∫(u_t² + c²u_x²)`
is conserved).

Results.
* `hasDerivAt_integral_param`: differentiation under `∫₀^ℓ` for jointly continuous integrands
  with a jointly continuous `t`-derivative (Mathlib's dominated version, bound by compactness).
* `hasDerivAt_energy`, `heat_energy_identity`: `d/dt ∫₀^ℓ u² = 2∫₀^ℓ u u_t = −2ν ∫₀^ℓ u_x² ≤ 0`
  (integration by parts, boundary terms vanish); `heat_zero_of_zero_data` / `heat_unique`: the
  solution with zero initial data is identically zero on `[0, ℓ] × [0, ∞)`, so two classical
  solutions with the same initial and boundary data coincide.
* `wave_energy_conserved`: `E(t) = ½∫₀^ℓ (u_t² + c² u_x²)` is constant in `t`.
-/

noncomputable section
namespace powerlib.PDE
open Set MeasureTheory intervalIntegral

/-! ## Differentiation under the integral sign -/

/-- `d/dt ∫ₐᵇ G(x,t) dx = ∫ₐᵇ G_t(x,t) dx` for continuous `G`, `G_t`. -/
@[powerlib_foundation] theorem hasDerivAt_integral_param {G Gt : ℝ × ℝ → ℝ} (a b : ℝ)
    (hG : Continuous G) (hGt : Continuous Gt)
    (hd : ∀ x τ, HasDerivAt (fun s => G (x, s)) (Gt (x, τ)) τ) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, G (x, s)) (∫ x in a..b, Gt (x, t)) t := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall t 1)).exists_bound_of_continuousOn
    hGt.continuousOn
  have hmeasG : ∀ s, Continuous fun x => G (x, s) := fun s => hG.comp (by fun_prop)
  have hmeasGt : ∀ s, Continuous fun x => Gt (x, s) := fun s => hGt.comp (by fun_prop)
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s x => G (x, s)) (F' := fun s x => Gt (x, s)) (x₀ := t) (a := a) (b := b)
    (bound := fun _ => C) (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (hmeasG s).aestronglyMeasurable)
    ((hmeasG t).intervalIntegrable a b) (hmeasGt t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x hx s hs => hC (x, s)
      ⟨uIoc_subset_uIcc hx, Metric.ball_subset_closedBall hs⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun x _ s _ => hd x s)
  exact this.2

/-! ## Partial derivatives of `C²` functions along coordinate lines -/

variable {u : ℝ × ℝ → ℝ}

@[powerlib_foundation] theorem hasDerivAt_x_line (hu : Differentiable ℝ u) (x t : ℝ) :
    HasDerivAt (fun y => u (y, t)) (dx u (x, t)) x := by
  have h := (hu (x, t)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id' x).prodMk (hasDerivAt_const x t))
  exact h

@[powerlib_foundation] theorem hasDerivAt_t_line (hu : Differentiable ℝ u) (x t : ℝ) :
    HasDerivAt (fun s => u (x, s)) (dt u (x, t)) t := by
  have h := (hu (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id' t))
  exact h

@[powerlib_foundation] theorem continuous_dx (hu : ContDiff ℝ 2 u) : Continuous (dx u) :=
  ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const)

@[powerlib_foundation] theorem continuous_dt (hu : ContDiff ℝ 2 u) : Continuous (dt u) :=
  ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const)

@[powerlib_foundation] theorem continuous_second (hu : ContDiff ℝ 2 u) (v w : ℝ × ℝ) :
    Continuous (fun p => fderiv ℝ (fun q => fderiv ℝ u q w) p v) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hfun : (fun p => fderiv ℝ (fun q => fderiv ℝ u q w) p v) =
      fun p => fderiv ℝ (fderiv ℝ u) p v w := by
    funext p
    rw [(hasFDerivAt_fderiv_apply hu w p).fderiv]
    rfl
  rw [hfun]
  exact ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const

@[powerlib_foundation] theorem continuous_dxdx (hu : ContDiff ℝ 2 u) : Continuous (dx (dx u)) :=
  continuous_second hu (1, 0) (1, 0)

@[powerlib_foundation] theorem continuous_dtdt (hu : ContDiff ℝ 2 u) : Continuous (dt (dt u)) :=
  continuous_second hu (0, 1) (0, 1)

@[powerlib_foundation] theorem continuous_dtdx (hu : ContDiff ℝ 2 u) : Continuous (dt (dx u)) :=
  continuous_second hu (0, 1) (1, 0)

/-! ## Heat equation: energy dissipation and uniqueness -/

/-- `d/dt ∫₀^ℓ u² = 2∫₀^ℓ u u_t`. -/
@[powerlib_foundation] theorem hasDerivAt_energy (hu : ContDiff ℝ 2 u) (ℓ t : ℝ) :
    HasDerivAt (fun s => ∫ x in (0 : ℝ)..ℓ, u (x, s) ^ 2)
      (∫ x in (0 : ℝ)..ℓ, 2 * u (x, t) * dt u (x, t)) t := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  refine hasDerivAt_integral_param (G := fun p => u p ^ 2) (Gt := fun p => 2 * u p * dt u p) 0 ℓ
    (hu.continuous.pow 2) ((continuous_const.mul hu.continuous).mul (continuous_dt hu)) ?_ t
  intro x τ
  have := (hasDerivAt_pow 2 (u (x, τ))).comp τ (hasDerivAt_t_line hd x τ)
  exact this.congr_deriv (by push_cast; ring)

/-- **Energy dissipation** for `u_t = ν u_xx` with zero Dirichlet data at time `t`:
`∫₀^ℓ u u_t = −ν ∫₀^ℓ u_x²`. -/
@[powerlib_foundation] theorem heat_energy_identity {ν ℓ t : ℝ} (hu : ContDiff ℝ 2 u)
    (hpde : ∀ x ∈ uIcc 0 ℓ, dt u (x, t) = ν * dx (dx u) (x, t))
    (h0 : u (0, t) = 0) (hℓ : u (ℓ, t) = 0) :
    ∫ x in (0 : ℝ)..ℓ, 2 * u (x, t) * dt u (x, t) = -(2 * ν) * ∫ x in (0 : ℝ)..ℓ, dx u (x, t) ^ 2 := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdxd : Differentiable ℝ (dx u) := differentiable_dx hu
  have hcongr : ∫ x in (0 : ℝ)..ℓ, 2 * u (x, t) * dt u (x, t) =
      ∫ x in (0 : ℝ)..ℓ, 2 * ν * (u (x, t) * dx (dx u) (x, t)) :=
    integral_congr fun x hx => by rw [hpde x hx]; ring
  have hibp := integral_mul_deriv_eq_deriv_mul (a := 0) (b := ℓ)
    (u := fun x => u (x, t)) (u' := fun x => dx u (x, t))
    (v := fun x => dx u (x, t)) (v' := fun x => dx (dx u) (x, t))
    (fun x _ => hasDerivAt_x_line hd x t) (fun x _ => hasDerivAt_x_line hdxd x t)
    ((continuous_dx hu).comp (by fun_prop) |>.intervalIntegrable 0 ℓ)
    ((continuous_dxdx hu).comp (by fun_prop) |>.intervalIntegrable 0 ℓ)
  rw [hcongr, intervalIntegral.integral_const_mul, hibp, h0, hℓ]
  simp only [zero_mul, sub_zero, zero_sub]
  rw [show (fun x => dx u (x, t) * dx u (x, t)) = fun x => dx u (x, t) ^ 2 by funext; ring]
  ring

/-- **Uniqueness for the heat equation (energy method)**: a classical solution of
`u_t = ν u_xx` on `[0, ℓ] × [0, ∞)` with zero Dirichlet data and zero initial data vanishes. -/
@[powerlib_foundation] theorem heat_zero_of_zero_data {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ)
    (hu : ContDiff ℝ 2 u)
    (hpde : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 ℓ, dt u (x, t) = ν * dx (dx u) (x, t))
    (hbc : ∀ t, 0 ≤ t → u (0, t) = 0 ∧ u (ℓ, t) = 0) (hic : ∀ x ∈ Icc 0 ℓ, u (x, 0) = 0) :
    ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 ℓ, u (x, t) = 0 := by
  set E := fun s => ∫ x in (0 : ℝ)..ℓ, u (x, s) ^ 2
  have hE : ∀ t, HasDerivAt E (∫ x in (0 : ℝ)..ℓ, 2 * u (x, t) * dt u (x, t)) t :=
    hasDerivAt_energy hu ℓ
  have hEnonpos : ∀ t, 0 ≤ t → (∫ x in (0 : ℝ)..ℓ, 2 * u (x, t) * dt u (x, t)) ≤ 0 := by
    intro t ht
    rw [heat_energy_identity hu (fun x hx => hpde t ht x (by rwa [uIcc_of_le hℓ.le] at hx))
      (hbc t ht).1 (hbc t ht).2]
    have : 0 ≤ ∫ x in (0 : ℝ)..ℓ, dx u (x, t) ^ 2 :=
      intervalIntegral.integral_nonneg hℓ.le fun x _ => sq_nonneg _
    nlinarith
  have hanti : AntitoneOn E (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun s _ => (hE s).continuousAt.continuousWithinAt
    · exact fun s _ => (hE s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hE s).deriv]
      exact hEnonpos s (le_of_lt hs)
  have hE0 : E 0 = 0 := by
    simp only [E]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => by
      rw [hic x (by rwa [uIcc_of_le hℓ.le] at hx)]; ring)]
    simp
  intro t ht x hx
  have hEt : E t ≤ 0 := by
    have := hanti (Set.mem_Ici.mpr le_rfl) ht ht
    rwa [hE0] at this
  by_contra hne
  have hpos : 0 < E t := by
    apply intervalIntegral.integral_pos hℓ
    · exact ((hu.continuous.comp (by fun_prop)).pow 2).continuousOn
    · intro y _; exact sq_nonneg _
    · exact ⟨x, hx, by positivity⟩
  linarith

/-- **Uniqueness**: two classical solutions with the same initial and Dirichlet data coincide. -/
@[powerlib_foundation] theorem heat_unique {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ)
    {u₁ u₂ : ℝ × ℝ → ℝ} (h₁ : ContDiff ℝ 2 u₁) (h₂ : ContDiff ℝ 2 u₂)
    (hpde₁ : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 ℓ, dt u₁ (x, t) = ν * dx (dx u₁) (x, t))
    (hpde₂ : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 ℓ, dt u₂ (x, t) = ν * dx (dx u₂) (x, t))
    (hbc : ∀ t, 0 ≤ t → u₁ (0, t) = u₂ (0, t) ∧ u₁ (ℓ, t) = u₂ (ℓ, t))
    (hic : ∀ x ∈ Icc 0 ℓ, u₁ (x, 0) = u₂ (x, 0)) :
    ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 ℓ, u₁ (x, t) = u₂ (x, t) := by
  have hw : ContDiff ℝ 2 (fun p => u₁ p - u₂ p) := h₁.sub h₂
  have hd₁ : Differentiable ℝ u₁ := h₁.differentiable (by norm_num)
  have hd₂ : Differentiable ℝ u₂ := h₂.differentiable (by norm_num)
  have hdx₁ := differentiable_dx h₁
  have hdx₂ := differentiable_dx h₂
  have hdt : ∀ p, dt (fun p => u₁ p - u₂ p) p = dt u₁ p - dt u₂ p := by
    intro p; simp only [dt]; rw [fderiv_fun_sub (hd₁ p) (hd₂ p)]; rfl
  have hdx : dx (fun p => u₁ p - u₂ p) = fun p => dx u₁ p - dx u₂ p := by
    funext p; simp only [dx]; rw [fderiv_fun_sub (hd₁ p) (hd₂ p)]; rfl
  have hdxx : ∀ p, dx (dx (fun p => u₁ p - u₂ p)) p = dx (dx u₁) p - dx (dx u₂) p := by
    intro p; rw [hdx]
    show fderiv ℝ (fun p => dx u₁ p - dx u₂ p) p (1, 0) =
      fderiv ℝ (dx u₁) p (1, 0) - fderiv ℝ (dx u₂) p (1, 0)
    rw [fderiv_fun_sub (hdx₁ p) (hdx₂ p)]; rfl
  have := heat_zero_of_zero_data hν hℓ hw (fun t ht x hx => by
      rw [hdt, hdxx, hpde₁ t ht x hx, hpde₂ t ht x hx]; ring)
    (fun t ht => ⟨by rw [(hbc t ht).1, sub_self], by rw [(hbc t ht).2, sub_self]⟩)
    (fun x hx => by rw [hic x hx, sub_self])
  intro t ht x hx
  exact sub_eq_zero.mp (this t ht x hx)

/-! ## Wave equation: energy conservation -/

/-- **Energy conservation** for `u_tt = c² u_xx` on `[0, ℓ]` with zero Dirichlet data:
`E(t) = ½∫₀^ℓ (u_t² + c² u_x²)` has zero derivative. -/
@[powerlib_foundation] theorem wave_energy_conserved {c ℓ : ℝ} (hu : ContDiff ℝ 2 u)
    (hpde : ∀ t, ∀ x ∈ uIcc 0 ℓ, dt (dt u) (x, t) = c ^ 2 * dx (dx u) (x, t))
    (hbc : ∀ t, u (0, t) = 0 ∧ u (ℓ, t) = 0) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in (0 : ℝ)..ℓ, (dt u (x, s) ^ 2 + c ^ 2 * dx u (x, s) ^ 2) / 2) 0 t := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdtd := differentiable_dt hu
  have hdxd := differentiable_dx hu
  -- derivative under the integral
  have hderiv := hasDerivAt_integral_param (G := fun p => (dt u p ^ 2 + c ^ 2 * dx u p ^ 2) / 2)
    (Gt := fun p => dt u p * dt (dt u) p + c ^ 2 * (dx u p * dt (dx u) p)) 0 ℓ
    ((((continuous_dt hu).pow 2).add (continuous_const.mul ((continuous_dx hu).pow 2))).div_const 2)
    (((continuous_dt hu).mul (continuous_dtdt hu)).add
      (continuous_const.mul ((continuous_dx hu).mul (continuous_dtdx hu))))
    (fun x τ => by
      have h1 := (hasDerivAt_pow 2 (dt u (x, τ))).comp τ (hasDerivAt_t_line hdtd x τ)
      have h2 := (hasDerivAt_pow 2 (dx u (x, τ))).comp τ (hasDerivAt_t_line hdxd x τ)
      have := ((h1.add (h2.const_mul (c ^ 2))).div_const 2)
      exact this.congr_deriv (by push_cast; ring)) t
  convert hderiv using 1
  -- `∫ (u_t u_tt + c² u_x u_xt) = c² [u_t u_x]₀^ℓ = 0`
  have hdtx : ∀ p, dt (dx u) p = dx (dt u) p := fun p => (dx_dt_comm hu p).symm
  have hcongr : ∫ x in (0 : ℝ)..ℓ, (dt u (x, t) * dt (dt u) (x, t) +
      c ^ 2 * (dx u (x, t) * dt (dx u) (x, t))) =
      ∫ x in (0 : ℝ)..ℓ, c ^ 2 * (dt u (x, t) * dx (dx u) (x, t) + dx (dt u) (x, t) * dx u (x, t)) :=
    integral_congr fun x hx => by rw [hpde t x hx, hdtx]; ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  -- the integrand is the `x`-derivative of `u_t u_x`
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := ℓ)
    (f := fun x => dt u (x, t) * dx u (x, t))
    (f' := fun x => dx (dt u) (x, t) * dx u (x, t) + dt u (x, t) * dx (dx u) (x, t))
    (fun x _ => (hasDerivAt_x_line hdtd x t).mul (hasDerivAt_x_line hdxd x t))
    ((((continuous_second hu (1, 0) (0, 1)).comp (by fun_prop)).mul
      ((continuous_dx hu).comp (by fun_prop))).add
      (((continuous_dt hu).comp (by fun_prop)).mul
      ((continuous_dxdx hu).comp (by fun_prop))) |>.intervalIntegrable 0 ℓ)
  have hcomm : (∫ x in (0 : ℝ)..ℓ, (dt u (x, t) * dx (dx u) (x, t) + dx (dt u) (x, t) * dx u (x, t))) =
      ∫ x in (0 : ℝ)..ℓ, (dx (dt u) (x, t) * dx u (x, t) + dt u (x, t) * dx (dx u) (x, t)) :=
    integral_congr fun x _ => by ring
  -- boundary values of `u_t` vanish because `u(0,·) = u(ℓ,·) = 0`
  have hut0 : dt u (0, t) = 0 := by
    have h := hasDerivAt_t_line hd 0 t
    have hz : (fun s => u (0, s)) = fun _ => 0 := funext fun s => (hbc s).1
    rw [hz] at h
    exact h.unique (hasDerivAt_const t 0)
  have hutℓ : dt u (ℓ, t) = 0 := by
    have h := hasDerivAt_t_line hd ℓ t
    have hz : (fun s => u (ℓ, s)) = fun _ => 0 := funext fun s => (hbc s).2
    rw [hz] at h
    exact h.unique (hasDerivAt_const t 0)
  rw [hcomm, hftc]
  simp [hut0, hutℓ]

end powerlib.PDE
