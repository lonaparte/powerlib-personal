import theorem.Dynamics.LipschitzFlow
import theorem.PhasePlane.Planar
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The planar return map and periodic orbits in an annulus

A planar field that turns at a definite angle speed on an annulus and whose Lyapunov function
increases on the inner band and decreases on the outer band has a periodic orbit in between:
the first return to the half-axis `{u₁ = 0, u₀ > 0}` is a continuous map of the starting radius,
and the intermediate value theorem gives a fixed point.

Scope.
* Autonomous continuous-time ODE `u̇ = f(u)` on `State 2 = EuclideanSpace ℝ (Fin 2)`; no input,
  delay or time variation. Forward solutions are those of a globally Lipschitz field
  (`Dynamics.forwardSolution`, `theorem/Dynamics/LipschitzFlow.lean`); a field Lipschitz only on
  a disc is first extended (`exists_lipschitzWith_eqOn`). Periodic orbits are written out in the
  statements, as in `theorem/NormalForm/Hopf.lean`: a curve `γ : ℝ → State 2` with
  `∀ t, HasDerivAt γ (f (γ t)) t`, `γ (t + T) = γ t`, `T > 0`, and `∃ t, γ t ≠ γ 0`.
* The hypotheses are bounds on the field and on a differentiable `V` on an annulus
  `s₁/Λ ≤ ‖u‖ ≤ s₂Λ`, `Λ = e^{4πβ/c}` (`bandFactor`): angle speed `u₀f₁ − u₁f₀ ≥ c‖u‖²`
  (`angNum`), radial rate `|u₀f₀ + u₁f₁| ≤ β‖u‖²` (`radNum`), `V` increasing along the first
  axis and the sign of `σ V̇` opposite on the inner and outer bands. No Poincaré–Bendixson theory
  is used: the fixed point comes from the intermediate value theorem.
* Generic foundation, independent of any model; no model family is defined.

Source: Guckenheimer–Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of
Vector Fields* (1983), §1.8 and §3.4 (the return map of a weak focus and the annulus argument
for the Hopf cycle); Hirsch–Smale–Devaney, *Differential Equations, Dynamical Systems, and an
Introduction to Chaos* (2nd ed.), §10.3 (local sections and the first-return map); Kuznetsov,
*Elements of Applied Bifurcation Theory* (3rd ed.), §3.4.

Results.
* `polar_return`: along a solution from `(s, 0)`, `s > 0`, that avoids a disc, the angle integral
  `Θ(T) = ∫₀ᵀ (φ₀f₁ − φ₁f₀)/‖φ‖² = 2π` puts `φ(T)` on the positive first axis (the complex
  form `z e^{−(k + iΘ)}` is constant).
* `hasDerivWithinAt_normSq`, `norm_bounds_of_radNum`: `(‖φ‖²)' = 2 radNum`, and the radial bound
  confines a solution between `s e^{−2βt}` and `s e^{2βt}` (barrier comparison).
* `continuousOn_root`: the root `τ(s)` of a jointly continuous, strictly increasing
  `Θ(s, ·) = v` is continuous; `hasDerivAt_forwardSolution`; `sign_sub_of_lie`.
* `exists_periodicOrbit_of_return` (any Banach space): a return `φ_T x = x`, `T > 0`, `f x ≠ 0`,
  gives a nonconstant `T`-periodic solution defined for all time.
* `exists_return_fixed`: under the annulus hypotheses the return time is continuous, the return
  map `P` is continuous, `σ(P(s₁) − s₁) > 0 > σ(P(s₂) − s₂)`, and `P` has a fixed point
  `s ∈ (s₁, s₂)` with return time in `(0, 2π/c]`.
* `exists_periodicOrbit_of_annulus`: for a field Lipschitz on a disc containing the annulus, a
  nonconstant periodic orbit through `(s, 0)`, `s₁ < s < s₂`, of period at most `2π/c`, inside
  the annulus.
-/

noncomputable section
namespace powerlib.Dynamics.PlanarReturn
open Set Filter Topology NNReal
open Complex (I exp_add)
open powerlib.PhasePlane (mk mk_apply_zero mk_apply_one)

/-- The angular numerator `u₀ f₁(u) − u₁ f₀(u)` of a planar field. -/
def angNum (f : State 2 → State 2) (u : State 2) : ℝ := u 0 * f u 1 - u 1 * f u 0

/-- The radial numerator `u₀ f₀(u) + u₁ f₁(u)` of a planar field. -/
def radNum (f : State 2 → State 2) (u : State 2) : ℝ := u 0 * f u 0 + u 1 * f u 1

/-- **The polar relation along a planar solution.** Let `φ` be continuous, start at `(s, 0)`,
`s > 0`, solve `φ̇ = f(φ)` on `[0, T)` (right derivatives) and stay outside the disc of radius
`r > 0` on `[0, T]`. If the angle integral `Θ(T) = ∫₀ᵀ (φ₀ f₁ − φ₁ f₀)/‖φ‖²` equals `2π`, then
`φ(T)` lies on the positive first axis. -/
@[tmio T, powerlib_foundation] theorem polar_return {f : State 2 → State 2} (hfc : Continuous f)
    {φ : ℝ → State 2} (hφc : Continuous φ) {s r T : ℝ} (hs : 0 < s) (hr : 0 < r) (hT : 0 ≤ T)
    (h0 : φ 0 = mk s 0)
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (f (φ t)) (Ici t) t)
    (hrφ : ∀ t ∈ Icc 0 T, r ≤ ‖φ t‖)
    (hΘ : ∫ τ in (0 : ℝ)..T, angNum f (φ τ) / max (‖φ τ‖ ^ 2) (r ^ 2) = 2 * Real.pi) :
    φ T 1 = 0 ∧ 0 < φ T 0 := by
  set ang : ℝ → ℝ := fun τ => angNum f (φ τ) / max (‖φ τ‖ ^ 2) (r ^ 2) with hang
  set rad : ℝ → ℝ := fun τ => radNum f (φ τ) / max (‖φ τ‖ ^ 2) (r ^ 2) with hrad
  have hden : ∀ τ, 0 < max (‖φ τ‖ ^ 2) (r ^ 2) := fun τ => lt_max_of_lt_right (by positivity)
  have hcang : Continuous ang := by
    refine Continuous.div ?_ ?_ (fun τ => (hden τ).ne')
    · unfold angNum
      fun_prop
    · fun_prop
  have hcrad : Continuous rad := by
    refine Continuous.div ?_ ?_ (fun τ => (hden τ).ne')
    · unfold radNum
      fun_prop
    · fun_prop
  set Θ : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, ang τ with hΘdef
  set k : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, rad τ with hkdef
  have hΘd : ∀ t, HasDerivAt Θ (ang t) t := fun t =>
    (hcang.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hkd : ∀ t, HasDerivAt k (rad t) t := fun t =>
    (hcrad.integral_hasStrictDerivAt 0 t).hasDerivAt
  set z : ℝ → ℂ := fun t => ((φ t 0 : ℝ) : ℂ) + ((φ t 1 : ℝ) : ℂ) * I with hz
  set e : ℝ → ℂ := fun t => Complex.exp (-(((k t : ℝ) : ℂ) + ((Θ t : ℝ) : ℂ) * I)) with he
  have hcz : Continuous z := by
    have h0 : Continuous fun t => φ t 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.comp hφc
    have h1 : Continuous fun t => φ t 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.comp hφc
    exact (Complex.continuous_ofReal.comp h0).add
      ((Complex.continuous_ofReal.comp h1).mul continuous_const)
  have hed : ∀ t, HasDerivAt e (e t * (-(((rad t : ℝ) : ℂ) + ((ang t : ℝ) : ℂ) * I))) t := by
    intro t
    have h := (((hkd t).ofReal_comp).add (((hΘd t).ofReal_comp).mul_const I)).neg.cexp
    convert h using 1
  have hzd : ∀ t ∈ Ico 0 T, HasDerivWithinAt z
      (((f (φ t) 0 : ℝ) : ℂ) + ((f (φ t) 1 : ℝ) : ℂ) * I) (Ici t) t := by
    intro t ht
    have h0 : HasDerivWithinAt (fun t => φ t 0) (f (φ t) 0) (Ici t) t := by
      exact ((EuclideanSpace.proj (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivWithinAt
        t (hφ t ht)
    have h1 : HasDerivWithinAt (fun t => φ t 1) (f (φ t) 1) (Ici t) t := by
      exact ((EuclideanSpace.proj (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivWithinAt
        t (hφ t ht)
    exact h0.ofReal_comp.add (h1.ofReal_comp.mul_const I)
  -- the product `w = z e` is constant on `[0, T]`
  have hwd : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t => z t * e t) 0 (Ici t) t := by
    intro t ht
    have h := (hzd t ht).mul (hed t).hasDerivWithinAt
    convert h using 1
    have hn : ‖φ t‖ ^ 2 = φ t 0 ^ 2 + φ t 1 ^ 2 := PhasePlane.norm_sq_eq (φ t)
    have hmax : max (‖φ t‖ ^ 2) (r ^ 2) = ‖φ t‖ ^ 2 := by
      apply max_eq_left
      have := hrφ t (Ico_subset_Icc_self ht)
      nlinarith
    have hpos : 0 < φ t 0 ^ 2 + φ t 1 ^ 2 := by rw [← hn, ← hmax]; exact hden t
    have hmax' : max (‖φ t‖ ^ 2) (r ^ 2) = φ t 0 ^ 2 + φ t 1 ^ 2 := by rw [hmax, hn]
    have key : ((f (φ t) 0 : ℝ) : ℂ) + ((f (φ t) 1 : ℝ) : ℂ) * I =
        z t * (((rad t : ℝ) : ℂ) + ((ang t : ℝ) : ℂ) * I) := by
      have e1 : φ t 0 * rad t - φ t 1 * ang t = f (φ t) 0 := by
        simp only [hrad, hang, hmax', radNum, angNum]
        field_simp
        ring
      have e2 : φ t 0 * ang t + φ t 1 * rad t = f (φ t) 1 := by
        simp only [hrad, hang, hmax', radNum, angNum]
        field_simp
        ring
      apply Complex.ext
      · simp only [hz, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
        linear_combination -e1
      · simp only [hz, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
        linear_combination -e2
    rw [key]
    ring
  have hwc : ContinuousOn (fun t => z t * e t) (Icc 0 T) := by
    refine (hcz.mul ?_).continuousOn
    exact continuous_iff_continuousAt.mpr fun t => (hed t).continuousAt
  have hconst := constant_of_has_deriv_right_zero hwc hwd T ⟨hT, le_rfl⟩
  have hz0 : z 0 * e 0 = (s : ℂ) := by
    simp [hz, he, hΘdef, hkdef, h0]
  rw [hz0] at hconst
  -- `z(T) = s e^{k(T)} e^{iΘ(T)} = s e^{k(T)}`
  have hΘT : Θ T = 2 * Real.pi := hΘ
  have hzT : z T = ((s * Real.exp (k T) : ℝ) : ℂ) := by
    have he' : e T * Complex.exp (((k T : ℝ) : ℂ) + ((Θ T : ℝ) : ℂ) * I) = 1 := by
      rw [he]; simp only; rw [← Complex.exp_add]; simp
    calc z T = z T * e T * Complex.exp (((k T : ℝ) : ℂ) + ((Θ T : ℝ) : ℂ) * I) := by
          rw [mul_assoc, he', mul_one]
      _ = (s : ℂ) * Complex.exp (((k T : ℝ) : ℂ) + ((Θ T : ℝ) : ℂ) * I) := by rw [hconst]
      _ = ((s * Real.exp (k T) : ℝ) : ℂ) := by
          rw [Complex.exp_add, hΘT]
          push_cast
          rw [show (2 * (Real.pi : ℂ)) * I = 2 * Real.pi * I by ring, Complex.exp_two_pi_mul_I]
          ring
  have hre := congrArg Complex.re hzT
  have him := congrArg Complex.im hzT
  simp [hz] at hre him
  refine ⟨him, ?_⟩
  rw [hre]
  exact mul_pos hs (Real.exp_pos _)

/-- `‖φ‖²` along a solution has the right derivative `2 radNum`. -/
@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_normSq {f : State 2 → State 2}
    {φ : ℝ → State 2} {t : ℝ} (h : HasDerivWithinAt φ (f (φ t)) (Ici t) t) :
    HasDerivWithinAt (fun τ => ‖φ τ‖ ^ 2) (2 * radNum f (φ t)) (Ici t) t := by
  have hc := PhasePlane.hasDerivWithinAt_iff_components.mp h
  have h2 := (hc.1.pow 2).add (hc.2.pow 2)
  have he : (fun τ => ‖φ τ‖ ^ 2) = fun τ => φ τ 0 ^ 2 + φ τ 1 ^ 2 := by
    funext τ; exact PhasePlane.norm_sq_eq (φ τ)
  rw [he]
  convert h2 using 1
  simp only [radNum]
  push_cast
  ring

/-- **Confinement by the radial numerator.** If `|radNum f u| ≤ β‖u‖²` on the band
`rin ≤ ‖u‖ ≤ rout`, a solution starting at norm `s` stays between `s e^{−2βt}` and `s e^{2βt}`
as long as these stay in the band. -/
@[tmio T, powerlib_foundation] theorem norm_bounds_of_radNum {f : State 2 → State 2}
    {φ : ℝ → State 2} {T s β rin rout : ℝ} (hφc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (f (φ t)) (Ici t) t) (hs : 0 < s) (hβ : 0 < β)
    (h0 : ‖φ 0‖ = s) (hin : rin ≤ s * Real.exp (-(2 * β * T)))
    (hout : s * Real.exp (2 * β * T) ≤ rout)
    (hrad : ∀ u, rin ≤ ‖u‖ → ‖u‖ ≤ rout → |radNum f u| ≤ β * ‖u‖ ^ 2) :
    ∀ t ∈ Icc 0 T,
      s * Real.exp (-(2 * β * t)) ≤ ‖φ t‖ ∧ ‖φ t‖ ≤ s * Real.exp (2 * β * t) := by
  have hρc : ContinuousOn (fun τ => ‖φ τ‖ ^ 2) (Icc 0 T) := hφc.norm.pow 2
  have hρd := fun t ht => hasDerivWithinAt_normSq (hφ t ht)
  have hup : ∀ t ∈ Icc 0 T, ‖φ t‖ ^ 2 ≤ (s * Real.exp (2 * β * t)) ^ 2 := by
    refine image_le_of_deriv_right_lt_deriv_boundary' hρc hρd
      (B := fun t => (s * Real.exp (2 * β * t)) ^ 2)
      (B' := fun t => 4 * β * (s * Real.exp (2 * β * t)) ^ 2) ?_ ?_ ?_ ?_
    · simp [h0]
    · exact (Continuous.continuousOn (by fun_prop))
    · intro t _
      have h1 : HasDerivAt (fun t => 2 * β * t) (2 * β) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * β)
      have h2 := (h1.exp.const_mul s).fun_pow 2
      convert h2.hasDerivWithinAt using 1
      push_cast
      ring
    · intro t ht heq
      have h1 : 0 ≤ s * Real.exp (2 * β * t) := by positivity
      have hn : ‖φ t‖ = s * Real.exp (2 * β * t) :=
        (pow_left_inj₀ (norm_nonneg _) h1 two_ne_zero).mp heq
      have hT0 : 0 ≤ T := le_trans ht.1 ht.2.le
      have he1 : 1 ≤ Real.exp (2 * β * t) := Real.one_le_exp (by nlinarith [ht.1])
      have he2 : Real.exp (-(2 * β * T)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have he3 : Real.exp (2 * β * t) ≤ Real.exp (2 * β * T) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.2])
      have hr := hrad (φ t) (by rw [hn]; nlinarith) (by rw [hn]; nlinarith)
      have hr2 := (abs_le.mp hr).2
      rw [hn] at hr2
      have hpos : 0 < (s * Real.exp (2 * β * t)) ^ 2 := by positivity
      show 2 * radNum f (φ t) < 4 * β * (s * Real.exp (2 * β * t)) ^ 2
      nlinarith
  have hlow : ∀ t ∈ Icc 0 T, -(‖φ t‖ ^ 2) ≤ -(s * Real.exp (-(2 * β * t))) ^ 2 := by
    refine image_le_of_deriv_right_lt_deriv_boundary' hρc.neg (fun t ht => (hρd t ht).neg)
      (B := fun t => -(s * Real.exp (-(2 * β * t))) ^ 2)
      (B' := fun t => 4 * β * (s * Real.exp (-(2 * β * t))) ^ 2) ?_ ?_ ?_ ?_
    · simp [h0]
    · exact (Continuous.continuousOn (by fun_prop))
    · intro t _
      have h1 : HasDerivAt (fun t => -(2 * β * t)) (-(2 * β)) t := by
        simpa using ((hasDerivAt_id t).const_mul (-(2 * β)))
      have h2 := ((h1.exp.const_mul s).fun_pow 2).neg
      convert h2.hasDerivWithinAt using 1
      push_cast
      ring
    · intro t ht heq
      have h1 : 0 ≤ s * Real.exp (-(2 * β * t)) := by positivity
      have hn : ‖φ t‖ = s * Real.exp (-(2 * β * t)) :=
        (pow_left_inj₀ (norm_nonneg _) h1 two_ne_zero).mp (neg_inj.mp heq)
      have hT0 : 0 ≤ T := le_trans ht.1 ht.2.le
      have he1 : Real.exp (-(2 * β * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      have he2 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by nlinarith)
      have he3 : Real.exp (-(2 * β * T)) ≤ Real.exp (-(2 * β * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.2])
      have hr := hrad (φ t) (by rw [hn]; nlinarith) (by rw [hn]; nlinarith)
      have hr2 := (abs_le.mp hr).1
      rw [hn] at hr2
      have hpos : 0 < (s * Real.exp (-(2 * β * t))) ^ 2 := by positivity
      show -(2 * radNum f (φ t)) < 4 * β * (s * Real.exp (-(2 * β * t))) ^ 2
      nlinarith
  intro t ht
  have h1 : 0 ≤ s * Real.exp (2 * β * t) := by positivity
  have h2 : 0 ≤ s * Real.exp (-(2 * β * t)) := by positivity
  refine ⟨?_, ?_⟩
  · exact (pow_le_pow_iff_left₀ h2 (norm_nonneg _) two_ne_zero).mp (by linarith [hlow t ht])
  · exact (pow_le_pow_iff_left₀ (norm_nonneg _) h1 two_ne_zero).mp (hup t ht)

/-- **Continuity of a parametric root.** If `Θ` is jointly continuous, strictly increasing in
its second argument on `[0, T]` for every `s ∈ S`, and `τ(s) ∈ (0, T]` solves `Θ(s, τ(s)) = v`,
then `τ` is continuous on `S`. -/
@[tmio T, powerlib_foundation] theorem continuousOn_root {Θ : ℝ → ℝ → ℝ}
    (hΘ : Continuous fun p : ℝ × ℝ => Θ p.1 p.2) {S : Set ℝ} {T v : ℝ}
    (hmono : ∀ s ∈ S, StrictMonoOn (Θ s) (Icc 0 T)) {τ : ℝ → ℝ}
    (hτ : ∀ s ∈ S, τ s ∈ Ioc 0 T ∧ Θ s (τ s) = v) : ContinuousOn τ S := by
  intro s₀ hs₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨⟨h0, hT⟩, hv⟩ := hτ s₀ hs₀
  have hcs : ∀ a : ℝ, ContinuousAt (fun s => Θ s a) s₀ := fun a =>
    (hΘ.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hlow : ∃ δ > 0, ∀ s ∈ S, dist s s₀ < δ → τ s₀ - ε / 2 ≤ τ s := by
    by_cases ha : τ s₀ - ε / 2 ≤ 0
    · exact ⟨1, one_pos, fun s hs _ => le_trans ha (hτ s hs).1.1.le⟩
    · push Not at ha
      have hlt : Θ s₀ (τ s₀ - ε / 2) < v := by
        rw [← hv]; exact hmono s₀ hs₀ ⟨ha.le, by linarith⟩ ⟨h0.le, hT⟩ (by linarith)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hcs (τ s₀ - ε / 2))
        (v - Θ s₀ (τ s₀ - ε / 2)) (by linarith)
      refine ⟨δ, hδ, fun s hs hd => ?_⟩
      have h1 := hball hd
      rw [Real.dist_eq] at h1
      have h2 : Θ s (τ s₀ - ε / 2) < v := by linarith [(abs_lt.mp h1).2]
      by_contra hcon
      push Not at hcon
      have hTs := hτ s hs
      have h3 : Θ s (τ s) ≤ Θ s (τ s₀ - ε / 2) :=
        ((hmono s hs).le_iff_le ⟨hTs.1.1.le, hTs.1.2⟩ ⟨ha.le, by linarith⟩).mpr hcon.le
      linarith [hTs.2]
  have hup : ∃ δ > 0, ∀ s ∈ S, dist s s₀ < δ → τ s ≤ τ s₀ + ε / 2 := by
    by_cases hb : T ≤ τ s₀ + ε / 2
    · exact ⟨1, one_pos, fun s hs _ => le_trans (hτ s hs).1.2 hb⟩
    · push Not at hb
      have hgt : v < Θ s₀ (τ s₀ + ε / 2) := by
        rw [← hv]; exact hmono s₀ hs₀ ⟨h0.le, hT⟩ ⟨by linarith, hb.le⟩ (by linarith)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hcs (τ s₀ + ε / 2))
        (Θ s₀ (τ s₀ + ε / 2) - v) (by linarith)
      refine ⟨δ, hδ, fun s hs hd => ?_⟩
      have h1 := hball hd
      rw [Real.dist_eq] at h1
      have h2 : v < Θ s (τ s₀ + ε / 2) := by linarith [(abs_lt.mp h1).1]
      by_contra hcon
      push Not at hcon
      have hTs := hτ s hs
      have h3 : Θ s (τ s₀ + ε / 2) ≤ Θ s (τ s) :=
        ((hmono s hs).le_iff_le ⟨by linarith, hb.le⟩ ⟨hTs.1.1.le, hTs.1.2⟩).mpr hcon.le
      linarith [hTs.2]
  obtain ⟨δ₁, hδ₁, h₁⟩ := hlow
  obtain ⟨δ₂, hδ₂, h₂⟩ := hup
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hd => ?_⟩
  have a1 := h₁ s hs (lt_of_lt_of_le hd (min_le_left _ _))
  have a2 := h₂ s hs (lt_of_lt_of_le hd (min_le_right _ _))
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {K : ℝ≥0}

/-- The forward solution has the two-sided derivative `f(φ(t))` at every `t > 0`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_forwardSolution (hf : LipschitzWith K f)
    (x : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (forwardSolution hf x) (f (forwardSolution hf x t)) t :=
  (lipschitzFlow_solution hf x t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht)

/-- **A return gives a periodic orbit.** If the forward solution from `x` returns to `x` at a
time `T > 0` and `f x ≠ 0`, the `T`-periodic extension `γ` of `t ↦ φ_t x` is a nonconstant
`T`-periodic solution of `ẋ = f x` defined for all time, and each `γ t` is some `φ_τ x` with
`τ ∈ [0, T)`. -/
@[tmio T, powerlib_foundation] theorem exists_periodicOrbit_of_return (hf : LipschitzWith K f)
    {x : E} {T : ℝ} (hT : 0 < T) (hret : forwardSolution hf x T = x) (hx : f x ≠ 0) :
    ∃ γ : ℝ → E, (∀ t, HasDerivAt γ (f (γ t)) t) ∧ (∀ t, γ (t + T) = γ t) ∧
      (∃ t, γ t ≠ γ 0) ∧ γ 0 = x ∧ ∀ t, ∃ τ ∈ Ico 0 T, γ t = forwardSolution hf x τ := by
  have hper : ∀ t, 0 ≤ t → forwardSolution hf x (t + T) = forwardSolution hf x t :=
    fun t ht => by rw [forwardSolution_add hf x hT.le ht, hret]
  set φ := forwardSolution hf x with hφ
  have hperN : ∀ n : ℕ, ∀ t, 0 ≤ t → φ (t + n * T) = φ t := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ k ih =>
      intro t ht
      have hk : (0 : ℝ) ≤ t + k * T := by positivity
      rw [show t + ((k + 1 : ℕ) : ℝ) * T = t + k * T + T by push_cast; ring, hper _ hk, ih t ht]
  set γ : ℝ → E := fun t => φ (T * Int.fract (t / T)) with hγ
  have hfr : ∀ u, 0 ≤ u → φ u = γ u := by
    intro u hu
    have hfl : (0 : ℤ) ≤ ⌊u / T⌋ := Int.floor_nonneg.mpr (div_nonneg hu hT.le)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hfl
    have hdec : u = T * Int.fract (u / T) + (k : ℝ) * T := by
      have := Int.floor_add_fract (u / T)
      rw [hk] at this
      push_cast at this
      field_simp at this ⊢
      linarith
    have hnn : 0 ≤ T * Int.fract (u / T) := mul_nonneg hT.le (Int.fract_nonneg _)
    simp only [hγ]
    conv_lhs => rw [hdec]
    exact hperN k _ hnn
  have hshift : ∀ (n : ℕ) (t : ℝ), γ (t + n * T) = γ t := by
    intro n t
    simp only [hγ]
    rw [show (t + n * T) / T = t / T + n by field_simp, Int.fract_add_natCast]
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · intro t₀
    obtain ⟨n, hn⟩ := exists_nat_gt (-t₀ / T)
    have hpos : 0 < t₀ + n * T := by
      have := (div_lt_iff₀ hT).mp hn
      linarith
    have hev : γ =ᶠ[𝓝 t₀] fun t => φ (t + n * T) := by
      have : ∀ᶠ t in 𝓝 t₀, 0 < t + n * T :=
        (continuous_id.add continuous_const).continuousAt.eventually (lt_mem_nhds hpos)
      filter_upwards [this] with t ht
      rw [hfr _ ht.le, hshift]
    have hd := (hasDerivAt_forwardSolution hf x hpos).comp_add_const t₀ (n * T)
    rw [← hφ, hfr _ hpos.le, hshift] at hd
    exact hd.congr_of_eventuallyEq hev
  · intro t
    have := hshift 1 t
    simpa using this
  · by_contra hcon
    push Not at hcon
    have hc : HasDerivAt γ 0 0 := by
      have : γ = fun _ => γ 0 := funext hcon
      rw [this]; exact hasDerivAt_const _ _
    have h1 : HasDerivAt φ (f (φ 1)) 1 := hasDerivAt_forwardSolution hf x one_pos
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (0 : ℝ) < 0 + n * T := ⟨1, by simpa using hT⟩
    have hd := (hasDerivAt_forwardSolution hf x hn).comp_add_const 0 (n * T)
    have hev : γ =ᶠ[𝓝 0] fun t => φ (t + n * T) := by
      have : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t + n * T :=
        (continuous_id.add continuous_const).continuousAt.eventually (lt_mem_nhds hn)
      filter_upwards [this] with t ht
      rw [hfr _ ht.le, hshift]
    have hd' := hd.congr_of_eventuallyEq hev
    rw [← hφ, hfr _ hn.le, hshift] at hd'
    have h0 : γ 0 = x := by simp [hγ, hφ, forwardSolution_zero]
    rw [h0] at hd'
    exact hx (hd'.unique hc)
  · simp [hγ, hφ, forwardSolution_zero]
  · intro t
    exact ⟨T * Int.fract (t / T), ⟨mul_nonneg hT.le (Int.fract_nonneg _),
      by nlinarith [Int.fract_lt_one (t / T)]⟩, rfl⟩

end Flow

/-- A field Lipschitz on a set of the plane agrees there with a globally Lipschitz field. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitzWith_eqOn {f : State 2 → State 2}
    {K : ℝ≥0} {s : Set (State 2)} (hf : LipschitzOnWith K f s) :
    ∃ K' : ℝ≥0, ∃ g : State 2 → State 2, LipschitzWith K' g ∧ EqOn f g s := by
  have h1 : LipschitzOnWith (1 * K) (fun x => WithLp.ofLp (f x)) s :=
    (PiLp.lipschitzWith_ofLp 2 _).comp_lipschitzOnWith hf
  obtain ⟨g, hg, hfg⟩ := h1.extend_pi
  refine ⟨_, fun x => WithLp.toLp 2 (g x), (PiLp.lipschitzWith_toLp 2 _).comp hg, ?_⟩
  intro x hx
  have := hfg hx
  simp only at this
  show f x = WithLp.toLp 2 (g x)
  rw [← this]

/-- The band factor `Λ = e^{4πβ/c}`: over one turn `2π/c` of an angle speed at least `c`, a radial
rate `|ṙ/r| ≤ β` changes the norm by a factor at most `Λ`. -/
def bandFactor (β c : ℝ) : ℝ := Real.exp (4 * Real.pi * β / c)

section Return

variable {f : State 2 → State 2} {K : ℝ≥0}

/-- Along a forward solution on `[0, T]`, `T > 0`, if `σ V̇ > 0` then `σ (V(φ_T) − V(φ_0)) > 0`. -/
@[tmio T, powerlib_foundation] theorem sign_sub_of_lie (hf : LipschitzWith K f) (x : State 2)
    {T : ℝ} (hT : 0 < T) {V : State 2 → ℝ} (hV : Differentiable ℝ V) {σ : ℝ}
    (hσ : ∀ t ∈ Icc 0 T, 0 < σ * fderiv ℝ V (forwardSolution hf x t)
      (f (forwardSolution hf x t))) :
    0 < σ * (V (forwardSolution hf x T) - V (forwardSolution hf x 0)) := by
  have hc : ContinuousOn (fun t => σ * V (forwardSolution hf x t)) (Icc 0 T) :=
    continuousOn_const.mul (hV.continuous.comp_continuousOn
      ((lipschitzFlow_solution hf x).continuousOn.mono Icc_subset_Ici_self))
  have hm : StrictMonoOn (fun t => σ * V (forwardSolution hf x t)) (Icc 0 T) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 T) hc fun t ht => ?_
    rw [interior_Icc] at ht
    have hd : HasDerivAt (fun t => σ * V (forwardSolution hf x t))
        (σ * fderiv ℝ V (forwardSolution hf x t) (f (forwardSolution hf x t))) t :=
      ((hV _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_forwardSolution hf x ht.1)).const_mul σ
    rw [hd.deriv]
    exact hσ t (Ioo_subset_Icc_self ht)
  have := hm ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hT
  simp only at this
  linarith

/-- **The return map has a fixed point.** Let `f` be globally Lipschitz on the plane and, on the
band `s₁/Λ ≤ ‖u‖ ≤ s₂Λ` (`Λ = bandFactor β c`), let the angle speed be at least `c > 0`
(`c‖u‖² ≤ u₀f₁ − u₁f₀`) and the radial rate at most `β > 0` (`|u₀f₀ + u₁f₁| ≤ β‖u‖²`). Let `V`
be differentiable and strictly increasing along the positive first axis on the band, with
`σ V̇ > 0` on the inner band `[s₁/Λ, s₁Λ]` and `σ V̇ < 0` on the outer band `[s₂/Λ, s₂Λ]`. Then for
some `s ∈ (s₁, s₂)` the solution from `(s, 0)` returns to `(s, 0)` at a time `T ∈ (0, 2π/c]`,
staying in the band. Proof: the return time to the section `{u₁ = 0, u₀ > 0}` is the root of the
angle integral (`polar_return`), continuous in `s` (`continuousOn_root`), so the return map
`P` is continuous; `V` gives `σ(P(s₁) − s₁) > 0 > σ(P(s₂) − s₂)`; the intermediate value
theorem. -/
@[tmio T, powerlib_foundation] theorem exists_return_fixed (hf : LipschitzWith K f)
    {c β s₁ s₂ : ℝ} (hc : 0 < c) (hβ : 0 < β) (hs₁ : 0 < s₁) (hs : s₁ < s₂)
    (hang : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      c * ‖u‖ ^ 2 ≤ angNum f u)
    (hrad : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      |radNum f u| ≤ β * ‖u‖ ^ 2)
    {V : State 2 → ℝ} (hV : Differentiable ℝ V)
    (hVm : StrictMonoOn (fun s => V (mk s 0)) (Icc (s₁ / bandFactor β c) (s₂ * bandFactor β c)))
    {σ : ℝ}
    (hin : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₁ * bandFactor β c →
      0 < σ * fderiv ℝ V u (f u))
    (hout : ∀ u, s₂ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      σ * fderiv ℝ V u (f u) < 0) :
    ∃ s ∈ Ioo s₁ s₂, ∃ T, 0 < T ∧ T ≤ 2 * Real.pi / c ∧
      forwardSolution hf (mk s 0) T = mk s 0 ∧
      ∀ t ∈ Icc 0 T, s₁ / bandFactor β c ≤ ‖forwardSolution hf (mk s 0) t‖ ∧
        ‖forwardSolution hf (mk s 0) t‖ ≤ s₂ * bandFactor β c := by
  set Λ := bandFactor β c with hΛdef
  set Tm := 2 * Real.pi / c with hTm
  have hTm0 : 0 < Tm := by positivity
  have hΛ : Λ = Real.exp (2 * β * Tm) := by
    rw [hΛdef, bandFactor, hTm]; congr 1; field_simp; norm_num
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact Real.one_le_exp (by positivity)
  have hΛ0 : 0 < Λ := by linarith
  have hΛinv : Real.exp (-(2 * β * Tm)) = Λ⁻¹ := by rw [hΛ, Real.exp_neg]
  have hfc : Continuous f := hf.continuous
  -- confinement of the solutions from the axis on `[0, Tm]`
  have hconf : ∀ s ∈ Icc s₁ s₂, ∀ t ∈ Icc 0 Tm,
      s / Λ ≤ ‖forwardSolution hf (mk s 0) t‖ ∧ ‖forwardSolution hf (mk s 0) t‖ ≤ s * Λ := by
    intro s hs t ht
    have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
    have hn0 : ‖mk s 0‖ = s := by
      rw [PhasePlane.norm_mk]; simp [Real.sqrt_sq hs0.le]
    have hb := norm_bounds_of_radNum (f := f) (φ := forwardSolution hf (mk s 0)) (T := Tm)
      (rin := s₁ / Λ) (rout := s₂ * Λ)
      ((lipschitzFlow_solution hf _).continuousOn.mono Icc_subset_Ici_self)
      (fun t ht => ((lipschitzFlow_solution hf _) t ht.1).mono (Ici_subset_Ici.mpr ht.1))
      hs0 hβ (by rw [forwardSolution_zero]; exact hn0)
      (by rw [hΛinv, ← div_eq_mul_inv]; exact div_le_div_of_nonneg_right hs.1 hΛ0.le)
      (by rw [← hΛ]; exact mul_le_mul_of_nonneg_right hs.2 hΛ0.le) hrad t ht
    have e1 : Real.exp (-(2 * β * Tm)) ≤ Real.exp (-(2 * β * t)) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2])
    have e2 : Real.exp (2 * β * t) ≤ Real.exp (2 * β * Tm) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2])
    rw [hΛinv] at e1
    rw [← hΛ] at e2
    constructor
    · calc s / Λ = s * Λ⁻¹ := div_eq_mul_inv _ _
        _ ≤ s * Real.exp (-(2 * β * t)) := mul_le_mul_of_nonneg_left e1 hs0.le
        _ ≤ _ := hb.1
    · exact hb.2.trans (mul_le_mul_of_nonneg_left e2 hs0.le)
  have hband : ∀ s ∈ Icc s₁ s₂, ∀ t ∈ Icc 0 Tm,
      s₁ / Λ ≤ ‖forwardSolution hf (mk s 0) t‖ ∧ ‖forwardSolution hf (mk s 0) t‖ ≤ s₂ * Λ :=
    fun s hs t ht => ⟨le_trans (div_le_div_of_nonneg_right hs.1 hΛ0.le) (hconf s hs t ht).1,
      le_trans (hconf s hs t ht).2 (mul_le_mul_of_nonneg_right hs.2 hΛ0.le)⟩
  have hr0 : 0 < s₁ / Λ := div_pos hs₁ hΛ0
  -- the frozen flow and the angle integral
  set φ : ℝ → ℝ → State 2 := fun s t => forwardSolution hf (mk s 0) (max t 0) with hφ
  have hφc : Continuous fun p : ℝ × ℝ => φ p.1 p.2 := by
    have : (fun p : ℝ × ℝ => φ p.1 p.2) =
        fun p => lipschitzFlow hf (Real.toNNReal p.2) (mk p.1 0) := by
      funext p
      show forwardSolution hf (mk p.1 0) (max p.2 0) =
        forwardSolution hf (mk p.1 0) (Real.toNNReal p.2 : ℝ)
      rw [Real.coe_toNNReal']
    rw [this]
    exact (lipschitzFlow hf).continuous (continuous_real_toNNReal.comp continuous_snd)
      (by unfold PhasePlane.mk; fun_prop)
  have hφeq : ∀ s t, 0 ≤ t → φ s t = forwardSolution hf (mk s 0) t := fun s t ht => by
    simp only [hφ, max_eq_left ht]
  set ang : ℝ → ℝ → ℝ := fun s τ =>
    angNum f (φ s τ) / max (‖φ s τ‖ ^ 2) ((s₁ / Λ) ^ 2) with hang_def
  have hden : ∀ s τ, 0 < max (‖φ s τ‖ ^ 2) ((s₁ / Λ) ^ 2) :=
    fun s τ => lt_max_of_lt_right (by positivity)
  have hangc : Continuous fun p : ℝ × ℝ => ang p.1 p.2 := by
    refine Continuous.div ?_ ?_ (fun p => (hden p.1 p.2).ne')
    · unfold angNum
      have h0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.comp hφc
      have h1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.comp hφc
      have h0' := (EuclideanSpace.proj (0 : Fin 2)).continuous.comp (hfc.comp hφc)
      have h1' := (EuclideanSpace.proj (1 : Fin 2)).continuous.comp (hfc.comp hφc)
      exact (h0.mul h1').sub (h1.mul h0')
    · exact (hφc.norm.pow 2).max continuous_const
  have hang_ge : ∀ s ∈ Icc s₁ s₂, ∀ τ ∈ Icc 0 Tm, c ≤ ang s τ := by
    intro s hs τ hτ
    have hb := hband s hs τ hτ
    have hmax : max (‖forwardSolution hf (mk s 0) τ‖ ^ 2) ((s₁ / Λ) ^ 2) =
        ‖forwardSolution hf (mk s 0) τ‖ ^ 2 :=
      max_eq_left (pow_le_pow_left₀ hr0.le hb.1 2)
    have hpos : 0 < ‖forwardSolution hf (mk s 0) τ‖ ^ 2 := by
      have := lt_of_lt_of_le hr0 hb.1; positivity
    simp only [hang_def, hφeq s τ hτ.1, hmax]
    rw [le_div_iff₀ hpos]
    exact hang _ hb.1 hb.2
  set Θ : ℝ → ℝ → ℝ := fun s t => ∫ τ in (0 : ℝ)..t, ang s τ with hΘ_def
  have hΘc : Continuous fun p : ℝ × ℝ => Θ p.1 p.2 :=
    intervalIntegral.continuous_parametric_primitive_of_continuous (f := ang) hangc
  have hcang : ∀ s, Continuous (ang s) := fun s =>
    hangc.comp (continuous_const.prodMk continuous_id)
  have hΘd : ∀ s t, HasDerivAt (Θ s) (ang s t) t := fun s t =>
    ((hcang s).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hΘmono : ∀ s ∈ Icc s₁ s₂, StrictMonoOn (Θ s) (Icc 0 Tm) := by
    intro s hs
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 Tm)
      (fun t _ => (hΘd s t).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hΘd s t).deriv]
    exact lt_of_lt_of_le hc (hang_ge s hs t (Ioo_subset_Icc_self ht))
  have hΘ0 : ∀ s, Θ s 0 = 0 := fun s => by simp [hΘ_def]
  have hΘTm : ∀ s ∈ Icc s₁ s₂, 2 * Real.pi ≤ Θ s Tm := by
    intro s hs
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hTm0.le
      (continuous_const.intervalIntegrable 0 Tm) ((hcang s).intervalIntegrable 0 Tm)
      (hang_ge s hs)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    have : Tm * c = 2 * Real.pi := by rw [hTm]; field_simp
    simp only [hΘ_def]
    linarith
  -- the return time
  have hex : ∀ s ∈ Icc s₁ s₂, ∃ T, T ∈ Ioc 0 Tm ∧ Θ s T = 2 * Real.pi := by
    intro s hs
    obtain ⟨T, hT, hTv⟩ := intermediate_value_Icc hTm0.le
      (fun t _ => (hΘd s t).continuousAt.continuousWithinAt)
      (show 2 * Real.pi ∈ Icc (Θ s 0) (Θ s Tm) from ⟨by rw [hΘ0]; positivity, hΘTm s hs⟩)
    refine ⟨T, ⟨lt_of_le_of_ne hT.1 ?_, hT.2⟩, hTv⟩
    rintro rfl
    rw [hΘ0] at hTv
    linarith [Real.pi_pos]
  choose! τ hτ using hex
  have hτc : ContinuousOn τ (Icc s₁ s₂) := continuousOn_root hΘc hΘmono hτ
  -- the return lands on the positive axis
  have hland : ∀ s ∈ Icc s₁ s₂, φ s (τ s) 1 = 0 ∧ 0 < φ s (τ s) 0 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
    obtain ⟨⟨hτ0, hτT⟩, hτv⟩ := hτ s hs
    have hcs : Continuous (φ s) := hφc.comp (continuous_const.prodMk continuous_id)
    refine polar_return (φ := φ s) hfc hcs hs0 hr0 hτ0.le ?_ ?_ ?_ hτv
    · show φ s 0 = mk s 0
      rw [hφeq s 0 le_rfl, forwardSolution_zero]
    · intro t ht
      have h := ((lipschitzFlow_solution hf (mk s 0)) t ht.1).mono (Ici_subset_Ici.mpr ht.1)
      have h' := h.congr (fun y hy => hφeq s y (le_trans ht.1 hy)) (hφeq s t ht.1)
      rw [hφeq s t ht.1]
      exact h'
    · intro t ht
      rw [hφeq s t ht.1]
      exact (hband s hs t ⟨ht.1, ht.2.trans hτT⟩).1
  set P : ℝ → ℝ := fun s => φ s (τ s) 0 with hP
  have hPc : ContinuousOn P (Icc s₁ s₂) := by
    have : ContinuousOn (fun s => φ s (τ s)) (Icc s₁ s₂) :=
      hφc.comp_continuousOn (continuousOn_id.prodMk hτc)
    exact (EuclideanSpace.proj (0 : Fin 2)).continuous.comp_continuousOn this
  have hPmk : ∀ s ∈ Icc s₁ s₂, forwardSolution hf (mk s 0) (τ s) = mk (P s) 0 := by
    intro s hs
    rw [← hφeq s (τ s) (hτ s hs).1.1.le, PhasePlane.ext_iff']
    exact ⟨rfl, (hland s hs).1⟩
  have hPband : ∀ s ∈ Icc s₁ s₂, s / Λ ≤ P s ∧ P s ≤ s * Λ := by
    intro s hs
    have h := hconf s hs (τ s) ⟨(hτ s hs).1.1.le, (hτ s hs).1.2⟩
    rw [hPmk s hs, PhasePlane.norm_mk] at h
    have hP0 : 0 < P s := (hland s hs).2
    simpa [Real.sqrt_sq hP0.le] using h
  -- the sign of `P(s) − s` at the two ends
  have hend : ∀ s ∈ Icc s₁ s₂,
      (∀ t ∈ Icc 0 (τ s), 0 < σ * fderiv ℝ V (forwardSolution hf (mk s 0) t)
        (f (forwardSolution hf (mk s 0) t))) → 0 < σ * (P s - s) := by
    intro s hs hσ
    have hV' := sign_sub_of_lie hf (mk s 0) (hτ s hs).1.1 hV hσ
    rw [hPmk s hs, forwardSolution_zero] at hV'
    have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
    have hmem : ∀ x, s / Λ ≤ x → x ≤ s * Λ →
        x ∈ Icc (s₁ / Λ) (s₂ * Λ) := fun x h1 h2 =>
      ⟨le_trans (div_le_div_of_nonneg_right hs.1 hΛ0.le) h1,
        le_trans h2 (mul_le_mul_of_nonneg_right hs.2 hΛ0.le)⟩
    have hsm : s ∈ Icc (s₁ / Λ) (s₂ * Λ) :=
      hmem s (div_le_self hs0.le hΛ1) (le_mul_of_one_le_right hs0.le hΛ1)
    have hPm := hmem (P s) (hPband s hs).1 (hPband s hs).2
    rcases lt_trichotomy σ 0 with hσn | hσ0 | hσp
    · have : V (mk (P s) 0) < V (mk s 0) := by nlinarith
      have := (hVm.lt_iff_lt hPm hsm).mp this
      nlinarith
    · simp [hσ0] at hV'
    · have : V (mk s 0) < V (mk (P s) 0) := by nlinarith
      have := (hVm.lt_iff_lt hsm hPm).mp this
      nlinarith
  have hs₁m : s₁ ∈ Icc s₁ s₂ := ⟨le_rfl, hs.le⟩
  have hs₂m : s₂ ∈ Icc s₁ s₂ := ⟨hs.le, le_rfl⟩
  have h₁ : 0 < σ * (P s₁ - s₁) := by
    refine hend s₁ hs₁m fun t ht => hin _ ?_ ?_
    · exact (hconf s₁ hs₁m t ⟨ht.1, ht.2.trans (hτ s₁ hs₁m).1.2⟩).1
    · exact (hconf s₁ hs₁m t ⟨ht.1, ht.2.trans (hτ s₁ hs₁m).1.2⟩).2
  have h₂ : σ * (P s₂ - s₂) < 0 := by
    have hend' : ∀ s ∈ Icc s₁ s₂,
        (∀ t ∈ Icc 0 (τ s), 0 < -σ * fderiv ℝ V (forwardSolution hf (mk s 0) t)
          (f (forwardSolution hf (mk s 0) t))) → 0 < -σ * (P s - s) := by
      intro s hs hσ
      have hV' := sign_sub_of_lie hf (mk s 0) (hτ s hs).1.1 hV hσ
      rw [hPmk s hs, forwardSolution_zero] at hV'
      have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
      have hmem : ∀ x, s / Λ ≤ x → x ≤ s * Λ →
          x ∈ Icc (s₁ / Λ) (s₂ * Λ) := fun x h1 h2 =>
        ⟨le_trans (div_le_div_of_nonneg_right hs.1 hΛ0.le) h1,
          le_trans h2 (mul_le_mul_of_nonneg_right hs.2 hΛ0.le)⟩
      have hsm : s ∈ Icc (s₁ / Λ) (s₂ * Λ) :=
        hmem s (div_le_self hs0.le hΛ1) (le_mul_of_one_le_right hs0.le hΛ1)
      have hPm := hmem (P s) (hPband s hs).1 (hPband s hs).2
      rcases lt_trichotomy σ 0 with hσn | hσ0 | hσp
      · have : V (mk s 0) < V (mk (P s) 0) := by nlinarith
        have := (hVm.lt_iff_lt hsm hPm).mp this
        nlinarith
      · simp [hσ0] at hV'
      · have : V (mk (P s) 0) < V (mk s 0) := by nlinarith
        have := (hVm.lt_iff_lt hPm hsm).mp this
        nlinarith
    have := hend' s₂ hs₂m fun t ht => by
      have hb := hconf s₂ hs₂m t ⟨ht.1, ht.2.trans (hτ s₂ hs₂m).1.2⟩
      have := hout _ hb.1 hb.2
      linarith
    linarith
  -- the intermediate value theorem
  have hgc : ContinuousOn (fun s => σ * (P s - s)) (Icc s₁ s₂) :=
    continuousOn_const.mul (hPc.sub continuousOn_id)
  obtain ⟨s, hs', hz⟩ := intermediate_value_Icc' hs.le hgc
    (show (0 : ℝ) ∈ Icc (σ * (P s₂ - s₂)) (σ * (P s₁ - s₁)) from ⟨h₂.le, h₁.le⟩)
  have hσ : σ ≠ 0 := by rintro rfl; simp at h₁
  have hPs : P s = s := by
    have := (mul_eq_zero.mp hz).resolve_left hσ
    linarith
  have hne1 : s ≠ s₁ := by rintro rfl; rw [hPs] at h₁; simp at h₁
  have hne2 : s ≠ s₂ := by rintro rfl; rw [hPs] at h₂; simp at h₂
  refine ⟨s, ⟨lt_of_le_of_ne hs'.1 (Ne.symm hne1), lt_of_le_of_ne hs'.2 hne2⟩, τ s,
    (hτ s hs').1.1, (hτ s hs').1.2, by rw [hPmk s hs', hPs], fun t ht => ?_⟩
  exact hband s hs' t ⟨ht.1, ht.2.trans (hτ s hs').1.2⟩

/-- **A periodic orbit in an annulus** (the planar return-map theorem). Let `f` be Lipschitz on the
closed disc of radius `R ≥ s₂Λ` (`Λ = bandFactor β c`) and satisfy on the band
`s₁/Λ ≤ ‖u‖ ≤ s₂Λ` the angle bound `c‖u‖² ≤ u₀f₁ − u₁f₀` (`c > 0`) and the radial bound
`|u₀f₀ + u₁f₁| ≤ β‖u‖²` (`β > 0`); let `V` be differentiable, strictly increasing along the
positive first axis on the band, with `σ V̇ > 0` on the inner band `[s₁/Λ, s₁Λ]` and `σ V̇ < 0` on
the outer band `[s₂/Λ, s₂Λ]`. Then `ẋ = f x` has a nonconstant periodic solution `γ`, defined for
all time, through a point `(s, 0)` with `s₁ < s < s₂`, with period at most `2π/c`, inside the
band. -/
@[tmio T, powerlib_foundation] theorem exists_periodicOrbit_of_annulus {R : ℝ}
    (hf : LipschitzOnWith K f (Metric.closedBall 0 R)) {c β s₁ s₂ : ℝ} (hc : 0 < c)
    (hβ : 0 < β) (hs₁ : 0 < s₁) (hs : s₁ < s₂) (hR : s₂ * bandFactor β c ≤ R)
    (hang : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      c * ‖u‖ ^ 2 ≤ angNum f u)
    (hrad : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      |radNum f u| ≤ β * ‖u‖ ^ 2)
    {V : State 2 → ℝ} (hV : Differentiable ℝ V)
    (hVm : StrictMonoOn (fun s => V (mk s 0)) (Icc (s₁ / bandFactor β c) (s₂ * bandFactor β c)))
    {σ : ℝ}
    (hin : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₁ * bandFactor β c →
      0 < σ * fderiv ℝ V u (f u))
    (hout : ∀ u, s₂ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      σ * fderiv ℝ V u (f u) < 0) :
    ∃ γ : ℝ → State 2, ∃ T, 0 < T ∧ T ≤ 2 * Real.pi / c ∧ (∀ t, HasDerivAt γ (f (γ t)) t) ∧
      (∀ t, γ (t + T) = γ t) ∧ (∃ t, γ t ≠ γ 0) ∧ (∃ s ∈ Ioo s₁ s₂, γ 0 = mk s 0) ∧
      ∀ t, s₁ / bandFactor β c ≤ ‖γ t‖ ∧ ‖γ t‖ ≤ s₂ * bandFactor β c := by
  obtain ⟨K', g, hg, hfg⟩ := exists_lipschitzWith_eqOn hf
  have hΛ1 : 1 ≤ bandFactor β c := Real.one_le_exp (by positivity)
  have hΛ0 : 0 < bandFactor β c := by linarith
  have heq : ∀ u, ‖u‖ ≤ s₂ * bandFactor β c → f u = g u := fun u hu =>
    hfg (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith))
  have hs₁le : s₁ * bandFactor β c ≤ s₂ * bandFactor β c :=
    mul_le_mul_of_nonneg_right hs.le hΛ0.le
  have hang' : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      c * ‖u‖ ^ 2 ≤ angNum g u := fun u h1 h2 => by
    have := hang u h1 h2; simpa [angNum, heq u h2] using this
  have hrad' : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      |radNum g u| ≤ β * ‖u‖ ^ 2 := fun u h1 h2 => by
    have := hrad u h1 h2; simpa [radNum, heq u h2] using this
  have hin' : ∀ u, s₁ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₁ * bandFactor β c →
      0 < σ * fderiv ℝ V u (g u) := fun u h1 h2 => by
    rw [← heq u (h2.trans hs₁le)]; exact hin u h1 h2
  have hout' : ∀ u, s₂ / bandFactor β c ≤ ‖u‖ → ‖u‖ ≤ s₂ * bandFactor β c →
      σ * fderiv ℝ V u (g u) < 0 := fun u h1 h2 => by
    rw [← heq u h2]; exact hout u h1 h2
  obtain ⟨s, hs', T, hT0, hTle, hret, hband⟩ :=
    exists_return_fixed hg hc hβ hs₁ hs hang' hrad' hV hVm hin' hout'
  have hs0 : 0 < s := hs₁.trans hs'.1
  have hn : ‖mk s 0‖ = s := by rw [PhasePlane.norm_mk]; simp [Real.sqrt_sq hs0.le]
  have hgx : g (mk s 0) ≠ 0 := by
    intro h0
    have h1 : s₁ / bandFactor β c ≤ ‖mk s 0‖ := by
      rw [hn]; exact le_trans (div_le_self hs₁.le hΛ1) hs'.1.le
    have h2 : ‖mk s 0‖ ≤ s₂ * bandFactor β c := by
      rw [hn]; exact le_trans hs'.2.le (le_mul_of_one_le_right (hs₁.trans hs).le hΛ1)
    have := hang' _ h1 h2
    rw [angNum, h0, hn] at this
    simp at this
    nlinarith [sq_pos_of_pos hs0]
  obtain ⟨γ, hγd, hγT, hγnc, hγ0, hγr⟩ := exists_periodicOrbit_of_return hg hT0 hret hgx
  have hγband : ∀ t, s₁ / bandFactor β c ≤ ‖γ t‖ ∧ ‖γ t‖ ≤ s₂ * bandFactor β c := by
    intro t
    obtain ⟨τ, hτ, hγτ⟩ := hγr t
    rw [hγτ]
    exact hband τ ⟨hτ.1, hτ.2.le⟩
  refine ⟨γ, T, hT0, hTle, fun t => ?_, hγT, hγnc, ⟨s, hs', hγ0⟩, hγband⟩
  rw [heq _ (hγband t).2]
  exact hγd t

end Return

end powerlib.Dynamics.PlanarReturn
