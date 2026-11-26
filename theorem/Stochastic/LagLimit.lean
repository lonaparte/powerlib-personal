import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The fast first-order lag tracks its input

The first-order lag `ẋ = −β (x − N)` with a continuous input `N`: its variation-of-constants
solution, uniqueness, and the limit `x_β(t) → N(t)` as `β → ∞` for every `t > 0` (the kernel
`β e^{−βs}` is an approximate identity), together with the frequency-domain statement
`β/(β + s) → 1`.

Scope.
* Scalar, real, continuous time; `N : ℝ → ℝ` continuous, no Lipschitz or differentiability
  assumption (a continuous sample path of a Brownian-driven process qualifies, path by path).
  Generic analysis; no stochastic object is involved.
* The time-domain limit is proved directly (dominated convergence after the substitution
  `u = β(t − s)`); the report's argument via uniqueness of the inverse Laplace transform is
  replaced by this exact statement. The Laplace-domain limit is stated separately
  (`tendsto_lagTransfer`, `tendsto_lagInitial`).
* The general linear time-varying variation-of-constants formula is
  `Dynamics.eq_variationOfConstants_of_hasDerivAt`; here the scalar closed form with the kernel
  `e^{−β(t−s)}` is needed explicitly.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.1, eq. (3-29) and
the Laplace argument following it (`x̂(s) = β/(β+s) N̂(s) + x(0)/(β+s)`).

Results.
* `lagSol` — `x(t) = e^{−βt} x₀ + β ∫₀ᵗ e^{−β(t−s)} N(s) ds`; `lagSol_zero`, `lagSol_eq`
  (`= e^{−βt}(x₀ + β∫₀ᵗ e^{βs} N(s) ds)`), `lagSol_hasDerivAt` (it solves (3-29)),
  `lagSol_unique` (every solution with `x(0) = x₀` is `lagSol`).
* `lagIntegral_subst` — the substitution `u = β(t − s)`:
  `β∫₀ᵗ e^{−β(t−s)} N(s) ds = ∫₀^{βt} e^{−u} N(t − u/β) du`.
* `tendsto_lagSol` — **(3-29) with `β → ∞`**: for every `t > 0`, `x₀` and continuous `N`,
  `lagSol β x₀ N t → N(t)` as `β → ∞`.
* `tendsto_lagTransfer`, `tendsto_lagInitial` — for every complex `s`, `β/(β + s) → 1` and
  `1/(β + s) → 0` as `β → ∞`.
-/

noncomputable section
namespace powerlib.Stochastic.LagLimit

open Real MeasureTheory Set Filter
open scoped Topology

/-- Variation-of-constants solution of `ẋ = −β(x − N)`, `x(0) = x₀`. -/
def lagSol (β x₀ : ℝ) (N : ℝ → ℝ) (t : ℝ) : ℝ :=
  exp (-β * t) * x₀ + β * ∫ s in (0 : ℝ)..t, exp (-β * (t - s)) * N s

@[tmio T, powerlib_foundation] theorem lagSol_zero (β x₀ : ℝ) (N : ℝ → ℝ) : lagSol β x₀ N 0 = x₀ := by
  simp [lagSol]

@[tmio T, powerlib_foundation] theorem lagSol_eq (β x₀ : ℝ) (N : ℝ → ℝ) (t : ℝ) :
    lagSol β x₀ N t = exp (-β * t) * (x₀ + β * ∫ s in (0 : ℝ)..t, exp (β * s) * N s) := by
  have e : ∀ s, exp (-β * (t - s)) * N s = exp (-β * t) * (exp (β * s) * N s) := by
    intro s; rw [← mul_assoc, ← exp_add]; ring_nf
  simp_rw [lagSol, e, intervalIntegral.integral_const_mul]
  ring

/-- `lagSol` solves `ẋ = −β (x − N)`. -/
@[tmio T, powerlib_foundation] theorem lagSol_hasDerivAt (β x₀ : ℝ) {N : ℝ → ℝ} (hN : Continuous N)
    (t : ℝ) : HasDerivAt (lagSol β x₀ N) (-β * (lagSol β x₀ N t - N t)) t := by
  have hI : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, exp (β * s) * N s) (exp (β * t) * N t) t :=
    ((by fun_prop : Continuous fun s => exp (β * s) * N s).integral_hasStrictDerivAt 0 t).hasDerivAt
  have he : HasDerivAt (fun u => exp (-β * u)) (exp (-β * t) * (-β)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-β)).exp
  have h := he.mul ((hI.const_mul β).const_add x₀)
  rw [show lagSol β x₀ N = fun u => exp (-β * u) * (x₀ + β * ∫ s in (0 : ℝ)..u, exp (β * s) * N s)
    from funext (lagSol_eq β x₀ N)]
  convert h using 1
  have hee : exp (-β * t) * exp (β * t) = 1 := by rw [← exp_add]; simp
  linear_combination (-(β * N t)) * hee

/-- **Uniqueness**: every differentiable solution of `ẋ = −β(x − N)` with `x(0) = x₀` is
`lagSol β x₀ N`. -/
@[tmio T, powerlib_foundation] theorem lagSol_unique {β x₀ : ℝ} {N : ℝ → ℝ} (hN : Continuous N)
    {x : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (-β * (x t - N t)) t) (h0 : x 0 = x₀) :
    x = lagSol β x₀ N := by
  set g : ℝ → ℝ := fun t => exp (β * t) * (x t - lagSol β x₀ N t)
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have he : HasDerivAt (fun u => exp (β * u)) (exp (β * t) * β) t := by
      simpa using ((hasDerivAt_id t).const_mul β).exp
    have := he.mul ((hx t).sub (lagSol_hasDerivAt β x₀ hN t))
    convert this using 1; simp only [Pi.sub_apply]; ring
  have hconst : ∀ t, g t = g 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  funext t
  have h1 := hconst t
  simp only [g, mul_zero, exp_zero, h0, lagSol_zero, sub_self] at h1
  have := (mul_eq_zero.mp h1).resolve_left (exp_pos _).ne'
  linarith

/-- The substitution `u = β (t − s)`:
`β ∫₀ᵗ e^{−β(t−s)} N(s) ds = ∫_{(0, βt]} e^{−u} N(t − u/β) du` for `β > 0`. -/
@[tmio T, powerlib_foundation] theorem lagIntegral_subst {β : ℝ} (hβ : 0 < β) (N : ℝ → ℝ) (t : ℝ) :
    β * ∫ s in (0 : ℝ)..t, exp (-β * (t - s)) * N s =
      ∫ u in (0 : ℝ)..β * t, exp (-u) * N (t - u / β) := by
  have h1 : ∫ s in (0 : ℝ)..t, exp (-β * (t - s)) * N s =
      ∫ v in (0 : ℝ)..t, exp (-β * v) * N (t - v) := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
      (fun s => exp (-β * (t - s)) * N s) t
    simp only [sub_sub_cancel, sub_self, sub_zero] at this
    exact this.symm
  have h2 := intervalIntegral.integral_comp_div (a := 0) (b := β * t)
    (fun v => exp (-β * v) * N (t - v)) hβ.ne'
  simp only [zero_div, mul_div_cancel_left₀ _ hβ.ne'] at h2
  rw [h1]
  have e : ∀ u, exp (-β * (u / β)) * N (t - u / β) = exp (-u) * N (t - u / β) := by
    intro u; congr 2; field_simp
  simp_rw [e] at h2
  rw [h2, smul_eq_mul]

/-- **Approximate identity: the fast lag tracks its input.** For `t > 0` and continuous `N`,
`lagSol β x₀ N t → N(t)` as `β → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_lagSol {t : ℝ} (ht : 0 < t) (x₀ : ℝ) {N : ℝ → ℝ}
    (hN : Continuous N) : Tendsto (fun β => lagSol β x₀ N t) atTop (𝓝 (N t)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hN.continuousOn
  set Fβ : ℝ → ℝ → ℝ := fun β u => (Ioc 0 (β * t)).indicator (fun u => exp (-u) * N (t - u / β)) u
  set f : ℝ → ℝ := (Ioi 0).indicator fun u => exp (-u) * N t
  have hint : ∀ β, 0 < β → ∫ u in (0 : ℝ)..β * t, exp (-u) * N (t - u / β) = ∫ u, Fβ β u := by
    intro β hβ
    rw [intervalIntegral.integral_of_le (by positivity), ← integral_indicator measurableSet_Ioc]
  have hlim : Tendsto (fun β => ∫ u, Fβ β u) atTop (𝓝 (∫ u, f u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((Ioi 0).indicator fun u => M * exp (-u)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun β => ?_
      refine (AEStronglyMeasurable.indicator ?_ measurableSet_Ioc)
      exact (by fun_prop : Continuous fun u => exp (-u) * N (t - u / β)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with β hβ
      refine ae_of_all _ fun u => ?_
      by_cases hu : u ∈ Ioc 0 (β * t)
      · have hu' : u ∈ Ioi (0 : ℝ) := hu.1
        simp only [Fβ, indicator_of_mem hu, indicator_of_mem hu']
        have hmem : t - u / β ∈ Icc 0 t := by
          constructor
          · have : u / β ≤ t := by rw [div_le_iff₀ hβ]; linarith [hu.2]
            linarith
          · have : 0 ≤ u / β := div_nonneg hu.1.le hβ.le
            linarith
        rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, mul_comm]
        exact mul_le_mul_of_nonneg_right (hM _ hmem) (exp_pos _).le
      · simp only [Fβ, indicator_of_notMem hu, norm_zero]
        by_cases hu' : u ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hu']
          have := (norm_nonneg (N 0)).trans (hM 0 ⟨le_refl _, ht.le⟩)
          positivity
        · rw [indicator_of_notMem hu']
    · have hb : IntegrableOn (fun u : ℝ => M * exp (-u)) (Ioi 0) :=
        (integrableOn_exp_neg_Ioi 0).const_mul M
      exact hb.integrable_indicator measurableSet_Ioi
    · refine ae_of_all _ fun u => ?_
      by_cases hu : u ∈ Ioi (0 : ℝ)
      · simp only [f, indicator_of_mem hu]
        have hev : ∀ᶠ β in atTop, Fβ β u = exp (-u) * N (t - u / β) := by
          filter_upwards [eventually_gt_atTop (u / t)] with β hβ
          have : u ≤ β * t := by rw [div_lt_iff₀ ht] at hβ; linarith
          simp only [Fβ, indicator_of_mem (show u ∈ Ioc 0 (β * t) from ⟨hu, this⟩)]
        refine Tendsto.congr' (EventuallyEq.symm hev) ?_
        have hdiv : Tendsto (fun β : ℝ => t - u / β) atTop (𝓝 t) := by
          have := (tendsto_const_nhds (x := u)).div_atTop tendsto_id
          simpa using (tendsto_const_nhds (x := t)).sub this
        exact tendsto_const_nhds.mul ((hN.tendsto t).comp hdiv)
      · simp only [f, indicator_of_notMem hu]
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun β => ?_)
        have : u ∉ Ioc 0 (β * t) := fun h => hu h.1
        simp only [Fβ, indicator_of_notMem this]
  have hf : ∫ u, f u = N t := by
    rw [integral_indicator measurableSet_Ioi, integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]
  rw [hf] at hlim
  have hexp : Tendsto (fun β => exp (-β * t) * x₀) atTop (𝓝 0) := by
    have : Tendsto (fun β : ℝ => -β * t) atTop atBot :=
      tendsto_neg_atTop_atBot.atBot_mul_const ht
    simpa using (tendsto_exp_atBot.comp this).mul_const x₀
  have hsum := hexp.add hlim
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  rw [lagSol, lagIntegral_subst hβ, hint β hβ]

/-- Frequency domain: `β/(β + s) → 1` as `β → ∞`, for every complex `s`. -/
@[tmio T, powerlib_foundation] theorem tendsto_lagTransfer (s : ℂ) :
    Tendsto (fun β : ℝ => (β : ℂ) / (β + s)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun β : ℝ => (β : ℂ)⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have h : Tendsto (fun β : ℝ => (1 + s * (β : ℂ)⁻¹)⁻¹) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := s)).mul hinv).const_add 1
    rw [mul_zero, add_zero] at this
    simpa using this.inv₀ one_ne_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  rw [show (1 : ℂ) + s * (β : ℂ)⁻¹ = (β + s) / β by field_simp, inv_div]

/-- The initial-condition term of the Laplace transform vanishes: `1/(β + s) → 0`. -/
@[tmio T, powerlib_foundation] theorem tendsto_lagInitial (s : ℂ) :
    Tendsto (fun β : ℝ => 1 / ((β : ℂ) + s)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun β : ℝ => (β : ℂ)⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have h2 := hinv.mul ((tendsto_lagTransfer s))
  rw [zero_mul] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  rw [← mul_div_assoc, inv_mul_cancel₀ hβ']

end powerlib.Stochastic.LagLimit
