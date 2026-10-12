import dependencies.Mathlib
import theorem.Attributes

/-! # Sliding Fourier coefficients (generalized averaging)

Foundation layer: an exact calculus identity for the sliding-window Fourier coefficients of
generalized averaging (Sanders et al. 1991). No converter model is fixed here.

Definitions. For a window length `T > 0`, a harmonic frequency `ω` (in the source `ω = 2π/T`;
the identities below hold for every real `ω`), an integer harmonic `k` and a complex signal
`x : ℝ → ℂ`,

  `⟨x⟩_k(t) = (1/T) ∫_{t−T}^{t} x(τ) e^{−jkωτ} dτ`   (`slidingCoeff`).

Results.
* `hasDerivAt_slidingCoeff`: if `x` is `C¹` (derivative `x'` continuous), then
  `d⟨x⟩_k/dt = ⟨ẋ⟩_k − jkω ⟨x⟩_k` (fundamental theorem of calculus for the moving window plus
  integration by parts).
* `hasDerivAt_slidingCoeff_of_ode`: along a solution of `ẋ = f(x, t)` with continuous
  `t ↦ f(x(t), t)`, `d⟨x⟩_k/dt = ⟨f(x, t)⟩_k − jkω⟨x⟩_k` (the generalized-averaging equation).
* `slidingCoeff_zero_demod`: `⟨x e^{−jωt}⟩₀ = ⟨x⟩₁` (demodulation by the fundamental turns the
  first harmonic into the zeroth one: dynamic phasor ↔ rotating-frame average).

Source: work-sync theory/T-averaging-method.md §1.6 (sliding Fourier coefficient and its
evolution equation), §2.3 (dq frame = rotating-frame average), §2.8 (dynamic phasor).
-/

noncomputable section
namespace powerlib.Averaging

open Complex intervalIntegral MeasureTheory

/-- Sliding Fourier coefficient `⟨x⟩_k(t) = (1/T) ∫_{t−T}^{t} x(τ) e^{−jkωτ} dτ`. -/
def slidingCoeff (T ω : ℝ) (k : ℤ) (x : ℝ → ℂ) (t : ℝ) : ℂ :=
  (1 / T : ℂ) * ∫ τ in (t - T)..t, x τ * Complex.exp (-((k : ℂ) * ω * τ * I))

@[powerlib_foundation] theorem hasDerivAt_harmonic (ω : ℝ) (k : ℤ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => Complex.exp (-((k : ℂ) * ω * τ * I)))
      (-((k : ℂ) * ω * I) * Complex.exp (-((k : ℂ) * ω * τ * I))) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => ((τ : ℂ))) 1 τ := (hasDerivAt_id τ).ofReal_comp
  have h2 : HasDerivAt (fun τ : ℝ => -((k : ℂ) * ω * τ * I)) (-((k : ℂ) * ω * I)) τ := by
    have := ((h1.const_mul ((k : ℂ) * ω)).mul_const I).neg
    simp only [mul_one] at this
    exact this
  have h3 := h2.cexp
  convert h3 using 1
  ring

@[powerlib_foundation] theorem continuous_harmonic (ω : ℝ) (k : ℤ) :
    Continuous fun τ : ℝ => Complex.exp (-((k : ℂ) * ω * τ * I)) := by
  fun_prop

/-- Derivative of a moving-window integral of a continuous function:
`d/dt ∫_{t−T}^{t} g = g(t) − g(t − T)`. -/
@[powerlib_foundation] theorem hasDerivAt_window_integral {g : ℝ → ℂ} (hg : Continuous g)
    (T t : ℝ) :
    HasDerivAt (fun t => ∫ τ in (t - T)..t, g τ) (g t - g (t - T)) t := by
  have hG : ∀ u, HasDerivAt (fun u => ∫ τ in (0 : ℝ)..u, g τ) (g u) u :=
    fun u => (hg.integral_hasStrictDerivAt 0 u).hasDerivAt
  have h1 := hG t
  have h2 := (hG (t - T)).comp_sub_const t T
  have hfun : (fun t => ∫ τ in (t - T)..t, g τ) =
      fun t => (∫ τ in (0 : ℝ)..t, g τ) - ∫ τ in (0 : ℝ)..(t - T), g τ := by
    funext t
    rw [integral_interval_sub_left (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  rw [hfun]
  exact h1.sub h2

/-- The generalized-averaging identity `d⟨x⟩_k/dt = ⟨ẋ⟩_k − jkω⟨x⟩_k` for a `C¹` signal. -/
@[powerlib_foundation] theorem hasDerivAt_slidingCoeff {T ω : ℝ} (k : ℤ) {x x' : ℝ → ℂ}
    (hx : ∀ τ, HasDerivAt x (x' τ) τ) (hx' : Continuous x') (t : ℝ) :
    HasDerivAt (slidingCoeff T ω k x)
      (slidingCoeff T ω k x' t - (k : ℂ) * ω * I * slidingCoeff T ω k x t) t := by
  set e : ℝ → ℂ := fun τ => Complex.exp (-((k : ℂ) * ω * τ * I)) with hedef
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun τ => (hx τ).continuousAt
  have hec : Continuous e := continuous_harmonic ω k
  have hg : Continuous fun τ => x τ * e τ := hxc.mul hec
  have hW := (hasDerivAt_window_integral hg T t).const_mul (1 / T : ℂ)
  -- integration by parts on the window
  have hparts : ∫ τ in (t - T)..t, x' τ * e τ =
      x t * e t - x (t - T) * e (t - T) +
        (k : ℂ) * ω * I * ∫ τ in (t - T)..t, x τ * e τ := by
    have h := integral_mul_deriv_eq_deriv_mul (a := t - T) (b := t) (u := e) (v := x)
      (u' := fun τ => -((k : ℂ) * ω * I) * e τ) (v' := x')
      (fun τ _ => hasDerivAt_harmonic ω k τ) (fun τ _ => hx τ)
      ((continuous_const.mul hec).intervalIntegrable _ _) (hx'.intervalIntegrable _ _)
    have h1 : ∫ τ in (t - T)..t, x' τ * e τ = ∫ τ in (t - T)..t, e τ * x' τ := by
      congr 1; funext τ; ring
    have h2 : ∫ τ in (t - T)..t, -((k : ℂ) * ω * I) * e τ * x τ =
        -((k : ℂ) * ω * I) * ∫ τ in (t - T)..t, x τ * e τ := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext τ; ring
    rw [h1, h, h2]
    ring
  unfold slidingCoeff
  convert hW using 1
  show (1 / (T : ℂ) * ∫ τ in (t - T)..t, x' τ * e τ) -
      (k : ℂ) * ω * I * (1 / (T : ℂ) * ∫ τ in (t - T)..t, x τ * e τ) = _
  rw [hparts]
  ring

/-- Along a solution of `ẋ = f(x, t)` (with `t ↦ f(x(t), t)` continuous):
`d⟨x⟩_k/dt = ⟨f(x, t)⟩_k − jkω⟨x⟩_k`. -/
@[powerlib_foundation] theorem hasDerivAt_slidingCoeff_of_ode {T ω : ℝ} (k : ℤ)
    {f : ℂ → ℝ → ℂ} {x : ℝ → ℂ} (hx : ∀ τ, HasDerivAt x (f (x τ) τ) τ)
    (hf : Continuous fun τ => f (x τ) τ) (t : ℝ) :
    HasDerivAt (slidingCoeff T ω k x)
      (slidingCoeff T ω k (fun τ => f (x τ) τ) t - (k : ℂ) * ω * I * slidingCoeff T ω k x t) t :=
  hasDerivAt_slidingCoeff k hx hf t

/-- Demodulation: `⟨x e^{−jωt}⟩₀ = ⟨x⟩₁`. -/
@[powerlib_foundation] theorem slidingCoeff_zero_demod (T ω : ℝ) (x : ℝ → ℂ) (t : ℝ) :
    slidingCoeff T ω 0 (fun τ => x τ * Complex.exp (-((ω : ℂ) * τ * I))) t =
      slidingCoeff T ω 1 x t := by
  simp only [slidingCoeff, Int.cast_zero, Int.cast_one, zero_mul, neg_zero, Complex.exp_zero,
    mul_one, one_mul]

end powerlib.Averaging
