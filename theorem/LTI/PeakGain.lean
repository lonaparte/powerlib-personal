import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import theorem.Attributes

/-! # Peak gain of a causal convolution over a finite horizon (foundation)

The exact worst-case response at one time `t` of a linear time-invariant system driven by an
arbitrary bounded input: for the causal convolution `y(t) = ∫₀ᵗ h(t − τ) u(τ) dτ` with
`|u| ≤ U` on `[0, t]`, `|y(t)| ≤ U ∫₀ᵗ |h|`, and the bang-bang input
`u(τ) = U sign h(t − τ)` attains the bound, so `U ∫₀ᵗ |h|` is the greatest attainable value.

Scope.
* Generic analysis; no model. Real-valued kernel `h : ℝ → ℝ` and input `u : ℝ → ℝ`, a horizon
  `t ≥ 0` (a period `T > 0` in the periodic statement), Lebesgue interval integrals. The kernel
  is only assumed interval-integrable on `[0, t]`; the input is interval-integrable and bounded
  by `U` on `[0, t]`. The integrability of the product `h(t − τ) u(τ)` is derived (an integrable
  function times a bounded measurable one), not assumed. The sign is `SignType.sign` cast to `ℝ`
  (`1`, `−1`, `0`).
* Every statement is about arbitrary functions; nothing here selects an engineering object
  (Rules §3, foundation). Engineering reading, for orientation only: with `h` the impulse
  response from a bridge voltage to a tank current, no modulation bounded by `U` can push the
  current at time `t` above `U ∫₀ᵗ |h|`, and the bang-bang modulation synchronized with the
  reversed impulse response reaches it. For a lossless resonator `∫₀^∞ |h| = ∞`, so the
  worst-case current grows without bound with the horizon.

Source: the classical fact that the peak-to-peak (`L∞`-induced) gain of a convolution operator
is the `L¹` norm of its kernel: Hölder's inequality for the pairing of `L¹` with `L∞`, with
equality at the sign of the kernel. The change of variables is Mathlib's
`intervalIntegral.integral_comp_sub_left`; the periodic shift is
`Function.Periodic.intervalIntegral_add_eq`.

Results.
* `abs_convolution_le`: for `t ≥ 0`, `h` and `u` interval-integrable on `[0, t]` and
  `|u τ| ≤ U` on `[0, t]`, `|∫ τ in 0..t, h (t − τ) * u τ| ≤ U * ∫ s in 0..t, |h s|`.
* `convolution_sign`: for every `h`, `t`, `U`, the bang-bang input `U * sign (h (t − τ))` gives
  exactly `∫ τ in 0..t, h (t − τ) * (U * sign (h (t − τ))) = U * ∫ s in 0..t, |h s|`.
* `isGreatest_convolution`: for `t ≥ 0`, `U ≥ 0` and `h` interval-integrable on `[0, t]`,
  `U * ∫ s in 0..t, |h s|` is the greatest element of the set of values
  `|∫ τ in 0..t, h (t − τ) * u τ|` over interval-integrable `u` with `|u| ≤ U` on `[0, t]`.
* `abs_periodic_convolution_le`: the periodic steady-state analogue: for a `T`-periodic kernel
  `g` (`T > 0`) interval-integrable over one period and an input as above on `[0, T]`, at every
  time `t`, `|∫ τ in 0..T, g (t − τ) * u τ| ≤ U * ∫ s in 0..T, |g s|`.
-/

noncomputable section
namespace powerlib.LTI
open MeasureTheory Set Filter
open scoped Interval

/-- The sign of a real number, cast back to `ℝ`, is a measurable function. -/
@[tmio T, powerlib_foundation] private theorem measurable_sign_cast :
    Measurable (fun x : ℝ => ((SignType.sign x : SignType) : ℝ)) := by
  have hfun : (fun x : ℝ => ((SignType.sign x : SignType) : ℝ)) =
      fun x => if 0 < x then 1 else if x < 0 then -1 else 0 := by
    funext x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · simp [hx, hx.not_gt]
    · simp
    · simp [hx]
  rw [hfun]
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

/-- An integrable function times a function bounded by `U` on `[0, t]` has integral bounded by
`U` times the integral of the absolute value of the first factor. -/
@[tmio T, powerlib_foundation] private theorem abs_integral_mul_le {f u : ℝ → ℝ} {t U : ℝ}
    (ht : 0 ≤ t) (hf : IntervalIntegrable f volume 0 t) (hu : IntervalIntegrable u volume 0 t)
    (hU : ∀ τ ∈ Icc 0 t, |u τ| ≤ U) :
    |∫ τ in 0..t, f τ * u τ| ≤ U * ∫ τ in 0..t, |f τ| := by
  have hbound : ∀ᵐ τ ∂volume.restrict (Ι 0 t), ‖u τ‖ ≤ U := by
    rw [uIoc_of_le ht]
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun τ hτ => hU τ (Ioc_subset_Icc_self hτ))
  have hfu : IntervalIntegrable (fun τ => f τ * u τ) volume 0 t :=
    intervalIntegrable_iff.mpr (Integrable.mul_bdd hf.def' hu.def'.aestronglyMeasurable hbound)
  calc |∫ τ in 0..t, f τ * u τ| ≤ ∫ τ in 0..t, |f τ * u τ| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ τ in 0..t, U * |f τ| := by
        refine intervalIntegral.integral_mono_on ht hfu.abs (hf.abs.const_mul U) fun τ hτ => ?_
        rw [abs_mul, mul_comm U]
        exact mul_le_mul_of_nonneg_left (hU τ hτ) (abs_nonneg _)
    _ = U * ∫ τ in 0..t, |f τ| := intervalIntegral.integral_const_mul U _

/-- The reversed kernel `τ ↦ h (t − τ)` is interval-integrable on `[0, t]` when `h` is. -/
@[tmio T, powerlib_foundation] private theorem intervalIntegrable_reverse {h : ℝ → ℝ} {t : ℝ}
    (hh : IntervalIntegrable h volume 0 t) :
    IntervalIntegrable (fun τ => h (t - τ)) volume 0 t := by
  simpa using (hh.comp_sub_left t).symm

/-- Reversing the kernel on `[0, t]` does not change the integral of its absolute value. -/
@[tmio T, powerlib_foundation] private theorem integral_abs_reverse (h : ℝ → ℝ) (t : ℝ) :
    ∫ τ in 0..t, |h (t - τ)| = ∫ s in 0..t, |h s| := by
  have h1 := intervalIntegral.integral_comp_sub_left (fun s => |h s|) t (a := 0) (b := t)
  simpa only [sub_self, sub_zero] using h1

/-- Peak bound of a causal convolution: an input bounded by `U` on `[0, t]` drives the response
at time `t` to at most `U ∫₀ᵗ |h|` in absolute value. -/
@[tmio T, powerlib_foundation] theorem abs_convolution_le {h u : ℝ → ℝ} {t U : ℝ} (ht : 0 ≤ t)
    (hh : IntervalIntegrable h volume 0 t) (hu : IntervalIntegrable u volume 0 t)
    (hU : ∀ τ ∈ Icc 0 t, |u τ| ≤ U) :
    |∫ τ in 0..t, h (t - τ) * u τ| ≤ U * ∫ s in 0..t, |h s| := by
  have key := abs_integral_mul_le ht (intervalIntegrable_reverse hh) hu hU
  rwa [integral_abs_reverse] at key

/-- The bang-bang input `U sign h(t − τ)`, synchronized with the reversed kernel, gives the
response `U ∫₀ᵗ |h|` at time `t`. -/
@[tmio T, powerlib_foundation] theorem convolution_sign (h : ℝ → ℝ) (t U : ℝ) :
    ∫ τ in 0..t, h (t - τ) * (U * ((SignType.sign (h (t - τ)) : SignType) : ℝ)) =
      U * ∫ s in 0..t, |h s| := by
  have hfun : (fun τ => h (t - τ) * (U * ((SignType.sign (h (t - τ)) : SignType) : ℝ))) =
      fun τ => U * |h (t - τ)| := by
    funext τ
    rw [mul_left_comm, self_mul_sign]
  rw [hfun, intervalIntegral.integral_const_mul, integral_abs_reverse]

/-- Exact peak gain: over interval-integrable inputs bounded by `U ≥ 0` on `[0, t]`, the greatest
absolute response at time `t` is `U ∫₀ᵗ |h|`, attained by the bang-bang input. -/
@[tmio T, powerlib_foundation] theorem isGreatest_convolution {h : ℝ → ℝ} {t U : ℝ} (ht : 0 ≤ t)
    (hU : 0 ≤ U) (hh : IntervalIntegrable h volume 0 t) :
    IsGreatest ((fun u : ℝ → ℝ => |∫ τ in 0..t, h (t - τ) * u τ|) ''
        {u | IntervalIntegrable u volume 0 t ∧ ∀ τ ∈ Icc 0 t, |u τ| ≤ U})
      (U * ∫ s in 0..t, |h s|) := by
  have hsign : ∀ x : ℝ, |U * ((SignType.sign x : SignType) : ℝ)| ≤ U := by
    intro x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · simp [hx, abs_of_nonneg hU]
    · simpa using hU
    · simp [hx, abs_of_nonneg hU]
  refine ⟨⟨fun τ => U * ((SignType.sign (h (t - τ)) : SignType) : ℝ), ⟨?_, fun τ _ => hsign _⟩,
    ?_⟩, ?_⟩
  · refine IntervalIntegrable.mono_fun' (g := fun _ => U) intervalIntegrable_const ?_
      (Eventually.of_forall fun τ => hsign _)
    exact ((measurable_sign_cast.comp_aemeasurable
      (intervalIntegrable_reverse hh).def'.aestronglyMeasurable.aemeasurable).const_mul
        U).aestronglyMeasurable
  · simp only
    rw [convolution_sign, abs_of_nonneg (mul_nonneg hU
      (intervalIntegral.integral_nonneg ht fun _ _ => abs_nonneg _))]
  · rintro _ ⟨u, ⟨hu, hUu⟩, rfl⟩
    exact abs_convolution_le ht hh hu hUu

/-- Periodic steady-state analogue: for a `T`-periodic kernel `g` convolved over one period with
an input bounded by `U` on `[0, T]`, the response at every time `t` is at most `U ∫₀ᵀ |g|` in
absolute value. -/
@[tmio T, powerlib_foundation] theorem abs_periodic_convolution_le {g u : ℝ → ℝ} {T U : ℝ}
    (hT : 0 < T) (hg : Function.Periodic g T) (hgi : IntervalIntegrable g volume 0 T)
    (hu : IntervalIntegrable u volume 0 T) (hU : ∀ τ ∈ Icc 0 T, |u τ| ≤ U) (t : ℝ) :
    |∫ τ in 0..T, g (t - τ) * u τ| ≤ U * ∫ s in 0..T, |g s| := by
  have hr : IntervalIntegrable (fun τ => g (t - τ)) volume 0 T := by
    simpa using ((hg.intervalIntegrable₀ hT.ne' hgi (t - T) t).comp_sub_left t).symm
  have hga : Function.Periodic (fun s => |g s|) T := fun s => by simp only [hg s]
  have h1 := intervalIntegral.integral_comp_sub_left (fun s => |g s|) t (a := 0) (b := T)
  have h2 := hga.intervalIntegral_add_eq (t - T) 0
  simp only [sub_zero, sub_add_cancel, zero_add] at h1 h2
  have key := abs_integral_mul_le hT.le hr hu hU
  rwa [h1, h2] at key

end powerlib.LTI
