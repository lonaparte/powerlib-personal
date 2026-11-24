import theorem.SpecialFunctions.Fundamental

/-! # Harmonics of bounded periodic signals and of bridge waveforms (foundation)

For a period `T > 0`, `ω = 2π/T` and `n : ℕ`, the `n`-th harmonic Fourier coefficients of a real
signal `v` on `[0, T]` are `aₙ = (2/T) ∫₀ᵀ v(t) cos(nωt) dt` (`harmonicCos`) and
`bₙ = (2/T) ∫₀ᵀ v(t) sin(nωt) dt` (`harmonicSin`); the amplitude of the `n`-th harmonic is
`√(aₙ² + bₙ²)`. For `n = 1` they are the fundamental coefficients `cosCoeff`, `sinCoeff` of
`theorem/SpecialFunctions/Fundamental.lean`. The `4/π` law holds for every harmonic: if `|v| ≤ V`
on `[0, T]`, then `√(aₙ² + bₙ²) ≤ 4V/π` for every `n ≥ 1`.

Two bridge waveforms are computed exactly. The square wave `V · sgn(cos(ωt))` has the harmonics
`aₙ = 4V/(nπ) · (−1)^((n−1)/2)` for odd `n`, `aₙ = 0` for even `n`, `bₙ = 0`: its `n`-th harmonic
has amplitude `4|V|/(nπ)`, the fundamental divided by `n`. The quasi-square (three-level) wave of
conduction angle `θ ∈ [0, π]` takes the value `V` where `cos(ωt) > cos(θ/2)` (that is,
`|ωt| < θ/2` modulo `2π`), `−V` where `cos(ωt) < −cos(θ/2)`, and `0` otherwise. It is the output
voltage of a full bridge under phase-shift control: the two legs, each a square wave, are shifted
by `π − θ`, which inserts a zero-voltage interval of width `π − θ` each half period (the same
waveform is the ideal reading of a zero-voltage interval inserted by a dead time; the voltage
during a real dead time depends on the current direction). Its harmonics are
`aₙ = 4V/(nπ) · sin(nθ/2)` for odd `n`, `aₙ = 0` for even `n`, `bₙ = 0`; the fundamental
amplitude is `(4|V|/π) sin(θ/2)`, and `θ = π` gives the harmonics of the square wave
(`sin(nπ/2) = (−1)^((n−1)/2)` for odd `n`).

Scope.
* Generic real analysis; no model family and no engineering object. In the bound, the signal
  `v : ℝ → ℝ` is an arbitrary function, interval integrable on `[0, T]` and bounded there by `V`;
  nothing else (continuity, periodicity, symmetry) is assumed. The harmonic index is a natural
  number; the bound needs `n ≠ 0` (the coefficient `a₀` is twice the mean value).
* The square and quasi-square waves are the ideal waveforms of the definitions: instantaneous
  transitions, levels `±V` and `0` exactly. Only the coefficients are computed; the convergence of
  the Fourier series and Parseval's identity are not part of this module.

Source: the Fourier series of the square wave and of the quasi-square wave of a full bridge under
phase-shift control (Mohan, Undeland, Robbins, *Power Electronics*, Wiley 2003, ch. 8, the
single-phase full-bridge inverter with voltage cancellation); the `L∞`–`L¹` duality proof of
`theorem/SpecialFunctions/Fundamental.lean`, with `∫₀ᵀ |cos(nωt − θ)| dt = 2T/π` for every
integer `n ≥ 1` (the integrand runs through `n` periods of `|cos|`).

Results.
* `harmonicCos v T n`, `harmonicSin v T n`: the `n`-th harmonic Fourier coefficients defined above;
  `quasiSquareWave V T θ t`: the quasi-square wave defined above.
* `harmonicCos_one`, `harmonicSin_one`: for `n = 1` they are `cosCoeff v T`, `sinCoeff v T`.
* `integral_abs_cos_harmonic`: `∫₀ᵀ |cos(nωt − θ)| dt = 2T/π` for `T > 0`, `n ≠ 0` and every `θ`.
* `harmonicCos_mul_cos_add_harmonicSin_mul_sin`: for `v` interval integrable on `[0, T]`,
  `aₙ cos θ + bₙ sin θ = (2/T) ∫₀ᵀ v(t) cos(nωt − θ) dt`.
* `harmonic_projection_le`: if moreover `T > 0`, `n ≠ 0` and `|v t| ≤ V` on `[0, T]`, then
  `aₙ cos θ + bₙ sin θ ≤ 4V/π` for every `θ`.
* `harmonic_le` (the `4/π` law for every harmonic): under the same hypotheses,
  `√(aₙ² + bₙ²) ≤ 4V/π`.
* `harmonicSin_eq_zero_of_symm`: a signal with `v(T − t) = v(t)` for all `t` has `bₙ = 0` for every
  `n`.
* Square wave: `squareWave_harmonicCos_odd` (`aₙ = 4V/(nπ) · (−1)^((n−1)/2)` for odd `n`, `T > 0`),
  `squareWave_harmonicCos_even` (`aₙ = 0` for even `n`, including `n = 0`), `squareWave_harmonicSin`
  (`bₙ = 0`), `squareWave_harmonic` (amplitude `4|V|/(nπ)` for odd `n`).
* Quasi-square wave, for `T > 0` and `0 ≤ θ ≤ π`: `quasiSquareWave_harmonicCos_odd`
  (`aₙ = 4V/(nπ) · sin(nθ/2)` for odd `n`), `quasiSquareWave_harmonicCos_even` (`aₙ = 0` for even
  `n`), `quasiSquareWave_harmonicSin` (`bₙ = 0`, every `T`, `θ`), `quasiSquareWave_harmonic`
  (amplitude `4|V|/(nπ) · |sin(nθ/2)|` for odd `n`), `quasiSquareWave_harmonic_le` (amplitude at
  most `4|V|/(nπ)` for every `n ≠ 0`), `quasiSquareWave_cosCoeff` (`cosCoeff = (4V/π) sin(θ/2)`),
  `quasiSquareWave_fundamental` (fundamental amplitude `(4|V|/π) sin(θ/2)`).
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real Set MeasureTheory

/-- `n`-th harmonic cosine coefficient over `[0, T]`: `(2/T) ∫₀ᵀ v(t) cos(n · 2πt/T) dt`. -/
def harmonicCos (v : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  2 / T * ∫ t in (0 : ℝ)..T, v t * cos (n * (2 * π / T) * t)

/-- `n`-th harmonic sine coefficient over `[0, T]`: `(2/T) ∫₀ᵀ v(t) sin(n · 2πt/T) dt`. -/
def harmonicSin (v : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  2 / T * ∫ t in (0 : ℝ)..T, v t * sin (n * (2 * π / T) * t)

/-- The quasi-square (three-level) wave of level `V` and conduction angle `θ`, centred on the
maxima of `cos(2πt/T)`: `V` where `cos(2πt/T) > cos(θ/2)`, `−V` where `cos(2πt/T) < −cos(θ/2)`,
`0` otherwise. -/
def quasiSquareWave (V T θ : ℝ) (t : ℝ) : ℝ :=
  V * if cos (θ / 2) < cos (2 * π / T * t) then 1
    else if cos (2 * π / T * t) < -cos (θ / 2) then -1 else 0

@[tmio T, powerlib_foundation] theorem harmonicCos_one (v : ℝ → ℝ) (T : ℝ) :
    harmonicCos v T 1 = cosCoeff v T := by
  simp [harmonicCos, cosCoeff]

@[tmio T, powerlib_foundation] theorem harmonicSin_one (v : ℝ → ℝ) (T : ℝ) :
    harmonicSin v T 1 = sinCoeff v T := by
  simp [harmonicSin, sinCoeff]

/-- The mean of `|cos|` over `n` periods: `∫₀ᵀ |cos(n · 2πt/T − θ)| dt = 2T/π` for `n ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem integral_abs_cos_harmonic {T : ℝ} (hT : 0 < T) {n : ℕ}
    (hn : n ≠ 0) (θ : ℝ) :
    ∫ t in (0 : ℝ)..T, |cos (n * (2 * π / T) * t - θ)| = 2 * T / π := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hT' : 0 < T / n := div_pos hT hn'
  have hω : (n : ℝ) * (2 * π / T) = 2 * π / (T / n) := by field_simp
  have hper : Function.Periodic (fun t => |cos (2 * π / (T / n) * t - θ)|) (T / n) := fun t => by
    simp only
    rw [show 2 * π / (T / n) * (t + T / n) - θ = 2 * π / (T / n) * t - θ + 2 * π by
      field_simp; ring, cos_add_two_pi]
  have h := hper.intervalIntegral_add_zsmul_eq (n : ℤ) 0
    (fun _ _ => Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [zero_add, zero_add, zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast,
    show (n : ℝ) * (T / n) = T by field_simp, integral_abs_cos_period hT'] at h
  simp_rw [hω]
  rw [h]
  field_simp

/-- The projection of `(aₙ, bₙ)` on the direction `θ` is the coefficient against `cos(nωt − θ)`. -/
@[tmio T, powerlib_foundation] theorem harmonicCos_mul_cos_add_harmonicSin_mul_sin {v : ℝ → ℝ}
    {T : ℝ} (hv : IntervalIntegrable v volume 0 T) (n : ℕ) (θ : ℝ) :
    harmonicCos v T n * cos θ + harmonicSin v T n * sin θ =
      2 / T * ∫ t in (0 : ℝ)..T, v t * cos (n * (2 * π / T) * t - θ) := by
  have hc : IntervalIntegrable (fun t => v t * cos (n * (2 * π / T) * t)) volume 0 T :=
    hv.mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun t => v t * sin (n * (2 * π / T) * t)) volume 0 T :=
    hv.mul_continuousOn (by fun_prop)
  have h : ∫ t in (0 : ℝ)..T, v t * cos (n * (2 * π / T) * t - θ) =
      (∫ t in (0 : ℝ)..T, v t * cos (n * (2 * π / T) * t)) * cos θ +
        (∫ t in (0 : ℝ)..T, v t * sin (n * (2 * π / T) * t)) * sin θ := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_add (hc.mul_const _) (hs.mul_const _)]
    congr 1
    ext t
    rw [cos_sub]
    ring
  rw [h, harmonicCos, harmonicSin]
  ring

/-- Every projection of the `n`-th harmonic of a signal bounded by `V` is at most `4V/π`. -/
@[tmio T, powerlib_foundation] theorem harmonic_projection_le {v : ℝ → ℝ} {T V : ℝ} (hT : 0 < T)
    {n : ℕ} (hn : n ≠ 0) (hv : IntervalIntegrable v volume 0 T)
    (hV : ∀ t ∈ Icc 0 T, |v t| ≤ V) (θ : ℝ) :
    harmonicCos v T n * cos θ + harmonicSin v T n * sin θ ≤ 4 * V / π := by
  rw [harmonicCos_mul_cos_add_harmonicSin_mul_sin hv n θ]
  have hle : ∫ t in (0 : ℝ)..T, v t * cos (n * (2 * π / T) * t - θ) ≤
      ∫ t in (0 : ℝ)..T, V * |cos (n * (2 * π / T) * t - θ)| := by
    refine intervalIntegral.integral_mono_on hT.le (hv.mul_continuousOn (by fun_prop))
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun t ht => ?_
    calc v t * cos (n * (2 * π / T) * t - θ) ≤ |v t * cos (n * (2 * π / T) * t - θ)| :=
          le_abs_self _
      _ = |v t| * |cos (n * (2 * π / T) * t - θ)| := abs_mul _ _
      _ ≤ V * |cos (n * (2 * π / T) * t - θ)| :=
          mul_le_mul_of_nonneg_right (hV t ht) (abs_nonneg _)
  rw [intervalIntegral.integral_const_mul, integral_abs_cos_harmonic hT hn] at hle
  calc 2 / T * ∫ t in (0 : ℝ)..T, v t * cos (n * (2 * π / T) * t - θ)
      ≤ 2 / T * (V * (2 * T / π)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * V / π := by field_simp; ring

/-- The `4/π` law for every harmonic: a signal bounded by `V` on a period has `n`-th harmonic
amplitude at most `4V/π` (`n ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem harmonic_le {v : ℝ → ℝ} {T V : ℝ} (hT : 0 < T) {n : ℕ}
    (hn : n ≠ 0) (hv : IntervalIntegrable v volume 0 T) (hV : ∀ t ∈ Icc 0 T, |v t| ≤ V) :
    √(harmonicCos v T n ^ 2 + harmonicSin v T n ^ 2) ≤ 4 * V / π := by
  -- the amplitude is the projection on the direction `arg (aₙ + j bₙ)`
  set z : ℂ := ⟨harmonicCos v T n, harmonicSin v T n⟩
  have ha : ‖z‖ * cos (Complex.arg z) = harmonicCos v T n := Complex.norm_mul_cos_arg z
  have hb : ‖z‖ * sin (Complex.arg z) = harmonicSin v T n := Complex.norm_mul_sin_arg z
  have hz : √(harmonicCos v T n ^ 2 + harmonicSin v T n ^ 2) = ‖z‖ :=
    (Complex.norm_eq_sqrt_sq_add_sq z).symm
  have hproj : ‖z‖ =
      harmonicCos v T n * cos (Complex.arg z) + harmonicSin v T n * sin (Complex.arg z) := by
    rw [← ha, ← hb]
    linear_combination -‖z‖ * cos_sq_add_sin_sq (Complex.arg z)
  rw [hz, hproj]
  exact harmonic_projection_le hT hn hv hV _

/-- A signal symmetric about the middle of the period, `v(T − t) = v(t)`, has no sine
harmonics: `t ↦ T − t` reverses the sign of the integrand. -/
@[tmio T, powerlib_foundation] theorem harmonicSin_eq_zero_of_symm {v : ℝ → ℝ} {T : ℝ}
    (hv : ∀ t, v (T - t) = v t) (n : ℕ) : harmonicSin v T n = 0 := by
  rcases eq_or_ne T 0 with hT | hT
  · simp [harmonicSin, hT]
  set g : ℝ → ℝ := fun t => v t * sin (n * (2 * π / T) * t) with hg
  have hodd : ∀ t, g (T - t) = -g t := by
    intro t
    have e : (n : ℝ) * (2 * π / T) * (T - t) = n * (2 * π) - n * (2 * π / T) * t := by
      field_simp
    simp only [hg, hv, e, sin_nat_mul_two_pi_sub]
    ring
  have hI : ∫ t in (0 : ℝ)..T, g t = -∫ t in (0 : ℝ)..T, g t := by
    calc ∫ t in (0 : ℝ)..T, g t = ∫ t in (T - T)..(T - 0), g t := by rw [sub_self, sub_zero]
      _ = ∫ t in (0 : ℝ)..T, g (T - t) := (intervalIntegral.integral_comp_sub_left g T).symm
      _ = ∫ t in (0 : ℝ)..T, -g t := by simp_rw [hodd]
      _ = -∫ t in (0 : ℝ)..T, g t := intervalIntegral.integral_neg
  have h0 : ∫ t in (0 : ℝ)..T, g t = 0 := by linarith
  rw [harmonicSin, ← hg, h0, mul_zero]

/-! ## Waveforms of the form `V g(ωt)` -/

/-- Reduction to the half period `[0, π]` of the cosine harmonic of `V g(2πt/T)`, for a profile
with `g(2π − u) = g(u)`. -/
@[tmio T, powerlib_foundation] private lemma harmonicCos_profile {g : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (V : ℝ) (n : ℕ) (hg : ∀ u, g (2 * π - u) = g u)
    (hint : IntervalIntegrable (fun u => g u * cos (n * u)) volume 0 π) :
    harmonicCos (fun t => V * g (2 * π / T * t)) T n =
      2 * V / π * ∫ u in (0 : ℝ)..π, g u * cos (n * u) := by
  set F : ℝ → ℝ := fun u => g u * cos (n * u) with hF
  have hω : 2 * π / T ≠ 0 := by positivity
  have hsym : ∀ u, F (2 * π - u) = F u := fun u => by
    simp only [hF, hg, mul_sub, cos_nat_mul_two_pi_sub]
  have hint2 : IntervalIntegrable F volume π (2 * π) := by
    have h := hint.comp_sub_left (2 * π)
    simp only [hsym, sub_zero, show 2 * π - π = π by ring] at h
    exact h.symm
  have hhalf : ∫ u in π..2 * π, F u = ∫ u in (0 : ℝ)..π, F u := by
    calc ∫ u in π..2 * π, F u = ∫ u in (2 * π - π)..(2 * π - 0), F u := by
          rw [show 2 * π - π = π by ring, sub_zero]
      _ = ∫ u in (0 : ℝ)..π, F (2 * π - u) :=
          (intervalIntegral.integral_comp_sub_left F (2 * π)).symm
      _ = ∫ u in (0 : ℝ)..π, F u := by simp_rw [hsym]
  have hpt : ∀ t, V * g (2 * π / T * t) * cos (n * (2 * π / T) * t) =
      V * F (2 * π / T * t) := fun t => by
    simp only [hF]
    ring_nf
  rw [harmonicCos]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left F hω,
    mul_zero, show 2 * π / T * T = 2 * π by field_simp,
    ← intervalIntegral.integral_add_adjacent_intervals hint hint2, hhalf, smul_eq_mul]
  field_simp
  ring

/-- `∫_{π−α}^{π} cos(nu) du = (−1)ⁿ ∫₀^α cos(nu) du`. -/
@[tmio T, powerlib_foundation] private lemma integral_cos_nat_mul_reflect (n : ℕ) (α : ℝ) :
    ∫ u in (π - α)..π, cos (n * u) = (-1) ^ n * ∫ u in (0 : ℝ)..α, cos (n * u) := by
  have h := intervalIntegral.integral_comp_sub_left (fun u => cos ((n : ℝ) * u)) π (a := 0)
    (b := α)
  simp only [sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1
  ext u
  rw [mul_sub, cos_nat_mul_pi_sub]

/-- `∫₀^α cos(nu) du = sin(nα)/n` for `n ≠ 0`. -/
@[tmio T, powerlib_foundation] private lemma integral_cos_nat_mul_eq {n : ℕ} (hn : n ≠ 0)
    (α : ℝ) : ∫ u in (0 : ℝ)..α, cos (n * u) = sin (n * α) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [intervalIntegral.integral_comp_mul_left (fun u => cos u) hn', integral_cos, mul_zero,
    sin_zero, sub_zero, smul_eq_mul]
  field_simp

/-- A three-level profile on `[0, π]`: `cos(nu)` on `(0, α)`, `0` on `(α, π − α)`, `−cos(nu)` on
`(π − α, π)` integrates to `(1 − (−1)ⁿ) ∫₀^α cos(nu) du`. -/
@[tmio T, powerlib_foundation] private lemma integral_profile {F : ℝ → ℝ} {α : ℝ} (n : ℕ)
    (h0 : 0 ≤ α) (h1 : α ≤ π - α) (hA : EqOn (fun u => cos (n * u)) F (Ioo 0 α))
    (hB : EqOn (fun _ => 0) F (Ioo α (π - α)))
    (hC : EqOn (fun u => -cos (n * u)) F (Ioo (π - α) π)) :
    IntervalIntegrable F volume 0 π ∧
      ∫ u in (0 : ℝ)..π, F u = (1 - (-1) ^ n) * ∫ u in (0 : ℝ)..α, cos (n * u) := by
  have h2 : π - α ≤ π := by linarith
  have iA : IntervalIntegrable F volume 0 α :=
    (Continuous.intervalIntegrable (u := fun u => cos (n * u)) (by fun_prop) _ _).congr_uIoo
      (by rwa [uIoo_of_le h0])
  have iB : IntervalIntegrable F volume α (π - α) :=
    intervalIntegrable_const.congr_uIoo (by rwa [uIoo_of_le h1])
  have iC : IntervalIntegrable F volume (π - α) π :=
    (Continuous.intervalIntegrable (u := fun u => -cos (n * u)) (by fun_prop) _ _).congr_uIoo
      (by rwa [uIoo_of_le h2])
  refine ⟨iA.trans (iB.trans iC), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals iA (iB.trans iC),
    ← intervalIntegral.integral_add_adjacent_intervals iB iC,
    ← intervalIntegral.integral_congr_Ioo_of_le h0 hA,
    ← intervalIntegral.integral_congr_Ioo_of_le h1 hB,
    ← intervalIntegral.integral_congr_Ioo_of_le h2 hC,
    intervalIntegral.integral_zero, intervalIntegral.integral_neg, integral_cos_nat_mul_reflect]
  ring

/-- `cos(ω(T − t)) = cos(ωt)` for `ω = 2π/T` (for `T = 0` both sides are `cos 0`). -/
@[tmio T, powerlib_foundation] private lemma cos_two_pi_div_mul_sub (T t : ℝ) :
    cos (2 * π / T * (T - t)) = cos (2 * π / T * t) := by
  rcases eq_or_ne T 0 with hT | hT
  · simp [hT]
  · rw [show 2 * π / T * (T - t) = 2 * π - 2 * π / T * t by field_simp, cos_two_pi_sub]

/-! ## The square wave -/

/-- The cosine harmonics of the square wave: `aₙ = (2V/π)(1 − (−1)ⁿ) ∫₀^{π/2} cos(nu) du`. -/
@[tmio T, powerlib_foundation] private lemma squareWave_harmonicCos {T : ℝ} (hT : 0 < T) (V : ℝ)
    (n : ℕ) : harmonicCos (squareWave V T) T n =
      2 * V / π * ((1 - (-1) ^ n) * ∫ u in (0 : ℝ)..π / 2, cos (n * u)) := by
  set g : ℝ → ℝ := fun u => if 0 ≤ cos u then 1 else -1 with hgdef
  have hsq : squareWave V T = fun t => V * g (2 * π / T * t) := rfl
  have hg : ∀ u, g (2 * π - u) = g u := fun u => by simp only [hgdef, cos_two_pi_sub]
  have hpi := pi_pos
  have hA : EqOn (fun u => cos (n * u)) (fun u => g u * cos (n * u)) (Ioo 0 (π / 2)) := by
    intro u hu
    have hc : 0 ≤ cos u := cos_nonneg_of_mem_Icc ⟨by linarith [hu.1], hu.2.le⟩
    simp only [hgdef, ite_eq_left hc, one_mul]
  have hB : EqOn (fun _ => 0) (fun u => g u * cos (n * u)) (Ioo (π / 2) (π - π / 2)) := by
    intro u hu
    exact absurd hu.2 (by linarith [hu.1])
  have hC : EqOn (fun u => -cos (n * u)) (fun u => g u * cos (n * u)) (Ioo (π - π / 2) π) := by
    intro u hu
    have hc : cos u < 0 := cos_neg_of_pi_div_two_lt_of_lt (by linarith [hu.1]) (by linarith [hu.2])
    simp only [hgdef, ite_eq_right (not_le.mpr hc)]
    ring
  obtain ⟨hint, hI⟩ := integral_profile n (by positivity) (by linarith) hA hB hC
  rw [hsq, harmonicCos_profile hT V n hg hint, hI]

/-- The odd harmonics of the square wave: `aₙ = 4V/(nπ) · (−1)^((n−1)/2)`. -/
@[tmio T, powerlib_foundation] theorem squareWave_harmonicCos_odd {T : ℝ} (hT : 0 < T) (V : ℝ)
    {n : ℕ} (hn : Odd n) :
    harmonicCos (squareWave V T) T n = 4 * V / (n * π) * (-1) ^ ((n - 1) / 2) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [squareWave_harmonicCos hT, integral_cos_nat_mul_eq hn0, hn.neg_one_pow]
  obtain ⟨k, rfl⟩ := hn
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  have hs : sin (((2 * k + 1 : ℕ) : ℝ) * (π / 2)) = (-1) ^ k := by
    rw [show (((2 * k + 1 : ℕ) : ℝ) * (π / 2)) = k * π + π / 2 by push_cast; ring,
      sin_add_pi_div_two, cos_nat_mul_pi]
  rw [hk, hs]
  field_simp
  ring

/-- The even harmonics of the square wave vanish (including the mean value, `n = 0`). -/
@[tmio T, powerlib_foundation] theorem squareWave_harmonicCos_even {T : ℝ} (hT : 0 < T) (V : ℝ)
    {n : ℕ} (hn : Even n) : harmonicCos (squareWave V T) T n = 0 := by
  rw [squareWave_harmonicCos hT, hn.neg_one_pow, sub_self, zero_mul, mul_zero]

/-- The square wave has no sine harmonics. -/
@[tmio T, powerlib_foundation] theorem squareWave_harmonicSin (V T : ℝ) (n : ℕ) :
    harmonicSin (squareWave V T) T n = 0 :=
  harmonicSin_eq_zero_of_symm (fun t => by simp only [squareWave, cos_two_pi_div_mul_sub]) n

/-- The `n`-th harmonic of the square wave has amplitude `4|V|/(nπ)` for odd `n`: the fundamental
divided by `n`. -/
@[tmio T, powerlib_foundation] theorem squareWave_harmonic {T : ℝ} (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : Odd n) :
    √(harmonicCos (squareWave V T) T n ^ 2 + harmonicSin (squareWave V T) T n ^ 2) =
      4 * |V| / (n * π) := by
  rw [squareWave_harmonicCos_odd hT V hn, squareWave_harmonicSin, zero_pow two_ne_zero, add_zero,
    sqrt_sq_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (mul_pos (Nat.cast_pos.mpr hn.pos) pi_pos)]

/-! ## The quasi-square wave -/

/-- The cosine harmonics of the quasi-square wave:
`aₙ = (2V/π)(1 − (−1)ⁿ) ∫₀^{θ/2} cos(nu) du` for `0 ≤ θ ≤ π`. -/
@[tmio T, powerlib_foundation] private lemma quasiSquareWave_harmonicCos {T θ : ℝ} (hT : 0 < T)
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ π) (V : ℝ) (n : ℕ) :
    harmonicCos (quasiSquareWave V T θ) T n =
      2 * V / π * ((1 - (-1) ^ n) * ∫ u in (0 : ℝ)..θ / 2, cos (n * u)) := by
  set c := cos (θ / 2) with hcdef
  set g : ℝ → ℝ := fun u => if c < cos u then 1 else if cos u < -c then -1 else 0 with hgdef
  have hq : quasiSquareWave V T θ = fun t => V * g (2 * π / T * t) := rfl
  have hg : ∀ u, g (2 * π - u) = g u := fun u => by simp only [hgdef, cos_two_pi_sub]
  have hpi := pi_pos
  have hc0 : 0 ≤ c := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hcπ : cos (π - θ / 2) = -c := cos_pi_sub _
  have hA : EqOn (fun u => cos (n * u)) (fun u => g u * cos (n * u)) (Ioo 0 (θ / 2)) := by
    intro u hu
    have h : c < cos u := cos_lt_cos_of_nonneg_of_le_pi hu.1.le (by linarith) hu.2
    simp only [hgdef, ite_eq_left h, one_mul]
  have hB : EqOn (fun _ => 0) (fun u => g u * cos (n * u)) (Ioo (θ / 2) (π - θ / 2)) := by
    intro u hu
    have h1 : cos u < c := cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [hu.2]) hu.1
    have h2 : -c < cos u := hcπ ▸ cos_lt_cos_of_nonneg_of_le_pi (by linarith [hu.1])
      (by linarith) hu.2
    simp only [hgdef, ite_eq_right (not_lt.mpr h1.le), ite_eq_right (not_lt.mpr h2.le), zero_mul]
  have hC : EqOn (fun u => -cos (n * u)) (fun u => g u * cos (n * u)) (Ioo (π - θ / 2) π) := by
    intro u hu
    have h1 : cos u < -c := hcπ ▸ cos_lt_cos_of_nonneg_of_le_pi (by linarith) hu.2.le hu.1
    simp only [hgdef, ite_eq_right (not_lt.mpr (by linarith : cos u ≤ c)), ite_eq_left h1]
    ring
  obtain ⟨hint, hI⟩ := integral_profile n (by positivity) (by linarith) hA hB hC
  rw [hq, harmonicCos_profile hT V n hg hint, hI]

/-- The odd harmonics of the quasi-square wave: `aₙ = 4V/(nπ) · sin(nθ/2)` for `0 ≤ θ ≤ π`. -/
@[tmio T, powerlib_foundation] theorem quasiSquareWave_harmonicCos_odd {T θ : ℝ} (hT : 0 < T)
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ π) (V : ℝ) {n : ℕ} (hn : Odd n) :
    harmonicCos (quasiSquareWave V T θ) T n = 4 * V / (n * π) * sin (n * θ / 2) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [quasiSquareWave_harmonicCos hT hθ₀ hθ, integral_cos_nat_mul_eq hn0, hn.neg_one_pow,
    mul_div_assoc']
  field_simp
  ring

/-- The even harmonics of the quasi-square wave vanish (including the mean value, `n = 0`). -/
@[tmio T, powerlib_foundation] theorem quasiSquareWave_harmonicCos_even {T θ : ℝ} (hT : 0 < T)
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ π) (V : ℝ) {n : ℕ} (hn : Even n) :
    harmonicCos (quasiSquareWave V T θ) T n = 0 := by
  rw [quasiSquareWave_harmonicCos hT hθ₀ hθ, hn.neg_one_pow, sub_self, zero_mul, mul_zero]

/-- The quasi-square wave has no sine harmonics. -/
@[tmio T, powerlib_foundation] theorem quasiSquareWave_harmonicSin (V T θ : ℝ) (n : ℕ) :
    harmonicSin (quasiSquareWave V T θ) T n = 0 :=
  harmonicSin_eq_zero_of_symm (fun t => by simp only [quasiSquareWave, cos_two_pi_div_mul_sub]) n

/-- The `n`-th harmonic of the quasi-square wave has amplitude `4|V|/(nπ) · |sin(nθ/2)|` for
odd `n`. -/
@[tmio T, powerlib_foundation] theorem quasiSquareWave_harmonic {T θ : ℝ} (hT : 0 < T)
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ π) (V : ℝ) {n : ℕ} (hn : Odd n) :
    √(harmonicCos (quasiSquareWave V T θ) T n ^ 2 +
        harmonicSin (quasiSquareWave V T θ) T n ^ 2) = 4 * |V| / (n * π) * |sin (n * θ / 2)| := by
  rw [quasiSquareWave_harmonicCos_odd hT hθ₀ hθ V hn, quasiSquareWave_harmonicSin,
    zero_pow two_ne_zero, add_zero, sqrt_sq_eq_abs, abs_mul, abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (mul_pos (Nat.cast_pos.mpr hn.pos) pi_pos)]

/-- Every harmonic `n ≠ 0` of the quasi-square wave has amplitude at most `4|V|/(nπ)`. -/
@[tmio T, powerlib_foundation] theorem quasiSquareWave_harmonic_le {T θ : ℝ} (hT : 0 < T)
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ π) (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    √(harmonicCos (quasiSquareWave V T θ) T n ^ 2 +
        harmonicSin (quasiSquareWave V T θ) T n ^ 2) ≤ 4 * |V| / (n * π) := by
  have hpos : 0 ≤ 4 * |V| / (n * π) := by positivity
  rcases Nat.even_or_odd n with he | ho
  · rw [quasiSquareWave_harmonicCos_even hT hθ₀ hθ V he, quasiSquareWave_harmonicSin,
      zero_pow two_ne_zero, add_zero, sqrt_zero]
    exact hpos
  · rw [quasiSquareWave_harmonic hT hθ₀ hθ V ho]
    exact mul_le_of_le_one_right hpos (abs_sin_le_one _)

/-- The fundamental of the quasi-square wave: `cosCoeff = (4V/π) sin(θ/2)` for `0 ≤ θ ≤ π`. -/
@[tmio T, powerlib_foundation] theorem quasiSquareWave_cosCoeff {T θ : ℝ} (hT : 0 < T)
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ π) (V : ℝ) :
    cosCoeff (quasiSquareWave V T θ) T = 4 * V / π * sin (θ / 2) := by
  rw [← harmonicCos_one, quasiSquareWave_harmonicCos_odd hT hθ₀ hθ V odd_one]
  simp

/-- The fundamental amplitude of the quasi-square wave is `(4|V|/π) sin(θ/2)` for `0 ≤ θ ≤ π`:
phase-shift control scales the square-wave fundamental by `sin(θ/2)`. -/
@[tmio T, powerlib_foundation] theorem quasiSquareWave_fundamental {T θ : ℝ} (hT : 0 < T)
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ π) (V : ℝ) :
    √(cosCoeff (quasiSquareWave V T θ) T ^ 2 + sinCoeff (quasiSquareWave V T θ) T ^ 2) =
      4 * |V| / π * sin (θ / 2) := by
  have h := quasiSquareWave_harmonic hT hθ₀ hθ V odd_one
  rw [harmonicCos_one, harmonicSin_one] at h
  rw [h, Nat.cast_one, one_mul, one_mul,
    abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]

end powerlib.SpecialFunctions
