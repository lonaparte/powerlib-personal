import theorem.PowerSystem.Synchronous.SubharmonicOrbit
import theorem.PowerSystem.Synchronous.LoadedSwing
import theorem.Averaging.PeriodicOrbitConstants

/-! # The loaded half-frequency swing oscillation is a periodic solution of the swing model

(header in progress)

Model boundary.
* x

Source: x

Results.
* x
-/

noncomputable section
namespace powerlib.Synchronous.LoadedSubharmonicOrbit

open Complex Set Filter Topology
open powerlib.Synchronous.OscillationPhasor
open powerlib.ParametricResonance
open powerlib.ParametricResonance.DuffingMathieu (pos vel vdp accel vdpField clampC)
open powerlib.ParametricResonance.QuadraticCubic (phase quadField nearId nearIdDeriv cubicCorr
  secondField)
open powerlib.ParametricResonance.Saturation (ampField ampSystem ampJacobian)
open powerlib.Synchronous.ParametricSaturation (modKs)
open powerlib.Synchronous.LoadedSwing (loadedSwing loadedFreqSq alpha2 alpha3 remainder)
open powerlib.Synchronous.SubharmonicOrbit (realField vdpDeriv)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## The second-order field is `C¹` in the amplitude -/

@[tmio T, powerlib_foundation] private theorem norm_mul_sub_le' {a₁ a₂ b₁ b₂ : ℂ} {r : ℝ}
    (ha₂ : ‖a₂‖ ≤ r) (hb₁ : ‖b₁‖ ≤ r) :
    ‖a₁ * a₂ - b₁ * b₂‖ ≤ r * (‖a₁ - b₁‖ + ‖a₂ - b₂‖) := by
  have e : a₁ * a₂ - b₁ * b₂ = (a₁ - b₁) * a₂ + b₁ * (a₂ - b₂) := by ring
  rw [e]
  calc _ ≤ ‖a₁ - b₁‖ * ‖a₂‖ + ‖b₁‖ * ‖a₂ - b₂‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ ‖a₁ - b₁‖ * r + r * ‖a₂ - b₂‖ := by gcongr
    _ = r * (‖a₁ - b₁‖ + ‖a₂ - b₂‖) := by ring

/-- The coefficient of `h` in the derivative of `cubicCorr`. -/
def cubicCoeffH (α₂ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  -(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ)) * (12 * z ^ 2 * phase ν t ^ 2 +
    40 / 3 * z * (starRingEnd ℂ) z + 4 / 3 * (starRingEnd ℂ) z ^ 2 * (phase ν t)⁻¹ ^ 2)

/-- The coefficient of `h̄` in the derivative of `cubicCorr`. -/
def cubicCoeffC (α₂ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  -(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ)) * (20 / 3 * z ^ 2 +
    8 / 3 * z * (starRingEnd ℂ) z * (phase ν t)⁻¹ ^ 2 - 4 * (starRingEnd ℂ) z ^ 2 * (phase ν t)⁻¹ ^ 4)

/-- The (real-linear) derivative of `w ↦ cubicCorr α₂ ν w t`:
`h ↦ cubicCoeffH · h + cubicCoeffC · h̄`. -/
def cubicDeriv (α₂ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  cubicCoeffH α₂ ν z t • ContinuousLinearMap.id ℝ ℂ +
    cubicCoeffC α₂ ν z t • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[tmio T, powerlib_foundation] theorem cubicDeriv_apply (α₂ ν : ℝ) (z : ℂ) (t : ℝ) (h : ℂ) :
    cubicDeriv α₂ ν z t h = cubicCoeffH α₂ ν z t * h + cubicCoeffC α₂ ν z t * (starRingEnd ℂ) h := by
  simp [cubicDeriv]

/-- **The second-order cubic term is differentiable in the amplitude** with derivative
`cubicDeriv`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_cubicCorr (α₂ ν : ℝ) (w : ℂ) (t : ℝ) :
    HasFDerivAt (fun z => cubicCorr α₂ ν z t) (cubicDeriv α₂ ν w t) w := by
  have hz : HasFDerivAt (fun z : ℂ => z) (ContinuousLinearMap.id ℝ ℂ) w := hasFDerivAt_id w
  have hc : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) z) (Complex.conjCLE : ℂ →L[ℝ] ℂ) w :=
    Complex.conjCLE.hasFDerivAt
  set e := phase ν t with he
  set k := -(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ)) with hk
  have H := (((((hz.pow 3).mul_const (4 * e ^ 2)).add (((hz.pow 2).mul hc).mul_const (20 / 3))).add
    ((hz.mul (hc.pow 2)).mul_const (4 / 3 * e⁻¹ ^ 2))).sub
    ((hc.pow 3).mul_const (4 / 3 * e⁻¹ ^ 4))).const_mul k
  convert H using 1
  · funext z
    simp only [cubicCorr, ← he, ← hk, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    ring
  · ext h
    simp only [cubicDeriv_apply, cubicCoeffH, cubicCoeffC, ← he, ← hk,
      smul_apply, add_apply,
      sub_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
    push_cast
    ring

/-- **The derivative of the second-order cubic term is Lipschitz on discs**: for `‖z‖, ‖y‖ ≤ r`,
`‖cubicDeriv z t − cubicDeriv y t‖ ≤ (5α₂² r/ν³) ‖z − y‖`. -/
@[tmio T, powerlib_foundation] theorem norm_cubicDeriv_sub_le {α₂ ν : ℝ} (hν : 0 < ν) {r : ℝ}
    {z y : ℂ} (hz : ‖z‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖cubicDeriv α₂ ν z t - cubicDeriv α₂ ν y t‖ ≤ 5 * α₂ ^ 2 / ν ^ 3 * r * ‖z - y‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  set d := ‖z - y‖ with hd
  have hzc : ‖(starRingEnd ℂ) z‖ ≤ r := by rwa [Complex.norm_conj]
  have hyc : ‖(starRingEnd ℂ) y‖ ≤ r := by rwa [Complex.norm_conj]
  have hdc : ‖(starRingEnd ℂ) z - (starRingEnd ℂ) y‖ = d := by
    rw [← map_sub, Complex.norm_conj]
  have hp : ‖phase ν t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hpi : ‖(phase ν t)⁻¹‖ = 1 := by rw [norm_inv, hp, inv_one]
  have s1 : ‖z ^ 2 - y ^ 2‖ ≤ 2 * r * d := by
    rw [sq, sq]; refine (norm_mul_sub_le' hz hy).trans (le_of_eq ?_); rw [hd]; ring
  have s2 : ‖z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y‖ ≤ 2 * r * d := by
    refine (norm_mul_sub_le' hzc hy).trans (le_of_eq ?_); rw [hdc, hd]; ring
  have s3 : ‖(starRingEnd ℂ) z ^ 2 - (starRingEnd ℂ) y ^ 2‖ ≤ 2 * r * d := by
    rw [sq, sq]; refine (norm_mul_sub_le' hzc hyc).trans (le_of_eq ?_); rw [hdc]; ring
  have hk : ‖-(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ))‖ = α₂ ^ 2 / (16 * ν ^ 3) := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg
      (by positivity)]
  have hA : ‖cubicCoeffH α₂ ν z t - cubicCoeffH α₂ ν y t‖ ≤
      α₂ ^ 2 / (16 * ν ^ 3) * (12 * (2 * r * d) + 40 / 3 * (2 * r * d) + 4 / 3 * (2 * r * d)) := by
    have e : cubicCoeffH α₂ ν z t - cubicCoeffH α₂ ν y t = -(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ)) *
        (12 * (z ^ 2 - y ^ 2) * phase ν t ^ 2 +
          40 / 3 * (z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y) +
          4 / 3 * ((starRingEnd ℂ) z ^ 2 - (starRingEnd ℂ) y ^ 2) * (phase ν t)⁻¹ ^ 2) := by
      simp only [cubicCoeffH]; ring
    rw [e, norm_mul, hk]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_mul, norm_mul, norm_pow, hp, one_pow, mul_one]
      simp only [Complex.norm_ofNat]; gcongr
    · rw [norm_mul]; simp only [norm_div, Complex.norm_ofNat]; gcongr
    · rw [norm_mul, norm_mul, norm_pow, hpi, one_pow, mul_one]
      simp only [norm_div, Complex.norm_ofNat]; gcongr
  have hB : ‖cubicCoeffC α₂ ν z t - cubicCoeffC α₂ ν y t‖ ≤
      α₂ ^ 2 / (16 * ν ^ 3) * (20 / 3 * (2 * r * d) + 8 / 3 * (2 * r * d) + 4 * (2 * r * d)) := by
    have e : cubicCoeffC α₂ ν z t - cubicCoeffC α₂ ν y t = -(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ)) *
        (20 / 3 * (z ^ 2 - y ^ 2) +
          8 / 3 * (z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y) * (phase ν t)⁻¹ ^ 2 -
          4 * ((starRingEnd ℂ) z ^ 2 - (starRingEnd ℂ) y ^ 2) * (phase ν t)⁻¹ ^ 4) := by
      simp only [cubicCoeffC]; ring
    rw [e, norm_mul, hk]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_mul]; simp only [norm_div, Complex.norm_ofNat]; gcongr
    · rw [norm_mul, norm_mul, norm_pow, hpi, one_pow, mul_one]
      simp only [norm_div, Complex.norm_ofNat]; gcongr
    · rw [norm_mul, norm_mul, norm_pow, hpi, one_pow, mul_one]
      simp only [Complex.norm_ofNat]; gcongr
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [sub_apply, cubicDeriv_apply, cubicDeriv_apply]
  have e : cubicCoeffH α₂ ν z t * h + cubicCoeffC α₂ ν z t * (starRingEnd ℂ) h -
      (cubicCoeffH α₂ ν y t * h + cubicCoeffC α₂ ν y t * (starRingEnd ℂ) h) =
      (cubicCoeffH α₂ ν z t - cubicCoeffH α₂ ν y t) * h +
        (cubicCoeffC α₂ ν z t - cubicCoeffC α₂ ν y t) * (starRingEnd ℂ) h := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc _ ≤ α₂ ^ 2 / (16 * ν ^ 3) * (12 * (2 * r * d) + 40 / 3 * (2 * r * d) +
        4 / 3 * (2 * r * d)) * ‖h‖ + α₂ ^ 2 / (16 * ν ^ 3) * (20 / 3 * (2 * r * d) +
        8 / 3 * (2 * r * d) + 4 * (2 * r * d)) * ‖h‖ := by gcongr
    _ = 5 * α₂ ^ 2 / ν ^ 3 * r * d * ‖h‖ := by field_simp; ring

/-- The derivative of the second-order cubic term is continuous in time. -/
@[tmio T, powerlib_foundation] theorem continuous_cubicDeriv (α₂ ν : ℝ) (w : ℂ) :
    Continuous (cubicDeriv α₂ ν w) := by
  have hp : Continuous fun t : ℝ => phase ν t := by unfold phase; fun_prop
  have hpi : Continuous fun t : ℝ => (phase ν t)⁻¹ :=
    hp.inv₀ fun t => QuadraticCubic.phase_ne_zero ν t
  refine continuous_clm_apply.mpr fun h => ?_
  simp only [cubicDeriv_apply, cubicCoeffH, cubicCoeffC]
  fun_prop

/-- The derivative of the second-order field `secondField = vdpField + cubicCorr`. -/
def secondDeriv (b k₀ k₁ α₂ α₃ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  vdpDeriv b k₀ k₁ α₃ ν z t + cubicDeriv α₂ ν z t

@[tmio T, powerlib_foundation] theorem hasFDerivAt_secondField (b k₀ k₁ α₂ α₃ ν : ℝ) (w : ℂ)
    (t : ℝ) : HasFDerivAt (fun z => secondField b k₀ k₁ α₂ α₃ ν z t)
      (secondDeriv b k₀ k₁ α₂ α₃ ν w t) w :=
  (SubharmonicOrbit.hasFDerivAt_vdpField b k₀ k₁ α₃ ν w t).add (hasFDerivAt_cubicCorr α₂ ν w t)

@[tmio T, powerlib_foundation] theorem norm_secondDeriv_sub_le {b k₀ k₁ α₂ α₃ ν : ℝ}
    (hν : 0 < ν) {r : ℝ} {z y : ℂ} (hz : ‖z‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖secondDeriv b k₀ k₁ α₂ α₃ ν z t - secondDeriv b k₀ k₁ α₂ α₃ ν y t‖ ≤
      (6 * |α₃| / ν + 5 * α₂ ^ 2 / ν ^ 3) * r * ‖z - y‖ := by
  have e : secondDeriv b k₀ k₁ α₂ α₃ ν z t - secondDeriv b k₀ k₁ α₂ α₃ ν y t =
      (vdpDeriv b k₀ k₁ α₃ ν z t - vdpDeriv b k₀ k₁ α₃ ν y t) +
        (cubicDeriv α₂ ν z t - cubicDeriv α₂ ν y t) := by
    simp only [secondDeriv]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := SubharmonicOrbit.norm_vdpDeriv_sub_le (b := b) (k₀ := k₀) (k₁ := k₁) (γ := α₃) hν
    hz hy t
  have h2 := norm_cubicDeriv_sub_le (α₂ := α₂) hν hz hy t
  calc _ ≤ 6 * |α₃| * r / ν * ‖z - y‖ + 5 * α₂ ^ 2 / ν ^ 3 * r * ‖z - y‖ := add_le_add h1 h2
    _ = (6 * |α₃| / ν + 5 * α₂ ^ 2 / ν ^ 3) * r * ‖z - y‖ := by ring

@[tmio T, powerlib_foundation] theorem continuous_secondDeriv (b k₀ k₁ α₂ α₃ ν : ℝ) (w : ℂ) :
    Continuous (secondDeriv b k₀ k₁ α₂ α₃ ν w) :=
  (SubharmonicOrbit.continuous_vdpDeriv b k₀ k₁ α₃ ν w).add (continuous_cubicDeriv α₂ ν w)

/-! ## Bounds of the near-identity transformation and of the inputs on discs -/

@[tmio T, powerlib_foundation] private theorem abs_pos_sub_le₂ (ν : ℝ) (z w : ℂ) (t : ℝ) :
    |pos ν z t - pos ν w t| ≤ ‖z - w‖ := by
  have : pos ν z t - pos ν w t = ((z - w) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re := by
    simp only [pos, sub_mul, Complex.sub_re]
  rw [this]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem abs_pos_le₂ (ν : ℝ) (z : ℂ) (t : ℝ) :
    |pos ν z t| ≤ ‖z‖ := by
  have := abs_pos_sub_le₂ ν z 0 t
  simpa [pos] using this

@[tmio T, powerlib_foundation] private theorem norm_phase₂ (ν t : ℝ) : ‖phase ν t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[tmio T, powerlib_foundation] private theorem norm_phase_inv₂ (ν t : ℝ) :
    ‖(phase ν t)⁻¹‖ = 1 := by
  rw [norm_inv, norm_phase₂, inv_one]

/-- **The near-identity generator is Lipschitz on discs**: for `‖z‖, ‖y‖ ≤ r`,
`‖u(z, t) − u(y, t)‖ ≤ (5|α₂|/(3ν²)) r ‖z − y‖`. -/
@[tmio T, powerlib_foundation] theorem norm_nearId_sub_le {α₂ ν : ℝ} (hν : 0 < ν) {r : ℝ}
    {z y : ℂ} (hz : ‖z‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖nearId α₂ ν z t - nearId α₂ ν y t‖ ≤ 5 * |α₂| / (3 * ν ^ 2) * r * ‖z - y‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  set d := ‖z - y‖ with hd
  have hzc : ‖(starRingEnd ℂ) z‖ ≤ r := by rwa [Complex.norm_conj]
  have hyc : ‖(starRingEnd ℂ) y‖ ≤ r := by rwa [Complex.norm_conj]
  have hdc : ‖(starRingEnd ℂ) z - (starRingEnd ℂ) y‖ = d := by
    rw [← map_sub, Complex.norm_conj]
  have s1 : ‖z ^ 2 - y ^ 2‖ ≤ 2 * r * d := by
    rw [sq, sq]; refine (norm_mul_sub_le' hz hy).trans (le_of_eq ?_); rw [hd]; ring
  have s2 : ‖z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y‖ ≤ 2 * r * d := by
    refine (norm_mul_sub_le' hzc hy).trans (le_of_eq ?_); rw [hdc, hd]; ring
  have s3 : ‖(starRingEnd ℂ) z ^ 2 - (starRingEnd ℂ) y ^ 2‖ ≤ 2 * r * d := by
    rw [sq, sq]; refine (norm_mul_sub_le' hzc hyc).trans (le_of_eq ?_); rw [hdc]; ring
  have hk : ‖((α₂ / (4 * ν ^ 2) : ℝ) : ℂ)‖ = |α₂| / (4 * ν ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * ν ^ 2)]
  have e : nearId α₂ ν z t - nearId α₂ ν y t = ((α₂ / (4 * ν ^ 2) : ℝ) : ℂ) *
      ((z ^ 2 - y ^ 2) * phase ν t -
        2 * (z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y) * (phase ν t)⁻¹ -
        ((starRingEnd ℂ) z ^ 2 - (starRingEnd ℂ) y ^ 2) * (phase ν t)⁻¹ ^ 3 / 3) := by
    simp only [nearId]; ring
  rw [e, norm_mul, hk]
  calc |α₂| / (4 * ν ^ 2) * ‖(z ^ 2 - y ^ 2) * phase ν t -
        2 * (z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y) * (phase ν t)⁻¹ -
        ((starRingEnd ℂ) z ^ 2 - (starRingEnd ℂ) y ^ 2) * (phase ν t)⁻¹ ^ 3 / 3‖
      ≤ |α₂| / (4 * ν ^ 2) * (2 * r * d + 2 * (2 * r * d) + 2 * r * d / 3) := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [norm_mul, norm_phase₂, mul_one]; exact s1
        · rw [norm_mul, norm_mul, norm_phase_inv₂, mul_one]
          simp only [Complex.norm_ofNat]; gcongr
        · rw [norm_div, norm_mul, norm_pow, norm_phase_inv₂, one_pow, mul_one]
          simp only [Complex.norm_ofNat]; gcongr
    _ = 5 * |α₂| / (3 * ν ^ 2) * r * d := by field_simp; ring

/-- `D_z u` is bilinear: the difference at two points and two directions. -/
@[tmio T, powerlib_foundation] theorem nearIdDeriv_sub_sub (α₂ ν : ℝ) (z y : ℂ) (t : ℝ)
    (h k : ℂ) : nearIdDeriv α₂ ν z t h - nearIdDeriv α₂ ν y t k =
      nearIdDeriv α₂ ν (z - y) t h + nearIdDeriv α₂ ν y t (h - k) := by
  simp only [nearIdDeriv, map_sub]; ring

@[tmio T, powerlib_foundation] theorem norm_nearIdDeriv_sub_sub_le {α₂ ν : ℝ} (hν : 0 < ν)
    (z y : ℂ) (t : ℝ) (h k : ℂ) : ‖nearIdDeriv α₂ ν z t h - nearIdDeriv α₂ ν y t k‖ ≤
      5 * |α₂| / (3 * ν ^ 2) * (‖z - y‖ * ‖h‖ + ‖y‖ * ‖h - k‖) := by
  rw [nearIdDeriv_sub_sub]
  refine (norm_add_le _ _).trans ?_
  have h1 := QuadraticCubic.norm_nearIdDeriv_le (α₂ := α₂) hν (z - y) h t
  have h2 := QuadraticCubic.norm_nearIdDeriv_le (α₂ := α₂) hν y (h - k) t
  linarith

/-- The quadratic field is Lipschitz on discs. -/
@[tmio T, powerlib_foundation] theorem norm_quadField_sub_le {α₂ ν : ℝ} (hν : 0 < ν) {r : ℝ}
    {z y : ℂ} (hz : ‖z‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖quadField α₂ ν z t - quadField α₂ ν y t‖ ≤ 2 * |α₂| * r / ν * ‖z - y‖ := by
  have e : quadField α₂ ν z t - quadField α₂ ν y t =
      I / ν * ((α₂ * ((pos ν z t + pos ν y t) * (pos ν z t - pos ν y t)) : ℝ) : ℂ) *
        (phase ν t)⁻¹ := by
    simp only [quadField]; push_cast; ring
  rw [e, norm_mul, norm_mul, norm_phase_inv₂, mul_one, norm_div, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 : |pos ν z t + pos ν y t| ≤ 2 * r := by
    calc _ ≤ |pos ν z t| + |pos ν y t| := abs_add_le _ _
      _ ≤ r + r := add_le_add ((abs_pos_le₂ ν z t).trans hz) ((abs_pos_le₂ ν y t).trans hy)
      _ = 2 * r := by ring
  calc 1 / ν * (|α₂| * (|pos ν z t + pos ν y t| * |pos ν z t - pos ν y t|))
      ≤ 1 / ν * (|α₂| * (2 * r * ‖z - y‖)) := by
        have h2 := abs_pos_sub_le₂ ν z y t
        have hr : 0 ≤ r := (norm_nonneg _).trans hz
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 2 * |α₂| * r / ν * ‖z - y‖ := by field_simp

@[tmio T, powerlib_foundation] theorem norm_quadField_le {α₂ ν : ℝ} (hν : 0 < ν) (z : ℂ)
    (t : ℝ) : ‖quadField α₂ ν z t‖ ≤ |α₂| / ν * ‖z‖ ^ 2 := by
  rw [quadField, norm_mul, norm_mul, norm_phase_inv₂, mul_one, norm_div, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs, abs_mul,
    abs_pow]
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_pos_le₂ ν z t) 2
  calc 1 / ν * (|α₂| * |pos ν z t| ^ 2) ≤ 1 / ν * (|α₂| * ‖z‖ ^ 2) := by gcongr
    _ = |α₂| / ν * ‖z‖ ^ 2 := by ring

/-! ## The loaded remainder is Lipschitz of third order -/

@[tmio T, powerlib_foundation] private theorem abs_cos_quad_le (x : ℝ) :
    |Real.cos x - 1 + x ^ 2 / 2| ≤ x ^ 4 / 6 := by
  have hconv : Convex ℝ (Icc (-|x|) |x|) := convex_Icc _ _
  have hd : ∀ s ∈ Icc (-|x|) |x|, HasDerivWithinAt (fun s => Real.cos s - 1 + s ^ 2 / 2)
      (s - Real.sin s) (Icc (-|x|) |x|) s := by
    intro s _
    have := (((Real.hasDerivAt_cos s).sub_const 1).add ((hasDerivAt_pow 2 s).div_const 2))
    convert this.hasDerivWithinAt using 1
    push_cast; ring
  have hb : ∀ s ∈ Icc (-|x|) |x|, ‖s - Real.sin s‖ ≤ |x| ^ 3 / 6 := by
    intro s hs
    rw [Real.norm_eq_abs]
    refine (Real.abs_sub_sin_le s).trans ?_
    have : |s| ≤ |x| := abs_le.mpr ⟨hs.1, hs.2⟩
    gcongr
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (⟨by linarith [abs_nonneg x], abs_nonneg x⟩ : (0 : ℝ) ∈ Icc (-|x|) |x|)
    (⟨neg_abs_le x, le_abs_self x⟩ : x ∈ Icc (-|x|) |x|)
  simp only [Real.cos_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero, sub_zero, Real.norm_eq_abs] at h
  calc |Real.cos x - 1 + x ^ 2 / 2| ≤ |x| ^ 3 / 6 * |x| := h
    _ = |x| ^ 4 / 6 := by ring
    _ = x ^ 4 / 6 := by
        have : |x| ^ 4 = x ^ 4 := by
          rw [← abs_pow]; exact abs_of_nonneg (by positivity)
        rw [this]

variable {p : Params}

@[tmio M, powerlib_domain] private theorem M_pos₂ (hp : p.Pos) : 0 < p.M := by
  have := hp.H; have := hp.ω₀
  rw [Params.M]; positivity

/-- The Lipschitz constant of the loaded remainder on `|x| ≤ m`. -/
def remLip (p : Params) (δ₀ ε m : ℝ) : ℝ :=
  p.Ks * (1 + |ε|) / p.M * (|Real.sin δ₀| * m ^ 3 / 6 + |Real.cos δ₀| * m ^ 4 / 6) +
    |ε| * (2 * |alpha2 p δ₀| * m + 3 * |alpha3 p δ₀| * m ^ 2)

/-- **The loaded remainder is Lipschitz of third order**: for `|x|, |y| ≤ m`,
`|remainder(x) − remainder(y)| ≤ remLip m |x − y|` with
`remLip m = (K_s(1 + |ε|)/M)(|sin δ₀| m³/6 + |cos δ₀| m⁴/6) + |ε|(2|α₂|m + 3|α₃|m²)`. -/
@[tmio M, powerlib_domain] theorem abs_loadedRemainder_sub_le (hp : p.Pos) (δ₀ ε Ω t : ℝ)
    {x y m : ℝ} (hx : |x| ≤ m) (hy : |y| ≤ m) :
    |remainder p δ₀ ε Ω t x - remainder p δ₀ ε Ω t y| ≤ remLip p δ₀ ε m * |x - y| := by
  have hM := M_pos₂ hp
  have hK := hp.Ks
  have hm : 0 ≤ m := (abs_nonneg _).trans hx
  set g' : ℝ → ℝ := fun s => -(modKs p ε Ω t / p.M) * (Real.sin δ₀ * (s - Real.sin s) +
      Real.cos δ₀ * (Real.cos s - 1 + s ^ 2 / 2)) -
    ε * Real.cos (Ω * t) * (2 * alpha2 p δ₀ * s + 3 * alpha3 p δ₀ * s ^ 2) with hg'
  have hd : ∀ s ∈ Icc (-m) m, HasDerivWithinAt (remainder p δ₀ ε Ω t) (g' s) (Icc (-m) m) s := by
    intro s _
    have h1 := ((Real.hasDerivAt_cos s).sub_const 1).add ((hasDerivAt_pow 2 s).div_const 2)
    have h2 := (Real.hasDerivAt_sin s).sub ((hasDerivAt_id s).sub ((hasDerivAt_pow 3 s).div_const 6))
    have h3 := ((h1.const_mul (Real.sin δ₀)).add (h2.const_mul (Real.cos δ₀))).const_mul
      (-(modKs p ε Ω t / p.M))
    have h4 := (((hasDerivAt_pow 2 s).const_mul (alpha2 p δ₀)).add
      ((hasDerivAt_pow 3 s).const_mul (alpha3 p δ₀))).const_mul (ε * Real.cos (Ω * t))
    have h5 := h3.sub h4
    convert h5.hasDerivWithinAt using 1
    · funext u; simp only [remainder, Pi.add_apply, Pi.sub_apply, id]
    · simp only [hg']; push_cast; ring
  have hcos : |modKs p ε Ω t| ≤ p.Ks * (1 + |ε|) := by
    rw [modKs, abs_mul, abs_of_pos hK]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hK.le
    rw [abs_one, abs_mul]
    have := Real.abs_cos_le_one (Ω * t)
    nlinarith [abs_nonneg ε]
  have hb : ∀ s ∈ Icc (-m) m, ‖g' s‖ ≤ remLip p δ₀ ε m := by
    intro s hs
    have hs' : |s| ≤ m := abs_le.mpr ⟨hs.1, hs.2⟩
    rw [Real.norm_eq_abs, hg']
    have e1 : |s - Real.sin s| ≤ m ^ 3 / 6 :=
      (Real.abs_sub_sin_le s).trans (by gcongr)
    have e2 : |Real.cos s - 1 + s ^ 2 / 2| ≤ m ^ 4 / 6 := by
      refine (abs_cos_quad_le s).trans ?_
      have : s ^ 4 ≤ m ^ 4 := by
        have e : s ^ 4 = |s| ^ 4 := by
          rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
        rw [e]
        gcongr
      linarith
    have e3 : |2 * alpha2 p δ₀ * s + 3 * alpha3 p δ₀ * s ^ 2| ≤
        2 * |alpha2 p δ₀| * m + 3 * |alpha3 p δ₀| * m ^ 2 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_two]; gcongr
      · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_pow]; gcongr
    have e4 : |ε * Real.cos (Ω * t)| ≤ |ε| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have e5 : |Real.sin δ₀ * (s - Real.sin s) + Real.cos δ₀ * (Real.cos s - 1 + s ^ 2 / 2)| ≤
        |Real.sin δ₀| * m ^ 3 / 6 + |Real.cos δ₀| * m ^ 4 / 6 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, mul_div_assoc, mul_div_assoc]
      gcongr
    calc _ ≤ |-(modKs p ε Ω t / p.M) * (Real.sin δ₀ * (s - Real.sin s) +
          Real.cos δ₀ * (Real.cos s - 1 + s ^ 2 / 2))| +
          |ε * Real.cos (Ω * t) * (2 * alpha2 p δ₀ * s + 3 * alpha3 p δ₀ * s ^ 2)| :=
          abs_sub _ _
      _ = |modKs p ε Ω t| / p.M * |Real.sin δ₀ * (s - Real.sin s) +
          Real.cos δ₀ * (Real.cos s - 1 + s ^ 2 / 2)| +
          |ε * Real.cos (Ω * t)| * |2 * alpha2 p δ₀ * s + 3 * alpha3 p δ₀ * s ^ 2| := by
          rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hM]
      _ ≤ p.Ks * (1 + |ε|) / p.M * (|Real.sin δ₀| * m ^ 3 / 6 + |Real.cos δ₀| * m ^ 4 / 6) +
          |ε| * (2 * |alpha2 p δ₀| * m + 3 * |alpha3 p δ₀| * m ^ 2) := by
          gcongr
      _ = remLip p δ₀ ε m := rfl
  have h := (convex_Icc (-m) m).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (⟨neg_le.mpr (by linarith [neg_abs_le y, abs_le.mp hy]), (abs_le.mp hy).2⟩ :
      y ∈ Icc (-m) m) (⟨(abs_le.mp hx).1, (abs_le.mp hx).2⟩ : x ∈ Icc (-m) m)
  simpa only [Real.norm_eq_abs] using h

/-! ## Global solutions of the loaded swing model -/

/-- The loaded swing field `(δ, δ̇) ↦ (δ̇, accel)` is globally Lipschitz (sup norm on `ℝ × ℝ`). -/
@[tmio M, powerlib_domain] theorem loaded_field_lipschitz (hp : p.Pos) (δ₀ ε Ω t : ℝ) :
    LipschitzWith (Real.toNNReal (1 + (p.Ks * (1 + |ε|) + |p.D|) / p.M))
      (fun q : ℝ × ℝ => (q.2, (loadedSwing p δ₀ ε Ω t).accel q.1 q.2)) := by
  have hM := M_pos₂ hp
  have hK := hp.Ks
  set c := (p.Ks * (1 + |ε|) + |p.D|) / p.M with hc
  have hc0 : 0 ≤ c := by positivity
  refine LipschitzWith.of_dist_le_mul fun q q' => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  simp only [Prod.dist_eq, Real.dist_eq]
  have hd1 : |q.1 - q'.1| ≤ max |q.1 - q'.1| |q.2 - q'.2| := le_max_left _ _
  have hd2 : |q.2 - q'.2| ≤ max |q.1 - q'.1| |q.2 - q'.2| := le_max_right _ _
  have hs := Real.abs_sin_sub_sin_le q.1 q'.1
  have hK1 : |modKs p ε Ω t| ≤ p.Ks * (1 + |ε|) := by
    rw [modKs, abs_mul, abs_of_pos hK]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hK.le
    rw [abs_one, abs_mul]
    have := Real.abs_cos_le_one (Ω * t)
    nlinarith [abs_nonneg ε]
  have hacc : |(loadedSwing p δ₀ ε Ω t).accel q.1 q.2 - (loadedSwing p δ₀ ε Ω t).accel q'.1 q'.2| ≤
      c * max |q.1 - q'.1| |q.2 - q'.2| := by
    have e : (loadedSwing p δ₀ ε Ω t).accel q.1 q.2 - (loadedSwing p δ₀ ε Ω t).accel q'.1 q'.2 =
        -(modKs p ε Ω t * (Real.sin q.1 - Real.sin q'.1) + p.D * (q.2 - q'.2)) / p.M := by
      simp only [SwingParams.accel, SwingParams.Pe, loadedSwing, sub_zero, zero_add]
      field_simp; ring
    rw [e, abs_div, abs_neg, abs_of_pos hM, div_le_iff₀ hM]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, hc]
    calc |modKs p ε Ω t| * |Real.sin q.1 - Real.sin q'.1| + |p.D| * |q.2 - q'.2|
        ≤ p.Ks * (1 + |ε|) * max |q.1 - q'.1| |q.2 - q'.2| +
            |p.D| * max |q.1 - q'.1| |q.2 - q'.2| := by
          gcongr
          exact hs.trans hd1
      _ = (p.Ks * (1 + |ε|) + |p.D|) / p.M * max |q.1 - q'.1| |q.2 - q'.2| * p.M := by
          field_simp
  apply max_le
  · calc |q.2 - q'.2| ≤ max |q.1 - q'.1| |q.2 - q'.2| := hd2
      _ ≤ (1 + c) * max |q.1 - q'.1| |q.2 - q'.2| := by nlinarith [abs_nonneg (q.2 - q'.2)]
  · calc _ ≤ c * max |q.1 - q'.1| |q.2 - q'.2| := hacc
      _ ≤ (1 + c) * max |q.1 - q'.1| |q.2 - q'.2| := by nlinarith [abs_nonneg (q.2 - q'.2)]

/-- **Global solutions of the loaded swing model** from every angle and speed at a time `τ`. -/
@[tmio M, powerlib_domain] theorem exists_loaded_solution (hp : p.Pos) (δ₀ ε Ω τ a a' : ℝ) :
    ∃ δ δ' : ℝ → ℝ, δ τ = a ∧ δ' τ = a' ∧ (∀ t, HasDerivAt δ (δ' t) t) ∧
      ∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε Ω t).accel (δ t) (δ' t)) t := by
  have hc : Continuous (Function.uncurry fun (s : ℝ) (q : ℝ × ℝ) =>
      (q.2, (loadedSwing p δ₀ ε Ω (s + τ)).accel q.1 q.2)) := by
    simp only [SwingParams.accel, SwingParams.Pe, loadedSwing, modKs]
    fun_prop
  obtain ⟨q, hq0, hq⟩ := DuffingMathieu.exists_global_solution hc
    (fun s => loaded_field_lipschitz hp δ₀ ε Ω (s + τ)) (a, a')
  refine ⟨fun t => (q (t - τ)).1, fun t => (q (t - τ)).2, by simp [hq0], by simp [hq0],
    fun t => ?_, fun t => ?_⟩
  · have h := (hasFDerivAt_fst.comp_hasDerivAt (t - τ) (hq (t - τ))).comp_sub_const t τ
    simpa using h
  · have h := (hasFDerivAt_snd.comp_hasDerivAt (t - τ) (hq (t - τ))).comp_sub_const t τ
    simpa [sub_add_cancel] using h

/-- **Uniqueness for the loaded swing model on an interval.** -/
@[tmio M, powerlib_domain] theorem loaded_unique_Icc (hp : p.Pos) {δ₀ ε Ω τ T₁ : ℝ}
    {δ₁ δ₁' δ₂ δ₂' : ℝ → ℝ} (h1 : ∀ t ∈ Icc τ T₁, HasDerivAt δ₁ (δ₁' t) t)
    (h1' : ∀ t ∈ Icc τ T₁,
      HasDerivAt δ₁' ((loadedSwing p δ₀ ε Ω t).accel (δ₁ t) (δ₁' t)) t)
    (h2 : ∀ t ∈ Icc τ T₁, HasDerivAt δ₂ (δ₂' t) t)
    (h2' : ∀ t ∈ Icc τ T₁,
      HasDerivAt δ₂' ((loadedSwing p δ₀ ε Ω t).accel (δ₂ t) (δ₂' t)) t)
    (h0 : δ₁ τ = δ₂ τ) (h0' : δ₁' τ = δ₂' τ) : ∀ t ∈ Icc τ T₁, δ₁ t = δ₂ t ∧ δ₁' t = δ₂' t := by
  set v : ℝ → ℝ × ℝ → ℝ × ℝ := fun t q => (q.2, (loadedSwing p δ₀ ε Ω t).accel q.1 q.2) with hv
  have hder : ∀ (a a' : ℝ → ℝ), (∀ t ∈ Icc τ T₁, HasDerivAt a (a' t) t) →
      (∀ t ∈ Icc τ T₁, HasDerivAt a' ((loadedSwing p δ₀ ε Ω t).accel (a t) (a' t)) t) →
      ∀ t ∈ Icc τ T₁, HasDerivAt (fun t => (a t, a' t)) (v t (a t, a' t)) t :=
    fun a a' ha ha' t ht => (ha t ht).prodMk (ha' t ht)
  intro t ht
  have hEq := ODE_solution_unique_of_mem_Icc_right (v := v) (s := fun _ => univ) (a := τ) (b := T₁)
    (f := fun t => (δ₁ t, δ₁' t)) (g := fun t => (δ₂ t, δ₂' t))
    (fun s _ => (loaded_field_lipschitz hp δ₀ ε Ω s).lipschitzOnWith)
    (fun s hs => (hder δ₁ δ₁' h1 h1' s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder δ₁ δ₁' h1 h1' s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    (fun s hs => (hder δ₂ δ₂' h2 h2' s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder δ₂ δ₂' h2 h2' s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun _ _ => mem_univ _) (by simp [h0, h0']) ht
  exact ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩

/-! ## The loaded swing as an equation for the scaled amplitude -/

/-- The loaded remainder read off the scaled amplitude `w`, at the angle `x = √ε Re(w e^{jνt})`. -/
def remW (p : Params) (δ₀ ν ε : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  remainder p δ₀ ε (2 * ν) t (√ε * pos ν w t)

/-- The remainder in van der Pol form, `U = −(j/ν) remainder · e^{−jνt}`. -/
def inputW (p : Params) (δ₀ ν ε : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  -(I / ν * (remW p δ₀ ν ε w t : ℂ) * (phase ν t)⁻¹)

/-- **The loaded swing in the scaled amplitude** `w = z/√ε`:
`ẇ = ε vdpField(w) + √ε quadField(w) + U/√ε` (damping `b`, stiffness `ν² − d`, pump `ω_L²`,
`α₃`; quadratic stiffness `α₂`). -/
def scaledField (p : Params) (δ₀ b d ν ε : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  ε • vdpField b (ν ^ 2 - d) (loadedFreqSq p δ₀) (alpha3 p δ₀) ν w t +
    √ε • quadField (alpha2 p δ₀) ν w t + (√ε)⁻¹ • inputW p δ₀ ν ε w t

@[tmio T, powerlib_foundation] private theorem pos_ofReal_mul₂ (ν s : ℝ) (w : ℂ) (t : ℝ) :
    pos ν ((s : ℂ) * w) t = s * pos ν w t := by
  simp only [pos, mul_assoc, Complex.re_ofReal_mul]

@[tmio T, powerlib_foundation] private theorem vel_ofReal_mul₂ (ν s : ℝ) (w : ℂ) (t : ℝ) :
    vel ν ((s : ℂ) * w) t = s * vel ν w t := by
  simp only [vel, mul_assoc, Complex.im_ofReal_mul]; ring

/-- The scaled field written at the unscaled amplitude `z = √ε w`. -/
@[tmio M, powerlib_domain] private theorem scaledField_eq {δ₀ b d ν ε : ℝ}
    (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) (w : ℂ)
    (t : ℝ) : ((√ε : ℝ) : ℂ) * scaledField p δ₀ b d ν ε w t =
      vdpField (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀) (alpha3 p δ₀) ν
          (((√ε : ℝ) : ℂ) * w) t -
        I / ν * ((-alpha2 p δ₀ * pos ν (((√ε : ℝ) : ℂ) * w) t ^ 2 +
          remainder p δ₀ ε (2 * ν) t (pos ν (((√ε : ℝ) : ℂ) * w) t) : ℝ) : ℂ) *
          Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hss : ((√ε : ℝ) : ℂ) ^ 2 = (ε : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hε.le]
  have hv := DuffingMathieu.vdpField_scaled hε.le b d (loadedFreqSq p δ₀) (alpha3 p δ₀) ν w t
  rw [← hd] at hv
  rw [hb, hd, ← hd, hv]
  have hinv : ((√ε : ℝ) : ℂ) * ((√ε : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs0'
  simp only [scaledField, inputW, remW, quadField, pos_ofReal_mul₂, Complex.real_smul, phase]
  rw [← Complex.exp_neg]
  push_cast
  generalize ((remainder p δ₀ ε (2 * ν) t (√ε * pos ν w t) : ℝ) : ℂ) = R
  linear_combination (-(I / (ν : ℂ) * R * Complex.exp (-((ν : ℂ) * (t : ℂ) * I)))) * hinv

/-- **The scaled amplitude of a loaded swing solution** solves `ẇ = scaledField(w, t)` in the
weakly nonlinear scaling `D/M = εb`, `ω_L² = ν² − εd` (`DuffingMathieu.hasDerivAt_vdp`,
`LoadedSwing.accel_eq`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_scaledAmp (hp : p.Pos) {δ₀ b d ν ε : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) (t : ℝ) :
    HasDerivAt (fun t => ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t - δ₀) (δ' t))
      (scaledField p δ₀ b d ν ε (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t - δ₀) (δ' t)) t) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hx' : ∀ t, HasDerivAt δ' (DuffingMathieu.accel (p.D / p.M) (loadedFreqSq p δ₀)
      (ε * loadedFreqSq p δ₀) (alpha3 p δ₀) ν t (δ t - δ₀) (δ' t) +
        (-alpha2 p δ₀ * (δ t - δ₀) ^ 2 + remainder p δ₀ ε (2 * ν) t (δ t - δ₀))) t := by
    intro t
    have h := hδ' t
    rw [show δ t = δ₀ + (δ t - δ₀) by ring, LoadedSwing.accel_eq hp,
      show 2 * ν / 2 = ν by ring] at h
    convert h using 1; ring
  have hz := DuffingMathieu.hasDerivAt_vdp hν.ne' (x := fun t => δ t - δ₀)
    (fun t => (hδ t).sub_const δ₀) hx' t
  have hw := hz.const_mul ((√ε : ℝ) : ℂ)⁻¹
  convert hw using 1
  have hzw : vdp ν t (δ t - δ₀) (δ' t) =
      ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t - δ₀) (δ' t)) := by field_simp
  have e := scaledField_eq hε hb hd (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t - δ₀) (δ' t)) t
  rw [← hzw, DuffingMathieu.pos_vdp] at e
  rw [← e]
  field_simp

/-! ## The remainder of the transformed amplitude equation -/

@[tmio T, powerlib_foundation] theorem vdpField_sub_coeff (b k₀ k₁ k₁' γ γ' ν : ℝ) (z : ℂ)
    (t : ℝ) : vdpField b k₀ k₁ γ ν z t - vdpField b k₀ k₁' γ' ν z t =
      vdpField 0 (ν ^ 2) (k₁ - k₁') (γ - γ') ν z t := by
  simp only [vdpField, accel]; push_cast; ring

@[tmio T, powerlib_foundation] theorem cubicCorr_eq_sq_mul (α₂ ν : ℝ) (z : ℂ) (t : ℝ) :
    cubicCorr α₂ ν z t = ((α₂ ^ 2 : ℝ) : ℂ) * cubicCorr 1 ν z t := by
  simp only [cubicCorr]; push_cast; ring

/-- **A change of the pump, cubic and quadratic coefficients of the second-order field** is
Lipschitz on discs with a constant linear in the coefficient changes. -/
@[tmio T, powerlib_foundation] theorem norm_secondField_coeff_sub_le {b k₀ k₁ k₁' α₂ α₂' α₃ α₃'
    ν : ℝ} (hν : 0 < ν) {r : ℝ} {z y : ℂ} (hz : ‖z‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖(secondField b k₀ k₁ α₂ α₃ ν z t - secondField b k₀ k₁' α₂' α₃' ν z t) -
        (secondField b k₀ k₁ α₂ α₃ ν y t - secondField b k₀ k₁' α₂' α₃' ν y t)‖ ≤
      ((|k₁ - k₁'| + 3 * |α₃ - α₃'| * r ^ 2) / ν + |α₂ ^ 2 - α₂' ^ 2| * (5 / (2 * ν ^ 3)) * r ^ 2) *
        ‖z - y‖ := by
  have e : ∀ x : ℂ, secondField b k₀ k₁ α₂ α₃ ν x t - secondField b k₀ k₁' α₂' α₃' ν x t =
      vdpField 0 (ν ^ 2) (k₁ - k₁') (α₃ - α₃') ν x t +
        ((α₂ ^ 2 - α₂' ^ 2 : ℝ) : ℂ) * cubicCorr 1 ν x t := by
    intro x
    rw [← vdpField_sub_coeff b k₀ k₁ k₁' α₃ α₃' ν x t]
    simp only [secondField, cubicCorr_eq_sq_mul α₂, cubicCorr_eq_sq_mul α₂']
    push_cast; ring
  rw [e z, e y]
  have h1 := DuffingMathieu.norm_vdpField_sub_le (b := 0) (k₀ := ν ^ 2) (k₁ := k₁ - k₁')
    (γ := α₃ - α₃') hν hz hy t
  have h2 := QuadraticCubic.norm_cubicCorr_sub_le (α₂ := 1) hν hz hy t
  have e2 : vdpField 0 (ν ^ 2) (k₁ - k₁') (α₃ - α₃') ν z t +
      ((α₂ ^ 2 - α₂' ^ 2 : ℝ) : ℂ) * cubicCorr 1 ν z t -
      (vdpField 0 (ν ^ 2) (k₁ - k₁') (α₃ - α₃') ν y t +
        ((α₂ ^ 2 - α₂' ^ 2 : ℝ) : ℂ) * cubicCorr 1 ν y t) =
      (vdpField 0 (ν ^ 2) (k₁ - k₁') (α₃ - α₃') ν z t -
        vdpField 0 (ν ^ 2) (k₁ - k₁') (α₃ - α₃') ν y t) +
      ((α₂ ^ 2 - α₂' ^ 2 : ℝ) : ℂ) * (cubicCorr 1 ν z t - cubicCorr 1 ν y t) := by ring
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp only [sub_self, abs_zero, mul_zero, add_zero, zero_add, one_pow, mul_one] at h1 h2
  calc _ ≤ (|k₁ - k₁'| + 3 * |α₃ - α₃'| * r ^ 2) / ν * ‖z - y‖ +
        |α₂ ^ 2 - α₂' ^ 2| * (5 / (2 * ν ^ 3) * r ^ 2 * ‖z - y‖) := by gcongr
    _ = _ := by ring

/-- The cut-off second-order field is differentiable inside the clamp. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_cutSecond {b k₀ k₁ α₂ α₃ ν ρc : ℝ} {x : ℂ}
    (hx : ‖x‖ < ρc) (t : ℝ) :
    HasFDerivAt (fun y => QuadraticCubic.cutSecond b k₀ k₁ α₂ α₃ ν ρc y t)
      (secondDeriv b k₀ k₁ α₂ α₃ ν x t) x := by
  refine (hasFDerivAt_secondField b k₀ k₁ α₂ α₃ ν x t).congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds x (sub_pos.mpr hx)] with z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  simp only [QuadraticCubic.cutSecond]
  rw [DuffingMathieu.clampC_of_norm_le]
  have := norm_le_norm_add_norm_sub' z x
  linarith [norm_sub_rev z x]

@[tmio T, powerlib_foundation] private theorem inv_sqrt_mul_sq {ε : ℝ} (hε : 0 < ε) (X : ℝ) :
    (√ε)⁻¹ * (ε ^ 2 * X) = ε * √ε * X := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have h2 : ε ^ 2 = ε * √ε * √ε := by rw [mul_assoc, hss, sq]
  rw [h2]; field_simp

/-- The remainder of the transformed amplitude equation relative to the limit second-order field
`F⁰ = secondField b (ν² − d) k₁⁰ α₂⁰ α₃⁰ ν`: `ε F(w) − ε√ε D_z u(w)[vdpField(w)] + U/√ε − D_z u(w)[U]
− ε F⁰(w − √ε u(w))`, with the actual coefficients `k₁, α₂, α₃` in `F`, `u` and `vdpField`. -/
def transRem (b d k₁ α₂ α₃ k10 a20 a30 ν ε : ℝ) (U : ℂ → ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  ε • secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν w t -
    (ε * √ε) • nearIdDeriv α₂ ν w t (vdpField b (ν ^ 2 - d) k₁ α₃ ν w t) +
    ((√ε)⁻¹ • U w t - nearIdDeriv α₂ ν w t (U w t)) -
    ε • secondField b (ν ^ 2 - d) k10 a20 a30 ν (w - √ε • nearId α₂ ν w t) t

/-- **The remainder of the transformed amplitude equation is of order `ε^{3/2}`, with a Lipschitz
constant of order `ε^{3/2}`**, on the disc `‖w‖ ≤ r`, uniformly in `0 < ε ≤ 1` and in the
coefficients: if the actual coefficients differ from the limit ones by `O(ε)`
(`|k₁ − k₁⁰| ≤ εK₁`, `|α₂² − α₂⁰²| ≤ εK₂`, `|α₃ − α₃⁰| ≤ εK₃`), are bounded
(`|α₂| ≤ A₂`, `|α₃| ≤ A₃`, `|k₁| ≤ K₀`) and the input is of order `ε²` with an `ε²`-Lipschitz
constant, then `‖transRem‖ ≤ ε√ε M_q` and `‖transRem(w) − transRem(w')‖ ≤ ε√ε L_q ‖w − w'‖`. -/
@[tmio T, powerlib_foundation] theorem transRem_bounds {ν : ℝ} (hν : 0 < ν)
    (b d k10 a20 a30 r K1 K2 K3 A2 A3 K0 mu lu : ℝ) (hr : 0 ≤ r) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hmu : 0 ≤ mu) (hlu : 0 ≤ lu) :
    ∃ Mq Lq : ℝ, 0 ≤ Mq ∧ 0 ≤ Lq ∧ ∀ ε, 0 < ε → ε ≤ 1 → ∀ (k₁ α₂ α₃ : ℝ) (U : ℂ → ℝ → ℂ),
      |k₁ - k10| ≤ ε * K1 → |α₂ ^ 2 - a20 ^ 2| ≤ ε * K2 → |α₃ - a30| ≤ ε * K3 →
      |α₂| ≤ A2 → |α₃| ≤ A3 → |k₁| ≤ K0 →
      (∀ w t, ‖w‖ ≤ r → ‖U w t‖ ≤ ε ^ 2 * mu) →
      (∀ w w' t, ‖w‖ ≤ r → ‖w'‖ ≤ r → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖) →
      ∀ w w' t, ‖w‖ ≤ r → ‖w'‖ ≤ r →
        ‖transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U w t‖ ≤ ε * √ε * Mq ∧
        ‖transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U w t -
          transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U w' t‖ ≤ ε * √ε * Lq * ‖w - w'‖ := by
  set c₁ := 5 * A2 / (6 * ν ^ 2) with hc₁
  set c₂ := 5 * A2 / (3 * ν ^ 2) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set R' := r + c₁ * r ^ 2 with hR'
  have hR'0 : 0 ≤ R' := by positivity
  set ρ'' := R' + 1 with hρ''
  have hρ''0 : 0 ≤ ρ'' := by positivity
  set ℓF := QuadraticCubic.lipSecond b (ν ^ 2 - d) k10 a20 a30 ν (2 * ρ'') with hℓF
  set L₂ := (6 * |a30| / ν + 5 * a20 ^ 2 / ν ^ 3) * R' with hL₂
  set ℓ₁ := (|d| + K0 + ν * |b| + 3 * A3 * r ^ 2) / ν with hℓ₁
  set CT1 := (K1 + 3 * K3 * r ^ 2) / ν + K2 * (5 / (2 * ν ^ 3)) * r ^ 2 with hCT1
  have hcut := QuadraticCubic.cutSecond_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := k10) (α₂ := a20)
    (α₃ := a30) hν hρ''0
  have hℓF0 : 0 ≤ ℓF := hcut.2.1
  have hL₂0 : 0 ≤ L₂ := by positivity
  have hℓ₁0 : 0 ≤ ℓ₁ := by positivity
  have hCT10 : 0 ≤ CT1 := by positivity
  refine ⟨CT1 * r + ℓF * (c₁ * r ^ 2) + c₂ * (r * (ℓ₁ * r)) + mu + c₂ * (r * mu),
    CT1 + (L₂ * ((1 + c₂ * r) * (c₁ * r ^ 2)) + ℓF * (c₂ * r)) + c₂ * (ℓ₁ * r + r * ℓ₁) + lu +
      c₂ * (mu + r * lu), by positivity, by positivity, ?_⟩
  intro ε hε hε1 k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl w w' t hw hw'
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hεs : ε ≤ √ε := by nlinarith
  have hε2 : ε ^ 2 ≤ ε * √ε := by rw [sq]; exact mul_le_mul_of_nonneg_left hεs hε.le
  have hc₁' : 5 * |α₂| / (6 * ν ^ 2) ≤ c₁ := by rw [hc₁]; gcongr
  have hc₂' : 5 * |α₂| / (3 * ν ^ 2) ≤ c₂ := by rw [hc₂]; gcongr
  have hℓ₁' : (|ν ^ 2 - (ν ^ 2 - d)| + |k₁| + ν * |b| + 3 * |α₃| * r ^ 2) / ν ≤ ℓ₁ := by
    rw [hℓ₁, show ν ^ 2 - (ν ^ 2 - d) = d by ring]; gcongr
  -- the pieces
  set F : ℂ → ℂ := fun x => secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν x t with hF
  set F0 : ℂ → ℂ := fun x => secondField b (ν ^ 2 - d) k10 a20 a30 ν x t with hF0
  set V : ℂ → ℂ := fun x => vdpField b (ν ^ 2 - d) k₁ α₃ ν x t with hV
  set Wm : ℂ → ℂ := fun x => x - √ε • nearId α₂ ν x t with hWm
  have hdec : ∀ x, transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U x t =
      ε • (F x - F0 x) + ε • (F0 x - F0 (Wm x)) - (ε * √ε) • nearIdDeriv α₂ ν x t (V x) +
        ((√ε)⁻¹ • U x t - nearIdDeriv α₂ ν x t (U x t)) := by
    intro x; simp only [transRem, hF, hF0, hV, hWm, smul_sub]; abel
  -- bounds of the transformation
  have hu : ∀ x, ‖x‖ ≤ r → ‖x - Wm x‖ ≤ √ε * (c₁ * r ^ 2) := by
    intro x hx
    simp only [hWm, sub_sub_cancel, norm_smul, Real.norm_of_nonneg hs0.le]
    gcongr
    refine (QuadraticCubic.norm_nearId_le hν x t).trans ?_
    exact mul_le_mul hc₁' (pow_le_pow_left₀ (norm_nonneg _) hx 2) (by positivity) hc₁0
  have hWr : ∀ x, ‖x‖ ≤ r → ‖Wm x‖ ≤ R' := by
    intro x hx
    have h1 := hu x hx
    have h3 : √ε * (c₁ * r ^ 2) ≤ c₁ * r ^ 2 := mul_le_of_le_one_left (by positivity) hs1
    calc ‖Wm x‖ = ‖x - (x - Wm x)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖x - Wm x‖ := norm_sub_le _ _
      _ ≤ R' := by rw [hR']; linarith
  have hul : ‖(w - Wm w) - (w' - Wm w')‖ ≤ √ε * (c₂ * r) * ‖w - w'‖ := by
    simp only [hWm, sub_sub_cancel, ← smul_sub, norm_smul, Real.norm_of_nonneg hs0.le]
    rw [mul_assoc]
    gcongr
    refine (norm_nearId_sub_le hν hw hw' t).trans ?_
    gcongr
  have hWl : ‖Wm w - Wm w'‖ ≤ (1 + c₂ * r) * ‖w - w'‖ := by
    have e : Wm w - Wm w' = (w - w') - ((w - Wm w) - (w' - Wm w')) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have : √ε * (c₂ * r) * ‖w - w'‖ ≤ c₂ * r * ‖w - w'‖ := by
      rw [mul_assoc]; exact mul_le_of_le_one_left (by positivity) hs1
    linarith [hul]
  -- the cut-off limit field agrees with `F0` on the disc of radius `R'`
  have hcutF : ∀ x, ‖x‖ ≤ R' → F0 x = QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρ'' x t :=
    fun x hx => by
      simp only [hF0, QuadraticCubic.cutSecond, DuffingMathieu.clampC_of_norm_le (hx.trans
        (by linarith : R' ≤ ρ''))]
  have hc₁r : 0 ≤ c₁ * r ^ 2 := mul_nonneg hc₁0 (sq_nonneg r)
  have hwR : ‖w‖ ≤ R' := by rw [hR']; linarith
  have hw'R : ‖w'‖ ≤ R' := by rw [hR']; linarith
  -- the input terms
  have hUw := hU w t hw
  have hUw' := hU w' t hw'
  have hUl' := hUl w w' t hw hw'
  have hVw : ‖V w‖ ≤ ℓ₁ * r := by
    have h := DuffingMathieu.norm_vdpField_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁) (γ := α₃)
      hν hw (by rw [norm_zero]; exact hr) t
    rw [DuffingMathieu.vdpField_zero, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul hℓ₁' hw (norm_nonneg _) hℓ₁0)
  have hVl : ‖V w - V w'‖ ≤ ℓ₁ * ‖w - w'‖ :=
    (DuffingMathieu.norm_vdpField_sub_le hν hw hw' t).trans
      (mul_le_mul_of_nonneg_right hℓ₁' (norm_nonneg _))
  have hDu : ∀ x h, ‖nearIdDeriv α₂ ν x t h‖ ≤ c₂ * (‖x‖ * ‖h‖) := fun x h =>
    (QuadraticCubic.norm_nearIdDeriv_le hν x h t).trans
      (mul_le_mul_of_nonneg_right hc₂' (by positivity))
  have hDul : ∀ h k, ‖nearIdDeriv α₂ ν w t h - nearIdDeriv α₂ ν w' t k‖ ≤
      c₂ * (‖w - w'‖ * ‖h‖ + ‖w'‖ * ‖h - k‖) := fun h k =>
    (norm_nearIdDeriv_sub_sub_le hν w w' t h k).trans
      (mul_le_mul_of_nonneg_right hc₂' (by positivity))
  -- the coefficient change
  have hT1 : ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖(F x - F0 x) - (F y - F0 y)‖ ≤ ε * CT1 * ‖x - y‖ := by
    intro x y hx hy
    refine (norm_secondField_coeff_sub_le hν hx hy t).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hCT1]
    have h1 : (|k₁ - k10| + 3 * |α₃ - a30| * r ^ 2) / ν ≤ ε * ((K1 + 3 * K3 * r ^ 2) / ν) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hν]
      have := mul_le_mul_of_nonneg_right hα₃ (by positivity : (0 : ℝ) ≤ 3 * r ^ 2)
      linarith
    have h2 : |α₂ ^ 2 - a20 ^ 2| * (5 / (2 * ν ^ 3)) * r ^ 2 ≤
        ε * (K2 * (5 / (2 * ν ^ 3)) * r ^ 2) := by
      have hX : 0 ≤ 5 / (2 * ν ^ 3) * r ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hα₂ hX
      calc |α₂ ^ 2 - a20 ^ 2| * (5 / (2 * ν ^ 3)) * r ^ 2 = |α₂ ^ 2 - a20 ^ 2| *
            (5 / (2 * ν ^ 3) * r ^ 2) := by ring
        _ ≤ ε * K2 * (5 / (2 * ν ^ 3) * r ^ 2) := this
        _ = _ := by ring
    linarith
  have hF0z : F 0 - F0 0 = 0 := by
    simp only [hF, hF0, QuadraticCubic.secondField_zero, sub_self]
  -- the second difference of the limit field
  have hD2 := Averaging.second_diff_le (f := QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρ'')
    (Df := secondDeriv b (ν ^ 2 - d) k10 a20 a30 ν) (ystar := 0) (ρ := R') (L₂ := L₂)
    (ℓ := ℓF) (fun x hx t => hasFDerivAt_cutSecond (by rw [sub_zero] at hx; linarith) t)
    (fun x y hx hy t => by
      rw [sub_zero] at hx hy
      exact (norm_secondDeriv_sub_le hν hx hy t).trans (le_of_eq (by rw [hL₂])))
    hcut.2.2.2.2.1 hℓF0 hL₂0 (a := w) (b := Wm w) (c := w') (d := Wm w')
    (by rw [sub_zero]; exact hwR) (by rw [sub_zero]; exact hWr w hw) (by rw [sub_zero]; exact hw'R)
    (by rw [sub_zero]; exact hWr w' hw') (m := (1 + c₂ * r) * ‖w - w'‖)
    (by have := mul_nonneg (mul_nonneg hc₂0 hr) (norm_nonneg (w - w')); linarith) hWl t
  rw [← hcutF w hwR, ← hcutF (Wm w) (hWr w hw), ← hcutF w' hw'R,
    ← hcutF (Wm w') (hWr w' hw')] at hD2
  clear_value F F0 V Wm
  constructor
  · -- the bound
    rw [hdec w]
    have t1 : ‖ε • (F w - F0 w)‖ ≤ ε * √ε * (CT1 * r) := by
      have h := hT1 w 0 hw (by rw [norm_zero]; exact hr)
      rw [hF0z, sub_zero, sub_zero] at h
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      calc ε * ‖F w - F0 w‖ ≤ ε * (ε * CT1 * r) := by gcongr; exact h.trans (by gcongr)
        _ = ε ^ 2 * (CT1 * r) := by ring
        _ ≤ ε * √ε * (CT1 * r) := by gcongr
    have t2 : ‖ε • (F0 w - F0 (Wm w))‖ ≤ ε * √ε * (ℓF * (c₁ * r ^ 2)) := by
      rw [norm_smul, Real.norm_of_nonneg hε.le, hcutF w hwR, hcutF (Wm w) (hWr w hw)]
      have h := hcut.2.2.2.2.1 w (Wm w) t
      calc ε * ‖_‖ ≤ ε * (ℓF * (√ε * (c₁ * r ^ 2))) := by
            gcongr; exact h.trans (by gcongr; exact hu w hw)
        _ = ε * √ε * (ℓF * (c₁ * r ^ 2)) := by ring
    have t3 : ‖(ε * √ε) • nearIdDeriv α₂ ν w t (V w)‖ ≤ ε * √ε * (c₂ * (r * (ℓ₁ * r))) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      gcongr
      exact (hDu w (V w)).trans (by gcongr)
    have t4 : ‖(√ε)⁻¹ • U w t‖ ≤ ε * √ε * mu := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (√ε)⁻¹ * ‖U w t‖ ≤ (√ε)⁻¹ * (ε ^ 2 * mu) :=
            mul_le_mul_of_nonneg_left hUw (inv_nonneg.mpr hs0.le)
        _ = ε * √ε * mu := inv_sqrt_mul_sq hε mu
    have t5 : ‖nearIdDeriv α₂ ν w t (U w t)‖ ≤ ε * √ε * (c₂ * (r * mu)) := by
      calc _ ≤ c₂ * (‖w‖ * ‖U w t‖) := hDu w (U w t)
        _ ≤ c₂ * (r * (ε ^ 2 * mu)) := by gcongr
        _ = ε ^ 2 * (c₂ * (r * mu)) := by ring
        _ ≤ ε * √ε * (c₂ * (r * mu)) := by gcongr
    calc _ ≤ ‖ε • (F w - F0 w)‖ + ‖ε • (F0 w - F0 (Wm w))‖ +
          ‖(ε * √ε) • nearIdDeriv α₂ ν w t (V w)‖ +
          (‖(√ε)⁻¹ • U w t‖ + ‖nearIdDeriv α₂ ν w t (U w t)‖) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            (norm_add_le _ _) le_rfl)) (norm_sub_le _ _))
      _ ≤ _ := by linarith only [t1, t2, t3, t4, t5]
  · -- the Lipschitz bound
    rw [hdec w, hdec w']
    have e : ε • (F w - F0 w) + ε • (F0 w - F0 (Wm w)) - (ε * √ε) • nearIdDeriv α₂ ν w t (V w) +
        ((√ε)⁻¹ • U w t - nearIdDeriv α₂ ν w t (U w t)) -
        (ε • (F w' - F0 w') + ε • (F0 w' - F0 (Wm w')) -
          (ε * √ε) • nearIdDeriv α₂ ν w' t (V w') +
          ((√ε)⁻¹ • U w' t - nearIdDeriv α₂ ν w' t (U w' t))) =
        ε • ((F w - F0 w) - (F w' - F0 w')) + ε • ((F0 w - F0 (Wm w)) - (F0 w' - F0 (Wm w'))) -
          (ε * √ε) • (nearIdDeriv α₂ ν w t (V w) - nearIdDeriv α₂ ν w' t (V w')) +
          ((√ε)⁻¹ • (U w t - U w' t) -
            (nearIdDeriv α₂ ν w t (U w t) - nearIdDeriv α₂ ν w' t (U w' t))) := by
      simp only [smul_sub]; abel
    rw [e]
    set Δ := ‖w - w'‖ with hΔ
    have t1 : ‖ε • ((F w - F0 w) - (F w' - F0 w'))‖ ≤ ε * √ε * CT1 * Δ := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      calc ε * ‖_‖ ≤ ε * (ε * CT1 * Δ) := by gcongr; exact hT1 w w' hw hw'
        _ = ε ^ 2 * CT1 * Δ := by ring
        _ ≤ ε * √ε * CT1 * Δ := by gcongr
    have t2 : ‖ε • ((F0 w - F0 (Wm w)) - (F0 w' - F0 (Wm w')))‖ ≤
        ε * √ε * (L₂ * ((1 + c₂ * r) * (c₁ * r ^ 2)) + ℓF * (c₂ * r)) * Δ := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      have h := hD2
      have hu' := hu w hw
      calc ε * ‖_‖ ≤ ε * (L₂ * ((1 + c₂ * r) * Δ) * (√ε * (c₁ * r ^ 2)) +
            ℓF * (√ε * (c₂ * r) * Δ)) := by
            apply mul_le_mul_of_nonneg_left _ hε.le
            refine h.trans (add_le_add ?_ ?_)
            · have h1 : 0 ≤ 1 + c₂ * r := add_nonneg zero_le_one (mul_nonneg hc₂0 hr)
              exact mul_le_mul_of_nonneg_left hu' (mul_nonneg hL₂0 (mul_nonneg h1 (norm_nonneg _)))
            · exact mul_le_mul_of_nonneg_left hul hℓF0
        _ = ε * √ε * (L₂ * ((1 + c₂ * r) * (c₁ * r ^ 2)) + ℓF * (c₂ * r)) * Δ := by ring
    have t3 : ‖(ε * √ε) • (nearIdDeriv α₂ ν w t (V w) - nearIdDeriv α₂ ν w' t (V w'))‖ ≤
        ε * √ε * (c₂ * (ℓ₁ * r + r * ℓ₁)) * Δ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc ε * √ε * ‖_‖ ≤ ε * √ε * (c₂ * (Δ * (ℓ₁ * r) + r * (ℓ₁ * Δ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine (hDul (V w) (V w')).trans ?_
            apply mul_le_mul_of_nonneg_left _ hc₂0
            exact add_le_add (mul_le_mul_of_nonneg_left hVw (norm_nonneg _))
              (mul_le_mul hw' hVl (norm_nonneg _) hr)
        _ = ε * √ε * (c₂ * (ℓ₁ * r + r * ℓ₁)) * Δ := by ring
    have t4 : ‖(√ε)⁻¹ • (U w t - U w' t)‖ ≤ ε * √ε * lu * Δ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (√ε)⁻¹ * ‖U w t - U w' t‖ ≤ (√ε)⁻¹ * (ε ^ 2 * lu * Δ) :=
            mul_le_mul_of_nonneg_left hUl' (inv_nonneg.mpr hs0.le)
        _ = ε * √ε * lu * Δ := by
            rw [show ε ^ 2 * lu * Δ = ε ^ 2 * (lu * Δ) by ring, inv_sqrt_mul_sq hε]; ring
    have t5 : ‖nearIdDeriv α₂ ν w t (U w t) - nearIdDeriv α₂ ν w' t (U w' t)‖ ≤
        ε * √ε * (c₂ * (mu + r * lu)) * Δ := by
      have hX : 0 ≤ c₂ * (mu + r * lu) := mul_nonneg hc₂0 (add_nonneg hmu (mul_nonneg hr hlu))
      calc _ ≤ c₂ * (Δ * ‖U w t‖ + ‖w'‖ * ‖U w t - U w' t‖) := hDul _ _
        _ ≤ c₂ * (Δ * (ε ^ 2 * mu) + r * (ε ^ 2 * lu * Δ)) :=
            mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hUw (norm_nonneg _))
              (mul_le_mul hw' hUl' (norm_nonneg _) hr)) hc₂0
        _ = ε ^ 2 * (c₂ * (mu + r * lu)) * Δ := by ring
        _ ≤ ε * √ε * (c₂ * (mu + r * lu)) * Δ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε2 hX) (norm_nonneg _)
    calc _ ≤ ‖ε • ((F w - F0 w) - (F w' - F0 w'))‖ +
          ‖ε • ((F0 w - F0 (Wm w)) - (F0 w' - F0 (Wm w')))‖ +
          ‖(ε * √ε) • (nearIdDeriv α₂ ν w t (V w) - nearIdDeriv α₂ ν w' t (V w'))‖ +
          (‖(√ε)⁻¹ • (U w t - U w' t)‖ +
            ‖nearIdDeriv α₂ ν w t (U w t) - nearIdDeriv α₂ ν w' t (U w' t)‖) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            (norm_add_le _ _) le_rfl)) (norm_sub_le _ _))
      _ ≤ _ := (add_le_add (add_le_add (add_le_add t1 t2) t3) (add_le_add t4 t5)).trans
          (le_of_eq (by ring))

/-! ## Uniform bounds for the machines of the weakly nonlinear scaling -/

/-- **The loaded machine in the scaling** `ω_L² = ν² − εd` (`0 < ε ≤ 1`, `cos δ₀ > 0`):
`K_s/M ≤ (ν² + |d|)/cos δ₀`, `α₂ = −ω_L² tan δ₀/2`, `α₃ = −ω_L²/6`, `0 < ω_L² ≤ ν² + |d|`. -/
@[tmio M, powerlib_domain] theorem machine_bounds (hp : p.Pos) {δ₀ ν d ε : ℝ}
    (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) :
    p.Ks / p.M ≤ (ν ^ 2 + |d|) / Real.cos δ₀ ∧
      alpha2 p δ₀ = -(loadedFreqSq p δ₀ * Real.tan δ₀) / 2 ∧
      alpha3 p δ₀ = -loadedFreqSq p δ₀ / 6 ∧ 0 < loadedFreqSq p δ₀ ∧
      loadedFreqSq p δ₀ ≤ ν ^ 2 + |d| := by
  have hM := M_pos₂ hp
  have hK := hp.Ks
  have hω : 0 < loadedFreqSq p δ₀ := by rw [loadedFreqSq]; positivity
  have hle : loadedFreqSq p δ₀ ≤ ν ^ 2 + |d| := by
    rw [hd]
    have : -(ε * d) ≤ |d| := by
      have h1 : |ε * d| ≤ |d| := by
        rw [abs_mul, abs_of_pos hε]; exact mul_le_of_le_one_left (abs_nonneg _) hε1
      linarith [neg_abs_le (ε * d)]
    linarith
  refine ⟨?_, ?_, ?_, hω, hle⟩
  · rw [le_div_iff₀ hc]
    calc p.Ks / p.M * Real.cos δ₀ = loadedFreqSq p δ₀ := by rw [loadedFreqSq]; ring
      _ ≤ ν ^ 2 + |d| := hle
  · rw [alpha2, loadedFreqSq, Real.tan_eq_sin_div_cos]; field_simp
  · rw [alpha3, loadedFreqSq]; field_simp

/-- The uniform bound `Λ(r)` of the scaled loaded remainder (`|remW| ≤ ε²Λr`, Lipschitz `ε²Λ`). -/
def remConstW (ν d δ₀ r : ℝ) : ℝ :=
  (ν ^ 2 + |d|) / Real.cos δ₀ * (2 * (|Real.sin δ₀| * r ^ 3 / 6 + |Real.cos δ₀| * r ^ 4 / 6) +
    |Real.sin δ₀| * r + r ^ 2 / 2)

/-- **The scaled loaded remainder is of order `ε²`, with an `ε²`-Lipschitz constant**, on the disc
`‖w‖ ≤ r`, uniformly for the machines of the scaling. -/
@[tmio M, powerlib_domain] theorem remW_bounds (hp : p.Pos) {δ₀ ν d ε r : ℝ}
    (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hr : 0 ≤ r) {w w' : ℂ} (hw : ‖w‖ ≤ r) (hw' : ‖w'‖ ≤ r) (t : ℝ) :
    |remW p δ₀ ν ε w t - remW p δ₀ ν ε w' t| ≤ ε ^ 2 * remConstW ν d δ₀ r * ‖w - w'‖ ∧
      |remW p δ₀ ν ε w t| ≤ ε ^ 2 * (remConstW ν d δ₀ r * r) := by
  have hM := M_pos₂ hp
  have hK := hp.Ks
  obtain ⟨hKM, -, -, -, -⟩ := machine_bounds hp hc hε hε1 hd
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  set kM := (ν ^ 2 + |d|) / Real.cos δ₀ with hkM
  have hkM0 : 0 ≤ kM := (div_nonneg hK.le hM.le).trans hKM
  set m := √ε * r with hm
  have hm0 : 0 ≤ m := by positivity
  have hx : ∀ z : ℂ, ‖z‖ ≤ r → |√ε * pos ν z t| ≤ m := fun z hz => by
    rw [abs_mul, abs_of_pos hs0, hm]
    exact mul_le_mul_of_nonneg_left ((abs_pos_le₂ ν z t).trans hz) hs0.le
  -- the Lipschitz constant on `|x| ≤ m`
  have hL : remLip p δ₀ ε m ≤ ε * √ε * remConstW ν d δ₀ r := by
    have hS := abs_nonneg (Real.sin δ₀)
    have hC := abs_nonneg (Real.cos δ₀)
    have ha2 : |alpha2 p δ₀| ≤ kM * |Real.sin δ₀| / 2 := by
      rw [alpha2, abs_div, abs_neg, abs_mul, abs_of_pos hK, abs_of_pos (by positivity : (0:ℝ) < 2 * p.M)]
      rw [show p.Ks * |Real.sin δ₀| / (2 * p.M) = p.Ks / p.M * |Real.sin δ₀| / 2 by field_simp]
      gcongr
    have ha3 : |alpha3 p δ₀| ≤ kM / 6 := by
      rw [alpha3, abs_div, abs_neg, abs_mul, abs_of_pos hK, abs_of_pos (by positivity : (0:ℝ) < 6 * p.M)]
      rw [show p.Ks * |Real.cos δ₀| / (6 * p.M) = p.Ks / p.M * |Real.cos δ₀| / 6 by field_simp]
      have := Real.abs_cos_le_one δ₀
      have h1 : p.Ks / p.M * |Real.cos δ₀| ≤ kM * 1 :=
        mul_le_mul hKM this hC hkM0
      linarith
    have hm2 : m ^ 2 = ε * r ^ 2 := by rw [hm, mul_pow, Real.sq_sqrt hε.le]
    have hm3 : m ^ 3 = ε * √ε * r ^ 3 := by rw [hm, mul_pow, pow_succ, Real.sq_sqrt hε.le]
    have hm4 : m ^ 4 = ε ^ 2 * r ^ 4 := by
      rw [hm, mul_pow, show √ε ^ 4 = (√ε ^ 2) ^ 2 by ring, Real.sq_sqrt hε.le]
    have hεs : ε ≤ √ε := by nlinarith
    have hε2 : ε ^ 2 ≤ ε * √ε := by rw [sq]; exact mul_le_mul_of_nonneg_left hεs hε.le
    rw [remLip, abs_of_pos hε, hm3, hm4, hm2]
    have h1 : p.Ks * (1 + ε) / p.M ≤ 2 * kM := by
      rw [show p.Ks * (1 + ε) / p.M = p.Ks / p.M * (1 + ε) by ring]
      nlinarith [div_nonneg hK.le hM.le]
    have h2 : |Real.sin δ₀| * (ε * √ε * r ^ 3) / 6 + |Real.cos δ₀| * (ε ^ 2 * r ^ 4) / 6 ≤
        ε * √ε * (|Real.sin δ₀| * r ^ 3 / 6 + |Real.cos δ₀| * r ^ 4 / 6) := by
      have : |Real.cos δ₀| * (ε ^ 2 * r ^ 4) / 6 ≤ |Real.cos δ₀| * (ε * √ε * r ^ 4) / 6 := by
        gcongr
      nlinarith
    have h3 : 2 * |alpha2 p δ₀| * m + 3 * |alpha3 p δ₀| * (ε * r ^ 2) ≤
        √ε * (kM * |Real.sin δ₀| * r + kM * r ^ 2 / 2) := by
      have e1 : 2 * |alpha2 p δ₀| * m ≤ √ε * (kM * |Real.sin δ₀| * r) := by
        rw [hm]; nlinarith [mul_le_mul_of_nonneg_right ha2 (mul_nonneg hs0.le hr)]
      have e2 : 3 * |alpha3 p δ₀| * (ε * r ^ 2) ≤ √ε * (kM * r ^ 2 / 2) := by
        have : 3 * |alpha3 p δ₀| ≤ kM / 2 := by linarith
        calc 3 * |alpha3 p δ₀| * (ε * r ^ 2) ≤ kM / 2 * (ε * r ^ 2) := by gcongr
          _ ≤ kM / 2 * (√ε * r ^ 2) := by gcongr
          _ = √ε * (kM * r ^ 2 / 2) := by ring
      linarith
    have hA : 0 ≤ |Real.sin δ₀| * r ^ 3 / 6 + |Real.cos δ₀| * r ^ 4 / 6 := by positivity
    calc p.Ks * (1 + ε) / p.M * (|Real.sin δ₀| * (ε * √ε * r ^ 3) / 6 +
          |Real.cos δ₀| * (ε ^ 2 * r ^ 4) / 6) +
          ε * (2 * |alpha2 p δ₀| * m + 3 * |alpha3 p δ₀| * (ε * r ^ 2))
        ≤ 2 * kM * (ε * √ε * (|Real.sin δ₀| * r ^ 3 / 6 + |Real.cos δ₀| * r ^ 4 / 6)) +
          ε * (√ε * (kM * |Real.sin δ₀| * r + kM * r ^ 2 / 2)) := by
          gcongr
      _ = ε * √ε * remConstW ν d δ₀ r := by rw [remConstW, ← hkM]; ring
  have hlip := abs_loadedRemainder_sub_le hp δ₀ ε (2 * ν) t (hx w hw) (hx w' hw')
  have hpos : |√ε * pos ν w t - √ε * pos ν w' t| ≤ √ε * ‖w - w'‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left (abs_pos_sub_le₂ ν w w' t) hs0.le
  have hRC : 0 ≤ remConstW ν d δ₀ r := by rw [remConstW, ← hkM]; positivity
  have hRL0 : 0 ≤ remLip p δ₀ ε m := by unfold remLip; positivity
  have he2 : ε ^ 2 = ε * √ε * √ε := by rw [mul_assoc, hss, sq]
  constructor
  · calc |remW p δ₀ ν ε w t - remW p δ₀ ν ε w' t|
        ≤ remLip p δ₀ ε m * |√ε * pos ν w t - √ε * pos ν w' t| := hlip
      _ ≤ remLip p δ₀ ε m * (√ε * ‖w - w'‖) := mul_le_mul_of_nonneg_left hpos hRL0
      _ ≤ ε * √ε * remConstW ν d δ₀ r * (√ε * ‖w - w'‖) :=
          mul_le_mul_of_nonneg_right hL (by positivity)
      _ = ε ^ 2 * remConstW ν d δ₀ r * ‖w - w'‖ := by rw [he2]; ring
  · have h0 : remainder p δ₀ ε (2 * ν) t 0 = 0 := by simp [remainder]
    have hlip0 := abs_loadedRemainder_sub_le hp δ₀ ε (2 * ν) t (hx w hw)
      (by rw [abs_zero]; exact hm0 : |(0 : ℝ)| ≤ m)
    rw [h0, sub_zero, sub_zero] at hlip0
    have hx0 : |√ε * pos ν w t| ≤ √ε * r := hx w hw
    calc |remW p δ₀ ν ε w t| ≤ remLip p δ₀ ε m * |√ε * pos ν w t| := hlip0
      _ ≤ ε * √ε * remConstW ν d δ₀ r * (√ε * r) := mul_le_mul hL hx0 (abs_nonneg _) (by positivity)
      _ = ε ^ 2 * (remConstW ν d δ₀ r * r) := by rw [he2]; ring

/-- The uniform speed constant of the scaled loaded field on the disc of radius `r`. -/
def speedConst (b d ν δ₀ r : ℝ) : ℝ :=
  (|d| + (ν ^ 2 + |d|) + ν * |b| + 3 * ((ν ^ 2 + |d|) / 6) * r ^ 2) / ν * r +
    (ν ^ 2 + |d|) * |Real.tan δ₀| / 2 / ν * r ^ 2 + remConstW ν d δ₀ r * r / ν

/-- The uniform Lipschitz constant of the scaled loaded field on the disc of radius `r`. -/
def lipConstW (b d ν δ₀ r : ℝ) : ℝ :=
  (|d| + (ν ^ 2 + |d|) + ν * |b| + 3 * ((ν ^ 2 + |d|) / 6) * r ^ 2) / ν +
    2 * ((ν ^ 2 + |d|) * |Real.tan δ₀| / 2) * r / ν + remConstW ν d δ₀ r / ν

/-- **Bounds of the scaled loaded field on discs**, uniformly for the machines of the scaling:
`‖scaledField(z)‖ ≤ √ε speedConst` and `scaledField` is `lipConstW`-Lipschitz on `‖z‖ ≤ r`. -/
@[tmio M, powerlib_domain] theorem scaledField_bounds (hp : p.Pos) {δ₀ b d ν ε r : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) (hr : 0 ≤ r) {z z' : ℂ} (hz : ‖z‖ ≤ r)
    (hz' : ‖z'‖ ≤ r) (t : ℝ) :
    ‖scaledField p δ₀ b d ν ε z t‖ ≤ √ε * speedConst b d ν δ₀ r ∧
      ‖scaledField p δ₀ b d ν ε z t - scaledField p δ₀ b d ν ε z' t‖ ≤
        lipConstW b d ν δ₀ r * ‖z - z'‖ := by
  obtain ⟨-, h2, h3, hω, hωle⟩ := machine_bounds hp hc hε hε1 hd
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hεs : ε ≤ √ε := by nlinarith [Real.mul_self_sqrt hε.le]
  have hK0 : 0 ≤ ν ^ 2 + |d| := by positivity
  have hA2 : |alpha2 p δ₀| ≤ (ν ^ 2 + |d|) * |Real.tan δ₀| / 2 := by
    rw [h2, abs_div, abs_neg, abs_mul, abs_of_pos hω, abs_two]
    gcongr
  have hA3 : |alpha3 p δ₀| ≤ (ν ^ 2 + |d|) / 6 := by
    rw [h3, abs_div, abs_neg, abs_of_pos hω, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    gcongr
  have hℓ : (|ν ^ 2 - (ν ^ 2 - d)| + |loadedFreqSq p δ₀| + ν * |b| + 3 * |alpha3 p δ₀| * r ^ 2) / ν ≤
      (|d| + (ν ^ 2 + |d|) + ν * |b| + 3 * ((ν ^ 2 + |d|) / 6) * r ^ 2) / ν := by
    rw [show ν ^ 2 - (ν ^ 2 - d) = d by ring, abs_of_pos hω]
    gcongr
  set ℓ₁ := (|d| + (ν ^ 2 + |d|) + ν * |b| + 3 * ((ν ^ 2 + |d|) / 6) * r ^ 2) / ν with hℓ₁
  have hℓ₁0 : 0 ≤ ℓ₁ := by positivity
  obtain ⟨hRl, hRb⟩ := remW_bounds hp hc hε hε1 hd hr hz hz' t
  obtain ⟨-, hRb'⟩ := remW_bounds hp hc hε hε1 hd hr hz' hz' t
  have hRC : 0 ≤ remConstW ν d δ₀ r := by
    rw [remConstW]; have := hc.le; positivity
  have hinv : ∀ x : ℂ, ‖inputW p δ₀ ν ε x t‖ = |remW p δ₀ ν ε x t| / ν := fun x => by
    rw [inputW, norm_neg, norm_mul, norm_mul, norm_phase_inv₂, mul_one, norm_div, Complex.norm_I,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs]
    ring
  have hinvs : ∀ X : ℝ, (√ε)⁻¹ * (ε ^ 2 * X) = ε * √ε * X := fun X => inv_sqrt_mul_sq hε X
  constructor
  · have hV := DuffingMathieu.norm_vdpField_sub_le (b := b) (k₀ := ν ^ 2 - d)
      (k₁ := loadedFreqSq p δ₀) (γ := alpha3 p δ₀) hν hz (by rw [norm_zero]; exact hr) t
    rw [DuffingMathieu.vdpField_zero, sub_zero, sub_zero] at hV
    have hQ := norm_quadField_le (α₂ := alpha2 p δ₀) hν z t
    rw [scaledField]
    calc _ ≤ ε * (ℓ₁ * r) + √ε * ((ν ^ 2 + |d|) * |Real.tan δ₀| / 2 / ν * r ^ 2) +
          (√ε)⁻¹ * (ε ^ 2 * (remConstW ν d δ₀ r * r) / ν) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [norm_smul, Real.norm_of_nonneg hε.le]
            exact mul_le_mul_of_nonneg_left (hV.trans (mul_le_mul hℓ hz (norm_nonneg _) hℓ₁0)) hε.le
          · rw [norm_smul, Real.norm_of_nonneg hs0.le]
            refine mul_le_mul_of_nonneg_left (hQ.trans ?_) hs0.le
            gcongr
          · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs0.le), hinv]
            gcongr
      _ = ε * (ℓ₁ * r) + √ε * ((ν ^ 2 + |d|) * |Real.tan δ₀| / 2 / ν * r ^ 2) +
          ε * √ε * (remConstW ν d δ₀ r * r / ν) := by
          rw [show ε ^ 2 * (remConstW ν d δ₀ r * r) / ν = ε ^ 2 * (remConstW ν d δ₀ r * r / ν) by
            ring, hinvs]
      _ ≤ √ε * (ℓ₁ * r) + √ε * ((ν ^ 2 + |d|) * |Real.tan δ₀| / 2 / ν * r ^ 2) +
          √ε * (remConstW ν d δ₀ r * r / ν) := by
          have h1 : ε * √ε ≤ √ε := mul_le_of_le_one_left hs0.le hε1
          gcongr
      _ = √ε * speedConst b d ν δ₀ r := by rw [speedConst, ← hℓ₁]; ring
  · have hV := DuffingMathieu.norm_vdpField_sub_le (b := b) (k₀ := ν ^ 2 - d)
      (k₁ := loadedFreqSq p δ₀) (γ := alpha3 p δ₀) hν hz hz' t
    have hQ := norm_quadField_sub_le (α₂ := alpha2 p δ₀) hν hz hz' t
    have hU : ‖inputW p δ₀ ν ε z t - inputW p δ₀ ν ε z' t‖ ≤ ε ^ 2 * remConstW ν d δ₀ r *
        ‖z - z'‖ / ν := by
      have e : inputW p δ₀ ν ε z t - inputW p δ₀ ν ε z' t =
          -(I / ν * ((remW p δ₀ ν ε z t - remW p δ₀ ν ε z' t : ℝ) : ℂ) * (phase ν t)⁻¹) := by
        simp only [inputW]; push_cast; ring
      rw [e, norm_neg, norm_mul, norm_mul, norm_phase_inv₂, mul_one, norm_div, Complex.norm_I,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs]
      calc 1 / ν * |remW p δ₀ ν ε z t - remW p δ₀ ν ε z' t| ≤
          1 / ν * (ε ^ 2 * remConstW ν d δ₀ r * ‖z - z'‖) := by gcongr
        _ = _ := by ring
    have e : scaledField p δ₀ b d ν ε z t - scaledField p δ₀ b d ν ε z' t =
        ε • (vdpField b (ν ^ 2 - d) (loadedFreqSq p δ₀) (alpha3 p δ₀) ν z t -
          vdpField b (ν ^ 2 - d) (loadedFreqSq p δ₀) (alpha3 p δ₀) ν z' t) +
        √ε • (quadField (alpha2 p δ₀) ν z t - quadField (alpha2 p δ₀) ν z' t) +
        (√ε)⁻¹ • (inputW p δ₀ ν ε z t - inputW p δ₀ ν ε z' t) := by
      simp only [scaledField, smul_sub]; abel
    rw [e]
    calc _ ≤ ε * (ℓ₁ * ‖z - z'‖) +
          √ε * (2 * ((ν ^ 2 + |d|) * |Real.tan δ₀| / 2) * r / ν * ‖z - z'‖) +
          (√ε)⁻¹ * (ε ^ 2 * (remConstW ν d δ₀ r * ‖z - z'‖ / ν)) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [norm_smul, Real.norm_of_nonneg hε.le]
            exact mul_le_mul_of_nonneg_left (hV.trans (mul_le_mul_of_nonneg_right hℓ
              (norm_nonneg _))) hε.le
          · rw [norm_smul, Real.norm_of_nonneg hs0.le]
            refine mul_le_mul_of_nonneg_left (hQ.trans ?_) hs0.le
            gcongr
          · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
            refine mul_le_mul_of_nonneg_left (hU.trans (le_of_eq ?_)) (inv_nonneg.mpr hs0.le)
            ring
      _ = ε * (ℓ₁ * ‖z - z'‖) +
          √ε * (2 * ((ν ^ 2 + |d|) * |Real.tan δ₀| / 2) * r / ν * ‖z - z'‖) +
          ε * √ε * (remConstW ν d δ₀ r * ‖z - z'‖ / ν) := by rw [hinvs]
      _ ≤ 1 * (ℓ₁ * ‖z - z'‖) + 1 * (2 * ((ν ^ 2 + |d|) * |Real.tan δ₀| / 2) * r / ν * ‖z - z'‖) +
          1 * (remConstW ν d δ₀ r * ‖z - z'‖ / ν) := by
          have h1 : ε * √ε ≤ 1 := by nlinarith
          gcongr
      _ = lipConstW b d ν δ₀ r * ‖z - z'‖ := by rw [lipConstW, ← hℓ₁]; ring

/-! ## The clamped amplitude equation and the clamped near-identity transformation -/

/-- The scaled loaded field read through the clamp `clampC ρc` (globally Lipschitz). -/
def clampField (p : Params) (δ₀ b d ν ε ρc : ℝ) (t : ℝ) (w : ℂ) : ℂ :=
  scaledField p δ₀ b d ν ε (clampC ρc w) t

/-- The clamped near-identity transformation `W = w − √ε u(clamp w, t)`. -/
def Wmap (α₂ ν ε ρc : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  w - √ε • nearId α₂ ν (clampC ρc w) t

@[tmio M, powerlib_domain] theorem continuous_clampField (δ₀ b d ν ε ρc : ℝ) :
    Continuous (Function.uncurry (clampField p δ₀ b d ν ε ρc)) := by
  have hc : Continuous fun q : ℝ × ℂ => clampC ρc q.2 :=
    (DuffingMathieu.continuous_clampC ρc).comp continuous_snd
  have hp : Continuous fun t : ℝ => phase ν t := by unfold phase; fun_prop
  have hpi : Continuous fun t : ℝ => (phase ν t)⁻¹ :=
    hp.inv₀ fun t => QuadraticCubic.phase_ne_zero ν t
  have h1 : Continuous fun q : ℝ × ℂ => vdpField b (ν ^ 2 - d) (loadedFreqSq p δ₀) (alpha3 p δ₀) ν
      (clampC ρc q.2) q.1 := by
    simp only [vdpField, accel, pos, vel]
    fun_prop
  have h2 : Continuous fun q : ℝ × ℂ => quadField (alpha2 p δ₀) ν (clampC ρc q.2) q.1 := by
    simp only [quadField, pos]
    have : Continuous fun q : ℝ × ℂ => (phase ν q.1)⁻¹ := hpi.comp continuous_fst
    fun_prop
  have h3 : Continuous fun q : ℝ × ℂ => inputW p δ₀ ν ε (clampC ρc q.2) q.1 := by
    simp only [inputW, remW, remainder, modKs, pos]
    have : Continuous fun q : ℝ × ℂ => (phase ν q.1)⁻¹ := hpi.comp continuous_fst
    fun_prop
  exact ((h1.const_smul ε).add (h2.const_smul √ε)).add (h3.const_smul (√ε)⁻¹)

/-- The clamped scaled field is globally Lipschitz. -/
@[tmio M, powerlib_domain] theorem clampField_lipschitz (hp : p.Pos) {δ₀ b d ν ε ρc : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) (hρc : 0 ≤ ρc) (t : ℝ) :
    LipschitzWith (Real.toNNReal (lipConstW b d ν δ₀ (2 * ρc))) (clampField p δ₀ b d ν ε ρc t) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h := (scaledField_bounds (b := b) hp hν hc hε hε1 hd (by positivity : (0 : ℝ) ≤ 2 * ρc)
    (DuffingMathieu.norm_clampC_le hρc w) (DuffingMathieu.norm_clampC_le hρc w') t).2
  have hL : 0 ≤ lipConstW b d ν δ₀ (2 * ρc) := by
    rw [lipConstW, remConstW]; have := hc.le; positivity
  rw [Real.coe_toNNReal _ hL]
  exact h.trans (mul_le_mul_of_nonneg_left (DuffingMathieu.norm_clampC_sub_le ρc w w') hL)

/-- The clamped scaled field is slow: `‖clampField‖ ≤ √ε speedConst`. -/
@[tmio M, powerlib_domain] theorem norm_clampField_le (hp : p.Pos) {δ₀ b d ν ε ρc : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) (hρc : 0 ≤ ρc) (t : ℝ) (w : ℂ) :
    ‖clampField p δ₀ b d ν ε ρc t w‖ ≤ √ε * speedConst b d ν δ₀ (2 * ρc) :=
  (scaledField_bounds hp hν hc hε hε1 hd (by positivity : (0 : ℝ) ≤ 2 * ρc)
    (DuffingMathieu.norm_clampC_le hρc w) (DuffingMathieu.norm_clampC_le hρc w) t).1

/-- **Global solutions of the clamped amplitude equation** from every time and amplitude. -/
@[tmio M, powerlib_domain] theorem exists_clamped_solution (hp : p.Pos) {δ₀ b d ν ε ρc : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) (hρc : 0 ≤ ρc) (τ : ℝ) (w₀ : ℂ) :
    ∃ w : ℝ → ℂ, w τ = w₀ ∧ ∀ t, HasDerivAt w (clampField p δ₀ b d ν ε ρc t (w t)) t := by
  have hcont : Continuous (Function.uncurry fun s (y : ℂ) => clampField p δ₀ b d ν ε ρc (s + τ) y) :=
    ((continuous_clampField (p := p) δ₀ b d ν ε ρc).comp
      ((continuous_fst.add (continuous_const (y := τ))).prodMk continuous_snd)).congr
        (fun q => rfl)
  obtain ⟨y, hy0, hy⟩ := DuffingMathieu.exists_global_solution hcont
    (fun s => clampField_lipschitz hp hν hc hε hε1 hd hρc (s + τ)) w₀
  refine ⟨fun t => y (t - τ), by simp [hy0], fun t => ?_⟩
  have h := (hy (t - τ)).comp_sub_const t τ
  rw [sub_add_cancel] at h
  exact h

@[tmio T, powerlib_foundation] private theorem phase_period₂ {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    phase ν (t + 2 * Real.pi / ν) = phase ν t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  rw [phase, phase, show ((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I =
    ((ν * t : ℝ) : ℂ) * I + 2 * Real.pi * I by push_cast; field_simp, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem pos_period₂ {ν : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : pos ν w (t + 2 * Real.pi / ν) = pos ν w t := by
  have := phase_period₂ hν t
  simp only [phase] at this
  simp only [pos, this]

@[tmio T, powerlib_foundation] private theorem vel_period₂ {ν : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : vel ν w (t + 2 * Real.pi / ν) = vel ν w t := by
  have := phase_period₂ hν t
  simp only [phase] at this
  simp only [vel, this]

/-- The clamped scaled field is `2π/ν`-periodic in time. -/
@[tmio M, powerlib_domain] theorem clampField_periodic {δ₀ b d ν ε ρc : ℝ} (hν : 0 < ν)
    (t : ℝ) (w : ℂ) :
    clampField p δ₀ b d ν ε ρc (t + 2 * Real.pi / ν) w = clampField p δ₀ b d ν ε ρc t w := by
  have hcos : Real.cos (2 * ν * (t + 2 * Real.pi / ν)) = Real.cos (2 * ν * t) := by
    rw [show 2 * ν * (t + 2 * Real.pi / ν) = 2 * ν * t + (2 : ℕ) * (2 * Real.pi) by
      push_cast; field_simp]
    exact Real.cos_add_nat_mul_two_pi _ 2
  simp only [clampField, scaledField, inputW, remW, remainder, modKs, quadField,
    DuffingMathieu.vdpField_periodic hν, pos_period₂ hν, phase_period₂ hν, hcos]

/-- The clamped near-identity transformation moves by at most `√ε (5|α₂|/(6ν²)) (2ρc)²`. -/
@[tmio T, powerlib_foundation] theorem norm_Wmap_sub_le {α₂ ν ε ρc : ℝ} (hν : 0 < ν)
    (hρc : 0 ≤ ρc) (w : ℂ) (t : ℝ) :
    ‖Wmap α₂ ν ε ρc w t - w‖ ≤ √ε * (5 * |α₂| / (6 * ν ^ 2) * (2 * ρc) ^ 2) := by
  rw [Wmap, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  exact (QuadraticCubic.norm_nearId_le hν _ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (DuffingMathieu.norm_clampC_le hρc w) 2) (by positivity))

/-- The clamped near-identity transformation is a Lipschitz perturbation of the identity. -/
@[tmio T, powerlib_foundation] theorem norm_Wmap_sub_sub_le {α₂ ν ε ρc : ℝ} (hν : 0 < ν)
    (hρc : 0 ≤ ρc) (w w' : ℂ) (t : ℝ) :
    ‖(Wmap α₂ ν ε ρc w t - Wmap α₂ ν ε ρc w' t) - (w - w')‖ ≤
      √ε * (5 * |α₂| / (3 * ν ^ 2) * (2 * ρc)) * ‖w - w'‖ := by
  have e : (Wmap α₂ ν ε ρc w t - Wmap α₂ ν ε ρc w' t) - (w - w') =
      -(√ε • (nearId α₂ ν (clampC ρc w) t - nearId α₂ ν (clampC ρc w') t)) := by
    simp only [Wmap, smul_sub]; abel
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  gcongr
  refine (norm_nearId_sub_le hν (DuffingMathieu.norm_clampC_le hρc w)
    (DuffingMathieu.norm_clampC_le hρc w') t).trans ?_
  exact mul_le_mul_of_nonneg_left (DuffingMathieu.norm_clampC_sub_le ρc w w') (by positivity)

/-- With `√ε (5|α₂|/(3ν²)) (2ρc) ≤ 1/2` the clamped transformation is bi-Lipschitz:
`‖w − w'‖ ≤ 2 ‖W − W'‖` and `‖W − W'‖ ≤ (3/2) ‖w − w'‖`. -/
@[tmio T, powerlib_foundation] theorem Wmap_bilipschitz {α₂ ν ε ρc : ℝ} (hν : 0 < ν)
    (hρc : 0 ≤ ρc) (hsmall : √ε * (5 * |α₂| / (3 * ν ^ 2) * (2 * ρc)) ≤ 1 / 2) (w w' : ℂ)
    (t : ℝ) : ‖w - w'‖ ≤ 2 * ‖Wmap α₂ ν ε ρc w t - Wmap α₂ ν ε ρc w' t‖ ∧
      ‖Wmap α₂ ν ε ρc w t - Wmap α₂ ν ε ρc w' t‖ ≤ 3 / 2 * ‖w - w'‖ := by
  have h := norm_Wmap_sub_sub_le (α₂ := α₂) (ε := ε) hν hρc w w' t
  have h1 := norm_sub_norm_le (Wmap α₂ ν ε ρc w t - Wmap α₂ ν ε ρc w' t) (w - w')
  have h2 := norm_sub_norm_le (w - w') (Wmap α₂ ν ε ρc w t - Wmap α₂ ν ε ρc w' t)
  rw [norm_sub_rev (w - w')] at h2
  have h3 : √ε * (5 * |α₂| / (3 * ν ^ 2) * (2 * ρc)) * ‖w - w'‖ ≤ 1 / 2 * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  constructor <;> linarith

/-- With `√ε (5|α₂|/(3ν²)) (2ρc) ≤ 1/2` the clamped transformation is onto at every time. -/
@[tmio T, powerlib_foundation] theorem exists_Wmap_eq {α₂ ν ε ρc : ℝ} (hν : 0 < ν)
    (hρc : 0 ≤ ρc) (hsmall : √ε * (5 * |α₂| / (3 * ν ^ 2) * (2 * ρc)) ≤ 1 / 2) (W : ℂ)
    (t : ℝ) : ∃ w, Wmap α₂ ν ε ρc w t = W := by
  set g : ℂ → ℂ := fun w => W + √ε • nearId α₂ ν (clampC ρc w) t with hg
  have hlip : LipschitzWith (1 / 2 : NNReal) g := by
    refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have h := norm_Wmap_sub_sub_le (α₂ := α₂) (ε := ε) hν hρc w w' t
    have e : g w - g w' = -((Wmap α₂ ν ε ρc w t - Wmap α₂ ν ε ρc w' t) - (w - w')) := by
      simp only [hg, Wmap]; abel
    rw [e, norm_neg]
    refine h.trans ?_
    have : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hc : ContractingWith (1 / 2) g := ⟨by norm_num, hlip⟩
  refine ⟨ContractingWith.fixedPoint g hc, ?_⟩
  have hfix : g (ContractingWith.fixedPoint g hc) = ContractingWith.fixedPoint g hc :=
    ContractingWith.fixedPoint_isFixedPt hc
  simp only [hg] at hfix
  calc Wmap α₂ ν ε ρc (ContractingWith.fixedPoint g hc) t =
      (W + √ε • nearId α₂ ν (clampC ρc (ContractingWith.fixedPoint g hc)) t) -
        √ε • nearId α₂ ν (clampC ρc (ContractingWith.fixedPoint g hc)) t := by
        rw [Wmap]; congr 1; exact hfix.symm
    _ = W := add_sub_cancel_right _ _

/-- The clamped transformation is `2π/ν`-periodic in time. -/
@[tmio T, powerlib_foundation] theorem Wmap_periodic {α₂ ν ε ρc : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : Wmap α₂ ν ε ρc w (t + 2 * Real.pi / ν) = Wmap α₂ ν ε ρc w t := by
  simp only [Wmap, nearId, phase_period₂ hν]

/-- The right-hand side of the transformed amplitude equation. -/
def transField (p : Params) (δ₀ b d ν ε : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  ε • secondField b (ν ^ 2 - d) (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν w t -
    (ε * √ε) • nearIdDeriv (alpha2 p δ₀) ν w t
      (vdpField b (ν ^ 2 - d) (loadedFreqSq p δ₀) (alpha3 p δ₀) ν w t) +
    ((√ε)⁻¹ • inputW p δ₀ ν ε w t - nearIdDeriv (alpha2 p δ₀) ν w t (inputW p δ₀ ν ε w t))

@[tmio T, powerlib_foundation] private theorem nearIdDeriv_real_smul (α₂ ν : ℝ) (z : ℂ) (t c : ℝ)
    (h : ℂ) : nearIdDeriv α₂ ν z t (c • h) = c • nearIdDeriv α₂ ν z t h := by
  simp only [nearIdDeriv, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring

/-- **The transformed amplitude equation along a clamped solution**: while `‖w(t)‖ < ρc`,
`W(t) = Wmap(w(t), t)` has the derivative `transField(w(t), t)`
(`QuadraticCubic.hasDerivAt_nearId`, `QuadraticCubic.nearIdDeriv_quadField`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_Wmap {δ₀ b d ν ε ρc : ℝ} (hν : 0 < ν)
    (hε : 0 < ε) {w : ℝ → ℂ} {t : ℝ}
    (hw : HasDerivAt w (clampField p δ₀ b d ν ε ρc t (w t)) t) (hwt : ‖w t‖ < ρc) :
    HasDerivAt (fun s => Wmap (alpha2 p δ₀) ν ε ρc (w s) s) (transField p δ₀ b d ν ε (w t) t) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hcl : clampC ρc (w t) = w t := DuffingMathieu.clampC_of_norm_le hwt.le
  rw [clampField, hcl] at hw
  have hN := QuadraticCubic.hasDerivAt_nearId (α₂ := alpha2 p δ₀) hν.ne' hw
  have hW := hw.sub (hN.const_smul √ε)
  have hev : (fun s => Wmap (alpha2 p δ₀) ν ε ρc (w s) s) =ᶠ[𝓝 t]
      fun s => w s - √ε • nearId (alpha2 p δ₀) ν (w s) s := by
    have hcont : ContinuousAt w t := hw.continuousAt
    filter_upwards [hcont.preimage_mem_nhds (Metric.ball_mem_nhds (w t) (sub_pos.mpr hwt))]
      with s hs
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hs
    have : ‖w s‖ ≤ ρc := by
      have := norm_le_norm_add_norm_sub' (w s) (w t)
      linarith
    simp only [Wmap, DuffingMathieu.clampC_of_norm_le this]
  refine (hW.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [transField, scaledField, QuadraticCubic.nearIdDeriv_add, nearIdDeriv_real_smul,
    QuadraticCubic.nearIdDeriv_quadField hν.ne', secondField, smul_add, smul_neg, smul_smul]
  have h1 : √ε * √ε = ε := hss
  have h2 : √ε * (√ε)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  rw [h1, h2, one_smul, show √ε * ε = ε * √ε by ring]
  abel

@[tmio M, powerlib_foundation] private theorem oscillator_of_vdp₂ {b k₀ k₁ γ ν : ℝ} (hν : ν ≠ 0)
    {z : ℝ → ℂ} {u : ℝ → ℝ} (t : ℝ)
    (hz : HasDerivAt z (vdpField b k₀ k₁ γ ν (z t) t -
      I / ν * (u t : ℂ) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) t) :
    HasDerivAt (fun t => pos ν (z t) t) (vel ν (z t) t) t ∧
      HasDerivAt (fun t => vel ν (z t) t)
        (accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t) t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have h1 : HasDerivAt (fun t : ℝ => ((ν * t : ℝ) : ℂ)) (ν : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul ν).ofReal_comp; simpa using this
  have hE := (h1.mul_const I).cexp
  set E := Complex.exp (((ν * t : ℝ) : ℂ) * I) with hEdef
  have hEinv : Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) * E = 1 := by
    rw [hEdef, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hZ := hz.mul hE
  set Z' := (vdpField b k₀ k₁ γ ν (z t) t - I / ν * (u t : ℂ) *
      Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) * E + z t * (E * ((ν : ℂ) * I)) with hZ'
  -- the derivative of `z e^{jνt}`
  have hkey : Z' = ((vel ν (z t) t : ℝ) : ℂ) -
      (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t) / ν : ℝ) : ℂ) * I := by
    have hzE : z t * E = ((pos ν (z t) t : ℝ) : ℂ) - (((vel ν (z t) t) / ν : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [pos, hEdef]
      · simp [vel, hEdef]; field_simp
    have e1 : (vdpField b k₀ k₁ γ ν (z t) t - I / ν * (u t : ℂ) *
        Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) * E =
        -(I / ν) * (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) +
          ν ^ 2 * pos ν (z t) t : ℝ) : ℂ) + (u t : ℂ)) := by
      simp only [vdpField]
      linear_combination (-(I / ν) * (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) +
          ν ^ 2 * pos ν (z t) t : ℝ) : ℂ) + (u t : ℂ))) * hEinv
    rw [hZ', e1, show z t * (E * ((ν : ℂ) * I)) = (z t * E) * ((ν : ℂ) * I) by ring, hzE]
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [hkey] at hZ
  constructor
  · have h := (Complex.reCLM.hasFDerivAt (x := z t * E)).comp_hasDerivAt t hZ
    simpa [pos, Function.comp_def] using h
  · have h := ((Complex.imCLM.hasFDerivAt (x := z t * E)).comp_hasDerivAt t hZ).const_mul (-ν)
    have e : -ν * Complex.imCLM (((vel ν (z t) t : ℝ) : ℂ) -
        (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t) / ν : ℝ) : ℂ) * I) =
        accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t := by
      simp; field_simp
    rw [e] at h
    simpa [vel, Function.comp_def] using h


/-- **A clamped solution inside the clamp carries a solution of the loaded swing model**: at a
time with `‖w(t)‖ < ρc`, `δ = δ₀ + Re(√ε w e^{jνt})`, `δ̇ = vel ν (√ε w) t` satisfy the loaded
swing equations (the converse of `hasDerivAt_scaledAmp`). -/
@[tmio M, powerlib_domain] theorem swing_of_clamped (hp : p.Pos) {δ₀ b d ν ε ρc : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    {w : ℝ → ℂ} {t : ℝ} (hw : HasDerivAt w (clampField p δ₀ b d ν ε ρc t (w t)) t)
    (hwt : ‖w t‖ < ρc) :
    HasDerivAt (fun s => δ₀ + pos ν (((√ε : ℝ) : ℂ) * w s) s)
        (vel ν (((√ε : ℝ) : ℂ) * w t) t) t ∧
      HasDerivAt (fun s => vel ν (((√ε : ℝ) : ℂ) * w s) s)
        ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ₀ + pos ν (((√ε : ℝ) : ℂ) * w t) t)
          (vel ν (((√ε : ℝ) : ℂ) * w t) t)) t := by
  have hcl : clampC ρc (w t) = w t := DuffingMathieu.clampC_of_norm_le hwt.le
  rw [clampField, hcl] at hw
  have hz := hw.const_mul ((√ε : ℝ) : ℂ)
  rw [scaledField_eq hε hb hd] at hz
  have hosc := oscillator_of_vdp₂ hν.ne' (z := fun s => ((√ε : ℝ) : ℂ) * w s)
    (u := fun s => -alpha2 p δ₀ * pos ν (((√ε : ℝ) : ℂ) * w s) s ^ 2 +
      remainder p δ₀ ε (2 * ν) s (pos ν (((√ε : ℝ) : ℂ) * w s) s)) t hz
  refine ⟨hosc.1.const_add δ₀, ?_⟩
  have e := LoadedSwing.accel_eq hp δ₀ ε (2 * ν) t (pos ν (((√ε : ℝ) : ℂ) * w t) t)
    (vel ν (((√ε : ℝ) : ℂ) * w t) t)
  rw [show 2 * ν / 2 = ν by ring] at e
  rw [e]
  convert hosc.2 using 1
  ring

/-! ## The limit second-order field in the hypotheses of the periodic-orbit theorem -/

/-- The limit second-order field (`ω_L² → ν²`): damping `b`, stiffness `ν² − d`, pump `ν²`,
quadratic stiffness `α₂⁰ = −ν² tan δ₀/2`, cubic stiffness `α₃⁰ = −ν²/6`. -/
abbrev limitSecond (b d ν δ₀ : ℝ) : ℂ → ℝ → ℂ :=
  secondField b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν

/-- The averaged limit amplitude field of the loaded swing:
`ampField (b/2) (d/(2ν)) (jν/4) 0 β⁰` with `β⁰ = −(ν/48)(3 + 5 tan²δ₀)`, the value of
`LoadedSwing.betaLoaded` at the loaded resonance (`LoadedSwing.betaLoaded_resonance`). -/
abbrev loadedAmp (b d ν δ₀ : ℝ) : ℂ → ℂ :=
  ampField (b / 2) (d / (2 * ν)) (I * ((ν / 4 : ℝ) : ℂ)) 0 (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2))

/-- The Jacobian of the averaged limit field at `w` in the real coordinates `(Re w, Im w)`. -/
abbrev loadedJac (b d ν δ₀ : ℝ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ampJacobian (b / 2) (d / (2 * ν)) (I * ((ν / 4 : ℝ) : ℂ)) 0
    (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) (toReal w)

/-- The period average of the limit second-order field is the averaged limit amplitude field
(`QuadraticCubic.fieldAverage_secondField`). -/
@[tmio M, powerlib_domain] theorem fieldAverage_limitSecond {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (w : ℂ) : Averaging.fieldAverage (limitSecond b d ν δ₀) (2 * Real.pi / ν) w =
      loadedAmp b d ν δ₀ w := by
  rw [limitSecond, QuadraticCubic.fieldAverage_secondField hν]
  have e1 : (ν ^ 2 - (ν ^ 2 - d)) / (2 * ν) = d / (2 * ν) := by ring
  have e2 : ν ^ 2 / (4 * ν) = ν / 4 := by field_simp
  have e3 : 3 * (-(ν ^ 2) / 6) / (8 * ν) - 5 * (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 / (12 * ν ^ 3) =
      -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) := by field_simp; ring
  rw [e1, e2, e3]

@[tmio T, powerlib_foundation] private theorem norm_toReal_symm₂ (x : ℝ²) :
    ‖toReal.symm x‖ = ‖x‖ := by
  have h := Saturation.norm_toReal (toReal.symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The derivative of the cut-off limit field in the real coordinates. -/
def limitDerivR (b d ν δ₀ : ℝ) (x : ℝ²) (t : ℝ) : ℝ² →L[ℝ] ℝ² :=
  (toReal : ℂ →L[ℝ] ℝ²).comp ((secondDeriv b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2)
    (-(ν ^ 2) / 6) ν (toReal.symm x) t).comp (toReal.symm : ℝ² →L[ℝ] ℂ))

/-- The cut-off limit field in real coordinates: derivative, Lipschitz derivative, continuity in
time, period average and its derivative at a locked state. -/
@[tmio M, powerlib_domain] theorem limit_hyp {b d ν δ₀ ρc : ℝ} (hν : 0 < ν) {wstar : ℂ}
    (hw0 : loadedAmp b d ν δ₀ wstar = 0) (hρc : ‖wstar‖ + 1 < ρc) :
    (∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ∀ t, HasFDerivAt (fun y => realField
      (QuadraticCubic.cutSecond b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6)
        ν ρc) y t) (limitDerivR b d ν δ₀ x t) x) ∧
    (∀ x y : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖y - toReal wstar‖ ≤ 1 → ∀ t,
      ‖limitDerivR b d ν δ₀ x t - limitDerivR b d ν δ₀ y t‖ ≤
        (6 * |-(ν ^ 2) / 6| / ν + 5 * (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 / ν ^ 3) *
          (‖wstar‖ + 1) * ‖x - y‖) ∧
    Continuous (limitDerivR b d ν δ₀ (toReal wstar)) ∧
    Averaging.fieldAverage (realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) (ν ^ 2)
      (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν ρc)) (2 * Real.pi / ν) (toReal wstar) = 0 ∧
    HasFDerivAt (Averaging.fieldAverage (realField (QuadraticCubic.cutSecond b (ν ^ 2 - d)
      (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν ρc)) (2 * Real.pi / ν))
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (loadedJac b d ν δ₀ wstar)) (toReal wstar) := by
  have hρc0 : 0 ≤ ρc := by linarith [norm_nonneg wstar]
  have hball : ∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖toReal.symm x‖ ≤ ‖wstar‖ + 1 := by
    intro x hx
    rw [norm_toReal_symm₂]
    have := norm_le_norm_add_norm_sub' x (toReal wstar)
    rw [Saturation.norm_toReal] at this
    linarith
  -- the period average of the cut field near the locked state
  have hav : ∀ x : ℝ², ‖x‖ ≤ ρc → Averaging.fieldAverage (realField (QuadraticCubic.cutSecond b
      (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν ρc)) (2 * Real.pi / ν) x =
      ampSystem (b / 2) (d / (2 * ν)) (I * ((ν / 4 : ℝ) : ℂ)) 0
        (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) x := by
    intro x hx
    rw [SubharmonicOrbit.fieldAverage_realField (fun w => Averaging.PeriodicField.continuous_snd
      (QuadraticCubic.cutSecond_hyp hν hρc0) w)]
    have hw : ‖toReal.symm x‖ ≤ ρc := by rw [norm_toReal_symm₂]; exact hx
    have e : Averaging.fieldAverage (QuadraticCubic.cutSecond b (ν ^ 2 - d) (ν ^ 2)
        (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν ρc) (2 * Real.pi / ν) (toReal.symm x) =
        Averaging.fieldAverage (limitSecond b d ν δ₀) (2 * Real.pi / ν) (toReal.symm x) := by
      simp only [Averaging.fieldAverage, QuadraticCubic.cutSecond, limitSecond,
        DuffingMathieu.clampC_of_norm_le hw]
    rw [e, fieldAverage_limitSecond hν, ← Saturation.toReal_ampField,
      ContinuousLinearEquiv.apply_symm_apply]
  have hy : ‖toReal wstar‖ < ρc := by rw [Saturation.norm_toReal]; linarith
  refine ⟨fun x hx t => ?_, fun x y hx hy t => ?_, ?_, ?_, ?_⟩
  · apply SubharmonicOrbit.hasFDerivAt_realField
    exact hasFDerivAt_cutSecond (by linarith [hball x hx]) t
  · have e : limitDerivR b d ν δ₀ x t - limitDerivR b d ν δ₀ y t =
        (toReal : ℂ →L[ℝ] ℝ²).comp ((secondDeriv b (ν ^ 2 - d) (ν ^ 2)
          (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν (toReal.symm x) t -
          secondDeriv b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν
            (toReal.symm y) t).comp (toReal.symm : ℝ² →L[ℝ] ℂ)) := by
      simp only [limitDerivR, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    rw [e]
    refine (SubharmonicOrbit.norm_conj_toReal_le _).trans ?_
    have h := norm_secondDeriv_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2)
      (α₂ := -(ν ^ 2 * Real.tan δ₀) / 2) (α₃ := -(ν ^ 2) / 6) hν (hball x hx) (hball y hy) t
    rw [← map_sub, norm_toReal_symm₂] at h
    exact h
  · refine continuous_clm_apply.mpr fun h => ?_
    simp only [limitDerivR, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact toReal.continuous.comp ((continuous_clm_apply.mp (continuous_secondDeriv _ _ _ _ _ _ _)) _)
  · rw [hav _ hy.le, Saturation.toReal_ampField]
    show toReal (loadedAmp b d ν δ₀ wstar) = 0
    rw [hw0, map_zero]
  · refine (Saturation.hasFDerivAt_ampSystem _ _ _ _ _ _).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (toReal wstar) (sub_pos.mpr hy)] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    apply hav
    have := norm_le_norm_add_norm_sub' x (toReal wstar)
    linarith [norm_sub_rev x (toReal wstar)]

@[tmio T, powerlib_foundation] private theorem half_bound {x : ℝ} (hx : 0 ≤ x) :
    1 / (2 * (x + 1)) * x ≤ 1 / 2 := by
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The cut-off limit second-order field in the real coordinates. -/
abbrev limitCutR (b d ν δ₀ ρc : ℝ) : ℝ² → ℝ → ℝ² :=
  realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2)
    (-(ν ^ 2) / 6) ν ρc)

/-- The remainder of the transformed loaded amplitude equation relative to the limit field. -/
abbrev transRemL (p : Params) (δ₀ b d ν ε : ℝ) : ℂ → ℝ → ℂ :=
  transRem b d (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2)
    (-(ν ^ 2) / 6) ν ε (inputW p δ₀ ν ε)

/-- **The core estimates of the loaded case.** For a locked amplitude `w*` there are `ε₁ > 0` and
`M_q, L_q ≥ 0` (depending on `b, d, ν, δ₀, ‖w*‖` only) such that for every `0 < ε ≤ ε₁` and every
machine of the scaling: the clamped transformation `Wmap` (clamp radius `‖w*‖ + 3`) is onto,
`2`-co-Lipschitz and moves by at most `1/2`; along every clamped solution `w` and over every period
that starts with `Wmap(w(s), s)` within `1/2` of `w*`, `w` stays within `3/2` of `w*` and the
transformed amplitude solves `Ẇ = ε limitCutR(W, t) + transRemL(w, t)` (real coordinates); and
`transRemL` is bounded by `ε√ε M_q` and `ε√ε L_q`-Lipschitz within `3/2` of `w*`. -/
@[tmio M, powerlib_domain] private theorem loaded_core {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (wstar : ℂ) :
    ∃ ε₁ Mq Lq Dc : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 ≤ Mq ∧ 0 ≤ Lq ∧ 0 ≤ Dc ∧ ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∀ p : Params, p.Pos → p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      (∀ w w' t, ‖w - w'‖ ≤ 2 * ‖Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) w t -
        Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) w' t‖) ∧
      (∀ w w' t, ‖Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) w t -
        Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) w' t‖ ≤ 3 / 2 * ‖w - w'‖) ∧
      (∀ w t, ‖Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) w t - w‖ ≤ √ε * Dc) ∧
      (∀ W t, ∃ w, Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) w t = W) ∧
      (∀ w t, ‖Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) w t - w‖ ≤ 1 / 2) ∧
      (∀ w : ℝ → ℂ, (∀ t, HasDerivAt w (clampField p δ₀ b d ν ε (‖wstar‖ + 3) t (w t)) t) →
        ∀ s, ‖Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) (w s) s - wstar‖ ≤ 1 / 2 →
        ∀ t ∈ Icc s (s + 2 * Real.pi / ν), ‖w t - wstar‖ ≤ 3 / 2 ∧
          HasDerivAt (fun t => toReal (Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) (w t) t))
            (ε • limitCutR b d ν δ₀ (‖wstar‖ + 3)
              (toReal (Wmap (alpha2 p δ₀) ν ε (‖wstar‖ + 3) (w t) t)) t +
              toReal (transRemL p δ₀ b d ν ε (w t) t)) t) ∧
      ∀ w w' t, ‖w - wstar‖ ≤ 3 / 2 → ‖w' - wstar‖ ≤ 3 / 2 →
        ‖transRemL p δ₀ b d ν ε w t‖ ≤ ε * √ε * Mq ∧
        ‖transRemL p δ₀ b d ν ε w t - transRemL p δ₀ b d ν ε w' t‖ ≤ ε * √ε * Lq * ‖w - w'‖ := by
  set R := ‖wstar‖ with hR
  set ρc := R + 3 with hρc
  set r := R + 2 with hr
  set T := 2 * Real.pi / ν with hT
  have hR0 : 0 ≤ R := norm_nonneg _
  have hρc0 : 0 ≤ ρc := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hT0 : 0 < T := by positivity
  set K0 := ν ^ 2 + |d| with hK0
  set A2 := K0 * |Real.tan δ₀| / 2 with hA2
  set A3 := K0 / 6 with hA3
  set K2 := Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|) with hK2
  set Λ := remConstW ν d δ₀ r with hΛ
  have hK00 : 0 ≤ K0 := by positivity
  have hΛ0 : 0 ≤ Λ := by rw [hΛ, remConstW]; have := hc.le; positivity
  obtain ⟨Mq, Lq, hMq, hLq, hTR⟩ := transRem_bounds hν b d (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2)
    (-(ν ^ 2) / 6) r |d| K2 (|d| / 6) A2 A3 K0 (Λ * r / ν) (Λ / ν) hr0 (by positivity)
    (by positivity) hK00 (abs_nonneg _) (by positivity) (by positivity) (by positivity)
    (by positivity)
  set c₂ := 5 * A2 / (3 * ν ^ 2) with hc₂
  set D₁ := 5 * A2 / (6 * ν ^ 2) * (2 * ρc) ^ 2 with hD₁
  set S := speedConst b d ν δ₀ (2 * ρc) with hS
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hD₁0 : 0 ≤ D₁ := by positivity
  have hS0 : 0 ≤ S := by
    rw [hS, speedConst, remConstW]; have := hc.le; positivity
  set σ := min (1 / (2 * (c₂ * (2 * ρc) + 1))) (min (1 / (2 * (D₁ + 1))) (1 / (2 * (S * T + 1))))
    with hσ
  have hσ0 : 0 < σ := by
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨min 1 (σ ^ 2), Mq, Lq, D₁, by positivity, min_le_left _ _, hMq, hLq, hD₁0, ?_⟩
  intro ε hε hεε₁ p hp hb hd
  have hε1 : ε ≤ 1 := hεε₁.trans (min_le_left _ _)
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hsσ : √ε ≤ σ := by
    have : ε ≤ σ ^ 2 := hεε₁.trans (min_le_right _ _)
    calc √ε ≤ √(σ ^ 2) := Real.sqrt_le_sqrt this
      _ = σ := Real.sqrt_sq hσ0.le
  obtain ⟨-, h2, h3, hω, hωle⟩ := machine_bounds hp hc hε hε1 hd
  have hα₂ : |alpha2 p δ₀| ≤ A2 := by
    rw [h2, abs_div, abs_neg, abs_mul, abs_of_pos hω, abs_two, hA2]
    gcongr
  have hα₃ : |alpha3 p δ₀| ≤ A3 := by
    rw [h3, abs_div, abs_neg, abs_of_pos hω, abs_of_pos (by norm_num : (0 : ℝ) < 6), hA3]
    gcongr
  -- the smallness conditions
  have hsm1 : √ε * (5 * |alpha2 p δ₀| / (3 * ν ^ 2) * (2 * ρc)) ≤ 1 / 2 := by
    have h1 : 5 * |alpha2 p δ₀| / (3 * ν ^ 2) * (2 * ρc) ≤ c₂ * (2 * ρc) := by
      rw [hc₂]; gcongr
    have h2' : σ ≤ 1 / (2 * (c₂ * (2 * ρc) + 1)) := min_le_left _ _
    calc √ε * (5 * |alpha2 p δ₀| / (3 * ν ^ 2) * (2 * ρc)) ≤ σ * (c₂ * (2 * ρc)) :=
          mul_le_mul hsσ h1 (by positivity) hσ0.le
      _ ≤ 1 / (2 * (c₂ * (2 * ρc) + 1)) * (c₂ * (2 * ρc)) :=
          mul_le_mul_of_nonneg_right h2' (by positivity)
      _ ≤ 1 / 2 := half_bound (by positivity)
  have hsm2 : ∀ w t, ‖Wmap (alpha2 p δ₀) ν ε ρc w t - w‖ ≤ 1 / 2 := by
    intro w t
    refine (norm_Wmap_sub_le hν hρc0 w t).trans ?_
    have h1 : 5 * |alpha2 p δ₀| / (6 * ν ^ 2) * (2 * ρc) ^ 2 ≤ D₁ := by rw [hD₁]; gcongr
    have h2' : σ ≤ 1 / (2 * (D₁ + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    calc √ε * (5 * |alpha2 p δ₀| / (6 * ν ^ 2) * (2 * ρc) ^ 2) ≤ σ * D₁ :=
          mul_le_mul hsσ h1 (by positivity) hσ0.le
      _ ≤ 1 / (2 * (D₁ + 1)) * D₁ := mul_le_mul_of_nonneg_right h2' hD₁0
      _ ≤ 1 / 2 := half_bound hD₁0
  have hsm3 : √ε * S * T ≤ 1 / 2 := by
    have h2' : σ ≤ 1 / (2 * (S * T + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    calc √ε * S * T = √ε * (S * T) := by ring
      _ ≤ σ * (S * T) := mul_le_mul_of_nonneg_right hsσ (by positivity)
      _ ≤ 1 / (2 * (S * T + 1)) * (S * T) := mul_le_mul_of_nonneg_right h2' (by positivity)
      _ ≤ 1 / 2 := half_bound (by positivity)
  -- the bounds of the transformed remainder
  have hTRε := hTR ε hε hε1 (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) (inputW p δ₀ ν ε)
    (by rw [hd, show ν ^ 2 - ε * d - ν ^ 2 = -(ε * d) by ring, abs_neg, abs_mul, abs_of_pos hε])
    (by
      rw [h2]
      have e : (-(loadedFreqSq p δ₀ * Real.tan δ₀) / 2) ^ 2 - (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 =
          ε * (Real.tan δ₀ ^ 2 / 4 * (-d) * (2 * ν ^ 2 - ε * d)) := by rw [hd]; ring
      rw [e, abs_mul, abs_of_pos hε, hK2]
      gcongr
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.tan δ₀ ^ 2 / 4)]
      gcongr
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ν ^ 2), abs_mul, abs_of_pos hε]
      gcongr
      exact mul_le_of_le_one_left (abs_nonneg _) hε1)
    (by
      rw [h3, hd, show -(ν ^ 2 - ε * d) / 6 - -(ν ^ 2) / 6 = ε * (d / 6) by ring, abs_mul,
        abs_of_pos hε, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)])
    hα₂ hα₃ (by rw [abs_of_pos hω]; exact hωle)
    (fun w t hw => by
      have h := (remW_bounds hp hc hε hε1 hd hr0 hw hw t).2
      rw [inputW, norm_neg, norm_mul, norm_mul, norm_phase_inv₂, mul_one, norm_div, Complex.norm_I,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs]
      calc 1 / ν * |remW p δ₀ ν ε w t| ≤ 1 / ν * (ε ^ 2 * (Λ * r)) := by gcongr
        _ = ε ^ 2 * (Λ * r / ν) := by ring)
    (fun w w' t hw hw' => by
      have h := (remW_bounds hp hc hε hε1 hd hr0 hw hw' t).1
      have e : inputW p δ₀ ν ε w t - inputW p δ₀ ν ε w' t =
          -(I / ν * ((remW p δ₀ ν ε w t - remW p δ₀ ν ε w' t : ℝ) : ℂ) * (phase ν t)⁻¹) := by
        simp only [inputW]; push_cast; ring
      rw [e, norm_neg, norm_mul, norm_mul, norm_phase_inv₂, mul_one, norm_div, Complex.norm_I,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs]
      calc 1 / ν * |remW p δ₀ ν ε w t - remW p δ₀ ν ε w' t| ≤
          1 / ν * (ε ^ 2 * Λ * ‖w - w'‖) := by gcongr
        _ = ε ^ 2 * (Λ / ν) * ‖w - w'‖ := by ring)
  have hdisc : ∀ w : ℂ, ‖w - wstar‖ ≤ 3 / 2 → ‖w‖ ≤ r := by
    intro w hw
    have := norm_le_norm_add_norm_sub' w wstar
    rw [hr]; linarith
  have hsmD : ∀ w t, ‖Wmap (alpha2 p δ₀) ν ε ρc w t - w‖ ≤ √ε * D₁ := by
    intro w t
    refine (norm_Wmap_sub_le hν hρc0 w t).trans ?_
    rw [hD₁]
    gcongr
  refine ⟨fun w w' t => (Wmap_bilipschitz hν hρc0 hsm1 w w' t).1,
    fun w w' t => (Wmap_bilipschitz hν hρc0 hsm1 w w' t).2, hsmD,
    fun W t => exists_Wmap_eq hν hρc0 hsm1 W t, hsm2, ?_,
    fun w w' t hw hw' => hTRε w w' t (hdisc w hw) (hdisc w' hw')⟩
  intro w hw s hs t ht
  -- the clamped solution stays within `3/2` of `w*` over the period
  have hws : ‖w s - wstar‖ ≤ 1 := by
    have h1 := hsm2 (w s) s
    calc ‖w s - wstar‖ = ‖(Wmap (alpha2 p δ₀) ν ε ρc (w s) s - wstar) -
          (Wmap (alpha2 p δ₀) ν ε ρc (w s) s - w s)‖ := by congr 1; abel
      _ ≤ 1 / 2 + 1 / 2 := (norm_sub_le _ _).trans (add_le_add hs h1)
      _ = 1 := by norm_num
  have hdrift : ‖w t - w s‖ ≤ 1 / 2 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := w)
      (f' := fun u => clampField p δ₀ b d ν ε ρc u (w u)) (C := √ε * S)
      (fun u _ => (hw u).hasDerivWithinAt)
      (fun u _ => norm_clampField_le hp hν hc hε hε1 hd hρc0 u (w u)) t ht
    refine h.trans ?_
    calc √ε * S * (t - s) ≤ √ε * S * T :=
          mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
      _ ≤ 1 / 2 := hsm3
  have hwt : ‖w t - wstar‖ ≤ 3 / 2 := by
    calc ‖w t - wstar‖ = ‖(w t - w s) + (w s - wstar)‖ := by congr 1; abel
      _ ≤ 1 / 2 + 1 := (norm_add_le _ _).trans (add_le_add hdrift hws)
      _ = 3 / 2 := by norm_num
  refine ⟨hwt, ?_⟩
  have hwn : ‖w t‖ < ρc := by
    have := hdisc (w t) hwt
    rw [hρc, ← hr] at *; linarith
  have hD := hasDerivAt_Wmap (p := p) (b := b) (d := d) hν hε (hw t) hwn
  have hD' := (toReal : ℂ →L[ℝ] ℝ²).hasFDerivAt.comp_hasDerivAt t hD
  refine hD'.congr_deriv ?_
  -- the transformed field is the limit field at `W` plus the transformed remainder
  have hcl : clampC ρc (w t) = w t := DuffingMathieu.clampC_of_norm_le hwn.le
  have hWeq : Wmap (alpha2 p δ₀) ν ε ρc (w t) t = w t - √ε • nearId (alpha2 p δ₀) ν (w t) t := by
    rw [Wmap, hcl]
  have hWn : ‖Wmap (alpha2 p δ₀) ν ε ρc (w t) t‖ ≤ ρc := by
    have h1 := hsm2 (w t) t
    have h2 := norm_le_norm_add_norm_sub' (Wmap (alpha2 p δ₀) ν ε ρc (w t) t) (w t)
    have h3 := hdisc (w t) hwt
    rw [hρc]; rw [hr] at h3; linarith
  have hf : limitCutR b d ν δ₀ ρc (toReal (Wmap (alpha2 p δ₀) ν ε ρc (w t) t)) t =
      toReal (limitSecond b d ν δ₀ (w t - √ε • nearId (alpha2 p δ₀) ν (w t) t) t) := by
    simp only [limitCutR, realField, ContinuousLinearEquiv.symm_apply_apply,
      QuadraticCubic.cutSecond]
    rw [DuffingMathieu.clampC_of_norm_le hWn, hWeq]
  rw [hf, ContinuousLinearEquiv.coe_coe, ← map_smul, ← map_add]
  congr 1
  simp only [transRemL, transRem, transField]
  abel

@[tmio T, powerlib_foundation] private theorem toEuclideanCLM_inv_apply₂
    {J : Matrix (Fin 2) (Fin 2) ℝ} (hJ : J.det ≠ 0) (v : ℝ²) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ v) = v ∧
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J v) = v := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have h1 : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J *
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  have h2 : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ *
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J = 1 := by
    rw [← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
  exact ⟨DFunLike.congr_fun h1 v, DFunLike.congr_fun h2 v⟩

/-- Clamped solutions are unique. -/
@[tmio M, powerlib_domain] theorem clamped_unique (hp : p.Pos) {δ₀ b d ν ε ρc : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hρc : 0 ≤ ρc) {w w' : ℝ → ℂ} (hw : ∀ t, HasDerivAt w (clampField p δ₀ b d ν ε ρc t (w t)) t)
    (hw' : ∀ t, HasDerivAt w' (clampField p δ₀ b d ν ε ρc t (w' t)) t) {t₀ : ℝ}
    (h : w t₀ = w' t₀) : w = w' :=
  ODE_solution_unique_univ (v := clampField p δ₀ b d ν ε ρc) (s := fun _ => univ)
    (fun t => (clampField_lipschitz hp hν hc hε hε1 hd hρc t).lipschitzOnWith)
    (fun t => ⟨hw t, mem_univ _⟩) (fun t => ⟨hw' t, mem_univ _⟩) h

@[tmio M, powerlib_domain] private theorem loaded_orbit_core {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {wstar : ℂ} (hw0 : loadedAmp b d ν δ₀ wstar = 0)
    (hdet : (loadedJac b d ν δ₀ wstar).det ≠ 0) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      ∃ w : ℝ → ℂ, (∀ t, HasDerivAt w (clampField p δ₀ b d ν ε (‖wstar‖ + 3) t (w t)) t) ∧
        (∀ t, w (t + 2 * Real.pi / ν) = w t) ∧ (∀ t, ‖w t - wstar‖ ≤ 3 / 2) ∧
        ∀ t, ‖w t - wstar‖ ≤ √ε * C := by
  obtain ⟨ε₁, Mq, Lq, Dc, hε₁, hε₁1, hMq, hLq, -, hcore⟩ := loaded_core (b := b) (d := d) hν hc wstar
  set ρc := ‖wstar‖ + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  have hfh := SubharmonicOrbit.realField_hyp (QuadraticCubic.cutSecond_hyp (b := b)
    (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2) (α₂ := -(ν ^ 2 * Real.tan δ₀) / 2) (α₃ := -(ν ^ 2) / 6) hν
    hρc0)
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2)
    (-(ν ^ 2) / 6) ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  have hℓ0 : 0 ≤ ℓ := hfh.2.1
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨hD, hDl, hDc, h0, hA⟩ := limit_hyp (ρc := ρc) hν hw0 (by linarith)
  set L₂ := (6 * |-(ν ^ 2) / 6| / ν + 5 * (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 / ν ^ 3) *
    (‖wstar‖ + 1) with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  set J := loadedJac b d ν δ₀ wstar with hJ
  set B := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ with hB
  have hAB := fun v => (toEuclideanCLM_inv_apply₂ hdet v).1
  have hBA := fun v => (toEuclideanCLM_inv_apply₂ hdet v).2
  set r₀ := min (1 / 2) (1 / (4 * ‖B‖ * L₂ + 1)) with hr₀
  have hr₀0 : 0 < r₀ := lt_min (by norm_num) (by positivity)
  have hr₀L : 4 * ‖B‖ * L₂ * r₀ ≤ 1 := by
    have h1 : r₀ ≤ 1 / (4 * ‖B‖ * L₂ + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have e : r₀ * (4 * ‖B‖ * L₂ + 1) = 4 * ‖B‖ * L₂ * r₀ + r₀ := by ring
    linarith only [h1, e, hr₀0]
  have hr₀ρ : 2 * r₀ ≤ 1 := by linarith [min_le_left (1 / 2 : ℝ) (1 / (4 * ‖B‖ * L₂ + 1))]
  set CS := Averaging.stroboConst ℓ M Mq T with hCS
  set LS := Averaging.stroboLip ℓ (2 * Lq) L₂ M Mq T with hLS
  have hCS0 : 0 ≤ CS := by rw [hCS, Averaging.stroboConst]; positivity
  have hLS0 : 0 ≤ LS := by rw [hLS, Averaging.stroboLip]; positivity
  set A2 := (ν ^ 2 + |d|) * |Real.tan δ₀| / 2 with hA2
  set D₁ := 5 * A2 / (6 * ν ^ 2) * (2 * ρc) ^ 2 with hD₁
  have hD₁0 : 0 ≤ D₁ := by positivity
  set σ := min (T / (4 * ‖B‖ * LS + 1)) (r₀ * T / (2 * ‖B‖ * CS + 1)) with hσ
  have hσ0 : 0 < σ := lt_min (by positivity) (by positivity)
  set C := D₁ + (M + Mq) * T + 2 * ‖B‖ * CS / T with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨min (min ε₁ (1 / (2 * (M + Mq) * T + 1))) (σ ^ 2), C, by positivity, hC0, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := hεε₁.trans hε₁1
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hεs : ε ≤ √ε := by
    calc ε = √ε * √ε := hss.symm
      _ ≤ √ε * 1 := mul_le_mul_of_nonneg_left hs1 hs0.le
      _ = √ε := mul_one _
  have hsσ : √ε ≤ σ := by
    have : ε ≤ σ ^ 2 := hεε₀.trans (min_le_right _ _)
    calc √ε ≤ √(σ ^ 2) := Real.sqrt_le_sqrt this
      _ = σ := Real.sqrt_sq hσ0.le
  obtain ⟨hbil, -, -, hsurj, -, hbund, hTR⟩ := hcore ε hε hεε₁ p hp hb hd
  obtain ⟨-, h2, -, hω, hωle⟩ := machine_bounds hp hc hε hε1 hd
  -- the family of transformed amplitudes
  choose w₀ hw₀ using fun y : ℝ² => hsurj (toReal.symm y) 0
  choose W hW0 hW using fun y : ℝ² =>
    exists_clamped_solution (b := b) hp hν hc hε hε1 hd hρc0 0 (w₀ y)
  set X : ℝ² → ℝ → ℝ² := fun y t => toReal (Wmap (alpha2 p δ₀) ν ε ρc (W y t) t) with hX
  set Q : ℝ² → ℝ → ℝ² := fun y t => toReal (transRemL p δ₀ b d ν ε (W y t) t) with hQ
  have hX0 : ∀ y, X y 0 = y := fun y => by
    simp only [hX, hW0, hw₀, ContinuousLinearEquiv.apply_symm_apply]
  have hstart : ∀ y : ℝ², ‖y - toReal wstar‖ ≤ 1 / 2 →
      ‖Wmap (alpha2 p δ₀) ν ε ρc (W y 0) 0 - wstar‖ ≤ 1 / 2 := by
    intro y hy
    rw [hW0, hw₀, ← norm_toReal_symm₂, map_sub, ContinuousLinearEquiv.symm_apply_apply] at *
    exact hy
  have hper : ∀ y, ‖y - toReal wstar‖ ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) T,
      ‖W y t - wstar‖ ≤ 3 / 2 ∧ HasDerivAt (X y) (ε • limitCutR b d ν δ₀ ρc (X y t) t + Q y t) t :=
    fun y hy t ht => hbund (W y) (hW y) 0 (hstart y hy) t (by rwa [zero_add])
  have hr₀h : r₀ ≤ 1 / 2 := min_le_left _ _
  -- the order conditions
  have hηε : ε * √ε ≤ ε := mul_le_of_le_one_right hε.le hs1
  have hεη : ε ^ 2 ≤ ε * √ε := by rw [sq]; exact mul_le_mul_of_nonneg_left hεs hε.le
  have hερ : 2 * ε * (M + Mq) * T ≤ 1 := by
    have h1 : ε ≤ 1 / (2 * (M + Mq) * T + 1) := hεε₀.trans ((min_le_left _ _).trans
      (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : ε * (2 * (M + Mq) * T + 1) = 2 * ε * (M + Mq) * T + ε := by ring
    linarith only [h1, e, hε]
  have hηL : 4 * (ε * √ε) * ‖B‖ * LS ≤ ε * T := by
    have h1 : √ε ≤ T / (4 * ‖B‖ * LS + 1) := hsσ.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : 4 * √ε * ‖B‖ * LS ≤ T := by
      have e : √ε * (4 * ‖B‖ * LS + 1) = 4 * √ε * ‖B‖ * LS + √ε := by ring
      linarith only [h1, e, hs0]
    calc 4 * (ε * √ε) * ‖B‖ * LS = ε * (4 * √ε * ‖B‖ * LS) := by ring
      _ ≤ ε * T := mul_le_mul_of_nonneg_left h2 hε.le
  have hηC : 2 * (ε * √ε) * ‖B‖ * CS ≤ ε * r₀ * T := by
    have h1 : √ε ≤ r₀ * T / (2 * ‖B‖ * CS + 1) := hsσ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : 2 * √ε * ‖B‖ * CS ≤ r₀ * T := by
      have e : √ε * (2 * ‖B‖ * CS + 1) = 2 * √ε * ‖B‖ * CS + √ε := by ring
      linarith only [h1, e, hs0]
    calc 2 * (ε * √ε) * ‖B‖ * CS = ε * (2 * √ε * ‖B‖ * CS) := by ring
      _ ≤ ε * (r₀ * T) := mul_le_mul_of_nonneg_left h2 hε.le
      _ = ε * r₀ * T := by ring
  obtain ⟨yε, hyε, hfix, -⟩ := Averaging.exists_periodic_point_perturbed hfh one_pos hL₂0 hD hDl
    hDc h0 hA hAB hBA hr₀0 hr₀ρ hr₀L hε hε1 hηε hεη (by positivity) hMq hερ hηL hηC hX0
    (fun y hy t ht => (hper y (hy.trans hr₀h) t ht).2)
    (fun y hy t ht => by
      have h := (hTR (W y t) (W y t) t (hper y (hy.trans hr₀h) t ht).1
        (hper y (hy.trans hr₀h) t ht).1).1
      simp only [hQ, Saturation.norm_toReal]
      exact h)
    (fun y y' hy hy' t ht => by
      have h := (hTR (W y t) (W y' t) t (hper y (hy.trans hr₀h) t ht).1
        (hper y' (hy'.trans hr₀h) t ht).1).2
      have hb2 := hbil (W y t) (W y' t) t
      simp only [hQ, hX, ← map_sub, Saturation.norm_toReal]
      calc _ ≤ ε * √ε * Lq * ‖W y t - W y' t‖ := h
        _ ≤ ε * √ε * Lq * (2 * ‖Wmap (alpha2 p δ₀) ν ε ρc (W y t) t -
            Wmap (alpha2 p δ₀) ν ε ρc (W y' t) t‖) :=
            mul_le_mul_of_nonneg_left hb2 (by positivity)
        _ = ε * √ε * (2 * Lq) * ‖Wmap (alpha2 p δ₀) ν ε ρc (W y t) t -
            Wmap (alpha2 p δ₀) ν ε ρc (W y' t) t‖ := by ring)
  have hyε' : ‖yε - toReal wstar‖ ≤ 2 * √ε * ‖B‖ * CS / T := by
    refine hyε.trans (le_of_eq ?_)
    rw [show 2 * (ε * √ε) * ‖B‖ * CS = ε * (2 * √ε * ‖B‖ * CS) by ring,
      mul_div_mul_left _ _ hε.ne']
  have hyεh : ‖yε - toReal wstar‖ ≤ 1 / 2 := by
    refine hyε.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hr₀h (by positivity : (0 : ℝ) ≤ ε * T)
    linarith only [hηC, this]
  -- the clamped solution is periodic
  set w := W yε with hwdef
  have hwT : w T = w 0 := by
    have h1 : Wmap (alpha2 p δ₀) ν ε ρc (w T) T = Wmap (alpha2 p δ₀) ν ε ρc (w 0) 0 := by
      have := hfix
      simp only [hX] at this
      have h0' : toReal (Wmap (alpha2 p δ₀) ν ε ρc (w 0) 0) = yε := hX0 yε
      exact toReal.injective (this.trans h0'.symm)
    have h2 : Wmap (alpha2 p δ₀) ν ε ρc (w T) 0 = Wmap (alpha2 p δ₀) ν ε ρc (w 0) 0 := by
      rw [← h1, show T = 0 + 2 * Real.pi / ν by rw [zero_add], Wmap_periodic hν]
    have := hbil (w T) (w 0) 0
    rw [h2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hwper : ∀ t, w (t + T) = w t := by
    have hshift : ∀ t, HasDerivAt (fun t => w (t + T))
        (clampField p δ₀ b d ν ε ρc t (w (t + T))) t := by
      intro t
      have h := (hW yε (t + T)).comp_add_const t T
      rw [clampField_periodic hν] at h
      exact h
    have := clamped_unique hp hν hc hε hε1 hd hρc0 hshift (hW yε) (t₀ := 0)
      (by show w (0 + T) = w 0; rw [zero_add, hwT])
    exact fun t => congrFun this t
  have hwin : ∀ t, ‖w t - wstar‖ ≤ 3 / 2 ∧ ‖w t - wstar‖ ≤ √ε * C := by
    intro t
    obtain ⟨t', ht', hwt⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := w) hwper hT0 t
    rw [hwt]
    have ht'' : t' ∈ Icc (0 : ℝ) T := ⟨ht'.1, ht'.2.le⟩
    refine ⟨(hper yε hyεh t' ht'').1, ?_⟩
    -- the drift of the transformed amplitude over one period
    have hdr := Averaging.perturbed_drift_le (f := limitCutR b d ν δ₀ ρc) hfh.2.2.2.2.2 hε.le
      (η := ε * √ε) (Mq := Mq) (x := X yε) (q := Q yε) ht'.1
      (fun s hs => (hper yε hyεh s ⟨hs.1, hs.2.trans ht''.2⟩).2)
      (fun s hs => by
        have h := (hTR (W yε s) (W yε s) s (hper yε hyεh s ⟨hs.1, hs.2.trans ht''.2⟩).1
          (hper yε hyεh s ⟨hs.1, hs.2.trans ht''.2⟩).1).1
        simp only [hQ, Saturation.norm_toReal]
        exact h)
    rw [hX0, sub_zero] at hdr
    have hdr' : ‖X yε t' - yε‖ ≤ √ε * ((M + Mq) * T) := by
      refine hdr.trans ?_
      have h1 : ε * M + ε * √ε * Mq ≤ ε * (M + Mq) := by
        have := mul_le_mul_of_nonneg_right hηε hMq
        linarith only [this]
      calc (ε * M + ε * √ε * Mq) * t' ≤ ε * (M + Mq) * T :=
            mul_le_mul h1 ht''.2 ht'.1 (by positivity)
        _ ≤ √ε * ((M + Mq) * T) := by
            rw [show ε * (M + Mq) * T = ε * ((M + Mq) * T) by ring]
            exact mul_le_mul_of_nonneg_right hεs (by positivity)
    have hα₂ : |alpha2 p δ₀| ≤ A2 := by
      rw [h2, abs_div, abs_neg, abs_mul, abs_of_pos hω, abs_two, hA2]
      gcongr
    have hW1 : ‖w t' - Wmap (alpha2 p δ₀) ν ε ρc (w t') t'‖ ≤ √ε * D₁ := by
      rw [norm_sub_rev]
      refine (norm_Wmap_sub_le hν hρc0 (w t') t').trans ?_
      rw [hD₁]
      gcongr
    have hW2 : ‖Wmap (alpha2 p δ₀) ν ε ρc (w t') t' - toReal.symm yε‖ = ‖X yε t' - yε‖ := by
      rw [← norm_toReal_symm₂, map_sub, ContinuousLinearEquiv.symm_apply_apply]
    have hW3 : ‖toReal.symm yε - wstar‖ ≤ 2 * √ε * ‖B‖ * CS / T := by
      rw [← norm_toReal_symm₂ (yε - toReal wstar), map_sub,
        ContinuousLinearEquiv.symm_apply_apply] at hyε'
      exact hyε'
    calc ‖w t' - wstar‖ = ‖(w t' - Wmap (alpha2 p δ₀) ν ε ρc (w t') t') +
          (Wmap (alpha2 p δ₀) ν ε ρc (w t') t' - toReal.symm yε) + (toReal.symm yε - wstar)‖ := by
          congr 1; abel
      _ ≤ √ε * D₁ + √ε * ((M + Mq) * T) + 2 * √ε * ‖B‖ * CS / T := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add hW1 (hW2.le.trans hdr'))) hW3)
      _ = √ε * C := by rw [hC]; ring
  exact ⟨w, hW yε, hwper, fun t => (hwin t).1, fun t => (hwin t).2⟩

/-- The swing solution `δ = δ₀ + Re(√ε w e^{jνt})`, `δ̇ = vel ν (√ε w) t` carried by a periodic
clamped solution `w` that stays within `3/2` of `w*`, with `|δ − δ₀ − √ε Re(w* e^{jνt})| ≤ Cε`
when `‖w − w*‖ ≤ √ε C`. -/
@[tmio M, powerlib_domain] theorem loaded_swing_of_orbit (hp : p.Pos) {δ₀ b d ν ε C : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    {wstar : ℂ} {w : ℝ → ℂ}
    (hW : ∀ t, HasDerivAt w (clampField p δ₀ b d ν ε (‖wstar‖ + 3) t (w t)) t)
    (hwper : ∀ t, w (t + 2 * Real.pi / ν) = w t) (hw32 : ∀ t, ‖w t - wstar‖ ≤ 3 / 2)
    (hwC : ∀ t, ‖w t - wstar‖ ≤ √ε * C) :
    (∀ t, HasDerivAt (fun t => δ₀ + pos ν (((√ε : ℝ) : ℂ) * w t) t)
      (vel ν (((√ε : ℝ) : ℂ) * w t) t) t) ∧
    (∀ t, HasDerivAt (fun t => vel ν (((√ε : ℝ) : ℂ) * w t) t)
      ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ₀ + pos ν (((√ε : ℝ) : ℂ) * w t) t)
        (vel ν (((√ε : ℝ) : ℂ) * w t) t)) t) ∧
    (∀ t, δ₀ + pos ν (((√ε : ℝ) : ℂ) * w (t + 2 * Real.pi / ν)) (t + 2 * Real.pi / ν) =
        δ₀ + pos ν (((√ε : ℝ) : ℂ) * w t) t ∧
      vel ν (((√ε : ℝ) : ℂ) * w (t + 2 * Real.pi / ν)) (t + 2 * Real.pi / ν) =
        vel ν (((√ε : ℝ) : ℂ) * w t) t) ∧
    ∀ t, |δ₀ + pos ν (((√ε : ℝ) : ℂ) * w t) t - δ₀ -
      √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε := by
  set ρc := ‖wstar‖ + 3 with hρc
  set T := 2 * Real.pi / ν with hT
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hwper' : ∀ t, w (t + T) = w t := hwper
  have hwin : ∀ t, ‖w t - wstar‖ ≤ 3 / 2 ∧ ‖w t - wstar‖ ≤ √ε * C := fun t => ⟨hw32 t, hwC t⟩
  have hwn : ∀ t, ‖w t‖ < ρc := fun t => by
    have := norm_le_norm_add_norm_sub' (w t) wstar
    have := (hwin t).1
    rw [hρc]; linarith
  -- the swing solution
  have hsw := fun t => swing_of_clamped hp hν hε hb hd (hW t) (hwn t)
  refine ⟨fun t => (hsw t).1, fun t => (hsw t).2, fun t => ⟨?_, ?_⟩, fun t => ?_⟩
  · rw [hwper]; exact congrArg (fun x => δ₀ + x) (pos_period₂ hν _ t)
  · rw [hwper]; exact vel_period₂ hν _ t
  · have e1 : pos ν (((√ε : ℝ) : ℂ) * w t) t = √ε * pos ν (w t) t := pos_ofReal_mul₂ ν √ε (w t) t
    have e2 : (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re = pos ν wstar t := rfl
    have e3 : pos ν (w t - wstar) t = pos ν (w t) t - pos ν wstar t := by
      simp only [pos, sub_mul, Complex.sub_re]
    have e : δ₀ + pos ν (((√ε : ℝ) : ℂ) * w t) t - δ₀ -
        √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re =
        √ε * pos ν (w t - wstar) t := by
      rw [e1, e2, e3]; ring
    rw [e, abs_mul, abs_of_pos hs0]
    calc √ε * |pos ν (w t - wstar) t| ≤ √ε * (√ε * C) :=
          mul_le_mul_of_nonneg_left ((abs_pos_le₂ ν _ t).trans (hwin t).2) hs0.le
      _ = C * (√ε * √ε) := by ring
      _ = C * ε := by rw [hss]

/-- **The loaded half-frequency oscillation is a periodic solution of the loaded swing model.**
Let `w*` be a nondegenerate locked state of the averaged limit amplitude equation of the loaded
swing, `loadedAmp b d ν δ₀ w* = 0` (damping `b/2`, detuning `d/(2ν)`, pump `jν/4`, frequency shift
`β⁰ = −(ν/48)(3 + 5 tan²δ₀)`) with `det (loadedJac b d ν δ₀ w*) ≠ 0`, at a stable loaded point
`cos δ₀ > 0`. There are `ε₀ > 0` and `C ≥ 0` (depending on `b, d, ν, δ₀, w*` only) such that for
every depth `0 < ε ≤ ε₀` and every machine in the weakly nonlinear scaling `D/M = εb`,
`ω_L² = ν² − εd`, the loaded swing model with `K_s(t) = K_s(1 + ε cos 2νt)` has a solution
`(δ, δ̇)` that is periodic with period `2π/ν` and satisfies
`|δ(t) − δ₀ − √ε Re(w* e^{jνt})| ≤ C ε` for ALL `t` — a relative error `O(√ε)`, the quadratic
stiffness `α₂` included through the second-order transformation
(`Averaging.exists_periodic_point_perturbed` with a remainder of order `ε^{3/2}`). -/
@[tmio M, powerlib_domain] theorem loaded_subharmonic_orbit {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {wstar : ℂ} (hw0 : loadedAmp b d ν δ₀ wstar = 0)
    (hdet : (loadedJac b d ν δ₀ wstar).det ≠ 0) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      ∃ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) ∧
        (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) ∧
        (∀ t, δ (t + 2 * Real.pi / ν) = δ t ∧ δ' (t + 2 * Real.pi / ν) = δ' t) ∧
        ∀ t, |δ t - δ₀ - √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε := by
  obtain ⟨ε₀, C, hε₀, hC, horb⟩ := loaded_orbit_core hν hc hw0 hdet
  refine ⟨ε₀, C, hε₀, hC, fun ε hε hεε₀ p hp hb hd => ?_⟩
  obtain ⟨w, hw, hwper, hw32, hwC⟩ := horb ε hε hεε₀ p hp hb hd
  obtain ⟨h1, h2, h3, h4⟩ := loaded_swing_of_orbit hp hν hε hb hd hw hwper hw32 hwC
  exact ⟨_, _, h1, h2, h3, h4⟩

/-! ## Stability of the loaded subharmonic orbit -/

@[tmio M, powerlib_foundation] private theorem vdp_pos_vel₂ {ν : ℝ} (hν : ν ≠ 0) (z : ℂ) (t : ℝ) :
    vdp ν t (pos ν z t) (vel ν z t) = z := by
  have h1 : (((pos ν z t : ℝ) : ℂ) - (((vel ν z t) / ν : ℝ) : ℂ) * I) =
      z * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [pos]
    · simp [vel]; field_simp
  rw [vdp, h1, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

@[tmio M, powerlib_foundation] private theorem vdp_sub₂ (ν t x x' y y' : ℝ) :
    vdp ν t (x - y) (x' - y') = vdp ν t x x' - vdp ν t y y' := by
  simp only [vdp]; push_cast; ring

/-- The phase-plane deviation from the swing solution carried by a clamped solution `w` is `√ε`
times the deviation of the scaled amplitudes. -/
@[tmio M, powerlib_domain] private theorem vdp_dev {ν ε δ₀ : ℝ} (hν : ν ≠ 0) (hε : 0 < ε)
    (δ δ' : ℝ) (w : ℂ) (t : ℝ) :
    vdp ν t (δ - (δ₀ + pos ν (((√ε : ℝ) : ℂ) * w) t)) (δ' - vel ν (((√ε : ℝ) : ℂ) * w) t) =
      ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ - δ₀) δ' - w) := by
  have hs0 : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hε).ne'
  rw [show δ - (δ₀ + pos ν (((√ε : ℝ) : ℂ) * w) t) = (δ - δ₀) - pos ν (((√ε : ℝ) : ℂ) * w) t by
    ring, vdp_sub₂, vdp_pos_vel₂ hν, mul_sub, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]

set_option maxHeartbeats 1000000 in
/-- **The loaded subharmonic orbit of a Hurwitz locked state is exponentially stable in the
loaded swing model.** If the Jacobian `loadedJac b d ν δ₀ w*` of the averaged limit field at the
locked state `w*` is Hurwitz (`cos δ₀ > 0`), there are `ε₀, ρ_s, K, β > 0` and `C ≥ 0` such that
for every `0 < ε ≤ ε₀` and every machine of the scaling `D/M = εb`, `ω_L² = ν² − εd` the loaded
swing model has a `2π/ν`-periodic solution `(δ_ε, δ̇_ε)` with
`|δ_ε − δ₀ − √ε Re(w* e^{jνt})| ≤ Cε`, and every solution `(δ, δ̇)` whose phase-plane deviation
`‖vdp ν τ (δ − δ_ε) (δ̇ − δ̇_ε)‖` at a time `τ` is at most `√ε ρ_s` converges to it:
`‖vdp ν t (δ − δ_ε) (δ̇ − δ̇_ε)‖ ≤ K e^{−βε(t − τ)} ‖vdp ν τ (δ − δ_ε) (δ̇ − δ̇_ε)‖` for `t ≥ τ`
(`Averaging.exp_stable_perturbed` with the Lyapunov matrix of the averaged Jacobian, the
transformed amplitude, `loaded_unique_Icc`). -/
@[tmio M, powerlib_domain] theorem loaded_orbit_stable {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {wstar : ℂ} (hw0 : loadedAmp b d ν δ₀ wstar = 0)
    (hJ : LinearSystems.IsHurwitz (loadedJac b d ν δ₀ wstar)) :
    ∃ ε₀ C ρs K β : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < ρs ∧ 0 < K ∧ 0 < β ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      ∃ δε δε' : ℝ → ℝ, (∀ t, HasDerivAt δε (δε' t) t) ∧
        (∀ t, HasDerivAt δε' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δε t) (δε' t)) t) ∧
        (∀ t, δε (t + 2 * Real.pi / ν) = δε t ∧ δε' (t + 2 * Real.pi / ν) = δε' t) ∧
        (∀ t, |δε t - δ₀ - √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
          ∀ τ, ‖vdp ν τ (δ τ - δε τ) (δ' τ - δε' τ)‖ ≤ √ε * ρs →
          ∀ t, τ ≤ t → ‖vdp ν t (δ t - δε t) (δ' t - δε' t)‖ ≤
            K * Real.exp (-(β * ε * (t - τ))) * ‖vdp ν τ (δ τ - δε τ) (δ' τ - δε' τ)‖ := by
  have hdet : (loadedJac b d ν δ₀ wstar).det ≠ 0 := (Criteria.isUnit_det_of_isHurwitz hJ).ne_zero
  obtain ⟨ε₁, Mq, Lq, Dc, hε₁, hε₁1, hMq, hLq, hDc0, hcore⟩ :=
    loaded_core (b := b) (d := d) hν hc wstar
  obtain ⟨ε₂, C, hε₂, hC, horb⟩ := loaded_orbit_core hν hc hw0 hdet
  set ρc := ‖wstar‖ + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  have hfh := SubharmonicOrbit.realField_hyp (QuadraticCubic.cutSecond_hyp (b := b)
    (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2) (α₂ := -(ν ^ 2 * Real.tan δ₀) / 2) (α₃ := -(ν ^ 2) / 6) hν
    hρc0)
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2)
    (-(ν ^ 2) / 6) ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  have hℓ0 : 0 ≤ ℓ := hfh.2.1
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨hD, hDl, hDc, -, hA⟩ := limit_hyp (ρc := ρc) hν hw0 (by linarith)
  set L₂ := (6 * |-(ν ^ 2) / 6| / ν + 5 * (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 / ν ^ 3) *
    (‖wstar‖ + 1) with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  set J := loadedJac b d ν δ₀ wstar with hJdef
  -- the Lyapunov certificate
  obtain ⟨P, hPd, hEq, -⟩ := hJ.exists_posDef_unique_solution_continuous_lyapunov 1
    Matrix.PosDef.one
  obtain ⟨p₁, hp₁, hlow⟩ := MatrixAlgebra.exists_pos_mul_norm_sq_le_quadraticForm P hPd
  set p₂ := ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) P‖ + 1 with hp₂
  have hp₂0 : 0 < p₂ := by positivity
  have hbd : ∀ e : ℝ², p₁ * ‖e‖ ^ 2 ≤ MatrixAlgebra.quadraticForm P e ∧
      MatrixAlgebra.quadraticForm P e ≤ p₂ * ‖e‖ ^ 2 := fun e =>
    ⟨hlow e, (MatrixAlgebra.quadraticForm_le_opNorm_mul_norm_sq P e).trans
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))⟩
  have hQ1 : ∀ e : ℝ², 1 * ‖e‖ ^ 2 ≤ MatrixAlgebra.quadraticForm 1 e := fun e => by
    simp [MatrixAlgebra.quadraticForm, real_inner_self_eq_norm_sq]
  set a := ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J‖ with ha
  set κ := min 1 (p₁ / (96 * p₂ ^ 3)) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  have hκc : 96 * p₂ ^ 3 * κ ^ 2 ≤ 1 ^ 2 * p₁ := by
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ p₁ / (96 * p₂ ^ 3) := min_le_right _ _
    have h3 : κ ^ 2 ≤ κ := by nlinarith
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 96 * p₂ ^ 3)]
  set r₁ := min (1 / 2) (κ / (2 * (L₂ + 1))) with hr₁
  have hr₁0 : 0 < r₁ := lt_min (by norm_num) (by positivity)
  have hr₁h : r₁ ≤ 1 / 2 := min_le_left _ _
  have hr₁ρ : 2 * r₁ ≤ 1 := by linarith
  have hr₁κ : 2 * L₂ * r₁ ≤ κ := by
    have h1 : r₁ ≤ κ / (2 * (L₂ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set δa := r₁ * p₁ / (2 * p₂) with hδa
  have hδa0 : 0 < δa := by positivity
  set G := Real.exp ((ℓ + 2 * Lq) * T) with hG
  set K₀ := Real.sqrt (G ^ 2 * (p₂ / p₁) * Real.exp (1 / (8 * p₂) * T)) with hK₀
  have hK₀0 : 0 < K₀ := Real.sqrt_pos.mpr (by positivity)
  set ρs := min (2 / 3 * δa) (1 / (3 * K₀)) with hρs
  have hρs0 : 0 < ρs := lt_min (by positivity) (by positivity)
  set LS := Averaging.stroboLip ℓ (2 * Lq) L₂ M Mq T with hLS
  have hLS0 : 0 ≤ LS := by
    rw [hLS, Averaging.stroboLip]
    refine mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg (sq_nonneg T) (add_nonneg
      (mul_nonneg hL₂0 (add_nonneg hM0 hMq)) (mul_nonneg hℓ0 (by linarith)))) (mul_nonneg hT0.le
      (by linarith)))
  set σ := min (κ * T / (2 * LS + 1)) (min (δa / (Dc + C + 1)) (1 / (2 * (C + 1)))) with hσ
  have hσ0 : 0 < σ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set ε₀ := min (min (min ε₁ ε₂) (min (1 / (2 * T * p₂ * a ^ 2 + 1)) (p₂ / T)))
    (min (1 / (2 * (M + Mq) * T + 1)) (σ ^ 2)) with hε₀
  refine ⟨ε₀, C, ρs, 3 * K₀, 1 / (16 * p₂), by positivity, hC, hρs0, by positivity,
    by positivity, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hεε₂ : ε ≤ ε₂ := hεε₀.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hε1 : ε ≤ 1 := hεε₁.trans hε₁1
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hεs : ε ≤ √ε := by
    calc ε = √ε * √ε := hss.symm
      _ ≤ √ε * 1 := mul_le_mul_of_nonneg_left hs1 hs0.le
      _ = √ε := mul_one _
  have hsσ : √ε ≤ σ := by
    have : ε ≤ σ ^ 2 := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc √ε ≤ √(σ ^ 2) := Real.sqrt_le_sqrt this
      _ = σ := Real.sqrt_sq hσ0.le
  obtain ⟨hbil, hbil', hWD, -, -, hbund, hTR⟩ := hcore ε hε hεε₁ p hp hb hd
  obtain ⟨w, hw, hwper, hw32, hwC⟩ := horb ε hε hεε₂ p hp hb hd
  obtain ⟨h1, h2, h3, h4⟩ := loaded_swing_of_orbit hp hν hε hb hd hw hwper hw32 hwC
  refine ⟨_, _, h1, h2, h3, h4, ?_⟩
  intro δ δ' hδ hδ' τ hτ t hτt
  -- the order conditions of the attraction estimate
  have hηε : ε * √ε ≤ ε := mul_le_of_le_one_right hε.le hs1
  have hεη : ε ^ 2 ≤ ε * √ε := by rw [sq]; exact mul_le_mul_of_nonneg_left hεs hε.le
  have hεa : 2 * (ε * T) * p₂ * a ^ 2 ≤ 1 := by
    have h5 : ε ≤ 1 / (2 * T * p₂ * a ^ 2 + 1) := hεε₀.trans ((min_le_left _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at h5
    have e : ε * (2 * T * p₂ * a ^ 2 + 1) = 2 * (ε * T) * p₂ * a ^ 2 + ε := by ring
    linarith only [h5, e, hε]
  have hεq : ε * T * 1 ≤ p₂ := by
    have h5 : ε ≤ p₂ / T := hεε₀.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
    rw [le_div_iff₀ hT0] at h5
    linarith only [h5]
  have hερ : 2 * ε * (M + Mq) * T ≤ 1 := by
    have h5 : ε ≤ 1 / (2 * (M + Mq) * T + 1) := hεε₀.trans ((min_le_right _ _).trans
      (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h5
    have e : ε * (2 * (M + Mq) * T + 1) = 2 * ε * (M + Mq) * T + ε := by ring
    linarith only [h5, e, hε]
  have hηκ : 2 * (ε * √ε) * LS ≤ κ * (ε * T) := by
    have h5 : √ε ≤ κ * T / (2 * LS + 1) := hsσ.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h5
    have h6 : 2 * √ε * LS ≤ κ * T := by
      have e : √ε * (2 * LS + 1) = 2 * √ε * LS + √ε := by ring
      linarith only [h5, e, hs0]
    calc 2 * (ε * √ε) * LS = ε * (2 * √ε * LS) := by ring
      _ ≤ ε * (κ * T) := mul_le_mul_of_nonneg_left h6 hε.le
      _ = κ * (ε * T) := by ring
  have hsC : √ε * C ≤ 1 / 2 := by
    have h5 : √ε ≤ 1 / (2 * (C + 1)) := hsσ.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc √ε * C ≤ 1 / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right h5 hC
      _ ≤ 1 / 2 := half_bound hC
  have hsDC : √ε * (Dc + C) ≤ δa := by
    have h5 : √ε ≤ δa / (Dc + C + 1) := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h5
    have e : √ε * (Dc + C + 1) = √ε * (Dc + C) + √ε := by ring
    linarith only [h5, e, hs0]
  -- the clamped solution through the scaled amplitude of `(δ, δ̇)` at `τ`
  set wδ : ℝ → ℂ := fun s => ((√ε : ℝ) : ℂ)⁻¹ * vdp ν s (δ s - δ₀) (δ' s) with hwδ
  obtain ⟨x, hxτ, hx⟩ := exists_clamped_solution (b := b) hp hν hc hε hε1 hd hρc0 τ (wδ τ)
  have hdev : ∀ s, ‖vdp ν s (δ s - (δ₀ + pos ν (((√ε : ℝ) : ℂ) * w s) s))
      (δ' s - vel ν (((√ε : ℝ) : ℂ) * w s) s)‖ = √ε * ‖wδ s - w s‖ := fun s => by
    rw [vdp_dev hν.ne' hε, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hτ' : ‖x τ - w τ‖ ≤ ρs := by
    have h5 : √ε * ‖wδ τ - w τ‖ ≤ √ε * ρs := (hdev τ).symm.le.trans hτ
    rw [hxτ]
    exact le_of_mul_le_mul_left h5 hs0
  -- the transformed amplitudes in real coordinates
  set X : ℝ → ℝ² := fun s => toReal (Wmap (alpha2 p δ₀) ν ε ρc (x s) s) with hX
  set Z : ℝ → ℝ² := fun s => toReal (Wmap (alpha2 p δ₀) ν ε ρc (w s) s) with hZ
  have hXZ : ∀ s, ‖X s - Z s‖ = ‖Wmap (alpha2 p δ₀) ν ε ρc (x s) s -
      Wmap (alpha2 p δ₀) ν ε ρc (w s) s‖ := fun s => by
    simp only [hX, hZ, ← map_sub, Saturation.norm_toReal]
  have hpt : ∀ s, ‖X s - toReal wstar‖ ≤ 1 / 2 →
      ‖Wmap (alpha2 p δ₀) ν ε ρc (x s) s - wstar‖ ≤ 1 / 2 := fun s hs => by
    simpa only [hX, ← map_sub, Saturation.norm_toReal] using hs
  have hpz : ∀ s, ‖Z s - toReal wstar‖ ≤ 1 / 2 →
      ‖Wmap (alpha2 p δ₀) ν ε ρc (w s) s - wstar‖ ≤ 1 / 2 := fun s hs => by
    simpa only [hZ, ← map_sub, Saturation.norm_toReal] using hs
  have hzb : ∀ s, ‖Z s - toReal wstar‖ ≤ r₁ * p₁ / (2 * 1 * p₂) * 1 := fun s => by
    simp only [hZ, ← map_sub, Saturation.norm_toReal]
    calc ‖Wmap (alpha2 p δ₀) ν ε ρc (w s) s - wstar‖ ≤
        ‖Wmap (alpha2 p δ₀) ν ε ρc (w s) s - w s‖ + ‖w s - wstar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ √ε * Dc + √ε * C := add_le_add (hWD _ _) (hwC s)
      _ = √ε * (Dc + C) := by ring
      _ ≤ δa := hsDC
      _ = r₁ * p₁ / (2 * 1 * p₂) * 1 := by rw [hδa]; ring
  have hstab := Averaging.exp_stable_perturbed hfh one_pos hL₂0 hD hDl hDc hA hPd hEq hp₁
    one_pos hbd hQ1 (le_refl a) hr₁0 hr₁ρ hκc hr₁κ hε hε1 hηε hεη (by positivity) hMq hεa hεq hερ
    hηκ (x := X) (z := Z) (qx := fun s => toReal (transRemL p δ₀ b d ν ε (x s) s))
    (qz := fun s => toReal (transRemL p δ₀ b d ν ε (w s) s))
    (fun s hxs hzs u hu => by
      have hx' := hbund x hx s (hpt s (hxs.trans hr₁h)) u hu
      have hz' := hbund w hw s (hpz s (hzs.trans hr₁h)) u hu
      refine ⟨hx'.2, hz'.2, ?_, ?_, ?_⟩
      · rw [Saturation.norm_toReal]; exact (hTR _ _ u hx'.1 hx'.1).1
      · rw [Saturation.norm_toReal]; exact (hTR _ _ u hz'.1 hz'.1).1
      · rw [← map_sub, Saturation.norm_toReal, hXZ]
        calc _ ≤ ε * √ε * Lq * ‖x u - w u‖ := (hTR _ _ u hx'.1 hz'.1).2
          _ ≤ ε * √ε * Lq * (2 * ‖Wmap (alpha2 p δ₀) ν ε ρc (x u) u -
              Wmap (alpha2 p δ₀) ν ε ρc (w u) u‖) :=
              mul_le_mul_of_nonneg_left (hbil _ _ u) (by positivity)
          _ = ε * √ε * (2 * Lq) * ‖Wmap (alpha2 p δ₀) ν ε ρc (x u) u -
              Wmap (alpha2 p δ₀) ν ε ρc (w u) u‖ := by ring)
    (fun s => by simpa using hzb s)
    (τ := τ) (by
      rw [hXZ]
      calc _ ≤ 3 / 2 * ‖x τ - w τ‖ := hbil' _ _ τ
        _ ≤ 3 / 2 * ρs := by gcongr
        _ ≤ 3 / 2 * (2 / 3 * δa) := by gcongr; exact min_le_left _ _
        _ = r₁ * p₁ / (2 * p₂) := by rw [hδa]; ring)
  -- the clamped solution stays inside the clamp after `τ`
  have hxw : ∀ s, τ ≤ s → ‖x s - w s‖ ≤
      3 * K₀ * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * ‖x τ - w τ‖ := by
    intro s hs
    have h5 := hstab s hs
    rw [hXZ, hXZ] at h5
    have h6 := hbil (x s) (w s) s
    have h7 := hbil' (x τ) (w τ) τ
    have hE : 0 ≤ Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) := (Real.exp_pos _).le
    calc ‖x s - w s‖ ≤ 2 * ‖Wmap (alpha2 p δ₀) ν ε ρc (x s) s -
          Wmap (alpha2 p δ₀) ν ε ρc (w s) s‖ := h6
      _ ≤ 2 * (K₀ * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) *
          ‖Wmap (alpha2 p δ₀) ν ε ρc (x τ) τ - Wmap (alpha2 p δ₀) ν ε ρc (w τ) τ‖) :=
          mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ ≤ 2 * (K₀ * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * (3 / 2 * ‖x τ - w τ‖)) := by
          gcongr
      _ = 3 * K₀ * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * ‖x τ - w τ‖ := by ring
  have hxin : ∀ s, τ ≤ s → ‖x s‖ < ρc := by
    intro s hs
    have h5 := hxw s hs
    have hE : Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ 1 / (16 * p₂) * ε * (s - τ) := by
          have := sub_nonneg.mpr hs; positivity
        linarith)
    have h6 : ‖x s - w s‖ ≤ 1 := by
      calc ‖x s - w s‖ ≤ 3 * K₀ * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * ‖x τ - w τ‖ := h5
        _ ≤ 3 * K₀ * 1 * ρs := by gcongr
        _ ≤ 3 * K₀ * 1 * (1 / (3 * K₀)) := by gcongr; exact min_le_right _ _
        _ = 1 := by field_simp
    have h7 := hwC s
    have h8 := norm_le_norm_add_norm_sub' (x s) wstar
    have h9 : ‖x s - wstar‖ ≤ ‖x s - w s‖ + ‖w s - wstar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [hρc]; linarith
  -- the swing solution through `x` agrees with `(δ, δ̇)` after `τ`
  have hsw := fun s (hs : τ ≤ s) => swing_of_clamped hp hν hε hb hd (hx s) (hxin s hs)
  have hpos0 : δ₀ + pos ν (((√ε : ℝ) : ℂ) * x τ) τ = δ τ := by
    rw [hxτ, hwδ]
    simp only
    rw [show ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν τ (δ τ - δ₀) (δ' τ)) =
      vdp ν τ (δ τ - δ₀) (δ' τ) by field_simp, DuffingMathieu.pos_vdp]
    ring
  have hvel0 : vel ν (((√ε : ℝ) : ℂ) * x τ) τ = δ' τ := by
    rw [hxτ, hwδ]
    simp only
    rw [show ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν τ (δ τ - δ₀) (δ' τ)) =
      vdp ν τ (δ τ - δ₀) (δ' τ) by field_simp, DuffingMathieu.vel_vdp hν.ne']
  have huniq := loaded_unique_Icc hp (T₁ := t) (fun s hs => (hsw s hs.1).1)
    (fun s hs => (hsw s hs.1).2) (fun s _ => hδ s) (fun s _ => hδ' s) hpos0 hvel0 t
    ⟨hτt, le_rfl⟩
  have hwt : wδ t = x t := by
    simp only [hwδ]
    rw [← huniq.1, ← huniq.2, show δ₀ + pos ν (((√ε : ℝ) : ℂ) * x t) t - δ₀ =
      pos ν (((√ε : ℝ) : ℂ) * x t) t by ring, vdp_pos_vel₂ hν.ne']
    field_simp
  have hwτ : wδ τ = x τ := hxτ.symm
  rw [hdev t, hdev τ, hwt, hwτ]
  have := hxw t hτt
  calc √ε * ‖x t - w t‖ ≤ √ε * (3 * K₀ * Real.exp (-(1 / (16 * p₂) * ε * (t - τ))) *
      ‖x τ - w τ‖) := mul_le_mul_of_nonneg_left this hs0.le
    _ = 3 * K₀ * Real.exp (-(1 / (16 * p₂) * ε * (t - τ))) * (√ε * ‖x τ - w τ‖) := by ring

end powerlib.Synchronous.LoadedSubharmonicOrbit
