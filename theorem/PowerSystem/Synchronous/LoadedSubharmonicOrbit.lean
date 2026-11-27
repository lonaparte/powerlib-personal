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
    simp only [Function.uncurry, SwingParams.accel, SwingParams.Pe, loadedSwing, modKs]
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
@[tmio M, powerlib_domain] private theorem scaledField_eq (hp : p.Pos) {δ₀ b d ν ε : ℝ}
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
  have e := scaledField_eq hp hε hb hd (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t - δ₀) (δ' t)) t
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

end powerlib.Synchronous.LoadedSubharmonicOrbit
