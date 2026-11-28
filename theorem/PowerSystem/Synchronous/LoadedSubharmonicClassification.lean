import theorem.PowerSystem.Synchronous.LoadedSubharmonicOrbitUnique
import theorem.Averaging.PeriodicOrbitClassification
import theorem.ParametricResonance.LockedStatePairs

/-! # All half-frequency periodic oscillations of small amplitude of the loaded swing

`theorem/PowerSystem/Synchronous/LoadedSubharmonicOrbitUnique.lean` proves for the amplitude
equation with a small input, `ẇ = ε vdpField(w) + √ε quadField(w) + U(w, t)/√ε`, that every
nondegenerate locked state `w*` of the averaged second-order limit field carries a periodic orbit,
unique among the solutions starting within `r₀` of `w*` (`input_orbit`), and for the loaded swing
that the subharmonic orbit is unique near its initial state (`loaded_orbit_unique`). Here all
periodic solutions starting in a disc are classified. Along a clamped solution the transformed
amplitude `W = w − √ε u(w, t)` (`Wmap`) obeys `Ẇ = ε F⁰(W, t) + O(ε^{3/2})`, so a solution that
returns after one period has `T ‖F̄⁰(W(0))‖ ≤ √ε C_S`
(`Averaging.perturbed_periodic_fieldAverage_le`); on the compact disc the averaged limit field
`secondAmp` is bounded below away from its finitely many nondegenerate zeros
(`Averaging.lower_bound_of_isCompact`,
`Averaging.zeros_finite_of_isCompact`), so `W(0)`, hence `w(0)`, is `O(√ε)`-close to a zero and
the solution is the orbit of that zero (`input_classification`). For the loaded swing at `δ₀`:
for every `R` and all small `ε`, every `2π/ν`-periodic solution whose phase-plane point starts in
the disc `|δ(0) − δ₀ − jδ̇(0)/ν| ≤ √ε R` is the operating point `δ ≡ δ₀` or one of the loaded
subharmonic orbits, one for each locked state of the averaged limit field `loadedAmp` in the disc
`|w*| ≤ R + 1`; the orbit of `−w*` is the orbit of `w*` shifted by half its period `π/ν`
(`loaded_classification`).

Model boundary.
* Generic part (`input_classification`, no model family): the clamped amplitude equation with an
  input of `LoadedSubharmonicOrbitUnique` with the clamp `clampC (R + 3)`, the bounds of
  `input_orbit` (coefficients within `O(ε)` of the limit values, the input `U` of order `ε²` with
  an `ε²`-Lipschitz constant on the disc `‖w‖ ≤ 2(R + 4)`, continuous and `2π/ν`-periodic), and
  every zero of `secondAmp b d k₁⁰ α₂⁰ α₃⁰ ν` in the disc `|w| ≤ R + 1` nondegenerate. The
  solutions classified are those starting in the disc `‖w(0)‖ ≤ R` and returning after one
  period; zeros up to `R + 1` are listed since `W(0)` may lie outside the disc of `w(0)`.
* Loaded instance: the loaded swing model of `LoadedSubharmonicOrbit` — one generator, TR-110's
  swing equation (3-8) at a loaded operating point `δ₀` with `cos δ₀ > 0`, mechanical power
  `K_s(t) sin δ₀`, power-angle curve `K_s(t) sin δ`, `K_s(t) = K_s(1 + ε cos 2νt)`, `Params.Pos`,
  state `(δ, δ̇)`, continuous time — in the weakly nonlinear scaling `D/M = εb`,
  `ω_L² = ν² − εd`. The constants depend on `b, d, ν, δ₀, R` only. Every zero of
  `loadedAmp b d ν δ₀ = ampField (b/2) (d/(2ν)) (jν/4) 0 β⁰`, `β⁰ = −(ν/48)(3 + 5 tan²δ₀)`, in the
  disc `|w| ≤ R + 1` must be nondegenerate: by `Saturation.shift_det_eq_zero_iff` this excludes
  exactly the first-order boundary `(b/2)² + (d/(2ν))² = (ν/4)²` and the fold `(b/2)² = (ν/4)²`
  (`loadedJac_det_ne_zero`). Solutions of other periods and periodic solutions of larger
  amplitude are not classified.
* Excluded: a constant mechanical power
  (`theorem/PowerSystem/Synchronous/ConstantPowerSubharmonicClassification.lean`), AVR/PSS,
  network and multi-machine dynamics, a modulation of `K_d`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11);
Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations* (the second
theorem of Bogoliubov); Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical
Systems*, Ch. 2.9 and 6 (second-order averaging, near-identity transformations, periodic
solutions); the generic estimates `Averaging.perturbed_periodic_fieldAverage_le`,
`Averaging.lower_bound_of_isCompact`, `Averaging.zeros_finite_of_isCompact`; the zeros
`Saturation.shift_zeros`, `Saturation.shift_det_eq_zero_iff`; the loaded construction
`LoadedSubharmonicOrbit.input_orbit`, `LoadedSubharmonicOrbit.transRem_bounds`,
`LoadedSubharmonicOrbit.hasDerivAt_Wmap_input`, `LoadedSubharmonicOrbit.second_hyp`,
`LoadedSubharmonicOrbit.swing_of_clamped`, `LoadedSubharmonicOrbit.loaded_unique_Icc`.

Sharpenings.
* `loaded_orbit_unique` claims uniqueness only among the solutions starting within `√ε r₀` of
  `√ε w*`. Here every `2π/ν`-periodic solution of the loaded swing starting in the disc of radius
  `√ε R` — for any `R` — is the operating point or one of the finitely many loaded subharmonic
  orbits.

Results.
* `input_classification` — the amplitude equation with a small input: the clamped solutions
  starting in the disc `‖w(0)‖ ≤ R` and returning after one period are among the orbits of the
  zeros of `secondAmp` in the disc `|w*| ≤ R + 1`, each unique within `r₀` of its zero.
* `loadedAmp_zeros`, `loadedAmp_ncard` — the zeros of `loadedAmp`: `0` and the pairs `±w*` on
  the amplitudes `(d/(2ν) ± s)/β⁰`; `1 + 2N` of them in the disc `|w| ≤ R`.
* `loadedJac_det_ne_zero` — off the first-order boundary and the fold every zero of `loadedAmp`
  is nondegenerate.
* `loaded_classification` — **all small periodic solutions of the loaded swing**: the operating
  point `δ_0 ≡ δ₀`, and the orbits `δ_{w*}` with `‖vdp ν t (δ_{w*} − δ₀) δ̇_{w*} − √ε w*‖ ≤ Cε`,
  `δ_{−w*}(t) = δ_{w*}(t + π/ν)`, each unique near `√ε w*`.
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
open powerlib.Synchronous.SubharmonicOrbit (realField)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Elementary facts -/

@[tmio T, powerlib_foundation] private theorem norm_toReal_symm₆ (x : ℝ²) :
    ‖toReal.symm x‖ = ‖x‖ := by
  have h := Saturation.norm_toReal (toReal.symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

@[tmio T, powerlib_foundation] private theorem toEuclideanCLM_inv_apply₆
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

@[tmio T, powerlib_foundation] private theorem exists_ge_all₆ {ι : Type*} [Finite ι]
    (g : ι → ℝ) : ∃ C, 0 ≤ C ∧ ∀ i, g i ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range g).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun i => (hC ⟨i, rfl⟩).trans (le_max_left _ _)⟩

@[tmio T, powerlib_foundation] private theorem half_bound₆ {x : ℝ} (hx : 0 ≤ x) :
    1 / (2 * (x + 1)) * x ≤ 1 / 2 := by
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- The period average of the cut-off limit field in real coordinates is the averaged limit field
on the disc of the clamp. -/
@[tmio T, powerlib_foundation] private theorem fieldAverage_cutSecond₆ {b d k₁ α₂ α₃ ν ρc : ℝ}
    (hν : 0 < ν) (hρc0 : 0 ≤ ρc) {x : ℝ²} (hx : ‖x‖ ≤ ρc) :
    Averaging.fieldAverage (realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν ρc))
      (2 * Real.pi / ν) x =
      ampSystem (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) x := by
  rw [SubharmonicOrbit.fieldAverage_realField (fun w => Averaging.PeriodicField.continuous_snd
    (QuadraticCubic.cutSecond_hyp hν hρc0) w)]
  have hw : ‖toReal.symm x‖ ≤ ρc := by rw [norm_toReal_symm₆]; exact hx
  have e : Averaging.fieldAverage (QuadraticCubic.cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν ρc)
      (2 * Real.pi / ν) (toReal.symm x) =
      Averaging.fieldAverage (secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν) (2 * Real.pi / ν)
        (toReal.symm x) := by
    simp only [Averaging.fieldAverage, QuadraticCubic.cutSecond,
      DuffingMathieu.clampC_of_norm_le hw]
  rw [e, QuadraticCubic.fieldAverage_secondField hν, show ν ^ 2 - (ν ^ 2 - d) = d by ring,
    ← Saturation.toReal_ampField, ContinuousLinearEquiv.apply_symm_apply]

/-! ## The classification for the amplitude equation with an input -/

set_option maxHeartbeats 1000000 in
/-- **The periodic solutions of the amplitude equation with an input starting in a disc.** Let
every zero of the averaged limit field `secondAmp b d k₁⁰ α₂⁰ α₃⁰ ν` in the disc `|w| ≤ R + 1` be
nondegenerate, and fix the constants `K₁, K₂, K₃, A₂, A₃, K₀, μ, l_u ≥ 0` of `input_orbit`. There
are `ε₀ > 0`, `C ≥ 0` and `r₀ > 0` such that for every `0 < ε ≤ ε₀`, all coefficients and every
continuous `2π/ν`-periodic input `U` within these bounds (on the disc `‖w‖ ≤ 2(R + 4)`), the
clamped amplitude equation `ẇ = inputClamp(w, t)` (clamp radius `R + 3`) has for each zero `w*`
in the disc a `2π/ν`-periodic solution `x_{w*}` with `‖x_{w*} − w*‖ ≤ min(3/2, √ε C)`, the only
clamped solution with `z(2π/ν) = z(0)` and `‖z(0) − w*‖ ≤ r₀`; and every clamped solution with
`z(2π/ν) = z(0)` and `‖z(0)‖ ≤ R` is one of them; clamped solutions drift by at most `1/2` over
one period (`input_orbit`, the transformed equation and
`Averaging.perturbed_periodic_fieldAverage_le`, `Averaging.lower_bound_of_isCompact`). -/
@[tmio T, powerlib_foundation] theorem input_classification {ν : ℝ} (hν : 0 < ν)
    {b d k10 a20 a30 : ℝ} {K1 K2 K3 A2 A3 K0 mu lu : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hK0 : 0 ≤ K0) (hmu : 0 ≤ mu) (hlu : 0 ≤ lu)
    {R : ℝ} (hR : 0 ≤ R)
    (hdeg : ∀ w, secondAmp b d k10 a20 a30 ν w = 0 → ‖w‖ ≤ R + 1 →
      (secondJac b d k10 a20 a30 ν w).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ (k₁ α₂ α₃ : ℝ) (U : ℂ → ℝ → ℂ),
      |k₁ - k10| ≤ ε * K1 → |α₂ ^ 2 - a20 ^ 2| ≤ ε * K2 → |α₃ - a30| ≤ ε * K3 →
      |α₂| ≤ A2 → |α₃| ≤ A3 → |k₁| ≤ K0 →
      (∀ w t, ‖w‖ ≤ 2 * (R + 4) → ‖U w t‖ ≤ ε ^ 2 * mu) →
      (∀ w w' t, ‖w‖ ≤ 2 * (R + 4) → ‖w'‖ ≤ 2 * (R + 4) →
        ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖) →
      Continuous (fun q : ℝ × ℂ => U q.2 q.1) → (∀ w t, U w (t + 2 * Real.pi / ν) = U w t) →
      ∃ x : ℂ → ℝ → ℂ,
        (∀ w, secondAmp b d k10 a20 a30 ν w = 0 → ‖w‖ ≤ R + 1 →
          (∀ t, HasDerivAt (x w) (inputClamp b d k₁ α₂ α₃ ν ε (R + 3) U t (x w t)) t) ∧
          (∀ t, x w (t + 2 * Real.pi / ν) = x w t) ∧ (∀ t, ‖x w t - w‖ ≤ 3 / 2) ∧
          ∀ t, ‖x w t - w‖ ≤ √ε * C) ∧
        (∀ z : ℝ → ℂ, (∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε (R + 3) U t (z t)) t) →
          z (2 * Real.pi / ν) = z 0 → ∀ w, secondAmp b d k10 a20 a30 ν w = 0 → ‖w‖ ≤ R + 1 →
          ‖z 0 - w‖ ≤ r₀ → z = x w) ∧
        (∀ z : ℝ → ℂ, (∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε (R + 3) U t (z t)) t) →
          z (2 * Real.pi / ν) = z 0 → ‖z 0‖ ≤ R →
          ∃ w, secondAmp b d k10 a20 a30 ν w = 0 ∧ ‖w‖ ≤ R + 1 ∧ z = x w) ∧
        ∀ z : ℝ → ℂ, (∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε (R + 3) U t (z t)) t) →
          ∀ t ∈ Icc 0 (2 * Real.pi / ν), ‖z t - z 0‖ ≤ 1 / 2 := by
  set ρc := R + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  -- the limit field in real coordinates and its average
  have hfh := SubharmonicOrbit.realField_hyp (QuadraticCubic.cutSecond_hyp (b := b)
    (k₀ := ν ^ 2 - d) (k₁ := k10) (α₂ := a20) (α₃ := a30) hν hρc0)
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) k10 a20 a30 ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  have hℓ0 : 0 ≤ ℓ := hfh.2.1
  have hM0 : 0 ≤ M := by positivity
  set F := Averaging.fieldAverage
    (realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρc)) T with hF
  -- the zeros in the disc and their nondegeneracy
  set Z : Set ℂ := {w | secondAmp b d k10 a20 a30 ν w = 0 ∧ ‖w‖ ≤ R + 1} with hZ
  have hsh : ∀ w ∈ Z, F (toReal w) = 0 ∧
      HasFDerivAt F (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (secondJac b d k10 a20 a30 ν w)) (toReal w) := fun w hw => by
    obtain ⟨-, -, -, h0, hA⟩ := second_hyp (ρc := ρc) hν hw.1 (by linarith [hw.2])
    exact ⟨h0, hA⟩
  set K := Metric.closedBall (0 : ℝ²) (R + 1) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hzK : ∀ y ∈ K, F y = 0 → toReal.symm y ∈ Z := by
    intro y hy h0
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [hF, fieldAverage_cutSecond₆ hν hρc0 (by linarith)] at h0
    have h1 : toReal (secondAmp b d k10 a20 a30 ν (toReal.symm y)) = 0 := by
      rw [← Saturation.toReal_ampField, ContinuousLinearEquiv.apply_symm_apply]; exact h0
    refine ⟨by rwa [ContinuousLinearEquiv.map_eq_zero_iff] at h1, ?_⟩
    rw [norm_toReal_symm₆]; exact hy
  have hFc : Continuous F := Averaging.fieldAverage_continuous hfh
  have hZf : Z.Finite := by
    have hfin := Averaging.zeros_finite_of_isCompact hKc hFc.continuousOn fun y hy h0 => by
      have hw := hzK y hy h0
      obtain ⟨-, hA⟩ := hsh _ hw
      rw [ContinuousLinearEquiv.apply_symm_apply] at hA
      exact ⟨_, _, hA, fun v => (toEuclideanCLM_inv_apply₆ (hdeg _ hw.1 hw.2) v).2⟩
    refine (hfin.image toReal.symm).subset fun w hw => ⟨toReal w, ⟨?_, (hsh w hw).1⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, Saturation.norm_toReal]; exact hw.2
    · exact ContinuousLinearEquiv.symm_apply_apply _ _
  have : Finite Z := hZf.to_subtype
  -- the lower bound of the averaged field on the disc
  obtain ⟨c, ρK, hc, hρK, hlow⟩ := Averaging.lower_bound_of_isCompact hKc hFc.continuousOn
    (ι := Z) (ystar := fun i => toReal i.1)
    (A := fun i => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (secondJac b d k10 a20 a30 ν i.1))
    (B := fun i => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      (secondJac b d k10 a20 a30 ν i.1)⁻¹)
    (fun i => (hsh i.1 i.2).1) (fun i => (hsh i.1 i.2).2)
    (fun i v => (toEuclideanCLM_inv_apply₆ (hdeg i.1 i.2.1 i.2.2) v).2)
    (fun y hy h0 => ⟨⟨toReal.symm y, hzK y hy h0⟩,
      (ContinuousLinearEquiv.apply_symm_apply _ _).symm⟩)
  -- the orbit of each zero
  have hO := fun i : Z => input_orbit hν hK1 hK2 hK3 hA2 hA3 hK0 hmu hlu i.2.1
    (hdeg i.1 i.2.1 i.2.2)
  choose εf Cf rf hεf hCf hrf horbf using hO
  obtain ⟨ε₁, hε₁0, hε₁⟩ := PH.exists_pos_lower _ hεf
  obtain ⟨r₁, hr₁0, hr₁⟩ := PH.exists_pos_lower _ hrf
  obtain ⟨C, hC0, hC⟩ := exists_ge_all₆ Cf
  set r₀ := min r₁ (1 / 2) with hr₀
  have hr₀0 : 0 < r₀ := lt_min hr₁0 (by norm_num)
  -- the transformed remainder on the disc
  obtain ⟨Mq, Lq, hMq, hLq, hTR⟩ := transRem_bounds hν b d k10 a20 a30 (R + 1) K1 K2 K3 A2 A3
    K0 mu lu (by positivity) hA2 hA3 hK0 hK1 hK2 hK3 hmu hlu
  set CS := Averaging.stroboConst ℓ M Mq T with hCS
  have hCS0 : 0 ≤ CS := by rw [hCS, Averaging.stroboConst]; positivity
  set S := (|d| + K0 + ν * |b| + 3 * A3 * (2 * ρc) ^ 2) / ν * (2 * ρc) +
    A2 / ν * (2 * ρc) ^ 2 + mu with hS
  have hS0 : 0 ≤ S := by positivity
  set D₁ := 5 * A2 / (6 * ν ^ 2) * (2 * ρc) ^ 2 with hD₁
  have hD₁0 : 0 ≤ D₁ := by positivity
  set Q := D₁ + CS / (c * T) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set σ := min (min (1 / (2 * (S * T + 1))) (1 / (2 * (D₁ + 1))))
    (min (c * ρK * T / (CS + 1)) (r₀ / (Q + 1))) with hσ
  have hσ0 : 0 < σ := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by positivity) (by positivity))
  refine ⟨min (min 1 ε₁) (σ ^ 2), C, r₀, by positivity, hC0, hr₀0, ?_⟩
  intro ε hε hεε₀ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl hUc hUp
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεf : ∀ i, ε ≤ εf i := fun i =>
    (hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _))).trans (hε₁ i)
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hεs : ε ≤ √ε := by nlinarith
  have hsσ : √ε ≤ σ := by
    have : ε ≤ σ ^ 2 := hεε₀.trans (min_le_right _ _)
    calc √ε ≤ √(σ ^ 2) := Real.sqrt_le_sqrt this
      _ = σ := Real.sqrt_sq hσ0.le
  have hsST : √ε * S * T ≤ 1 / 2 := by
    have h1 : σ ≤ 1 / (2 * (S * T + 1)) := (min_le_left _ _).trans (min_le_left _ _)
    calc √ε * S * T = √ε * (S * T) := by ring
      _ ≤ σ * (S * T) := mul_le_mul_of_nonneg_right hsσ (by positivity)
      _ ≤ 1 / (2 * (S * T + 1)) * (S * T) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 1 / 2 := half_bound₆ (by positivity)
  have hsD : √ε * D₁ ≤ 1 / 2 := by
    have h1 : σ ≤ 1 / (2 * (D₁ + 1)) := (min_le_left _ _).trans (min_le_right _ _)
    calc √ε * D₁ ≤ σ * D₁ := mul_le_mul_of_nonneg_right hsσ hD₁0
      _ ≤ 1 / (2 * (D₁ + 1)) * D₁ := mul_le_mul_of_nonneg_right h1 hD₁0
      _ ≤ 1 / 2 := half_bound₆ hD₁0
  have hsK : √ε * CS < c * ρK * T := by
    have h1 : σ ≤ c * ρK * T / (CS + 1) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : CS / (CS + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    calc √ε * CS ≤ c * ρK * T / (CS + 1) * CS :=
          mul_le_mul_of_nonneg_right (hsσ.trans h1) hCS0
      _ = c * ρK * T * (CS / (CS + 1)) := by ring
      _ < c * ρK * T * 1 := by gcongr
      _ = c * ρK * T := mul_one _
  have hsQ : √ε * Q ≤ r₀ := by
    have h1 : σ ≤ r₀ / (Q + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 := mul_le_mul_of_nonneg_right (hsσ.trans h1) hQ0
    have h3 : r₀ / (Q + 1) * Q ≤ r₀ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hUl' : ∀ w w' t, ‖w‖ ≤ 2 * ρc → ‖w'‖ ≤ 2 * ρc → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖ :=
    fun w w' t hw hw' => hUl w w' t (hw.trans (by linarith)) (hw'.trans (by linarith))
  have hU' : ∀ w t, ‖w‖ ≤ 2 * ρc → ‖U w t‖ ≤ ε ^ 2 * mu :=
    fun w t hw => hU w t (hw.trans (by linarith))
  -- the orbits
  have hdisc : ∀ i : Z, 2 * (‖i.1‖ + 3) ≤ 2 * (R + 4) := fun i => by linarith [i.2.2]
  have hW := fun i : Z => horbf i ε hε (hεf i) k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0'
    (fun w t hw => hU w t (hw.trans (hdisc i)))
    (fun w w' t hw hw' => hUl w w' t (hw.trans (hdisc i)) (hw'.trans (hdisc i))) hUc hUp
  choose o ho hoper ho32 hoC hou using hW
  classical
  set x : ℂ → ℝ → ℂ := fun w => if h : w ∈ Z then o ⟨w, h⟩ else 0 with hx
  have hxw : ∀ (w : ℂ) (h : w ∈ Z), x w = o ⟨w, h⟩ := fun w h => by simp [hx, h]
  -- the clamps agree inside the disc
  have hcl : ∀ (r : ℝ) (t : ℝ) (w : ℂ), ‖w‖ ≤ r → ‖w‖ ≤ ρc →
      inputClamp b d k₁ α₂ α₃ ν ε r U t w = inputClamp b d k₁ α₂ α₃ ν ε ρc U t w :=
    fun r t w h1 h2 => by
      simp only [inputClamp, DuffingMathieu.clampC_of_norm_le h1,
        DuffingMathieu.clampC_of_norm_le h2]
  have hoc : ∀ (i : Z) t, HasDerivAt (o i) (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (o i t)) t := by
    intro i t
    have h1 := ho i t
    have hn : ‖o i t‖ ≤ ‖i.1‖ + 3 / 2 := by
      have := norm_le_norm_add_norm_sub' (o i t) i.1
      linarith [ho32 i t]
    rwa [hcl (‖i.1‖ + 3) t (o i t) (by linarith) (by linarith [i.2.2])] at h1
  -- the drift of a clamped solution over one period
  have hdrift : ∀ z : ℝ → ℂ, (∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (z t)) t) →
      ∀ t ∈ Icc 0 T, ‖z t - z 0‖ ≤ 1 / 2 := by
    intro z hz t ht
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := z)
      (f' := fun u => inputClamp b d k₁ α₂ α₃ ν ε ρc U u (z u)) (C := √ε * S)
      (fun u _ => (hz u).hasDerivWithinAt)
      (fun u _ => norm_inputClamp_le hν hε hε1 hρc0 hA2' hA3' hK0' hmu hU' u (z u)) t ht
    refine h.trans ?_
    calc √ε * S * (t - 0) ≤ √ε * S * T :=
          mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
      _ ≤ 1 / 2 := hsST
  -- a clamped solution returning after one period is periodic
  have hperiodic : ∀ z : ℝ → ℂ,
      (∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (z t)) t) → z T = z 0 →
      ∀ t, z (t + T) = z t := by
    intro z hz hzT
    have hshift : ∀ t, HasDerivAt (fun t => z (t + T))
        (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (z (t + T))) t := by
      intro t
      have h := (hz (t + T)).comp_add_const t T
      rw [inputClamp_periodic hν ρc hUp] at h
      exact h
    have := inputClamp_unique hν hε hε1 hρc0 hA2' hA3' hK0' hlu hUl' hshift hz (t₀ := 0)
      (by show z (0 + T) = z 0; rw [zero_add, hzT])
    exact fun t => congrFun this t
  -- uniqueness near each zero
  have hloc : ∀ z : ℝ → ℂ,
      (∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (z t)) t) → z T = z 0 →
      ∀ i : Z, ‖z 0 - i.1‖ ≤ r₀ → z = o i := by
    intro z hz hzT i hzi
    have hzp := hperiodic z hz hzT
    have hnear : ∀ t, ‖z t - i.1‖ ≤ 1 := by
      intro t
      obtain ⟨t', ht', hzt⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := z) hzp hT0 t
      rw [hzt]
      have h1 := hdrift z hz t' ⟨ht'.1, ht'.2.le⟩
      have h2 : r₀ ≤ 1 / 2 := min_le_right _ _
      calc ‖z t' - i.1‖ = ‖(z t' - z 0) + (z 0 - i.1)‖ := by congr 1; abel
        _ ≤ 1 / 2 + 1 / 2 := (norm_add_le _ _).trans (add_le_add h1 (hzi.trans h2))
        _ = 1 := by norm_num
    have hz' : ∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε (‖i.1‖ + 3) U t (z t)) t := by
      intro t
      have hn : ‖z t‖ ≤ ‖i.1‖ + 1 := by
        have := norm_le_norm_add_norm_sub' (z t) i.1
        linarith [hnear t]
      rw [hcl (‖i.1‖ + 3) t (z t) (by linarith) (by linarith [i.2.2])]
      exact hz t
    exact (hou i z hz' (hzi.trans ((min_le_left _ _).trans (hr₁ i)))).2 hzT
  refine ⟨x, fun w hw0 hwR => ?_, fun z hz hzT w hw0 hwR hzw => ?_, fun z hz hzT hzR => ?_,
    hdrift⟩
  · rw [hxw w ⟨hw0, hwR⟩]
    exact ⟨hoc ⟨w, hw0, hwR⟩, hoper ⟨w, hw0, hwR⟩, ho32 ⟨w, hw0, hwR⟩,
      fun t => (hoC ⟨w, hw0, hwR⟩ t).trans (mul_le_mul_of_nonneg_left (hC _) hs0.le)⟩
  · rw [hxw w ⟨hw0, hwR⟩]
    exact hloc z hz hzT ⟨w, hw0, hwR⟩ hzw
  · -- the transformed amplitude over the first period
    have hzn : ∀ t ∈ Icc 0 T, ‖z t‖ ≤ R + 1 / 2 := fun t ht => by
      have := norm_le_norm_add_norm_sub' (z t) (z 0)
      linarith [hdrift z hz t ht]
    set W : ℝ → ℂ := fun t => Wmap α₂ ν ε ρc (z t) t with hWdef
    have hWD : ∀ t, ‖W t - z t‖ ≤ √ε * D₁ := fun t => by
      refine (norm_Wmap_sub_le hν hρc0 (z t) t).trans ?_
      rw [hD₁]
      gcongr
    have hTRε := hTR ε hε hε1 k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0'
      (fun w t hw => hU w t (hw.trans (by linarith)))
      (fun w w' t hw hw' => hUl w w' t (hw.trans (by linarith)) (hw'.trans (by linarith)))
    have hxW : ∀ t ∈ Icc 0 (0 + T), HasDerivAt (fun s => toReal (W s))
        (ε • realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρc)
          (toReal (W t)) t + toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (z t) t)) t := by
      intro t ht
      rw [zero_add] at ht
      have hwn : ‖z t‖ < ρc := by linarith [hzn t ht]
      have hD := hasDerivAt_Wmap_input (b := b) (d := d) (k₁ := k₁) (α₃ := α₃) hν hε (hz t) hwn
      have hD' := (toReal : ℂ →L[ℝ] ℝ²).hasFDerivAt.comp_hasDerivAt t hD
      refine hD'.congr_deriv ?_
      have hcl' : clampC ρc (z t) = z t := DuffingMathieu.clampC_of_norm_le hwn.le
      have hWeq : W t = z t - √ε • nearId α₂ ν (z t) t := by
        simp only [hWdef, Wmap, hcl']
      have hWn : ‖W t‖ ≤ ρc := by
        have := norm_le_norm_add_norm_sub' (W t) (z t)
        linarith [hWD t, hzn t ht]
      have hf : realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρc)
          (toReal (W t)) t =
          toReal (secondField b (ν ^ 2 - d) k10 a20 a30 ν (z t - √ε • nearId α₂ ν (z t) t) t) := by
        simp only [realField, ContinuousLinearEquiv.symm_apply_apply, QuadraticCubic.cutSecond]
        rw [DuffingMathieu.clampC_of_norm_le hWn, hWeq]
      rw [hf, ContinuousLinearEquiv.coe_coe, ← map_smul, ← map_add]
      congr 1
      simp only [transRem, transIn]
      abel
    have hq : ∀ t ∈ Icc 0 (0 + T),
        ‖toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (z t) t)‖ ≤ ε * √ε * Mq := by
      intro t ht
      rw [zero_add] at ht
      rw [Saturation.norm_toReal]
      have hn : ‖z t‖ ≤ R + 1 := by linarith [hzn t ht]
      exact (hTRε (z t) (z t) t hn hn).1
    have hWT : toReal (W (0 + T)) = toReal (W 0) := by
      simp only [hWdef, zero_add]
      rw [hzT, show T = 0 + 2 * Real.pi / ν by rw [zero_add], Wmap_periodic hν]
    have hav := Averaging.perturbed_periodic_fieldAverage_le hfh hε.le
      (mul_le_of_le_one_right hε.le hs1) (by rw [sq]; exact mul_le_mul_of_nonneg_left hεs hε.le)
      hMq hxW hq hWT
    -- `W(0)` is near a zero
    have hav' : T * ‖F (toReal (W 0))‖ ≤ √ε * CS := by
      have h1 : ε * (T * ‖F (toReal (W 0))‖) ≤ ε * (√ε * CS) := by
        calc ε * (T * ‖F (toReal (W 0))‖) ≤ ε * √ε * CS := hav
          _ = ε * (√ε * CS) := by ring
      exact le_of_mul_le_mul_left h1 hε
    have hW0K : toReal (W 0) ∈ K := by
      rw [hK, Metric.mem_closedBall, dist_zero_right, Saturation.norm_toReal]
      have := norm_le_norm_add_norm_sub' (W 0) (z 0)
      linarith [hWD 0, hzR]
    rcases hlow _ hW0K with h | ⟨i, hi⟩
    · exfalso
      have h1 : c * ρK * T ≤ T * ‖F (toReal (W 0))‖ := by
        rw [mul_comm T]; exact mul_le_mul_of_nonneg_right h hT0.le
      linarith
    · have h1 : ‖W 0 - i.1‖ ≤ √ε * (CS / (c * T)) := by
        have h2 : c * T * ‖W 0 - i.1‖ ≤ √ε * CS := by
          have e : ‖toReal (W 0) - toReal i.1‖ = ‖W 0 - i.1‖ := by
            rw [← map_sub, Saturation.norm_toReal]
          calc c * T * ‖W 0 - i.1‖ = T * (c * ‖toReal (W 0) - toReal i.1‖) := by rw [e]; ring
            _ ≤ T * ‖F (toReal (W 0))‖ := mul_le_mul_of_nonneg_left hi hT0.le
            _ ≤ √ε * CS := hav'
        calc ‖W 0 - i.1‖ = c * T * ‖W 0 - i.1‖ / (c * T) := by field_simp
          _ ≤ √ε * CS / (c * T) := by gcongr
          _ = √ε * (CS / (c * T)) := by ring
      have hzi : ‖z 0 - i.1‖ ≤ r₀ := by
        calc ‖z 0 - i.1‖ = ‖(z 0 - W 0) + (W 0 - i.1)‖ := by congr 1; abel
          _ ≤ √ε * D₁ + √ε * (CS / (c * T)) := by
              refine (norm_add_le _ _).trans (add_le_add ?_ h1)
              rw [norm_sub_rev]; exact hWD 0
          _ = √ε * Q := by rw [hQ]; ring
          _ ≤ r₀ := hsQ
      refine ⟨i.1, i.2.1, i.2.2, ?_⟩
      rw [hxw i.1 i.2]
      exact hloc z hz hzT i hzi

/-! ## The loaded swing -/

@[tmio M, powerlib_foundation] private theorem vdp_pos_vel₆ {ν : ℝ} (hν : ν ≠ 0) (z : ℂ) (t : ℝ) :
    vdp ν t (pos ν z t) (vel ν z t) = z := by
  have h1 : (((pos ν z t : ℝ) : ℂ) - (((vel ν z t) / ν : ℝ) : ℂ) * I) =
      z * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [pos]
    · simp [vel]; field_simp
  rw [vdp, h1, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

@[tmio T, powerlib_foundation] private theorem exp_shift₆ {ν : ℝ} (t a : ℝ) (k : ℤ)
    (ha : ν * a = k * Real.pi) :
    Complex.exp (((ν * (t + a) : ℝ) : ℂ) * I) =
      (-1) ^ k * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
  rw [show ((ν * (t + a) : ℝ) : ℂ) * I = ((ν * t : ℝ) : ℂ) * I + k * (Real.pi * I) by
    push_cast; rw [mul_add, ← ofReal_mul ν a, ha]; push_cast; ring, Complex.exp_add,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, mul_comm]

@[tmio T, powerlib_foundation] private theorem pos_period₆ {ν : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    pos ν w (t + 2 * Real.pi / ν) = pos ν w t := by
  simp only [pos, exp_shift₆ (ν := ν) t (2 * Real.pi / ν) 2 (by field_simp; ring)]
  norm_num

@[tmio T, powerlib_foundation] private theorem vel_period₆ {ν : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    vel ν w (t + 2 * Real.pi / ν) = vel ν w t := by
  simp only [vel, exp_shift₆ (ν := ν) t (2 * Real.pi / ν) 2 (by field_simp; ring)]
  norm_num

@[tmio M, powerlib_foundation] private theorem vdp_period₆ {ν : ℝ} (hν : 0 < ν) (x x' : ℝ) :
    vdp ν (2 * Real.pi / ν) x x' = vdp ν 0 x x' := by
  have h := exp_shift₆ (ν := ν) 0 (2 * Real.pi / ν) 2 (by field_simp; ring)
  have h' : Complex.exp (-(((ν * (0 + 2 * Real.pi / ν) : ℝ) : ℂ) * I)) =
      Complex.exp (-(((ν * 0 : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, Complex.exp_neg, h]
    norm_num
  rw [zero_add] at h'
  simp only [vdp, h']

/-- Half a period turns the van der Pol amplitude into its opposite. -/
@[tmio M, powerlib_foundation] private theorem vdp_half₆ {ν : ℝ} (hν : 0 < ν) (t x x' : ℝ) :
    vdp ν (t + Real.pi / ν) x x' = -vdp ν t x x' := by
  have h := exp_shift₆ (ν := ν) t (Real.pi / ν) 1 (by field_simp; ring)
  have h' : Complex.exp (-(((ν * (t + Real.pi / ν) : ℝ) : ℂ) * I)) =
      -Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, Complex.exp_neg, h]
    simp
  simp only [vdp, h']
  ring

variable {p : Params}

/-- Global uniqueness for the loaded swing model. -/
@[tmio M, powerlib_domain] private theorem loaded_unique_univ₆ (hp : p.Pos) {δ₀ ε Ω : ℝ}
    {δ₁ δ₁' δ₂ δ₂' : ℝ → ℝ} (h1 : ∀ t, HasDerivAt δ₁ (δ₁' t) t)
    (h1' : ∀ t, HasDerivAt δ₁' ((loadedSwing p δ₀ ε Ω t).accel (δ₁ t) (δ₁' t)) t)
    (h2 : ∀ t, HasDerivAt δ₂ (δ₂' t) t)
    (h2' : ∀ t, HasDerivAt δ₂' ((loadedSwing p δ₀ ε Ω t).accel (δ₂ t) (δ₂' t)) t) {t₀ : ℝ}
    (h0 : δ₁ t₀ = δ₂ t₀) (h0' : δ₁' t₀ = δ₂' t₀) : δ₁ = δ₂ ∧ δ₁' = δ₂' := by
  have h := ODE_solution_unique_univ
    (v := fun t (q : ℝ × ℝ) => (q.2, (loadedSwing p δ₀ ε Ω t).accel q.1 q.2))
    (s := fun _ => univ) (f := fun t => (δ₁ t, δ₁' t)) (g := fun t => (δ₂ t, δ₂' t)) (t₀ := t₀)
    (fun t => (loaded_field_lipschitz hp δ₀ ε Ω t).lipschitzOnWith)
    (fun t => ⟨(h1 t).prodMk (h1' t), mem_univ _⟩) (fun t => ⟨(h2 t).prodMk (h2' t), mem_univ _⟩)
    (by simp [h0, h0'])
  exact ⟨funext fun t => congrArg Prod.fst (congrFun h t),
    funext fun t => congrArg Prod.snd (congrFun h t)⟩

/-- The pumped loaded swing model is `π/ν`-periodic in time. -/
@[tmio M, powerlib_domain] private theorem loadedSwing_half₆ {δ₀ ε ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    loadedSwing p δ₀ ε (2 * ν) (t + Real.pi / ν) = loadedSwing p δ₀ ε (2 * ν) t := by
  have : Real.cos (2 * ν * (t + Real.pi / ν)) = Real.cos (2 * ν * t) := by
    rw [show 2 * ν * (t + Real.pi / ν) = 2 * ν * t + 2 * Real.pi by field_simp,
      Real.cos_add_two_pi]
  simp only [loadedSwing, modKs, this]

/-- **The nondegenerate parameter set of the loaded swing.** Off the first-order boundary
`(b/2)² + (d/(2ν))² ≠ (ν/4)²` and the fold `(b/2)² ≠ (ν/4)²`, every zero of the averaged limit
field `loadedAmp` has an invertible Jacobian (`Saturation.shift_det_eq_zero_iff`; the frequency
shift `β⁰ = −(ν/48)(3 + 5 tan²δ₀)` never vanishes). -/
@[tmio M, powerlib_domain] theorem loadedJac_det_ne_zero {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hlin : (b / 2) ^ 2 + (d / (2 * ν)) ^ 2 ≠ (ν / 4) ^ 2) (hfold : (b / 2) ^ 2 ≠ (ν / 4) ^ 2)
    {w : ℂ} (hw : loadedAmp b d ν δ₀ w = 0) : (loadedJac b d ν δ₀ w).det ≠ 0 := by
  have hβ : -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) ≠ 0 := by
    have : 0 < 3 + 5 * Real.tan δ₀ ^ 2 := by positivity
    have : 0 < ν / 48 := by positivity
    intro h; nlinarith
  have hc : ‖I * ((ν / 4 : ℝ) : ℂ)‖ = ν / 4 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  intro h
  rcases (Saturation.shift_det_eq_zero_iff hβ hw).mp h with h' | h'
  · rw [hc] at h'; exact hlin h'.2
  · rw [hc] at h'; exact hfold h'.2

/-- **The zeros of the averaged limit field of the loaded swing.** Every zero of `loadedAmp` is
the trivial state or a locked state with `|w*|² = (d/(2ν) ± s)/β⁰`, `s = √(ν²/16 − b²/4)`,
`β⁰ = −(ν/48)(3 + 5 tan²δ₀)` (`b² ≤ ν²/4`); each of these amplitudes that is positive carries
exactly the pair `w*`, `−w*` (`Saturation.shift_zeros`). -/
@[tmio M, powerlib_domain] theorem loadedAmp_zeros {b d ν δ₀ : ℝ} (hν : 0 < ν) :
    (∀ w : ℂ, loadedAmp b d ν δ₀ w = 0 → w = 0 ∨ ((b / 2) ^ 2 ≤ (ν / 4) ^ 2 ∧
      (‖w‖ ^ 2 = (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) /
          (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ∨
        ‖w‖ ^ 2 = (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) /
          (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2))))) ∧
    ∀ A : ℝ, 0 < A → (b / 2) ^ 2 ≤ (ν / 4) ^ 2 →
      (A = (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) / (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ∨
        A = (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) /
          (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2))) →
      ∃ w : ℂ, ‖w‖ ^ 2 = A ∧ w ≠ -w ∧
        ∀ z : ℂ, (‖z‖ ^ 2 = A ∧ loadedAmp b d ν δ₀ z = 0) ↔ (z = w ∨ z = -w) := by
  have hβ : -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) ≠ 0 := by
    have : 0 < 3 + 5 * Real.tan δ₀ ^ 2 := by positivity
    have : 0 < ν / 48 := by positivity
    intro h; nlinarith
  have hc0 : I * ((ν / 4 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (by exact_mod_cast (by positivity : ν / 4 ≠ 0))
  have hc : ‖I * ((ν / 4 : ℝ) : ℂ)‖ = ν / 4 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  obtain ⟨h1, h2⟩ := Saturation.shift_zeros (σ := b / 2) (Δ := d / (2 * ν)) hc0 hβ
  rw [hc] at h1 h2
  exact ⟨h1, h2⟩

/-- **The number of zeros of the averaged limit field of the loaded swing in the disc
`|w| ≤ R`**: off the fold (`(b/2)² < (ν/4)²`), the trivial state and two locked states for each
of the amplitudes `(d/(2ν) ± s)/β⁰` in `(0, R²]` (`Saturation.shift_zeros_ncard`). -/
@[tmio M, powerlib_domain] theorem loadedAmp_ncard {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hb : (b / 2) ^ 2 < (ν / 4) ^ 2) {R : ℝ} (hR : 0 ≤ R) :
    {w : ℂ | loadedAmp b d ν δ₀ w = 0 ∧ ‖w‖ ≤ R}.ncard =
      1 + 2 * ((if 0 < (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) /
            (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ∧
          (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) /
            (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ≤ R ^ 2 then 1 else 0) +
        (if 0 < (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) /
            (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ∧
          (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) /
            (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ≤ R ^ 2 then 1 else 0)) := by
  have hβ : -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) ≠ 0 := by
    have : 0 < 3 + 5 * Real.tan δ₀ ^ 2 := by positivity
    have : 0 < ν / 48 := by positivity
    intro h; nlinarith
  have hc0 : I * ((ν / 4 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (by exact_mod_cast (by positivity : ν / 4 ≠ 0))
  have hc : ‖I * ((ν / 4 : ℝ) : ℂ)‖ = ν / 4 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := Saturation.shift_zeros_ncard (σ := b / 2) (Δ := d / (2 * ν)) hc0 hβ
    (by rw [hc]; exact hb) hR
  rw [hc] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **All `2π/ν`-periodic oscillations of small amplitude of the loaded swing.** Let every zero of
the averaged limit field `loadedAmp b d ν δ₀` in the disc `|w| ≤ R + 1` be nondegenerate
(`loadedJac_det_ne_zero`), `cos δ₀ > 0`. There are `ε₀ > 0`, `C ≥ 0`, `r₀ > 0` (depending on
`b, d, ν, δ₀, R` only) such that for every `0 < ε ≤ ε₀` and every machine of the scaling
`D/M = εb`, `ω_L² = ν² − εd`, the loaded swing model with `K_s(t) = K_s(1 + ε cos 2νt)` has for
each such zero `w*` a `2π/ν`-periodic solution `(δ_{w*}, δ̇_{w*})` with
`‖vdp ν t (δ_{w*}(t) − δ₀) δ̇_{w*}(t) − √ε w*‖ ≤ Cε` for all `t`, such that:
* `δ_0 ≡ δ₀` (the operating point is the orbit of the trivial zero);
* `δ_{−w*}(t) = δ_{w*}(t + π/ν)`;
* `(δ_{w*}, δ̇_{w*})` is the only solution returning after one period whose phase-plane point at
  `t = 0` lies within `√ε r₀` of `√ε w*`;
* every solution with `(δ, δ̇)(2π/ν) = (δ, δ̇)(0)` and `|δ(0) − δ₀ − jδ̇(0)/ν| ≤ √ε R` is one of
  them (`input_classification` for `U = inputW`, `swing_of_clamped`, `loaded_unique_Icc`). -/
@[tmio M, powerlib_domain] theorem loaded_classification {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {R : ℝ} (hR : 0 ≤ R)
    (hdeg : ∀ w, loadedAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → (loadedJac b d ν δ₀ w).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      ∃ δw δw' : ℂ → ℝ → ℝ,
        (∀ w, loadedAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 →
          (∀ t, HasDerivAt (δw w) (δw' w t) t) ∧
          (∀ t, HasDerivAt (δw' w)
            ((loadedSwing p δ₀ ε (2 * ν) t).accel (δw w t) (δw' w t)) t) ∧
          (∀ t, δw w (t + 2 * Real.pi / ν) = δw w t ∧ δw' w (t + 2 * Real.pi / ν) = δw' w t) ∧
          (∀ t, ‖vdp ν t (δw w t - δ₀) (δw' w t) - ((√ε : ℝ) : ℂ) * w‖ ≤ C * ε) ∧
          (∀ t, δw (-w) t = δw w (t + Real.pi / ν) ∧ δw' (-w) t = δw' w (t + Real.pi / ν)) ∧
          ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
            (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
            δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
            ‖vdp ν 0 (δ 0 - δ₀) (δ' 0) - ((√ε : ℝ) : ℂ) * w‖ ≤ √ε * r₀ →
            δ = δw w ∧ δ' = δw' w) ∧
        (∀ t, δw 0 t = δ₀ ∧ δw' 0 t = 0) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
          δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
          ‖vdp ν 0 (δ 0 - δ₀) (δ' 0)‖ ≤ √ε * R →
          ∃ w, loadedAmp b d ν δ₀ w = 0 ∧ ‖w‖ ≤ R + 1 ∧ δ = δw w ∧ δ' = δw' w := by
  obtain ⟨hAe, hJe⟩ := loadedAmp_eq_secondAmp (b := b) (d := d) (δ₀ := δ₀) hν
  have hdeg' : ∀ w, secondAmp b d (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν w = 0 →
      ‖w‖ ≤ R + 1 →
      (secondJac b d (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν w).det ≠ 0 := by
    intro w hw hwR
    rw [← hJe]
    exact hdeg w (by rw [hAe]; exact hw) hwR
  set ρU := 2 * (R + 4) with hρU
  have hρU0 : 0 ≤ ρU := by positivity
  have hRC : 0 ≤ remConstW ν d δ₀ ρU := by rw [remConstW]; have := hc.le; positivity
  obtain ⟨ε₁, C, r₁, hε₁, hC, hr₁, hcl⟩ := input_classification hν (K1 := |d|)
    (K2 := Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|)) (K3 := |d| / 6)
    (A2 := (ν ^ 2 + |d|) * |Real.tan δ₀| / 2) (A3 := (ν ^ 2 + |d|) / 6) (K0 := ν ^ 2 + |d|)
    (mu := remConstW ν d δ₀ ρU * ρU / ν) (lu := remConstW ν d δ₀ ρU / ν) (abs_nonneg _)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hR hdeg'
  set r₀ := min r₁ (1 / 2) with hr₀
  have hr₀0 : 0 < r₀ := lt_min hr₁ (by norm_num)
  have hr₀1 : r₀ ≤ r₁ := min_le_left _ _
  have hr₀h : r₀ ≤ 1 / 2 := min_le_right _ _
  refine ⟨min ε₁ (min 1 ((r₀ / (C + 1)) ^ 2)), C, r₀, by positivity, hC, hr₀0, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hsC : √ε * C ≤ r₀ := by
    have h1 : ε ≤ (r₀ / (C + 1)) ^ 2 := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : √ε ≤ r₀ / (C + 1) := by
      calc √ε ≤ √((r₀ / (C + 1)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = r₀ / (C + 1) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ (by positivity)] at h2
    have e : √ε * (C + 1) = √ε * C + √ε := by ring
    linarith only [h2, e, hs0]
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨k1, k2, k3, a2, a3, k0⟩ := loaded_coeff_bounds hp hc hε hε1 hd
  obtain ⟨hU, hUl⟩ := inputW_bounds hp hν hc hε hε1 hd hρU0
  obtain ⟨x, hx, hloc, hK, hdrift⟩ := hcl ε hε hεε₁ (loadedFreqSq p δ₀) (alpha2 p δ₀)
    (alpha3 p δ₀) (inputW p δ₀ ν ε) k1 k2 k3 a2 a3 k0 hU hUl (continuous_inputW p δ₀ ν ε)
    (inputW_periodic hν)
  have hAe' : ∀ w, loadedAmp b d ν δ₀ w =
      secondAmp b d (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν w := fun w => by
    rw [hAe]
  -- the swing solutions carried by the orbits
  set δw : ℂ → ℝ → ℝ := fun w t => δ₀ + pos ν (((√ε : ℝ) : ℂ) * x w t) t with hδw
  set δw' : ℂ → ℝ → ℝ := fun w t => vel ν (((√ε : ℝ) : ℂ) * x w t) t with hδw'
  have hsw : ∀ w, loadedAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ t,
      HasDerivAt (δw w) (δw' w t) t ∧ HasDerivAt (δw' w)
        ((loadedSwing p δ₀ ε (2 * ν) t).accel (δw w t) (δw' w t)) t := by
    intro w hw0 hwR t
    have hw0' := (hAe' w).symm.trans hw0
    have hn : ‖x w t‖ < R + 3 := by
      have := norm_le_norm_add_norm_sub' (x w t) w
      linarith [(hx w hw0' hwR).2.2.1 t]
    have hwc : HasDerivAt (x w) (clampField p δ₀ b d ν ε (R + 3) t (x w t)) t :=
      (hx w hw0' hwR).1 t
    exact swing_of_clamped hp hν hε hb hd hwc hn
  -- a periodic swing solution starting near the disc is carried by a periodic clamped solution
  have hcore : ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
      δ T = δ 0 → δ' T = δ' 0 → ‖vdp ν 0 (δ 0 - δ₀) (δ' 0)‖ ≤ √ε * (R + 3 / 2) →
      ∃ z : ℝ → ℂ, (∀ t, HasDerivAt z (inputClamp b d (loadedFreqSq p δ₀) (alpha2 p δ₀)
          (alpha3 p δ₀) ν ε (R + 3) (inputW p δ₀ ν ε) t (z t)) t) ∧ z T = z 0 ∧
        ((√ε : ℝ) : ℂ) * z 0 = vdp ν 0 (δ 0 - δ₀) (δ' 0) := by
    intro δ δ' hδ hδ' hTδ hTδ' h0
    obtain ⟨z, hz0, hz⟩ := exists_clamped_solution (b := b) hp hν hc hε hε1 hd
      (by positivity : (0 : ℝ) ≤ R + 3) 0 (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (δ 0 - δ₀) (δ' 0))
    have hzc : ∀ t, HasDerivAt z (inputClamp b d (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀)
        ν ε (R + 3) (inputW p δ₀ ν ε) t (z t)) t := hz
    have hz0v : ((√ε : ℝ) : ℂ) * z 0 = vdp ν 0 (δ 0 - δ₀) (δ' 0) := by
      rw [hz0]; field_simp
    have hz0n : ‖z 0‖ ≤ R + 3 / 2 := by
      have e : ‖vdp ν 0 (δ 0 - δ₀) (δ' 0)‖ = √ε * ‖z 0‖ := by
        rw [← hz0v, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      rw [e] at h0
      exact le_of_mul_le_mul_left h0 hs0
    have hzn : ∀ t ∈ Icc 0 T, ‖z t‖ < R + 3 := fun t ht => by
      have := norm_le_norm_add_norm_sub' (z t) (z 0)
      linarith [hdrift z hzc t ht]
    have hsz := fun s (hs : s ∈ Icc 0 T) => swing_of_clamped hp hν hε hb hd (hz s) (hzn s hs)
    have hpos0 : δ₀ + pos ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ 0 := by
      rw [hz0v, DuffingMathieu.pos_vdp]; ring
    have hvel0 : vel ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ' 0 := by
      rw [hz0v, DuffingMathieu.vel_vdp hν.ne']
    have hU' := loaded_unique_Icc hp (τ := 0) (T₁ := T) (fun s hs => (hsz s hs).1)
      (fun s hs => (hsz s hs).2) (fun s _ => hδ s) (fun s _ => hδ' s) hpos0 hvel0
    refine ⟨z, hzc, ?_, hz0v⟩
    obtain ⟨e1, e2⟩ := hU' T ⟨hT0.le, le_rfl⟩
    have h5 : ((√ε : ℝ) : ℂ) * z T = vdp ν T (δ T - δ₀) (δ' T) := by
      rw [← e1, ← e2, add_sub_cancel_left, vdp_pos_vel₆ hν.ne']
    have h7 : vdp ν T (δ T - δ₀) (δ' T) = vdp ν 0 (δ 0 - δ₀) (δ' 0) := by
      rw [hTδ, hTδ', hT, vdp_period₆ hν]
    exact mul_left_cancel₀ hs0' (h5.trans (h7.trans hz0v.symm))
  -- a swing solution equal to an orbit at `t = 0` is that orbit
  have hglob : ∀ w, loadedAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ δ δ' : ℝ → ℝ,
      (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
      ((√ε : ℝ) : ℂ) * x w 0 = vdp ν 0 (δ 0 - δ₀) (δ' 0) → δ = δw w ∧ δ' = δw' w := by
    intro w hw0 hwR δ δ' hδ hδ' h0
    refine loaded_unique_univ₆ hp hδ hδ' (fun t => (hsw w hw0 hwR t).1)
      (fun t => (hsw w hw0 hwR t).2) (t₀ := 0) ?_ ?_
    · show δ 0 = δ₀ + pos ν (((√ε : ℝ) : ℂ) * x w 0) 0
      rw [h0, DuffingMathieu.pos_vdp]; ring
    · show δ' 0 = vel ν (((√ε : ℝ) : ℂ) * x w 0) 0
      rw [h0, DuffingMathieu.vel_vdp hν.ne']
  -- uniqueness near each locked state
  have hlocal : ∀ w, loadedAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ δ δ' : ℝ → ℝ,
      (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
      δ T = δ 0 → δ' T = δ' 0 →
      ‖vdp ν 0 (δ 0 - δ₀) (δ' 0) - ((√ε : ℝ) : ℂ) * w‖ ≤ √ε * r₀ → δ = δw w ∧ δ' = δw' w := by
    intro w hw0 hwR δ δ' hδ hδ' hTδ hTδ' h0
    have h0' : ‖vdp ν 0 (δ 0 - δ₀) (δ' 0)‖ ≤ √ε * (R + 3 / 2) := by
      have := norm_le_norm_add_norm_sub' (vdp ν 0 (δ 0 - δ₀) (δ' 0)) (((√ε : ℝ) : ℂ) * w)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at this
      nlinarith
    obtain ⟨z, hz, hzT, hz0v⟩ := hcore δ δ' hδ hδ' hTδ hTδ' h0'
    have hzw : ‖z 0 - w‖ ≤ r₁ := by
      have e : vdp ν 0 (δ 0 - δ₀) (δ' 0) - ((√ε : ℝ) : ℂ) * w = ((√ε : ℝ) : ℂ) * (z 0 - w) := by
        rw [mul_sub, hz0v]
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h0
      exact (le_of_mul_le_mul_left h0 hs0).trans hr₀1
    have hzx := hloc z hz hzT w ((hAe' w).symm.trans hw0) hwR hzw
    exact hglob w hw0 hwR δ δ' hδ hδ' (by rw [← hzx]; exact hz0v)
  have hper : ∀ w, loadedAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ s,
      δw w (s + 2 * Real.pi / ν) = δw w s ∧ δw' w (s + 2 * Real.pi / ν) = δw' w s := by
    intro w hw0 hwR s
    have h1 : x w (s + 2 * Real.pi / ν) = x w s := (hx w ((hAe' w).symm.trans hw0) hwR).2.1 s
    simp only [hδw, hδw', h1, pos_period₆ hν, vel_period₆ hν, and_self]
  refine ⟨δw, δw', fun w hw0 hwR => ⟨fun t => (hsw w hw0 hwR t).1, fun t => (hsw w hw0 hwR t).2,
    hper w hw0 hwR, fun t => ?_, fun t => ?_, hlocal w hw0 hwR⟩, fun t => ?_, ?_⟩
  · have hw0' := (hAe' w).symm.trans hw0
    show ‖vdp ν t (δ₀ + pos ν (((√ε : ℝ) : ℂ) * x w t) t - δ₀)
      (vel ν (((√ε : ℝ) : ℂ) * x w t) t) - ((√ε : ℝ) : ℂ) * w‖ ≤ C * ε
    rw [add_sub_cancel_left, vdp_pos_vel₆ hν.ne', ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hs0.le]
    calc √ε * ‖x w t - w‖ ≤ √ε * (√ε * C) :=
          mul_le_mul_of_nonneg_left ((hx w hw0' hwR).2.2.2 t) hs0.le
      _ = C * (√ε * √ε) := by ring
      _ = C * ε := by rw [hss]
  · -- the half-period shift of the orbit of `w*` is the orbit of `−w*`
    have hw0' : loadedAmp b d ν δ₀ (-w) = 0 := by
      have e : loadedAmp b d ν δ₀ (-w) = -loadedAmp b d ν δ₀ w :=
        Saturation.ampField_neg _ _ _ _ _ w
      rw [e, hw0, neg_zero]
    have hwR' : ‖-w‖ ≤ R + 1 := by rw [norm_neg]; exact hwR
    set a := Real.pi / ν with ha
    have hδs : ∀ s, HasDerivAt (fun s => δw w (s + a)) (δw' w (s + a)) s := fun s =>
      ((hsw w hw0 hwR (s + a)).1).comp_add_const s a
    have hδs' : ∀ s, HasDerivAt (fun s => δw' w (s + a))
        ((loadedSwing p δ₀ ε (2 * ν) s).accel (δw w (s + a)) (δw' w (s + a))) s := fun s => by
      have h := ((hsw w hw0 hwR (s + a)).2).comp_add_const s a
      rw [ha, loadedSwing_half₆ hν] at h
      exact h
    have hTs : δw w (T + a) = δw w (0 + a) := by
      rw [show T + a = a + 2 * Real.pi / ν by rw [hT]; ring, zero_add, (hper w hw0 hwR a).1]
    have hTs' : δw' w (T + a) = δw' w (0 + a) := by
      rw [show T + a = a + 2 * Real.pi / ν by rw [hT]; ring, zero_add, (hper w hw0 hwR a).2]
    have hstart : ‖vdp ν 0 (δw w (0 + a) - δ₀) (δw' w (0 + a)) - ((√ε : ℝ) : ℂ) * -w‖ ≤
        √ε * r₀ := by
      have e : vdp ν 0 (δw w (0 + a) - δ₀) (δw' w (0 + a)) =
          -(((√ε : ℝ) : ℂ) * x w a) := by
        rw [zero_add, ← neg_neg (vdp ν 0 _ _), ← vdp_half₆ hν, zero_add]
        show -vdp ν a (δ₀ + pos ν (((√ε : ℝ) : ℂ) * x w a) a - δ₀)
          (vel ν (((√ε : ℝ) : ℂ) * x w a) a) = _
        rw [add_sub_cancel_left, vdp_pos_vel₆ hν.ne']
      rw [e, mul_neg, neg_sub_neg, norm_sub_rev, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs0.le]
      exact mul_le_mul_of_nonneg_left
        (((hx w ((hAe' w).symm.trans hw0) hwR).2.2.2 a).trans hsC) hs0.le
    obtain ⟨h1, h2⟩ := hlocal (-w) hw0' hwR' (fun s => δw w (s + a)) (fun s => δw' w (s + a))
      hδs hδs' hTs hTs' hstart
    exact ⟨(congrFun h1 t).symm, (congrFun h2 t).symm⟩
  · -- the trivial zero carries the operating point
    have h0 : loadedAmp b d ν δ₀ 0 = 0 := Saturation.ampField_zero _ _ _ _ _
    have hzs : ∀ s, HasDerivAt (fun _ : ℝ => (0 : ℝ))
        ((loadedSwing p δ₀ ε (2 * ν) s).accel ((fun _ : ℝ => δ₀) s)
          ((fun _ : ℝ => (0 : ℝ)) s)) s := fun s => by
      simpa [SwingParams.accel, SwingParams.Pe, loadedSwing] using hasDerivAt_const s (0 : ℝ)
    obtain ⟨h1, h2⟩ := hlocal 0 h0 (by rw [norm_zero]; linarith) (fun _ => δ₀) (fun _ => 0)
      (fun s => hasDerivAt_const s δ₀) hzs rfl rfl (by simp [vdp]; positivity)
    exact ⟨(congrFun h1 t).symm, (congrFun h2 t).symm⟩
  · -- the classification
    intro δ δ' hδ hδ' hTδ hTδ' h0
    obtain ⟨z, hz, hzT, hz0v⟩ := hcore δ δ' hδ hδ' hTδ hTδ'
      (h0.trans (mul_le_mul_of_nonneg_left (by linarith) hs0.le))
    have hz0R : ‖z 0‖ ≤ R := by
      have e : ‖vdp ν 0 (δ 0 - δ₀) (δ' 0)‖ = √ε * ‖z 0‖ := by
        rw [← hz0v, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      rw [e] at h0
      exact le_of_mul_le_mul_left h0 hs0
    obtain ⟨w, hw0, hwR, hzx⟩ := hK z hz hzT hz0R
    have hw0' : loadedAmp b d ν δ₀ w = 0 := (hAe' w).trans hw0
    exact ⟨w, hw0', hwR, hglob w hw0' hwR δ δ' hδ hδ' (by rw [← hzx]; exact hz0v)⟩

end powerlib.Synchronous.LoadedSubharmonicOrbit
