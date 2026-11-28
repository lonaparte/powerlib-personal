import theorem.PowerSystem.Synchronous.SubharmonicOrbit
import theorem.Averaging.PeriodicOrbitClassification
import theorem.ParametricResonance.LockedStatePairs

/-! # All half-frequency periodic swing oscillations of small amplitude

`theorem/PowerSystem/Synchronous/SubharmonicOrbit.lean` and
`theorem/PowerSystem/Synchronous/SubharmonicOrbitUnique.lean` turn every nondegenerate locked state
`w*` of the averaged amplitude equation of TR-110's pumped swing model into a `2π/ν`-periodic
solution, unique in a tube around `√ε w* e^{jνt}`. Whether the swing model has other periodic
solutions of small amplitude was left open. Here all of them are classified: for every radius `R`
and all small depths `ε`, every `2π/ν`-periodic solution of the swing model whose phase-plane point
starts in the disc `|δ(0) − jδ̇(0)/ν| ≤ √ε R` is the unloaded equilibrium `δ ≡ 0` or one of the
subharmonic orbits, one for each locked state `w*` with `|w*| ≤ R`; the locked states come in
pairs `±w*` (`Saturation.zero_pair_iff`), and the orbit of `−w*` is the orbit of `w*` shifted by
half its period `π/ν`. The zeros of the averaged field in the disc are counted explicitly
(`Saturation.shift_zeros_ncard`): the trivial state and two locked states for each of the
amplitudes `|w*|² = −16(d/(2ν) ± s)/ν`, `s = √(ν²/16 − b²/4)`, lying in `(0, R²]`.

Model boundary.
* The swing model of `SubharmonicOrbit`: one generator, TR-110's swing equation (3-8) with
  `P_e = K_s(t) sin δ + K_d Δω`, `K_s(t) = K_s(1 + ε cos 2νt)` (pump `Ω = 2ν`, `ν > 0`), `P_m = 0`,
  `Params.Pos`, state `(δ, δ̇)`, continuous time, in the weakly nonlinear scaling `2ξω_n = εb`,
  `ω_n² = ν² − εd`; the constants depend on `b, d, ν, R` only, and every machine of the scaling
  with `0 < ε ≤ ε₀` is covered.
* The disc is the phase-plane disc `‖vdp ν 0 δ(0) δ̇(0)‖ = |δ(0) − jδ̇(0)/ν| ≤ √ε R` of the van der
  Pol amplitude at `t = 0`, `R ≥ 0` arbitrary (amplitudes of the order `√ε` of the subharmonic
  oscillation); a periodic solution is one that returns after one period `2π/ν`
  (`(δ, δ̇)(2π/ν) = (δ, δ̇)(0)`). Solutions of other periods, and periodic solutions of larger
  amplitude, are not classified.
* Locked states are the zeros of `limitAmp b d ν = ampField (b/2) (d/(2ν)) (jν/4) 0 (−ν/16)`; all
  zeros in the disc must be nondegenerate (`det (limitJac b d ν w*) ≠ 0`). By
  `Saturation.shift_det_eq_zero_iff` this excludes exactly the first-order boundary
  `(b/2)² + (d/(2ν))² = (ν/4)²` (`σ² + Δ² = |c|²`, the trivial state degenerate) and the
  fold `(b/2)² = (ν/4)²` when its locked amplitude `−8d/ν²` lies in `(0, R²]`
  (`limitJac_det_ne_zero`).
* Excluded as in `SubharmonicOrbit`: a loaded operating point
  (`theorem/PowerSystem/Synchronous/LoadedSubharmonicClassification.lean`), AVR/PSS, network and
  multi-machine dynamics, a modulation of `K_d`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11);
Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations* (the second
theorem of Bogoliubov); Hale, *Ordinary Differential Equations*, Ch. V (all periodic solutions
near a compact set from the zeros of the averaged field); the generic classification
`Averaging.periodic_orbit_classification_compact`, the zeros `Saturation.shift_zeros`,
`Saturation.shift_zeros_ncard`, `Saturation.shift_det_eq_zero_iff`; the scaled swing model
`SubharmonicOrbit.hasDerivAt_scaled_limit`, `SubharmonicOrbit.swing_of_scaled`,
`SubharmonicOrbit.uncut_of_real`, `SubharmonicOrbit.averaged_limitCut_at`,
`SubharmonicOrbit.swing_unique_Icc`, `SubharmonicOrbit.swing_field_lipschitz`.

Sharpenings.
* `SubharmonicOrbitUnique.subharmonic_orbit_unique` claims uniqueness only among the periodic
  solutions that stay in a tube of radius `√ε r₀` around `√ε w* e^{jνt}` for all `t`. Here every
  `2π/ν`-periodic swing solution starting in the disc of radius `√ε R` — for any `R` — is the
  equilibrium or one of the finitely many subharmonic orbits, and each orbit is the only periodic
  solution starting within `√ε r₀` of `√ε w*` at `t = 0`.

Results.
* `limitAmp_zeros`, `limitAmp_finite`, `limitAmp_ncard` — the zeros of the averaged limit field:
  `0` and the pairs `±w*` on the amplitudes `−16(d/(2ν) ± s)/ν`; finitely many; `1 + 2N` in the
  disc.
* `limitJac_det_ne_zero` — off the first-order boundary and the fold every zero is
  nondegenerate.
* `scaled_classification` — the cut-off scaled model in real coordinates: the periodic solutions
  starting in the disc `‖x(0)‖ ≤ R` are the Bogoliubov orbits of the zeros in the disc.
* `subharmonic_classification` — **all small periodic swing solutions**: for `0 < ε ≤ ε₀` the
  `2π/ν`-periodic swing solutions starting in the disc of radius `√ε R` are exactly the orbits
  `(δ_{w*}, δ̇_{w*})` of the zeros `|w*| ≤ R`, with `δ_0 ≡ 0`, the phase-plane tube
  `‖vdp − √ε w*‖ ≤ Cε√ε`, `δ_{−w*}(t) = δ_{w*}(t + π/ν)`, and uniqueness near each `√ε w*`.
-/

noncomputable section
namespace powerlib.Synchronous.SubharmonicOrbit

open Complex Set Filter Topology
open powerlib.Synchronous.OscillationPhasor
open powerlib.Synchronous.ParametricSwing (frozen natFreq)
open powerlib.Synchronous.ParametricSaturation (modKs remainder)
open powerlib.ParametricResonance
open powerlib.ParametricResonance.DuffingMathieu (pos vel vdp accel vdpField)
open powerlib.ParametricResonance.Saturation (ampField ampSystem ampJacobian)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Elementary facts -/

@[tmio T, powerlib_foundation] private theorem norm_toReal_symm₅ (x : ℝ²) :
    ‖toReal.symm x‖ = ‖x‖ := by
  have h := Saturation.norm_toReal (toReal.symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

@[tmio T, powerlib_foundation] private theorem toEuclideanCLM_inv_apply₅
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

@[tmio M, powerlib_foundation] private theorem vdp_pos_vel₅ {ν : ℝ} (hν : ν ≠ 0) (z : ℂ) (t : ℝ) :
    vdp ν t (pos ν z t) (vel ν z t) = z := by
  have h1 : (((pos ν z t : ℝ) : ℂ) - (((vel ν z t) / ν : ℝ) : ℂ) * I) =
      z * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [pos]
    · simp [vel]; field_simp
  rw [vdp, h1, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

@[tmio T, powerlib_foundation] private theorem exp_shift₅ {ν : ℝ} (t a : ℝ)
    (k : ℤ) (ha : ν * a = k * Real.pi) :
    Complex.exp (((ν * (t + a) : ℝ) : ℂ) * I) =
      (-1) ^ k * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
  rw [show ((ν * (t + a) : ℝ) : ℂ) * I = ((ν * t : ℝ) : ℂ) * I + k * (Real.pi * I) by
    push_cast; rw [mul_add, ← ofReal_mul ν a, ha]; push_cast; ring, Complex.exp_add,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, mul_comm]

@[tmio T, powerlib_foundation] private theorem pos_period₅ {ν : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    pos ν w (t + 2 * Real.pi / ν) = pos ν w t := by
  simp only [pos, exp_shift₅ (ν := ν) t (2 * Real.pi / ν) 2 (by field_simp; ring)]
  norm_num

@[tmio T, powerlib_foundation] private theorem vel_period₅ {ν : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    vel ν w (t + 2 * Real.pi / ν) = vel ν w t := by
  simp only [vel, exp_shift₅ (ν := ν) t (2 * Real.pi / ν) 2 (by field_simp; ring)]
  norm_num

@[tmio M, powerlib_foundation] private theorem vdp_period₅ {ν : ℝ} (hν : 0 < ν) (x x' : ℝ) :
    vdp ν (2 * Real.pi / ν) x x' = vdp ν 0 x x' := by
  have hE : Complex.exp (-(((ν * (2 * Real.pi / ν) : ℝ) : ℂ) * I)) =
      Complex.exp (-(((ν * 0 : ℝ) : ℂ) * I)) := by
    rw [show ν * (2 * Real.pi / ν) = 2 * Real.pi by field_simp, mul_zero,
      show -(((2 * Real.pi : ℝ) : ℂ) * I) = -(2 * Real.pi * I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    simp
  simp only [vdp, hE]

/-- Half a period turns the van der Pol amplitude into its opposite. -/
@[tmio M, powerlib_foundation] private theorem vdp_half₅ {ν : ℝ} (hν : 0 < ν) (t x x' : ℝ) :
    vdp ν (t + Real.pi / ν) x x' = -vdp ν t x x' := by
  have h := exp_shift₅ (ν := ν) t (Real.pi / ν) 1 (by field_simp; ring)
  have h' : Complex.exp (-(((ν * (t + Real.pi / ν) : ℝ) : ℂ) * I)) =
      -Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, Complex.exp_neg, h]
    simp
  simp only [vdp, h']
  ring

variable {p : Params}

/-- Global uniqueness for the swing model. -/
@[tmio M, powerlib_domain] private theorem swing_unique_univ₅ (hp : p.Pos) {ε Ω : ℝ}
    {δ₁ δ₁' δ₂ δ₂' : ℝ → ℝ} (h1 : ∀ t, HasDerivAt δ₁ (δ₁' t) t)
    (h1' : ∀ t, HasDerivAt δ₁' ((frozen p (modKs p ε Ω) t).toSwing.accel (δ₁ t) (δ₁' t)) t)
    (h2 : ∀ t, HasDerivAt δ₂ (δ₂' t) t)
    (h2' : ∀ t, HasDerivAt δ₂' ((frozen p (modKs p ε Ω) t).toSwing.accel (δ₂ t) (δ₂' t)) t)
    {t₀ : ℝ} (h0 : δ₁ t₀ = δ₂ t₀) (h0' : δ₁' t₀ = δ₂' t₀) : δ₁ = δ₂ ∧ δ₁' = δ₂' := by
  have h := ODE_solution_unique_univ
    (v := fun t (q : ℝ × ℝ) => (q.2, (frozen p (modKs p ε Ω) t).toSwing.accel q.1 q.2))
    (s := fun _ => univ) (f := fun t => (δ₁ t, δ₁' t)) (g := fun t => (δ₂ t, δ₂' t)) (t₀ := t₀)
    (fun t => (swing_field_lipschitz hp ε Ω t).lipschitzOnWith)
    (fun t => ⟨(h1 t).prodMk (h1' t), mem_univ _⟩) (fun t => ⟨(h2 t).prodMk (h2' t), mem_univ _⟩)
    (by simp [h0, h0'])
  exact ⟨funext fun t => congrArg Prod.fst (congrFun h t),
    funext fun t => congrArg Prod.snd (congrFun h t)⟩

/-- The pumped swing model is `π/ν`-periodic in time. -/
@[tmio M, powerlib_domain] private theorem accel_half₅ (hp : p.Pos) {ε ν : ℝ} (hν : 0 < ν)
    (t x y : ℝ) :
    (frozen p (modKs p ε (2 * ν)) (t + Real.pi / ν)).toSwing.accel x y =
      (frozen p (modKs p ε (2 * ν)) t).toSwing.accel x y := by
  rw [ParametricSaturation.accel_eq hp, ParametricSaturation.accel_eq hp]
  have : Real.cos (2 * ν * (t + Real.pi / ν)) = Real.cos (2 * ν * t) := by
    rw [show 2 * ν * (t + Real.pi / ν) = 2 * ν * t + 2 * Real.pi by field_simp,
      Real.cos_add_two_pi]
  rw [this]

/-! ## The zeros of the averaged limit field -/

@[tmio M, powerlib_foundation] private theorem pump_ne_zero₅ {ν : ℝ} (hν : 0 < ν) :
    I * ((ν / 4 : ℝ) : ℂ) ≠ 0 :=
  mul_ne_zero I_ne_zero (by exact_mod_cast (by positivity : ν / 4 ≠ 0))

@[tmio M, powerlib_foundation] private theorem norm_pump₅ {ν : ℝ} (hν : 0 < ν) :
    ‖I * ((ν / 4 : ℝ) : ℂ)‖ = ν / 4 := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- **The zeros of the averaged limit field.** Every zero of `limitAmp b d ν` is the trivial state
or a locked state with `|w*|² = −16(d/(2ν) + s)/ν` or `|w*|² = −16(d/(2ν) − s)/ν`,
`s = √(ν²/16 − b²/4)` (`b² ≤ ν²/4`); each of these amplitudes that is positive carries exactly the
pair `w*`, `−w*` (`Saturation.shift_zeros` with `σ = b/2`, `Δ = d/(2ν)`, `|c| = ν/4`,
`β = −ν/16`). -/
@[tmio M, powerlib_foundation] theorem limitAmp_zeros {b d ν : ℝ} (hν : 0 < ν) :
    (∀ w : ℂ, limitAmp b d ν w = 0 → w = 0 ∨ ((b / 2) ^ 2 ≤ (ν / 4) ^ 2 ∧
      (‖w‖ ^ 2 = -16 * (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν ∨
        ‖w‖ ^ 2 = -16 * (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν))) ∧
    ∀ A : ℝ, 0 < A → (b / 2) ^ 2 ≤ (ν / 4) ^ 2 →
      (A = -16 * (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν ∨
        A = -16 * (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν) →
      ∃ w : ℂ, ‖w‖ ^ 2 = A ∧ w ≠ -w ∧
        ∀ z : ℂ, (‖z‖ ^ 2 = A ∧ limitAmp b d ν z = 0) ↔ (z = w ∨ z = -w) := by
  have hβ : -ν / 16 ≠ 0 := by have := hν.ne'; intro h; apply this; linarith
  have hdiv : ∀ u : ℝ, u / (-ν / 16) = -16 * u / ν := fun u => by field_simp
  obtain ⟨h1, h2⟩ := Saturation.shift_zeros (σ := b / 2) (Δ := d / (2 * ν)) (pump_ne_zero₅ hν) hβ
  rw [norm_pump₅ hν] at h1 h2
  simp only [hdiv] at h1 h2
  exact ⟨h1, h2⟩

/-- The zero set of the averaged limit field is finite. -/
@[tmio M, powerlib_foundation] theorem limitAmp_finite {b d ν : ℝ} (hν : 0 < ν) :
    {w : ℂ | limitAmp b d ν w = 0}.Finite :=
  Saturation.shift_zeros_finite (pump_ne_zero₅ hν)
    (by have := hν.ne'; intro h; apply this; linarith)

/-- **The number of zeros in the disc `|w| ≤ R`**: off the fold (`(b/2)² < (ν/4)²`), the trivial
state and two locked states for each of the amplitudes `−16(d/(2ν) ± s)/ν` in `(0, R²]`
(`Saturation.shift_zeros_ncard`). -/
@[tmio M, powerlib_foundation] theorem limitAmp_ncard {b d ν : ℝ} (hν : 0 < ν)
    (hb : (b / 2) ^ 2 < (ν / 4) ^ 2) {R : ℝ} (hR : 0 ≤ R) :
    {w : ℂ | limitAmp b d ν w = 0 ∧ ‖w‖ ≤ R}.ncard =
      1 + 2 * ((if 0 < -16 * (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν ∧
          -16 * (d / (2 * ν) + √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν ≤ R ^ 2 then 1 else 0) +
        (if 0 < -16 * (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν ∧
          -16 * (d / (2 * ν) - √((ν / 4) ^ 2 - (b / 2) ^ 2)) / ν ≤ R ^ 2 then 1 else 0)) := by
  have hβ : -ν / 16 ≠ 0 := by have := hν.ne'; intro h; apply this; linarith
  have hdiv : ∀ u : ℝ, u / (-ν / 16) = -16 * u / ν := fun u => by field_simp
  have h := Saturation.shift_zeros_ncard (σ := b / 2) (Δ := d / (2 * ν)) (pump_ne_zero₅ hν) hβ
    (by rw [norm_pump₅ hν]; exact hb) hR
  rw [norm_pump₅ hν] at h
  simp only [hdiv] at h
  exact h

/-- **The nondegenerate parameter set.** Off the first-order boundary
`(b/2)² + (d/(2ν))² ≠ (ν/4)²` and off the fold `(b/2)² ≠ (ν/4)²`, every zero of the averaged limit
field has an invertible Jacobian (`Saturation.shift_det_eq_zero_iff`: these are exactly the
degenerate cases). -/
@[tmio M, powerlib_foundation] theorem limitJac_det_ne_zero {b d ν : ℝ} (hν : 0 < ν)
    (hlin : (b / 2) ^ 2 + (d / (2 * ν)) ^ 2 ≠ (ν / 4) ^ 2) (hfold : (b / 2) ^ 2 ≠ (ν / 4) ^ 2)
    {w : ℂ} (hw : limitAmp b d ν w = 0) : (limitJac b d ν w).det ≠ 0 := by
  have hβ : -ν / 16 ≠ 0 := by have := hν.ne'; intro h; apply this; linarith
  intro h
  rcases (Saturation.shift_det_eq_zero_iff hβ hw).mp h with h' | h'
  · rw [norm_pump₅ hν] at h'; exact hlin h'.2
  · rw [norm_pump₅ hν] at h'; exact hfold h'.2

/-! ## The classification for the cut-off scaled model -/

/-- **The periodic solutions of the cut-off scaled model starting in a disc.** Let every zero of
the averaged limit field in the disc `|w| ≤ R` be nondegenerate. There are `ε₀ > 0`, `C, D ≥ 0`
and `r₀ > 0` (depending on `b, d, ν, R`) such that for `0 < ε ≤ ε₀` and `ω_n² = ν² − εd` the real
form of the scaled swing model cut off at `R + 3` has, for each zero `w*` in the disc, a
`2π/ν`-periodic solution `x_{w*}` with `‖x_{w*}(t) − w*‖ ≤ Cε`, the only solution with
`x(2π/ν) = x(0)` and `‖x(0) − w*‖ ≤ r₀`; every solution with `x(2π/ν) = x(0)` and `‖x(0)‖ ≤ R` is
one of them; solutions exist from every initial state and drift by at most `Dε` over one period
(`Averaging.periodic_orbit_classification_compact`). -/
@[tmio M, powerlib_domain] theorem scaled_classification {b d ν : ℝ} (hν : 0 < ν) {R : ℝ}
    (hR : 0 ≤ R) (hdeg : ∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R → (limitJac b d ν w).det ≠ 0) :
    ∃ ε₀ C D r₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ ωn : ℝ, ωn ^ 2 = ν ^ 2 - ε * d →
      ∃ x : ℂ → ℝ → ℝ²,
        (∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R →
          (∀ t, HasDerivAt (x w) (ε • realField (limitCut b d ν (R + 3)) (x w t) t +
            ε ^ 2 • realField (rCut ωn ν d ε (R + 3)) (x w t) t) t) ∧
          (∀ t, x w (t + 2 * Real.pi / ν) = x w t) ∧ ∀ t, ‖x w t - toReal w‖ ≤ C * ε) ∧
        (∀ z : ℝ → ℝ², (∀ t, HasDerivAt z (ε • realField (limitCut b d ν (R + 3)) (z t) t +
            ε ^ 2 • realField (rCut ωn ν d ε (R + 3)) (z t) t) t) →
          z (2 * Real.pi / ν) = z 0 → ∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R →
          ‖z 0 - toReal w‖ ≤ r₀ → z = x w) ∧
        (∀ z : ℝ → ℝ², (∀ t, HasDerivAt z (ε • realField (limitCut b d ν (R + 3)) (z t) t +
            ε ^ 2 • realField (rCut ωn ν d ε (R + 3)) (z t) t) t) →
          z (2 * Real.pi / ν) = z 0 → ‖z 0‖ ≤ R →
          ∃ w, limitAmp b d ν w = 0 ∧ ‖w‖ ≤ R ∧ z = x w ∧ ‖z 0 - toReal w‖ ≤ C * ε) ∧
        (∀ y₀ : ℝ², ∃ z : ℝ → ℝ², z 0 = y₀ ∧ ∀ t, HasDerivAt z
          (ε • realField (limitCut b d ν (R + 3)) (z t) t +
            ε ^ 2 • realField (rCut ωn ν d ε (R + 3)) (z t) t) t) ∧
        ∀ z : ℝ → ℝ², (∀ t, HasDerivAt z (ε • realField (limitCut b d ν (R + 3)) (z t) t +
            ε ^ 2 • realField (rCut ωn ν d ε (R + 3)) (z t) t) t) →
          ∀ t ∈ Icc 0 (2 * Real.pi / ν), ‖z t - z 0‖ ≤ D * ε := by
  set ρc := R + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  set Kω := ν ^ 2 + |d| with hKω
  have hK0 : 0 ≤ Kω := by positivity
  have hf := realField_hyp (DuffingMathieu.cutField_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2)
    (γ := -(ν ^ 2) / 6) hν hρc0)
  set ℓ := DuffingMathieu.lipConst b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  have hℓ0 : 0 ≤ ℓ := hf.2.1
  have hM0 : 0 ≤ M := by positivity
  set ℓr := rLip ν d Kω (2 * ρc) with hℓr
  set Mr := rBound ν d Kω (2 * ρc) with hMr
  have hℓr0 : 0 ≤ ℓr := by rw [hℓr, rLip]; positivity
  have hMr0 : 0 ≤ Mr := by rw [hMr, rBound]; positivity
  -- the zeros in the disc
  set Z : Set ℂ := {w | limitAmp b d ν w = 0 ∧ ‖w‖ ≤ R} with hZ
  have hZf : Z.Finite := (limitAmp_finite hν).subset fun w hw => hw.1
  have : Finite Z := hZf.to_subtype
  have hball : ∀ (i : Z) (x : ℝ²), ‖x - toReal i.1‖ ≤ 1 → ‖x‖ ≤ R + 1 := by
    intro i x hx
    have := norm_le_norm_add_norm_sub' x (toReal i.1)
    rw [Saturation.norm_toReal] at this
    linarith [i.2.2]
  have hzero : ∀ y ∈ Metric.closedBall (0 : ℝ²) R,
      Averaging.fieldAverage (realField (limitCut b d ν ρc)) T y = 0 →
      ∃ i : Z, y = toReal i.1 := by
    intro y hy h0
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [fieldAverage_limitCut hν (by linarith)] at h0
    have h1 : toReal (limitAmp b d ν (toReal.symm y)) = 0 := by
      rw [← Saturation.toReal_ampField, ContinuousLinearEquiv.apply_symm_apply]; exact h0
    have h2 : limitAmp b d ν (toReal.symm y) = 0 := by
      rwa [ContinuousLinearEquiv.map_eq_zero_iff] at h1
    exact ⟨⟨toReal.symm y, h2, by rw [norm_toReal_symm₅]; exact hy⟩,
      (ContinuousLinearEquiv.apply_symm_apply _ _).symm⟩
  obtain ⟨ε₁, C, r₀, hε₁, hC, hr₀, hcl⟩ := Averaging.periodic_orbit_classification_compact hf
    hℓr0 hMr0 (ι := Z) (ystar := fun i => toReal i.1) (ρ := fun _ => 1)
    (L₂ := fun _ => ν * (R + 1)) (Df := limitDeriv b d ν)
    (A := fun i => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (limitJac b d ν i.1))
    (B := fun i => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (limitJac b d ν i.1)⁻¹)
    (fun _ => one_pos) (fun _ => by positivity)
    (fun i x hx t => hasFDerivAt_limitCut (by linarith [hball i x hx]) t)
    (fun i x y hx hy t => norm_limitDeriv_sub_le hν (hball i x hx) (hball i y hy) t)
    (fun i => continuous_limitDeriv b d ν _)
    (fun i => (averaged_limitCut_at hν i.2.1 (by linarith [i.2.2])).1)
    (fun i => (averaged_limitCut_at hν i.2.1 (by linarith [i.2.2])).2)
    (fun i v => (toEuclideanCLM_inv_apply₅ (hdeg i.1 i.2.1 i.2.2) v).1)
    (fun i v => (toEuclideanCLM_inv_apply₅ (hdeg i.1 i.2.1 i.2.2) v).2)
    (isCompact_closedBall 0 R) hzero
  refine ⟨min ε₁ 1, C, (M + Mr) * T, r₀, lt_min hε₁ one_pos, min_le_right _ _, hC,
    by positivity, hr₀, fun ε hε hεε₀ ωn hωn => ?_⟩
  have hε1 : ε ≤ 1 := hεε₀.trans (min_le_right _ _)
  have hKω' : ωn ^ 2 ≤ Kω := by
    rw [hωn, hKω]
    have : -(ε * d) ≤ |d| := by
      have h1 : |ε * d| ≤ |d| := by
        rw [abs_mul, abs_of_pos hε]; exact mul_le_of_le_one_left (abs_nonneg _) hε1
      linarith [neg_abs_le (ε * d)]
    linarith
  have hr := realField_hyp (rCut_hyp (d := d) hν hε hε1 hKω' hρc0)
  obtain ⟨x, hx, hun, hK⟩ := hcl ε hε (hεε₀.trans (min_le_left _ _)) _ hr
  classical
  set x' : ℂ → ℝ → ℝ² := fun w => if h : w ∈ Z then x ⟨w, h⟩ else 0 with hx'
  have hxw : ∀ (w : ℂ) (h : w ∈ Z), x' w = x ⟨w, h⟩ := fun w h => by simp [hx', h]
  refine ⟨x', fun w hw0 hwR => ?_, fun z hz hzT w hw0 hwR hzw => ?_, fun z hz hzT hzR => ?_,
    fun y₀ => ?_, fun z hz t ht => ?_⟩
  · rw [hxw w ⟨hw0, hwR⟩]
    exact hx ⟨w, hw0, hwR⟩
  · rw [hxw w ⟨hw0, hwR⟩]
    exact hun z hz hzT ⟨w, hw0, hwR⟩ hzw
  · obtain ⟨i, hzi, hi⟩ := hK z hz hzT (by rw [Metric.mem_closedBall, dist_zero_right]; exact hzR)
    refine ⟨i.1, i.2.1, i.2.2, ?_, hi⟩
    rw [hxw i.1 i.2]
    exact hzi
  · exact DuffingMathieu.exists_global_solution
      (Averaging.full_field_continuous hf.2.2.1 hr.2.2.1 ε)
      (fun t => Averaging.field_lipschitzWith hf.2.2.2.2.1 hr.2.2.2.2.1 hℓ0 hℓr0 hε.le t) y₀
  · have h := Averaging.solution_drift_le hf.2.2.2.2.2 hr.2.2.2.2.2 hε.le hε1 hz ht.1
    calc ‖z t - z 0‖ ≤ ε * (M + Mr) * (t - 0) := h
      _ ≤ ε * (M + Mr) * T := by gcongr; linarith [ht.2]
      _ = (M + Mr) * T * ε := by ring

/-! ## The classification for the swing model -/

/-- **All `2π/ν`-periodic swing oscillations of small amplitude.** Let every zero of the averaged
limit field `limitAmp b d ν` in the disc `|w| ≤ R` be nondegenerate (`limitJac_det_ne_zero`:
off the first-order boundary and the fold). There are `ε₀ > 0`, `C ≥ 0`, `r₀ > 0` (depending on
`b, d, ν, R` only) such that for every `0 < ε ≤ ε₀` and every machine of the scaling
`2ξω_n = εb`, `ω_n² = ν² − εd`, TR-110's swing model with `K_s(t) = K_s(1 + ε cos 2νt)` has for each
zero `w*`, `|w*| ≤ R`, a `2π/ν`-periodic solution `(δ_{w*}, δ̇_{w*})` with
`‖vdp ν t δ_{w*}(t) δ̇_{w*}(t) − √ε w*‖ ≤ Cε√ε` for all `t`, such that:
* `δ_0 ≡ 0` (the unloaded equilibrium is the orbit of the trivial zero);
* `δ_{−w*}(t) = δ_{w*}(t + π/ν)`: the locked pair `±w*` is one oscillation shifted by half its
  period;
* `(δ_{w*}, δ̇_{w*})` is the only solution returning after one period whose phase-plane point at
  `t = 0` lies within `√ε r₀` of `√ε w*`;
* every solution `(δ, δ̇)` with `(δ, δ̇)(2π/ν) = (δ, δ̇)(0)` and `|δ(0) − jδ̇(0)/ν| ≤ √ε R` is one
  of them (`scaled_classification`, `SubharmonicOrbit.swing_of_scaled`,
  `SubharmonicOrbit.swing_unique_Icc`). -/
@[tmio M, powerlib_domain] theorem subharmonic_classification {b d ν : ℝ} (hν : 0 < ν) {R : ℝ}
    (hR : 0 ≤ R) (hdeg : ∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R → (limitJac b d ν w).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      2 * p.dampingRatio * natFreq p = ε * b → natFreq p ^ 2 = ν ^ 2 - ε * d →
      ∃ δw δw' : ℂ → ℝ → ℝ,
        (∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R →
          (∀ t, HasDerivAt (δw w) (δw' w t) t) ∧
          (∀ t, HasDerivAt (δw' w)
            ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δw w t) (δw' w t)) t) ∧
          (∀ t, δw w (t + 2 * Real.pi / ν) = δw w t ∧ δw' w (t + 2 * Real.pi / ν) = δw' w t) ∧
          (∀ t, ‖vdp ν t (δw w t) (δw' w t) - ((√ε : ℝ) : ℂ) * w‖ ≤ C * ε * √ε) ∧
          (∀ t, δw (-w) t = δw w (t + Real.pi / ν) ∧ δw' (-w) t = δw' w (t + Real.pi / ν)) ∧
          ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
            (∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t) →
            δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
            ‖vdp ν 0 (δ 0) (δ' 0) - ((√ε : ℝ) : ℂ) * w‖ ≤ √ε * r₀ → δ = δw w ∧ δ' = δw' w) ∧
        (∀ t, δw 0 t = 0 ∧ δw' 0 t = 0) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t) →
          δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
          ‖vdp ν 0 (δ 0) (δ' 0)‖ ≤ √ε * R →
          ∃ w, limitAmp b d ν w = 0 ∧ ‖w‖ ≤ R ∧ δ = δw w ∧ δ' = δw' w := by
  obtain ⟨ε₁, C, D, r₁, hε₁, hε₁1, hC, hD, hr₁, hcl⟩ := scaled_classification hν hR hdeg
  set r₀ := min r₁ (1 / 2) with hr₀
  have hr₀0 : 0 < r₀ := lt_min hr₁ (by norm_num)
  set ε₀ := min ε₁ (min (1 / (2 * (D + 1))) (r₀ / (C + 1))) with hε₀
  refine ⟨ε₀, C, r₀, lt_min hε₁ (lt_min (by positivity) (by positivity)), hC, hr₀0,
    fun ε hε hεε₀ p hp hb hd => ?_⟩
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hDε : D * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * (D + 1)) := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hCε : C * ε ≤ r₀ := by
    have h1 : ε ≤ r₀ / (C + 1) := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hr₀h : r₀ ≤ 1 / 2 := min_le_right _ _
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  set ρc := R + 3 with hρc
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨x, hx, hun, hK, hex, hdrift⟩ := hcl ε hε hεε₁ (natFreq p) hd
  -- the swing solutions carried by the orbits
  set δw : ℂ → ℝ → ℝ := fun w t => pos ν (((√ε : ℝ) : ℂ) * toReal.symm (x w t)) t with hδw
  set δw' : ℂ → ℝ → ℝ := fun w t => vel ν (((√ε : ℝ) : ℂ) * toReal.symm (x w t)) t with hδw'
  have hxin : ∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R → ∀ t, ‖x w t‖ ≤ ρc := by
    intro w hw0 hwR t
    have h1 := (hx w hw0 hwR).2.2 t
    have := norm_le_norm_add_norm_sub' (x w t) (toReal w)
    rw [Saturation.norm_toReal] at this
    rw [hρc]; linarith
  have hsw : ∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R → ∀ t,
      HasDerivAt (δw w) (δw' w t) t ∧ HasDerivAt (δw' w)
        ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δw w t) (δw' w t)) t := fun w hw0 hwR t =>
    swing_of_scaled hp hν hε hb hd t (uncut_of_real t ((hx w hw0 hwR).1 t) (hxin w hw0 hwR t))
  -- a periodic swing solution starting near the disc is carried by a periodic scaled solution
  have hcore : ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t) →
      δ T = δ 0 → δ' T = δ' 0 → ‖vdp ν 0 (δ 0) (δ' 0)‖ ≤ √ε * (R + 1 / 2) →
      ∃ z : ℝ → ℝ², (∀ t, HasDerivAt z (ε • realField (limitCut b d ν ρc) (z t) t +
          ε ^ 2 • realField (rCut (natFreq p) ν d ε ρc) (z t) t) t) ∧ z T = z 0 ∧
        ((√ε : ℝ) : ℂ) * toReal.symm (z 0) = vdp ν 0 (δ 0) (δ' 0) := by
    intro δ δ' hδ hδ' hTδ hTδ' h0
    obtain ⟨z, hz0, hz⟩ := hex (toReal (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (δ 0) (δ' 0)))
    have hz0v : ((√ε : ℝ) : ℂ) * toReal.symm (z 0) = vdp ν 0 (δ 0) (δ' 0) := by
      rw [hz0, ContinuousLinearEquiv.symm_apply_apply]; field_simp
    have hz0n : ‖z 0‖ ≤ R + 1 / 2 := by
      have e : ‖vdp ν 0 (δ 0) (δ' 0)‖ = √ε * ‖z 0‖ := by
        rw [← hz0v, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_toReal_symm₅]
      rw [e] at h0
      exact le_of_mul_le_mul_left h0 hs0
    have hzn : ∀ t ∈ Icc 0 T, ‖z t‖ ≤ ρc := fun t ht => by
      have h1 := hdrift z hz t ht
      have := norm_le_norm_add_norm_sub' (z t) (z 0)
      rw [hρc]; linarith
    have hsz := fun t (ht : t ∈ Icc 0 T) =>
      swing_of_scaled hp hν hε hb hd t (uncut_of_real t (hz t) (hzn t ht))
    have hpos0 : pos ν (((√ε : ℝ) : ℂ) * toReal.symm (z 0)) 0 = δ 0 := by
      rw [hz0v, DuffingMathieu.pos_vdp]
    have hvel0 : vel ν (((√ε : ℝ) : ℂ) * toReal.symm (z 0)) 0 = δ' 0 := by
      rw [hz0v, DuffingMathieu.vel_vdp hν.ne']
    have hU := swing_unique_Icc hp (τ := 0) (T₁ := T) (fun s hs => (hsz s hs).1)
      (fun s hs => (hsz s hs).2) (fun s _ => hδ s) (fun s _ => hδ' s) hpos0 hvel0
    refine ⟨z, hz, ?_, hz0v⟩
    obtain ⟨e1, e2⟩ := hU T ⟨hT0.le, le_rfl⟩
    have h5 : ((√ε : ℝ) : ℂ) * toReal.symm (z T) = vdp ν T (δ T) (δ' T) := by
      rw [← e1, ← e2, vdp_pos_vel₅ hν.ne']
    have h7 : vdp ν T (δ T) (δ' T) = vdp ν 0 (δ 0) (δ' 0) := by
      rw [hTδ, hTδ', hT, vdp_period₅ hν]
    have h8 := mul_left_cancel₀ hs0' (h5.trans (h7.trans hz0v.symm))
    exact toReal.symm.injective h8
  -- a periodic swing solution equal to an orbit at `t = 0` is that orbit
  have hglob : ∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R → ∀ δ δ' : ℝ → ℝ,
      (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t) →
      ((√ε : ℝ) : ℂ) * toReal.symm (x w 0) = vdp ν 0 (δ 0) (δ' 0) → δ = δw w ∧ δ' = δw' w := by
    intro w hw0 hwR δ δ' hδ hδ' h0
    refine swing_unique_univ₅ hp hδ hδ' (fun t => (hsw w hw0 hwR t).1)
      (fun t => (hsw w hw0 hwR t).2) (t₀ := 0) ?_ ?_
    · show δ 0 = pos ν (((√ε : ℝ) : ℂ) * toReal.symm (x w 0)) 0
      rw [h0, DuffingMathieu.pos_vdp]
    · show δ' 0 = vel ν (((√ε : ℝ) : ℂ) * toReal.symm (x w 0)) 0
      rw [h0, DuffingMathieu.vel_vdp hν.ne']
  -- uniqueness near each locked state
  have hloc : ∀ w, limitAmp b d ν w = 0 → ‖w‖ ≤ R → ∀ δ δ' : ℝ → ℝ,
      (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t) →
      δ T = δ 0 → δ' T = δ' 0 →
      ‖vdp ν 0 (δ 0) (δ' 0) - ((√ε : ℝ) : ℂ) * w‖ ≤ √ε * r₀ → δ = δw w ∧ δ' = δw' w := by
    intro w hw0 hwR δ δ' hδ hδ' hTδ hTδ' h0
    have h0' : ‖vdp ν 0 (δ 0) (δ' 0)‖ ≤ √ε * (R + 1 / 2) := by
      have := norm_le_norm_add_norm_sub' (vdp ν 0 (δ 0) (δ' 0)) (((√ε : ℝ) : ℂ) * w)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at this
      nlinarith
    obtain ⟨z, hz, hzT, hz0v⟩ := hcore δ δ' hδ hδ' hTδ hTδ' h0'
    have hzw : ‖z 0 - toReal w‖ ≤ r₁ := by
      have e : vdp ν 0 (δ 0) (δ' 0) - ((√ε : ℝ) : ℂ) * w =
          ((√ε : ℝ) : ℂ) * toReal.symm (z 0 - toReal w) := by
        rw [map_sub, ContinuousLinearEquiv.symm_apply_apply, mul_sub, hz0v]
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_toReal_symm₅] at h0
      exact (le_of_mul_le_mul_left h0 hs0).trans (min_le_left _ _)
    have hzx := hun z hz hzT w hw0 hwR hzw
    exact hglob w hw0 hwR δ δ' hδ hδ' (by rw [← hzx]; exact hz0v)
  refine ⟨δw, δw', fun w hw0 hwR => ⟨fun t => (hsw w hw0 hwR t).1, fun t => (hsw w hw0 hwR t).2,
    fun t => ?_, fun t => ?_, fun t => ?_, hloc w hw0 hwR⟩, fun t => ?_, ?_⟩
  · have h1 : x w (t + 2 * Real.pi / ν) = x w t := (hx w hw0 hwR).2.1 t
    simp only [hδw, hδw', hT, h1, pos_period₅ hν, vel_period₅ hν, and_self]
  · show ‖vdp ν t (pos ν (((√ε : ℝ) : ℂ) * toReal.symm (x w t)) t)
      (vel ν (((√ε : ℝ) : ℂ) * toReal.symm (x w t)) t) - ((√ε : ℝ) : ℂ) * w‖ ≤ C * ε * √ε
    rw [vdp_pos_vel₅ hν.ne', ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have e : toReal.symm (x w t) - w = toReal.symm (x w t - toReal w) := by
      rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
    rw [e, norm_toReal_symm₅]
    calc √ε * ‖x w t - toReal w‖ ≤ √ε * (C * ε) :=
          mul_le_mul_of_nonneg_left ((hx w hw0 hwR).2.2 t) hs0.le
      _ = C * ε * √ε := by ring
  · -- the half-period shift of the orbit of `w*` is the orbit of `−w*`
    have hw0' : limitAmp b d ν (-w) = 0 := by
      have e : limitAmp b d ν (-w) = -limitAmp b d ν w := Saturation.ampField_neg _ _ _ _ _ w
      rw [e, hw0, neg_zero]
    have hwR' : ‖-w‖ ≤ R := by rw [norm_neg]; exact hwR
    set a := Real.pi / ν with ha
    have hδs : ∀ s, HasDerivAt (fun s => δw w (s + a)) (δw' w (s + a)) s := fun s =>
      ((hsw w hw0 hwR (s + a)).1).comp_add_const s a
    have hδs' : ∀ s, HasDerivAt (fun s => δw' w (s + a))
        ((frozen p (modKs p ε (2 * ν)) s).toSwing.accel (δw w (s + a)) (δw' w (s + a))) s :=
      fun s => by
        have h := ((hsw w hw0 hwR (s + a)).2).comp_add_const s a
        rw [ha, accel_half₅ hp hν] at h
        exact h
    have hper : ∀ s, δw w (s + 2 * Real.pi / ν) = δw w s ∧
        δw' w (s + 2 * Real.pi / ν) = δw' w s := fun s => by
      have h1 : x w (s + 2 * Real.pi / ν) = x w s := (hx w hw0 hwR).2.1 s
      simp only [hδw, hδw', h1, pos_period₅ hν, vel_period₅ hν, and_self]
    have hTs : δw w (T + a) = δw w (0 + a) := by
      rw [show T + a = a + 2 * Real.pi / ν by rw [hT]; ring, zero_add, (hper a).1]
    have hTs' : δw' w (T + a) = δw' w (0 + a) := by
      rw [show T + a = a + 2 * Real.pi / ν by rw [hT]; ring, zero_add, (hper a).2]
    have hstart : ‖vdp ν 0 (δw w (0 + a)) (δw' w (0 + a)) - ((√ε : ℝ) : ℂ) * -w‖ ≤ √ε * r₀ := by
      have e : vdp ν 0 (δw w (0 + a)) (δw' w (0 + a)) =
          -(((√ε : ℝ) : ℂ) * toReal.symm (x w a)) := by
        rw [zero_add, ← neg_neg (vdp ν 0 _ _), ← vdp_half₅ hν, zero_add]
        show -vdp ν a (pos ν (((√ε : ℝ) : ℂ) * toReal.symm (x w a)) a)
          (vel ν (((√ε : ℝ) : ℂ) * toReal.symm (x w a)) a) = _
        rw [vdp_pos_vel₅ hν.ne']
      rw [e, mul_neg, neg_sub_neg, norm_sub_rev, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs0.le]
      have e2 : toReal.symm (x w a) - w = toReal.symm (x w a - toReal w) := by
        rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
      rw [e2, norm_toReal_symm₅]
      exact mul_le_mul_of_nonneg_left (((hx w hw0 hwR).2.2 a).trans hCε) hs0.le
    obtain ⟨h1, h2⟩ := hloc (-w) hw0' hwR' (fun s => δw w (s + a)) (fun s => δw' w (s + a))
      hδs hδs' hTs hTs' hstart
    exact ⟨(congrFun h1 t).symm, (congrFun h2 t).symm⟩
  · -- the trivial zero carries the equilibrium
    have h0 : limitAmp b d ν 0 = 0 := Saturation.ampField_zero _ _ _ _ _
    have hzs : ∀ s, HasDerivAt (fun _ : ℝ => (0 : ℝ))
        ((frozen p (modKs p ε (2 * ν)) s).toSwing.accel ((fun _ : ℝ => (0 : ℝ)) s)
          ((fun _ : ℝ => (0 : ℝ)) s)) s := fun s => by
      rw [ParametricSaturation.accel_eq hp]
      simpa using hasDerivAt_const s (0 : ℝ)
    obtain ⟨h1, h2⟩ := hloc 0 h0 (by rw [norm_zero]; exact hR) (fun _ => 0) (fun _ => 0)
      (fun s => hasDerivAt_const s 0) hzs rfl rfl (by simp [vdp]; positivity)
    exact ⟨(congrFun h1 t).symm, (congrFun h2 t).symm⟩
  · -- the classification
    intro δ δ' hδ hδ' hTδ hTδ' h0
    obtain ⟨z, hz, hzT, hz0v⟩ := hcore δ δ' hδ hδ' hTδ hTδ'
      (h0.trans (mul_le_mul_of_nonneg_left (by linarith) hs0.le))
    have hz0R : ‖z 0‖ ≤ R := by
      have e : ‖vdp ν 0 (δ 0) (δ' 0)‖ = √ε * ‖z 0‖ := by
        rw [← hz0v, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_toReal_symm₅]
      rw [e] at h0
      exact le_of_mul_le_mul_left h0 hs0
    obtain ⟨w, hw0, hwR, hzx, -⟩ := hK z hz hzT hz0R
    exact ⟨w, hw0, hwR, hglob w hw0 hwR δ δ' hδ hδ' (by rw [← hzx]; exact hz0v)⟩

end powerlib.Synchronous.SubharmonicOrbit
