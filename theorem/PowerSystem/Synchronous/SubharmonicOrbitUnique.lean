import theorem.PowerSystem.Synchronous.SubharmonicOrbit

/-! # Uniqueness of the subharmonic swing orbit in its tube

`theorem/PowerSystem/Synchronous/SubharmonicOrbit.lean` turns every nondegenerate phase-locked
state `w*` of the averaged amplitude equation into a `2π/ν`-periodic solution of TR-110's swing
model, `δ_ε(t) = √ε Re(w* e^{jνt}) + O(ε^{3/2})` (`SubharmonicOrbit.subharmonic_orbit`), but drops
the uniqueness part of Bogoliubov's theorem (`Averaging.exists_periodic_orbit`). Here it is kept
and transferred to the swing model: the orbit is the only `2π/ν`-periodic solution of the swing
model whose phase-plane point stays in the tube of radius `√ε r₀` around `√ε w* e^{jνt}`.

Model boundary.
* The swing model of `SubharmonicOrbit`: one generator, TR-110's swing equation (3-8) with
  `P_e = K_s(t) sin δ + K_d Δω`, `K_s(t) = K_s(1 + ε cos 2νt)`, `P_m = 0`, `Params.Pos`, state
  `(δ, δ̇)`, continuous time, in the weakly nonlinear scaling `2ξω_n = εb`, `ω_n² = ν² − εd`.
* The tube is measured in the phase-plane norm `‖vdp ν t δ δ̇ − √ε w*‖ =
  |δ − jδ̇/ν − √ε w* e^{jνt}|` of the van der Pol amplitude, for all `t`; the radius `√ε r₀`
  (`r₀ > 0` depending on `b, d, ν, w*` only) is of the order of the amplitude. Uniqueness among
  all periodic solutions of other periods or outside the tube is not claimed.
* Excluded as in `SubharmonicOrbit`: a loaded operating point (its uniqueness is
  `LoadedSubharmonicOrbitUnique.loaded_orbit_unique`), AVR/PSS, network and multi-machine
  dynamics, a modulation of `K_d`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11);
Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations* (the second
theorem of Bogoliubov, uniqueness of the periodic solution near a hyperbolic equilibrium of the
averaged system, `Averaging.exists_periodic_orbit`); the scaled swing model
`SubharmonicOrbit.hasDerivAt_scaled_limit`, `SubharmonicOrbit.swing_orbit_of_real`.

Results.
* `scaled_orbit_unique` — the periodic solution of the cut-off scaled model of
  `SubharmonicOrbit.scaled_orbit` is the only solution with `x(2π/ν) = x(0)` within `r₀` of
  `toReal w*` at `t = 0`.
* `subharmonic_orbit_unique` — **the subharmonic swing orbit is unique in its tube**: the
  `2π/ν`-periodic swing solution `(δ_ε, δ̇_ε)` with `|δ_ε − √ε Re(w* e^{jνt})| ≤ C ε √ε` stays in
  the tube of radius `√ε r₀`, and every `2π/ν`-periodic swing solution that stays in this tube is
  `(δ_ε, δ̇_ε)`.
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

@[tmio T, powerlib_foundation] private theorem toEuclideanCLM_inv_apply'
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

/-- **The periodic solution of the cut-off scaled model is unique near the locked state** (the
uniqueness part of Bogoliubov's second theorem `Averaging.exists_periodic_orbit`, kept in
`SubharmonicOrbit.scaled_orbit`'s construction). -/
@[tmio M, powerlib_domain] theorem scaled_orbit_unique {b d ν : ℝ} (hν : 0 < ν) {wstar : ℂ}
    (hw0 : limitAmp b d ν wstar = 0) (hdet : (limitJac b d ν wstar).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ C * ε₀ ≤ 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 / 2 ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ ωn : ℝ, ωn ^ 2 = ν ^ 2 - ε * d →
      ∃ x : ℝ → ℝ², (∀ t, HasDerivAt x (ε • realField (limitCut b d ν (‖wstar‖ + 3)) (x t) t +
          ε ^ 2 • realField (rCut ωn ν d ε (‖wstar‖ + 3)) (x t) t) t) ∧
        (∀ t, x (t + 2 * Real.pi / ν) = x t) ∧ (∀ t, ‖x t - toReal wstar‖ ≤ C * ε) ∧
        ∀ z : ℝ → ℝ², (∀ t, HasDerivAt z (ε • realField (limitCut b d ν (‖wstar‖ + 3)) (z t) t +
          ε ^ 2 • realField (rCut ωn ν d ε (‖wstar‖ + 3)) (z t) t) t) →
          z (2 * Real.pi / ν) = z 0 → ‖z 0 - toReal wstar‖ ≤ r₀ → z = x := by
  set ρc := ‖wstar‖ + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  set ℓ := DuffingMathieu.lipConst b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  set K := ν ^ 2 + |d| with hK
  set ℓr := rLip ν d K (2 * ρc) with hℓr
  set Mr := rBound ν d K (2 * ρc) with hMr
  set L₂ := ν * (‖wstar‖ + 1) with hL₂
  set J := limitJac b d ν wstar with hJ
  set B := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ with hB
  set r₀ := min (1 / 2) (1 / (4 * ‖B‖ * L₂ + 1)) with hr₀
  have hf := realField_hyp (DuffingMathieu.cutField_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2)
    (γ := -(ν ^ 2) / 6) hν hρc0)
  have hℓ0 : 0 ≤ ℓ := hf.2.1
  have hM0 : 0 ≤ M := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hℓr0 : 0 ≤ ℓr := by rw [hℓr, rLip]; positivity
  have hMr0 : 0 ≤ Mr := by rw [hMr, rBound]; positivity
  have hL₂0 : 0 ≤ L₂ := by positivity
  set CS := Averaging.stroboConst ℓ M Mr T with hCS
  set LS := Averaging.stroboLip ℓ ℓr L₂ M Mr T with hLS
  have hCS0 : 0 ≤ CS := by rw [hCS, Averaging.stroboConst]; positivity
  have hLS0 : 0 ≤ LS := by rw [hLS, Averaging.stroboLip]; positivity
  set C := 2 * ‖B‖ * CS / T + (M + Mr) * T with hC
  have hC0 : 0 ≤ C := by positivity
  set ε₀ := min (min 1 (1 / (2 * (M + Mr) * T + 1)))
    (min (T / (4 * ‖B‖ * LS + 1)) (min (r₀ * T / (2 * ‖B‖ * CS + 1)) (1 / (C + 1)))) with hε₀
  have hr₀0 : 0 < r₀ := lt_min (by norm_num) (by positivity)
  have hε₀0 : 0 < ε₀ := by positivity
  have hr₀h : r₀ ≤ 1 / 2 := min_le_left _ _
  refine ⟨ε₀, C, r₀, hε₀0, hC0, ?_, hr₀0, hr₀h, ?_⟩
  · have h1 : ε₀ ≤ 1 / (C + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))
    calc C * ε₀ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  intro ε hε hεε₀ ωn hωn
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hKω : ωn ^ 2 ≤ K := by
    rw [hωn, hK]
    have : -(ε * d) ≤ |d| := by
      have h1 : |ε * d| ≤ |d| := by
        rw [abs_mul, abs_of_pos hε]; exact mul_le_of_le_one_left (abs_nonneg _) hε1
      linarith [neg_abs_le (ε * d)]
    linarith
  have hr := realField_hyp (rCut_hyp (d := d) hν hε hε1 hKω hρc0)
  obtain ⟨h0, hA⟩ := averaged_limitCut_at (b := b) (d := d) (ρc := ρc) hν hw0 (by linarith)
  have hAB := fun v => (toEuclideanCLM_inv_apply' hdet v).1
  have hBA := fun v => (toEuclideanCLM_inv_apply' hdet v).2
  have hball : ∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖x‖ ≤ ‖wstar‖ + 1 := by
    intro x hx
    have := norm_le_norm_add_norm_sub' x (toReal wstar)
    rw [Saturation.norm_toReal] at this
    linarith
  have hD : ∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ∀ t,
      HasFDerivAt (fun y => realField (limitCut b d ν ρc) y t) (limitDeriv b d ν x t) x :=
    fun x hx t => hasFDerivAt_limitCut (by linarith [hball x hx]) t
  have hDl : ∀ x y : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖y - toReal wstar‖ ≤ 1 → ∀ t,
      ‖limitDeriv b d ν x t - limitDeriv b d ν y t‖ ≤ L₂ * ‖x - y‖ :=
    fun x y hx hy t => norm_limitDeriv_sub_le hν (hball x hx) (hball y hy) t
  have hερ : 2 * ε * (M + Mr) * T ≤ 1 := by
    have h1 : ε ≤ 1 / (2 * (M + Mr) * T + 1) := hεε₀.trans ((min_le_left _ _).trans
      (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : ε * (2 * (M + Mr) * T + 1) = 2 * ε * (M + Mr) * T + ε := by ring
    linarith
  have hεL : 4 * ε * ‖B‖ * LS ≤ T := by
    have h1 : ε ≤ T / (4 * ‖B‖ * LS + 1) := hεε₀.trans ((min_le_right _ _).trans
      (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : ε * (4 * ‖B‖ * LS + 1) = 4 * ε * ‖B‖ * LS + ε := by ring
    linarith
  have hεC : 2 * ε * ‖B‖ * CS ≤ r₀ * T := by
    have h1 : ε ≤ r₀ * T / (2 * ‖B‖ * CS + 1) := hεε₀.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : ε * (2 * ‖B‖ * CS + 1) = 2 * ε * ‖B‖ * CS + ε := by ring
    linarith
  have hr₀L : 4 * ‖B‖ * L₂ * r₀ ≤ 1 := by
    have h1 : r₀ ≤ 1 / (4 * ‖B‖ * L₂ + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have e : r₀ * (4 * ‖B‖ * L₂ + 1) = 4 * ‖B‖ * L₂ * r₀ + r₀ := by ring
    linarith
  have hr₀ρ : 2 * r₀ ≤ 1 := by
    have := min_le_left (1 / 2 : ℝ) (1 / (4 * ‖B‖ * L₂ + 1))
    linarith
  obtain ⟨x, hx, hper, hbd, huniq⟩ := Averaging.exists_periodic_orbit hf hr one_pos hL₂0 hD hDl
    (continuous_limitDeriv b d ν _) h0 hA hAB hBA hr₀0 hr₀ρ hr₀L hε hε1 hερ hεL hεC
  exact ⟨x, hx, hper, fun t => (hbd t).trans (le_of_eq (by rw [hC]; ring)), huniq⟩

@[tmio M, powerlib_foundation] private theorem vdp_pos_vel' {ν : ℝ} (hν : ν ≠ 0) (z : ℂ) (t : ℝ) :
    vdp ν t (pos ν z t) (vel ν z t) = z := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have h1 : (((pos ν z t : ℝ) : ℂ) - (((vel ν z t) / ν : ℝ) : ℂ) * I) =
      z * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [pos]
    · simp [vel]; field_simp
  rw [vdp, h1, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

@[tmio M, powerlib_foundation] private theorem vdp_sub' (ν t x x' y y' : ℝ) :
    vdp ν t (x - y) (x' - y') = vdp ν t x x' - vdp ν t y y' := by
  simp only [vdp]; push_cast; ring


variable {p : Params}

@[tmio T, powerlib_foundation] private theorem norm_toReal_symm' (x : ℝ²) :
    ‖toReal.symm x‖ = ‖x‖ := by
  have h := Saturation.norm_toReal (toReal.symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

@[tmio T, powerlib_foundation] private theorem exp_period' {ν : ℝ} (hν : 0 < ν) :
    Complex.exp (-(((ν * (2 * Real.pi / ν) : ℝ) : ℂ) * I)) = 1 := by
  rw [show ν * (2 * Real.pi / ν) = 2 * Real.pi by field_simp]
  rw [show -(((2 * Real.pi : ℝ) : ℂ) * I) = -(2 * Real.pi * I) by push_cast; ring,
    Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- **The subharmonic swing orbit is unique in its tube.** Let `w*` be a nondegenerate
phase-locked state of the averaged limit amplitude equation (`limitAmp b d ν w* = 0`,
`det (limitJac b d ν w*) ≠ 0`). There are `ε₀ > 0`, `C ≥ 0` and `r₀ > 0` (depending on
`b, d, ν, w*` only) such that for every `0 < ε ≤ ε₀` and every machine of the scaling
`2ξω_n = εb`, `ω_n² = ν² − εd`, the swing model has a `2π/ν`-periodic solution `(δ_ε, δ̇_ε)` with
`|δ_ε(t) − √ε Re(w* e^{jνt})| ≤ C ε √ε`, whose phase-plane point stays within `√ε r₀` of
`√ε w* e^{jνt}`, and every `2π/ν`-periodic solution `(δ, δ̇)` of the swing model with
`‖vdp ν t δ(t) δ̇(t) − √ε w*‖ ≤ √ε r₀` for all `t` equals `(δ_ε, δ̇_ε)` (the uniqueness of
`Averaging.exists_periodic_orbit` for the scaled model, `hasDerivAt_scaled_limit`). -/
@[tmio M, powerlib_domain] theorem subharmonic_orbit_unique {b d ν : ℝ} (hν : 0 < ν)
    {wstar : ℂ} (hw0 : limitAmp b d ν wstar = 0) (hdet : (limitJac b d ν wstar).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      2 * p.dampingRatio * natFreq p = ε * b → natFreq p ^ 2 = ν ^ 2 - ε * d →
      ∃ δε δε' : ℝ → ℝ, (∀ t, HasDerivAt δε (δε' t) t) ∧
        (∀ t, HasDerivAt δε' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δε t) (δε' t)) t) ∧
        (∀ t, δε (t + 2 * Real.pi / ν) = δε t ∧ δε' (t + 2 * Real.pi / ν) = δε' t) ∧
        (∀ t, |δε t - √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε * √ε) ∧
        (∀ t, ‖vdp ν t (δε t) (δε' t) - ((√ε : ℝ) : ℂ) * wstar‖ ≤ √ε * r₀) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t) →
          (∀ t, δ (t + 2 * Real.pi / ν) = δ t ∧ δ' (t + 2 * Real.pi / ν) = δ' t) →
          (∀ t, ‖vdp ν t (δ t) (δ' t) - ((√ε : ℝ) : ℂ) * wstar‖ ≤ √ε * r₀) →
          δ = δε ∧ δ' = δε' := by
  obtain ⟨ε₁, C, r₀, hε₁, hC, hCε₁, hr₀, hr₀h, horb⟩ := scaled_orbit_unique hν hw0 hdet
  refine ⟨min ε₁ (r₀ / (C + 1)), C, r₀, lt_min hε₁ (by positivity), hC, hr₀, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hCr : C * ε ≤ r₀ := by
    have h1 : ε ≤ r₀ / (C + 1) := hεε₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  set ρc := ‖wstar‖ + 3 with hρc
  set T := 2 * Real.pi / ν with hT
  obtain ⟨x, hx, hper, hbd, huniq⟩ := horb ε hε hεε₁ (natFreq p) hd
  have hCε : C * ε ≤ 1 := (mul_le_mul_of_nonneg_left hεε₁ hC).trans hCε₁
  obtain ⟨h1, h2, h3, h4⟩ := swing_orbit_of_real hp hν hε hb hd hx hper hbd hCε
  -- the phase-plane point of the orbit
  have hvdpε : ∀ t, vdp ν t (pos ν (((√ε : ℝ) : ℂ) * toReal.symm (x t)) t)
      (vel ν (((√ε : ℝ) : ℂ) * toReal.symm (x t)) t) = ((√ε : ℝ) : ℂ) * toReal.symm (x t) :=
    fun t => vdp_pos_vel' hν.ne' _ t
  refine ⟨_, _, h1, h2, h3, h4, fun t => ?_, ?_⟩
  · rw [hvdpε, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have e : toReal.symm (x t) - wstar = toReal.symm (x t - toReal wstar) := by
      simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply]
    rw [e, norm_toReal_symm']
    exact mul_le_mul_of_nonneg_left ((hbd t).trans hCr) hs0.le
  intro δ δ' hδ hδ' hδper htube
  -- the scaled amplitude of `(δ, δ̇)` solves the cut-off scaled model
  set z : ℝ → ℝ² := fun t => toReal (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t) (δ' t)) with hz
  have hzw : ∀ t, ‖toReal.symm (z t) - wstar‖ ≤ r₀ := fun t => by
    simp only [hz, ContinuousLinearEquiv.symm_apply_apply]
    have h5 := htube t
    have e : vdp ν t (δ t) (δ' t) - ((√ε : ℝ) : ℂ) * wstar =
        ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t) (δ' t) - wstar) := by
      field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h5
    exact le_of_mul_le_mul_left h5 hs0
  have hzin : ∀ t, ‖toReal.symm (z t)‖ ≤ ρc := fun t => by
    have := norm_le_norm_add_norm_sub' (toReal.symm (z t)) wstar
    have := hzw t
    rw [hρc]; linarith
  have hzsol : ∀ t, HasDerivAt z (ε • realField (limitCut b d ν ρc) (z t) t +
      ε ^ 2 • realField (rCut (natFreq p) ν d ε ρc) (z t) t) t := by
    intro t
    have h5 := hasDerivAt_scaled_limit hp hν hε hb hd hδ hδ' t
    have h6 := (toReal : ℂ →L[ℝ] ℝ²).hasFDerivAt.comp_hasDerivAt t h5
    refine h6.congr_deriv ?_
    have hcl := DuffingMathieu.clampC_of_norm_le (hzin t)
    simp only [hz, ContinuousLinearEquiv.symm_apply_apply] at hcl
    simp only [ContinuousLinearEquiv.coe_coe, map_add, map_smul, hz, realField,
      ContinuousLinearEquiv.symm_apply_apply, limitCut, rCut, DuffingMathieu.cutField, hcl]
  have hzT : z T = z 0 := by
    have e1 : δ T = δ 0 := by have := (hδper 0).1; rwa [zero_add] at this
    have e2 : δ' T = δ' 0 := by have := (hδper 0).2; rwa [zero_add] at this
    have hE : Complex.exp (-(((ν * T : ℝ) : ℂ) * I)) = 1 := exp_period' hν
    simp only [hz, e1, e2, vdp, hE, mul_zero, Complex.ofReal_zero, zero_mul, neg_zero,
      Complex.exp_zero]
  have hz0 : ‖z 0 - toReal wstar‖ ≤ r₀ := by
    rw [← norm_toReal_symm', map_sub]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    simpa [hz] using hzw 0
  have hzx : z = x := huniq z hzsol hzT hz0
  -- back to the swing model
  have hδeq : ∀ t, ((√ε : ℝ) : ℂ) * toReal.symm (x t) = vdp ν t (δ t) (δ' t) := fun t => by
    rw [← hzx]
    simp only [hz, ContinuousLinearEquiv.symm_apply_apply]
    field_simp
  constructor
  · funext t
    show δ t = pos ν (((√ε : ℝ) : ℂ) * toReal.symm (x t)) t
    rw [hδeq, DuffingMathieu.pos_vdp]
  · funext t
    show δ' t = vel ν (((√ε : ℝ) : ℂ) * toReal.symm (x t)) t
    rw [hδeq, DuffingMathieu.vel_vdp hν.ne']

end powerlib.Synchronous.SubharmonicOrbit
