import theorem.PowerSystem.Synchronous.LoadedSubharmonicOrbit

/-! # Uniqueness of the loaded subharmonic orbit; the amplitude equation with a small input

`theorem/PowerSystem/Synchronous/LoadedSubharmonicOrbit.lean` turns every nondegenerate locked
state `w*` of the averaged second-order amplitude equation of the loaded swing into a
`2π/ν`-periodic solution of the loaded swing model (`loaded_subharmonic_orbit`), but drops the
uniqueness clause of `Averaging.exists_periodic_point_perturbed`. Here its construction is rerun,
uniqueness clause included, for the scaled amplitude equation of the pumped oscillator with
quadratic and cubic stiffness and an arbitrary small input,
`ẇ = ε vdpField(w) + √ε quadField(w) + U(w, t)/√ε` (`inputField`): pump `k₁`, quadratic
stiffness `α₂` and cubic stiffness `α₃` within `O(ε)` of limit values `k₁⁰, α₂⁰, α₃⁰`, and an
input `U` of order `ε²` with an `ε²`-Lipschitz constant. For a nondegenerate locked state `w*` of
the averaged limit field `secondAmp b d k₁⁰ α₂⁰ α₃⁰ ν` this gives the periodic orbit and its
uniqueness near `w*` (`input_orbit`), its exponential attraction when the averaged Jacobian
`secondJac` is Hurwitz (`input_orbit_stable`) and its instability when the Jacobian has a root
with positive real part (`input_orbit_unstable`). The loaded swing is the instance `k₁ = ω_L²`,
`U = inputW` (`loadedAmp_eq_secondAmp`, `loaded_coeff_bounds`, `inputW_bounds`): its subharmonic
orbit is the only solution of the loaded swing model that starts within `√ε r₀` of `√ε w*` in the
phase plane and returns to its initial state after one period (`loaded_orbit_unique`). The
constant-power swing of `LoadedSwingConstantPower` is a second instance
(`theorem/PowerSystem/Synchronous/ConstantPowerSubharmonicOrbit.lean`).

Model boundary.
* Generic part (`inputField` to `input_orbit_unstable`, no model family): the scaled van der Pol
  amplitude `w = vdp(x, ẋ)/√ε` of `ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = g(t, x)`
  (`hasDerivAt_inputAmp`, `oscillator_of_inputField`, input `vdpInput g`), continuous time,
  `ν > 0`, `0 < ε ≤ ε₀`; the input `U` is arbitrary, continuous and `2π/ν`-periodic, with
  `‖U‖ ≤ ε²μ` and an `ε²l_u` Lipschitz constant on the disc `‖w‖ ≤ 2(‖w*‖ + 3)`. Orbit,
  uniqueness, attraction and escape are stated for the equation read through the clamp
  `clampC (‖w*‖ + 3)` (`inputClamp`); the solutions concerned stay in the disc where the clamp is
  the identity. All constants depend on `b, d, ν, k₁⁰, α₂⁰, α₃⁰, w*` and on the bounds only.
* Loaded instance: the loaded swing model of `LoadedSubharmonicOrbit` — one generator, TR-110's
  swing equation (3-8) at a loaded operating point `δ₀` with `cos δ₀ > 0`, mechanical power
  `K_s(t) sin δ₀`, power-angle curve `K_s(t) sin δ`, `K_s(t) = K_s(1 + ε cos 2νt)`, `Params.Pos`,
  state `(δ, δ̇)`, continuous time — in the weakly nonlinear scaling `D/M = εb`,
  `ω_L² = ν² − εd`. Uniqueness is claimed among the solutions that start in the phase-plane ball
  `‖vdp ν 0 (δ(0) − δ₀) δ̇(0) − √ε w*‖ ≤ √ε r₀` and return after one period; the
  `2π/ν`-periodic solutions starting in a disc of radius `√ε R` are classified in
  `theorem/PowerSystem/Synchronous/LoadedSubharmonicClassification.lean`
  (`LoadedSubharmonicOrbit.loaded_classification`, generic
  `LoadedSubharmonicOrbit.input_classification`). Excluded as in `LoadedSubharmonicOrbit`: a
  constant mechanical power (`ConstantPowerSubharmonicOrbit`), AVR/PSS, network and multi-machine
  dynamics, a modulation of `K_d`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11);
Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations* (the second
theorem of Bogoliubov: the periodic solution near a hyperbolic equilibrium of the averaged system
is unique, and its stability is that of the equilibrium); Sanders–Verhulst–Murdock, *Averaging
Methods in Nonlinear Dynamical Systems*, Ch. 2.9 (second-order averaging, near-identity
transformations); the loaded construction `LoadedSubharmonicOrbit.transRem_bounds`,
`LoadedSubharmonicOrbit.Wmap_bilipschitz`, `LoadedSubharmonicOrbit.exists_Wmap_eq`,
`LoadedSubharmonicOrbit.swing_of_clamped`, `LoadedSubharmonicOrbit.loaded_swing_of_orbit`,
`LoadedSubharmonicOrbit.loaded_unique_Icc`; `Averaging.exists_periodic_point_perturbed`,
`Averaging.exp_stable_perturbed`, `Averaging.unstable_perturbed`; the Lyapunov equation
(LeanForControl `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov`) and Chetaev's
certificate (`LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos`).

Sharpenings.
* `loaded_subharmonic_orbit` gives existence only. Here the loaded orbit is the unique fixed point
  of the period map in a ball of radius `√ε r₀` around `√ε w*`: every solution starting there and
  returning after one period is the orbit — not only every periodic solution that stays in a tube
  for all time (the form of `SubharmonicOrbitUnique.subharmonic_orbit_unique`).
* The private core estimates of `LoadedSubharmonicOrbit` (`loaded_core`, `loaded_orbit_core`) are
  not reusable; their content is re-derived here once for an arbitrary input (`input_core`,
  `input_orbit`), and the loaded swing is one instance of it.

Results.
* `inputField`, `vdpInput`, `inputClamp`, `transIn` — the amplitude equation with an input, an
  input read off the position, the clamped equation, the transformed right-hand side.
* `hasDerivAt_inputAmp`, `oscillator_of_inputField` — the oscillator with an input `g(t, x)` and
  its scaled amplitude equation, both directions.
* `norm_inputField_le`, `norm_inputField_sub_le`, `continuous_inputClamp`,
  `inputClamp_lipschitz`, `norm_inputClamp_le`, `exists_inputClamp_solution`, `inputClamp_unique`,
  `inputClamp_periodic`, `hasDerivAt_Wmap_input` — bounds, global solutions, uniqueness,
  periodicity, the transformed equation along clamped solutions.
* `secondAmp`, `secondJac`, `secondDerivR`, `second_hyp` — the averaged limit field, its Jacobian,
  and the hypotheses of the periodic-orbit theorem at a locked state.
* `input_core`, `input_orbit` — **the periodic orbit of the amplitude equation with an input**,
  `‖w − w*‖ ≤ √ε C`, unique among the clamped solutions that start within `r₀` of `w*` and return
  after one period.
* `input_orbit_stable`, `input_orbit_unstable` — attraction at the rate `βε` for a Hurwitz
  averaged Jacobian; escape for a root with positive real part.
* `loadedAmp_eq_secondAmp`, `loaded_coeff_bounds`, `inputW_bounds`, `continuous_inputW`,
  `inputW_periodic` — the loaded swing in the hypotheses of the generic theorems.
* `loaded_orbit_unique` — **the loaded subharmonic orbit is unique**: the `2π/ν`-periodic solution
  with `|δ_ε − δ₀ − √ε Re(w* e^{jνt})| ≤ Cε` is the only solution that starts within `√ε r₀` of
  `√ε w*` in the phase plane and returns after one period.
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

@[tmio T, powerlib_foundation] private theorem pos_ofReal_mul₃ (ν s : ℝ) (w : ℂ) (t : ℝ) :
    pos ν ((s : ℂ) * w) t = s * pos ν w t := by
  simp only [pos, mul_assoc, Complex.re_ofReal_mul]

@[tmio T, powerlib_foundation] private theorem norm_phase_inv₃ (ν t : ℝ) :
    ‖(phase ν t)⁻¹‖ = 1 := by
  rw [norm_inv, show ‖phase ν t‖ = 1 from Complex.norm_exp_ofReal_mul_I _, inv_one]

@[tmio T, powerlib_foundation] private theorem phase_period₃ {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    phase ν (t + 2 * Real.pi / ν) = phase ν t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  rw [phase, phase, show ((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I =
    ((ν * t : ℝ) : ℂ) * I + 2 * Real.pi * I by push_cast; field_simp, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem pos_period₃ {ν : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : pos ν w (t + 2 * Real.pi / ν) = pos ν w t := by
  have := phase_period₃ hν t
  simp only [phase] at this
  simp only [pos, this]

@[tmio T, powerlib_foundation] private theorem norm_toReal_symm₃ (x : ℝ²) :
    ‖toReal.symm x‖ = ‖x‖ := by
  have h := Saturation.norm_toReal (toReal.symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

@[tmio T, powerlib_foundation] private theorem half_bound₃ {x : ℝ} (hx : 0 ≤ x) :
    1 / (2 * (x + 1)) * x ≤ 1 / 2 := by
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

@[tmio T, powerlib_foundation] private theorem toEuclideanCLM_inv_apply₃
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

@[tmio T, powerlib_foundation] private theorem nearIdDeriv_real_smul₃ (α₂ ν : ℝ) (z : ℂ)
    (t c : ℝ) (h : ℂ) : nearIdDeriv α₂ ν z t (c • h) = c • nearIdDeriv α₂ ν z t h := by
  simp only [nearIdDeriv, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring

@[tmio M, powerlib_foundation] private theorem oscillator_of_vdp₃ {b k₀ k₁ γ ν : ℝ}
    (hν : ν ≠ 0) {z : ℝ → ℂ} {u : ℝ → ℝ} (t : ℝ)
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

/-! ## The scaled amplitude equation with an input -/

/-- **The scaled amplitude field of the pumped oscillator with quadratic and cubic stiffness and
an input** `U` in van der Pol form: `ε vdpField(w) + √ε quadField(w) + U/√ε` (damping `b`,
stiffness `ν² − d`, pump `k₁`, cubic stiffness `α₃`, quadratic stiffness `α₂`). The loaded
swing's field `scaledField` is the instance with `k₁ = ω_L²` and `U = inputW`. -/
def inputField (b d k₁ α₂ α₃ ν ε : ℝ) (U : ℂ → ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  ε • vdpField b (ν ^ 2 - d) k₁ α₃ ν w t + √ε • quadField α₂ ν w t + (√ε)⁻¹ • U w t

/-- An input `g(t, x)` of the oscillator read off the scaled amplitude `w` in van der Pol form:
`−(j/ν) g(t, √ε Re(w e^{jνt})) e^{−jνt}` (`inputW` is the instance of the loaded remainder). -/
def vdpInput (ν ε : ℝ) (g : ℝ → ℝ → ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  -(I / ν * (g t (√ε * pos ν w t) : ℂ) * (phase ν t)⁻¹)

/-- The input field read through the clamp `clampC ρc` (`clampField` is the loaded instance). -/
def inputClamp (b d k₁ α₂ α₃ ν ε ρc : ℝ) (U : ℂ → ℝ → ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  inputField b d k₁ α₂ α₃ ν ε U (clampC ρc w) t

/-- The right-hand side of the transformed amplitude equation with an input (`transField` is
the loaded instance). -/
def transIn (b d k₁ α₂ α₃ ν ε : ℝ) (U : ℂ → ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  ε • secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν w t -
    (ε * √ε) • nearIdDeriv α₂ ν w t (vdpField b (ν ^ 2 - d) k₁ α₃ ν w t) +
    ((√ε)⁻¹ • U w t - nearIdDeriv α₂ ν w t (U w t))

variable {b d k₁ α₂ α₃ ν ε : ℝ}

/-- The input field written at the unscaled amplitude `z = √ε w`. -/
@[tmio T, powerlib_foundation] private theorem inputField_eq (hε : 0 < ε) (g : ℝ → ℝ → ℝ)
    (w : ℂ) (t : ℝ) :
    ((√ε : ℝ) : ℂ) * inputField b d k₁ α₂ α₃ ν ε (vdpInput ν ε g) w t =
      vdpField (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν (((√ε : ℝ) : ℂ) * w) t -
        I / ν * ((-α₂ * pos ν (((√ε : ℝ) : ℂ) * w) t ^ 2 +
          g t (pos ν (((√ε : ℝ) : ℂ) * w) t) : ℝ) : ℂ) *
          Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  rw [DuffingMathieu.vdpField_scaled hε.le b d k₁ α₃ ν w t]
  have hinv : ((√ε : ℝ) : ℂ) * ((√ε : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs0'
  simp only [inputField, vdpInput, quadField, pos_ofReal_mul₃, Complex.real_smul, phase]
  rw [← Complex.exp_neg]
  push_cast
  generalize ((g t (√ε * pos ν w t) : ℝ) : ℂ) = R
  linear_combination (-(I / (ν : ℂ) * R * Complex.exp (-((ν : ℂ) * (t : ℂ) * I)))) * hinv

/-- **The scaled amplitude of the oscillator with an input** `g(t, x)`: if
`ẍ = −(εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₃x³) − α₂x² + g(t, x)`, then `w = vdp(x, ẋ)/√ε` solves
`ẇ = inputField(w, t)` with the input `vdpInput g` (`DuffingMathieu.hasDerivAt_vdp`). -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_inputAmp (hν : 0 < ν) (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} {x x' : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) -
      α₂ * x t ^ 2 + g t (x t)) t) (t : ℝ) :
    HasDerivAt (fun t => ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t))
      (inputField b d k₁ α₂ α₃ ν ε (vdpInput ν ε g)
        (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hx'' : ∀ t, HasDerivAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) +
      (-α₂ * x t ^ 2 + g t (x t))) t := fun t => by
    convert hx' t using 1; ring
  have hz := DuffingMathieu.hasDerivAt_vdp hν.ne' hx hx'' t
  have hw := hz.const_mul ((√ε : ℝ) : ℂ)⁻¹
  convert hw using 1
  have hzw : vdp ν t (x t) (x' t) =
      ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) := by field_simp
  have e := inputField_eq (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) (ν := ν) hε g
    (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t
  rw [← hzw, DuffingMathieu.pos_vdp] at e
  rw [← e]
  field_simp

/-- **A solution of the amplitude equation with an input carries a solution of the
oscillator** (the converse of `hasDerivAt_inputAmp`): at a time where `ẇ = inputField(w, t)`,
`x = Re(√ε w e^{jνt})`, `ẋ = vel ν (√ε w) t` satisfy the oscillator equations. -/
@[tmio T, powerlib_foundation] theorem oscillator_of_inputField (hν : 0 < ν) (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} {w : ℝ → ℂ} {t : ℝ}
    (hw : HasDerivAt w (inputField b d k₁ α₂ α₃ ν ε (vdpInput ν ε g) (w t) t) t) :
    HasDerivAt (fun s => pos ν (((√ε : ℝ) : ℂ) * w s) s) (vel ν (((√ε : ℝ) : ℂ) * w t) t) t ∧
      HasDerivAt (fun s => vel ν (((√ε : ℝ) : ℂ) * w s) s)
        (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (pos ν (((√ε : ℝ) : ℂ) * w t) t)
            (vel ν (((√ε : ℝ) : ℂ) * w t) t) - α₂ * pos ν (((√ε : ℝ) : ℂ) * w t) t ^ 2 +
          g t (pos ν (((√ε : ℝ) : ℂ) * w t) t)) t := by
  have hz := hw.const_mul ((√ε : ℝ) : ℂ)
  rw [inputField_eq hε] at hz
  have hosc := oscillator_of_vdp₃ hν.ne' (z := fun s => ((√ε : ℝ) : ℂ) * w s)
    (u := fun s => -α₂ * pos ν (((√ε : ℝ) : ℂ) * w s) s ^ 2 +
      g s (pos ν (((√ε : ℝ) : ℂ) * w s) s)) t hz
  refine ⟨hosc.1, ?_⟩
  convert hosc.2 using 1
  ring

/-- **The input field is slow on discs**: with `|α₂| ≤ A₂`, `|α₃| ≤ A₃`, `|k₁| ≤ K₀` and
`‖U‖ ≤ ε²μ` on `‖w‖ ≤ r`, `‖inputField(z)‖ ≤ √ε ((|d| + K₀ + ν|b| + 3A₃r²)r/ν + A₂r²/ν + μ)`. -/
@[tmio T, powerlib_foundation] theorem norm_inputField_le (hν : 0 < ν) {r A2 A3 K0 mu : ℝ}
    {U : ℂ → ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 ≤ r) (hA2 : |α₂| ≤ A2)
    (hA3 : |α₃| ≤ A3) (hK0 : |k₁| ≤ K0) (hmu : 0 ≤ mu)
    (hU : ∀ w t, ‖w‖ ≤ r → ‖U w t‖ ≤ ε ^ 2 * mu) {z : ℂ} (hz : ‖z‖ ≤ r) (t : ℝ) :
    ‖inputField b d k₁ α₂ α₃ ν ε U z t‖ ≤
      √ε * ((|d| + K0 + ν * |b| + 3 * A3 * r ^ 2) / ν * r + A2 / ν * r ^ 2 + mu) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hεs : ε ≤ √ε := by nlinarith
  have hℓ : (|ν ^ 2 - (ν ^ 2 - d)| + |k₁| + ν * |b| + 3 * |α₃| * r ^ 2) / ν ≤
      (|d| + K0 + ν * |b| + 3 * A3 * r ^ 2) / ν := by
    rw [show ν ^ 2 - (ν ^ 2 - d) = d by ring]
    gcongr
  set ℓ₁ := (|d| + K0 + ν * |b| + 3 * A3 * r ^ 2) / ν with hℓ₁
  have hA30 : 0 ≤ A3 := (abs_nonneg _).trans hA3
  have hK00 : 0 ≤ K0 := (abs_nonneg _).trans hK0
  have hA20 : 0 ≤ A2 := (abs_nonneg _).trans hA2
  have hℓ₁0 : 0 ≤ ℓ₁ := by positivity
  have hV := DuffingMathieu.norm_vdpField_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁)
    (γ := α₃) hν hz (by rw [norm_zero]; exact hr) t
  rw [DuffingMathieu.vdpField_zero, sub_zero, sub_zero] at hV
  have hQ := norm_quadField_le (α₂ := α₂) hν z t
  have hUz := hU z t hz
  rw [inputField]
  calc _ ≤ ε * (ℓ₁ * r) + √ε * (A2 / ν * r ^ 2) + (√ε)⁻¹ * (ε ^ 2 * mu) := by
        refine (norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [norm_smul, Real.norm_of_nonneg hε.le]
          exact mul_le_mul_of_nonneg_left (hV.trans (mul_le_mul hℓ hz (norm_nonneg _) hℓ₁0)) hε.le
        · rw [norm_smul, Real.norm_of_nonneg hs0.le]
          refine mul_le_mul_of_nonneg_left (hQ.trans ?_) hs0.le
          gcongr
        · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
          exact mul_le_mul_of_nonneg_left hUz (inv_nonneg.mpr hs0.le)
    _ = ε * (ℓ₁ * r) + √ε * (A2 / ν * r ^ 2) + ε * √ε * mu := by
        congr 1
        have h2 : ε ^ 2 = ε * √ε * √ε := by rw [mul_assoc, hss, sq]
        rw [h2]; field_simp
    _ ≤ √ε * (ℓ₁ * r) + √ε * (A2 / ν * r ^ 2) + √ε * mu := by
        have h1 : ε * √ε ≤ √ε := mul_le_of_le_one_left hs0.le hε1
        gcongr
    _ = _ := by ring

/-- **The input field is Lipschitz on discs**, with the constant
`(|d| + K₀ + ν|b| + 3A₃r²)/ν + 2A₂r/ν + l_u` when `U` is `ε²l_u`-Lipschitz on `‖w‖ ≤ r`. -/
@[tmio T, powerlib_foundation] theorem norm_inputField_sub_le (hν : 0 < ν) {r A2 A3 K0 lu : ℝ}
    {U : ℂ → ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hA2 : |α₂| ≤ A2) (hA3 : |α₃| ≤ A3)
    (hK0 : |k₁| ≤ K0) (hlu : 0 ≤ lu)
    (hUl : ∀ w w' t, ‖w‖ ≤ r → ‖w'‖ ≤ r → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖)
    {z z' : ℂ} (hz : ‖z‖ ≤ r) (hz' : ‖z'‖ ≤ r) (t : ℝ) :
    ‖inputField b d k₁ α₂ α₃ ν ε U z t - inputField b d k₁ α₂ α₃ ν ε U z' t‖ ≤
      ((|d| + K0 + ν * |b| + 3 * A3 * r ^ 2) / ν + 2 * A2 * r / ν + lu) * ‖z - z'‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hℓ : (|ν ^ 2 - (ν ^ 2 - d)| + |k₁| + ν * |b| + 3 * |α₃| * r ^ 2) / ν ≤
      (|d| + K0 + ν * |b| + 3 * A3 * r ^ 2) / ν := by
    rw [show ν ^ 2 - (ν ^ 2 - d) = d by ring]
    gcongr
  set ℓ₁ := (|d| + K0 + ν * |b| + 3 * A3 * r ^ 2) / ν with hℓ₁
  have hA30 : 0 ≤ A3 := (abs_nonneg _).trans hA3
  have hK00 : 0 ≤ K0 := (abs_nonneg _).trans hK0
  have hA20 : 0 ≤ A2 := (abs_nonneg _).trans hA2
  have hℓ₁0 : 0 ≤ ℓ₁ := by positivity
  have hV := DuffingMathieu.norm_vdpField_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁)
    (γ := α₃) hν hz hz' t
  have hQ := norm_quadField_sub_le (α₂ := α₂) hν hz hz' t
  have hU := hUl z z' t hz hz'
  have e : inputField b d k₁ α₂ α₃ ν ε U z t - inputField b d k₁ α₂ α₃ ν ε U z' t =
      ε • (vdpField b (ν ^ 2 - d) k₁ α₃ ν z t - vdpField b (ν ^ 2 - d) k₁ α₃ ν z' t) +
      √ε • (quadField α₂ ν z t - quadField α₂ ν z' t) + (√ε)⁻¹ • (U z t - U z' t) := by
    simp only [inputField, smul_sub]; abel
  rw [e]
  calc _ ≤ ε * (ℓ₁ * ‖z - z'‖) + √ε * (2 * A2 * r / ν * ‖z - z'‖) +
        (√ε)⁻¹ * (ε ^ 2 * lu * ‖z - z'‖) := by
        refine (norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [norm_smul, Real.norm_of_nonneg hε.le]
          exact mul_le_mul_of_nonneg_left (hV.trans (mul_le_mul_of_nonneg_right hℓ
            (norm_nonneg _))) hε.le
        · rw [norm_smul, Real.norm_of_nonneg hs0.le]
          refine mul_le_mul_of_nonneg_left (hQ.trans ?_) hs0.le
          gcongr
        · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
          exact mul_le_mul_of_nonneg_left hU (inv_nonneg.mpr hs0.le)
    _ = ε * (ℓ₁ * ‖z - z'‖) + √ε * (2 * A2 * r / ν * ‖z - z'‖) +
        ε * √ε * (lu * ‖z - z'‖) := by
        congr 1
        have h2 : ε ^ 2 = ε * √ε * √ε := by rw [mul_assoc, hss, sq]
        rw [h2]; field_simp
    _ ≤ 1 * (ℓ₁ * ‖z - z'‖) + 1 * (2 * A2 * r / ν * ‖z - z'‖) + 1 * (lu * ‖z - z'‖) := by
        have h1 : ε * √ε ≤ 1 := by nlinarith
        gcongr
    _ = _ := by ring

/-- The clamped input field is continuous when the input is. -/
@[tmio T, powerlib_foundation] theorem continuous_inputClamp (b d k₁ α₂ α₃ ν ε ρc : ℝ)
    {U : ℂ → ℝ → ℂ} (hU : Continuous fun q : ℝ × ℂ => U q.2 q.1) :
    Continuous (Function.uncurry (inputClamp b d k₁ α₂ α₃ ν ε ρc U)) := by
  have hcl := DuffingMathieu.continuous_clampC ρc
  have hc : Continuous fun q : ℝ × ℂ => clampC ρc q.2 := hcl.comp continuous_snd
  have hp : Continuous fun t : ℝ => phase ν t := by unfold phase; fun_prop
  have hpi : Continuous fun t : ℝ => (phase ν t)⁻¹ :=
    hp.inv₀ fun t => QuadraticCubic.phase_ne_zero ν t
  have h1 : Continuous fun q : ℝ × ℂ => vdpField b (ν ^ 2 - d) k₁ α₃ ν (clampC ρc q.2) q.1 := by
    simp only [vdpField, accel, pos, vel]
    fun_prop
  have h2 : Continuous fun q : ℝ × ℂ => quadField α₂ ν (clampC ρc q.2) q.1 := by
    simp only [quadField, pos]
    have : Continuous fun q : ℝ × ℂ => (phase ν q.1)⁻¹ := hpi.comp continuous_fst
    fun_prop
  have h3 : Continuous fun q : ℝ × ℂ => U (clampC ρc q.2) q.1 :=
    hU.comp (continuous_fst.prodMk hc)
  exact ((h1.const_smul ε).add (h2.const_smul √ε)).add (h3.const_smul (√ε)⁻¹)

/-- The clamped input field is globally Lipschitz. -/
@[tmio T, powerlib_foundation] theorem inputClamp_lipschitz (hν : 0 < ν) {ρc A2 A3 K0 lu : ℝ}
    {U : ℂ → ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρc : 0 ≤ ρc) (hA2 : |α₂| ≤ A2)
    (hA3 : |α₃| ≤ A3) (hK0 : |k₁| ≤ K0) (hlu : 0 ≤ lu)
    (hUl : ∀ w w' t, ‖w‖ ≤ 2 * ρc → ‖w'‖ ≤ 2 * ρc → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖)
    (t : ℝ) :
    LipschitzWith (Real.toNNReal ((|d| + K0 + ν * |b| + 3 * A3 * (2 * ρc) ^ 2) / ν +
      2 * A2 * (2 * ρc) / ν + lu)) (inputClamp b d k₁ α₂ α₃ ν ε ρc U t) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hA30 : 0 ≤ A3 := (abs_nonneg _).trans hA3
  have hK00 : 0 ≤ K0 := (abs_nonneg _).trans hK0
  have hA20 : 0 ≤ A2 := (abs_nonneg _).trans hA2
  have hL : 0 ≤ (|d| + K0 + ν * |b| + 3 * A3 * (2 * ρc) ^ 2) / ν + 2 * A2 * (2 * ρc) / ν + lu := by
    positivity
  rw [Real.coe_toNNReal _ hL]
  exact (norm_inputField_sub_le hν hε hε1 hA2 hA3 hK0 hlu hUl
    (DuffingMathieu.norm_clampC_le hρc w) (DuffingMathieu.norm_clampC_le hρc w') t).trans
    (mul_le_mul_of_nonneg_left (DuffingMathieu.norm_clampC_sub_le ρc w w') hL)

/-- The clamped input field is slow. -/
@[tmio T, powerlib_foundation] theorem norm_inputClamp_le (hν : 0 < ν) {ρc A2 A3 K0 mu : ℝ}
    {U : ℂ → ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρc : 0 ≤ ρc) (hA2 : |α₂| ≤ A2)
    (hA3 : |α₃| ≤ A3) (hK0 : |k₁| ≤ K0) (hmu : 0 ≤ mu)
    (hU : ∀ w t, ‖w‖ ≤ 2 * ρc → ‖U w t‖ ≤ ε ^ 2 * mu) (t : ℝ) (w : ℂ) :
    ‖inputClamp b d k₁ α₂ α₃ ν ε ρc U t w‖ ≤
      √ε * ((|d| + K0 + ν * |b| + 3 * A3 * (2 * ρc) ^ 2) / ν * (2 * ρc) +
        A2 / ν * (2 * ρc) ^ 2 + mu) :=
  norm_inputField_le hν hε hε1 (by positivity) hA2 hA3 hK0 hmu hU
    (DuffingMathieu.norm_clampC_le hρc w) t

/-- **Global solutions of the clamped amplitude equation with an input.** -/
@[tmio T, powerlib_foundation] theorem exists_inputClamp_solution (hν : 0 < ν)
    {ρc A2 A3 K0 lu : ℝ} {U : ℂ → ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρc : 0 ≤ ρc)
    (hA2 : |α₂| ≤ A2) (hA3 : |α₃| ≤ A3) (hK0 : |k₁| ≤ K0) (hlu : 0 ≤ lu)
    (hUl : ∀ w w' t, ‖w‖ ≤ 2 * ρc → ‖w'‖ ≤ 2 * ρc → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖)
    (hUc : Continuous fun q : ℝ × ℂ => U q.2 q.1) (τ : ℝ) (w₀ : ℂ) :
    ∃ w : ℝ → ℂ, w τ = w₀ ∧ ∀ t, HasDerivAt w (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (w t)) t := by
  have hcont :
      Continuous (Function.uncurry fun s (y : ℂ) => inputClamp b d k₁ α₂ α₃ ν ε ρc U (s + τ) y) :=
    ((continuous_inputClamp b d k₁ α₂ α₃ ν ε ρc hUc).comp
      ((continuous_fst.add (continuous_const (y := τ))).prodMk continuous_snd)).congr
        (fun q => rfl)
  obtain ⟨y, hy0, hy⟩ := DuffingMathieu.exists_global_solution hcont
    (fun s => inputClamp_lipschitz hν hε hε1 hρc hA2 hA3 hK0 hlu hUl (s + τ)) w₀
  refine ⟨fun t => y (t - τ), by simp [hy0], fun t => ?_⟩
  have h := (hy (t - τ)).comp_sub_const t τ
  rw [sub_add_cancel] at h
  exact h

/-- Clamped solutions with an input are unique. -/
@[tmio T, powerlib_foundation] theorem inputClamp_unique (hν : 0 < ν) {ρc A2 A3 K0 lu : ℝ}
    {U : ℂ → ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρc : 0 ≤ ρc) (hA2 : |α₂| ≤ A2)
    (hA3 : |α₃| ≤ A3) (hK0 : |k₁| ≤ K0) (hlu : 0 ≤ lu)
    (hUl : ∀ w w' t, ‖w‖ ≤ 2 * ρc → ‖w'‖ ≤ 2 * ρc → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖)
    {w w' : ℝ → ℂ} (hw : ∀ t, HasDerivAt w (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (w t)) t)
    (hw' : ∀ t, HasDerivAt w' (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (w' t)) t) {t₀ : ℝ}
    (h : w t₀ = w' t₀) : w = w' :=
  ODE_solution_unique_univ (v := inputClamp b d k₁ α₂ α₃ ν ε ρc U) (s := fun _ => univ)
    (fun t => (inputClamp_lipschitz hν hε hε1 hρc hA2 hA3 hK0 hlu hUl t).lipschitzOnWith)
    (fun t => ⟨hw t, mem_univ _⟩) (fun t => ⟨hw' t, mem_univ _⟩) h

/-- The clamped input field is `2π/ν`-periodic when the input is. -/
@[tmio T, powerlib_foundation] theorem inputClamp_periodic (hν : 0 < ν) (ρc : ℝ)
    {U : ℂ → ℝ → ℂ} (hUp : ∀ w t, U w (t + 2 * Real.pi / ν) = U w t) (t : ℝ) (w : ℂ) :
    inputClamp b d k₁ α₂ α₃ ν ε ρc U (t + 2 * Real.pi / ν) w =
      inputClamp b d k₁ α₂ α₃ ν ε ρc U t w := by
  simp only [inputClamp, inputField, quadField, DuffingMathieu.vdpField_periodic hν,
    pos_period₃ hν, phase_period₃ hν, hUp]

/-- **The transformed amplitude equation with an input along a clamped solution**: while
`‖w(t)‖ < ρc`, `W(t) = Wmap(w(t), t)` has the derivative `transIn(w(t), t)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_Wmap_input (hν : 0 < ν) (hε : 0 < ε)
    {ρc : ℝ} {U : ℂ → ℝ → ℂ} {w : ℝ → ℂ} {t : ℝ}
    (hw : HasDerivAt w (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (w t)) t) (hwt : ‖w t‖ < ρc) :
    HasDerivAt (fun s => Wmap α₂ ν ε ρc (w s) s) (transIn b d k₁ α₂ α₃ ν ε U (w t) t) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hcl : clampC ρc (w t) = w t := DuffingMathieu.clampC_of_norm_le hwt.le
  rw [inputClamp, hcl] at hw
  have hN := QuadraticCubic.hasDerivAt_nearId (α₂ := α₂) hν.ne' hw
  have hW := hw.sub (hN.const_smul √ε)
  have hev : (fun s => Wmap α₂ ν ε ρc (w s) s) =ᶠ[𝓝 t]
      fun s => w s - √ε • nearId α₂ ν (w s) s := by
    have hcont : ContinuousAt w t := hw.continuousAt
    filter_upwards [hcont.preimage_mem_nhds (Metric.ball_mem_nhds (w t) (sub_pos.mpr hwt))]
      with s hs
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hs
    have : ‖w s‖ ≤ ρc := by
      have := norm_le_norm_add_norm_sub' (w s) (w t)
      linarith
    simp only [Wmap, DuffingMathieu.clampC_of_norm_le this]
  refine (hW.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [transIn, inputField, QuadraticCubic.nearIdDeriv_add, nearIdDeriv_real_smul₃,
    QuadraticCubic.nearIdDeriv_quadField hν.ne', secondField, smul_add, smul_neg, smul_smul]
  have h2 : √ε * (√ε)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  rw [hss, h2, one_smul, show √ε * ε = ε * √ε by ring]
  abel

/-! ## The averaged limit field -/

/-- The averaged second-order amplitude field
`ampField (b/2) (d/(2ν)) (jk₁/(4ν)) 0 β_eff`, `β_eff = 3α₃/(8ν) − 5α₂²/(12ν³)`: the period average
of `secondField b (ν² − d) k₁ α₂ α₃ ν` (`QuadraticCubic.fieldAverage_secondField`). -/
abbrev secondAmp (b d k₁ α₂ α₃ ν : ℝ) : ℂ → ℂ :=
  ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
    (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3))

/-- The Jacobian of `secondAmp` at `w` in the real coordinates `(Re w, Im w)`. -/
abbrev secondJac (b d k₁ α₂ α₃ ν : ℝ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ampJacobian (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
    (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (toReal w)

/-- The derivative of the second-order field in the real coordinates. -/
def secondDerivR (b d k₁ α₂ α₃ ν : ℝ) (x : ℝ²) (t : ℝ) : ℝ² →L[ℝ] ℝ² :=
  (toReal : ℂ →L[ℝ] ℝ²).comp ((secondDeriv b (ν ^ 2 - d) k₁ α₂ α₃ ν (toReal.symm x) t).comp
    (toReal.symm : ℝ² →L[ℝ] ℂ))

/-- **The cut-off second-order field in real coordinates at a locked state** `w*` of
`secondAmp`: derivative, Lipschitz derivative within `1` of `w*`, continuity in time, period
average `0` at `w*` and its derivative `secondJac` there. -/
@[tmio T, powerlib_foundation] theorem second_hyp {ρc : ℝ} (hν : 0 < ν) {wstar : ℂ}
    (hw0 : secondAmp b d k₁ α₂ α₃ ν wstar = 0) (hρc : ‖wstar‖ + 1 < ρc) :
    (∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ∀ t, HasFDerivAt (fun y => realField
      (QuadraticCubic.cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν ρc) y t)
        (secondDerivR b d k₁ α₂ α₃ ν x t) x) ∧
    (∀ x y : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖y - toReal wstar‖ ≤ 1 → ∀ t,
      ‖secondDerivR b d k₁ α₂ α₃ ν x t - secondDerivR b d k₁ α₂ α₃ ν y t‖ ≤
        (6 * |α₃| / ν + 5 * α₂ ^ 2 / ν ^ 3) * (‖wstar‖ + 1) * ‖x - y‖) ∧
    Continuous (secondDerivR b d k₁ α₂ α₃ ν (toReal wstar)) ∧
    Averaging.fieldAverage (realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν ρc))
      (2 * Real.pi / ν) (toReal wstar) = 0 ∧
    HasFDerivAt (Averaging.fieldAverage (realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k₁
      α₂ α₃ ν ρc)) (2 * Real.pi / ν))
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (secondJac b d k₁ α₂ α₃ ν wstar))
      (toReal wstar) := by
  have hρc0 : 0 ≤ ρc := by linarith [norm_nonneg wstar]
  have hball : ∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖toReal.symm x‖ ≤ ‖wstar‖ + 1 := by
    intro x hx
    rw [norm_toReal_symm₃]
    have := norm_le_norm_add_norm_sub' x (toReal wstar)
    rw [Saturation.norm_toReal] at this
    linarith
  have hav : ∀ x : ℝ², ‖x‖ ≤ ρc → Averaging.fieldAverage (realField (QuadraticCubic.cutSecond b
      (ν ^ 2 - d) k₁ α₂ α₃ ν ρc)) (2 * Real.pi / ν) x =
      ampSystem (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) x := by
    intro x hx
    rw [SubharmonicOrbit.fieldAverage_realField (fun w => Averaging.PeriodicField.continuous_snd
      (QuadraticCubic.cutSecond_hyp hν hρc0) w)]
    have hw : ‖toReal.symm x‖ ≤ ρc := by rw [norm_toReal_symm₃]; exact hx
    have e : Averaging.fieldAverage (QuadraticCubic.cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν ρc)
        (2 * Real.pi / ν) (toReal.symm x) =
        Averaging.fieldAverage (secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν) (2 * Real.pi / ν)
          (toReal.symm x) := by
      simp only [Averaging.fieldAverage, QuadraticCubic.cutSecond,
        DuffingMathieu.clampC_of_norm_le hw]
    rw [e, QuadraticCubic.fieldAverage_secondField hν, show ν ^ 2 - (ν ^ 2 - d) = d by ring,
      ← Saturation.toReal_ampField, ContinuousLinearEquiv.apply_symm_apply]
  have hy : ‖toReal wstar‖ < ρc := by rw [Saturation.norm_toReal]; linarith
  refine ⟨fun x hx t => ?_, fun x y hx hy t => ?_, ?_, ?_, ?_⟩
  · apply SubharmonicOrbit.hasFDerivAt_realField
    exact hasFDerivAt_cutSecond (by linarith [hball x hx]) t
  · have e : secondDerivR b d k₁ α₂ α₃ ν x t - secondDerivR b d k₁ α₂ α₃ ν y t =
        (toReal : ℂ →L[ℝ] ℝ²).comp ((secondDeriv b (ν ^ 2 - d) k₁ α₂ α₃ ν (toReal.symm x) t -
          secondDeriv b (ν ^ 2 - d) k₁ α₂ α₃ ν (toReal.symm y) t).comp
            (toReal.symm : ℝ² →L[ℝ] ℂ)) := by
      simp only [secondDerivR, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    rw [e]
    refine (SubharmonicOrbit.norm_conj_toReal_le _).trans ?_
    have h := norm_secondDeriv_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁) (α₂ := α₂)
      (α₃ := α₃) hν (hball x hx) (hball y hy) t
    rw [← map_sub, norm_toReal_symm₃] at h
    exact h
  · refine continuous_clm_apply.mpr fun h => ?_
    simp only [secondDerivR, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact toReal.continuous.comp
      ((continuous_clm_apply.mp (continuous_secondDeriv _ _ _ _ _ _ _)) _)
  · rw [hav _ hy.le, Saturation.toReal_ampField]
    show toReal (secondAmp b d k₁ α₂ α₃ ν wstar) = 0
    rw [hw0, map_zero]
  · refine (Saturation.hasFDerivAt_ampSystem _ _ _ _ _ _).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (toReal wstar) (sub_pos.mpr hy)] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    apply hav
    have := norm_le_norm_add_norm_sub' x (toReal wstar)
    linarith [norm_sub_rev x (toReal wstar)]

/-! ## The core estimates and the periodic orbit of the amplitude equation with an input -/

/-- **The core estimates for an input.** Let `w*` be given, the limit coefficients
`k₁⁰, α₂⁰, α₃⁰` and the constants `K₁, K₂, K₃, A₂, A₃, K₀, μ, l_u ≥ 0`. There are `ε₁ > 0` and
`M_q, L_q, D_c ≥ 0` such that for every `0 < ε ≤ ε₁`, all coefficients with
`|k₁ − k₁⁰| ≤ εK₁`, `|α₂² − α₂⁰²| ≤ εK₂`, `|α₃ − α₃⁰| ≤ εK₃`, `|α₂| ≤ A₂`, `|α₃| ≤ A₃`,
`|k₁| ≤ K₀`, and every input with `‖U‖ ≤ ε²μ`, `ε²l_u`-Lipschitz on `‖w‖ ≤ 2(‖w*‖ + 3)`: the
clamped transformation `Wmap` (clamp radius `‖w*‖ + 3`) is onto, `2`-co-Lipschitz,
`3/2`-Lipschitz and moves by at most `min(1/2, √ε D_c)`; along every clamped solution and over
every period that starts with `Wmap(w(s), s)` within `1/2` of `w*`, `w` stays within `3/2` of
`w*` and the transformed amplitude solves `Ẇ = ε F⁰_cut(W, t) + transRem(w, t)` (real
coordinates, `F⁰ = secondField b (ν² − d) k₁⁰ α₂⁰ α₃⁰ ν`); and `transRem` is bounded by
`ε√ε M_q` and `ε√ε L_q`-Lipschitz within `3/2` of `w*` (`transRem_bounds`). -/
@[tmio T, powerlib_foundation] theorem input_core {ν : ℝ} (hν : 0 < ν)
    (b d k10 a20 a30 K1 K2 K3 A2 A3 K0 mu lu : ℝ) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hK0 : 0 ≤ K0) (hmu : 0 ≤ mu) (hlu : 0 ≤ lu) (wstar : ℂ) :
    ∃ ε₁ Mq Lq Dc : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 ≤ Mq ∧ 0 ≤ Lq ∧ 0 ≤ Dc ∧ ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∀ (k₁ α₂ α₃ : ℝ) (U : ℂ → ℝ → ℂ),
      |k₁ - k10| ≤ ε * K1 → |α₂ ^ 2 - a20 ^ 2| ≤ ε * K2 → |α₃ - a30| ≤ ε * K3 →
      |α₂| ≤ A2 → |α₃| ≤ A3 → |k₁| ≤ K0 →
      (∀ w t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖U w t‖ ≤ ε ^ 2 * mu) →
      (∀ w w' t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖w'‖ ≤ 2 * (‖wstar‖ + 3) →
        ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖) →
      (∀ w w' t, ‖w - w'‖ ≤ 2 * ‖Wmap α₂ ν ε (‖wstar‖ + 3) w t -
        Wmap α₂ ν ε (‖wstar‖ + 3) w' t‖) ∧
      (∀ w w' t, ‖Wmap α₂ ν ε (‖wstar‖ + 3) w t -
        Wmap α₂ ν ε (‖wstar‖ + 3) w' t‖ ≤ 3 / 2 * ‖w - w'‖) ∧
      (∀ w t, ‖Wmap α₂ ν ε (‖wstar‖ + 3) w t - w‖ ≤ √ε * Dc) ∧
      (∀ W t, ∃ w, Wmap α₂ ν ε (‖wstar‖ + 3) w t = W) ∧
      (∀ w t, ‖Wmap α₂ ν ε (‖wstar‖ + 3) w t - w‖ ≤ 1 / 2) ∧
      (∀ w : ℝ → ℂ, (∀ t, HasDerivAt w (inputClamp b d k₁ α₂ α₃ ν ε (‖wstar‖ + 3) U t (w t)) t) →
        ∀ s, ‖Wmap α₂ ν ε (‖wstar‖ + 3) (w s) s - wstar‖ ≤ 1 / 2 →
        ∀ t ∈ Icc s (s + 2 * Real.pi / ν), ‖w t - wstar‖ ≤ 3 / 2 ∧
          HasDerivAt (fun t => toReal (Wmap α₂ ν ε (‖wstar‖ + 3) (w t) t))
            (ε • realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν (‖wstar‖ + 3))
              (toReal (Wmap α₂ ν ε (‖wstar‖ + 3) (w t) t)) t +
              toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (w t) t)) t) ∧
      ∀ w w' t, ‖w - wstar‖ ≤ 3 / 2 → ‖w' - wstar‖ ≤ 3 / 2 →
        ‖transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U w t‖ ≤ ε * √ε * Mq ∧
        ‖transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U w t -
          transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U w' t‖ ≤ ε * √ε * Lq * ‖w - w'‖ := by
  set R := ‖wstar‖ with hR
  set ρc := R + 3 with hρc
  set r := R + 2 with hr
  set T := 2 * Real.pi / ν with hT
  have hR0 : 0 ≤ R := norm_nonneg _
  have hρc0 : 0 ≤ ρc := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hT0 : 0 < T := by positivity
  obtain ⟨Mq, Lq, hMq, hLq, hTR⟩ := transRem_bounds hν b d k10 a20 a30 r K1 K2 K3 A2 A3 K0 mu lu
    hr0 hA2 hA3 hK0 hK1 hK2 hK3 hmu hlu
  set c₂ := 5 * A2 / (3 * ν ^ 2) with hc₂
  set D₁ := 5 * A2 / (6 * ν ^ 2) * (2 * ρc) ^ 2 with hD₁
  set S := (|d| + K0 + ν * |b| + 3 * A3 * (2 * ρc) ^ 2) / ν * (2 * ρc) +
    A2 / ν * (2 * ρc) ^ 2 + mu with hS
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hD₁0 : 0 ≤ D₁ := by positivity
  have hS0 : 0 ≤ S := by positivity
  set σ := min (1 / (2 * (c₂ * (2 * ρc) + 1))) (min (1 / (2 * (D₁ + 1))) (1 / (2 * (S * T + 1))))
    with hσ
  have hσ0 : 0 < σ := by
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨min 1 (σ ^ 2), Mq, Lq, D₁, by positivity, min_le_left _ _, hMq, hLq, hD₁0, ?_⟩
  intro ε hε hεε₁ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl
  have hε1 : ε ≤ 1 := hεε₁.trans (min_le_left _ _)
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hsσ : √ε ≤ σ := by
    have : ε ≤ σ ^ 2 := hεε₁.trans (min_le_right _ _)
    calc √ε ≤ √(σ ^ 2) := Real.sqrt_le_sqrt this
      _ = σ := Real.sqrt_sq hσ0.le
  -- the smallness conditions
  have hsm1 : √ε * (5 * |α₂| / (3 * ν ^ 2) * (2 * ρc)) ≤ 1 / 2 := by
    have h1 : 5 * |α₂| / (3 * ν ^ 2) * (2 * ρc) ≤ c₂ * (2 * ρc) := by
      rw [hc₂]; gcongr
    have h2' : σ ≤ 1 / (2 * (c₂ * (2 * ρc) + 1)) := min_le_left _ _
    calc √ε * (5 * |α₂| / (3 * ν ^ 2) * (2 * ρc)) ≤ σ * (c₂ * (2 * ρc)) :=
          mul_le_mul hsσ h1 (by positivity) hσ0.le
      _ ≤ 1 / (2 * (c₂ * (2 * ρc) + 1)) * (c₂ * (2 * ρc)) :=
          mul_le_mul_of_nonneg_right h2' (by positivity)
      _ ≤ 1 / 2 := half_bound₃ (by positivity)
  have hsm2 : ∀ w t, ‖Wmap α₂ ν ε ρc w t - w‖ ≤ 1 / 2 := by
    intro w t
    refine (norm_Wmap_sub_le hν hρc0 w t).trans ?_
    have h1 : 5 * |α₂| / (6 * ν ^ 2) * (2 * ρc) ^ 2 ≤ D₁ := by rw [hD₁]; gcongr
    have h2' : σ ≤ 1 / (2 * (D₁ + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    calc √ε * (5 * |α₂| / (6 * ν ^ 2) * (2 * ρc) ^ 2) ≤ σ * D₁ :=
          mul_le_mul hsσ h1 (by positivity) hσ0.le
      _ ≤ 1 / (2 * (D₁ + 1)) * D₁ := mul_le_mul_of_nonneg_right h2' hD₁0
      _ ≤ 1 / 2 := half_bound₃ hD₁0
  have hsm3 : √ε * S * T ≤ 1 / 2 := by
    have h2' : σ ≤ 1 / (2 * (S * T + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    calc √ε * S * T = √ε * (S * T) := by ring
      _ ≤ σ * (S * T) := mul_le_mul_of_nonneg_right hsσ (by positivity)
      _ ≤ 1 / (2 * (S * T + 1)) * (S * T) := mul_le_mul_of_nonneg_right h2' (by positivity)
      _ ≤ 1 / 2 := half_bound₃ (by positivity)
  -- the bounds of the transformed remainder
  have hr2 : r ≤ 2 * ρc := by rw [hr, hρc]; linarith
  have hTRε := hTR ε hε hε1 k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0'
    (fun w t hw => hU w t (hw.trans hr2))
    (fun w w' t hw hw' => hUl w w' t (hw.trans hr2) (hw'.trans hr2))
  have hdisc : ∀ w : ℂ, ‖w - wstar‖ ≤ 3 / 2 → ‖w‖ ≤ r := by
    intro w hw
    have := norm_le_norm_add_norm_sub' w wstar
    rw [hr]; linarith
  have hsmD : ∀ w t, ‖Wmap α₂ ν ε ρc w t - w‖ ≤ √ε * D₁ := by
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
    calc ‖w s - wstar‖ = ‖(Wmap α₂ ν ε ρc (w s) s - wstar) -
          (Wmap α₂ ν ε ρc (w s) s - w s)‖ := by congr 1; abel
      _ ≤ 1 / 2 + 1 / 2 := (norm_sub_le _ _).trans (add_le_add hs h1)
      _ = 1 := by norm_num
  have hdrift : ‖w t - w s‖ ≤ 1 / 2 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := w)
      (f' := fun u => inputClamp b d k₁ α₂ α₃ ν ε ρc U u (w u)) (C := √ε * S)
      (fun u _ => (hw u).hasDerivWithinAt)
      (fun u _ => norm_inputClamp_le hν hε hε1 hρc0 hA2' hA3' hK0' hmu hU u (w u)) t ht
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
    rw [hρc]; rw [hr] at this; linarith
  have hD := hasDerivAt_Wmap_input (b := b) (d := d) (k₁ := k₁) (α₃ := α₃) hν hε (hw t) hwn
  have hD' := (toReal : ℂ →L[ℝ] ℝ²).hasFDerivAt.comp_hasDerivAt t hD
  refine hD'.congr_deriv ?_
  -- the transformed field is the limit field at `W` plus the transformed remainder
  have hcl : clampC ρc (w t) = w t := DuffingMathieu.clampC_of_norm_le hwn.le
  have hWeq : Wmap α₂ ν ε ρc (w t) t = w t - √ε • nearId α₂ ν (w t) t := by
    rw [Wmap, hcl]
  have hWn : ‖Wmap α₂ ν ε ρc (w t) t‖ ≤ ρc := by
    have h1 := hsm2 (w t) t
    have h2 := norm_le_norm_add_norm_sub' (Wmap α₂ ν ε ρc (w t) t) (w t)
    have h3 := hdisc (w t) hwt
    rw [hρc]; rw [hr] at h3; linarith
  have hf : realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρc)
      (toReal (Wmap α₂ ν ε ρc (w t) t)) t =
      toReal (secondField b (ν ^ 2 - d) k10 a20 a30 ν (w t - √ε • nearId α₂ ν (w t) t) t) := by
    simp only [realField, ContinuousLinearEquiv.symm_apply_apply, QuadraticCubic.cutSecond]
    rw [DuffingMathieu.clampC_of_norm_le hWn, hWeq]
  rw [hf, ContinuousLinearEquiv.coe_coe, ← map_smul, ← map_add]
  congr 1
  simp only [transRem, transIn]
  abel

set_option maxHeartbeats 1000000 in
/-- **The periodic orbit of the amplitude equation with an input, unique near the locked
state.** Let `w*` be a nondegenerate locked state of the averaged limit field,
`secondAmp b d k₁⁰ α₂⁰ α₃⁰ ν w* = 0`, `det (secondJac … w*) ≠ 0`, and fix the constants
`K₁, K₂, K₃, A₂, A₃, K₀, μ, l_u ≥ 0` of `input_core`. There are `ε₀ > 0`, `C ≥ 0` and `r₀ > 0`
such that for every `0 < ε ≤ ε₀`, all coefficients and every continuous, `2π/ν`-periodic input
`U` within these bounds, the clamped amplitude equation `ẇ = inputClamp(w, t)` (clamp radius
`‖w*‖ + 3`) has a `2π/ν`-periodic solution `w` with `‖w − w*‖ ≤ min(3/2, √ε C)`, and every
clamped solution `z` with `‖z(0) − w*‖ ≤ r₀` stays within `3/2` of `w*` over the first period
and, if `z(2π/ν) = z(0)`, is `w` (`Averaging.exists_periodic_point_perturbed` with `η = ε√ε`,
uniqueness clause included). -/
@[tmio T, powerlib_foundation] theorem input_orbit {ν : ℝ} (hν : 0 < ν) {b d k10 a20 a30 : ℝ}
    {K1 K2 K3 A2 A3 K0 mu lu : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hA2 : 0 ≤ A2)
    (hA3 : 0 ≤ A3) (hK0 : 0 ≤ K0) (hmu : 0 ≤ mu) (hlu : 0 ≤ lu) {wstar : ℂ}
    (hw0 : secondAmp b d k10 a20 a30 ν wstar = 0)
    (hdet : (secondJac b d k10 a20 a30 ν wstar).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ (k₁ α₂ α₃ : ℝ) (U : ℂ → ℝ → ℂ),
      |k₁ - k10| ≤ ε * K1 → |α₂ ^ 2 - a20 ^ 2| ≤ ε * K2 → |α₃ - a30| ≤ ε * K3 →
      |α₂| ≤ A2 → |α₃| ≤ A3 → |k₁| ≤ K0 →
      (∀ w t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖U w t‖ ≤ ε ^ 2 * mu) →
      (∀ w w' t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖w'‖ ≤ 2 * (‖wstar‖ + 3) →
        ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖) →
      Continuous (fun q : ℝ × ℂ => U q.2 q.1) → (∀ w t, U w (t + 2 * Real.pi / ν) = U w t) →
      ∃ w : ℝ → ℂ, (∀ t, HasDerivAt w (inputClamp b d k₁ α₂ α₃ ν ε (‖wstar‖ + 3) U t (w t)) t) ∧
        (∀ t, w (t + 2 * Real.pi / ν) = w t) ∧ (∀ t, ‖w t - wstar‖ ≤ 3 / 2) ∧
        (∀ t, ‖w t - wstar‖ ≤ √ε * C) ∧
        ∀ z : ℝ → ℂ, (∀ t, HasDerivAt z (inputClamp b d k₁ α₂ α₃ ν ε (‖wstar‖ + 3) U t (z t)) t) →
          ‖z 0 - wstar‖ ≤ r₀ → (∀ t ∈ Icc 0 (2 * Real.pi / ν), ‖z t - wstar‖ ≤ 3 / 2) ∧
            (z (2 * Real.pi / ν) = z 0 → z = w) := by
  obtain ⟨ε₁, Mq, Lq, Dc, hε₁, hε₁1, hMq, hLq, hDc0, hcore⟩ :=
    input_core hν b d k10 a20 a30 K1 K2 K3 A2 A3 K0 mu lu hK1 hK2 hK3 hA2 hA3 hK0 hmu hlu wstar
  set ρc := ‖wstar‖ + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  have hfh := SubharmonicOrbit.realField_hyp (QuadraticCubic.cutSecond_hyp (b := b)
    (k₀ := ν ^ 2 - d) (k₁ := k10) (α₂ := a20) (α₃ := a30) hν hρc0)
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) k10 a20 a30 ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  have hℓ0 : 0 ≤ ℓ := hfh.2.1
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨hD, hDl, hDc, h0, hA⟩ := second_hyp (ρc := ρc) hν hw0 (by linarith)
  set L₂ := (6 * |a30| / ν + 5 * a20 ^ 2 / ν ^ 3) * (‖wstar‖ + 1) with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  set J := secondJac b d k10 a20 a30 ν wstar with hJ
  set B := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ with hB
  have hAB := fun v => (toEuclideanCLM_inv_apply₃ hdet v).1
  have hBA := fun v => (toEuclideanCLM_inv_apply₃ hdet v).2
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
  set σ := min (T / (4 * ‖B‖ * LS + 1)) (min (r₀ * T / (2 * ‖B‖ * CS + 1)) (r₀ / (2 * (Dc + 1))))
    with hσ
  have hσ0 : 0 < σ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set C := Dc + (M + Mq) * T + 2 * ‖B‖ * CS / T with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨min (min ε₁ (1 / (2 * (M + Mq) * T + 1))) (σ ^ 2), C, r₀ / 2, by positivity, hC0,
    by positivity, ?_⟩
  intro ε hε hεε₀ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl hUc hUp
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
  have hUl' : ∀ w w' t, ‖w‖ ≤ 2 * ρc → ‖w'‖ ≤ 2 * ρc → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖ :=
    hUl
  obtain ⟨hbil, -, hWD, hsurj, -, hbund, hTR⟩ :=
    hcore ε hε hεε₁ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl
  -- the family of transformed amplitudes
  choose w₀ hw₀ using fun y : ℝ² => hsurj (toReal.symm y) 0
  choose W hW0 hW using fun y : ℝ² =>
    exists_inputClamp_solution (b := b) (d := d) hν hε hε1 hρc0 hA2' hA3' hK0' hlu hUl' hUc 0
      (w₀ y)
  set X : ℝ² → ℝ → ℝ² := fun y t => toReal (Wmap α₂ ν ε ρc (W y t) t) with hX
  set Q : ℝ² → ℝ → ℝ² := fun y t => toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (W y t) t)
    with hQ
  have hX0 : ∀ y, X y 0 = y := fun y => by
    simp only [hX, hW0, hw₀, ContinuousLinearEquiv.apply_symm_apply]
  have hstart : ∀ y : ℝ², ‖y - toReal wstar‖ ≤ 1 / 2 →
      ‖Wmap α₂ ν ε ρc (W y 0) 0 - wstar‖ ≤ 1 / 2 := by
    intro y hy
    rw [hW0, hw₀, ← norm_toReal_symm₃, map_sub, ContinuousLinearEquiv.symm_apply_apply] at *
    exact hy
  have hper : ∀ y, ‖y - toReal wstar‖ ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) T,
      ‖W y t - wstar‖ ≤ 3 / 2 ∧ HasDerivAt (X y)
        (ε • realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρc) (X y t) t +
          Q y t) t :=
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
    have h1 : √ε ≤ r₀ * T / (2 * ‖B‖ * CS + 1) :=
      hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : 2 * √ε * ‖B‖ * CS ≤ r₀ * T := by
      have e : √ε * (2 * ‖B‖ * CS + 1) = 2 * √ε * ‖B‖ * CS + √ε := by ring
      linarith only [h1, e, hs0]
    calc 2 * (ε * √ε) * ‖B‖ * CS = ε * (2 * √ε * ‖B‖ * CS) := by ring
      _ ≤ ε * (r₀ * T) := mul_le_mul_of_nonneg_left h2 hε.le
      _ = ε * r₀ * T := by ring
  have hsD : √ε * Dc ≤ r₀ / 2 := by
    have h1 : √ε ≤ r₀ / (2 * (Dc + 1)) := hsσ.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : √ε * (2 * (Dc + 1)) = 2 * (√ε * Dc) + 2 * √ε := by ring
    linarith only [h1, e, hs0]
  obtain ⟨yε, hyε, hfix, hun⟩ := Averaging.exists_periodic_point_perturbed hfh one_pos hL₂0 hD
    hDl hDc h0 hA hAB hBA hr₀0 hr₀ρ hr₀L hε hε1 hηε hεη (by positivity) hMq hερ hηL hηC hX0
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
        _ ≤ ε * √ε * Lq * (2 * ‖Wmap α₂ ν ε ρc (W y t) t - Wmap α₂ ν ε ρc (W y' t) t‖) :=
            mul_le_mul_of_nonneg_left hb2 (by positivity)
        _ = ε * √ε * (2 * Lq) * ‖Wmap α₂ ν ε ρc (W y t) t - Wmap α₂ ν ε ρc (W y' t) t‖ := by
            ring)
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
    have h1 : Wmap α₂ ν ε ρc (w T) T = Wmap α₂ ν ε ρc (w 0) 0 := by
      have := hfix
      simp only [hX] at this
      have h0' : toReal (Wmap α₂ ν ε ρc (w 0) 0) = yε := hX0 yε
      exact toReal.injective (this.trans h0'.symm)
    have h2 : Wmap α₂ ν ε ρc (w T) 0 = Wmap α₂ ν ε ρc (w 0) 0 := by
      rw [← h1, show T = 0 + 2 * Real.pi / ν by rw [zero_add], Wmap_periodic hν]
    have := hbil (w T) (w 0) 0
    rw [h2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hwper : ∀ t, w (t + T) = w t := by
    have hshift : ∀ t, HasDerivAt (fun t => w (t + T))
        (inputClamp b d k₁ α₂ α₃ ν ε ρc U t (w (t + T))) t := by
      intro t
      have h := (hW yε (t + T)).comp_add_const t T
      rw [inputClamp_periodic hν ρc hUp] at h
      exact h
    have := inputClamp_unique hν hε hε1 hρc0 hA2' hA3' hK0' hlu hUl' hshift (hW yε) (t₀ := 0)
      (by show w (0 + T) = w 0; rw [zero_add, hwT])
    exact fun t => congrFun this t
  have hwin : ∀ t, ‖w t - wstar‖ ≤ 3 / 2 ∧ ‖w t - wstar‖ ≤ √ε * C := by
    intro t
    obtain ⟨t', ht', hwt⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := w) hwper hT0 t
    rw [hwt]
    have ht'' : t' ∈ Icc (0 : ℝ) T := ⟨ht'.1, ht'.2.le⟩
    refine ⟨(hper yε hyεh t' ht'').1, ?_⟩
    -- the drift of the transformed amplitude over one period
    have hdr := Averaging.perturbed_drift_le
      (f := realField (QuadraticCubic.cutSecond b (ν ^ 2 - d) k10 a20 a30 ν ρc))
      hfh.2.2.2.2.2 hε.le (η := ε * √ε) (Mq := Mq) (x := X yε) (q := Q yε) ht'.1
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
    have hW1 : ‖w t' - Wmap α₂ ν ε ρc (w t') t'‖ ≤ √ε * Dc := by
      rw [norm_sub_rev]; exact hWD _ _
    have hW2 : ‖Wmap α₂ ν ε ρc (w t') t' - toReal.symm yε‖ = ‖X yε t' - yε‖ := by
      rw [← norm_toReal_symm₃, map_sub, ContinuousLinearEquiv.symm_apply_apply]
    have hW3 : ‖toReal.symm yε - wstar‖ ≤ 2 * √ε * ‖B‖ * CS / T := by
      rw [← norm_toReal_symm₃ (yε - toReal wstar), map_sub,
        ContinuousLinearEquiv.symm_apply_apply] at hyε'
      exact hyε'
    calc ‖w t' - wstar‖ = ‖(w t' - Wmap α₂ ν ε ρc (w t') t') +
          (Wmap α₂ ν ε ρc (w t') t' - toReal.symm yε) + (toReal.symm yε - wstar)‖ := by
          congr 1; abel
      _ ≤ √ε * Dc + √ε * ((M + Mq) * T) + 2 * √ε * ‖B‖ * CS / T := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add hW1 (hW2.le.trans hdr'))) hW3)
      _ = √ε * C := by rw [hC]; ring
  refine ⟨w, hW yε, hwper, fun t => (hwin t).1, fun t => (hwin t).2, ?_⟩
  -- uniqueness: a clamped solution starting near `w*` that returns after one period is `w`
  intro z hz hz0
  set y' := toReal (Wmap α₂ ν ε ρc (z 0) 0) with hy'
  have hy'b : ‖y' - toReal wstar‖ ≤ r₀ := by
    rw [hy', ← map_sub, Saturation.norm_toReal]
    calc ‖Wmap α₂ ν ε ρc (z 0) 0 - wstar‖ ≤ ‖Wmap α₂ ν ε ρc (z 0) 0 - z 0‖ + ‖z 0 - wstar‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r₀ / 2 + r₀ / 2 := add_le_add ((hWD _ _).trans hsD) hz0
      _ = r₀ := by ring
  have hw₀z : w₀ y' = z 0 := by
    have h1 : Wmap α₂ ν ε ρc (w₀ y') 0 = Wmap α₂ ν ε ρc (z 0) 0 := by
      rw [hw₀, hy', ContinuousLinearEquiv.symm_apply_apply]
    have := hbil (w₀ y') (z 0) 0
    rw [h1, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hWz : W y' = z := inputClamp_unique hν hε hε1 hρc0 hA2' hA3' hK0' hlu hUl' (hW y') hz
    (t₀ := 0) (by rw [hW0, hw₀z])
  have hy'h : ‖y' - toReal wstar‖ ≤ 1 / 2 := hy'b.trans hr₀h
  refine ⟨fun t ht => ?_, fun hzT => ?_⟩
  · rw [← hWz]; exact (hper y' hy'h t ht).1
  · have hXT : X y' T = y' := by
      simp only [hX, hWz]
      rw [hzT, show T = 0 + 2 * Real.pi / ν by rw [zero_add], Wmap_periodic hν]
    have := hun y' hy'b hXT
    rw [← hWz, this]

/-! ## Stability of the orbit of the amplitude equation with an input -/

set_option maxHeartbeats 1000000 in
/-- **The orbit of a Hurwitz locked state attracts the clamped solutions.** If the Jacobian
`secondJac b d k₁⁰ α₂⁰ α₃⁰ ν w*` of the averaged limit field at the locked state `w*` is
Hurwitz, there are `ε₀, ρ_s, K, β > 0` and `C ≥ 0` such that for every `0 < ε ≤ ε₀`, all
coefficients and inputs within the bounds of `input_orbit`, the clamped amplitude equation has a
`2π/ν`-periodic solution `w` with `‖w − w*‖ ≤ min(3/2, √ε C)`, and every clamped solution `x`
with `‖x(τ) − w(τ)‖ ≤ ρ_s` satisfies `‖x(t) − w(t)‖ ≤ K e^{−βε(t − τ)} ‖x(τ) − w(τ)‖` and stays
inside the clamp, `‖x(t)‖ < ‖w*‖ + 3`, for `t ≥ τ` (`Averaging.exp_stable_perturbed` with the
Lyapunov matrix of the Jacobian, LeanForControl
`IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov`). -/
@[tmio T, powerlib_foundation] theorem input_orbit_stable {ν : ℝ} (hν : 0 < ν)
    {b d k10 a20 a30 : ℝ} {K1 K2 K3 A2 A3 K0 mu lu : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hK0 : 0 ≤ K0) (hmu : 0 ≤ mu) (hlu : 0 ≤ lu)
    {wstar : ℂ} (hw0 : secondAmp b d k10 a20 a30 ν wstar = 0)
    (hJ : LinearSystems.IsHurwitz (secondJac b d k10 a20 a30 ν wstar)) :
    ∃ ε₀ C ρs K β : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < ρs ∧ 0 < K ∧ 0 < β ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ (k₁ α₂ α₃ : ℝ) (U : ℂ → ℝ → ℂ),
      |k₁ - k10| ≤ ε * K1 → |α₂ ^ 2 - a20 ^ 2| ≤ ε * K2 → |α₃ - a30| ≤ ε * K3 →
      |α₂| ≤ A2 → |α₃| ≤ A3 → |k₁| ≤ K0 →
      (∀ w t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖U w t‖ ≤ ε ^ 2 * mu) →
      (∀ w w' t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖w'‖ ≤ 2 * (‖wstar‖ + 3) →
        ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖) →
      Continuous (fun q : ℝ × ℂ => U q.2 q.1) → (∀ w t, U w (t + 2 * Real.pi / ν) = U w t) →
      ∃ w : ℝ → ℂ, (∀ t, HasDerivAt w (inputClamp b d k₁ α₂ α₃ ν ε (‖wstar‖ + 3) U t (w t)) t) ∧
        (∀ t, w (t + 2 * Real.pi / ν) = w t) ∧ (∀ t, ‖w t - wstar‖ ≤ 3 / 2) ∧
        (∀ t, ‖w t - wstar‖ ≤ √ε * C) ∧
        ∀ x : ℝ → ℂ, (∀ t, HasDerivAt x (inputClamp b d k₁ α₂ α₃ ν ε (‖wstar‖ + 3) U t (x t)) t) →
          ∀ τ, ‖x τ - w τ‖ ≤ ρs → ∀ t, τ ≤ t →
            ‖x t - w t‖ ≤ K * Real.exp (-(β * ε * (t - τ))) * ‖x τ - w τ‖ ∧
            ‖x t‖ < ‖wstar‖ + 3 := by
  have hdet : (secondJac b d k10 a20 a30 ν wstar).det ≠ 0 :=
    (Criteria.isUnit_det_of_isHurwitz hJ).ne_zero
  obtain ⟨ε₁, Mq, Lq, Dc, hε₁, hε₁1, hMq, hLq, hDc0, hcore⟩ :=
    input_core hν b d k10 a20 a30 K1 K2 K3 A2 A3 K0 mu lu hK1 hK2 hK3 hA2 hA3 hK0 hmu hlu wstar
  obtain ⟨ε₂, C, r₀o, hε₂, hC, -, horb⟩ := input_orbit hν hK1 hK2 hK3 hA2 hA3 hK0 hmu hlu hw0 hdet
  set ρc := ‖wstar‖ + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  have hfh := SubharmonicOrbit.realField_hyp (QuadraticCubic.cutSecond_hyp (b := b)
    (k₀ := ν ^ 2 - d) (k₁ := k10) (α₂ := a20) (α₃ := a30) hν hρc0)
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) k10 a20 a30 ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  have hℓ0 : 0 ≤ ℓ := hfh.2.1
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨hD, hDl, hDc, -, hA⟩ := second_hyp (ρc := ρc) hν hw0 (by linarith)
  set L₂ := (6 * |a30| / ν + 5 * a20 ^ 2 / ν ^ 3) * (‖wstar‖ + 1) with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  set J := secondJac b d k10 a20 a30 ν wstar with hJdef
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
    simp [MatrixAlgebra.quadraticForm]
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
  set Kq := Real.sqrt (G ^ 2 * (p₂ / p₁) * Real.exp (1 / (8 * p₂) * T)) with hKq
  have hKq0 : 0 < Kq := Real.sqrt_pos.mpr (by positivity)
  set ρs := min (2 / 3 * δa) (1 / (3 * Kq)) with hρs
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
  refine ⟨ε₀, C, ρs, 3 * Kq, 1 / (16 * p₂), by positivity, hC, hρs0, by positivity,
    by positivity, ?_⟩
  intro ε hε hεε₀ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl hUc hUp
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
  obtain ⟨hbil, hbil', hWD, -, -, hbund, hTR⟩ :=
    hcore ε hε hεε₁ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl
  obtain ⟨w, hw, hwper, hw32, hwC, -⟩ :=
    horb ε hε hεε₂ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl hUc hUp
  refine ⟨w, hw, hwper, hw32, hwC, ?_⟩
  intro x hx τ hτ t hτt
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
  have hsDC : √ε * (Dc + C) ≤ δa := by
    have h5 : √ε ≤ δa / (Dc + C + 1) := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h5
    have e : √ε * (Dc + C + 1) = √ε * (Dc + C) + √ε := by ring
    linarith only [h5, e, hs0]
  -- the transformed amplitudes in real coordinates
  set X : ℝ → ℝ² := fun s => toReal (Wmap α₂ ν ε ρc (x s) s) with hX
  set Z : ℝ → ℝ² := fun s => toReal (Wmap α₂ ν ε ρc (w s) s) with hZ
  have hXZ : ∀ s, ‖X s - Z s‖ = ‖Wmap α₂ ν ε ρc (x s) s - Wmap α₂ ν ε ρc (w s) s‖ := fun s => by
    simp only [hX, hZ, ← map_sub, Saturation.norm_toReal]
  have hpt : ∀ s, ‖X s - toReal wstar‖ ≤ 1 / 2 →
      ‖Wmap α₂ ν ε ρc (x s) s - wstar‖ ≤ 1 / 2 := fun s hs => by
    simpa only [hX, ← map_sub, Saturation.norm_toReal] using hs
  have hpz : ∀ s, ‖Z s - toReal wstar‖ ≤ 1 / 2 →
      ‖Wmap α₂ ν ε ρc (w s) s - wstar‖ ≤ 1 / 2 := fun s hs => by
    simpa only [hZ, ← map_sub, Saturation.norm_toReal] using hs
  have hzb : ∀ s, ‖Z s - toReal wstar‖ ≤ r₁ * p₁ / (2 * 1 * p₂) * 1 := fun s => by
    simp only [hZ, ← map_sub, Saturation.norm_toReal]
    calc ‖Wmap α₂ ν ε ρc (w s) s - wstar‖ ≤ ‖Wmap α₂ ν ε ρc (w s) s - w s‖ + ‖w s - wstar‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ √ε * Dc + √ε * C := add_le_add (hWD _ _) (hwC s)
      _ = √ε * (Dc + C) := by ring
      _ ≤ δa := hsDC
      _ = r₁ * p₁ / (2 * 1 * p₂) * 1 := by rw [hδa]; ring
  have hstab := Averaging.exp_stable_perturbed hfh one_pos hL₂0 hD hDl hDc hA hPd hEq hp₁
    one_pos hbd hQ1 (le_refl a) hr₁0 hr₁ρ hκc hr₁κ hε hε1 hηε hεη (by positivity) hMq hεa hεq hερ
    hηκ (x := X) (z := Z)
    (qx := fun s => toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (x s) s))
    (qz := fun s => toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (w s) s))
    (fun s hxs hzs u hu => by
      have hx' := hbund x hx s (hpt s (hxs.trans hr₁h)) u hu
      have hz' := hbund w hw s (hpz s (hzs.trans hr₁h)) u hu
      refine ⟨hx'.2, hz'.2, ?_, ?_, ?_⟩
      · rw [Saturation.norm_toReal]; exact (hTR _ _ u hx'.1 hx'.1).1
      · rw [Saturation.norm_toReal]; exact (hTR _ _ u hz'.1 hz'.1).1
      · rw [← map_sub, Saturation.norm_toReal, hXZ]
        calc _ ≤ ε * √ε * Lq * ‖x u - w u‖ := (hTR _ _ u hx'.1 hz'.1).2
          _ ≤ ε * √ε * Lq * (2 * ‖Wmap α₂ ν ε ρc (x u) u - Wmap α₂ ν ε ρc (w u) u‖) :=
              mul_le_mul_of_nonneg_left (hbil _ _ u) (by positivity)
          _ = ε * √ε * (2 * Lq) * ‖Wmap α₂ ν ε ρc (x u) u - Wmap α₂ ν ε ρc (w u) u‖ := by ring)
    (fun s => by simpa using hzb s)
    (τ := τ) (by
      rw [hXZ]
      calc _ ≤ 3 / 2 * ‖x τ - w τ‖ := hbil' _ _ τ
        _ ≤ 3 / 2 * ρs := by gcongr
        _ ≤ 3 / 2 * (2 / 3 * δa) := by gcongr; exact min_le_left _ _
        _ = r₁ * p₁ / (2 * p₂) := by rw [hδa]; ring)
  -- the attraction estimate and the clamp
  have hxw : ∀ s, τ ≤ s → ‖x s - w s‖ ≤
      3 * Kq * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * ‖x τ - w τ‖ := by
    intro s hs
    have h5 := hstab s hs
    rw [hXZ, hXZ] at h5
    have h6 := hbil (x s) (w s) s
    have h7 := hbil' (x τ) (w τ) τ
    have hE : 0 ≤ Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) := (Real.exp_pos _).le
    calc ‖x s - w s‖ ≤ 2 * ‖Wmap α₂ ν ε ρc (x s) s - Wmap α₂ ν ε ρc (w s) s‖ := h6
      _ ≤ 2 * (Kq * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) *
          ‖Wmap α₂ ν ε ρc (x τ) τ - Wmap α₂ ν ε ρc (w τ) τ‖) :=
          mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ ≤ 2 * (Kq * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * (3 / 2 * ‖x τ - w τ‖)) := by
          gcongr
      _ = 3 * Kq * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * ‖x τ - w τ‖ := by ring
  have hxin : ∀ s, τ ≤ s → ‖x s‖ < ρc := by
    intro s hs
    have h5 := hxw s hs
    have hE : Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ 1 / (16 * p₂) * ε * (s - τ) := by
          have := sub_nonneg.mpr hs; positivity
        linarith)
    have h6 : ‖x s - w s‖ ≤ 1 := by
      calc ‖x s - w s‖ ≤ 3 * Kq * Real.exp (-(1 / (16 * p₂) * ε * (s - τ))) * ‖x τ - w τ‖ := h5
        _ ≤ 3 * Kq * 1 * ρs := by gcongr
        _ ≤ 3 * Kq * 1 * (1 / (3 * Kq)) := by gcongr; exact min_le_right _ _
        _ = 1 := by field_simp
    have h7 := hw32 s
    have h8 := norm_le_norm_add_norm_sub' (x s) wstar
    have h9 : ‖x s - wstar‖ ≤ ‖x s - w s‖ + ‖w s - wstar‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [hρc]; linarith
  exact ⟨hxw t hτt, hxin t hτt⟩

/-- The first time a continuous function reaches a level. -/
@[tmio T, powerlib_foundation] private theorem exists_first_hit₃ {g : ℝ → ℝ} (hg : Continuous g)
    {a t c : ℝ} (hat : a ≤ t) (ha : g a < c) (ht : c ≤ g t) :
    ∃ s ∈ Icc a t, c ≤ g s ∧ ∀ u ∈ Icc a s, g u ≤ c := by
  set S := Icc a t ∩ g ⁻¹' Ici c with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_Ici.preimage hg)
  have hSne : S.Nonempty := ⟨t, ⟨hat, le_rfl⟩, ht⟩
  have hSbdd : BddBelow S := ⟨a, fun u hu => hu.1.1⟩
  have hsS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hbefore : ∀ u ∈ Ico a (sInf S), g u < c := by
    intro u hu
    by_contra h
    push Not at h
    exact absurd (csInf_le hSbdd ⟨⟨hu.1, hu.2.le.trans hsS.1.2⟩, h⟩) (not_le.mpr hu.2)
  have has : a < sInf S := by
    rcases eq_or_lt_of_le hsS.1.1 with h | h
    · exfalso
      have : c ≤ g (sInf S) := hsS.2
      rw [← h] at this
      linarith
    · exact h
  have hle : g (sInf S) ≤ c := by
    have hcl : sInf S ∈ closure (Ico a (sInf S)) := by
      rw [closure_Ico has.ne]; exact ⟨has.le, le_rfl⟩
    exact (hg.continuousWithinAt (s := Ico a (sInf S))).closure_le hcl continuousWithinAt_const
      fun u hu => (hbefore u hu).le
  refine ⟨sInf S, hsS.1, hsS.2, fun u hu => ?_⟩
  rcases eq_or_lt_of_le hu.2 with h | h
  · rw [h]; exact hle
  · exact (hbefore u ⟨hu.1, h⟩).le

/-- The transformed amplitude is continuous along a continuous curve. -/
@[tmio T, powerlib_foundation] private theorem continuous_Wmap_comp₃ {α₂ ν ε ρc : ℝ}
    {x : ℝ → ℂ} (hx : Continuous x) : Continuous fun s => Wmap α₂ ν ε ρc (x s) s := by
  have hc : Continuous fun s => clampC ρc (x s) := (DuffingMathieu.continuous_clampC ρc).comp hx
  have hp : Continuous fun t : ℝ => phase ν t := by unfold phase; fun_prop
  have hpi : Continuous fun t : ℝ => (phase ν t)⁻¹ :=
    hp.inv₀ fun t => QuadraticCubic.phase_ne_zero ν t
  simp only [Wmap, nearId]
  fun_prop

set_option maxHeartbeats 1000000 in
/-- **The orbit of a locked state with an unstable averaged Jacobian repels clamped
solutions.** If `secondJac b d k₁⁰ α₂⁰ α₃⁰ ν w*` is invertible and has a characteristic root
`μ` with `Re μ > 0`, there are `ε₀, ρ_s > 0` and `C ≥ 0` such that for every `0 < ε ≤ ε₀`, all
coefficients and inputs within the bounds of `input_orbit`, the periodic solution `w` of the
clamped amplitude equation (`‖w − w*‖ ≤ min(3/2, √ε C)`) is unstable: for every `η > 0` a clamped
solution `x` starts within `η` of `w(0)` and reaches the distance `ρ_s` from `w` at some
`t ≥ 0`, staying inside the clamp on `[0, t]` (`Averaging.unstable_perturbed` with the Chetaev
form of the Jacobian). -/
@[tmio T, powerlib_foundation] theorem input_orbit_unstable {ν : ℝ} (hν : 0 < ν)
    {b d k10 a20 a30 : ℝ} {K1 K2 K3 A2 A3 K0 mu lu : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hK0 : 0 ≤ K0) (hmu : 0 ≤ mu) (hlu : 0 ≤ lu)
    {wstar : ℂ} (hw0 : secondAmp b d k10 a20 a30 ν wstar = 0)
    (hdet : (secondJac b d k10 a20 a30 ν wstar).det ≠ 0) {μ : ℂ}
    (hroot : (Linear.characteristicMatrix (secondJac b d k10 a20 a30 ν wstar) μ).det = 0)
    (hμ : 0 < μ.re) :
    ∃ ε₀ C ρs : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < ρs ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ (k₁ α₂ α₃ : ℝ) (U : ℂ → ℝ → ℂ),
      |k₁ - k10| ≤ ε * K1 → |α₂ ^ 2 - a20 ^ 2| ≤ ε * K2 → |α₃ - a30| ≤ ε * K3 →
      |α₂| ≤ A2 → |α₃| ≤ A3 → |k₁| ≤ K0 →
      (∀ w t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖U w t‖ ≤ ε ^ 2 * mu) →
      (∀ w w' t, ‖w‖ ≤ 2 * (‖wstar‖ + 3) → ‖w'‖ ≤ 2 * (‖wstar‖ + 3) →
        ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖) →
      Continuous (fun q : ℝ × ℂ => U q.2 q.1) → (∀ w t, U w (t + 2 * Real.pi / ν) = U w t) →
      ∃ w : ℝ → ℂ, (∀ t, HasDerivAt w (inputClamp b d k₁ α₂ α₃ ν ε (‖wstar‖ + 3) U t (w t)) t) ∧
        (∀ t, w (t + 2 * Real.pi / ν) = w t) ∧ (∀ t, ‖w t - wstar‖ ≤ 3 / 2) ∧
        (∀ t, ‖w t - wstar‖ ≤ √ε * C) ∧
        ∀ η, 0 < η → ∃ x : ℝ → ℂ,
          (∀ t, HasDerivAt x (inputClamp b d k₁ α₂ α₃ ν ε (‖wstar‖ + 3) U t (x t)) t) ∧
          ‖x 0 - w 0‖ ≤ η ∧ ∃ t, 0 ≤ t ∧ ρs ≤ ‖x t - w t‖ ∧
            ∀ s ∈ Icc 0 t, ‖x s‖ < ‖wstar‖ + 3 := by
  obtain ⟨ε₁, Mq, Lq, Dc, hε₁, hε₁1, hMq, hLq, hDc0, hcore⟩ :=
    input_core hν b d k10 a20 a30 K1 K2 K3 A2 A3 K0 mu lu hK1 hK2 hK3 hA2 hA3 hK0 hmu hlu wstar
  obtain ⟨ε₂, C, r₀o, hε₂, hC, -, horb⟩ := input_orbit hν hK1 hK2 hK3 hA2 hA3 hK0 hmu hlu hw0 hdet
  set ρc := ‖wstar‖ + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  have hfh := SubharmonicOrbit.realField_hyp (QuadraticCubic.cutSecond_hyp (b := b)
    (k₀ := ν ^ 2 - d) (k₁ := k10) (α₂ := a20) (α₃ := a30) hν hρc0)
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) k10 a20 a30 ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  have hℓ0 : 0 ≤ ℓ := hfh.2.1
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨hD, hDl, hDc, -, hA⟩ := second_hyp (ρc := ρc) hν hw0 (by linarith)
  set L₂ := (6 * |a30| / ν + 5 * a20 ^ 2 / ν ^ 3) * (‖wstar‖ + 1) with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  set J := secondJac b d k10 a20 a30 ν wstar with hJdef
  -- the Chetaev certificate
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root hroot
  obtain ⟨α, H, wv, hα, hH, -, hHw, hQ⟩ :=
    LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos J hv heig hμ
  obtain ⟨q₁, hq₁, hqlow⟩ := MatrixAlgebra.exists_pos_mul_norm_sq_le_quadraticForm _ hQ
  set ηH := ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) H‖ with hηH
  set a := ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J‖ with ha
  have hηH0 : 0 ≤ ηH := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  set κ := min 1 (q₁ / (16 * (ηH + 1))) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκq : 16 * ηH * κ ≤ q₁ := by
    have h1 : κ ≤ q₁ / (16 * (ηH + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set r₁ := min (1 / 2) (κ / (2 * (L₂ + 1))) with hr₁
  have hr₁0 : 0 < r₁ := lt_min (by norm_num) (by positivity)
  have hr₁h : r₁ ≤ 1 / 2 := min_le_left _ _
  have hr₁ρ : 2 * r₁ ≤ 1 := by linarith
  have hr₁κ : 2 * L₂ * r₁ ≤ κ := by
    have h1 : r₁ ≤ κ / (2 * (L₂ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set LS := Averaging.stroboLip ℓ (2 * Lq) L₂ M Mq T with hLS
  have hLS0 : 0 ≤ LS := by
    rw [hLS, Averaging.stroboLip]
    refine mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg (sq_nonneg T) (add_nonneg
      (mul_nonneg hL₂0 (add_nonneg hM0 hMq)) (mul_nonneg hℓ0 (by linarith)))) (mul_nonneg hT0.le
      (by linarith)))
  set σ := min (κ * T / (2 * LS + 1)) (min (r₁ / 2 / (Dc + C + 1)) (1 / (2 * (C + 1)))) with hσ
  have hσ0 : 0 < σ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set ε₀ := min (min (min ε₁ ε₂) (min (1 / (T * a + 1)) (q₁ / (4 * T * ηH * (a ^ 2 + 1) + 1))))
    (min (1 / (2 * (M + Mq) * T + 1)) (σ ^ 2)) with hε₀
  refine ⟨ε₀, C, r₁ / 3, by positivity, hC, by positivity, ?_⟩
  intro ε hε hεε₀ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl hUc hUp
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
  have hUl' : ∀ w w' t, ‖w‖ ≤ 2 * ρc → ‖w'‖ ≤ 2 * ρc → ‖U w t - U w' t‖ ≤ ε ^ 2 * lu * ‖w - w'‖ :=
    hUl
  obtain ⟨hbil, hbil', hWD, hsurj, -, hbund, hTR⟩ :=
    hcore ε hε hεε₁ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl
  obtain ⟨w, hw, hwper, hw32, hwC, -⟩ :=
    horb ε hε hεε₂ k₁ α₂ α₃ U hk₁ hα₂ hα₃ hA2' hA3' hK0' hU hUl hUc hUp
  refine ⟨w, hw, hwper, hw32, hwC, ?_⟩
  intro η hη
  -- the order conditions of the escape estimate
  have hηε : ε * √ε ≤ ε := mul_le_of_le_one_right hε.le hs1
  have hεη : ε ^ 2 ≤ ε * √ε := by rw [sq]; exact mul_le_mul_of_nonneg_left hεs hε.le
  have hεa : ε * T * a ≤ 1 := by
    have h5 : ε ≤ 1 / (T * a + 1) := hεε₀.trans ((min_le_left _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at h5
    have e : ε * (T * a + 1) = ε * T * a + ε := by ring
    linarith only [h5, e, hε]
  have hεH : 4 * (ε * T) * ηH * (a ^ 2 + 1) ≤ q₁ := by
    have h5 : ε ≤ q₁ / (4 * T * ηH * (a ^ 2 + 1) + 1) := hεε₀.trans ((min_le_left _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    rw [le_div_iff₀ (by positivity)] at h5
    have e : ε * (4 * T * ηH * (a ^ 2 + 1) + 1) = 4 * (ε * T) * ηH * (a ^ 2 + 1) + ε := by ring
    linarith only [h5, e, hε]
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
  have hsDC : √ε * (Dc + C) ≤ r₁ / 2 := by
    have h5 : √ε ≤ r₁ / 2 / (Dc + C + 1) := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h5
    have e : √ε * (Dc + C + 1) = √ε * (Dc + C) + √ε := by ring
    linarith only [h5, e, hs0]
  -- the family of transformed amplitudes from time `0`
  choose w₀ hw₀ using fun y : ℝ² => hsurj (toReal.symm y) 0
  choose xs hxs0 hxs using fun y : ℝ² =>
    exists_inputClamp_solution (b := b) (d := d) hν hε hε1 hρc0 hA2' hA3' hK0' hlu hUl' hUc 0
      (w₀ y)
  set X : ℝ² → ℝ → ℝ² := fun y s => toReal (Wmap α₂ ν ε ρc (xs y s) s) with hX
  set Z : ℝ → ℝ² := fun s => toReal (Wmap α₂ ν ε ρc (w s) s) with hZ
  have hX0 : ∀ y, X y 0 = y := fun y => by
    simp only [hX, hxs0, hw₀, ContinuousLinearEquiv.apply_symm_apply]
  have hXZ : ∀ y s, ‖X y s - Z s‖ = ‖Wmap α₂ ν ε ρc (xs y s) s - Wmap α₂ ν ε ρc (w s) s‖ :=
    fun y s => by simp only [hX, hZ, ← map_sub, Saturation.norm_toReal]
  have hZb : ∀ s, ‖Wmap α₂ ν ε ρc (w s) s - wstar‖ ≤ r₁ / 2 := fun s =>
    calc ‖Wmap α₂ ν ε ρc (w s) s - wstar‖ ≤ ‖Wmap α₂ ν ε ρc (w s) s - w s‖ + ‖w s - wstar‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ √ε * Dc + √ε * C := add_le_add (hWD _ _) (hwC s)
      _ = √ε * (Dc + C) := by ring
      _ ≤ r₁ / 2 := hsDC
  have hzb : ∀ s, ‖Z s - toReal wstar‖ ≤ r₁ / 2 := fun s => by
    simp only [hZ, ← map_sub, Saturation.norm_toReal]; exact hZb s
  obtain ⟨y, hy, t, ht, hesc⟩ := Averaging.unstable_perturbed hfh one_pos hL₂0 hD hDl hDc hA hH
    hHw hα (fun e => hqlow e) (le_refl a) (le_refl ηH) hr₁0 hr₁ρ hκ0.le hκ1 hκq hr₁κ hε hε1 hηε
    hεη (by positivity) hMq hεa hεH hερ hηκ (X := X)
    (Q := fun y s => toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (xs y s) s)) hX0 (z := Z)
    (qz := fun s => toReal (transRem b d k₁ α₂ α₃ k10 a20 a30 ν ε U (w s) s))
    (fun y s hxs' hzs u hu => by
      have hx' := hbund (xs y) (hxs y) s (by
        simpa only [hX, ← map_sub, Saturation.norm_toReal] using hxs'.trans hr₁h) u hu
      have hz' := hbund w hw s (by
        simpa only [hZ, ← map_sub, Saturation.norm_toReal] using hzs.trans hr₁h) u hu
      refine ⟨hx'.2, hz'.2, ?_, ?_, ?_⟩
      · rw [Saturation.norm_toReal]; exact (hTR _ _ u hx'.1 hx'.1).1
      · rw [Saturation.norm_toReal]; exact (hTR _ _ u hz'.1 hz'.1).1
      · rw [← map_sub, Saturation.norm_toReal, hXZ]
        calc _ ≤ ε * √ε * Lq * ‖xs y u - w u‖ := (hTR _ _ u hx'.1 hz'.1).2
          _ ≤ ε * √ε * Lq * (2 * ‖Wmap α₂ ν ε ρc (xs y u) u - Wmap α₂ ν ε ρc (w u) u‖) :=
              mul_le_mul_of_nonneg_left (hbil _ _ u) (by positivity)
          _ = ε * √ε * (2 * Lq) * ‖Wmap α₂ ν ε ρc (xs y u) u - Wmap α₂ ν ε ρc (w u) u‖ := by
              ring)
    hzb (δ := min (η / 2) (r₁ / 4)) (lt_min (by positivity) (by positivity))
  set x := xs y with hxdef
  -- the first time the transformed deviation reaches `r₁/2`
  have hg : Continuous fun s => ‖X y s - Z s‖ := by
    have hxc : Continuous x := continuous_iff_continuousAt.mpr fun s => (hxs y s).continuousAt
    have hwc : Continuous w := continuous_iff_continuousAt.mpr fun s => (hw s).continuousAt
    exact ((toReal.continuous.comp (continuous_Wmap_comp₃ hxc)).sub
      (toReal.continuous.comp (continuous_Wmap_comp₃ hwc))).norm
  have hg0 : ‖X y 0 - Z 0‖ < r₁ / 2 := by
    have : ‖X y 0 - Z 0‖ ≤ r₁ / 4 := by rw [hX0]; exact hy.trans (min_le_right _ _)
    linarith
  obtain ⟨t₁, ht₁, hhit, hbefore⟩ := exists_first_hit₃ hg ht hg0 hesc
  -- before `t₁` the clamped solution stays inside the clamp
  have hin : ∀ s ∈ Icc 0 t₁, ‖x s‖ < ρc := by
    intro s hs
    have h5 := hbefore s hs
    rw [hXZ] at h5
    have h6 : ‖Wmap α₂ ν ε ρc (x s) s - wstar‖ ≤ r₁ := by
      calc _ ≤ ‖Wmap α₂ ν ε ρc (x s) s - Wmap α₂ ν ε ρc (w s) s‖ +
            ‖Wmap α₂ ν ε ρc (w s) s - wstar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ r₁ / 2 + r₁ / 2 := add_le_add h5 (hZb s)
        _ = r₁ := by ring
    have h7 : ‖x s - Wmap α₂ ν ε ρc (x s) s‖ ≤ r₁ / 2 := by
      rw [norm_sub_rev]
      refine (hWD _ _).trans ?_
      have : √ε * Dc ≤ √ε * (Dc + C) := mul_le_mul_of_nonneg_left (by linarith) hs0.le
      linarith
    have h8 : ‖x s - wstar‖ ≤ 1 := by
      calc ‖x s - wstar‖ ≤ ‖x s - Wmap α₂ ν ε ρc (x s) s‖ +
            ‖Wmap α₂ ν ε ρc (x s) s - wstar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ r₁ / 2 + r₁ := add_le_add h7 h6
        _ ≤ 1 := by linarith
    have := norm_le_norm_add_norm_sub' (x s) wstar
    rw [hρc]; linarith
  refine ⟨x, hxs y, ?_, t₁, ht₁.1, ?_, hin⟩
  · have h5 := hbil (x 0) (w 0) 0
    rw [← hXZ, hX0] at h5
    have h6 : ‖y - Z 0‖ ≤ η / 2 := hy.trans (min_le_left _ _)
    linarith
  · have h5 := hbil' (x t₁) (w t₁) t₁
    rw [← hXZ] at h5
    linarith

/-! ## The loaded swing as an instance: uniqueness of the loaded subharmonic orbit -/

variable {p : Params}

@[tmio M, powerlib_foundation] private theorem vdp_pos_vel₃ {ν : ℝ} (hν : ν ≠ 0) (z : ℂ)
    (t : ℝ) : vdp ν t (pos ν z t) (vel ν z t) = z := by
  have h1 : (((pos ν z t : ℝ) : ℂ) - (((vel ν z t) / ν : ℝ) : ℂ) * I) =
      z * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [pos]
    · simp [vel]; field_simp
  rw [vdp, h1, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

@[tmio M, powerlib_foundation] private theorem vdp_period₃ {ν : ℝ} (hν : 0 < ν) (x x' : ℝ) :
    vdp ν (2 * Real.pi / ν) x x' = vdp ν 0 x x' := by
  have hE : Complex.exp (-(((ν * (2 * Real.pi / ν) : ℝ) : ℂ) * I)) =
      Complex.exp (-(((ν * 0 : ℝ) : ℂ) * I)) := by
    rw [show ν * (2 * Real.pi / ν) = 2 * Real.pi by field_simp, mul_zero,
      show -(((2 * Real.pi : ℝ) : ℂ) * I) = -(2 * Real.pi * I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    simp
  simp only [vdp, hE]

/-- The averaged limit field of the loaded swing and its Jacobian are `secondAmp`, `secondJac`
with pump `ν²`, quadratic stiffness `−ν² tan δ₀/2` and cubic stiffness `−ν²/6`. -/
@[tmio M, powerlib_domain] theorem loadedAmp_eq_secondAmp {b d ν δ₀ : ℝ} (hν : 0 < ν) :
    loadedAmp b d ν δ₀ = secondAmp b d (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν ∧
      loadedJac b d ν δ₀ =
        secondJac b d (ν ^ 2) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν := by
  have e2 : ν ^ 2 / (4 * ν) = ν / 4 := by field_simp
  have e3 : 3 * (-(ν ^ 2) / 6) / (8 * ν) - 5 * (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 / (12 * ν ^ 3) =
      -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) := by field_simp; ring
  refine ⟨?_, ?_⟩ <;> funext w <;> simp only [loadedAmp, loadedJac, secondAmp, secondJac, e2, e3]

/-- **The coefficients of the loaded machines of the scaling** `ω_L² = ν² − εd`
(`0 < ε ≤ 1`, `cos δ₀ > 0`) are `O(ε)`-close to the limit coefficients `ν²`, `−ν² tan δ₀/2`,
`−ν²/6` and uniformly bounded (`machine_bounds`). -/
@[tmio M, powerlib_domain] theorem loaded_coeff_bounds (hp : p.Pos) {δ₀ ν d ε : ℝ}
    (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) :
    |loadedFreqSq p δ₀ - ν ^ 2| ≤ ε * |d| ∧
      |alpha2 p δ₀ ^ 2 - (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2| ≤
        ε * (Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|)) ∧
      |alpha3 p δ₀ - -(ν ^ 2) / 6| ≤ ε * (|d| / 6) ∧
      |alpha2 p δ₀| ≤ (ν ^ 2 + |d|) * |Real.tan δ₀| / 2 ∧ |alpha3 p δ₀| ≤ (ν ^ 2 + |d|) / 6 ∧
      |loadedFreqSq p δ₀| ≤ ν ^ 2 + |d| := by
  obtain ⟨-, h2, h3, hω, hωle⟩ := machine_bounds hp hc hε hε1 hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd, show ν ^ 2 - ε * d - ν ^ 2 = -(ε * d) by ring, abs_neg, abs_mul, abs_of_pos hε]
  · rw [h2]
    have e : (-(loadedFreqSq p δ₀ * Real.tan δ₀) / 2) ^ 2 - (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 =
        ε * (Real.tan δ₀ ^ 2 / 4 * (-d) * (2 * ν ^ 2 - ε * d)) := by rw [hd]; ring
    rw [e, abs_mul, abs_of_pos hε]
    gcongr
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.tan δ₀ ^ 2 / 4)]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ν ^ 2), abs_mul, abs_of_pos hε]
    gcongr
    exact mul_le_of_le_one_left (abs_nonneg _) hε1
  · rw [h3, hd, show -(ν ^ 2 - ε * d) / 6 - -(ν ^ 2) / 6 = ε * (d / 6) by ring, abs_mul,
      abs_of_pos hε, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  · rw [h2, abs_div, abs_neg, abs_mul, abs_of_pos hω, abs_two]
    gcongr
  · rw [h3, abs_div, abs_neg, abs_of_pos hω, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    gcongr
  · rw [abs_of_pos hω]; exact hωle

/-- **The loaded remainder in van der Pol form is of order `ε²`, with an `ε²`-Lipschitz
constant**, on the disc `‖w‖ ≤ r` (`remW_bounds`). -/
@[tmio M, powerlib_domain] theorem inputW_bounds (hp : p.Pos) {δ₀ ν d ε r : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hr : 0 ≤ r) :
    (∀ w t, ‖w‖ ≤ r → ‖inputW p δ₀ ν ε w t‖ ≤ ε ^ 2 * (remConstW ν d δ₀ r * r / ν)) ∧
      ∀ w w' t, ‖w‖ ≤ r → ‖w'‖ ≤ r →
        ‖inputW p δ₀ ν ε w t - inputW p δ₀ ν ε w' t‖ ≤
          ε ^ 2 * (remConstW ν d δ₀ r / ν) * ‖w - w'‖ := by
  refine ⟨fun w t hw => ?_, fun w w' t hw hw' => ?_⟩
  · have h := (remW_bounds hp hc hε hε1 hd hr hw hw t).2
    rw [inputW, norm_neg, norm_mul, norm_mul, norm_phase_inv₃, mul_one, norm_div, Complex.norm_I,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs]
    calc 1 / ν * |remW p δ₀ ν ε w t| ≤ 1 / ν * (ε ^ 2 * (remConstW ν d δ₀ r * r)) := by gcongr
      _ = ε ^ 2 * (remConstW ν d δ₀ r * r / ν) := by ring
  · have h := (remW_bounds hp hc hε hε1 hd hr hw hw' t).1
    have e : inputW p δ₀ ν ε w t - inputW p δ₀ ν ε w' t =
        -(I / ν * ((remW p δ₀ ν ε w t - remW p δ₀ ν ε w' t : ℝ) : ℂ) * (phase ν t)⁻¹) := by
      simp only [inputW]; push_cast; ring
    rw [e, norm_neg, norm_mul, norm_mul, norm_phase_inv₃, mul_one, norm_div, Complex.norm_I,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le, Real.norm_eq_abs]
    calc 1 / ν * |remW p δ₀ ν ε w t - remW p δ₀ ν ε w' t| ≤
        1 / ν * (ε ^ 2 * remConstW ν d δ₀ r * ‖w - w'‖) := by gcongr
      _ = ε ^ 2 * (remConstW ν d δ₀ r / ν) * ‖w - w'‖ := by ring

@[tmio M, powerlib_domain] theorem continuous_inputW (p : Params) (δ₀ ν ε : ℝ) :
    Continuous fun q : ℝ × ℂ => inputW p δ₀ ν ε q.2 q.1 := by
  have hp : Continuous fun t : ℝ => phase ν t := by unfold phase; fun_prop
  have hpi : Continuous fun t : ℝ => (phase ν t)⁻¹ :=
    hp.inv₀ fun t => QuadraticCubic.phase_ne_zero ν t
  have : Continuous fun q : ℝ × ℂ => (phase ν q.1)⁻¹ := hpi.comp continuous_fst
  simp only [inputW, remW, remainder, modKs, pos]
  fun_prop

@[tmio M, powerlib_domain] theorem inputW_periodic {δ₀ ν ε : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    inputW p δ₀ ν ε w (t + 2 * Real.pi / ν) = inputW p δ₀ ν ε w t := by
  have hcos : Real.cos (2 * ν * (t + 2 * Real.pi / ν)) = Real.cos (2 * ν * t) := by
    rw [show 2 * ν * (t + 2 * Real.pi / ν) = 2 * ν * t + (2 : ℕ) * (2 * Real.pi) by
      push_cast; field_simp]
    exact Real.cos_add_nat_mul_two_pi _ 2
  simp only [inputW, remW, remainder, modKs, pos_period₃ hν, phase_period₃ hν, hcos]

/-- Global uniqueness for the loaded swing model. -/
@[tmio M, powerlib_domain] private theorem loaded_unique_univ (hp : p.Pos) {δ₀ ε Ω : ℝ}
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

/-- **The loaded subharmonic orbit is unique near its initial state.** Let `w*` be a
nondegenerate locked state of the averaged limit amplitude equation of the loaded swing
(`loadedAmp b d ν δ₀ w* = 0`, `det (loadedJac b d ν δ₀ w*) ≠ 0`, `cos δ₀ > 0`). There are
`ε₀ > 0`, `C ≥ 0` and `r₀ > 0` (depending on `b, d, ν, δ₀, w*` only) such that for every
`0 < ε ≤ ε₀` and every machine of the scaling `D/M = εb`, `ω_L² = ν² − εd` the loaded swing model
with `K_s(t) = K_s(1 + ε cos 2νt)` has a `2π/ν`-periodic solution `(δ_ε, δ̇_ε)` with
`|δ_ε(t) − δ₀ − √ε Re(w* e^{jνt})| ≤ C ε` (the orbit of `loaded_subharmonic_orbit`), whose
phase-plane point stays within `√ε r₀` of `√ε w* e^{jνt}`, and every solution `(δ, δ̇)` of the
loaded swing model that starts within `√ε r₀` of `√ε w*` in the phase-plane norm,
`‖vdp ν 0 (δ(0) − δ₀) δ̇(0) − √ε w*‖ ≤ √ε r₀`, and returns after one period,
`(δ, δ̇)(2π/ν) = (δ, δ̇)(0)`, is `(δ_ε, δ̇_ε)`: the period map has exactly one fixed point in this
ball (the uniqueness clause of `Averaging.exists_periodic_point_perturbed` through
`input_orbit`). -/
@[tmio M, powerlib_domain] theorem loaded_orbit_unique {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {wstar : ℂ} (hw0 : loadedAmp b d ν δ₀ wstar = 0)
    (hdet : (loadedJac b d ν δ₀ wstar).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      ∃ δε δε' : ℝ → ℝ, (∀ t, HasDerivAt δε (δε' t) t) ∧
        (∀ t, HasDerivAt δε' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δε t) (δε' t)) t) ∧
        (∀ t, δε (t + 2 * Real.pi / ν) = δε t ∧ δε' (t + 2 * Real.pi / ν) = δε' t) ∧
        (∀ t, |δε t - δ₀ - √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε) ∧
        (∀ t, ‖vdp ν t (δε t - δ₀) (δε' t) - ((√ε : ℝ) : ℂ) * wstar‖ ≤ √ε * r₀) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
          δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
          ‖vdp ν 0 (δ 0 - δ₀) (δ' 0) - ((√ε : ℝ) : ℂ) * wstar‖ ≤ √ε * r₀ →
          δ = δε ∧ δ' = δε' := by
  obtain ⟨hAe, hJe⟩ := loadedAmp_eq_secondAmp (b := b) (d := d) (δ₀ := δ₀) hν
  rw [hAe] at hw0
  rw [hJe] at hdet
  set ρ := 2 * (‖wstar‖ + 3) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hRC : 0 ≤ remConstW ν d δ₀ ρ := by rw [remConstW]; have := hc.le; positivity
  obtain ⟨ε₁, C, r₀, hε₁, hC, hr₀, horb⟩ := input_orbit hν (K1 := |d|)
    (K2 := Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|)) (K3 := |d| / 6)
    (A2 := (ν ^ 2 + |d|) * |Real.tan δ₀| / 2) (A3 := (ν ^ 2 + |d|) / 6) (K0 := ν ^ 2 + |d|)
    (mu := remConstW ν d δ₀ ρ * ρ / ν) (lu := remConstW ν d δ₀ ρ / ν) (abs_nonneg _)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hw0 hdet
  refine ⟨min ε₁ (min 1 ((r₀ / (C + 1)) ^ 2)), C, r₀, by positivity, hC, hr₀, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsC : √ε * C ≤ r₀ := by
    have h1 : ε ≤ (r₀ / (C + 1)) ^ 2 := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : √ε ≤ r₀ / (C + 1) := by
      calc √ε ≤ √((r₀ / (C + 1)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = r₀ / (C + 1) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ (by positivity)] at h2
    have e : √ε * (C + 1) = √ε * C + √ε := by ring
    linarith only [h2, e, hs0]
  obtain ⟨k1, k2, k3, a2, a3, k0⟩ := loaded_coeff_bounds hp hc hε hε1 hd
  obtain ⟨hU, hUl⟩ := inputW_bounds hp hν hc hε hε1 hd hρ0
  obtain ⟨w, hw, hwper, hw32, hwC, huniq⟩ := horb ε hε hεε₁ (loadedFreqSq p δ₀) (alpha2 p δ₀)
    (alpha3 p δ₀) (inputW p δ₀ ν ε) k1 k2 k3 a2 a3 k0 hU hUl (continuous_inputW p δ₀ ν ε)
    (inputW_periodic hν)
  have hwc : ∀ t, HasDerivAt w (clampField p δ₀ b d ν ε (‖wstar‖ + 3) t (w t)) t := hw
  obtain ⟨h1, h2, h3, h4⟩ := loaded_swing_of_orbit hp hν hε hb hd hwc hwper hw32 hwC
  refine ⟨_, _, h1, h2, h3, h4, fun t => ?_, ?_⟩
  · rw [add_sub_cancel_left, vdp_pos_vel₃ hν.ne', ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hs0.le]
    exact mul_le_mul_of_nonneg_left ((hwC t).trans hsC) hs0.le
  intro δ δ' hδ hδ' hTδ hTδ' h0
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  -- the clamped solution through the scaled amplitude of `(δ, δ̇)` at `0`
  obtain ⟨z, hz0, hz⟩ := exists_clamped_solution (b := b) hp hν hc hε hε1 hd
    (by positivity : (0 : ℝ) ≤ ‖wstar‖ + 3) 0 (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (δ 0 - δ₀) (δ' 0))
  have hzc : ∀ t, HasDerivAt z (inputClamp b d (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν
      ε (‖wstar‖ + 3) (inputW p δ₀ ν ε) t (z t)) t := hz
  have hz0' : ‖z 0 - wstar‖ ≤ r₀ := by
    rw [hz0]
    have e : vdp ν 0 (δ 0 - δ₀) (δ' 0) - ((√ε : ℝ) : ℂ) * wstar = ((√ε : ℝ) : ℂ) *
        (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (δ 0 - δ₀) (δ' 0) - wstar) := by field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h0
    exact le_of_mul_le_mul_left h0 hs0
  obtain ⟨hin, hzw⟩ := huniq z hzc hz0'
  -- over the first period `z` carries `(δ, δ̇)`
  have hzn : ∀ t ∈ Icc 0 T, ‖z t‖ < ‖wstar‖ + 3 := fun t ht => by
    have := norm_le_norm_add_norm_sub' (z t) wstar
    have := hin t ht
    linarith
  have hsw := fun s (hs : s ∈ Icc 0 T) => swing_of_clamped hp hν hε hb hd (hz s) (hzn s hs)
  have hz0v : ((√ε : ℝ) : ℂ) * z 0 = vdp ν 0 (δ 0 - δ₀) (δ' 0) := by
    rw [hz0]; field_simp
  have hpos0 : δ₀ + pos ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ 0 := by
    rw [hz0v, DuffingMathieu.pos_vdp]; ring
  have hvel0 : vel ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ' 0 := by
    rw [hz0v, DuffingMathieu.vel_vdp hν.ne']
  have hU' := loaded_unique_Icc hp (τ := 0) (T₁ := T) (fun s hs => (hsw s hs).1)
    (fun s hs => (hsw s hs).2) (fun s _ => hδ s) (fun s _ => hδ' s) hpos0 hvel0
  -- the scaled amplitude returns after one period
  have hzT : z T = z 0 := by
    obtain ⟨e1, e2⟩ := hU' T ⟨hT0.le, le_rfl⟩
    have h5 : ((√ε : ℝ) : ℂ) * z T = vdp ν T (δ T - δ₀) (δ' T) := by
      rw [← e1, ← e2, add_sub_cancel_left, vdp_pos_vel₃ hν.ne']
    have h7 : vdp ν T (δ T - δ₀) (δ' T) = vdp ν 0 (δ 0 - δ₀) (δ' 0) := by
      rw [hTδ, hTδ', vdp_period₃ hν]
    exact mul_left_cancel₀ hs0' (h5.trans (h7.trans hz0v.symm))
  have hzw' := hzw hzT
  -- `(δ, δ̇)` and the orbit agree at `0`, hence everywhere
  refine loaded_unique_univ hp hδ hδ' h1 h2 (t₀ := 0) ?_ ?_
  · rw [← hpos0, hzw']
  · rw [← hvel0, hzw']

end powerlib.Synchronous.LoadedSubharmonicOrbit
