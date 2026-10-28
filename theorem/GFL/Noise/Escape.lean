import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Integral.Prod

/-! # Escape analysis of the reduced 2D GFL–PLL model: algebraic and calculus facts

Model boundary.
Same 2D slow model as `theorem/GFL/Noise/Embedding.lean`: state
`(θ_e, η)`, drift `(K_p h(θ_e) + K_i η, h(θ_e))`, `h : ℝ → ℝ` the reduced phase-detector
characteristic (assumed differentiable where stated), `𝒱' = −h`.  Only the frequency noise channel
`(−ε, 0)ᵀ` is used for the stationary density.  Continuous time.  Foundation results (Rules §3):
* the trajectory statement is about the deterministic ODE;
* the stationary statement is that `e^{−𝓗/T}` solves the stationary Fokker–Planck **equation**
  pointwise (a PDE identity); that it is the law of the SDE solution is not claimed;
* the Langer statement is an eigenvalue computation of the saddle Jacobian;
* the truncated-mean statement is a calculus identity for the exponential density.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/escape-quasipotential.md`
§0 (Lyapunov erratum: `𝓗 = ½ K_i η² + 𝒱`, `𝒱 = −∫h`, `𝓗̇ = −K_p h²`; the old pairing
`𝒱 = −K_i ∫h` fails), §2 (frequency channel: `B Bᵀ = 2 T_eff R`, `ρ∞ = e^{−𝓗/T_eff}`),
§5b–§5c (Langer factor `λ_b/ω_b = √(1 + ζ_b²) + ζ_b`, saddle Jacobian), §5b (right-truncated
exponential mean `E[X | X < T] = μ − T e^{−T/μ}/(1 − e^{−T/μ})`).

Results.
* `H_hasDerivAt_along`: along a trajectory, `𝓗 = ½ K_i η² + 𝒱(θ)` decreases at rate `K_p h²`
  (§0); `Hold_hasDerivAt_along`, `Hold_deriv_pos_somewhere`: the old pairing (Corrections).
* `fpFreq_gibbs` (with `gibbs2_hasDerivAt_θ`, `gibbs2_hasDerivAt_η`): if `ε² = 2 K_p T`
  (`B Bᵀ = 2 T R`, `T = T_eff`), then `e^{−𝓗/T}` solves the stationary Fokker–Planck equation
  pointwise; `gibbs2_not_integrable`: it is not normalizable in general (Corrections).
* `saddleJac_partials`, `saddleJac_det_sub`, `saddleJac_eigen`, `saddle_stable_eigen_neg`,
  `langer_factor`, `langer_factor_gt_one`, `langer_factor_mul_textbook`: the saddle Jacobian, its
  eigenvalues and the Langer factor `λ_b/ω_b = √(1 + ζ_b²) + ζ_b`.
* `truncExp_mean`, `truncExp_mean_lt`: `E[X | X < T] = μ − T e^{−T/μ}/(1 − e^{−T/μ}) < μ` for
  the exponential density with mean `μ`.

Corrections.
* (§0, recorded in the note) The old pairing `𝓗_old = ½ K_i η² − K_i ∫h` does **not** satisfy
  `𝓗̇_old = −K_p K_i h²`: along trajectories `𝓗̇_old = −K_p K_i h² + K_i (1 − K_i) η h`
  (`Hold_hasDerivAt_along`), which is positive at some states whenever `K_i ∉ {0, 1}`
  (`Hold_deriv_pos_somewhere`).
* (§2) `e^{−𝓗/T}` is a pointwise stationary solution, but it is **not normalizable** on the
  whole plane as soon as `𝒱` stays bounded above on a set of infinite length (periodic or tilted
  washboard potentials) (`gibbs2_not_integrable`); a probability density needs a bounded domain
  or a confining potential.
* (§5b–§5c) In this pH structure the dissipation sits on the position-like coordinate, so the
  Langer factor is `√(1 + ζ_b²) + ζ_b > 1`, the reciprocal of the textbook (momentum-damping)
  value `√(1 + ζ_b²) − ζ_b < 1` (`langer_factor_mul_textbook`).
-/

noncomputable section
namespace powerlib.GFL.Noise.Escape

open Real MeasureTheory Set Matrix
open scoped ENNReal

/-! ## Lyapunov pairing along trajectories (§0) -/

/-- Along a trajectory of `θ̇ = K_p h(θ) + K_i η`, `η̇ = h(θ)`, the corrected energy
`𝓗 = ½ K_i η² + 𝒱(θ)` (`𝒱' = −h`) decreases at rate `K_p h²`. -/
@[tmio T, powerlib_foundation] theorem H_hasDerivAt_along {Kp Ki : ℝ} {h V : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (-h x) x) {θ η : ℝ → ℝ} {t : ℝ}
    (hθ : HasDerivAt θ (Kp * h (θ t) + Ki * η t) t) (hη : HasDerivAt η (h (θ t)) t) :
    HasDerivAt (fun s => Ki / 2 * η s ^ 2 + V (θ s)) (-(Kp * h (θ t) ^ 2)) t := by
  have h1 := (hη.pow 2).const_mul (Ki / 2)
  have h2 := (hV (θ t)).comp t hθ
  convert! h1.add h2 using 1
  push_cast
  ring

/-- The old pairing `𝓗_old = ½ K_i η² + K_i 𝒱(θ)`: along trajectories
`𝓗̇_old = −K_p K_i h² + K_i (1 − K_i) η h`. -/
@[powerlib_foundation] theorem Hold_hasDerivAt_along {Kp Ki : ℝ} {h V : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (-h x) x) {θ η : ℝ → ℝ} {t : ℝ}
    (hθ : HasDerivAt θ (Kp * h (θ t) + Ki * η t) t) (hη : HasDerivAt η (h (θ t)) t) :
    HasDerivAt (fun s => Ki / 2 * η s ^ 2 + Ki * V (θ s))
      (-(Kp * Ki * h (θ t) ^ 2) + Ki * (1 - Ki) * η t * h (θ t)) t := by
  have h1 := (hη.pow 2).const_mul (Ki / 2)
  have h2 := ((hV (θ t)).comp t hθ).const_mul Ki
  convert! h1.add h2 using 1
  push_cast
  ring

/-- **Erratum witness**: for `K_i > 0`, `K_i ≠ 1` the old energy increases at some state
(`h = 1`, `η = (K_p + 1)/(1 − K_i)`), so it is not a Lyapunov function. -/
@[powerlib_foundation] theorem Hold_deriv_pos_somewhere {Kp Ki : ℝ} (hKi : 0 < Ki) (hKi1 : Ki ≠ 1) :
    ∃ hθ η : ℝ, 0 < -(Kp * Ki * hθ ^ 2) + Ki * (1 - Ki) * η * hθ := by
  refine ⟨1, (Kp + 1) / (1 - Ki), ?_⟩
  have h1 : (1 - Ki) ≠ 0 := sub_ne_zero.mpr (Ne.symm hKi1)
  have : -(Kp * Ki * 1 ^ 2) + Ki * (1 - Ki) * ((Kp + 1) / (1 - Ki)) * 1 = Ki := by
    field_simp; ring
  rw [this]; exact hKi

/-! ## Stationary Fokker–Planck equation, frequency channel (§2) -/

/-- Partial derivative in `θ` of a function of `(θ, η)`. -/
def dθ (F : ℝ → ℝ → ℝ) (θ η : ℝ) : ℝ := deriv (fun x => F x η) θ

/-- Partial derivative in `η`. -/
def dη (F : ℝ → ℝ → ℝ) (θ η : ℝ) : ℝ := deriv (fun y => F θ y) η

/-- Stationary Fokker–Planck operator `L*ρ = −∂_θ(f₁ρ) − ∂_η(f₂ρ) + ½ ε² ∂²_θ ρ` of the 2D slow
model with the frequency channel `(−ε, 0)ᵀ` (diffusion matrix `diag(ε², 0)`). -/
def fpFreq (Kp Ki ε : ℝ) (h : ℝ → ℝ) (ρ : ℝ → ℝ → ℝ) (θ η : ℝ) : ℝ :=
  -dθ (fun x y => (Kp * h x + Ki * y) * ρ x y) θ η - dη (fun x y => h x * ρ x y) θ η +
    ε ^ 2 / 2 * dθ (dθ ρ) θ η

/-- Gibbs function `e^{−𝓗/T}`, `𝓗 = 𝒱(θ) + ½ K_i η²`. -/
def gibbs2 (V : ℝ → ℝ) (Ki T θ η : ℝ) : ℝ := exp (-(V θ + Ki / 2 * η ^ 2) / T)

@[powerlib_foundation] theorem gibbs2_hasDerivAt_θ {V h : ℝ → ℝ} (hV : ∀ x, HasDerivAt V (-h x) x)
    (Ki T η x : ℝ) :
    HasDerivAt (fun x => gibbs2 V Ki T x η) (h x / T * gibbs2 V Ki T x η) x := by
  have hq : HasDerivAt (fun x => -(V x + Ki / 2 * η ^ 2) / T) (h x / T) x := by
    have := ((hV x).add_const (Ki / 2 * η ^ 2)).neg.div_const T
    convert! this using 1; rw [neg_neg]
  have := hq.exp
  unfold gibbs2
  convert! this using 1
  ring

@[powerlib_foundation] theorem gibbs2_hasDerivAt_η (V : ℝ → ℝ) (Ki T θ y : ℝ) :
    HasDerivAt (fun y => gibbs2 V Ki T θ y) (-(Ki * y) / T * gibbs2 V Ki T θ y) y := by
  have hq : HasDerivAt (fun y : ℝ => V θ + Ki / 2 * y ^ 2) (Ki * y) y := by
    have := ((hasDerivAt_pow 2 y).const_mul (Ki / 2)).const_add (V θ)
    convert! this using 1; push_cast; ring
  have hq' : HasDerivAt (fun y => -(V θ + Ki / 2 * y ^ 2) / T) (-(Ki * y) / T) y := by
    have := hq.neg.div_const T
    convert! this using 1
  have := hq'.exp
  unfold gibbs2
  convert! this using 1
  ring

/-- **Frequency-channel Gibbs law (§2)**: if `ε² = 2 K_p T` (i.e. `B Bᵀ = 2 T R`,
`T = T_eff`), then `e^{−𝓗/T}` solves the stationary Fokker–Planck equation pointwise, for any
damping and any `C¹` characteristic `h`. -/
@[powerlib_foundation] theorem fpFreq_gibbs {Kp Ki ε T : ℝ} {h h' V : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (-h x) x) (hh : ∀ x, HasDerivAt h (h' x) x) (hT : T ≠ 0)
    (hε : ε ^ 2 = 2 * Kp * T) (θ η : ℝ) :
    fpFreq Kp Ki ε h (gibbs2 V Ki T) θ η = 0 := by
  set ρ := gibbs2 V Ki T with hρ
  have hdθρ : dθ ρ = fun x y => h x / T * ρ x y := by
    funext x y; exact (gibbs2_hasDerivAt_θ hV Ki T y x).deriv
  have e1 : dθ (fun x y => (Kp * h x + Ki * y) * ρ x y) θ η =
      Kp * h' θ * ρ θ η + (Kp * h θ + Ki * η) * (h θ / T * ρ θ η) := by
    have := (((hh θ).const_mul Kp).add_const (Ki * η)).mul (gibbs2_hasDerivAt_θ hV Ki T η θ)
    exact this.deriv
  have e2 : dη (fun x y => h x * ρ x y) θ η = h θ * (-(Ki * η) / T * ρ θ η) := by
    have := (gibbs2_hasDerivAt_η V Ki T θ η).const_mul (h θ)
    exact this.deriv
  have e3 : dθ (dθ ρ) θ η = h' θ / T * ρ θ η + h θ / T * (h θ / T * ρ θ η) := by
    rw [hdθρ]
    have := ((hh θ).div_const T).mul (gibbs2_hasDerivAt_θ hV Ki T η θ)
    exact this.deriv
  unfold fpFreq
  rw [e1, e2, e3, hε]
  field_simp
  ring

/-- **Not normalizable**: if `𝒱 ≤ C` on a measurable set of infinite length, `e^{−𝓗/T}` is not
integrable on the plane. -/
@[powerlib_foundation] theorem gibbs2_not_integrable {V : ℝ → ℝ} {Ki T C : ℝ} (hT : 0 < T)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : volume S = ∞) (hVS : ∀ x ∈ S, V x ≤ C) :
    ¬ Integrable (fun p : ℝ × ℝ => gibbs2 V Ki T p.1 p.2) (volume.prod volume) := by
  intro hint
  obtain ⟨y, hy⟩ := hint.prod_left_ae.exists
  set c := exp (-(C + Ki / 2 * y ^ 2) / T) with hc
  have hcpos : 0 < c := exp_pos _
  have hle : ∀ x, S.indicator (fun _ => ENNReal.ofReal c) x ≤ ‖gibbs2 V Ki T x y‖ₑ := by
    intro x
    by_cases hx : x ∈ S
    · have hg : 0 ≤ gibbs2 V Ki T x y := (exp_pos _).le
      rw [indicator_of_mem hx, Real.enorm_eq_ofReal hg]
      apply ENNReal.ofReal_le_ofReal
      unfold gibbs2
      apply exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hT.le
      linarith [hVS x hx]
    · rw [indicator_of_notMem hx]; positivity
  have hlt := hy.hasFiniteIntegral
  unfold HasFiniteIntegral at hlt
  have hge : ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal c) x ≤ ∫⁻ x, ‖gibbs2 V Ki T x y‖ₑ :=
    lintegral_mono hle
  rw [lintegral_indicator_const hSm, hS, ENNReal.mul_top (by simpa using hcpos)] at hge
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)

/-! ## Langer factor at the saddle (§5b–§5c) -/

/-- Saddle Jacobian of the drift `(K_p h + K_i η, h)` at `(θ_s, 0)` with `h(θ_s) = 0`,
`h'(θ_s) = c` (`c > 0` on the saddle side, `𝒱''(θ_s) = −c`). -/
def saddleJac (Kp Ki c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Kp * c, Ki; c, 0]

/-- The entries of `saddleJac` are the partial derivatives of the drift field. -/
@[powerlib_foundation] theorem saddleJac_partials {Kp Ki c θs η : ℝ} {h : ℝ → ℝ}
    (hh : HasDerivAt h c θs) :
    HasDerivAt (fun θ => Kp * h θ + Ki * η) (saddleJac Kp Ki c 0 0) θs ∧
      HasDerivAt (fun y => Kp * h θs + Ki * y) (saddleJac Kp Ki c 0 1) η ∧
      HasDerivAt h (saddleJac Kp Ki c 1 0) θs ∧
      HasDerivAt (fun _ : ℝ => h θs) (saddleJac Kp Ki c 1 1) η := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [saddleJac] using (hh.const_mul Kp).add_const (Ki * η)
  · simpa [saddleJac] using ((hasDerivAt_id η).const_mul Ki).const_add (Kp * h θs)
  · simpa [saddleJac] using hh
  · simpa [saddleJac] using hasDerivAt_const η (h θs)

/-- Undamped barrier frequency `ω_b = √(K_i c)`. -/
def omegaB (Ki c : ℝ) : ℝ := √(Ki * c)

/-- Barrier damping ratio `ζ_b = (K_p/2) √(c/K_i)`. -/
def zetaB (Kp Ki c : ℝ) : ℝ := Kp / 2 * √(c / Ki)

/-- Unstable eigenvalue `λ_b = K_p c/2 + √(K_p² c²/4 + K_i c)`. -/
def lambdaB (Kp Ki c : ℝ) : ℝ := Kp * c / 2 + √(Kp ^ 2 * c ^ 2 / 4 + Ki * c)

/-- Characteristic polynomial of the saddle Jacobian: `λ² − K_p c λ − K_i c`. -/
@[powerlib_foundation] theorem saddleJac_det_sub (Kp Ki c l : ℝ) :
    (l • (1 : Matrix (Fin 2) (Fin 2) ℝ) - saddleJac Kp Ki c).det = l ^ 2 - Kp * c * l - Ki * c := by
  rw [Matrix.det_fin_two]
  simp [saddleJac]
  ring

/-- `λ_b` is an eigenvalue of the saddle Jacobian with eigenvector `(λ_b, c)`. -/
@[powerlib_foundation] theorem saddleJac_eigen {Kp Ki c : ℝ} (hKi : 0 ≤ Ki) (hc : 0 ≤ c) :
    saddleJac Kp Ki c *ᵥ ![lambdaB Kp Ki c, c] = lambdaB Kp Ki c • ![lambdaB Kp Ki c, c] := by
  have hs : 0 ≤ Kp ^ 2 * c ^ 2 / 4 + Ki * c := by positivity
  have hsq := Real.sq_sqrt hs
  ext i; fin_cases i <;>
    simp [saddleJac, lambdaB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> nlinarith [hsq]

/-- The other eigenvalue `K_p c/2 − √(K_p² c²/4 + K_i c)` is negative (`K_i, c > 0`): the
equilibrium is a saddle. -/
@[powerlib_foundation] theorem saddle_stable_eigen_neg {Kp Ki c : ℝ} (hKi : 0 < Ki) (hc : 0 < c) :
    Kp * c / 2 - √(Kp ^ 2 * c ^ 2 / 4 + Ki * c) < 0 := by
  have h1 : √(Kp ^ 2 * c ^ 2 / 4) < √(Kp ^ 2 * c ^ 2 / 4 + Ki * c) :=
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith [mul_pos hKi hc])
  have h2 : √(Kp ^ 2 * c ^ 2 / 4) = |Kp * c / 2| := by
    rw [← Real.sqrt_sq_eq_abs]; congr 1; ring
  rw [h2] at h1
  linarith [le_abs_self (Kp * c / 2)]

/-- **Langer factor (§5b boxed)**: `λ_b / ω_b = √(1 + ζ_b²) + ζ_b`. -/
@[powerlib_foundation] theorem langer_factor {Kp Ki c : ℝ} (hKi : 0 < Ki) (hc : 0 < c) :
    lambdaB Kp Ki c / omegaB Ki c = √(1 + zetaB Kp Ki c ^ 2) + zetaB Kp Ki c := by
  have hω : 0 < omegaB Ki c := Real.sqrt_pos.mpr (mul_pos hKi hc)
  rw [div_eq_iff hω.ne']
  have hωζ : zetaB Kp Ki c * omegaB Ki c = Kp * c / 2 := by
    unfold zetaB omegaB
    rw [mul_assoc, ← Real.sqrt_mul (div_pos hc hKi).le]
    rw [show c / Ki * (Ki * c) = c ^ 2 by field_simp, Real.sqrt_sq hc.le]
    ring
  have hsq : √(1 + zetaB Kp Ki c ^ 2) * omegaB Ki c = √(Kp ^ 2 * c ^ 2 / 4 + Ki * c) := by
    unfold omegaB
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    unfold zetaB
    rw [mul_pow, Real.sq_sqrt (div_pos hc hKi).le]
    field_simp
    ring
  rw [add_mul, hsq, hωζ, lambdaB]
  ring

/-- With `K_p > 0` the factor exceeds one: escape is **accelerated** relative to the undamped
barrier frequency. -/
@[powerlib_foundation] theorem langer_factor_gt_one {Kp Ki c : ℝ} (hKp : 0 < Kp) (hKi : 0 < Ki)
    (hc : 0 < c) : 1 < √(1 + zetaB Kp Ki c ^ 2) + zetaB Kp Ki c := by
  have hz : 0 < zetaB Kp Ki c := by
    unfold zetaB; exact mul_pos (by positivity) (Real.sqrt_pos.mpr (div_pos hc hKi))
  have : 1 ≤ √(1 + zetaB Kp Ki c ^ 2) := Real.one_le_sqrt.mpr (by nlinarith)
  linarith

/-- **Correction (sign of the Langer factor)**: the pH value is the reciprocal of the textbook
momentum-damping value `√(1 + ζ²) − ζ`. -/
@[powerlib_foundation] theorem langer_factor_mul_textbook (ζ : ℝ) :
    (√(1 + ζ ^ 2) + ζ) * (√(1 + ζ ^ 2) - ζ) = 1 := by
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + ζ ^ 2 by positivity)
  nlinarith

/-! ## Right-truncated exponential mean (§5b) -/

/-- **Truncated exponential mean**: for the exponential density with mean `μ`,
`E[X | X < T] = (∫₀ᵀ x e^{−x/μ} dx)/(∫₀ᵀ e^{−x/μ} dx) = μ − T e^{−T/μ}/(1 − e^{−T/μ})`
(the normalizing `1/μ` of the density cancels). -/
@[powerlib_foundation] theorem truncExp_mean {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T) :
    (∫ x in (0 : ℝ)..T, x * exp (-x / μ)) / (∫ x in (0 : ℝ)..T, exp (-x / μ)) =
      μ - T * exp (-T / μ) / (1 - exp (-T / μ)) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => exp (-x / μ)) (exp (-x / μ) * (-1 / μ)) x := by
    intro x
    have := ((hasDerivAt_id' x).neg.div_const μ).exp
    convert! this using 1
  have h1 : ∀ x ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun x => -μ * (x + μ) * exp (-x / μ)) (x * exp (-x / μ)) x := by
    intro x _
    have := (((hasDerivAt_id' x).add_const μ).const_mul (-μ)).mul (hd x)
    convert! this using 1
    field_simp
    ring
  have h2 : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt (fun x => -μ * exp (-x / μ)) (exp (-x / μ)) x := by
    intro x _
    have := (hd x).const_mul (-μ)
    convert! this using 1
    field_simp
  have hi1 : IntervalIntegrable (fun x => x * exp (-x / μ)) volume 0 T := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun x => exp (-x / μ)) volume 0 T := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h1 hi1,
    intervalIntegral.integral_eq_sub_of_hasDerivAt h2 hi2]
  have hE : exp (-T / μ) < 1 := by
    rw [Real.exp_lt_one_iff]; exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hT) hμ
  have hE' : 1 - exp (-T / μ) ≠ 0 := by linarith
  have hden : -μ * exp (-T / μ) - -μ * exp (-(0 : ℝ) / μ) = μ * (1 - exp (-T / μ)) := by
    rw [neg_zero, zero_div, exp_zero]; ring
  have hnum : -μ * (T + μ) * exp (-T / μ) - -μ * (0 + μ) * exp (-(0 : ℝ) / μ) =
      μ * (μ * (1 - exp (-T / μ)) - T * exp (-T / μ)) := by
    rw [neg_zero, zero_div, exp_zero]; ring
  rw [hden, hnum, mul_div_mul_left _ _ hμ.ne', sub_div, mul_div_cancel_right₀ _ hE']

/-- The truncation biases the mean downwards: `E[X | X < T] < μ`. -/
@[powerlib_foundation] theorem truncExp_mean_lt {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T) :
    μ - T * exp (-T / μ) / (1 - exp (-T / μ)) < μ := by
  have hE : exp (-T / μ) < 1 := by
    rw [Real.exp_lt_one_iff]; exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hT) hμ
  have : 0 < T * exp (-T / μ) / (1 - exp (-T / μ)) :=
    div_pos (mul_pos hT (exp_pos _)) (by linarith)
  linarith

end powerlib.GFL.Noise.Escape
