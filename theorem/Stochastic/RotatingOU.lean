import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SpectralDensity
import theorem.Stochastic.LyapunovCovariance
import theorem.LTI.Oscillator2

/-! # The damped rotating oscillator under periodic forcing and white noise

The linear normal form `ż = (−γ + iω₀) z + F e^{iΩt} + σξ` of a forced oscillation, split into its
deterministic forced response and its noise part: the exact steady-state response with its
phase, the coherent input `Q` of the report's first-order reduction with its exact amplitude, and
the stationary covariance, lag covariance and spectral density of the noise part.

Scope.
* State `z = x + iy` (`x` = index `0`, `y` = index `1` of the real form), constant parameters
  `γ > 0` (damping), `ω₀` (natural angular frequency), `Ω` (forcing angular frequency), `F`
  (forcing amplitude), `σ` (noise intensity, two independent white noises of intensity `σ` on `x`
  and `y`, so the noise covariance is `σ² I`). Continuous time. Generic mathematics of a normal
  form; no power-system model is selected.
* The deterministic part is an ODE statement about `z : ℝ → ℂ`.
* The noise part is treated at covariance level (Mathlib has no Itô integral): the stationary
  covariance is the solution of the covariance Lyapunov equation `A Σ + Σ Aᵀ + σ² I = 0`
  (`Lyapunov.SolvesCovLyapunov`), the lag covariance is the deterministic moment object
  `e^{τA} Σ`, and `cov_linearStep` is the one-step covariance identity behind it (an exact step
  `X(t+τ) = e^{τA} X(t) + Z` with `Z` independent of `X(t)`). That these are the moments of the
  Itô solution is not proved here.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.1–§3.6.2,
eqs. (3-30)–(3-35) and Table 3-1 (forced-oscillation row).

Results.
* `forcedPhasor`, `forcedResp`, `forcedPhasor_eq` — `c = F/(γ + i(Ω − ω₀))` in Cartesian form.
* `forcedResp_hasDerivAt`, `eq_forcedResp_add`, `tendsto_sub_forcedResp` — `z_c(t) = c e^{iΩt}`,
  `c = F/(γ + i(Ω − ω₀))`, solves the forced equation; every solution is
  `z_c(t) + e^{(−γ+iω₀)t}(z(0) − z_c(0))`, so all solutions converge to `z_c` for `γ > 0`. The
  report's integral `∫₀ᵗ e^{(t−s)M} F[cos Ωs, sin Ωs]ᵀ ds` in (3-32) is the solution from
  `z(0) = 0`, i.e. `z_c(t) − e^{(−γ+iω₀)t} z_c(0)`: it equals the steady state only as `t → ∞`.
* `re_forcedResp`, `re_forcedResp_eq_cos` — `x_c(t) = F(γ cos Ωt + (Ω−ω₀) sin Ωt)/(γ² + (Ω−ω₀)²)
  = F cos(Ωt − ψ)/√(γ² + (Ω−ω₀)²)` with `ψ = arctan((Ω − ω₀)/γ)`.
* **Correction of (3-32)**: `report_xc_iff` — the report's `x_c = F cos(Ωt)/√(γ² + (Ω−ω₀)²)`
  (phase `ψ` omitted) holds for all `t` iff `Ω = ω₀` (`F ≠ 0`).
* (3-34)/(3-35) deterministic part: `forcedQ`, `re_forcedResp_hasDerivAt` — `ẋ_c = −γ(x_c − Q)`
  with `Q(t) = Re((1 + iΩ/γ) z_c(t))`; `forcedQCoeff`, `forcedQ_eq` — `Q(t) = |q| cos(Ωt + arg q)`,
  `q = (1 + iΩ/γ) c`; `lamForced`, `norm_forcedQ_coeff` —
  `|q| = |λ|`, `λ = (F/γ)√((γ² + Ω²)/(γ² + (Ω − ω₀)²))`, exactly the Table 3-1
  `λ` of a forced oscillation (the report's (3-34) omits the phase of `Q`, irrelevant for the
  spectral density). With `σ₁ = 0` the classifier gives `V_PS = 1` for every `λ`
  (`Periodogram.vps_forced`), so in particular for this one.
* Noise part: `rotMat` (the report's `M`), `rotMat_stationaryCov` — the covariance Lyapunov
  equation has the unique solution `Σ = σ²/(2γ) I`; `exp_rotMat` —
  `e^{τM} = e^{−γτ}(cos(ω₀τ) I + sin(ω₀τ) J)`; `lagCov_rotMat` — `(e^{τM}Σ)₀₀ = rotOUAutocov`, i.e.
  `Cov(x(t+τ), x(t)) = σ²/(2γ) e^{−γτ} cos(ω₀τ)`; `cov_linearStep` — the one-step covariance
  identity `Cov(aX + bY + Z, X) = a Var X + b Cov(Y, X)` for `Z ⟂ X`.
* **Correction of (3-33)–(3-35)**: `rotOUAutocov` (the `x`-autocovariance
  `σ²/(2γ) e^{−γ|τ|} cos(ω₀τ)`); `rotOUAutocov_zero` — the one-time variance is the scalar OU
  variance `σ²/(2γ)` (so (3-33) holds for one-time marginals); `rotOUAutocov_eq_ouAutocov_iff` —
  the autocovariances agree for all lags iff `ω₀ = 0`; `rotOUAutocov_not_ou` — for `ω₀ ≠ 0` the
  `x`-component autocovariance is not `c e^{−θ|τ|}` for any `θ, c`, so `x_ou` is not a scalar OU
  process and (3-34)/(3-35) (a scalar SDE `ẋ = −γ(x − Q) + σξ`) is an approximation.
* `spectralDensity_rotOU`, `spectralDensity_rotOU_zero` — the exact noise spectral density is the
  Lorentzian pair `(σ²/2)[1/(γ² + (ω−ω₀)²) + 1/(γ² + (ω+ω₀)²)]`; at `ω = 0` it is
  `σ²/(γ² + ω₀²)`, strictly below the value `σ²/γ²` of (3-37) with `β = γ` when `ω₀ ≠ 0`.
-/

noncomputable section
namespace powerlib.Stochastic.RotatingOU

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology Matrix.Norms.Frobenius

/-! ## Deterministic forced response -/

/-- Steady-state phasor `c = F/(γ + i(Ω − ω₀))`. -/
def forcedPhasor (γ ω₀ Ω F : ℝ) : ℂ := F / (γ + (Ω - ω₀) * Complex.I)

/-- Steady-state forced response `z_c(t) = c e^{iΩt}`. -/
def forcedResp (γ ω₀ Ω F : ℝ) (t : ℝ) : ℂ :=
  forcedPhasor γ ω₀ Ω F * Complex.exp (Ω * t * Complex.I)

@[tmio T, powerlib_foundation] private theorem den_ne_zero {γ : ℝ} (hγ : γ ≠ 0) (d : ℝ) :
    (γ : ℂ) + d * Complex.I ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; exact hγ this

@[tmio T, powerlib_foundation] private theorem hasDerivAt_cexp_mul_I (Ω t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Ω * t * Complex.I))
      (Complex.exp (Ω * t * Complex.I) * (Ω * Complex.I)) t := by
  have h : HasDerivAt (fun t : ℝ => (Ω : ℂ) * t * Complex.I) (Ω * Complex.I) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).const_mul (Ω : ℂ)).mul_const Complex.I
  exact h.cexp

/-- `z_c` solves `ż = (−γ + iω₀) z + F e^{iΩt}` (`γ ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem forcedResp_hasDerivAt {γ : ℝ} (hγ : γ ≠ 0) (ω₀ Ω F t : ℝ) :
    HasDerivAt (forcedResp γ ω₀ Ω F)
      ((-γ + ω₀ * Complex.I) * forcedResp γ ω₀ Ω F t + F * Complex.exp (Ω * t * Complex.I)) t := by
  have h := (hasDerivAt_cexp_mul_I Ω t).const_mul (forcedPhasor γ ω₀ Ω F)
  show HasDerivAt (fun y : ℝ => forcedPhasor γ ω₀ Ω F * Complex.exp (Ω * y * Complex.I)) _ t
  convert h using 1
  have hd := den_ne_zero hγ (Ω - ω₀)
  push_cast at hd
  have hkey : forcedPhasor γ ω₀ Ω F * (γ + (Ω - ω₀) * Complex.I) = F := div_mul_cancel₀ _ hd
  simp only [forcedResp]
  linear_combination (-(Complex.exp (Ω * t * Complex.I))) * hkey

/-- **Every solution is the forced response plus a decaying free mode**:
`z(t) = z_c(t) + e^{(−γ+iω₀)t} (z(0) − z_c(0))`. -/
@[tmio T, powerlib_foundation] theorem eq_forcedResp_add {γ ω₀ Ω F : ℝ} (hγ : γ ≠ 0) {z : ℝ → ℂ}
    (hz : ∀ t, HasDerivAt z ((-γ + ω₀ * Complex.I) * z t + F * Complex.exp (Ω * t * Complex.I)) t)
    (t : ℝ) :
    z t = forcedResp γ ω₀ Ω F t +
      Complex.exp ((-γ + ω₀ * Complex.I) * t) * (z 0 - forcedResp γ ω₀ Ω F 0) := by
  set a : ℂ := -γ + ω₀ * Complex.I
  set w : ℝ → ℂ := fun s => z s - forcedResp γ ω₀ Ω F s
  have hw : ∀ s, HasDerivAt w (a * w s) s := by
    intro s
    have := (hz s).sub (forcedResp_hasDerivAt hγ ω₀ Ω F s)
    convert this using 1
    simp only [w]; ring
  have hea : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-a * s)) (Complex.exp (-a * s) * -a) s :=
    fun s => by simpa using ((hasDerivAt_id s).ofReal_comp.const_mul (-a)).cexp
  set g : ℝ → ℂ := fun s => Complex.exp (-a * s) * w s
  have hg : ∀ s, HasDerivAt g 0 s := by
    intro s
    have := (hea s).mul (hw s)
    convert this using 1; ring
  have hconst : g t = g 0 :=
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  simp only [g, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hconst
  have hinv : Complex.exp (a * t) * Complex.exp (-a * t) = 1 := by
    rw [← Complex.exp_add]; simp
  have : w t = Complex.exp (a * t) * w 0 := by
    calc w t = Complex.exp (a * t) * (Complex.exp (-a * t) * w t) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = Complex.exp (a * t) * w 0 := by rw [hconst]
  simp only [w] at this
  rw [← this]; ring

/-- **The forced response attracts every solution** (`γ > 0`). -/
@[tmio T, powerlib_foundation] theorem tendsto_sub_forcedResp {γ ω₀ Ω F : ℝ} (hγ : 0 < γ)
    {z : ℝ → ℂ}
    (hz : ∀ t, HasDerivAt z ((-γ + ω₀ * Complex.I) * z t + F * Complex.exp (Ω * t * Complex.I)) t) :
    Tendsto (fun t => z t - forcedResp γ ω₀ Ω F t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have e : ∀ t, ‖z t - forcedResp γ ω₀ Ω F t‖ =
      Real.exp (-γ * t) * ‖z 0 - forcedResp γ ω₀ Ω F 0‖ := by
    intro t
    have hre : ((-(γ : ℂ) + ω₀ * Complex.I) * t).re = -γ * t := by
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
      ring
    rw [eq_forcedResp_add hγ.ne' hz t, add_sub_cancel_left, norm_mul, Complex.norm_exp, hre]
  have h : Tendsto (fun t : ℝ => Real.exp (-γ * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have h2 := h.mul_const ‖z 0 - forcedResp γ ω₀ Ω F 0‖
  rw [zero_mul] at h2
  exact h2.congr fun t => (e t).symm

@[tmio T, powerlib_foundation] theorem forcedPhasor_eq (γ ω₀ Ω F : ℝ) :
    forcedPhasor γ ω₀ Ω F = ⟨F * γ / (γ ^ 2 + (Ω - ω₀) ^ 2), -(F * (Ω - ω₀)) / (γ ^ 2 + (Ω - ω₀) ^ 2)⟩ := by
  have hden : ((γ : ℂ) + (Ω - ω₀) * Complex.I) = ⟨γ, Ω - ω₀⟩ := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [forcedPhasor, hden]
  apply Complex.ext
  · simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_mk]; ring
  · simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_mk]; ring

/-- `x_c(t) = Re z_c(t) = F (γ cos Ωt + (Ω − ω₀) sin Ωt)/(γ² + (Ω − ω₀)²)`. -/
@[tmio T, powerlib_foundation] theorem re_forcedResp (γ ω₀ Ω F t : ℝ) :
    (forcedResp γ ω₀ Ω F t).re =
      F * (γ * Real.cos (Ω * t) + (Ω - ω₀) * Real.sin (Ω * t)) / (γ ^ 2 + (Ω - ω₀) ^ 2) := by
  rw [forcedResp, forcedPhasor_eq, Complex.mul_re,
    show (Ω : ℂ) * t * Complex.I = ((Ω * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp only
  ring

/-- Amplitude–phase form: `x_c(t) = F cos(Ωt − ψ)/√(γ² + (Ω − ω₀)²)`, `ψ = arctan((Ω − ω₀)/γ)`
(`γ > 0`). -/
@[tmio T, powerlib_foundation] theorem re_forcedResp_eq_cos {γ : ℝ} (hγ : 0 < γ) (ω₀ Ω F t : ℝ) :
    (forcedResp γ ω₀ Ω F t).re = F / √(γ ^ 2 + (Ω - ω₀) ^ 2) *
      Real.cos (Ω * t - Real.arctan ((Ω - ω₀) / γ)) := by
  set d := Ω - ω₀
  have hr : 0 < γ ^ 2 + d ^ 2 := by positivity
  set r := √(γ ^ 2 + d ^ 2) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hr
  have hr2 : r ^ 2 = γ ^ 2 + d ^ 2 := Real.sq_sqrt hr.le
  have hs : √(1 + (d / γ) ^ 2) = r / γ := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    nlinarith [hr2]
  rw [re_forcedResp, Real.cos_sub, Real.cos_arctan, Real.sin_arctan, hs]
  field_simp
  rw [hr2]
  ring

/-- **Correction of (3-32).** The report's `x_c(t) = F cos(Ωt)/√(γ² + (Ω − ω₀)²)` (no phase) is
the steady-state response for every `t` iff `Ω = ω₀`. -/
@[tmio T, powerlib_foundation] theorem report_xc_iff {γ ω₀ Ω F : ℝ} (hγ : 0 < γ) (hF : F ≠ 0) :
    (∀ t, (forcedResp γ ω₀ Ω F t).re = F * Real.cos (Ω * t) / √(γ ^ 2 + (Ω - ω₀) ^ 2)) ↔
      Ω = ω₀ := by
  have hr : 0 < γ ^ 2 + (Ω - ω₀) ^ 2 := by positivity
  have hr0 : 0 < √(γ ^ 2 + (Ω - ω₀) ^ 2) := Real.sqrt_pos.mpr hr
  have hr2 : √(γ ^ 2 + (Ω - ω₀) ^ 2) ^ 2 = γ ^ 2 + (Ω - ω₀) ^ 2 := Real.sq_sqrt hr.le
  constructor
  · intro h
    have h0 := h 0
    rw [re_forcedResp] at h0
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero] at h0
    rw [div_eq_div_iff hr.ne' hr0.ne'] at h0
    have h1 : γ * √(γ ^ 2 + (Ω - ω₀) ^ 2) = γ ^ 2 + (Ω - ω₀) ^ 2 :=
      mul_left_cancel₀ hF (by linear_combination h0)
    have h2 : √(γ ^ 2 + (Ω - ω₀) ^ 2) = γ := by
      have h3 : γ * √(γ ^ 2 + (Ω - ω₀) ^ 2) =
          √(γ ^ 2 + (Ω - ω₀) ^ 2) * √(γ ^ 2 + (Ω - ω₀) ^ 2) := by
        rw [h1, ← sq, hr2]
      exact (mul_right_cancel₀ hr0.ne' h3).symm
    rw [h2] at hr2
    have h3 : (Ω - ω₀) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith
  · intro h t
    subst h
    rw [re_forcedResp, sub_self, zero_mul, add_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
      Real.sqrt_sq hγ.le]
    field_simp

/-- The coherent input of the reduction (3-34)/(3-35): `Q(t) = Re((1 + iΩ/γ) z_c(t))`. -/
def forcedQ (γ ω₀ Ω F t : ℝ) : ℝ := ((1 + Ω / γ * Complex.I) * forcedResp γ ω₀ Ω F t).re

/-- **The deterministic part of (3-34)/(3-35)**: `ẋ_c = −γ (x_c − Q)` with `Q = forcedQ`. -/
@[tmio T, powerlib_foundation] theorem re_forcedResp_hasDerivAt {γ : ℝ} (hγ : γ ≠ 0) (ω₀ Ω F t : ℝ) :
    HasDerivAt (fun t => (forcedResp γ ω₀ Ω F t).re)
      (-γ * ((forcedResp γ ω₀ Ω F t).re - forcedQ γ ω₀ Ω F t)) t := by
  have h := ((hasDerivAt_cexp_mul_I Ω t).const_mul (forcedPhasor γ ω₀ Ω F))
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  simp only [Function.comp_def, Complex.reCLM_apply] at hre
  show HasDerivAt (fun y : ℝ => (forcedPhasor γ ω₀ Ω F * Complex.exp (Ω * y * Complex.I)).re) _ t
  convert hre using 1
  rw [forcedQ, ← Complex.sub_re, ← Complex.re_ofReal_mul]
  congr 1
  simp only [forcedResp]
  have : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  field_simp
  push_cast
  ring

/-- The phasor of `Q`: `q = (1 + iΩ/γ) c`. -/
def forcedQCoeff (γ ω₀ Ω F : ℝ) : ℂ := (1 + Ω / γ * Complex.I) * forcedPhasor γ ω₀ Ω F

/-- `Q(t) = |q| cos(Ωt + arg q)`: a sinusoid of amplitude `|q|` at the forcing frequency. -/
@[tmio T, powerlib_foundation] theorem forcedQ_eq (γ ω₀ Ω F t : ℝ) :
    forcedQ γ ω₀ Ω F t = ‖forcedQCoeff γ ω₀ Ω F‖ *
      Real.cos (Ω * t + Complex.arg (forcedQCoeff γ ω₀ Ω F)) := by
  set q := forcedQCoeff γ ω₀ Ω F
  have e : (1 + Ω / γ * Complex.I) * forcedResp γ ω₀ Ω F t =
      ((‖q‖ : ℝ) : ℂ) * Complex.exp (((Ω * t + Complex.arg q : ℝ) : ℂ) * Complex.I) := by
    rw [forcedResp, ← mul_assoc]
    change q * _ = _
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I q]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [forcedQ, e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The Table 3-1 value of `λ` for a forced oscillation:
`λ = (F/γ) √((γ² + Ω²)/(γ² + (Ω − ω₀)²))`. -/
def lamForced (γ ω₀ Ω F : ℝ) : ℝ := F / γ * √((γ ^ 2 + Ω ^ 2) / (γ ^ 2 + (Ω - ω₀) ^ 2))

/-- **The amplitude of `Q` is the Table 3-1 `λ`**: `|q| = |λ|` for `γ > 0`. -/
@[tmio T, powerlib_foundation] theorem norm_forcedQ_coeff {γ : ℝ} (hγ : 0 < γ) (ω₀ Ω F : ℝ) :
    ‖forcedQCoeff γ ω₀ Ω F‖ = |lamForced γ ω₀ Ω F| := by
  have hr : 0 < γ ^ 2 + (Ω - ω₀) ^ 2 := by positivity
  have hn1 : ‖(1 : ℂ) + Ω / γ * Complex.I‖ = √(γ ^ 2 + Ω ^ 2) / γ := by
    rw [show (1 : ℂ) + Ω / γ * Complex.I = ((1 : ℝ) : ℂ) + ((Ω / γ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_add_mul_I, Real.sqrt_eq_iff_mul_self_eq (by positivity)
      (by positivity)]
    rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity)]
    field_simp
  have hn2 : ‖forcedPhasor γ ω₀ Ω F‖ = |F| / √(γ ^ 2 + (Ω - ω₀) ^ 2) := by
    rw [forcedPhasor, show (Ω : ℂ) - ω₀ = ((Ω - ω₀ : ℝ) : ℂ) by push_cast; ring, norm_div,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_add_mul_I]
  rw [forcedQCoeff, norm_mul, hn1, hn2, lamForced, abs_mul, abs_div, abs_of_pos hγ,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_div (by positivity)]
  field_simp

/-! ## Noise part: stationary covariance and lag covariance -/

/-- The drift matrix `M = [[−γ, −ω₀], [ω₀, −γ]]` of (3-31). -/
def rotMat (γ ω₀ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-γ, -ω₀; ω₀, -γ]

/-- **Stationary covariance.** For `γ ≠ 0` the covariance Lyapunov equation
`M Σ + Σ Mᵀ + σ² I = 0` has the unique solution `Σ = σ²/(2γ) I`. -/
@[tmio T, powerlib_foundation] theorem rotMat_stationaryCov {γ : ℝ} (hγ : γ ≠ 0) (ω₀ σ : ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ) :
    Lyapunov.SolvesCovLyapunov (rotMat γ ω₀) P ((σ ^ 2) • 1) ↔ P = (σ ^ 2 / (2 * γ)) • 1 := by
  have hsol : Lyapunov.SolvesCovLyapunov (rotMat γ ω₀) ((σ ^ 2 / (2 * γ)) • 1) ((σ ^ 2) • 1) := by
    unfold Lyapunov.SolvesCovLyapunov
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotMat] <;> field_simp <;> ring
  constructor
  · intro h
    refine Lyapunov.solvesCovLyapunov_unique_fin_two ?_ ?_ h hsol
    · simp [rotMat, Matrix.trace_fin_two]; exact hγ
    · have hdet : (rotMat γ ω₀).det = γ ^ 2 + ω₀ ^ 2 := by
        simp [rotMat, Matrix.det_fin_two]; ring
      have hγ2 : 0 < γ ^ 2 := by positivity
      rw [hdet]; positivity
  · rintro rfl; exact hsol

/-- **Matrix exponential of the rotating drift**: `e^{τM} = e^{−γτ}(cos(ω₀τ) I + sin(ω₀τ) J)`,
`J = [[0, −1], [1, 0]]`. -/
@[tmio T, powerlib_foundation] theorem exp_rotMat (γ ω₀ τ : ℝ) :
    NormedSpace.exp (τ • rotMat γ ω₀) =
      (Real.exp (-γ * τ) * Real.cos (ω₀ * τ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (Real.exp (-γ * τ) * Real.sin (ω₀ * τ)) • !![0, -1; 1, 0] := by
  set J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0] with hJ
  set f1 : ℝ → ℝ := fun s => Real.exp (-γ * s) * Real.cos (ω₀ * s) with hf1
  set f2 : ℝ → ℝ := fun s => Real.exp (-γ * s) * Real.sin (ω₀ * s) with hf2
  have he : ∀ s, HasDerivAt (fun s => Real.exp (-γ * s)) (Real.exp (-γ * s) * (-γ)) s := by
    intro s; simpa using ((hasDerivAt_id s).const_mul (-γ)).exp
  have hd1 : ∀ s, HasDerivAt f1 (-γ * f1 s - ω₀ * f2 s) s := by
    intro s
    have hc : HasDerivAt (fun s => Real.cos (ω₀ * s)) (-Real.sin (ω₀ * s) * ω₀) s := by
      simpa [mul_comm] using ((hasDerivAt_id s).const_mul ω₀).cos
    convert (he s).mul hc using 1
    simp only [hf1, hf2]; ring
  have hd2 : ∀ s, HasDerivAt f2 (-γ * f2 s + ω₀ * f1 s) s := by
    intro s
    have hs : HasDerivAt (fun s => Real.sin (ω₀ * s)) (Real.cos (ω₀ * s) * ω₀) s := by
      simpa [mul_comm] using ((hasDerivAt_id s).const_mul ω₀).sin
    convert (he s).mul hs using 1
    simp only [hf1, hf2]; ring
  have hA : rotMat γ ω₀ = (-γ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ω₀ • J := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, hJ]
  have hJ2 : J * J = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hJ, Matrix.mul_apply, Fin.sum_univ_two]
  have key := LTI.exp_smul_eq_of_hasDerivAt (A := rotMat γ ω₀)
    (E := fun s => f1 s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + f2 s • J)
    (by simp [hf1, hf2]) (fun s => by
      have h := ((hd1 s).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)).add ((hd2 s).smul_const J)
      convert! h using 1
      rw [hA]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJ2]
      module) τ
  rw [← key]

/-- **Lag covariance of the `x`-component**: `(e^{τM} Σ)₀₀ = σ²/(2γ) e^{−γτ} cos(ω₀τ)` for
`τ ≥ 0`, `Σ = σ²/(2γ) I`. -/
@[tmio T, powerlib_foundation] theorem lagCov_rotMat (γ ω₀ σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (NormedSpace.exp (τ • rotMat γ ω₀) * ((σ ^ 2 / (2 * γ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) 0 0 =
      OU.ouAutocov γ σ τ * Real.cos (ω₀ * τ) := by
  rw [exp_rotMat, Matrix.mul_smul, Matrix.mul_one]
  simp [OU.ouAutocov, OU.ouStatVar, abs_of_nonneg hτ]
  ring

/-- One-step covariance identity: `Cov(aX + bY + Z, X) = a Var X + b Cov(Y, X)` when `Z` is
independent of `X` (all square-integrable). With `Var X = σ²/(2γ)`, `Cov(Y, X) = 0` and
`(a, b)` the first row of `e^{τM}` it gives `lagCov_rotMat`. -/
@[tmio T, powerlib_foundation] theorem cov_linearStep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y Z : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hZ : MemLp Z 2 P) (hind : IndepFun Z X P) (a b : ℝ) :
    cov[fun ω => a * X ω + b * Y ω + Z ω, X; P] = a * Var[X; P] + b * cov[Y, X; P] := by
  have hXa : MemLp (fun ω => a * X ω) 2 P := hX.const_mul a
  have hYb : MemLp (fun ω => b * Y ω) 2 P := hY.const_mul b
  have hXY : MemLp (fun ω => a * X ω + b * Y ω) 2 P := hXa.add hYb
  have e : (fun ω => a * X ω + b * Y ω + Z ω) = (fun ω => a * X ω + b * Y ω) + Z := rfl
  rw [e, covariance_add_left hXY hZ hX, hind.covariance_eq_zero hZ hX, add_zero]
  have e2 : (fun ω => a * X ω + b * Y ω) = (fun ω => a * X ω) + fun ω => b * Y ω := rfl
  rw [e2, covariance_add_left hXa hYb hX, covariance_const_mul_left,
    covariance_const_mul_left, covariance_self hX.aemeasurable]

/-- Autocovariance of the `x`-component of the stationary rotating OU process,
`σ²/(2γ) e^{−γ|τ|} cos(ω₀τ)`. -/
def rotOUAutocov (γ ω₀ σ τ : ℝ) : ℝ := OU.ouAutocov γ σ τ * Real.cos (ω₀ * τ)

/-- One-time marginals: `Var x = σ²/(2γ)`, the variance of the report's scalar `x_ou` (3-33). -/
@[tmio T, powerlib_foundation] theorem rotOUAutocov_zero (γ ω₀ σ : ℝ) :
    rotOUAutocov γ ω₀ σ 0 = OU.ouAutocov γ σ 0 := by
  simp [rotOUAutocov]

/-- **(3-33) as processes**: the `x`-autocovariance equals the scalar OU autocovariance at all
lags iff `ω₀ = 0` (`σ ≠ 0`, `γ ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem rotOUAutocov_eq_ouAutocov_iff {γ σ : ℝ} (hγ : γ ≠ 0)
    (hσ : σ ≠ 0) (ω₀ : ℝ) :
    (∀ τ, rotOUAutocov γ ω₀ σ τ = OU.ouAutocov γ σ τ) ↔ ω₀ = 0 := by
  constructor
  · intro h
    by_contra hω
    have h1 := h (Real.pi / ω₀)
    rw [rotOUAutocov, show ω₀ * (Real.pi / ω₀) = Real.pi by field_simp, Real.cos_pi] at h1
    have hpos : OU.ouAutocov γ σ (Real.pi / ω₀) ≠ 0 := by
      unfold OU.ouAutocov OU.ouStatVar
      have : σ ^ 2 / (2 * γ) ≠ 0 := div_ne_zero (pow_ne_zero 2 hσ) (mul_ne_zero two_ne_zero hγ)
      exact mul_ne_zero (Real.exp_pos _).ne' this
    exact hpos (by linarith)
  · rintro rfl τ; simp [rotOUAutocov]

/-- **(3-34)/(3-35) is an approximation**: for `ω₀ ≠ 0` the `x`-component autocovariance is not
of the form `c e^{−θ|τ|}` (the autocovariance of a stationary scalar OU process) for any `θ, c`. -/
@[tmio T, powerlib_foundation] theorem rotOUAutocov_not_ou {γ σ ω₀ : ℝ} (hγ : γ ≠ 0) (hσ : σ ≠ 0)
    (hω : ω₀ ≠ 0) : ¬ ∃ θ c : ℝ, ∀ τ, rotOUAutocov γ ω₀ σ τ = c * Real.exp (-θ * |τ|) := by
  rintro ⟨θ, c, h⟩
  have h1 := h (Real.pi / 2 / ω₀)
  rw [rotOUAutocov, show ω₀ * (Real.pi / 2 / ω₀) = Real.pi / 2 by field_simp, Real.cos_pi_div_two,
    mul_zero] at h1
  have hc : c = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h (Real.exp_pos _).ne'
  have h0 := h 0
  simp [rotOUAutocov, OU.ouAutocov, OU.ouStatVar, hc] at h0
  rcases h0 with h0 | h0
  · exact hσ h0
  · exact hγ h0

/-- **Exact noise spectral density**: the Lorentzian pair
`(σ²/2)[1/(γ² + (ω−ω₀)²) + 1/(γ² + (ω+ω₀)²)]` (`γ > 0`). -/
@[tmio T, powerlib_foundation] theorem spectralDensity_rotOU {γ : ℝ} (hγ : 0 < γ) (ω₀ σ ω : ℝ) :
    Periodogram.spectralDensity (rotOUAutocov γ ω₀ σ) ω =
      ((σ ^ 2 / 2 * (1 / (γ ^ 2 + (ω - ω₀) ^ 2) + 1 / (γ ^ 2 + (ω + ω₀) ^ 2)) : ℝ) : ℂ) := by
  have e : rotOUAutocov γ ω₀ σ = fun τ => OU.ouStatVar γ σ *
      (Real.exp (-γ * |τ|) * Real.cos (ω₀ * τ)) := by
    funext τ; simp only [rotOUAutocov, OU.ouAutocov]; ring
  rw [e, Periodogram.spectralDensity_const_mul, Periodogram.spectralDensity_dampedCos hγ,
    ← Complex.ofReal_mul]
  congr 1
  have h1 : γ ^ 2 + (ω - ω₀) ^ 2 ≠ 0 := by positivity
  have h2 : γ ^ 2 + (ω + ω₀) ^ 2 ≠ 0 := by positivity
  unfold OU.ouStatVar
  field_simp

/-- At zero frequency the exact noise density is `σ²/(γ² + ω₀²)`, strictly below the value
`σ²/γ²` that (3-37) assigns with `β = γ`, `σ₂ = σ`, whenever `σ ≠ 0` and `ω₀ ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_rotOU_zero {γ : ℝ} (hγ : 0 < γ) (ω₀ σ : ℝ) :
    Periodogram.spectralDensity (rotOUAutocov γ ω₀ σ) 0 = ((σ ^ 2 / (γ ^ 2 + ω₀ ^ 2) : ℝ) : ℂ) ∧
      (σ ≠ 0 → ω₀ ≠ 0 → σ ^ 2 / (γ ^ 2 + ω₀ ^ 2) < σ ^ 2 / γ ^ 2) := by
  refine ⟨?_, fun hσ hω => ?_⟩
  · rw [spectralDensity_rotOU hγ]
    congr 1
    have h1 : γ ^ 2 + ω₀ ^ 2 ≠ 0 := by positivity
    rw [zero_sub, zero_add, neg_sq]
    field_simp
    ring
  · exact div_lt_div_of_pos_left (by positivity) (by positivity) (by
      have := pow_pos (abs_pos.mpr hω) 2; rw [sq_abs] at this; linarith)

end powerlib.Stochastic.RotatingOU
