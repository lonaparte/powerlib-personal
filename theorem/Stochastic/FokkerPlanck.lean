import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # One-dimensional Fokker–Planck operator: adjointness, probability flux, stationary solutions

Source: work-sync `theory/T-fokker-planck.md` §1.1 (`L* p = −∇·(μ p) + ½ ∂ᵢ∂ⱼ[(ΣΣᵀ)ᵢⱼ p]` obtained
by integrating by parts against test functions), §1.3 (probability flux
`J = μ p − ½ ∇·(ΣΣᵀ p)`), §1.4 (one-dimensional zero-flux stationary density
`p∞ = (C/D) exp(∫ μ/D)` and the Gibbs form `p∞ ∝ exp(−V/D)` for `μ = −V'`, `D` constant).

Scope (Rules §3).  These are statements about the **differential operators** on `ℝ`:
`L φ = μ φ' + ½ a φ''` (generator expression, `a = σ²` the diffusion coefficient) and
`L* p = −(μ p)' + ½ (a p)''`.  We prove that `L*` is the formal adjoint of `L` against compactly
supported `C²` test functions, that `L* p = −J'`, and that the zero-flux / Gibbs densities are
stationary solutions of `L* p = 0`.  That `L*` governs the density of an Itô diffusion (Itô's
formula) is **not** formalized.  Foundation results only.

Correction / missing hypothesis (§1.4).  `exp(−V/D)` solves `L* p = 0` pointwise for every `V`,
but it is a stationary **probability density** only after normalization, which needs
`Z = ∫ exp(−V/D) < ∞` (`gibbs_normalized`); for a periodic or tilted-washboard potential on `ℝ`
`Z = ∞` and there is no normalizable stationary density on the line.
-/

noncomputable section
namespace powerlib.Stochastic.FP

open MeasureTheory Real

/-- Generator expression `L φ = μ φ' + ½ a φ''` (one dimension, `a = σ²`). -/
def gen1 (μ a φ : ℝ → ℝ) (x : ℝ) : ℝ := μ x * deriv φ x + a x / 2 * deriv (deriv φ) x

/-- Forward (Fokker–Planck) operator `L* p = −(μ p)' + ½ (a p)''`. -/
def fp1 (μ a p : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (fun y => μ y * p y) x + 1 / 2 * deriv (deriv (fun y => a y * p y)) x

/-- Probability flux `J = μ p − ½ (a p)'`. -/
def flux1 (μ a p : ℝ → ℝ) (x : ℝ) : ℝ := μ x * p x - 1 / 2 * deriv (fun y => a y * p y) x

/-- `L* p = −J'` whenever `μ p` and `(a p)'` are differentiable at `x`. -/
@[powerlib_foundation] theorem fp1_eq_neg_deriv_flux {μ a p : ℝ → ℝ} {x : ℝ}
    (h1 : DifferentiableAt ℝ (fun y => μ y * p y) x)
    (h2 : DifferentiableAt ℝ (deriv (fun y => a y * p y)) x) :
    fp1 μ a p x = -deriv (flux1 μ a p) x := by
  unfold fp1 flux1
  rw [show (fun y => μ y * p y - 1 / 2 * deriv (fun y => a y * p y) y) =
      (fun y => μ y * p y) - fun y => 1 / 2 * deriv (fun y => a y * p y) y from rfl,
    deriv_sub h1 (h2.const_mul _), deriv_const_mul _ h2]
  ring

/-- Integration by parts on `ℝ` against a compactly supported `C¹` function. -/
@[powerlib_foundation] theorem integral_mul_deriv_of_hasCompactSupport {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    ∫ x, u x * deriv v x = -∫ x, deriv u x * v x := by
  have hdu := hu.continuous_deriv le_rfl
  have hdv := hv.continuous_deriv le_rfl
  have hvc' : HasCompactSupport (deriv v) := hvc.deriv
  apply integral_mul_deriv_eq_deriv_mul_of_integrable
  · exact fun x _ => (hu.differentiable one_ne_zero x).hasDerivAt
  · exact fun x _ => (hv.differentiable one_ne_zero x).hasDerivAt
  · exact (hu.continuous.mul hdv).integrable_of_hasCompactSupport hvc'.mul_left
  · exact (hdu.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  · exact (hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left

/-- **`L*` is the formal adjoint of `L` (§1.1)**: for compactly supported `C²` test functions `φ`,
`∫ p (L φ) = ∫ (L* p) φ`, provided `μ p ∈ C¹` and `a p ∈ C²`. -/
@[powerlib_foundation] theorem integral_gen1_eq_integral_fp1 {μ a p φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hμp : ContDiff ℝ 1 (fun y => μ y * p y)) (hap : ContDiff ℝ 2 (fun y => a y * p y)) :
    ∫ x, p x * gen1 μ a φ x = ∫ x, fp1 μ a p x * φ x := by
  have hφ1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hap1 : ContDiff ℝ 1 (deriv (fun y => a y * p y)) := hap.deriv'
  have hφ' : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hap' : ContDiff ℝ 1 (fun y => a y * p y) := hap.of_le (by norm_num)
  have hφc1 : HasCompactSupport (deriv φ) := hφc.deriv
  have hφc2 : HasCompactSupport (deriv (deriv φ)) := hφc1.deriv
  have hcφ := hφ.continuous
  have hcφ1 := hφ1.continuous
  have hcφ2 := hφ1.continuous_deriv le_rfl
  -- first-order part
  have e1 : ∫ x, (μ x * p x) * deriv φ x = -∫ x, deriv (fun y => μ y * p y) x * φ x :=
    integral_mul_deriv_of_hasCompactSupport hμp hφ' hφc
  -- second-order part, twice
  have e2 : ∫ x, (a x * p x) * deriv (deriv φ) x =
      -∫ x, deriv (fun y => a y * p y) x * deriv φ x :=
    integral_mul_deriv_of_hasCompactSupport hap' hφ1 hφc1
  have e3 : ∫ x, deriv (fun y => a y * p y) x * deriv φ x =
      -∫ x, deriv (deriv (fun y => a y * p y)) x * φ x :=
    integral_mul_deriv_of_hasCompactSupport hap1 hφ' hφc
  have i1 : Integrable (fun x => (μ x * p x) * deriv φ x) :=
    (hμp.continuous.mul hcφ1).integrable_of_hasCompactSupport hφc1.mul_left
  have i2 : Integrable (fun x => (a x * p x) * deriv (deriv φ) x) :=
    (hap'.continuous.mul hcφ2).integrable_of_hasCompactSupport hφc2.mul_left
  have i3 : Integrable (fun x => -(deriv (fun y => μ y * p y) x * φ x)) :=
    (((hμp.continuous_deriv le_rfl).mul hcφ).integrable_of_hasCompactSupport hφc.mul_left).neg
  have i4 : Integrable (fun x => deriv (deriv (fun y => a y * p y)) x * φ x) :=
    ((hap1.continuous_deriv le_rfl).mul hcφ).integrable_of_hasCompactSupport hφc.mul_left
  have lhs : (fun x => p x * gen1 μ a φ x) =
      fun x => (μ x * p x) * deriv φ x + 1 / 2 * ((a x * p x) * deriv (deriv φ) x) := by
    funext x; unfold gen1; ring
  have rhs : (fun x => fp1 μ a p x * φ x) =
      fun x => -(deriv (fun y => μ y * p y) x * φ x) +
        1 / 2 * (deriv (deriv (fun y => a y * p y)) x * φ x) := by
    funext x; unfold fp1; ring
  rw [lhs, rhs, integral_add i1 (i2.const_mul _), integral_add i3 (i4.const_mul _),
    integral_const_mul, integral_const_mul, integral_neg, e1, e2, e3]
  ring

/-! ## Stationary solutions -/

/-- **One-dimensional zero-flux density (§1.4)**: for `dX = μ dt + √(2D) dW` (`a = 2D`), if
`Φ' = μ/D` and `p = (C/D) e^{Φ}` with `D ≠ 0` everywhere, then `(D p)' = μ p`, the flux
`J = μ p − (D p)'` vanishes identically and `L* p = 0`. -/
@[powerlib_foundation] theorem zeroFlux_hasDerivAt {μ D Φ : ℝ → ℝ} (C : ℝ)
    (hD : ∀ x, D x ≠ 0) (hΦ : ∀ x, HasDerivAt Φ (μ x / D x) x) (x : ℝ) :
    HasDerivAt (fun y => D y * (C / D y * exp (Φ y))) (μ x * (C / D x * exp (Φ x))) x := by
  have e : (fun y => D y * (C / D y * exp (Φ y))) = fun y => C * exp (Φ y) := by
    funext y; field_simp [hD y]
  rw [e]
  have := ((hΦ x).exp).const_mul C
  convert! this using 1
  field_simp [hD x]

@[powerlib_foundation] theorem zeroFlux_flux {μ D Φ : ℝ → ℝ} (C : ℝ)
    (hD : ∀ x, D x ≠ 0) (hΦ : ∀ x, HasDerivAt Φ (μ x / D x) x) (x : ℝ) :
    flux1 μ (fun y => 2 * D y) (fun y => C / D y * exp (Φ y)) x = 0 := by
  unfold flux1
  have h := (zeroFlux_hasDerivAt C hD hΦ x).const_mul 2
  have e : (fun y => 2 * D y * (C / D y * exp (Φ y))) =
      fun y => 2 * (D y * (C / D y * exp (Φ y))) := by funext y; ring
  rw [e, h.deriv]
  ring

@[powerlib_foundation] theorem zeroFlux_stationary {μ D Φ : ℝ → ℝ} (C : ℝ)
    (hD : ∀ x, D x ≠ 0) (hΦ : ∀ x, HasDerivAt Φ (μ x / D x) x) (x : ℝ) :
    fp1 μ (fun y => 2 * D y) (fun y => C / D y * exp (Φ y)) x = 0 := by
  unfold fp1
  have hd : deriv (fun y => 2 * D y * (C / D y * exp (Φ y))) =
      fun y => 2 * (μ y * (C / D y * exp (Φ y))) := by
    funext y
    have h := (zeroFlux_hasDerivAt C hD hΦ y).const_mul 2
    have e : (fun y => 2 * D y * (C / D y * exp (Φ y))) =
        fun y => 2 * (D y * (C / D y * exp (Φ y))) := by funext y; ring
    rw [e, h.deriv]
  rw [hd]
  by_cases hdiff : DifferentiableAt ℝ (fun y => μ y * (C / D y * exp (Φ y))) x
  · rw [deriv_const_mul _ hdiff]; ring
  · have h2 : ¬ DifferentiableAt ℝ (fun y => 2 * (μ y * (C / D y * exp (Φ y)))) x := by
      intro h; apply hdiff
      have := h.const_mul (1 / 2 : ℝ)
      simpa [← mul_assoc] using this
    rw [deriv_zero_of_not_differentiableAt hdiff, deriv_zero_of_not_differentiableAt h2]
    ring

/-- **Gibbs form (§1.4)**: gradient drift `μ = −V'`, constant `D > 0`: `p = e^{−V/D}` has zero
flux and solves `L* p = 0` (special case `Φ = −V/D`, `C = D`). -/
@[powerlib_foundation] theorem gibbs_stationary {V V' : ℝ → ℝ} {D : ℝ} (hD : D ≠ 0)
    (hV : ∀ x, HasDerivAt V (V' x) x) (x : ℝ) :
    fp1 (fun y => -V' y) (fun _ => 2 * D) (fun y => exp (-V y / D)) x = 0 := by
  have hΦ : ∀ x, HasDerivAt (fun y => -V y / D) ((fun y => -V' y) x / (fun _ => D) x) x := by
    intro x
    simpa [neg_div] using ((hV x).neg.div_const D)
  have := zeroFlux_stationary (μ := fun y => -V' y) (D := fun _ => D) D (fun _ => hD) hΦ x
  convert! this using 3
  rw [div_self hD, one_mul]

@[powerlib_foundation] theorem gibbs_flux {V V' : ℝ → ℝ} {D : ℝ} (hD : D ≠ 0)
    (hV : ∀ x, HasDerivAt V (V' x) x) (x : ℝ) :
    flux1 (fun y => -V' y) (fun _ => 2 * D) (fun y => exp (-V y / D)) x = 0 := by
  have hΦ : ∀ x, HasDerivAt (fun y => -V y / D) ((fun y => -V' y) x / (fun _ => D) x) x := by
    intro x
    simpa [neg_div] using ((hV x).neg.div_const D)
  have := zeroFlux_flux (μ := fun y => -V' y) (D := fun _ => D) D (fun _ => hD) hΦ x
  convert! this using 3
  rw [div_self hD, one_mul]

/-- **Normalization hypothesis made explicit**: if `Z = ∫ e^{−V/D} < ∞` (integrability), then
`e^{−V/D}/Z` is a probability density (nonnegative, total mass one). -/
@[powerlib_foundation] theorem gibbs_normalized {V : ℝ → ℝ} {D : ℝ}
    (hint : Integrable (fun x => exp (-V x / D))) :
    (∀ x, 0 ≤ exp (-V x / D) / ∫ y, exp (-V y / D)) ∧
      ∫ x, exp (-V x / D) / ∫ y, exp (-V y / D) = 1 := by
  have hZ : 0 < ∫ y, exp (-V y / D) := by
    rw [integral_pos_iff_support_of_nonneg (fun y => (exp_pos _).le) hint]
    have : Function.support (fun y => exp (-V y / D)) = Set.univ := by
      ext y; simp [(exp_pos _).ne']
    rw [this]; simp
  refine ⟨fun x => div_nonneg (exp_pos _).le hZ.le, ?_⟩
  rw [integral_div, div_self hZ.ne']

/-- Without normalizability: `e^{−V/D}` is not integrable when `V ≤ C` on a measurable set of
infinite length (e.g. periodic `V`). -/
@[powerlib_foundation] theorem gibbs_not_integrable {V : ℝ → ℝ} {D C : ℝ} (hD : 0 < D)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : volume S = ⊤) (hVS : ∀ x ∈ S, V x ≤ C) :
    ¬ Integrable (fun x => exp (-V x / D)) := by
  intro hint
  have hle : ∀ x, S.indicator (fun _ => ENNReal.ofReal (exp (-C / D))) x ≤
      ‖exp (-V x / D)‖ₑ := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal (exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      apply exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hD.le
      linarith [hVS x hx]
    · rw [Set.indicator_of_notMem hx]; positivity
  have hge : ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal (exp (-C / D))) x ≤
      ∫⁻ x, ‖exp (-V x / D)‖ₑ := lintegral_mono hle
  rw [lintegral_indicator_const hSm, hS, ENNReal.mul_top (by simpa using exp_pos _)] at hge
  exact absurd (lt_of_le_of_lt hge hint.hasFiniteIntegral) (lt_irrefl _)

end powerlib.Stochastic.FP
