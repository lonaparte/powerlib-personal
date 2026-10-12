import theorem.PhasePlane.Planar
import theorem.NormalForm.Logistic

/-! # Truncated Hopf normal form

Foundation layer: the cubic truncation of the Hopf normal form, not an engineering model.

Model boundary. State `x = (x 0, x 1) ∈ State 2`, identified with `z = x 0 + i x 1`. Constant
parameters `μ, ω₀` and cubic coefficient `c = l₁ + iκ` (`l₁ = Re c`, the first Lyapunov
coefficient of the truncation). The vector field is exactly
`ż = (μ + iω₀) z + c z |z|²` (`field_complex`), i.e.
`ẋ₀ = μx₀ − ω₀x₁ + (l₁x₀ − κx₁)ρ`, `ẋ₁ = ω₀x₀ + μx₁ + (κx₀ + l₁x₁)ρ`, `ρ = x₀² + x₁²`,
with no `O(|z|⁴)` remainder, continuous time, no input or noise.

Results.
* Linearization at the origin `!![μ, −ω₀; ω₀, μ]`: every eigenvalue has real part `μ`, and
  `μ + iω₀` is one; for the linear part (`c = 0`) every solution has `‖x(t)‖ = e^{μ(t−a)}‖x(a)‖`,
  so the linear decay rate is exactly `|μ|` when `μ < 0`. The origin of the nonlinear field is
  locally exponentially stable for `μ < 0` and unstable for `μ > 0`.
* Polar form: along every solution `ρ̇ = 2μρ + 2l₁ρ²`, `ṙ = μr + l₁r³` (`r > 0`) and
  `x₀ẋ₁ − x₁ẋ₀ = (ω₀ + κρ)ρ`, i.e. `θ̇ = ω₀ + κr²`.
* If `R² = −μ/l₁ > 0` the circle `|z| = R` is invariant and carries the periodic solution
  `R (cos Ωt, sin Ωt)`, `Ω = ω₀ + κR²` (`Ω ≠ 0`); its range is the whole circle.
* Supercritical (`μ > 0 > l₁`, `R = √(μ/|l₁|)`): the cycle is an attracting limit cycle; every
  forward-complete solution with `x(a) ≠ 0` has `|z| → R` and distance to the cycle `→ 0`.
* Subcritical (`μ < 0 < l₁`, `R = √(−μ/l₁)`): the cycle is repelling,
  `|1/|z|² − 1/R²|` grows like `e^{2|μ|(t−a)}`, and solutions starting inside converge to `0`.

Periodic orbits and attracting limit cycles are written out in the statements (behaviour is
defined only in the semantic layer). A *periodic orbit* of `ẋ = f x` with period `T` is a curve
`γ : ℝ → State n` with `0 < T`, `∀ t, HasDerivAt γ (f (γ t)) t` (a solution defined for all time),
`∀ t, γ (t + T) = γ t` and `∃ t, γ t ≠ γ 0` (nonconstant). It is an *attracting limit cycle* when,
in addition, some open `U ⊇ range γ` is *orbitally attracted*: every forward-complete solution
`φ` (`IsIntegralCurveOn φ (fun _ x => f x) (Ici a)`) with `φ a ∈ U` has
`Metric.infDist (φ t) (range γ) → 0` as `t → ∞`.

Source: work-sync theory/T-hopf-bifurcation.md §1.1–1.4, theory/T-bifurcation.md §1.4
(Hopf normal form), theory/T-fold-critical-scaling.md §2.4 (Hopf linear rate).
The `O(|z|⁴)` / `O(r⁵)` remainder bookkeeping of §1.2 is not formalized (truncated system only).

Architecture: a truncated normal form, not an engineering model, so no model family is defined;
all results remain public foundation support. Behaviour is LeanForControl's predicates and the
linearization theorems of `powerlib.Criteria` / `powerlib.Flow`.
-/

noncomputable section

namespace powerlib.NormalForm.Hopf
open Set Filter Topology Matrix
open powerlib.Dynamics (State)
open powerlib.PhasePlane

/-- Parameters `μ, ω₀` and cubic coefficient `c = l₁ + iκ`. -/
structure Params where
  μ : ℝ
  ω₀ : ℝ
  l₁ : ℝ
  κ : ℝ

/-- The truncated Hopf normal form in Cartesian coordinates. -/
def field (p : Params) (x : State 2) : State 2 :=
  mk (p.μ * x 0 - p.ω₀ * x 1 + (p.l₁ * x 0 - p.κ * x 1) * (x 0 ^ 2 + x 1 ^ 2))
    (p.ω₀ * x 0 + p.μ * x 1 + (p.κ * x 0 + p.l₁ * x 1) * (x 0 ^ 2 + x 1 ^ 2))

/-- The planar state as a complex number. -/
def toComplex (x : State 2) : ℂ := ⟨x 0, x 1⟩

@[powerlib_foundation] theorem field_contDiff (p : Params) {k : WithTop ℕ∞} :
    ContDiff ℝ k (field p) := by
  apply contDiff_of_components <;> (simp only [field, mk_apply_zero, mk_apply_one]; fun_prop)

@[simp, powerlib_foundation] theorem field_apply_zero (p : Params) (x : State 2) :
    field p x 0 = p.μ * x 0 - p.ω₀ * x 1 + (p.l₁ * x 0 - p.κ * x 1) * (x 0 ^ 2 + x 1 ^ 2) := rfl

@[simp, powerlib_foundation] theorem field_apply_one (p : Params) (x : State 2) :
    field p x 1 = p.ω₀ * x 0 + p.μ * x 1 + (p.κ * x 0 + p.l₁ * x 1) * (x 0 ^ 2 + x 1 ^ 2) := rfl

/-- The Cartesian field is the complex normal form `ż = (μ + iω₀) z + c z |z|²`. -/
@[powerlib_foundation] theorem field_complex (p : Params) (x : State 2) :
    toComplex (field p x) =
      (p.μ + p.ω₀ * Complex.I) * toComplex x +
        (p.l₁ + p.κ * Complex.I) * toComplex x * (Complex.normSq (toComplex x) : ℂ) := by
  apply Complex.ext
  · change field p x 0 = _
    simp only [field_apply_zero, toComplex, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply]
    ring
  · change field p x 1 = _
    simp only [field_apply_one, toComplex, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply]
    ring

@[powerlib_foundation] theorem field_zero (p : Params) : field p 0 = 0 := by
  rw [field, mk_eq_zero_iff]; simp only [PiLp.zero_apply]; constructor <;> ring

/-- The linear part of the normal form. -/
def linPart (p : Params) : Matrix (Fin 2) (Fin 2) ℝ := !![p.μ, -p.ω₀; p.ω₀, p.μ]

@[powerlib_foundation] theorem hasFDerivAt_field_zero (p : Params) :
    HasFDerivAt (field p) (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (linPart p)) 0 := by
  refine hasFDerivAt_of_components _
    ![p.μ • coord 0 - p.ω₀ • coord 1, p.ω₀ • coord 0 + p.μ • coord 1] ?_ ?_
  · have h0 := hasFDerivAt_coord 0 (0 : State 2)
    have h1 := hasFDerivAt_coord 1 (0 : State 2)
    have hρ : HasFDerivAt (fun x : State 2 => x 0 ^ 2 + x 1 ^ 2) _ 0 := (h0.pow 2).add (h1.pow 2)
    intro i; fin_cases i
    · show HasFDerivAt (fun y => field p y 0) (p.μ • coord 0 - p.ω₀ • coord 1) 0
      have h : HasFDerivAt (fun x : State 2 =>
          p.μ * x 0 - p.ω₀ * x 1 + (p.l₁ * x 0 - p.κ * x 1) * (x 0 ^ 2 + x 1 ^ 2)) _ 0 :=
        ((h0.const_mul p.μ).sub (h1.const_mul p.ω₀)).add
          (((h0.const_mul p.l₁).sub (h1.const_mul p.κ)).mul hρ)
      have hf : (fun y => field p y 0) = fun x : State 2 =>
          p.μ * x 0 - p.ω₀ * x 1 + (p.l₁ * x 0 - p.κ * x 1) * (x 0 ^ 2 + x 1 ^ 2) :=
        funext fun _ => rfl
      rw [hf]
      convert h using 1
      ext v; simp
    · show HasFDerivAt (fun y => field p y 1) (p.ω₀ • coord 0 + p.μ • coord 1) 0
      have h : HasFDerivAt (fun x : State 2 =>
          p.ω₀ * x 0 + p.μ * x 1 + (p.κ * x 0 + p.l₁ * x 1) * (x 0 ^ 2 + x 1 ^ 2)) _ 0 :=
        ((h0.const_mul p.ω₀).add (h1.const_mul p.μ)).add
          (((h0.const_mul p.κ).add (h1.const_mul p.l₁)).mul hρ)
      have hf : (fun y => field p y 1) = fun x : State 2 =>
          p.ω₀ * x 0 + p.μ * x 1 + (p.κ * x 0 + p.l₁ * x 1) * (x 0 ^ 2 + x 1 ^ 2) :=
        funext fun _ => rfl
      rw [hf]
      convert h using 1
      ext v; simp
  · intro i v; fin_cases i <;> simp [linPart] <;> ring

@[powerlib_foundation] theorem fderiv_field_zero (p : Params) :
    fderiv ℝ (field p) 0 = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (linPart p) :=
  (hasFDerivAt_field_zero p).fderiv

@[powerlib_foundation] theorem trace_linPart (p : Params) : (linPart p).trace = 2 * p.μ := by
  simp [linPart, Matrix.trace_fin_two]; ring

@[powerlib_foundation] theorem det_linPart (p : Params) :
    (linPart p).det = p.μ ^ 2 + p.ω₀ ^ 2 := by
  simp [linPart, Matrix.det_fin_two]; ring

/-- Every eigenvalue of the linear part has real part `μ`. -/
@[powerlib_foundation] theorem eigenvalue_re (p : Params) {s : ℂ} {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heig : (linPart p).map (algebraMap ℝ ℂ) *ᵥ v = s • v) : s.re = p.μ := by
  have h := Criteria.det_characteristicMatrix_eq_zero_of_eigenpair (linPart p) hv heig
  rw [Criteria.det_characteristicMatrix_fin_two, trace_linPart, det_linPart] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have him' : 2 * (s.re - p.μ) * s.im = 0 := by linarith
  rcases mul_eq_zero.mp him' with h1 | h1
  · linarith [mul_eq_zero.mp h1 |>.resolve_left (by norm_num : (2 : ℝ) ≠ 0)]
  · rw [h1] at hre
    nlinarith [sq_nonneg (s.re - p.μ), sq_nonneg p.ω₀]

/-- `μ + iω₀` is an eigenvalue of the linear part. -/
@[powerlib_foundation] theorem exists_eigenpair (p : Params) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (linPart p).map (algebraMap ℝ ℂ) *ᵥ v = ((p.μ : ℂ) + p.ω₀ * Complex.I) • v := by
  apply Criteria.exists_eigenpair_of_det_characteristicMatrix_eq_zero
  rw [Criteria.det_characteristicMatrix_fin_two, trace_linPart, det_linPart]
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

/-- For `μ < 0` the origin is locally exponentially stable. -/
@[powerlib_foundation] theorem origin_stable (p : Params) (hμ : p.μ < 0) :
    LocallyExponentiallyStable (field p) 0 :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two (linPart p) (field_contDiff p)
    (field_zero p) (fderiv_field_zero p) (by rw [trace_linPart]; linarith)
    (by rw [det_linPart]; nlinarith [sq_nonneg p.ω₀, mul_pos (neg_pos.mpr hμ) (neg_pos.mpr hμ)])

/-- For `μ > 0` the origin is unstable. -/
@[powerlib_foundation] theorem origin_unstable (p : Params) (hμ : 0 < p.μ) :
    Unstable (field p) 0 :=
  Criteria.unstable_of_jacobian_trace_pos_fin_two (linPart p) (field_contDiff p)
    (field_zero p) (fderiv_field_zero p) (by rw [trace_linPart]; linarith)

/-! ## Polar form -/

@[powerlib_foundation] theorem radial_identity (p : Params) (x : State 2) :
    x 0 * field p x 0 + x 1 * field p x 1 =
      p.μ * (x 0 ^ 2 + x 1 ^ 2) + p.l₁ * (x 0 ^ 2 + x 1 ^ 2) ^ 2 := by
  simp [field]; ring

/-- `x₀ẋ₁ − x₁ẋ₀ = (ω₀ + κρ)ρ`, i.e. `θ̇ = ω₀ + κ r²`. -/
@[powerlib_foundation] theorem angular_identity (p : Params) (x : State 2) :
    x 0 * field p x 1 - x 1 * field p x 0 = (p.ω₀ + p.κ * ‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  rw [norm_sq_eq]; simp [field]; ring

/-- Along every solution, `ρ = ‖x‖²` obeys `ρ̇ = 2μρ + 2l₁ρ²`. -/
@[powerlib_foundation] theorem normSq_isIntegralCurveOn (p : Params) {φ : ℝ → State 2}
    {s : Set ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => field p x) s) :
    IsIntegralCurveOn (fun t => ‖φ t‖ ^ 2) (fun _ r => Logistic.field p.μ p.l₁ r) s := by
  intro t ht
  obtain ⟨h0, h1⟩ := hasDerivWithinAt_iff_components.mp (hφ t ht)
  have h := (h0.pow 2).add (h1.pow 2)
  have hfun : (fun τ => ‖φ τ‖ ^ 2) = fun τ => φ τ 0 ^ 2 + φ τ 1 ^ 2 := by
    funext τ; exact norm_sq_eq (φ τ)
  rw [hfun]
  convert h using 1
  have := radial_identity p (φ t)
  simp only [Logistic.field]
  push_cast
  linear_combination (-2 : ℝ) * this

/-- For `r = ‖x‖ > 0`, `ṙ = μ r + l₁ r³`. -/
@[powerlib_foundation] theorem radius_hasDerivWithinAt (p : Params) {φ : ℝ → State 2}
    {s : Set ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => field p x) s) {t : ℝ} (ht : t ∈ s)
    (hne : φ t ≠ 0) :
    HasDerivWithinAt (fun τ => ‖φ τ‖) (p.μ * ‖φ t‖ + p.l₁ * ‖φ t‖ ^ 3) s t := by
  have hρ := normSq_isIntegralCurveOn p hφ t ht
  have hpos : 0 < ‖φ t‖ := norm_pos_iff.mpr hne
  have hsq := hρ.sqrt (pow_pos hpos 2).ne'
  have hfun : (fun τ => √(‖φ τ‖ ^ 2)) = fun τ => ‖φ τ‖ := by
    funext τ; exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hsq
  convert hsq using 1
  rw [Real.sqrt_sq hpos.le]
  simp only [Logistic.field]
  field_simp

/-- Linear part only (`c = 0`): `‖x(t)‖ = e^{μ(t − a)} ‖x(a)‖`, the exact linear decay rate. -/
@[powerlib_foundation] theorem linear_norm_eq {μ ω₀ : ℝ} {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field ⟨μ, ω₀, 0, 0⟩) a b) :
    ∀ t ∈ Icc a b, ‖φ t‖ = Real.exp (μ * (t - a)) * ‖φ a‖ := by
  have hρ := normSq_isIntegralCurveOn ⟨μ, ω₀, 0, 0⟩ hφ
  have hconst := eq_of_hasDerivWithinAt_zero
    (F := fun t => ‖φ t‖ ^ 2 * Real.exp (-2 * μ * (t - a))) (a := a) (b := b)
    (by
      intro t ht
      have he : HasDerivAt (fun s => Real.exp (-2 * μ * (s - a)))
          (Real.exp (-2 * μ * (t - a)) * (-2 * μ)) t := by
        have : HasDerivAt (fun s => -2 * μ * (s - a)) (-2 * μ) t := by
          simpa using ((hasDerivAt_id t).sub_const a).const_mul (-2 * μ)
        exact this.exp
      convert (hρ t ht).mul he.hasDerivWithinAt using 1
      simp [Logistic.field]; ring)
  intro t ht
  have h := hconst t ht
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at h
  have hsq : ‖φ t‖ ^ 2 = (Real.exp (μ * (t - a)) * ‖φ a‖) ^ 2 := by
    have he : Real.exp (-2 * μ * (t - a)) * Real.exp (μ * (t - a)) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring_nf
    calc ‖φ t‖ ^ 2 = ‖φ t‖ ^ 2 * Real.exp (-2 * μ * (t - a)) * Real.exp (μ * (t - a)) ^ 2 := by
          rw [mul_assoc, he, mul_one]
      _ = (Real.exp (μ * (t - a)) * ‖φ a‖) ^ 2 := by rw [h]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-! ## The invariant circle and its periodic solution -/

/-- Radius of the invariant circle, `R = √(−μ/l₁)`. -/
def radius (p : Params) : ℝ := √(-p.μ / p.l₁)

/-- Angular frequency on the circle, `Ω = ω₀ + κ R²`. -/
def frequency (p : Params) : ℝ := p.ω₀ + p.κ * (-p.μ / p.l₁)

/-- The explicit periodic solution `R (cos Ωt, sin Ωt)`. -/
def cycle (p : Params) (t : ℝ) : State 2 :=
  mk (radius p * Real.cos (frequency p * t)) (radius p * Real.sin (frequency p * t))

@[simp, powerlib_foundation] theorem cycle_apply_zero (p : Params) (t : ℝ) :
    cycle p t 0 = radius p * Real.cos (frequency p * t) := rfl

@[simp, powerlib_foundation] theorem cycle_apply_one (p : Params) (t : ℝ) :
    cycle p t 1 = radius p * Real.sin (frequency p * t) := rfl

@[powerlib_foundation] theorem radius_nonneg (p : Params) : 0 ≤ radius p := Real.sqrt_nonneg _

@[powerlib_foundation] theorem radius_sq (p : Params) (hR : 0 ≤ -p.μ / p.l₁) :
    radius p ^ 2 = -p.μ / p.l₁ :=
  Real.sq_sqrt hR

/-- The circle `‖x‖² = −μ/l₁` is invariant. -/
@[powerlib_foundation] theorem circle_invariant (p : Params) (hμ : p.μ ≠ 0) (hl : p.l₁ ≠ 0)
    (hR : 0 < -p.μ / p.l₁) {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field p) a b) (ha : ‖φ a‖ ^ 2 = -p.μ / p.l₁) :
    ∀ t ∈ Icc a b, ‖φ t‖ ^ 2 = -p.μ / p.l₁ :=
  Logistic.level_invariant hμ hl hR (normSq_isIntegralCurveOn p hφ) ha

@[powerlib_foundation] theorem cycle_hasDerivAt (p : Params) (hl : p.l₁ ≠ 0)
    (hR : 0 ≤ -p.μ / p.l₁) (t : ℝ) :
    HasDerivAt (cycle p) (field p (cycle p t)) t := by
  have hR2 := radius_sq p hR
  have hμR : p.μ + p.l₁ * radius p ^ 2 = 0 := by rw [hR2]; field_simp; ring
  have hc : HasDerivAt (fun s => Real.cos (frequency p * s))
      (-Real.sin (frequency p * t) * frequency p) t := by
    have := ((hasDerivAt_id' t).const_mul (frequency p)).cos
    rwa [mul_one] at this
  have hs : HasDerivAt (fun s => Real.sin (frequency p * s))
      (Real.cos (frequency p * t) * frequency p) t := by
    have := ((hasDerivAt_id' t).const_mul (frequency p)).sin
    rwa [mul_one] at this
  rw [← hasDerivWithinAt_univ, hasDerivWithinAt_iff_components]
  have hpyth : Real.cos (frequency p * t) ^ 2 + Real.sin (frequency p * t) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have hfreq : frequency p = p.ω₀ + p.κ * radius p ^ 2 := by rw [hR2]; rfl
  have hsum : (radius p * Real.cos (frequency p * t)) ^ 2 +
      (radius p * Real.sin (frequency p * t)) ^ 2 = radius p ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, hpyth, mul_one]
  constructor
  · have hc' : HasDerivWithinAt (fun τ => cycle p τ 0)
        (radius p * (-Real.sin (frequency p * t) * frequency p)) univ t :=
      (hc.const_mul (radius p)).hasDerivWithinAt
    convert hc' using 1
    rw [field_apply_zero, cycle_apply_zero, cycle_apply_one, hsum]
    linear_combination (radius p * Real.cos (frequency p * t)) * hμR +
      (radius p * Real.sin (frequency p * t)) * hfreq
  · have hs' : HasDerivWithinAt (fun τ => cycle p τ 1)
        (radius p * (Real.cos (frequency p * t) * frequency p)) univ t :=
      (hs.const_mul (radius p)).hasDerivWithinAt
    convert hs' using 1
    rw [field_apply_one, cycle_apply_zero, cycle_apply_one, hsum]
    linear_combination (radius p * Real.sin (frequency p * t)) * hμR -
      (radius p * Real.cos (frequency p * t)) * hfreq

@[powerlib_foundation] theorem norm_cycle (p : Params) (t : ℝ) : ‖cycle p t‖ = radius p := by
  rw [cycle, norm_mk, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one,
    Real.sqrt_sq (radius_nonneg p)]

/-- The range of the cycle is the whole circle of radius `R` (`Ω ≠ 0`). -/
@[powerlib_foundation] theorem range_cycle (p : Params) (hΩ : frequency p ≠ 0) :
    range (cycle p) = Metric.sphere 0 (radius p) := by
  ext y
  simp only [mem_range, mem_sphere_iff_norm, sub_zero]
  constructor
  · rintro ⟨t, rfl⟩; exact norm_cycle p t
  · intro hy
    set z : ℂ := ⟨y 0, y 1⟩
    have hz : ‖z‖ = radius p := by
      rw [← hy, Complex.norm_eq_sqrt_sq_add_sq, ← norm_mk, mk_coords]
    refine ⟨Complex.arg z / frequency p, ?_⟩
    rw [cycle, mul_div_cancel₀ _ hΩ, ← hz, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    exact mk_coords y

/-- If `R² = −μ/l₁ > 0` and `Ω ≠ 0`, the cycle is a `2π/|Ω|`-periodic orbit: a nonconstant
`T`-periodic solution of `ẋ = field p x` defined for all time, `T = 2π/|Ω| > 0`. -/
@[powerlib_foundation] theorem cycle_isPeriodicOrbit (p : Params) (hl : p.l₁ ≠ 0)
    (hR : 0 < -p.μ / p.l₁) (hΩ : frequency p ≠ 0) :
    0 < 2 * Real.pi / |frequency p| ∧ (∀ t, HasDerivAt (cycle p) (field p (cycle p t)) t) ∧
      (∀ t, cycle p (t + 2 * Real.pi / |frequency p|) = cycle p t) ∧
      ∃ t, cycle p t ≠ cycle p 0 := by
  have hrpos : 0 < radius p := Real.sqrt_pos.mpr hR
  refine ⟨by positivity, cycle_hasDerivAt p hl hR.le, ?_, ?_⟩
  · intro t
    rcases lt_or_gt_of_ne hΩ with h | h
    · have hT : frequency p * (t + 2 * Real.pi / |frequency p|) =
          frequency p * t - 2 * Real.pi := by
        rw [abs_of_neg h]; field_simp; ring
      simp only [cycle, hT, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
    · have hT : frequency p * (t + 2 * Real.pi / |frequency p|) =
          frequency p * t + 2 * Real.pi := by
        rw [abs_of_pos h]; field_simp
      simp only [cycle, hT, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · refine ⟨Real.pi / frequency p, ?_⟩
    rw [cycle, cycle, mul_div_cancel₀ _ hΩ, mul_zero, Real.cos_pi, Real.sin_pi, Real.cos_zero,
      Real.sin_zero, Ne, mk_eq_iff]
    intro h
    linarith [h.1]

/-- Distance from a nonzero state to the circle of radius `R ≥ 0` is at most `|‖x‖ − R|`. -/
@[powerlib_foundation] theorem infDist_sphere_le {x : State 2} (hx : x ≠ 0) {R : ℝ} (hR : 0 ≤ R) :
    Metric.infDist x (Metric.sphere 0 R) ≤ |‖x‖ - R| := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hmem : (R / ‖x‖) • x ∈ Metric.sphere (0 : State 2) R := by
    rw [mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hR,
      abs_of_pos hn, div_mul_cancel₀ _ hn.ne']
  refine (Metric.infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
  have hx' : x - (R / ‖x‖) • x = (1 - R / ‖x‖) • x := by rw [sub_smul, one_smul]
  rw [dist_eq_norm, hx', norm_smul, Real.norm_eq_abs,
    show 1 - R / ‖x‖ = (‖x‖ - R) / ‖x‖ by field_simp, abs_div, abs_of_pos hn,
    div_mul_cancel₀ _ hn.ne']

/-- Supercritical truncation (`μ > 0`, `l₁ < 0`): every forward-complete nonzero solution has
`‖x(t)‖ → R = √(μ/|l₁|)`. -/
@[powerlib_foundation] theorem supercritical_norm_tendsto (p : Params) (hμ : 0 < p.μ)
    (hl : p.l₁ < 0) {φ : ℝ → State 2} {a : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => field p x) (Ici a)) (ha : φ a ≠ 0) :
    Tendsto (fun t => ‖φ t‖) atTop (𝓝 (radius p)) := by
  have hρ := Logistic.tendsto_level hμ hl (normSq_isIntegralCurveOn p hφ)
    (pow_pos (norm_pos_iff.mpr ha) 2)
  have := (Real.continuous_sqrt.tendsto _).comp hρ
  refine this.congr (fun t => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- Supercritical truncation: the cycle is an attracting limit cycle — a `2π/|Ω|`-periodic orbit
(as in `cycle_isPeriodicOrbit`) together with an open neighbourhood `U ⊇ range (cycle p)` that it
attracts orbitally: every forward-complete solution starting in `U` has distance to the cycle
`→ 0`. Here `U` is the punctured plane, so it attracts every forward-complete solution that does
not start at the origin. -/
@[powerlib_foundation] theorem supercritical_isAttractingLimitCycle (p : Params) (hμ : 0 < p.μ)
    (hl : p.l₁ < 0) (hΩ : frequency p ≠ 0) :
    (0 < 2 * Real.pi / |frequency p| ∧ (∀ t, HasDerivAt (cycle p) (field p (cycle p t)) t) ∧
      (∀ t, cycle p (t + 2 * Real.pi / |frequency p|) = cycle p t) ∧
      ∃ t, cycle p t ≠ cycle p 0) ∧
    ∃ U : Set (State 2), IsOpen U ∧ range (cycle p) ⊆ U ∧
      ∀ (a : ℝ) (φ : ℝ → State 2), IsIntegralCurveOn φ (fun _ x => field p x) (Ici a) →
        φ a ∈ U → Tendsto (fun t => Metric.infDist (φ t) (range (cycle p))) atTop (𝓝 0) := by
  have hR : 0 < -p.μ / p.l₁ := div_pos_of_neg_of_neg (by linarith) hl
  have hrpos : 0 < radius p := Real.sqrt_pos.mpr hR
  refine ⟨cycle_isPeriodicOrbit p hl.ne hR hΩ, {x | x ≠ 0}, isOpen_ne, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    intro h0
    have := norm_cycle p t
    rw [h0, norm_zero] at this
    linarith
  · intro a φ hφ ha
    rw [range_cycle p hΩ]
    have hnorm := supercritical_norm_tendsto p hμ hl hφ ha
    have hpos : ∀ t, a ≤ t → φ t ≠ 0 := by
      intro t ht h0
      have := Logistic.pos (normSq_isIntegralCurveOn p (hφ.mono (Icc_subset_Ici_self : Icc a t ⊆ Ici a)))
        (pow_pos (norm_pos_iff.mpr ha) 2) t ⟨ht, le_rfl⟩
      rw [h0, norm_zero] at this
      norm_num at this
    have hup : Tendsto (fun t => |‖φ t‖ - radius p|) atTop (𝓝 0) := by
      have := (hnorm.sub_const (radius p)).abs
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun t => Metric.infDist_nonneg)
      (eventually_atTop.mpr ⟨a, fun t ht => infDist_sphere_le (hpos t ht) hrpos.le⟩) hup

/-- Subcritical truncation (`μ < 0`, `l₁ > 0`): the circle `R = √(−μ/l₁)` is repelling — the
deviation `|1/‖x‖² − 1/R²|` grows like `e^{2|μ|(t−a)}`. -/
@[powerlib_foundation] theorem subcritical_repelling (p : Params) (hμ : p.μ < 0)
    {φ : ℝ → State 2} {a b : ℝ} (hφ : IsTrajectoryOn φ (field p) a b) (ha : φ a ≠ 0) :
    ∀ t ∈ Icc a b, |1 / ‖φ t‖ ^ 2 - 1 / (-p.μ / p.l₁)| =
      |1 / ‖φ a‖ ^ 2 - 1 / (-p.μ / p.l₁)| * Real.exp (2 * |p.μ| * (t - a)) :=
  Logistic.deviation_growth hμ (normSq_isIntegralCurveOn p hφ) (pow_pos (norm_pos_iff.mpr ha) 2)

/-- Subcritical truncation: forward-complete solutions starting inside the unstable cycle
converge to the origin. -/
@[powerlib_foundation] theorem subcritical_inside_tendsto_zero (p : Params) (hμ : p.μ < 0)
    (hl : 0 < p.l₁) {φ : ℝ → State 2} {a : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => field p x) (Ici a)) (ha : φ a ≠ 0)
    (hin : ‖φ a‖ < radius p) :
    Tendsto φ atTop (𝓝 0) := by
  have hR : 0 < -p.μ / p.l₁ := div_pos (by linarith) hl
  have hin2 : ‖φ a‖ ^ 2 < -p.μ / p.l₁ := by
    rw [← radius_sq p hR.le]
    exact pow_lt_pow_left₀ hin (norm_nonneg _) two_ne_zero
  have hρ := Logistic.tendsto_zero_of_lt_level hμ hl (normSq_isIntegralCurveOn p hφ)
    (pow_pos (norm_pos_iff.mpr ha) 2) hin2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto _).comp hρ
  simp only [Real.sqrt_zero] at this
  refine this.congr (fun t => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

end powerlib.NormalForm.Hopf
