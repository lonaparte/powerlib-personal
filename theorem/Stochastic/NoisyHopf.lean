import theorem.Stochastic.SmallNoise
import theorem.NormalForm.HopfRadialRate

/-! # The noisy Hopf normal form: global solutions, small-noise expansion, limit-cycle frame

The Hopf normal form with additive noise `dz = ((μ + iω₀) z + (l₁ + iκ) z|z|²) dt + σ dw`
(TR-110 (3-26)/(3-27): `μ = γ`, `ω₀ = ω_h`, `l₁ = −1`, `κ = 0`), read path by path: for `l₁ < 0`
it has a unique solution on every `[0, T]` for every continuous noise path, its solutions satisfy
the uniform small-noise expansion `z_σ = z₀ + σ ζ + O(σ²)`, and along the limit cycle the
variational matrix in the co-rotating frame is constant: `diag(−2γ, 0)` for (3-26), the
linearization behind the amplitude–phase model (3-28).

Model boundary.
* State `x = (x₀, x₁) ∈ State 2` (`z = x₀ + i x₁`), the truncated normal form `Hopf.field p` of
  `theorem/NormalForm/Hopf.lean` with constant parameters `p = ⟨μ, ω₀, l₁, κ⟩`, no `O(|z|⁴)`
  remainder; additive noise `σ w(t)` with a continuous path `w : ℝ → State 2` (two noise
  components, as `σ(ξ_x, ξ_y)` in (3-27)); continuous time, horizon `[0, T]`. The SDE is read as
  its integral equation path by path (`theorem/Stochastic/SmallNoise.lean`); no Itô calculus.
* Supercritical case `l₁ < 0` for existence and the expansion; the cycle identities need
  `l₁ ≠ 0`, `−μ/l₁ ≥ 0` (cycle radius `R = √(−μ/l₁)`, frequency `Ω = ω₀ + κR²`).
* A normal form, not an engineering model: no model family; public foundation.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.1, eqs. (3-26)
(`ż = (γ + iω_h)z − |z|²z + σξ`), (3-27) (Cartesian form) and (3-28)
(`z ≈ (√γ + p) e^{iφ}`, `ṗ = −2γp + σ_p ξ_p`, `φ̇ = ω_h + (σ_φ/√γ) ξ_φ`).

Corrections and sharpenings.
* (3-28) is a first-order (small-noise) statement: the exact content proved here is the uniform
  expansion `‖z_σ − z₀ − σζ‖ ≤ Cσ²` (`noisyHopf_expansion`) together with the constant
  co-rotating variational matrix `[[−2μ, 0], [2κR², 0]]` (`corotating_jac_cycle`), which is
  `diag(−2γ, 0)` for (3-26) (`tr110_corotating_jac`). For a normal form with `κ ≠ 0` the radial
  perturbation drives the phase (`2κR²`), so the phase is not a Brownian motion independent of the
  amplitude; independence of `p` and `φ` in (3-28) uses `κ = 0`.

Results.
* `norm_field_le` — `‖f(z)‖ ≤ (|μ| + |ω₀|)‖z‖ + (|l₁| + |κ|)‖z‖³`; `inner_field_add_le` — for
  `l₁ < 0`, `⟪y, f(y + e)⟫ ≤ K‖y‖² + K'` for `‖e‖ ≤ m` (dissipativity under bounded noise).
* `existsUnique_noisyHopf` — for `l₁ < 0`, existence and uniqueness of the solution on `[0, T]`
  for every continuous noise path (no blow-up).
* `noisyHopf_expansion` — the noise-free solution `x₀`, the variational solution `ζ`, and the
  uniform expansion `x_σ = x₀ + σζ + O(σ²)` on `[0, T]` for `|σ| ≤ σ₀`.
* `jac`, `hasFDerivAt_field`, `fderiv_field` — the Jacobian matrix at every point (extending
  `Hopf.fderiv_field_zero`).
* `rot`, `rot_neg_mul_rot`, `rot_mul_rot_neg`; `jac_cycle` — along the cycle,
  `f'(x₀(t)) = rot(Ωt) [[−2μ, 0], [2κR², 0]] rot(−Ωt) + Ω J`; `corotating_jac_cycle` — the
  co-rotating variational matrix is the constant `[[−2μ, 0], [2κR², 0]]`;
  `tr110_corotating_jac` — for (3-26), `diag(−2γ, 0)` (radius `√γ`, frequency `ω_h` from
  `Hopf.tr110_limitCycle`).
-/

noncomputable section
namespace powerlib.Stochastic.NoisyHopf

open Set Filter Topology Matrix
open powerlib.Dynamics (State)
open powerlib.PhasePlane powerlib.NormalForm.Hopf

/-! ## A priori bound of the supercritical normal form under additive noise -/

@[tmio T, powerlib_foundation] private theorem inner_two (x y : State 2) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- `‖f(z)‖² = (μ² + ω₀²)ρ + 2(μl₁ + ω₀κ)ρ² + (l₁² + κ²)ρ³`, `ρ = ‖z‖²`. -/
@[tmio M, powerlib_foundation] private theorem norm_field_sq (p : Params) (z : State 2) :
    ‖field p z‖ ^ 2 = (p.μ ^ 2 + p.ω₀ ^ 2) * ‖z‖ ^ 2 +
      2 * (p.μ * p.l₁ + p.ω₀ * p.κ) * (‖z‖ ^ 2) ^ 2 + (p.l₁ ^ 2 + p.κ ^ 2) * (‖z‖ ^ 2) ^ 3 := by
  rw [norm_sq_eq, norm_sq_eq, field_apply_zero, field_apply_one]
  ring

/-- Polynomial growth of the field: `‖f(z)‖ ≤ (|μ| + |ω₀|)‖z‖ + (|l₁| + |κ|)‖z‖³`. -/
@[tmio M, powerlib_foundation] theorem norm_field_le (p : Params) (z : State 2) :
    ‖field p z‖ ≤ (|p.μ| + |p.ω₀|) * ‖z‖ + (|p.l₁| + |p.κ|) * ‖z‖ ^ 3 := by
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg _
  have hrhs : 0 ≤ (|p.μ| + |p.ω₀|) * r + (|p.l₁| + |p.κ|) * r ^ 3 := by positivity
  refine (sq_le_sq₀ (norm_nonneg _) hrhs).1 ?_
  rw [norm_field_sq]
  have h1 : p.μ ^ 2 + p.ω₀ ^ 2 ≤ (|p.μ| + |p.ω₀|) ^ 2 := by
    nlinarith [abs_nonneg p.μ, abs_nonneg p.ω₀, sq_abs p.μ, sq_abs p.ω₀]
  have h2 : p.μ * p.l₁ + p.ω₀ * p.κ ≤ (|p.μ| + |p.ω₀|) * (|p.l₁| + |p.κ|) := by
    have := abs_mul p.μ p.l₁
    have := abs_mul p.ω₀ p.κ
    nlinarith [le_abs_self (p.μ * p.l₁), le_abs_self (p.ω₀ * p.κ), abs_nonneg p.μ,
      abs_nonneg p.ω₀, abs_nonneg p.l₁, abs_nonneg p.κ]
  have h3 : p.l₁ ^ 2 + p.κ ^ 2 ≤ (|p.l₁| + |p.κ|) ^ 2 := by
    nlinarith [abs_nonneg p.l₁, abs_nonneg p.κ, sq_abs p.l₁, sq_abs p.κ]
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hr4 : 0 ≤ r ^ 4 := by positivity
  have hr6 : 0 ≤ r ^ 6 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 hr2, mul_le_mul_of_nonneg_right h2 hr4,
    mul_le_mul_of_nonneg_right h3 hr6]

/-- `−c r⁴ + q r³ ≤ q⁴/c³` for `c > 0`, `q, r ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem quartic_le {c q r : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (hr : 0 ≤ r) : -c * r ^ 4 + q * r ^ 3 ≤ q ^ 4 / c ^ 3 := by
  have hrhs : 0 ≤ q ^ 4 / c ^ 3 := by positivity
  rcases le_or_gt q (c * r) with h | h
  · nlinarith [pow_nonneg hr 3]
  · have hrq : r ≤ q / c := by rw [le_div_iff₀ hc]; linarith
    have h3 : r ^ 3 ≤ (q / c) ^ 3 := pow_le_pow_left₀ hr hrq 3
    have h4 : q * r ^ 3 ≤ q ^ 4 / c ^ 3 := by
      calc q * r ^ 3 ≤ q * (q / c) ^ 3 := mul_le_mul_of_nonneg_left h3 hq
        _ = q ^ 4 / c ^ 3 := by rw [div_pow]; ring
    nlinarith [pow_nonneg hr 4]

/-- **Dissipativity of the supercritical normal form under bounded perturbation**: for `l₁ < 0`
and every `m`, there are `K, K' ≥ 0` with `⟪y, f(y + e)⟫ ≤ K‖y‖² + K'` whenever `‖e‖ ≤ m`. The cubic
term `l₁ ‖z‖⁴` dominates every perturbation of the noise. -/
@[tmio M, powerlib_foundation] theorem inner_field_add_le (p : Params) (hl : p.l₁ < 0) (m : ℝ) :
    ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧
      ∀ y e : State 2, ‖e‖ ≤ m → inner ℝ y (field p (y + e)) ≤ K * ‖y‖ ^ 2 + K' := by
  set m' := max m 0
  set a := |p.μ| + |p.ω₀|
  set b := |p.l₁| + |p.κ|
  set c := -p.l₁
  have hc : 0 < c := by simp [c]; linarith
  have hm' : 0 ≤ m' := le_max_right _ _
  refine ⟨2 * |p.μ| + 1, (2 * |p.μ| + 1) * m' ^ 2 + (m' * a) ^ 2 / 2 + (m' * b) ^ 4 / c ^ 3,
    by positivity, by positivity, fun y e he => ?_⟩
  have he' : ‖e‖ ≤ m' := he.trans (le_max_left _ _)
  set z := y + e
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg _
  -- `⟪y, f z⟫ = ⟪z, f z⟫ − ⟪e, f z⟫`
  have hyz : y = z - e := by simp [z]
  have hinner : inner ℝ y (field p z) = (p.μ * r ^ 2 + p.l₁ * (r ^ 2) ^ 2) -
      inner ℝ e (field p z) := by
    rw [hyz, inner_sub_left, inner_two z, radial_identity, ← norm_sq_eq]
  have hcs : -inner ℝ e (field p z) ≤ m' * (a * r + b * r ^ 3) := by
    have h1 := neg_le_abs (inner ℝ e (field p z))
    have h2 := abs_real_inner_le_norm e (field p z)
    have h3 : ‖e‖ * ‖field p z‖ ≤ m' * (a * r + b * r ^ 3) :=
      mul_le_mul he' (norm_field_le p z) (norm_nonneg _) hm'
    linarith
  have hq := quartic_le hc (by positivity : 0 ≤ m' * b) hr
  have ham : m' * a * r ≤ (m' * a) ^ 2 / 2 + r ^ 2 / 2 := by nlinarith [sq_nonneg (m' * a - r)]
  have hμ : p.μ * r ^ 2 ≤ |p.μ| * r ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have hr2 : r ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * m' ^ 2 := by
    have h1 : r ≤ ‖y‖ + m' := (norm_add_le _ _).trans (add_le_add le_rfl he')
    nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - m')]
  have hμ0 : 0 ≤ |p.μ| := abs_nonneg _
  rw [hinner]
  have hl₁ : p.l₁ * (r ^ 2) ^ 2 = -c * r ^ 4 := by rw [show c = -p.l₁ from rfl]; ring
  rw [hl₁]
  nlinarith [mul_le_mul_of_nonneg_left hr2 (by positivity : (0 : ℝ) ≤ |p.μ| + 1 / 2)]

/-! ## Global existence, uniqueness and the small-noise expansion -/

/-- **The noisy supercritical normal form has a unique solution on every `[0, T]`.** For
`l₁ < 0`, every continuous noise path `w`, every `σ` and every initial state `a`, the integral
equation `x(t) = a + ∫₀ᵗ f(x(s)) ds + σ(w(t) − w(0))` of `dx = f(x) dt + σ dw` (TR-110 (3-26)/(3-27)
for `tr110Params`) has a continuous solution on `[0, T]`, and any two coincide there: no blow-up
for any noise path. -/
@[tmio M, powerlib_foundation] theorem existsUnique_noisyHopf (p : Params) (hl : p.l₁ < 0)
    (a : State 2) (σ : ℝ) {w : ℝ → State 2} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x : ℝ → State 2, Continuous x ∧
      (∀ t ∈ Icc 0 T, x t = a + (∫ s in (0 : ℝ)..t, field p (x s)) + σ • (w t - w 0)) ∧
      ∀ x' : ℝ → State 2, Continuous x' →
        (∀ t ∈ Icc 0 T, x' t = a + (∫ s in (0 : ℝ)..t, field p (x' s)) + σ • (w t - w 0)) →
        EqOn x' x (Icc 0 T) := by
  obtain ⟨x, hx, hxeq⟩ := SmallNoise.exists_additiveNoise (field_contDiff p)
    (inner_field_add_le p hl) a σ hw hT
  exact ⟨x, hx, hxeq, fun x' hx' hx'eq =>
    SmallNoise.eqOn_of_additiveNoise (field_contDiff p) hx' hx hx'eq hxeq⟩

/-- **Small-noise expansion of the noisy normal form** (the rigorous content of the
linearization behind (3-28)): for `l₁ < 0`, let `x₀` be the noise-free solution from `a` and `ζ`
the solution of the variational equation `ζ(t) = ∫₀ᵗ f'(x₀(s)) ζ(s) ds + (w(t) − w(0))`. Then
`x_σ = x₀ + σ ζ + O(σ²)` uniformly on `[0, T]`. -/
@[tmio M, powerlib_foundation] theorem noisyHopf_expansion (p : Params) (hl : p.l₁ < 0)
    (a : State 2) {w : ℝ → State 2} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x₀ ζ : ℝ → State 2, Continuous x₀ ∧ Continuous ζ ∧
      (∀ t ∈ Icc 0 T, x₀ t = a + ∫ s in (0 : ℝ)..t, field p (x₀ s)) ∧
      (∀ t ∈ Icc 0 T, ζ t = (∫ s in (0 : ℝ)..t, fderiv ℝ (field p) (x₀ s) (ζ s)) + (w t - w 0)) ∧
      ∃ σ₀ > 0, ∃ C, ∀ σ : ℝ, |σ| ≤ σ₀ → ∀ x : ℝ → State 2, Continuous x →
        (∀ t ∈ Icc 0 T, x t = a + (∫ s in (0 : ℝ)..t, field p (x s)) + σ • (w t - w 0)) →
        ∀ t ∈ Icc 0 T, ‖x t - x₀ t - σ • ζ t‖ ≤ C * σ ^ 2 := by
  obtain ⟨x₀, hx₀, hx₀eq⟩ := SmallNoise.exists_additiveNoise (field_contDiff p)
    (inner_field_add_le p hl) a 0 hw hT
  have hx₀eq' : ∀ t ∈ Icc 0 T, x₀ t = a + ∫ s in (0 : ℝ)..t, field p (x₀ s) := fun t ht => by
    rw [hx₀eq t ht, zero_smul, add_zero]
  obtain ⟨ζ, hζ, hζeq⟩ := SmallNoise.exists_variational (field_contDiff p) hx₀ hw hT
  exact ⟨x₀, ζ, hx₀, hζ, hx₀eq', hζeq,
    SmallNoise.norm_sub_sub_smul_le (field_contDiff p) hw hx₀ hx₀eq' hζ hζeq⟩

/-! ## The variational matrix along the limit cycle -/

/-- The Jacobian matrix of the normal form at `x`. -/
def jac (p : Params) (x : State 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.μ + p.l₁ * (3 * x 0 ^ 2 + x 1 ^ 2) - 2 * p.κ * x 0 * x 1,
      -p.ω₀ + 2 * p.l₁ * x 0 * x 1 - p.κ * (x 0 ^ 2 + 3 * x 1 ^ 2);
    p.ω₀ + p.κ * (3 * x 0 ^ 2 + x 1 ^ 2) + 2 * p.l₁ * x 0 * x 1,
      p.μ + 2 * p.κ * x 0 * x 1 + p.l₁ * (x 0 ^ 2 + 3 * x 1 ^ 2)]

@[tmio M, powerlib_foundation] theorem hasFDerivAt_field (p : Params) (x : State 2) :
    HasFDerivAt (field p) (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jac p x)) x := by
  have h0 := Dynamics.hasFDerivAt_coord 0 x
  have h1 := Dynamics.hasFDerivAt_coord 1 x
  have hρ : HasFDerivAt (fun y : State 2 => y 0 ^ 2 + y 1 ^ 2) _ x := (h0.pow 2).add (h1.pow 2)
  have hF0 : HasFDerivAt (fun y : State 2 =>
      p.μ * y 0 - p.ω₀ * y 1 + (p.l₁ * y 0 - p.κ * y 1) * (y 0 ^ 2 + y 1 ^ 2)) _ x :=
    ((h0.const_mul p.μ).sub (h1.const_mul p.ω₀)).add
      (((h0.const_mul p.l₁).sub (h1.const_mul p.κ)).mul hρ)
  have hF1 : HasFDerivAt (fun y : State 2 =>
      p.ω₀ * y 0 + p.μ * y 1 + (p.κ * y 0 + p.l₁ * y 1) * (y 0 ^ 2 + y 1 ^ 2)) _ x :=
    ((h0.const_mul p.ω₀).add (h1.const_mul p.μ)).add
      (((h0.const_mul p.κ).add (h1.const_mul p.l₁)).mul hρ)
  have e0 : (fun y => field p y 0) = fun y : State 2 =>
      p.μ * y 0 - p.ω₀ * y 1 + (p.l₁ * y 0 - p.κ * y 1) * (y 0 ^ 2 + y 1 ^ 2) := funext fun _ => rfl
  have e1 : (fun y => field p y 1) = fun y : State 2 =>
      p.ω₀ * y 0 + p.μ * y 1 + (p.κ * y 0 + p.l₁ * y 1) * (y 0 ^ 2 + y 1 ^ 2) := funext fun _ => rfl
  refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
    (fun i => fderiv ℝ (fun y => field p y i) x) (fun i => ?_) ?_
  · fin_cases i
    · show HasFDerivAt (fun y => field p y 0) _ x
      rw [e0]; exact hF0.differentiableAt.hasFDerivAt
    · show HasFDerivAt (fun y => field p y 1) _ x
      rw [e1]; exact hF1.differentiableAt.hasFDerivAt
  · intro i v
    rw [Fin.sum_univ_two]
    fin_cases i
    · show fderiv ℝ (fun y => field p y 0) x v = _
      rw [e0, hF0.fderiv]
      simp [jac]
      ring
    · show fderiv ℝ (fun y => field p y 1) x v = _
      rw [e1, hF1.fderiv]
      simp [jac]
      ring

@[tmio M, powerlib_foundation] theorem fderiv_field (p : Params) (x : State 2) :
    fderiv ℝ (field p) x = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jac p x) :=
  (hasFDerivAt_field p x).fderiv

/-- The rotation by the angle `θ`. -/
def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- **The variational matrix along the cycle.** On the cycle `R(cos Ωt, sin Ωt)`,
`R² = −μ/l₁`, `Ω = ω₀ + κR²`, the Jacobian is the frame rotation `Ω J` plus the rotated constant
matrix `D = [[−2μ, 0], [2κR², 0]]` (radial relaxation `−2μ`, amplitude-to-phase coupling
`2κR²`, neutral phase). -/
@[tmio M, powerlib_foundation] theorem jac_cycle (p : Params) (hl : p.l₁ ≠ 0)
    (hR : 0 ≤ -p.μ / p.l₁) (t : ℝ) :
    jac p (cycle p t) = rot (frequency p * t) * !![-2 * p.μ, 0; 2 * p.κ * radius p ^ 2, 0] *
      rot (-(frequency p * t)) + frequency p • !![0, -1; 1, 0] := by
  have hR2 : p.l₁ * radius p ^ 2 + p.μ = 0 := by rw [radius_sq p hR]; field_simp; ring
  have hΩ : frequency p = p.ω₀ + p.κ * radius p ^ 2 := by rw [radius_sq p hR]; rfl
  have hsc : Real.sin (frequency p * t) ^ 2 + Real.cos (frequency p * t) ^ 2 - 1 = 0 := by
    rw [Real.sin_sq_add_cos_sq]; ring
  set c := Real.cos (frequency p * t)
  set s := Real.sin (frequency p * t)
  set R := radius p
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jac, rot, cycle, Real.cos_neg, Real.sin_neg, R]
  · linear_combination (3 * c ^ 2 + s ^ 2) * hR2 - p.μ * hsc
  · linear_combination 2 * c * s * hR2 - p.κ * R ^ 2 * hsc + hΩ
  · linear_combination 2 * c * s * hR2 + p.κ * R ^ 2 * hsc - hΩ
  · linear_combination (c ^ 2 + 3 * s ^ 2) * hR2 - p.μ * hsc

@[tmio T, powerlib_foundation] theorem rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, Real.cos_neg, Real.sin_neg] <;> nlinarith [h]

@[tmio T, powerlib_foundation] theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  simpa using rot_neg_mul_rot (-θ)

/-- **In the co-rotating frame the variational matrix is constant**:
`rot(−Ωt) (f'(x₀(t)) − Ω J) rot(Ωt) = [[−2μ, 0], [2κR², 0]]` along the cycle `x₀ = cycle p`. -/
@[tmio M, powerlib_foundation] theorem corotating_jac_cycle (p : Params) (hl : p.l₁ ≠ 0)
    (hR : 0 ≤ -p.μ / p.l₁) (t : ℝ) :
    rot (-(frequency p * t)) * (jac p (cycle p t) - frequency p • !![0, -1; 1, 0]) *
      rot (frequency p * t) = !![-2 * p.μ, 0; 2 * p.κ * radius p ^ 2, 0] := by
  rw [jac_cycle p hl hR t, add_sub_cancel_right, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    rot_neg_mul_rot, Matrix.one_mul, Matrix.mul_assoc, rot_neg_mul_rot, Matrix.mul_one]

/-- **TR-110 (3-26)–(3-28), limit-cycle frame.** For `ż = (γ + iω_h)z − |z|²z`, `γ > 0`, along
the cycle `√γ (cos ω_h t, sin ω_h t)` the co-rotating variational matrix is `diag(−2γ, 0)`: the
radial perturbation relaxes at the rate `2γ` (the OU rate of `p` in (3-28)) and the phase is
neutral (the Brownian phase `φ` of (3-28)). -/
@[tmio M, powerlib_foundation] theorem tr110_corotating_jac {γ : ℝ} (hγ : 0 < γ) (ωh t : ℝ) :
    rot (-(ωh * t)) * (jac (tr110Params γ ωh) (cycle (tr110Params γ ωh) t) -
      ωh • !![0, -1; 1, 0]) * rot (ωh * t) = !![-2 * γ, 0; 0, 0] := by
  obtain ⟨-, hfreq, -⟩ := tr110_limitCycle hγ ωh
  have h := corotating_jac_cycle (tr110Params γ ωh) (by simp [tr110Params])
    (by simp [tr110Params]; exact hγ.le) t
  rw [hfreq] at h
  rw [h]
  simp [tr110Params]

end powerlib.Stochastic.NoisyHopf
