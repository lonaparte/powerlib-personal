import dependencies.Mathlib
import theorem.Attributes

/-! # The overdamped washboard (Adler equation) `θ̇ = B − A sin θ`

Equilibrium existence, Adler's period formula and the mean running velocity of the canonical
scalar phase equation (overdamped tilted washboard); not a power-system model.

Model boundary.
* Scalar phase `θ ∈ ℝ` (unwrapped), constant real parameters `A` (restoring amplitude) and `B`
  (tilt / frequency mismatch), continuous time: `θ̇ = B − A sin θ = −V'(θ)` with
  `V(θ) = −A cos θ − Bθ`. No inertia, noise or input.
* A canonical textbook system: no model family; foundation results.

Source: work-sync theory/T-nonlinear-phase-plane.md §1.5 (washboard; `B > A` ⇒ no barrier,
monotone running) and its code check "Adler running velocity = √(B² − A²)".

Results.
* `adler_equilibrium_iff`: an equilibrium exists iff `|B| ≤ |A|` (for `A > 0`: iff `|B| ≤ A`).
* `hasDerivAt_adlerPrimitive`: for `B > |A|`, with `s = √(B² − A²)`, the smooth function
  `G(θ) = (θ − 2 arctan(A cos θ / (B + s − A sin θ)))/s` satisfies `G' = 1/(B − A sin θ)` on
  all of `ℝ`, and `G(θ + 2π) = G(θ) + 2π/s` (`adlerPrimitive_add_two_pi`).
* `adler_integral` (Adler's formula): `∫₀^{2π} dθ/(B − A sin θ) = 2π/√(B² − A²)`.
* Running solutions (`B > |A|`): along every solution, `G(θ(t)) − t` is constant
  (`adler_time`); the time needed to advance by `2π` is exactly `T = 2π/√(B² − A²)`
  (`adler_slip_time`); `|θ(t) − θ(0) − √(B² − A²) t| ≤ 2π` (`adler_deviation`), hence the
  average angular velocity is `lim θ(t)/t = √(B² − A²)` (`adler_mean_velocity`).

Potential shapes: `V(θ) = −A cos θ − Bθ` is the washboard of `theorem/Potential/Wells.lean`
(`V₀ = A`, `α = B/A`); for `|B| < A` its barriers are those of `theorem/Potential/Barrier.lean`
with `φ = 0`, `c = B`.
-/

noncomputable section
namespace powerlib.PhasePlane.Adler

open Real Filter Topology

/-- An equilibrium of `θ̇ = B − A sin θ` exists iff `|B| ≤ |A|`. -/
@[powerlib_foundation] theorem adler_equilibrium_iff (A B : ℝ) :
    (∃ θ, B - A * Real.sin θ = 0) ↔ |B| ≤ |A| := by
  constructor
  · rintro ⟨θ, h⟩
    have hB : B = A * Real.sin θ := by linarith
    rw [hB, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg A) (abs_sin_le_one θ)
  · intro h
    rcases eq_or_ne A 0 with hA | hA
    · subst hA
      simp only [abs_zero] at h
      exact ⟨0, by simp [abs_nonpos_iff.mp h]⟩
    · refine ⟨Real.arcsin (B / A), ?_⟩
      have h1 : |B / A| ≤ 1 := by
        rw [abs_div, div_le_one (abs_pos.mpr hA)]; exact h
      rw [Real.sin_arcsin (by linarith [neg_abs_le (B / A), abs_le.mp h1])
        (abs_le.mp h1).2]
      field_simp; ring

variable {A B : ℝ}

/-- `s = √(B² − A²)`. -/
def rate (A B : ℝ) : ℝ := √(B ^ 2 - A ^ 2)

/-- The smooth primitive `G(θ) = (θ − 2 arctan(A cos θ / (B + s − A sin θ)))/s`. -/
def adlerPrimitive (A B θ : ℝ) : ℝ :=
  (θ - 2 * Real.arctan (A * Real.cos θ / (B + rate A B - A * Real.sin θ))) / rate A B

@[powerlib_foundation] theorem rate_pos (h : |A| < B) : 0 < rate A B := by
  apply Real.sqrt_pos.mpr
  have := abs_nonneg A
  nlinarith [sq_abs A]

@[powerlib_foundation] theorem rate_sq (h : |A| < B) : rate A B ^ 2 = B ^ 2 - A ^ 2 :=
  Real.sq_sqrt (by have := abs_nonneg A; nlinarith [sq_abs A])

@[powerlib_foundation] theorem denom_pos (h : |A| < B) (θ : ℝ) : 0 < B - A * Real.sin θ := by
  have : A * Real.sin θ ≤ |A| := by
    calc A * Real.sin θ ≤ |A * Real.sin θ| := le_abs_self _
      _ = |A| * |Real.sin θ| := abs_mul _ _
      _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one θ) (abs_nonneg A)
      _ = |A| := mul_one _
  linarith

@[powerlib_foundation] theorem hasDerivAt_adlerPrimitive (h : |A| < B) (θ : ℝ) :
    HasDerivAt (adlerPrimitive A B) (1 / (B - A * Real.sin θ)) θ := by
  have hs := rate_pos h
  have hs2 := rate_sq h
  set s := rate A B
  have hd : 0 < B - A * Real.sin θ := denom_pos h θ
  have hD : 0 < B + s - A * Real.sin θ := by linarith
  -- derivative of the arctan argument
  have hu : HasDerivAt (fun θ => A * Real.cos θ / (B + s - A * Real.sin θ))
      ((-(A * Real.sin θ) * (B + s - A * Real.sin θ) - A * Real.cos θ * (-(A * Real.cos θ))) /
        (B + s - A * Real.sin θ) ^ 2) θ := by
    have h1 : HasDerivAt (fun θ => A * Real.cos θ) (-(A * Real.sin θ)) θ := by
      simpa using (Real.hasDerivAt_cos θ).const_mul A
    have h2 : HasDerivAt (fun θ => B + s - A * Real.sin θ) (-(A * Real.cos θ)) θ := by
      simpa using ((Real.hasDerivAt_sin θ).const_mul A).const_sub (B + s)
    exact h1.div h2 hD.ne'
  have hG := ((hasDerivAt_id θ).sub ((hu.arctan).const_mul 2)).div_const s
  convert hG using 1
  · rfl
  -- algebra: `(1 − 2 u'/(1 + u²))/s = 1/(B − A sin θ)`
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by rw [← Real.sin_sq_add_cos_sq θ]; ring
  have key : 1 + (A * Real.cos θ / (B + s - A * Real.sin θ)) ^ 2 =
      2 * (B + s) * (B - A * Real.sin θ) / (B + s - A * Real.sin θ) ^ 2 := by
    field_simp
    rw [hc]
    nlinarith [hs2]
  rw [key]
  have hA2 : A ^ 2 = B ^ 2 - s ^ 2 := by linarith
  have hnum : -(A * Real.sin θ) * (B + s - A * Real.sin θ) - A * Real.cos θ * (-(A * Real.cos θ)) =
      B ^ 2 - s ^ 2 - A * Real.sin θ * (B + s) := by
    have : A * Real.cos θ * (-(A * Real.cos θ)) = -(A ^ 2 * Real.cos θ ^ 2) := by ring
    rw [this, hc, ← hA2]; ring
  rw [hnum]
  have hBs : 0 < B + s := by have := abs_nonneg A; linarith
  field_simp
  ring

/-- `G(θ + 2π) = G(θ) + 2π/s`. -/
@[powerlib_foundation] theorem adlerPrimitive_add_two_pi (θ : ℝ) :
    adlerPrimitive A B (θ + 2 * π) = adlerPrimitive A B θ + 2 * π / rate A B := by
  simp only [adlerPrimitive, Real.cos_add_two_pi, Real.sin_add_two_pi]
  ring

/-- Adler's formula: `∫₀^{2π} dθ/(B − A sin θ) = 2π/√(B² − A²)` for `B > |A|`. -/
@[powerlib_foundation] theorem adler_integral (h : |A| < B) :
    ∫ θ in (0 : ℝ)..(2 * π), 1 / (B - A * Real.sin θ) = 2 * π / √(B ^ 2 - A ^ 2) := by
  have hcont : Continuous fun θ => 1 / (B - A * Real.sin θ) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro θ; exact (denom_pos h θ).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_adlerPrimitive h θ) (hcont.intervalIntegrable _ _)]
  rw [show (2 * π : ℝ) = 0 + 2 * π by ring, adlerPrimitive_add_two_pi]
  simp only [rate]
  ring

/-- Along every solution of `θ̇ = B − A sin θ` (`B > |A|`), `G(θ(t)) − t` is constant. -/
@[powerlib_foundation] theorem adler_time (h : |A| < B) {θ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (B - A * Real.sin (θ t)) t) (t : ℝ) :
    adlerPrimitive A B (θ t) = t + adlerPrimitive A B (θ 0) := by
  have hd : ∀ t, HasDerivAt (fun t => adlerPrimitive A B (θ t) - t) 0 t := by
    intro t
    have h1 := (hasDerivAt_adlerPrimitive h (θ t)).comp t (hθ t)
    have h2 := h1.sub (hasDerivAt_id t)
    convert h2 using 1
    · rfl
    rw [one_div, inv_mul_cancel₀ (denom_pos h (θ t)).ne']; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  simp only [sub_zero] at hc
  linarith

/-- The slip time: the solution advances by `2π` in exactly `T = 2π/√(B² − A²)`. -/
@[powerlib_foundation] theorem adler_slip_time (h : |A| < B) {θ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (B - A * Real.sin (θ t)) t) {t₁ t₂ : ℝ}
    (h12 : θ t₂ = θ t₁ + 2 * π) : t₂ - t₁ = 2 * π / √(B ^ 2 - A ^ 2) := by
  have e1 := adler_time h hθ t₁
  have e2 := adler_time h hθ t₂
  rw [h12, adlerPrimitive_add_two_pi] at e2
  simp only [rate] at e2
  linarith

/-- Bounded deviation from uniform rotation: `|θ(t) − θ(0) − √(B² − A²) t| ≤ 2π`. -/
@[powerlib_foundation] theorem adler_deviation (h : |A| < B) {θ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (B - A * Real.sin (θ t)) t) (t : ℝ) :
    |θ t - θ 0 - √(B ^ 2 - A ^ 2) * t| ≤ 2 * π := by
  have e := adler_time h hθ t
  have hs := rate_pos h
  simp only [adlerPrimitive] at e
  set s := rate A B
  set a₁ := Real.arctan (A * Real.cos (θ t) / (B + s - A * Real.sin (θ t)))
  set a₀ := Real.arctan (A * Real.cos (θ 0) / (B + s - A * Real.sin (θ 0)))
  have e' : θ t - θ 0 - s * t = 2 * a₁ - 2 * a₀ := by
    field_simp at e; linarith
  have hs' : √(B ^ 2 - A ^ 2) = s := rfl
  rw [hs', e']
  have h1 := Real.neg_pi_div_two_lt_arctan (A * Real.cos (θ t) / (B + s - A * Real.sin (θ t)))
  have h2 := Real.arctan_lt_pi_div_two (A * Real.cos (θ t) / (B + s - A * Real.sin (θ t)))
  have h3 := Real.neg_pi_div_two_lt_arctan (A * Real.cos (θ 0) / (B + s - A * Real.sin (θ 0)))
  have h4 := Real.arctan_lt_pi_div_two (A * Real.cos (θ 0) / (B + s - A * Real.sin (θ 0)))
  rw [abs_le]
  constructor <;> linarith

/-- The average angular velocity of every running solution is `√(B² − A²)`. -/
@[powerlib_foundation] theorem adler_mean_velocity (h : |A| < B) {θ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (B - A * Real.sin (θ t)) t) :
    Tendsto (fun t => θ t / t) atTop (𝓝 (√(B ^ 2 - A ^ 2))) := by
  set s := √(B ^ 2 - A ^ 2)
  -- θ(t)/t = s + (θ(t) − θ(0) − s t)/t + θ(0)/t
  have hdecomp : ∀ t, t ≠ 0 → θ t / t = s + (θ t - θ 0 - s * t) / t + θ 0 / t := by
    intro t ht; field_simp; ring
  have hb : Tendsto (fun t => (θ t - θ 0 - s * t) / t) atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => 2 * π / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) _ hinv
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht]
    exact div_le_div_of_nonneg_right (adler_deviation h hθ t) ht.le
  have hc : Tendsto (fun t : ℝ => θ 0 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := (tendsto_const_nhds (x := s)).add hb |>.add hc
  rw [add_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (hdecomp t ht.ne').symm

end powerlib.PhasePlane.Adler
