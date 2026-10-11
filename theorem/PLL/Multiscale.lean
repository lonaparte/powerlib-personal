import theorem.PLL.Linear

/-! # SRF-PLL time-scale algebra: slow manifold, reduced slow equation, eigenvalues

Foundation module (algebraic and linear-system facts about the reduction of the SRF-PLL in
T-gfl-multiscale-modeling §1.5; no claim about the accuracy of the reduction itself — the
Tikhonov/Fenichel error estimates are not formalized).

Setting: `(θ, ξ)` coordinates of `theorem/PLL/Model.lean` (`xiField a b Δω`:
`θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`), `a = V K_p`, `b = V K_i`, `Δω = ω_s − ω_g`.

* Slow manifold (quasi-steady state of the `θ` equation with `ξ` frozen): on the domain
  `|Δω + b ξ| < a` the branch `θ*(ξ) = arcsin((Δω + b ξ)/a)` solves `Δω − a sin θ + b ξ = 0`,
  lies in `(−π/2, π/2)`, and has normal Jacobian `∂_θ(Δω − a sin θ + bξ) = −a cos θ* < 0`.
* Reduced slow equation `ξ̇ = −sin θ*(ξ)`: on that domain it equals the linear field
  `−(Δω + b ξ)/a = −(b/a)(ξ − ξ*)`, `ξ* = −Δω/b`; the equilibrium `ξ*` is inside the domain;
  the shifted 1-state LTI model `ẏ = −(b/a) y` is exponentially stable iff `b/a > 0`.
* Eigenvalues of the in-phase linearization `λ² + aλ + b = 0` and the overdamping parameter
  `ε_od = b/a² = 1/(4ζ²)` (`ζ = a/(2√b)`, the `zeta` of `Linear.lean`):
  real roots iff `ε_od ≤ 1/4` (`ζ ≥ 1`); then `λ± = −(a/2)(1 ∓ √(1 − 4ε_od))`,
  `λ₊/λ₋ = 4ε_od/(1 + √(1 − 4ε_od))² ∈ [ε_od, 4ε_od]`, `λ₋ ∈ [−a, −a/2]`,
  `λ₊ ∈ [−2b/a, −b/a]`.

Source: work-sync `theory/T-gfl-multiscale-modeling.md` §1.5, §1.7, §1.8;
`theory/T-invariant-coordinates.md` §1.2 (overdamped limit).

Correction (§1.5): the reduced equation `ξ̇ = −(Δω + V K_i ξ)/(V K_p)` is stated without its
domain; it is valid only where the slow manifold exists, `|Δω + b ξ| < a` (on `|·| = a` the
manifold folds, `cos θ* = 0`, and normal hyperbolicity is lost). Also `ε_od = |λ₊/λ₋|` is not
exactly `b/a²`: the exact ratio is `4ε/(1 + √(1 − 4ε))²`, which lies between `ε` and `4ε`
and is `ε + O(ε²)`.
-/

noncomputable section
namespace powerlib.PLL
open Matrix

/-! ## Slow manifold -/

/-- Slow-manifold branch `θ*(ξ) = arcsin((Δω + b ξ)/a)`. -/
def slowAngle (a b Δω ξ : ℝ) : ℝ := Real.arcsin ((Δω + b * ξ) / a)

@[powerlib_foundation] theorem slowAngle_spec {a b Δω ξ : ℝ} (ha : 0 < a)
    (hdom : |Δω + b * ξ| < a) :
    Δω - a * Real.sin (slowAngle a b Δω ξ) + b * ξ = 0 ∧
      |slowAngle a b Δω ξ| < Real.pi / 2 ∧
      -(a * Real.cos (slowAngle a b Δω ξ)) < 0 := by
  have hx : |(Δω + b * ξ) / a| < 1 := by rw [abs_div, abs_of_pos ha, div_lt_one ha]; exact hdom
  have hx' := abs_lt.mp hx
  have hsin : Real.sin (slowAngle a b Δω ξ) = (Δω + b * ξ) / a :=
    Real.sin_arcsin hx'.1.le hx'.2.le
  have hlt : |slowAngle a b Δω ξ| < Real.pi / 2 :=
    abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arcsin.mpr hx'.1, Real.arcsin_lt_pi_div_two.mpr hx'.2⟩
  have hcos : 0 < Real.cos (slowAngle a b Δω ξ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (slowAngle a b Δω ξ)],
      lt_of_le_of_lt (le_abs_self _) hlt⟩
  refine ⟨?_, hlt, by nlinarith⟩
  rw [hsin]; field_simp; ring

/-- Reduced slow field on the domain: `−sin θ*(ξ) = −(Δω + b ξ)/a = −(b/a)(ξ − ξ*)`,
`ξ* = −Δω/b`. -/
@[powerlib_foundation] theorem reduced_slow_field {a b Δω ξ : ℝ} (ha : 0 < a) (hb : b ≠ 0)
    (hdom : |Δω + b * ξ| < a) :
    -Real.sin (slowAngle a b Δω ξ) = -(b / a) * (ξ - (-Δω / b)) := by
  have hx : |(Δω + b * ξ) / a| < 1 := by rw [abs_div, abs_of_pos ha, div_lt_one ha]; exact hdom
  have hx' := abs_lt.mp hx
  rw [slowAngle, Real.sin_arcsin hx'.1.le hx'.2.le]
  field_simp
  ring

/-- The reduced equilibrium `ξ* = −Δω/b` lies in the slow-manifold domain, with `θ* = 0`. -/
@[powerlib_foundation] theorem reduced_equilibrium_mem {a b Δω : ℝ} (ha : 0 < a) (hb : b ≠ 0) :
    |Δω + b * (-Δω / b)| < a ∧ slowAngle a b Δω (-Δω / b) = 0 := by
  have h0 : Δω + b * (-Δω / b) = 0 := by field_simp; ring
  refine ⟨by rw [h0, abs_zero]; exact ha, ?_⟩
  rw [slowAngle, h0, zero_div, Real.arcsin_zero]

/-- The shifted reduced slow model `ẏ = −(b/a) y` (`y = ξ − ξ*`). -/
def reducedModel (a b : ℝ) : LTI.AutonomousModel 1 := ⟨!![-(b / a)]⟩

/-- The reduced slow model is exponentially stable iff `b/a > 0`. -/
@[powerlib_foundation] theorem reducedModel_exponentiallyStable_iff (a b : ℝ) :
    LTI.ExponentiallyStable (reducedModel a b) ↔ 0 < b / a := by
  rw [LTI.exponentiallyStable_iff_spectrallyStable]
  have hdet : ∀ s : ℂ, (LTI.characteristicMatrix (reducedModel a b).A s).det =
      s + ((b / a : ℝ) : ℂ) := by
    intro s
    simp [LTI.characteristicMatrix, reducedModel]
  constructor
  · intro h
    have := h (-((b / a : ℝ) : ℂ)) (by rw [hdet]; ring)
    simpa using this
  · intro h s hs
    rw [hdet] at hs
    have : s = -((b / a : ℝ) : ℂ) := by linear_combination hs
    rw [this]; simpa using h

/-! ## Eigenvalues and the overdamping parameter -/

/-- `ε_od = b/a² = 1/(4ζ²)` with `ζ = a/(2√b)` (`a = V K_p`, `b = V K_i > 0`, `a ≠ 0`). -/
@[powerlib_foundation] theorem epsOd_eq {V Kp Ki : ℝ} (ha : V * Kp ≠ 0) (hb : 0 < V * Ki) :
    V * Ki / (V * Kp) ^ 2 = 1 / (4 * zeta V Kp Ki ^ 2) := by
  have hsq : omegaN V Ki ^ 2 = V * Ki := Real.sq_sqrt hb.le
  have h2 : (2 * omegaN V Ki) ^ 2 = 4 * (V * Ki) := by rw [mul_pow, hsq]; norm_num
  have ha2 : (V * Kp) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  rw [zeta, div_pow, h2]
  field_simp

/-- The in-phase eigenvalues are real iff `ε_od ≤ 1/4` (`a ≠ 0`). -/
@[powerlib_foundation] theorem eigen_real_iff {a b : ℝ} (ha : a ≠ 0) :
    0 ≤ a ^ 2 - 4 * b ↔ b / a ^ 2 ≤ 1 / 4 := by
  have ha2 : 0 < a ^ 2 := by positivity
  rw [div_le_iff₀ ha2]
  constructor <;> intro h <;> linarith

/-- Real eigenvalues `λ± = −(a/2)(1 ∓ √(1 − 4ε))`, `ε = b/a²` (`a > 0`, `4b ≤ a²`), roots of
`λ² + aλ + b`. -/
@[powerlib_foundation] theorem eigen_roots {a b : ℝ} (ha : 0 < a) (hd : 4 * b ≤ a ^ 2) :
    let s := Real.sqrt (1 - 4 * (b / a ^ 2))
    (-(a / 2) * (1 - s)) ^ 2 + a * (-(a / 2) * (1 - s)) + b = 0 ∧
      (-(a / 2) * (1 + s)) ^ 2 + a * (-(a / 2) * (1 + s)) + b = 0 := by
  intro s
  have h1 : 0 ≤ 1 - 4 * (b / a ^ 2) := by
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * (b / a ^ 2) := Real.sq_sqrt h1
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hs' : a ^ 2 * s ^ 2 = a ^ 2 - 4 * b := by rw [hs]; field_simp
  constructor
  · linear_combination (1 / 4 : ℝ) * hs'
  · linear_combination (1 / 4 : ℝ) * hs'

/-- Exact eigenvalue ratio: `λ₊/λ₋ = 4ε/(1 + √(1 − 4ε))²`, and `ε ≤ λ₊/λ₋ ≤ 4ε`
(`a > 0`, `0 ≤ b`, `4b ≤ a²`). -/
@[powerlib_foundation] theorem eigen_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hd : 4 * b ≤ a ^ 2) :
    let ε := b / a ^ 2
    let s := Real.sqrt (1 - 4 * ε)
    (-(a / 2) * (1 - s)) / (-(a / 2) * (1 + s)) = 4 * ε / (1 + s) ^ 2 ∧
      ε ≤ 4 * ε / (1 + s) ^ 2 ∧ 4 * ε / (1 + s) ^ 2 ≤ 4 * ε := by
  intro ε s
  have hε : 0 ≤ ε := by positivity
  have h1 : 0 ≤ 1 - 4 * ε := by
    simp only [ε]
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * ε := Real.sq_sqrt h1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by nlinarith
  have hpos : 0 < 1 + s := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : -(a / 2) * (1 + s) ≠ 0 := by
      have : 0 < a / 2 * (1 + s) := by positivity
      linarith
    rw [div_eq_div_iff this (by positivity)]
    linear_combination (a / 2) * (1 + s) * hs
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- Fast and slow eigenvalue bounds: `λ₋ ∈ [−a, −a/2]`, `λ₊ ∈ [−2b/a, −b/a]`
(`a > 0`, `0 ≤ b`, `4b ≤ a²`). -/
@[powerlib_foundation] theorem eigen_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hd : 4 * b ≤ a ^ 2) :
    let s := Real.sqrt (1 - 4 * (b / a ^ 2))
    (-a ≤ -(a / 2) * (1 + s) ∧ -(a / 2) * (1 + s) ≤ -(a / 2)) ∧
      (-(2 * b / a) ≤ -(a / 2) * (1 - s) ∧ -(a / 2) * (1 - s) ≤ -(b / a)) := by
  intro s
  have h1 : 0 ≤ 1 - 4 * (b / a ^ 2) := by
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * (b / a ^ 2) := Real.sq_sqrt h1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by nlinarith [div_nonneg hb (sq_nonneg a)]
  have hkey : a / 2 * (1 - s) * (1 + s) = 2 * b / a := by
    have : (1 - s) * (1 + s) = 4 * (b / a ^ 2) := by nlinarith
    rw [mul_assoc, this]; field_simp; ring
  refine ⟨⟨by nlinarith, by nlinarith⟩, ?_, ?_⟩
  · -- `a/2 (1 − s) = (2b/a)/(1 + s) ≤ 2b/a`
    have h2 : a / 2 * (1 - s) ≤ 2 * b / a := by
      have : 0 ≤ a / 2 * (1 - s) := by nlinarith
      nlinarith
    linarith
  · have h2 : b / a ≤ a / 2 * (1 - s) := by
      have h3 : (1 + s) ≤ 2 := by linarith
      have : 0 ≤ a / 2 * (1 - s) := by nlinarith
      have h4 : 2 * b / a ≤ a / 2 * (1 - s) * 2 := by
        rw [← hkey]; exact mul_le_mul_of_nonneg_left h3 this
      have : 2 * b / a = 2 * (b / a) := by ring
      linarith
    linarith

end powerlib.PLL
