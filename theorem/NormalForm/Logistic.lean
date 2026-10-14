import theorem.NormalForm.Scalar

/-! # The scalar Bernoulli (logistic) amplitude equation `ρ̇ = 2μρ + 2lρ²`

Explicit solution of the squared-amplitude equation of the truncated Hopf normal form (and, with
`ρ = x²`, of the pitchfork).

Scope.
* The scalar ODE `ρ̇ = 2μρ + 2lρ²` (`field`) on solution segments; a scalar ODE fact, not a model,
  and no model family.

Source: work-sync theory/T-hopf-bifurcation.md §1.2–1.3 (amplitude equation `ṙ = μr + l₁r³`,
written for `ρ = r²`); task note: "取 ρ = |z|² 得 logistic 方程，可显式求解".

Results.
* `reciprocal_formula`: for a solution `ρ > 0` on `[a, b]` and `μ ≠ 0`, the quantity
  `(1/ρ + l/μ) e^{2μ(t − a)}` is constant, i.e.
  `1/ρ(t) + l/μ = (1/ρ(a) + l/μ) e^{−2μ(t − a)}`.
* Positivity is preserved (`ρ = 0` is an equilibrium; `pos`).
* If `R² := −μ/l > 0`, the level `ρ = R²` is invariant (`level_invariant`).
* `μ > 0`, `l < 0`: every forward-complete positive solution converges to `R² = μ/|l|`
  (`tendsto_level`).
* `μ < 0`, `l > 0`: the distance `|1/ρ − 1/R²|` grows like `e^{2|μ|(t − a)}` (repelling level,
  `deviation_growth`), and solutions below the level converge to `0`
  (`tendsto_zero_of_lt_level`).
-/

noncomputable section
namespace powerlib.NormalForm.Logistic
open Set Filter Topology

/-- The squared-amplitude field `ρ ↦ 2μρ + 2lρ²`. -/
def field (μ l : ℝ) (ρ : ℝ) : ℝ := 2 * μ * ρ + 2 * l * ρ ^ 2

@[powerlib_foundation] theorem field_contDiff (μ l : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (field μ l) := by
  unfold field; fun_prop

@[powerlib_foundation] theorem field_zero (μ l : ℝ) : field μ l 0 = 0 := by simp [field]

/-- A solution that starts positive stays positive. -/
@[powerlib_foundation] theorem pos {μ l : ℝ} {ρ : ℝ → ℝ} {a b : ℝ}
    (hρ : IsIntegralCurveOn ρ (fun _ r => field μ l r) (Icc a b)) (ha : 0 < ρ a) :
    ∀ t ∈ Icc a b, 0 < ρ t :=
  pos_of_pos (field_contDiff μ l) (field_zero μ l) hρ ha

/-- Explicit solution in the reciprocal variable. -/
@[powerlib_foundation] theorem reciprocal_formula {μ l : ℝ} (hμ : μ ≠ 0) {ρ : ℝ → ℝ} {a b : ℝ}
    (hρ : IsIntegralCurveOn ρ (fun _ r => field μ l r) (Icc a b)) (ha : 0 < ρ a) :
    ∀ t ∈ Icc a b, 1 / ρ t + l / μ = (1 / ρ a + l / μ) * Real.exp (-2 * μ * (t - a)) := by
  have hpos := pos hρ ha
  have hconst := eq_of_hasDerivWithinAt_zero
    (F := fun t => ((ρ t)⁻¹ + l / μ) * Real.exp (2 * μ * (t - a))) (a := a) (b := b)
    (by
      intro t ht
      have hne : ρ t ≠ 0 := (hpos t ht).ne'
      have hd : HasDerivWithinAt ρ (field μ l (ρ t)) (Icc a b) t := hρ t ht
      have h3 : HasDerivWithinAt (fun s => (ρ s)⁻¹ + l / μ)
          (-(field μ l (ρ t)) / ρ t ^ 2) (Icc a b) t := (hd.inv hne).add_const (l / μ)
      have he : HasDerivWithinAt (fun s => Real.exp (2 * μ * (s - a)))
          (Real.exp (2 * μ * (t - a)) * (2 * μ)) (Icc a b) t := by
        have : HasDerivAt (fun s => 2 * μ * (s - a)) (2 * μ) t := by
          simpa using ((hasDerivAt_id t).sub_const a).const_mul (2 * μ)
        exact this.exp.hasDerivWithinAt
      convert h3.mul he using 1
      simp only [field]
      field_simp
      ring)
  intro t ht
  have h := hconst t ht
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at h
  have hexp : Real.exp (2 * μ * (t - a)) * Real.exp (-2 * μ * (t - a)) = 1 := by
    rw [← Real.exp_add]; simp
  calc 1 / ρ t + l / μ
      = ((ρ t)⁻¹ + l / μ) * Real.exp (2 * μ * (t - a)) * Real.exp (-2 * μ * (t - a)) := by
        rw [mul_assoc, hexp, mul_one, one_div]
    _ = _ := by rw [h, one_div]

/-- The level `ρ = −μ/l` is invariant. -/
@[powerlib_foundation] theorem level_invariant {μ l : ℝ} (hμ : μ ≠ 0) (hl : l ≠ 0)
    (hR : 0 < -μ / l) {ρ : ℝ → ℝ} {a b : ℝ}
    (hρ : IsIntegralCurveOn ρ (fun _ r => field μ l r) (Icc a b)) (ha : ρ a = -μ / l) :
    ∀ t ∈ Icc a b, ρ t = -μ / l := by
  intro t ht
  have h := reciprocal_formula hμ hρ (ha ▸ hR) t ht
  have hzero : 1 / ρ a + l / μ = 0 := by rw [ha]; field_simp; ring
  rw [hzero, zero_mul] at h
  have hpos := pos hρ (ha ▸ hR) t ht
  have h' : -l / μ = -(l / μ) := neg_div _ _
  have : 1 / ρ t = -l / μ := by linarith
  rw [one_div, inv_eq_iff_eq_inv] at this
  rw [this]; field_simp

/-- `μ > 0`, `l < 0`: every forward-complete positive solution converges to `μ/|l| = −μ/l`. -/
@[powerlib_foundation] theorem tendsto_level {μ l : ℝ} (hμ : 0 < μ) (hl : l < 0)
    {ρ : ℝ → ℝ} {a : ℝ}
    (hρ : IsIntegralCurveOn ρ (fun _ r => field μ l r) (Ici a)) (ha : 0 < ρ a) :
    Tendsto ρ atTop (𝓝 (-μ / l)) := by
  have hseg : ∀ t, a ≤ t → IsIntegralCurveOn ρ (fun _ r => field μ l r) (Icc a t) :=
    fun t _ => hρ.mono Icc_subset_Ici_self
  have hpos : ∀ t, a ≤ t → 0 < ρ t := fun t ht => pos (hseg t ht) ha t ⟨ht, le_rfl⟩
  have hw : ∀ t, a ≤ t →
      1 / ρ t = -l / μ + (1 / ρ a + l / μ) * Real.exp (-2 * μ * (t - a)) := fun t ht => by
    have := reciprocal_formula hμ.ne' (hseg t ht) ha t ⟨ht, le_rfl⟩
    have h' : -l / μ = -(l / μ) := neg_div _ _
    linarith
  have hexp : Tendsto (fun t => Real.exp (-2 * μ * (t - a))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 * μ * (t - a)) atTop atTop :=
      Tendsto.const_mul_atTop (show (0 : ℝ) < 2 * μ by positivity)
        (tendsto_atTop_add_const_right _ (-a) tendsto_id) |>.congr
        (fun t => by simp only [id]; ring)
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr (fun t => by simp [neg_mul])
  have hlimw : Tendsto (fun t => -l / μ + (1 / ρ a + l / μ) * Real.exp (-2 * μ * (t - a)))
      atTop (𝓝 (-l / μ)) := by
    have := (hexp.const_mul (1 / ρ a + l / μ)).const_add (-l / μ)
    rwa [mul_zero, add_zero] at this
  have hlpos : 0 < -l / μ := div_pos (by linarith) hμ
  have hcont : ContinuousAt (fun w : ℝ => 1 / w) (-l / μ) :=
    continuousAt_const.div continuousAt_id hlpos.ne'
  have hval : 1 / (-l / μ) = -μ / l := by field_simp
  have := hcont.tendsto.comp hlimw
  rw [hval] at this
  refine this.congr' (eventually_atTop.mpr ⟨a, fun t ht => ?_⟩)
  simp only [Function.comp]
  rw [← hw t ht, one_div_one_div]

/-- `μ < 0`, `l > 0`: the deviation from the invariant level, measured in `1/ρ`, grows like
`e^{2|μ|(t − a)}`; the level `−μ/l` is repelling. -/
@[powerlib_foundation] theorem deviation_growth {μ l : ℝ} (hμ : μ < 0) {ρ : ℝ → ℝ} {a b : ℝ}
    (hρ : IsIntegralCurveOn ρ (fun _ r => field μ l r) (Icc a b)) (ha : 0 < ρ a) :
    ∀ t ∈ Icc a b, |1 / ρ t - 1 / (-μ / l)| =
      |1 / ρ a - 1 / (-μ / l)| * Real.exp (2 * |μ| * (t - a)) := by
  intro t ht
  have h := reciprocal_formula hμ.ne hρ ha t ht
  have hinv : 1 / (-μ / l) = -(l / μ) := by
    rcases eq_or_ne l 0 with hl | hl
    · simp [hl]
    · field_simp
  rw [hinv, sub_neg_eq_add, sub_neg_eq_add, h, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_neg hμ]
  congr 2; ring

/-- `μ < 0`, `l > 0`: forward-complete solutions starting inside the level converge to `0`. -/
@[powerlib_foundation] theorem tendsto_zero_of_lt_level {μ l : ℝ} (hμ : μ < 0) (hl : 0 < l)
    {ρ : ℝ → ℝ} {a : ℝ}
    (hρ : IsIntegralCurveOn ρ (fun _ r => field μ l r) (Ici a)) (ha : 0 < ρ a)
    (hlt : ρ a < -μ / l) :
    Tendsto ρ atTop (𝓝 0) := by
  have hseg : ∀ t, a ≤ t → IsIntegralCurveOn ρ (fun _ r => field μ l r) (Icc a t) :=
    fun t _ => hρ.mono Icc_subset_Ici_self
  have hpos : ∀ t, a ≤ t → 0 < ρ t := fun t ht => pos (hseg t ht) ha t ⟨ht, le_rfl⟩
  set K := 1 / ρ a + l / μ
  have hK : 0 < K := by
    have h1 : 1 / (-μ / l) < 1 / ρ a := one_div_lt_one_div_of_lt ha hlt
    have h2 : 1 / (-μ / l) = -(l / μ) := by field_simp
    simp only [K]; linarith
  have hw : ∀ t, a ≤ t → 1 / ρ t = -(l / μ) + K * Real.exp (-2 * μ * (t - a)) := fun t ht => by
    have := reciprocal_formula hμ.ne (hseg t ht) ha t ⟨ht, le_rfl⟩
    linarith
  have hexp : Tendsto (fun t => Real.exp (-2 * μ * (t - a))) atTop atTop := by
    have h1 : Tendsto (fun t : ℝ => -2 * μ * (t - a)) atTop atTop :=
      Tendsto.const_mul_atTop (show (0 : ℝ) < -2 * μ by linarith)
        (tendsto_atTop_add_const_right _ (-a) tendsto_id) |>.congr
        (fun t => by simp only [id]; ring)
    exact Real.tendsto_exp_atTop.comp h1
  have hinv : Tendsto (fun t => 1 / ρ t) atTop atTop := by
    have : Tendsto (fun t => -(l / μ) + K * Real.exp (-2 * μ * (t - a))) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (hexp.const_mul_atTop hK)
    exact this.congr' (eventually_atTop.mpr ⟨a, fun t ht => (hw t ht).symm⟩)
  have := hinv.inv_tendsto_atTop
  refine this.congr' (eventually_atTop.mpr ⟨a, fun t ht => ?_⟩)
  simp

end powerlib.NormalForm.Logistic
