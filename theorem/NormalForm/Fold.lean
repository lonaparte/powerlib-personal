import theorem.NormalForm.Scalar

/-! # Fold (saddle-node) normal form `ẋ = μ − x²`

The equilibria, their stability, the semistable merger and the potential barrier of the truncated
one-dimensional fold normal form.

Model boundary.
* State: the single coordinate `x` (stored as `x 0` of `State 1`, see `NormalForm.lift`).
* Parameter: `μ ∈ ℝ`, constant in time (frozen-parameter, static bifurcation picture).
* Vector field: exactly `ẋ = μ − x²` (no higher-order remainder, no noise, no input,
  continuous time). Conclusions are about equilibria and their trajectory-level stability.
* A truncated normal form, not an engineering model: no model family; all results remain public
  foundation support. Behaviour is LeanForControl's predicates (`LocallyExponentiallyStable`,
  `Unstable`, `unstable_of_fixed_escape`).

Source: work-sync theory/T-fold-bifurcation.md §1.1–1.4, theory/T-bifurcation.md §1.4,
theory/T-fold-critical-scaling.md §1.1–1.4, theory/T-bifurcation-hypersurfaces.md §1.2.

Results.
* Equilibria: `μ − x² = 0 ↔ 0 ≤ μ ∧ (x = √μ ∨ x = −√μ)` (`field_eq_zero_iff`); there are
  `2 / 1 / 0` equilibria for `μ > 0 / μ = 0 / μ < 0` (`equilibria_ncard`).
* `μ > 0`: `√μ` is locally exponentially stable and `−√μ` is unstable (scalar linearization,
  `f_x = −2x`; `upper_locallyExponentiallyStable`, `lower_unstable`).
* `μ = 0`: the merged equilibrium is unstable (`critical_unstable`); solutions are
  `x₀ / (1 + x₀ (t − t₀))`, so every solution starting at `x₀ > 0` decays to `0` (attraction from
  the right, `critical_tendsto_zero_of_pos`) and every solution starting at `x₀ < 0` cannot exist
  for a time `1 / |x₀|` (finite-time escape on the left, `critical_escape_of_neg`): the
  equilibrium is semistable.
* Recovery rate `|f_x(√μ)| = 2√μ` (`recovery_rate`); with the potential `V(x) = −μx + x³/3`
  (`V' = −f`), the barrier is `V(−√μ) − V(√μ) = (4/3) μ^{3/2}` (`barrier`).
* One-dimensional `Σ_SN` (`f = f_x = 0`) holds exactly at `μ = 0` (`saddleNodeCondition_iff`).

Potential shapes: the barrier `(4/3) μ^{3/2}` is the local fold form of the tilted-washboard
barrier `ΔV ∝ δ^{3/2}` (`theorem/Potential/Barrier.lean`); the pitchfork potential
`−μx²/2 + x⁴/4` is in `theorem/NormalForm/Pitchfork.lean` and the general single / double well and
washboard shapes in `theorem/Potential/Wells.lean`.
-/

noncomputable section
namespace powerlib.NormalForm.Fold
open Set Filter Topology
open powerlib.Dynamics (State)

/-- The fold normal form `x ↦ μ − x²`. -/
def field (μ : ℝ) (x : ℝ) : ℝ := μ - x ^ 2

/-- The fold normal form as a vector field on `State 1`. -/
def system (μ : ℝ) : State 1 → State 1 := lift (field μ)

/-- The potential `V(x) = −μ x + x³/3`, with `V' = −(μ − x²)`. -/
def potential (μ : ℝ) (x : ℝ) : ℝ := -μ * x + x ^ 3 / 3

@[tmio T, powerlib_foundation] theorem field_contDiff (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (field μ) := by
  unfold field; fun_prop

@[powerlib_foundation] theorem hasDerivAt_field (μ x : ℝ) :
    HasDerivAt (field μ) (-2 * x) x := by
  have := (hasDerivAt_pow 2 x).const_sub μ
  unfold field
  convert this using 1
  push_cast; ring

@[powerlib_foundation] theorem deriv_field (μ x : ℝ) : deriv (field μ) x = -2 * x :=
  (hasDerivAt_field μ x).deriv

@[powerlib_foundation] theorem hasDerivAt_potential (μ x : ℝ) :
    HasDerivAt (potential μ) (-field μ x) x := by
  have h := ((hasDerivAt_id x).const_mul (-μ)).add (((hasDerivAt_id x).pow 3).div_const 3)
  convert h using 1
  · funext y; simp [potential]
  · simp [field]; ring

@[powerlib_foundation] theorem field_eq_zero_iff (μ x : ℝ) :
    field μ x = 0 ↔ 0 ≤ μ ∧ (x = √μ ∨ x = -√μ) := by
  unfold field
  constructor
  · intro h
    have hμ : μ = x ^ 2 := by linarith
    refine ⟨hμ ▸ sq_nonneg x, ?_⟩
    rw [hμ, Real.sqrt_sq_eq_abs]
    rcases le_total 0 x with hx | hx
    · left; rw [abs_of_nonneg hx]
    · right; rw [abs_of_nonpos hx, neg_neg]
  · rintro ⟨hμ, hx | hx⟩ <;> subst hx <;> simp [Real.sq_sqrt hμ]

@[powerlib_foundation] theorem field_sqrt {μ : ℝ} (hμ : 0 ≤ μ) : field μ √μ = 0 :=
  (field_eq_zero_iff μ _).mpr ⟨hμ, Or.inl rfl⟩

@[powerlib_foundation] theorem field_neg_sqrt {μ : ℝ} (hμ : 0 ≤ μ) : field μ (-√μ) = 0 :=
  (field_eq_zero_iff μ _).mpr ⟨hμ, Or.inr rfl⟩

/-- Equilibria of the lifted system. -/
@[powerlib_foundation] theorem system_eq_zero_iff (μ : ℝ) (x : State 1) :
    system μ x = 0 ↔ 0 ≤ μ ∧ (x = embed √μ ∨ x = embed (-√μ)) := by
  rw [← embed_coord x, system, lift_eq_zero_iff, field_eq_zero_iff, embed_eq_iff, embed_eq_iff]

/-- For `μ < 0` the fold system has no equilibrium. -/
@[powerlib_foundation] theorem no_equilibrium {μ : ℝ} (hμ : μ < 0) (x : State 1) :
    system μ x ≠ 0 := by
  rw [Ne, system_eq_zero_iff]
  exact fun h => absurd h.1 (not_le.mpr hμ)

/-- The equilibrium set of the normal form. -/
@[powerlib_foundation] theorem equilibria_eq (μ : ℝ) :
    {x : ℝ | field μ x = 0} = if μ < 0 then ∅ else {√μ, -√μ} := by
  split_ifs with hμ
  · ext x; simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, field_eq_zero_iff]
    exact fun h => absurd h.1 (not_le.mpr hμ)
  · ext x; simp [field_eq_zero_iff, not_lt.mp hμ]

/-- The number of equilibria is `2` for `μ > 0`, `1` for `μ = 0` and `0` for `μ < 0`. -/
@[powerlib_foundation] theorem equilibria_ncard (μ : ℝ) :
    {x : ℝ | field μ x = 0}.ncard = if 0 < μ then 2 else if μ = 0 then 1 else 0 := by
  rw [equilibria_eq]
  rcases lt_trichotomy μ 0 with h | h | h
  · simp [h, h.ne, not_lt.mpr h.le]
  · subst h; simp
  · have hs : √μ ≠ -√μ := by
      have := Real.sqrt_pos.mpr h; linarith
    simp [not_lt.mpr h.le, h, Set.ncard_pair hs]

/-- For `μ > 0` the upper equilibrium `√μ` is locally exponentially stable. -/
@[powerlib_foundation] theorem upper_locallyExponentiallyStable {μ : ℝ} (hμ : 0 < μ) :
    LocallyExponentiallyStable (system μ) (embed √μ) :=
  lift_locallyExponentiallyStable (field_contDiff μ) (field_sqrt hμ.le)
    (by rw [deriv_field]; have := Real.sqrt_pos.mpr hμ; linarith)

/-- For `μ > 0` the lower equilibrium `−√μ` is unstable. -/
@[powerlib_foundation] theorem lower_unstable {μ : ℝ} (hμ : 0 < μ) :
    Unstable (system μ) (embed (-√μ)) :=
  lift_unstable (field_contDiff μ) (field_neg_sqrt hμ.le)
    (by rw [deriv_field]; have := Real.sqrt_pos.mpr hμ; linarith)

/-- Local recovery rate on the stable branch: `|f_x(√μ)| = 2√μ`. -/
@[powerlib_foundation] theorem recovery_rate (μ : ℝ) :
    |deriv (field μ) √μ| = 2 * √μ := by
  rw [deriv_field, abs_of_nonpos (by have := Real.sqrt_nonneg μ; linarith)]
  ring

/-- Slopes at the two branches: `f_x(±√μ) = ∓2√μ`. -/
@[powerlib_foundation] theorem slopes (μ : ℝ) :
    deriv (field μ) √μ = -2 * √μ ∧ deriv (field μ) (-√μ) = 2 * √μ := by
  exact ⟨by rw [deriv_field], by rw [deriv_field]; ring⟩

@[powerlib_foundation] theorem rpow_three_halves {μ : ℝ} (hμ : 0 ≤ μ) :
    μ ^ ((3 : ℝ) / 2) = μ * √μ := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hμ (by norm_num),
    Real.rpow_one, Real.sqrt_eq_rpow]

/-- The barrier from the stable node to the saddle is `ΔV = (4/3) μ^{3/2}`. -/
@[powerlib_foundation] theorem barrier {μ : ℝ} (hμ : 0 ≤ μ) :
    potential μ (-√μ) - potential μ √μ = 4 / 3 * μ ^ ((3 : ℝ) / 2) := by
  rw [rpow_three_halves hμ]
  have h2 : √μ ^ 2 = μ := Real.sq_sqrt hμ
  have h3 : √μ ^ 3 = μ * √μ := by rw [pow_succ, h2]
  unfold potential
  rw [show (-√μ) ^ 3 = -(√μ ^ 3) by ring, h3]
  ring

/-- The one-dimensional saddle-node condition `f = f_x = 0` holds exactly at `μ = 0`. -/
@[powerlib_foundation] theorem saddleNodeCondition_iff (μ : ℝ) :
    SaddleNodeCondition (field μ) ↔ μ = 0 := by
  rw [NormalForm.saddleNodeCondition_iff (field_contDiff μ (k := 1)).differentiable_one]
  constructor
  · rintro ⟨x, h0, h1⟩
    rw [deriv_field] at h1
    have hx : x = 0 := by linarith
    subst hx; simpa [field] using h0
  · rintro rfl
    exact ⟨0, by simp [field], by simp [deriv_field]⟩

/-! ## The critical parameter `μ = 0` -/

@[powerlib_foundation] theorem critical_hasDerivAt (x₀ t : ℝ) (h : 1 + x₀ * t ≠ 0) :
    HasDerivAt (fun s => x₀ / (1 + x₀ * s)) (field 0 (x₀ / (1 + x₀ * t))) t := by
  have hden : HasDerivAt (fun s => 1 + x₀ * s) x₀ t := by
    simpa using ((hasDerivAt_id t).const_mul x₀).const_add 1
  have := (hasDerivAt_const t x₀).div hden h
  convert this using 1
  simp only [field]
  field_simp
  ring

/-- At `μ = 0` the merged equilibrium is unstable: arbitrarily small negative initial states
reach `|x| = 1` in finite time. -/
@[powerlib_foundation] theorem critical_unstable :
    Unstable (system 0) (embed 0) := by
  refine _root_.unstable_of_fixed_escape (ε := 1) one_pos ?_
  intro δ hδ
  set c := min (δ / 2) (1 / 2) with hc
  have hc0 : 0 < c := lt_min (by linarith) (by norm_num)
  have hc1 : c ≤ 1 / 2 := min_le_right _ _
  have hcδ : c < δ := (min_le_left _ _).trans_lt (by linarith)
  set T := (1 - c) / c
  have hT : 0 ≤ T := div_nonneg (by linarith) hc0.le
  have hden : ∀ t ∈ Icc (0 : ℝ) T, 0 < 1 + -c * t := by
    intro t ht
    have : c * t ≤ c * T := mul_le_mul_of_nonneg_left ht.2 hc0.le
    have hcT : c * T = 1 - c := by simp only [T]; field_simp
    linarith
  refine ⟨T, fun t => embed (-c / (1 + -c * t)), T, ?_, ?_, ⟨hT, le_rfl⟩, ?_⟩
  · apply isTrajectoryOn_embed
    intro t ht
    exact (critical_hasDerivAt (-c) t (hden t ht).ne').hasDerivWithinAt
  · simp [abs_of_pos hc0, hcδ]
  · have hcT : 1 + -c * T = c := by simp only [T]; field_simp; ring
    rw [embed_sub, norm_embed, hcT, sub_zero, neg_div, div_self hc0.ne', abs_neg, abs_one]

/-- At `μ = 0` every solution starting at `x₀ > 0` is `x₀ / (1 + x₀ (t − a))`. -/
@[powerlib_foundation] theorem critical_solution_pos {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => field 0 r) (Icc a b)) (ha : 0 < ψ a) :
    ∀ t ∈ Icc a b, ψ t = ψ a / (1 + ψ a * (t - a)) := by
  have hpos := pos_of_pos (field_contDiff 0) (by simp [field]) hψ ha
  have hconst := eq_of_hasDerivWithinAt_zero (F := fun t => (ψ t)⁻¹ - t) (a := a) (b := b)
    (by
      intro t ht
      have hd : HasDerivWithinAt ψ (-(ψ t) ^ 2) (Icc a b) t := by
        simpa [field] using hψ t ht
      have h : HasDerivWithinAt (fun t => (ψ t)⁻¹ - t) (-(-(ψ t) ^ 2) / ψ t ^ 2 - 1)
          (Icc a b) t := (hd.inv (hpos t ht).ne').sub (hasDerivWithinAt_id t (Icc a b))
      convert h using 1
      rw [neg_neg, div_self (pow_ne_zero 2 (hpos t ht).ne')]; ring)
  intro t ht
  have h := hconst t ht
  have hψt := (hpos t ht).ne'
  have hψa := ha.ne'
  have hrec : (ψ t)⁻¹ = (ψ a)⁻¹ + (t - a) := by linarith
  have hden : 1 + ψ a * (t - a) ≠ 0 := by
    have := mul_nonneg ha.le (sub_nonneg.mpr ht.1); linarith
  rw [eq_div_iff hden]
  field_simp at hrec
  linarith

/-- At `μ = 0` every forward-complete solution starting at `x₀ > 0` converges to `0`. -/
@[powerlib_foundation] theorem critical_tendsto_zero_of_pos {ψ : ℝ → ℝ} {a : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => field 0 r) (Ici a)) (ha : 0 < ψ a) :
    Tendsto ψ atTop (𝓝 0) := by
  have hformula : ∀ t, a ≤ t → ψ t = ψ a / (1 + ψ a * (t - a)) := fun t ht =>
    critical_solution_pos (hψ.mono Icc_subset_Ici_self) ha t ⟨ht, le_rfl⟩
  have hlim : Tendsto (fun t => ψ a / (1 + ψ a * (t - a))) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply tendsto_atTop_add_const_left
    exact (tendsto_atTop_add_const_right _ (-a) tendsto_id).const_mul_atTop ha |>.congr
      (fun t => by simp only [id]; ring)
  exact hlim.congr' (eventually_atTop.mpr ⟨a, fun t ht => (hformula t ht).symm⟩)

/-- At `μ = 0` a solution starting at `x₀ < 0` cannot be continued for the time `−1/x₀`. -/
@[powerlib_foundation] theorem critical_escape_of_neg {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => field 0 r) (Icc a b)) (ha : ψ a < 0) :
    b < a - 1 / ψ a := by
  by_contra hb
  push Not at hb
  have hneg := neg_of_neg (field_contDiff 0) (by simp [field]) hψ ha
  have hconst := eq_of_hasDerivWithinAt_zero (F := fun t => (ψ t)⁻¹ - t) (a := a) (b := b)
    (by
      intro t ht
      have hd : HasDerivWithinAt ψ (-(ψ t) ^ 2) (Icc a b) t := by
        simpa [field] using hψ t ht
      have h : HasDerivWithinAt (fun t => (ψ t)⁻¹ - t) (-(-(ψ t) ^ 2) / ψ t ^ 2 - 1)
          (Icc a b) t := (hd.inv (hneg t ht).ne).sub (hasDerivWithinAt_id t (Icc a b))
      convert h using 1
      rw [neg_neg, div_self (pow_ne_zero 2 (hneg t ht).ne)]; ring)
  set t := a - 1 / ψ a
  have ht : t ∈ Icc a b := ⟨by
    have : 0 < -(1 / ψ a) := by have := one_div_neg.mpr ha; linarith
    simp only [t]; linarith, hb⟩
  have h := hconst t ht
  simp only [t] at h
  have : (ψ (a - 1 / ψ a))⁻¹ = 0 := by
    have h' : (ψ (a - 1 / ψ a))⁻¹ = (ψ a)⁻¹ + (a - 1 / ψ a - a) := by linarith
    rw [h']; field_simp; ring
  exact (inv_ne_zero (hneg _ ht).ne) this

end powerlib.NormalForm.Fold
