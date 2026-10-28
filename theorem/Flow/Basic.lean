import theorem.Flow.Defs

/-! # Relations between the behavioural sentences

The implications between the sentences hold for every vector field and are proved once: global
exponential stability gives every other attractive sentence, a decay rate and sampled contraction;
a local exponential estimate gives local asymptotic stability; a positive decay rate gives sampled
contraction; and a conserved energy with a strict minimum gives Lyapunov stability
(Lagrange–Dirichlet) while ruling out convergence of every solution through a nearby state.

Scope.
* Generic: an arbitrary autonomous field `f : ℝⁿ → ℝⁿ` and point `x`, read by the flow semantics
  of `theorem/Flow/Defs.lean`; no model.

Source: the definitions of `theorem/Flow/Defs.lean` and LeanForControl's local notions
(`LeanForControl.Stability.DefsAutonomous`).

Results.
* `tendsto_of_segment_bound`: an exponential estimate on every segment of a forward-complete
  solution forces convergence.
* Global exponential stability: `GloballyExponentiallyStable.locallyExponentiallyStable`,
  `.lyapunovStable`, `.globallyAsymptoticallyStable`, `.holds` (every attractive sentence),
  `.exists_decay` (a positive rate), `.sampledContraction`.
* Local asymptotic stability: `locallyExponentiallyStable_localAsymptoticStable`,
  `GloballyAsymptoticallyStable.localAsymptoticStable`, `Property.localAsymptoticStable` (every
  attractive sentence implies it).
* Decay rates: `Decay.mono` (a rate gives every smaller rate), `Decay.lyapunovStable` (a
  nonnegative rate), `Decay.sampledContraction` (a positive rate).
* Conservation: `Conservative.lyapunovStable` (Lagrange–Dirichlet),
  `Conservative.not_localAsymptoticStable` (with a solution through every state and `0 < n`).
-/

noncomputable section

namespace powerlib.Flow

open Set Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- An exponential estimate on every segment of a forward-complete solution forces convergence. -/
@[tmio T, powerlib_foundation] theorem tendsto_of_segment_bound
    {f : ℝⁿ → ℝⁿ} {x : ℝⁿ} {C a : ℝ} (ha : 0 < a) {t₀ : ℝ}
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀))
    (hb : ∀ t₁ : ℝ, IsTrajectoryOn φ f t₀ t₁ → ∀ t : ℝ, t ∈ Icc t₀ t₁ →
      ‖φ t - x‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖) :
    Tendsto φ atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hexp : Tendsto (fun t => Real.exp (-a * (t - t₀))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_atTop_atTop.2 fun b =>
      ⟨b + t₀, fun t ht => by linarith⟩).const_mul_atTop_of_neg (by linarith))
  have hlim : Tendsto (fun t => C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖) atTop (𝓝 0) := by
    simpa using (hexp.const_mul C).mul_const ‖φ t₀ - x‖
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop t₀] with t ht
  exact hb t (hφ.mono Icc_subset_Ici_self) t ⟨ht, le_rfl⟩

/-- A global exponential estimate is in particular a local one. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.locallyExponentiallyStable
    {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable f x) : LocallyExponentiallyStable f x := by
  obtain ⟨-, -, C, a, hC, ha, hb⟩ := h
  exact ⟨1, C, a, one_pos, hC, ha, fun t₀ t₁ φ hφ _ t ht => hb t₀ t₁ φ hφ t ht⟩

@[powerlib_foundation] theorem GloballyExponentiallyStable.lyapunovStable {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable f x) : LyapunovStable f x :=
  h.locallyExponentiallyStable.lyapunovStable

/-- Global exponential stability gives global asymptotic stability. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.globallyAsymptoticallyStable
    {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable f x) : GloballyAsymptoticallyStable f x := by
  obtain ⟨heq, hfc, C, a, hC, ha, hb⟩ := h
  refine ⟨heq, hfc, (show GloballyExponentiallyStable f x from
    ⟨heq, hfc, C, a, hC, ha, hb⟩).lyapunovStable, fun t₀ φ hφ => ?_⟩
  exact tendsto_of_segment_bound ha hφ fun t₁ hseg => hb t₀ t₁ φ hseg

/-- A local exponential estimate gives local asymptotic stability. -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_localAsymptoticStable
    {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : LocallyExponentiallyStable f x) : LocalAsymptoticStable f x := by
  refine ⟨h.lyapunovStable, ?_⟩
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ := h
  exact ⟨r, hr, fun t₀ φ hφ h0 =>
    tendsto_of_segment_bound ha hφ fun t₁ hseg => hb t₀ t₁ φ hseg h0⟩

/-- Global asymptotic stability gives local asymptotic stability. -/
@[powerlib_foundation] theorem GloballyAsymptoticallyStable.localAsymptoticStable
    {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyAsymptoticallyStable f x) : LocalAsymptoticStable f x :=
  ⟨h.2.2.1, 1, one_pos, fun t₀ φ hφ _ => h.2.2.2 t₀ φ hφ⟩

/-- Every attractive sentence implies local asymptotic stability. -/
@[powerlib_foundation] theorem Property.localAsymptoticStable {f : ℝⁿ → ℝⁿ} {x : ℝⁿ} {P : Property}
    (hP : P.Attractive)
    (h : P.holds f x) : LocalAsymptoticStable f x := by
  cases P
  case locallyAsymptoticallyStable => exact h
  case locallyExponentiallyStable => exact locallyExponentiallyStable_localAsymptoticStable h
  case globallyAsymptoticallyStable => exact GloballyAsymptoticallyStable.localAsymptoticStable h
  case globallyExponentiallyStable =>
    exact GloballyAsymptoticallyStable.localAsymptoticStable h.globallyAsymptoticallyStable
  all_goals exact absurd hP id

/-- Global exponential stability gives every attractive sentence. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.holds {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable f x) {P : Property} (hP : P.Attractive) : P.holds f x := by
  cases P
  case locallyAsymptoticallyStable =>
    exact locallyExponentiallyStable_localAsymptoticStable h.locallyExponentiallyStable
  case locallyExponentiallyStable => exact h.locallyExponentiallyStable
  case globallyAsymptoticallyStable => exact h.globallyAsymptoticallyStable
  case globallyExponentiallyStable => exact h
  all_goals exact absurd hP id

/-! ## Decay rates and sampled contraction -/

/-- A decay rate gives every smaller rate. -/
@[powerlib_foundation] theorem Decay.mono {f : ℝⁿ → ℝⁿ} {x : ℝⁿ} {a b : ℝ} (h : Decay f x a)
    (hba : b ≤ a) : Decay f x b := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun t₀ t₁ φ hφ t ht => (hC t₀ t₁ φ hφ t ht).trans ?_⟩
  have hexp : Real.exp (-a * (t - t₀)) ≤ Real.exp (-b * (t - t₀)) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.1])
  have h0 : 0 ≤ ‖φ t₀ - x‖ := norm_nonneg _
  calc C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖
      ≤ max C 0 * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖ := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * Real.exp (-b * (t - t₀)) * ‖φ t₀ - x‖ := by
        gcongr

/-- Global exponential stability decays at a positive rate. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.exists_decay {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable f x) : ∃ a, 0 < a ∧ Decay f x a := by
  obtain ⟨-, -, C, a, -, ha, hb⟩ := h
  exact ⟨a, ha, C, hb⟩

/-- A decay rate `a ≥ 0` gives Lyapunov stability: the overshoot constant bounds every solution
segment by a fixed multiple of its initial distance. -/
@[powerlib_foundation] theorem Decay.lyapunovStable {f : ℝⁿ → ℝⁿ} {x : ℝⁿ} {a : ℝ} (ha : 0 ≤ a)
    (h : Flow.Decay f x a) : LyapunovStable f x := by
  obtain ⟨C, hC⟩ := h
  intro ε hε
  refine ⟨ε / (|C| + 1), by positivity, fun t₀ t₁ φ hφ h0 t ht => ?_⟩
  have he : Real.exp (-a * (t - t₀)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  have hd := norm_nonneg (φ t₀ - x)
  have hCe : C * Real.exp (-a * (t - t₀)) ≤ |C| :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
      (mul_le_of_le_one_right (abs_nonneg C) he)
  have h1 : (|C| + 1) * ‖φ t₀ - x‖ < ε := by
    rwa [lt_div_iff₀ (by positivity), mul_comm] at h0
  calc ‖φ t - x‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖ := hC t₀ t₁ φ hφ t ht
    _ ≤ |C| * ‖φ t₀ - x‖ := mul_le_mul_of_nonneg_right hCe hd
    _ < ε := by nlinarith

/-- A positive decay rate gives sampled contraction: the overshoot is eventually beaten by the
exponential. -/
@[powerlib_foundation] theorem Decay.sampledContraction {f : ℝⁿ → ℝⁿ} {x : ℝⁿ} {a : ℝ}
    (h : Decay f x a) (ha : 0 < a) : SampledContraction f x := by
  obtain ⟨C, hC⟩ := h
  have hlim : Tendsto (fun k : ℕ => max C 0 * Real.exp (-a * k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => Real.exp (-a * k)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg
        (by linarith))
    simpa using h1.const_mul (max C 0)
  obtain ⟨k, hk⟩ := ((eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds one_pos))).exists
  refine ⟨k, hk.1, max C 0 * Real.exp (-a * k), hk.2, fun t₀ φ hφ => ?_⟩
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb := hC t₀ (t₀ + k) φ hφ (t₀ + k) ⟨by linarith, le_rfl⟩
  rw [add_sub_cancel_left] at hb
  refine hb.trans ?_
  gcongr
  exact le_max_left _ _

/-- Global exponential stability gives sampled contraction. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.sampledContraction {f : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} (h : GloballyExponentiallyStable f x) : SampledContraction f x := by
  obtain ⟨a, ha, hd⟩ := h.exists_decay
  exact hd.sampledContraction ha

/-! ## Conservation -/

/-- A conserved energy with a strict minimum gives Lyapunov stability (Lagrange–Dirichlet): a
solution starting where the energy is below its minimum on a sphere never reaches the sphere. -/
@[powerlib_foundation] theorem Conservative.lyapunovStable {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : Conservative f x) : LyapunovStable f x := by
  obtain ⟨V, hV, hmin, hcons⟩ := h
  intro ε hε
  by_cases hs : (Metric.sphere x ε).Nonempty
  · obtain ⟨y₀, hy₀, hmin₀⟩ := (isCompact_sphere x ε).exists_isMinOn hs hV.continuousOn
    have hy₀x : y₀ ≠ x := by
      rintro rfl
      rw [Metric.mem_sphere, dist_self] at hy₀
      exact hε.ne hy₀
    have hm : 0 < V y₀ - V x := by linarith [hmin y₀ hy₀x]
    obtain ⟨δ, hδ, hδV⟩ := Metric.continuousAt_iff.mp hV.continuousAt _ hm
    refine ⟨min δ ε, lt_min hδ hε, fun t₀ t₁ φ hφ h0 t ht => ?_⟩
    by_contra hge
    push Not at hge
    obtain ⟨τ, hτ, hτε, -⟩ := exists_first_sphere_hit
      (hφ.continuousOn.mono (Icc_subset_Icc le_rfl ht.2)) (h0.trans_le (min_le_right _ _))
      ⟨ht.1, le_rfl⟩ hge
    have hτV : V (φ τ) = V (φ t₀) := hcons t₀ t₁ φ hφ τ ⟨hτ.1, hτ.2.trans ht.2⟩
    have h1 : V y₀ ≤ V (φ τ) := hmin₀ (by rw [Metric.mem_sphere, dist_eq_norm]; exact hτε)
    have h2 := hδV (show dist (φ t₀) x < δ by
      rw [dist_eq_norm]
      exact h0.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at h2
    linarith [(abs_lt.mp h2).2]
  · refine ⟨ε, hε, fun t₀ t₁ φ hφ h0 t ht => ?_⟩
    by_contra hge
    push Not at hge
    obtain ⟨τ, -, hτε, -⟩ := exists_first_sphere_hit
      (hφ.continuousOn.mono (Icc_subset_Icc le_rfl ht.2)) h0 ⟨ht.1, le_rfl⟩ hge
    exact hs ⟨φ τ, by rw [Metric.mem_sphere, dist_eq_norm]; exact hτε⟩

/-- A conserved energy rules out local asymptotic stability once a solution passes through every
state and the state space is not a point: the energy of a solution through a nearby state stays
above its minimum, so the solution cannot converge. -/
@[powerlib_foundation] theorem Conservative.not_localAsymptoticStable (hn : 0 < n)
    {f : ℝⁿ → ℝⁿ} {x : ℝⁿ} (h : Conservative f x) (hc : ForwardComplete f) :
    ¬ LocalAsymptoticStable f x := by
  rintro ⟨-, c, hc0, hconv⟩
  obtain ⟨V, hV, hmin, hcons⟩ := h
  set y : ℝⁿ := x + EuclideanSpace.single ⟨0, hn⟩ (c / 2) with hy_def
  have hsingle : ‖EuclideanSpace.single (⟨0, hn⟩ : Fin n) (c / 2)‖ = c / 2 := by
    rw [PiLp.norm_single, Real.norm_of_nonneg (by linarith)]
  have hyx : y ≠ x := by
    intro hyx
    have h0 : ‖y - x‖ = 0 := by rw [hyx, sub_self, norm_zero]
    rw [hy_def, add_sub_cancel_left, hsingle] at h0
    linarith
  obtain ⟨φ, hφ0, hφ⟩ := hc 0 y
  have hlim := hconv 0 φ hφ (by rw [hφ0, hy_def, add_sub_cancel_left, hsingle]; linarith)
  have hconst : ∀ t, 0 ≤ t → V (φ t) = V y := fun t ht => by
    rw [hcons 0 t φ (hφ.mono Icc_subset_Ici_self) t ⟨ht, le_rfl⟩, hφ0]
  have hlimV : Tendsto (fun t => V (φ t)) atTop (𝓝 (V x)) := (hV.tendsto x).comp hlim
  have hlimy : Tendsto (fun t => V (φ t)) atTop (𝓝 (V y)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop 0).mono fun t ht => (hconst t ht).symm)
  exact (hmin y hyx).ne (tendsto_nhds_unique hlimV hlimy)

end powerlib.Flow
