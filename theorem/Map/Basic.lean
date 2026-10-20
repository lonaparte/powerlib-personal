import theorem.Map.Defs

/-! # Elementary facts of the map semantics

The general facts about the discrete-time notions of `theorem/Map/Defs.lean`, proved once, as
`theorem/Flow/Basic.lean` does for the flow notions.

Scope. Arbitrary maps `F : ℝⁿ → ℝⁿ` and discrete-time systems with ports; no model.

Source: the map semantics (`theorem/Map/Defs.lean`).

Results.
* `Map.System.autonomous_passive`: a discrete system without ports is passive.
* `Map.LyapunovStable.fixed`: a Lyapunov stable point is fixed.
* `Map.LocallyExponentiallyStable.lyapunovStable`, `.localAsymptoticStable`: geometric decay
  gives Lyapunov and local asymptotic stability.
* `Map.GloballyExponentiallyStable.locallyExponentiallyStable`, `.globallyAsymptoticallyStable`,
  `.sampledContraction`: a global geometric estimate gives the local one, global asymptotic
  stability and sampled contraction (the discrete counterparts of `theorem/Flow/Basic.lean`).
* `Map.GloballyAsymptoticallyStable.localAsymptoticStable`;
  `Map.GloballyExponentiallyStable.holdsMap`: a global geometric estimate gives every attractive
  sentence and sampled contraction, for every step length;
  `Flow.Property.localAsymptoticStable_of_holdsMap`: every attractive sentence of a map gives
  local asymptotic stability. -/

noncomputable section

namespace powerlib

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Map

open Filter Topology

/-- A system without ports is passive (zero storage). -/
@[powerlib_foundation] theorem System.autonomous_passive (T : ℝ) (F : ℝⁿ → ℝⁿ) :
    (System.autonomous T F).Passive :=
  ⟨fun _ => 0, fun _ => le_rfl, fun x u => by
    simp [System.supply, System.autonomous, Subsingleton.elim u 0]⟩

/-- A Lyapunov stable point is fixed. -/
@[powerlib_foundation] theorem LyapunovStable.fixed {F : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : LyapunovStable F x) : F x = x := by
  by_contra hne
  have hpos : 0 < ‖F x - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ, hδ, hb⟩ := h _ hpos
  have := hb x (by simpa using hδ) 1
  simp at this

/-- Geometric decay gives Lyapunov stability. -/
@[powerlib_foundation] theorem LocallyExponentiallyStable.lyapunovStable {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} (h : LocallyExponentiallyStable F x) : LyapunovStable F x := by
  obtain ⟨r, C, ρ, hr, hC, hρ0, hρ1, hb⟩ := h
  intro ε hε
  refine ⟨min r (ε / C), lt_min hr (div_pos hε (by linarith)), fun y hy k => ?_⟩
  have hyr : ‖y - x‖ < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hyε : ‖y - x‖ < ε / C := lt_of_lt_of_le hy (min_le_right _ _)
  have hρk : ρ ^ k ≤ 1 := pow_le_one₀ hρ0 hρ1.le
  calc ‖F^[k] y - x‖ ≤ C * ρ ^ k * ‖y - x‖ := hb y hyr k
    _ ≤ C * 1 * ‖y - x‖ := by gcongr
    _ < C * (ε / C) := by
        rw [mul_one]; exact mul_lt_mul_of_pos_left hyε (by linarith)
    _ = ε := by field_simp

/-- Geometric decay gives local asymptotic stability. -/
@[powerlib_foundation] theorem LocallyExponentiallyStable.localAsymptoticStable
    {F : ℝⁿ → ℝⁿ} {x : ℝⁿ} (h : LocallyExponentiallyStable F x) :
    LocalAsymptoticStable F x := by
  refine ⟨h.lyapunovStable, ?_⟩
  obtain ⟨r, C, ρ, hr, hC, hρ0, hρ1, hb⟩ := h
  refine ⟨r, hr, fun y hy => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k * ‖y - x‖) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
    simpa using this.mul_const ‖y - x‖
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hb y hy k) hlim

/-- A global geometric estimate is in particular a local one. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.locallyExponentiallyStable
    {F : ℝⁿ → ℝⁿ} {x : ℝⁿ} (h : GloballyExponentiallyStable F x) :
    LocallyExponentiallyStable F x := by
  obtain ⟨-, C, ρ, hC, hρ0, hρ1, hb⟩ := h
  exact ⟨1, C, ρ, one_pos, hC, hρ0, hρ1, fun y _ k => hb y k⟩

/-- A global geometric estimate gives global asymptotic stability. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.globallyAsymptoticallyStable
    {F : ℝⁿ → ℝⁿ} {x : ℝⁿ} (h : GloballyExponentiallyStable F x) :
    GloballyAsymptoticallyStable F x := by
  refine ⟨h.1, h.locallyExponentiallyStable.lyapunovStable, fun y => ?_⟩
  obtain ⟨-, C, ρ, -, hρ0, hρ1, hb⟩ := h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k * ‖y - x‖) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
    simpa using this.mul_const ‖y - x‖
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hb y k) hlim

/-- A global geometric estimate gives sampled contraction: the overshoot `C` is eventually beaten
by `ρ^k`. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.sampledContraction {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} (h : GloballyExponentiallyStable F x) : SampledContraction F x := by
  obtain ⟨-, C, ρ, -, hρ0, hρ1, hb⟩ := h
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
  obtain ⟨k, hk⟩ := ((eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds one_pos))).exists
  exact ⟨k, hk.1, C * ρ ^ k, hk.2, fun y => hb y k⟩

/-- Global asymptotic stability gives local asymptotic stability. -/
@[powerlib_foundation] theorem GloballyAsymptoticallyStable.localAsymptoticStable {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} (h : GloballyAsymptoticallyStable F x) : LocalAsymptoticStable F x :=
  ⟨h.2.1, 1, one_pos, fun y _ => h.2.2 y⟩

/-- A global geometric estimate gives every attractive sentence and sampled contraction, for every
step length. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.holdsMap {F : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable F x) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) (T : ℝ) : P.holdsMap T F x := by
  rcases hP with hP | rfl
  · cases P
    case locallyAsymptoticallyStable =>
      exact h.locallyExponentiallyStable.localAsymptoticStable
    case locallyExponentiallyStable => exact h.locallyExponentiallyStable
    case globallyAsymptoticallyStable => exact h.globallyAsymptoticallyStable
    case globallyExponentiallyStable => exact h
    all_goals exact hP.elim
  · exact h.sampledContraction

end Map

/-- Every attractive sentence of a map gives local asymptotic stability. -/
@[powerlib_foundation] theorem Flow.Property.localAsymptoticStable_of_holdsMap {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} {P : Flow.Property} (hP : P.Attractive) {T : ℝ} (h : P.holdsMap T F x) :
    Map.LocalAsymptoticStable F x := by
  cases P
  case locallyAsymptoticallyStable => exact h
  case locallyExponentiallyStable => exact Map.LocallyExponentiallyStable.localAsymptoticStable h
  case globallyAsymptoticallyStable =>
    exact Map.GloballyAsymptoticallyStable.localAsymptoticStable h
  case globallyExponentiallyStable =>
    exact Map.LocallyExponentiallyStable.localAsymptoticStable
      (Map.GloballyExponentiallyStable.locallyExponentiallyStable h)
  all_goals exact hP.elim

end powerlib
