import theorem.Flow.Defs

/-! # Relations between the behavioural sentences

The implications between the sentences hold for every vector field and are proved once:
global exponential stability gives every other attractive sentence, and a local exponential
estimate gives local asymptotic stability. -/

noncomputable section

namespace powerlib.Flow

open Set Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- An exponential estimate on every segment of a forward-complete solution forces convergence. -/
@[powerlib_foundation] theorem tendsto_of_segment_bound
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
@[powerlib_foundation] theorem locallyExponentiallyStable_localAsymptoticStable
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
  cases P with
  | locallyAsymptoticallyStable => exact h
  | locallyExponentiallyStable => exact locallyExponentiallyStable_localAsymptoticStable h
  | globallyAsymptoticallyStable => exact GloballyAsymptoticallyStable.localAsymptoticStable h
  | globallyExponentiallyStable =>
    exact GloballyAsymptoticallyStable.localAsymptoticStable h.globallyAsymptoticallyStable
  | lyapunovStable => exact absurd hP id
  | unstable => exact absurd hP id

/-- Global exponential stability gives every attractive sentence. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.holds {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable f x) {P : Property} (hP : P.Attractive) : P.holds f x := by
  cases P with
  | locallyAsymptoticallyStable =>
    exact locallyExponentiallyStable_localAsymptoticStable h.locallyExponentiallyStable
  | locallyExponentiallyStable => exact h.locallyExponentiallyStable
  | globallyAsymptoticallyStable => exact h.globallyAsymptoticallyStable
  | globallyExponentiallyStable => exact h
  | lyapunovStable => exact absurd hP id
  | unstable => exact absurd hP id

end powerlib.Flow
