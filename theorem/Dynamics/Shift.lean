import theorem.Flow.Basic

/-! # Moving an equilibrium to the origin

Generic foundation, independent of any model: each behavioural sentence of the Flow semantics
holds for `f` at `e` exactly when it holds for `z ↦ f (z + e)` at `0`
(`Flow.Property.holds_shift_iff`). Model families read about a non-zero operating point use it to
place the operating point at the origin, where the sentences of the library are interpreted.
The per-predicate lemmas (`Dynamics.lyapunovStable_shift_iff`, …) live in `powerlib.Dynamics`;
`Flow.Property.holds_shift_iff` keeps the namespace of the codex type `Flow.Property` it extends
(dot notation). -/

noncomputable section

namespace powerlib.Dynamics

open Set Filter Topology
open powerlib.Flow (ForwardComplete GloballyExponentiallyStable GloballyAsymptoticallyStable Decay
  SampledContraction Conservative)

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

section Shift

/-- Solutions of `z ↦ f (z + e)` are the solutions of `f` moved by `-e`. -/
@[powerlib_foundation] theorem isIntegralCurveOn_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} {φ : ℝ → ℝⁿ}
    {s : Set ℝ} :
    IsIntegralCurveOn (fun t => φ t - e) (fun _ z => f (z + e)) s ↔
      IsIntegralCurveOn φ (fun _ x => f x) s := by
  simp only [IsIntegralCurveOn, sub_add_cancel, hasDerivWithinAt_sub_const_iff]

private theorem forall_curve_shift {e : ℝⁿ} {Q : (ℝ → ℝⁿ) → Prop} :
    (∀ ψ : ℝ → ℝⁿ, Q ψ) ↔ ∀ φ : ℝ → ℝⁿ, Q (fun t => φ t - e) :=
  ⟨fun h φ => h _, fun h ψ => by simpa using h (fun t => ψ t + e)⟩

private theorem tendsto_shift_iff {e : ℝⁿ} {φ : ℝ → ℝⁿ} :
    Tendsto (fun t => φ t - e) atTop (𝓝 0) ↔ Tendsto φ atTop (𝓝 e) := by
  have h := tendsto_sub_const_iff (f := φ) (l := atTop) e (c := e)
  rwa [sub_self] at h

@[powerlib_foundation] theorem isEquilibrium_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    IsEquilibrium (fun z => f (z + e)) 0 ↔ IsEquilibrium f e := by
  simp [IsEquilibrium]

@[powerlib_foundation] theorem lyapunovStable_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    LyapunovStable (fun z => f (z + e)) 0 ↔ LyapunovStable f e := by
  unfold LyapunovStable
  refine forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ =>
    forall₂_congr fun t₀ t₁ => (forall_curve_shift (e := e)).trans (forall_congr' fun φ => ?_)
  simp only [IsTrajectoryOn, isIntegralCurveOn_shift_iff, sub_zero]

@[powerlib_foundation] theorem locallyExponentiallyStable_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    LocallyExponentiallyStable (fun z => f (z + e)) 0 ↔ LocallyExponentiallyStable f e := by
  unfold LocallyExponentiallyStable
  refine exists_congr fun r => exists_congr fun C => exists_congr fun a =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun t₀ t₁ => (forall_curve_shift (e := e)).trans (forall_congr' fun φ => ?_)
  simp only [IsTrajectoryOn, isIntegralCurveOn_shift_iff, sub_zero]

@[powerlib_foundation] theorem unstable_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    Unstable (fun z => f (z + e)) 0 ↔ Unstable f e :=
  not_congr lyapunovStable_shift_iff

@[powerlib_foundation] theorem localAsymptoticStable_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    LocalAsymptoticStable (fun z => f (z + e)) 0 ↔ LocalAsymptoticStable f e := by
  unfold LocalAsymptoticStable
  refine and_congr lyapunovStable_shift_iff (exists_congr fun c => and_congr_right fun _ =>
    forall_congr' fun t₀ => (forall_curve_shift (e := e)).trans (forall_congr' fun φ => ?_))
  simp only [isIntegralCurveOn_shift_iff, sub_zero, tendsto_shift_iff]

@[powerlib_foundation] theorem globalAsymptoticStable_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    GlobalAsymptoticStable (fun z => f (z + e)) 0 ↔ GlobalAsymptoticStable f e := by
  unfold GlobalAsymptoticStable
  refine and_congr lyapunovStable_shift_iff (forall_congr' fun t₀ =>
    (forall_curve_shift (e := e)).trans (forall_congr' fun φ => ?_))
  simp only [isIntegralCurveOn_shift_iff, tendsto_shift_iff]

@[powerlib_foundation] theorem forwardComplete_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    ForwardComplete (fun z => f (z + e)) ↔ ForwardComplete f := by
  constructor
  · intro h t₀ x₀
    obtain ⟨ψ, hψ0, hψ⟩ := h t₀ (x₀ - e)
    refine ⟨fun t => ψ t + e, by simp [hψ0], ?_⟩
    rw [← isIntegralCurveOn_shift_iff (e := e)]
    simpa using hψ
  · intro h t₀ z₀
    obtain ⟨φ, hφ0, hφ⟩ := h t₀ (z₀ + e)
    exact ⟨fun t => φ t - e, by simp [hφ0], isIntegralCurveOn_shift_iff.mpr hφ⟩

@[powerlib_foundation] theorem decay_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} {a : ℝ} :
    Decay (fun z => f (z + e)) 0 a ↔ Decay f e a := by
  unfold Decay
  refine exists_congr fun C => forall₂_congr fun t₀ t₁ =>
    (forall_curve_shift (e := e)).trans (forall_congr' fun φ => ?_)
  simp only [IsTrajectoryOn, isIntegralCurveOn_shift_iff, sub_zero]

@[powerlib_foundation] theorem sampledContraction_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    SampledContraction (fun z => f (z + e)) 0 ↔ SampledContraction f e := by
  unfold SampledContraction
  refine exists_congr fun k => and_congr_right fun _ => exists_congr fun c =>
    and_congr_right fun _ => forall_congr' fun t₀ =>
    (forall_curve_shift (e := e)).trans (forall_congr' fun φ => ?_)
  simp only [IsTrajectoryOn, isIntegralCurveOn_shift_iff, sub_zero]

@[powerlib_foundation] theorem globallyExponentiallyStable_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    GloballyExponentiallyStable (fun z => f (z + e)) 0 ↔ GloballyExponentiallyStable f e := by
  unfold GloballyExponentiallyStable
  refine and_congr isEquilibrium_shift_iff (and_congr forwardComplete_shift_iff
    (exists_congr fun C => exists_congr fun a => and_congr_right fun _ => and_congr_right fun _ =>
      forall₂_congr fun t₀ t₁ => (forall_curve_shift (e := e)).trans (forall_congr' fun φ => ?_)))
  simp only [IsTrajectoryOn, isIntegralCurveOn_shift_iff, sub_zero]

@[powerlib_foundation] theorem globallyAsymptoticallyStable_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    GloballyAsymptoticallyStable (fun z => f (z + e)) 0 ↔ GloballyAsymptoticallyStable f e :=
  and_congr isEquilibrium_shift_iff (and_congr forwardComplete_shift_iff
    globalAsymptoticStable_shift_iff)

@[powerlib_foundation] theorem conservative_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} :
    Conservative (fun z => f (z + e)) 0 ↔ Conservative f e := by
  constructor
  · rintro ⟨V, hV, hmin, hcons⟩
    refine ⟨fun x => V (x - e), hV.comp (continuous_id.sub continuous_const),
      fun x hx => ?_, fun t₀ t₁ φ hφ t ht => ?_⟩
    · simpa using hmin (x - e) (sub_ne_zero.mpr hx)
    · exact hcons t₀ t₁ (fun t => φ t - e) (isIntegralCurveOn_shift_iff.mpr hφ) t ht
  · rintro ⟨V, hV, hmin, hcons⟩
    refine ⟨fun z => V (z + e), hV.comp (continuous_id.add continuous_const),
      fun z hz => ?_, fun t₀ t₁ ψ hψ t ht => ?_⟩
    · simpa using hmin (z + e) (by simpa using hz)
    · have hφ : IsIntegralCurveOn (fun t => ψ t + e) (fun _ x => f x) (Icc t₀ t₁) := by
        rw [← isIntegralCurveOn_shift_iff (e := e)]
        simpa using hψ
      simpa using hcons t₀ t₁ (fun t => ψ t + e) hφ t ht

end Shift

end powerlib.Dynamics

namespace powerlib.Flow

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Every behavioural sentence of the Flow semantics is invariant under moving the equilibrium to
the origin: the sentence holds for `f` at `e` exactly when it holds for `z ↦ f (z + e)` at `0`. -/
@[powerlib_foundation] theorem Property.holds_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} (P : Property) :
    P.holds (fun z => f (z + e)) 0 ↔ P.holds f e := by
  cases P
  case lyapunovStable => exact Dynamics.lyapunovStable_shift_iff
  case locallyAsymptoticallyStable => exact Dynamics.localAsymptoticStable_shift_iff
  case locallyExponentiallyStable => exact Dynamics.locallyExponentiallyStable_shift_iff
  case globallyAsymptoticallyStable => exact Dynamics.globallyAsymptoticallyStable_shift_iff
  case globallyExponentiallyStable => exact Dynamics.globallyExponentiallyStable_shift_iff
  case unstable => exact Dynamics.unstable_shift_iff
  case decay a => exact Dynamics.decay_shift_iff
  case contractive => exact Dynamics.sampledContraction_shift_iff
  case conservative => exact Dynamics.conservative_shift_iff

end powerlib.Flow
