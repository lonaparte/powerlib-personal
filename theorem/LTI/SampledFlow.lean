import theorem.LTI.Sampling
import theorem.Linear.Stability
import theorem.Map.LinearReading

/-! # Exact samples of linear flows read every sentence (foundation)

The linear flow `ẋ = A x` and its exact samples `x_{k+1} = e^{TA} x_k` with step length `T > 0`
satisfy the same sentences at the origin, every one of them (`holds_iff_holdsMap_exp`): the
attractive sentences and sampled contraction are the Hurwitz property of `A` and the Schur
property of `e^{TA}` (`Linear.holds_iff_isHurwitz`, `Map.holdsMap_op_iff_schurStable`,
`LTI.isHurwitz_iff_schurStable_exp`); Lyapunov stability, instability, every decay rate and
conservation are read directly, through the samples of the solutions and, back from the samples
to every time, through the bound of the flow over one period (a decay rate, and so Lyapunov
stability) or the average of an energy over one period (conservation). Scaffold: the readings of
`theorem/ExactSampling.agda`.

Scope.
* Continuous time: the affine linear field `affineLinearVectorField A 0` of any real square
  matrix `A` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, read by the flow semantics at the origin
  (`theorem/Flow/Defs.lean`); solutions through `Linear.solution` (`theorem/Linear/Stability.lean`).
* Discrete time: the linear map `Map.op (e^{TA})` with step length `T`, read by the map semantics
  at the origin (`theorem/Map/Defs.lean`; a decay rate `a` per unit time is the rate `a T` per
  step, `Flow.Property.holdsMap`).
* Every sampling period `T > 0`; the statements are about arbitrary matrices: generic
  mathematics, no model.

Source: the flow and map semantics (`theorem/Flow/Defs.lean`, `theorem/Map/Defs.lean`), the linear
hubs `theorem/Linear/Stability.lean` and `theorem/Map/LinearReading.lean`, the Hurwitz–Schur
correspondence `LTI.isHurwitz_iff_schurStable_exp` (`theorem/LTI/Sampling.lean`); work-sync
`theory/T-control-delay.md` §1.4 (ZOH), `theory/T-numerical-integration.md` §2.7 (the discrete
recursion as the sampled semantics).

Results.
* The sampled map: `op_exp_smul` (`op (e^{sA}) = e^{s op A}`), `op_exp_add_smul` (the flow over
  `s + τ` is the flow over `s` after the flow over `τ`), `iterate_op_exp` (the `k`-th iterate of
  `e^{TA}` is the flow over `k T`).
* Readings, for `T > 0`: `decay_iff_exp` (`Flow.Decay` at the rate `a` iff `Map.Decay` at the rate
  `a T` per step), `lyapunovStable_iff_exp`, `conservative_iff_exp`, and the main
  `holds_iff_holdsMap_exp`: `P.holds (affineLinearVectorField A 0) 0 ↔ P.holdsMap T (op e^{TA}) 0`
  for every sentence `P`.

Family and connection conclusions.
* None: generic laws of linear flows and their samples; the exact-sampling families of
  `theorem/LTI/ExactSampling.lean` read them in their connection statements.
-/

noncomputable section

namespace powerlib

open Set LinearSystems NormedSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace LTI

/-- The sampled map of a period `s` is the flow over `s`. -/
@[powerlib_foundation] theorem op_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    Map.op (exp (s • A)) = exp (s • Linear.op A) := by
  rw [show Map.op (exp (s • A)) = Linear.op (exp (s • A)) from rfl, Linear.op_exp]
  exact congrArg exp (map_smul (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) s A)

/-- The iterates of the sampled map are the flow at the sampling instants. -/
@[powerlib_foundation] theorem iterate_op_exp (A : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (k : ℕ)
    (y : ℝⁿ) :
    (⇑(Map.op (exp (T • A))))^[k] y = Map.op (exp (((k : ℝ) * T) • A)) y := by
  rw [← FunLike.coe_pow_eq_iterate, ← map_pow, ← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]

/-- The solution of `ẋ = A x` through `x₀` at `t₀` is the flow `e^{(t - t₀) A} x₀`. -/
private theorem solution_zero (A : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ) (x₀ : ℝⁿ) (t : ℝ) :
    Linear.solution A 0 t₀ x₀ t = Map.op (exp ((t - t₀) • A)) x₀ := by
  rw [op_exp_smul]
  simp [Linear.solution]

/-- The flow is continuous in time. -/
private theorem continuous_op_exp (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun s : ℝ => Map.op (exp (s • A)) := by
  simp_rw [op_exp_smul]
  exact continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Linear.op A) t).continuousAt

/-- The flow over `s + τ` is the flow over `s` after the flow over `τ`. -/
@[powerlib_foundation] theorem op_exp_add_smul (A : Matrix (Fin n) (Fin n) ℝ) (s τ : ℝ) (y : ℝⁿ) :
    Map.op (exp ((s + τ) • A)) y = Map.op (exp (s • A)) (Map.op (exp (τ • A)) y) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right τ)]
  exact Linear.op_mul_apply _ _ y

/-- The solution from `y` at time zero is a solution segment on every interval. -/
private theorem isTrajectoryOn_solution (A : Matrix (Fin n) (Fin n) ℝ) (y : ℝⁿ) (t₁ : ℝ) :
    IsTrajectoryOn (Linear.solution A 0 0 y) (affineLinearVectorField A 0) 0 t₁ :=
  fun t _ => (Linear.solution_hasDerivAt A 0 0 y t).hasDerivWithinAt

/-- Sampled at `k T`, the solution from `y` is the `k`-th iterate of the sampled map. -/
private theorem solution_mul (A : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (y : ℝⁿ) (k : ℕ) :
    Linear.solution A 0 0 y (k * T) = (⇑(Map.op (exp (T • A))))^[k] y := by
  rw [solution_zero, iterate_op_exp, sub_zero]

/-- **Decay rates under exact sampling.** For `T > 0`, the linear flow decays at the rate `a`
exactly when its sampled map decays at the rate `a T` per step: every time is a sampling
instant plus less than one period, over which the flow is bounded. -/
@[powerlib_foundation] theorem decay_iff_exp (A : Matrix (Fin n) (Fin n) ℝ) {T : ℝ} (hT : 0 < T)
    (a : ℝ) :
    Flow.Decay (affineLinearVectorField A 0) 0 a ↔
      Map.Decay (Map.op (exp (T • A))) 0 (a * T) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun y k => ?_⟩
    have h := hC 0 (k * T) _ (isTrajectoryOn_solution A y _) (k * T) ⟨by positivity, le_rfl⟩
    rwa [solution_mul, Linear.solution_initial, show -a * (k * T - 0) = -(a * T) * k by ring]
      at h
  · rintro ⟨C, hC⟩
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuous_op_exp A).continuousOn (s := Icc 0 T)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
    refine ⟨M * max C 0 * Real.exp (|a| * T), fun t₀ t₁ φ hφ t ht => ?_⟩
    rw [Linear.trajectory_eq_solution hφ t ht, solution_zero, sub_zero, sub_zero]
    have hτ : 0 ≤ (t - t₀) / T := div_nonneg (sub_nonneg.mpr ht.1) hT.le
    set k := ⌊(t - t₀) / T⌋₊
    set s := t - t₀ - k * T with hs
    have hk1 : (k : ℝ) * T ≤ t - t₀ := (le_div_iff₀ hT).mp (Nat.floor_le hτ)
    have hk2 : t - t₀ < (k + 1) * T := (div_lt_iff₀ hT).mp (Nat.lt_floor_add_one _)
    have hsT : s ∈ Icc 0 T := ⟨by linarith, by linarith⟩
    have hsplit : Map.op (exp ((t - t₀) • A)) (φ t₀) =
        Map.op (exp (s • A)) ((⇑(Map.op (exp (T • A))))^[k] (φ t₀)) := by
      rw [iterate_op_exp, ← op_exp_add_smul, hs, sub_add_cancel]
    have h1 := hC (φ t₀) k
    rw [sub_zero, sub_zero] at h1
    have h2 : ‖(⇑(Map.op (exp (T • A))))^[k] (φ t₀)‖ ≤
        max C 0 * Real.exp (-(a * T) * k) * ‖φ t₀‖ :=
      h1.trans (by gcongr; exact le_max_left _ _)
    have has : a * s ≤ |a| * T :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) hsT.1).trans
        (mul_le_mul_of_nonneg_left hsT.2 (abs_nonneg a))
    have he : Real.exp (-(a * T) * k) ≤ Real.exp (|a| * T) * Real.exp (-a * (t - t₀)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : a * s = a * (t - t₀) - a * T * k := by rw [hs]; ring
      linarith
    rw [hsplit]
    calc ‖Map.op (exp (s • A)) ((⇑(Map.op (exp (T • A))))^[k] (φ t₀))‖
        ≤ ‖Map.op (exp (s • A))‖ * ‖(⇑(Map.op (exp (T • A))))^[k] (φ t₀)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * (max C 0 * Real.exp (-(a * T) * k) * ‖φ t₀‖) :=
          mul_le_mul (hM s hsT) h2 (norm_nonneg _) hM0
      _ ≤ M * (max C 0 * (Real.exp (|a| * T) * Real.exp (-a * (t - t₀))) * ‖φ t₀‖) := by
          gcongr
      _ = M * max C 0 * Real.exp (|a| * T) * Real.exp (-a * (t - t₀)) * ‖φ t₀‖ := by ring

/-- **Lyapunov stability under exact sampling.** For `T > 0`, the linear flow is Lyapunov stable
at the origin exactly when its sampled map is: the samples of a flow staying close stay close,
and a Lyapunov stable linear map has bounded powers, which bound the flow at every time. -/
@[powerlib_foundation] theorem lyapunovStable_iff_exp (A : Matrix (Fin n) (Fin n) ℝ) {T : ℝ}
    (hT : 0 < T) :
    LyapunovStable (affineLinearVectorField A 0) 0 ↔
      Map.LyapunovStable (Map.op (exp (T • A))) 0 := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, fun y hy k => ?_⟩
    have h := hb 0 (k * T) _ (isTrajectoryOn_solution A y _)
      (by rwa [Linear.solution_initial]) (k * T) ⟨by positivity, le_rfl⟩
    rwa [solution_mul] at h
  · intro h
    have hd := Map.decay_zero_of_lyapunovStable h
    rw [← zero_mul T] at hd
    exact ((decay_iff_exp A hT 0).mpr hd).lyapunovStable le_rfl

/-- **Conservation under exact sampling.** For `T > 0`, the linear flow conserves an energy with
a strict minimum at the origin exactly when its sampled map does: a conserved energy of the flow
is conserved at the samples, and the average over one period of the flow of an energy conserved
by the sampled map is conserved by the flow. -/
@[powerlib_foundation] theorem conservative_iff_exp (A : Matrix (Fin n) (Fin n) ℝ) {T : ℝ}
    (hT : 0 < T) :
    Flow.Conservative (affineLinearVectorField A 0) 0 ↔
      Map.Conservative (Map.op (exp (T • A))) 0 := by
  constructor
  · rintro ⟨V, hV, hmin, hcons⟩
    refine ⟨V, hV, hmin, fun y k => ?_⟩
    have h := hcons 0 (k * T) _ (isTrajectoryOn_solution A y _) (k * T) ⟨by positivity, le_rfl⟩
    rwa [solution_mul, Linear.solution_initial] at h
  · rintro ⟨V, hV, hmin, hcons⟩
    have hc : Continuous fun p : ℝⁿ × ℝ => V (Map.op (exp (p.2 • A)) p.1) :=
      hV.comp (((continuous_op_exp A).comp continuous_snd).clm_apply continuous_fst)
    have hper : ∀ y, Function.Periodic (fun s : ℝ => V (Map.op (exp (s • A)) y)) T := by
      intro y s
      have h := hcons (Map.op (exp (s • A)) y) 1
      rw [Function.iterate_one] at h
      simp only
      rw [add_comm, op_exp_add_smul, h]
    have hinv : ∀ (τ : ℝ) z,
        ∫ s in (0 : ℝ)..T, V (Map.op (exp (s • A)) (Map.op (exp (τ • A)) z)) =
          ∫ s in (0 : ℝ)..T, V (Map.op (exp (s • A)) z) := by
      intro τ z
      simp_rw [← op_exp_add_smul]
      rw [intervalIntegral.integral_comp_add_right (fun s : ℝ => V (Map.op (exp (s • A)) z)),
        zero_add, add_comm T τ, (hper z).intervalIntegral_add_eq τ 0, zero_add]
    refine ⟨fun y => ∫ s in (0 : ℝ)..T, V (Map.op (exp (s • A)) y),
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun y (s : ℝ) => V (Map.op (exp (s • A)) y)) hc continuous_const, fun y hy => ?_,
      fun t₀ t₁ φ hφ t ht => ?_⟩
    · have hne : ∀ s : ℝ, Map.op (exp (s • A)) y ≠ 0 := by
        intro s h0
        have h := op_exp_add_smul A (-s) s y
        rw [neg_add_cancel, zero_smul, h0, map_zero] at h
        exact hy (by simpa using h)
      simp only [map_zero]
      exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
        continuousOn_const
        (hV.comp ((continuous_op_exp A).clm_apply continuous_const)).continuousOn
        (fun s _ => (hmin _ (hne s)).le) ⟨0, ⟨le_rfl, hT.le⟩, hmin _ (hne 0)⟩
    · simp only
      rw [Linear.trajectory_eq_solution hφ t ht, solution_zero, hinv]

/-- **Exact sampling reads every sentence.** For a sampling period `T > 0`, every sentence holds
for the linear flow `ẋ = A x` at the origin exactly when it holds for its sampled map `e^{TA}`
with step length `T`. -/
@[powerlib_foundation] theorem holds_iff_holdsMap_exp (A : Matrix (Fin n) (Fin n) ℝ) {T : ℝ}
    (hT : 0 < T) (P : Flow.Property) :
    P.holds (affineLinearVectorField A 0) 0 ↔ P.holdsMap T (Map.op (exp (T • A))) 0 := by
  have hatt : ∀ {P : Flow.Property}, P.Attractive ∨ P = .contractive →
      (P.holds (affineLinearVectorField A 0) 0 ↔ P.holdsMap T (Map.op (exp (T • A))) 0) := by
    intro P hP
    rw [Map.holdsMap_op_iff_schurStable hP, ← isHurwitz_iff_schurStable_exp A hT]
    rcases hP with hP | rfl
    · exact Linear.holds_iff_isHurwitz 0 hP
    · exact Linear.sampledContraction_iff_isHurwitz 0
  cases P
  case lyapunovStable => exact lyapunovStable_iff_exp A hT
  case unstable => exact (lyapunovStable_iff_exp A hT).not
  case decay a => exact decay_iff_exp A hT a
  case conservative => exact conservative_iff_exp A hT
  case contractive => exact hatt (Or.inr rfl)
  all_goals exact hatt (Or.inl trivial)

end LTI

end powerlib
