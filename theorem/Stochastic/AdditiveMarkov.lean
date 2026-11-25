import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SolutionFlow
import theorem.Stochastic.BrownianMaximal
import theorem.Stochastic.UniformLDP
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # The Markov property of the additive-noise solution at deterministic times

For a Brownian motion `B` (Mathlib's `IsBrownianReal`) and a measurable path-space version `X` of
it on `[0, T₁ + T₂]`, the solution `x = S(x₀, c X)` of `x(t) = x₀ + c N X(t) + ∫₀ᵗ b(x)` restarted
at the deterministic time `T₁` is the solution from `x(T₁)` driven by the increments
`θ_{T₁} X = X(T₁ + ·) − X(T₁)` (`Stochastic.LDP.pathExt_solMap_add`); the increments are
independent of the past `X|[0, T₁]` and have the law of a Brownian path on `[0, T₂]`. Hence the
**Markov property**: the conditional law of the future given the past depends on the past only
through `x(T₁)`, in the integral form
`P(x|[0, T₁] ∈ A, x(T₁ + ·) ∈ C) = ∫_{x|[0, T₁] ∈ A} Q_C(x(T₁)) dP`,
`Q_C(y) = P(S(y, c X') ∈ C)` for any version `X'` of a Brownian motion on `[0, T₂]`.

Scope.
* Generic: `E` a real Banach space, `b` globally Lipschitz, `N : ℝ →L[ℝ] E` (one noise column,
  written `(Fin 1 → ℝ) →L[ℝ] E`), `c` any real noise scale (`c = √ε`), `T₁, T₂ > 0`, path spaces
  `C([0, T], ·)` with their Borel σ-algebras. Deterministic restart times only; the strong Markov
  property (at stopping times) is not formalized.
* No Itô calculus: additive noise, the solution is a continuous functional of the driving path
  (`Stochastic.LDP.solMap`).

Source: D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed. (1999), Ch. I
§1 and Ch. III §1 (Markov property of Brownian motion; Markov processes from independent
increments); M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 3 §1 (the solution as a functional of the driving path); Mathlib's
`IsPreBrownianReal.indepFun_shift` (weak Markov property of Brownian motion).

Results.
* Paths: `restrictPath` (restriction to `[0, T₁]`), `restartPath` (the path after `T₁`),
  `continuous_restrictPath`, `continuous_shiftPath`, `restrictPath_smul`, `shiftPath_smul`,
  `restrictPath_solMap` (the solution restricted is the solution of the restricted noise),
  `restartPath_solMap` (flow property in path form).
* `indepFun_restrictPath_shiftPath`: for a version `X` of a pre-Brownian motion on `[0, T₁ + T₂]`,
  the past `X|[0, T₁]` and the increments `θ_{T₁} X` are independent;
  `restrictPath_version`, `shiftPath_version`: they are versions of `B` on `[0, T₁]` and of the
  shifted Brownian motion `B(T₁ + ·) − B(T₁)` on `[0, T₂]`.
* `map_version_eq` (**uniqueness of the law**): two measurable versions of pre-Brownian motions on
  `[0, T]` (on any probability spaces) have the same law on `C([0, T])`.
* `measure_solMap_markov` (**Markov property at a deterministic time**) and
  `measure_solMap_markov_le` (its bound form: if `Q_C ≤ q` on the possible states `x(T₁)`, the
  joint probability is at most `q P(x|[0, T₁] ∈ A)`).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ## Restriction and restart of paths -/

/-- Restriction of a path on `[0, T]` to `[0, T₁]`, `T₁ ≤ T`. -/
def restrictPath {T₁ T : ℝ≥0} (h : T₁ ≤ T) (w : C(Icc (0 : ℝ) T, E)) :
    C(Icc (0 : ℝ) T₁, E) :=
  w.comp ⟨inclusion (Icc_subset_Icc_right (NNReal.coe_le_coe.mpr h)), continuous_inclusion _⟩

/-- The path after `T₁`: `t ↦ x(T₁ + t)` on `[0, T₂]`, for a path on `[0, T₁ + T₂]`. -/
def restartPath (T₁ T₂ : ℝ≥0) (x : C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), E)) :
    C(Icc (0 : ℝ) T₂, E) :=
  ⟨fun t => pathExt x (T₁ + t), (continuous_pathExt x).comp
    (continuous_const.add continuous_subtype_val)⟩

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem pathExt_restrictPath {T₁ T : ℝ≥0} (h : T₁ ≤ T)
    (w : C(Icc (0 : ℝ) T, E)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T₁) :
    pathExt (restrictPath h w) s = pathExt w s := by
  have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans (NNReal.coe_le_coe.mpr h)⟩
  rw [pathExt_of_mem _ hs, pathExt_of_mem _ hs']
  rfl

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem continuous_restrictPath {T₁ T : ℝ≥0} (h : T₁ ≤ T) :
    Continuous (restrictPath (E := E) h) :=
  ContinuousMap.continuous_precomp _

@[tmio T, powerlib_foundation] theorem restrictPath_smul {T₁ T : ℝ≥0} (h : T₁ ≤ T) (c : ℝ)
    (w : C(Icc (0 : ℝ) T, E)) : restrictPath h (c • w) = c • restrictPath h w := rfl

@[tmio T, powerlib_foundation] theorem pathExt_smul {T : ℝ≥0} (c : ℝ) (w : C(Icc (0 : ℝ) T, E))
    (s : ℝ) : pathExt (c • w) s = c • pathExt w s := rfl

@[tmio T, powerlib_foundation] theorem shiftPath_smul (T₁ T₂ : ℝ≥0) (c : ℝ)
    (w : C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), E)) :
    shiftPath T₁ T₂ (c • w) = c • shiftPath T₁ T₂ w := by
  ext t
  simp only [shiftPath, ContinuousMap.coe_mk, ContinuousMap.smul_apply]
  rw [pathExt_smul, pathExt_smul, smul_sub]

omit [NormedSpace ℝ E] in
/-- The increments map is `2`-Lipschitz, hence continuous. -/
@[tmio T, powerlib_foundation] theorem continuous_shiftPath (T₁ T₂ : ℝ≥0) :
    Continuous (shiftPath (F := E) T₁ T₂) := by
  refine (LipschitzWith.of_dist_le_mul fun w w' => ?_).continuous (K := 2)
  rw [dist_eq_norm, dist_eq_norm]
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
  simp only [shiftPath, ContinuousMap.sub_apply, ContinuousMap.coe_mk]
  have h1 := norm_pathExt_sub_le w w' (T₁ + t)
  have h2 := norm_pathExt_sub_le w w' T₁
  calc ‖pathExt w (T₁ + t) - pathExt w T₁ - (pathExt w' (T₁ + t) - pathExt w' T₁)‖
      = ‖(pathExt w (T₁ + t) - pathExt w' (T₁ + t)) - (pathExt w T₁ - pathExt w' T₁)‖ := by
        congr 1; abel
    _ ≤ ‖pathExt w (T₁ + t) - pathExt w' (T₁ + t)‖ + ‖pathExt w T₁ - pathExt w' T₁‖ :=
        norm_sub_le _ _
    _ ≤ ‖w - w'‖ + ‖w - w'‖ := add_le_add h1 h2
    _ = (2 : ℝ≥0) * ‖w - w'‖ := by push_cast; ring

/-- **The solution restricted to `[0, T₁]`** is the solution driven by the restricted noise. -/
@[tmio T, powerlib_foundation] theorem restrictPath_solMap [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) {T₁ T : ℝ≥0} (h : T₁ ≤ T)
    (w : C(Icc (0 : ℝ) T, F)) :
    restrictPath h (solMap b N x₀ w) = solMap b N x₀ (restrictPath h w) := by
  refine eq_solMap hb fun t => ?_
  have hspec := solMap_spec hb N x₀ w (inclusion (Icc_subset_Icc_right
    (NNReal.coe_le_coe.mpr h)) t)
  refine hspec.trans ?_
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.2.1] at hs
  rw [pathExt_restrictPath h _ ⟨hs.1, hs.2.trans t.2.2⟩]

/-- **Flow property, path form**: the solution after `T₁` is the solution from `x(T₁)` driven by
the increments `θ_{T₁} w`. -/
@[tmio T, powerlib_foundation] theorem restartPath_solMap [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) {T₁ T₂ : ℝ≥0}
    (w : C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), F)) :
    restartPath T₁ T₂ (solMap b N x₀ w) =
      solMap b N (pathExt (solMap b N x₀ w) T₁) (shiftPath T₁ T₂ w) := by
  ext t
  have h := pathExt_solMap_add hb N x₀ w t.2
  rw [pathExt_of_mem _ t.2] at h
  exact h

/-! ## Independence of the past and the increments -/

section Indep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A partition node of `[0, T]`, clamped to `j ≤ n`, as a point of `Iic T`. -/
private def clampNode (T : ℝ≥0) (n j : ℕ) : Iic T :=
  ⟨node T n (min j n), by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [node]
    · have h := (node_mem (T := T) hn (min_le_right j n)).2
      exact_mod_cast h⟩

/-- Normalized increments of a function on `Iic T` over the uniform partition. -/
private def pastIncr (T : ℝ≥0) (n : ℕ) (f : Iic T → ℝ) : Fin n → ℝ :=
  fun k => (f (clampNode T n (k + 1)) - f (clampNode T n k)) / √(mesh T n)

/-- Normalized increments of a function on `ℝ≥0` over the uniform partition of `[0, T]`. -/
private def shiftIncr (T : ℝ≥0) (n : ℕ) (f : ℝ≥0 → ℝ) : Fin n → ℝ :=
  fun k => (f (node T n (k + 1)) - f (node T n k)) / √(mesh T n)

/-- Limit of the polygonal interpolations of a function on `Iic T`. -/
private def pastLim (T : ℝ≥0) (f : Iic T → ℝ) : C(Icc (0 : ℝ) T, Fin 1 → ℝ) :=
  limUnder atTop fun n : ℕ => polyPath T (n + 1) (pastIncr T (n + 1) f)

/-- Limit of the polygonal interpolations of a function on `ℝ≥0` over `[0, T]`. -/
private def shiftLim (T : ℝ≥0) (f : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) T, Fin 1 → ℝ) :=
  limUnder atTop fun n : ℕ => polyPath T (n + 1) (shiftIncr T (n + 1) f)

@[tmio T, powerlib_foundation] private theorem measurable_pastLim {T : ℝ≥0}
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] :
    Measurable (pastLim T) := by
  have hm : ∀ n, Measurable (pastIncr T n) := fun n => measurable_pi_iff.mpr fun k => by
    have ha : Measurable fun f : Iic T → ℝ => f (clampNode T n (k + 1)) := measurable_pi_apply _
    have hb : Measurable fun f : Iic T → ℝ => f (clampNode T n k) := measurable_pi_apply _
    exact (ha.sub hb).div_const _
  exact (StronglyMeasurable.limUnder fun n =>
    continuous_polyPath.comp_stronglyMeasurable (hm (n + 1)).stronglyMeasurable).measurable

@[tmio T, powerlib_foundation] private theorem measurable_shiftLim {T : ℝ≥0}
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] :
    Measurable (shiftLim T) := by
  have hm : ∀ n, Measurable (shiftIncr T n) := fun n => measurable_pi_iff.mpr fun k => by
    have ha : Measurable fun f : ℝ≥0 → ℝ => f (node T n (k + 1)) := measurable_pi_apply _
    have hb : Measurable fun f : ℝ≥0 → ℝ => f (node T n k) := measurable_pi_apply _
    exact (ha.sub hb).div_const _
  exact (StronglyMeasurable.limUnder fun n =>
    continuous_polyPath.comp_stronglyMeasurable (hm (n + 1)).stronglyMeasurable).measurable

/-- The NNReal point of a real time in `Icc 0 T`. -/
@[tmio T, powerlib_foundation] private theorem nnreal_mk_coe (y : ℝ≥0) (h : 0 ≤ (y : ℝ)) :
    (⟨(y : ℝ), h⟩ : ℝ≥0) = y := rfl

/-- **Independence of the past and the increments**: for a version `X` of a pre-Brownian motion on
`[0, T₁ + T₂]`, the restriction `X|[0, T₁]` and the increments `θ_{T₁} X` are independent (the
weak Markov property `IsPreBrownianReal.indepFun_shift` read on path space through polygonal
interpolations). -/
@[tmio T, powerlib_foundation] theorem indepFun_restrictPath_shiftPath
    (hB : IsPreBrownianReal B P) {T₁ T₂ : ℝ≥0} (hT₁ : 0 < (T₁ : ℝ)) (hT₂ : 0 < (T₂ : ℝ))
    [MeasurableSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)]
    {X : Ω → C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)}
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), X ω t 0 = B ⟨t, t.2.1⟩ ω) :
    IndepFun (fun ω => restrictPath le_self_add (X ω)) (fun ω => shiftPath T₁ T₂ (X ω)) P := by
  set B' : ℝ≥0 → Ω → ℝ := fun s => (hB.aemeasurable s).mk (B s) with hB'def
  have hBB' : ∀ s, B s =ᵐ[P] B' s := fun s => (hB.aemeasurable s).ae_eq_mk
  have hB' : IsPreBrownianReal B' P := hB.congr hBB'
  have h2 := (hB'.indepFun_shift T₁).comp (measurable_shiftLim (T := T₂))
    (measurable_pastLim (T := T₁))
  have hsum : ((T₁ + T₂ : ℝ≥0) : ℝ) = T₁ + T₂ := NNReal.coe_add T₁ T₂
  have hgood : ∀ᵐ ω ∂P, (∀ t : Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), X ω t 0 = B ⟨t, t.2.1⟩ ω) ∧
      (∀ n j : ℕ, B (node T₁ n j) ω = B' (node T₁ n j) ω) ∧
      (∀ n j : ℕ, B (T₁ + node T₂ n j) ω = B' (T₁ + node T₂ n j) ω) ∧
      B T₁ ω = B' T₁ ω ∧ B 0 ω = 0 := by
    have h1 : ∀ᵐ ω ∂P, ∀ n j : ℕ, B (node T₁ n j) ω = B' (node T₁ n j) ω :=
      ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => hBB' _
    have h3 : ∀ᵐ ω ∂P, ∀ n j : ℕ, B (T₁ + node T₂ n j) ω = B' (T₁ + node T₂ n j) ω :=
      ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => hBB' _
    filter_upwards [hXB, h1, h3, hBB' T₁, hB.eval_zero_ae_eq_zero] with ω a b c d e
    exact ⟨a, b, c, d, e⟩
  refine h2.symm.congr ?_ ?_
  · -- the past
    filter_upwards [hgood] with ω hω
    obtain ⟨hX, hn, -, -, h0⟩ := hω
    set Y := restrictPath le_self_add (X ω) with hY
    have hval : ∀ m j : ℕ, 0 < m → j ≤ m → pathExt Y (node T₁ m j) 0 = B' (node T₁ m j) ω := by
      intro m j hm hj
      have hmem := node_mem (T := T₁) hm hj
      have hmem' : (node T₁ m j : ℝ) ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
        ⟨hmem.1, hmem.2.trans (by rw [hsum]; linarith [T₂.coe_nonneg])⟩
      rw [hY, pathExt_restrictPath _ _ hmem, pathExt_of_mem _ hmem', hX, nnreal_mk_coe, hn]
    have hterm : ∀ n : ℕ, polyPath T₁ (n + 1) (pastIncr T₁ (n + 1) fun t : Iic T₁ => B' t ω) =
        polyInterp T₁ (n + 1) Y := by
      intro n
      congr 1
      funext k
      have hk := k.2
      simp only [pastIncr, nodeIncr, clampNode]
      rw [hval _ _ (Nat.succ_pos n) hk, hval _ _ (Nat.succ_pos n) hk.le,
        min_eq_left hk, min_eq_left hk.le]
    have hY0 : pathExt Y 0 0 = 0 := by
      have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) := ⟨le_rfl, NNReal.coe_nonneg _⟩
      rw [hY, pathExt_restrictPath _ _ ⟨le_rfl, T₁.coe_nonneg⟩, pathExt_of_mem _ hmem, hX]
      exact h0
    have ht := (tendsto_polyInterp hT₁ Y hY0).comp (tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, pastLim]
    simp_rw [hterm]
    exact ht.limUnder_eq
  · -- the increments
    filter_upwards [hgood] with ω hω
    obtain ⟨hX, -, hs, hT, -⟩ := hω
    set Y := shiftPath T₁ T₂ (X ω) with hY
    have hX1 : pathExt (X ω) T₁ 0 = B' T₁ ω := by
      have hmem : (T₁ : ℝ) ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
        ⟨T₁.coe_nonneg, by rw [hsum]; linarith [T₂.coe_nonneg]⟩
      rw [pathExt_of_mem _ hmem, hX, nnreal_mk_coe, hT]
    have hval : ∀ m j : ℕ, 0 < m → j ≤ m →
        pathExt Y (node T₂ m j) 0 = B' (T₁ + node T₂ m j) ω - B' T₁ ω := by
      intro m j hm hj
      have hmem := node_mem (T := T₂) hm hj
      have hmem' : (T₁ : ℝ) + node T₂ m j ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
        ⟨by linarith [hmem.1, T₁.coe_nonneg], by rw [hsum]; linarith [hmem.2]⟩
      rw [hY, pathExt_of_mem _ hmem]
      simp only [shiftPath, ContinuousMap.coe_mk, Pi.sub_apply]
      rw [hX1, pathExt_of_mem _ hmem', hX]
      have e : (⟨(T₁ : ℝ) + node T₂ m j, hmem'.1⟩ : ℝ≥0) = T₁ + node T₂ m j :=
        NNReal.eq (by push_cast; rfl)
      rw [e, hs]
    have hterm : ∀ n : ℕ, polyPath T₂ (n + 1)
        (shiftIncr T₂ (n + 1) fun t => B' (T₁ + t) ω - B' T₁ ω) = polyInterp T₂ (n + 1) Y := by
      intro n
      congr 1
      funext k
      have hk := k.2
      simp only [shiftIncr, nodeIncr]
      rw [hval _ _ (Nat.succ_pos n) hk, hval _ _ (Nat.succ_pos n) hk.le]
    have hY0 : pathExt Y 0 0 = 0 := by
      rw [hY, pathExt_of_mem _ ⟨le_rfl, T₂.coe_nonneg⟩]
      simp [shiftPath]
    have ht := (tendsto_polyInterp hT₂ Y hY0).comp (tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, shiftLim]
    simp_rw [hterm]
    exact ht.limUnder_eq

/-- The restriction of a version on `[0, T]` is a version on `[0, T₁]`. -/
@[tmio T, powerlib_foundation] theorem restrictPath_version {T₁ T : ℝ≥0} (h : T₁ ≤ T)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)}
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) :
    ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T₁, restrictPath h (X ω) t 0 = B ⟨t, t.2.1⟩ ω := by
  filter_upwards [hXB] with ω hω t
  exact hω _

/-- The increments of a version on `[0, T₁ + T₂]` are a version of the shifted process
`B(T₁ + ·) − B(T₁)` on `[0, T₂]`. -/
@[tmio T, powerlib_foundation] theorem shiftPath_version {T₁ T₂ : ℝ≥0}
    {X : Ω → C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)}
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), X ω t 0 = B ⟨t, t.2.1⟩ ω) :
    ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T₂,
      shiftPath T₁ T₂ (X ω) t 0 = B (T₁ + ⟨t, t.2.1⟩) ω - B T₁ ω := by
  have hsum : ((T₁ + T₂ : ℝ≥0) : ℝ) = T₁ + T₂ := NNReal.coe_add T₁ T₂
  filter_upwards [hXB] with ω hω t
  have h1 : (T₁ : ℝ) + t ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
    ⟨by linarith [t.2.1, T₁.coe_nonneg], by rw [hsum]; linarith [t.2.2]⟩
  have h2 : (T₁ : ℝ) ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
    ⟨T₁.coe_nonneg, by rw [hsum]; linarith [T₂.coe_nonneg]⟩
  simp only [shiftPath, ContinuousMap.coe_mk, Pi.sub_apply]
  rw [pathExt_of_mem _ h1, pathExt_of_mem _ h2, hω, hω, nnreal_mk_coe]
  rfl

end Indep

/-! ## Uniqueness of the law of a version -/

section Law

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For a version `X` of a pre-Brownian motion and a bounded continuous `f ≥ 0`, the integrals of
`f` over the laws of the polygonal paths with standard Gaussian increments converge to the
integral of `f` over the law of `X`. -/
@[tmio T, powerlib_foundation] private theorem tendsto_lintegral_version [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {T : ℝ≥0} (hT : 0 < (T : ℝ))
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω)
    (f : C(Icc (0 : ℝ) T, Fin 1 → ℝ) →ᵇ ℝ≥0) :
    Tendsto (fun n : ℕ => ∫⁻ y, (f (polyPath T (n + 1) y) : ℝ≥0∞) ∂(gaussLaw (n + 1) 1))
      atTop (𝓝 (∫⁻ x, (f x : ℝ≥0∞) ∂(P.map X))) := by
  have hf : Measurable fun x => (f x : ℝ≥0∞) := f.continuous.measurable.coe_nnreal_ennreal
  have hn : ∀ n : ℕ, ∫⁻ y, (f (polyPath T (n + 1) y) : ℝ≥0∞) ∂(gaussLaw (n + 1) 1) =
      ∫⁻ ω, (f (polyInterp T (n + 1) (X ω)) : ℝ≥0∞) ∂P := by
    intro n
    have hmeq : P.map (fun ω => nodeIncr T (n + 1) (X ω)) = gaussLaw (n + 1) 1 := by
      rw [← map_polyNoise hB hT (Nat.succ_pos n) one_pos]
      refine Measure.map_congr ?_
      filter_upwards [hXB] with ω hω
      funext k
      have hk := k.2
      simp only [nodeIncr, polyNoise, Real.sqrt_one, one_mul]
      rw [pathExt_of_mem _ (node_mem (Nat.succ_pos n) hk),
        pathExt_of_mem _ (node_mem (Nat.succ_pos n) hk.le), hω, hω, nnreal_mk_coe,
        nnreal_mk_coe]
    rw [← hmeq, lintegral_map (show Measurable fun y : Fin (n + 1) → ℝ =>
        (f (polyPath T (n + 1) y) : ℝ≥0∞) from hf.comp continuous_polyPath.measurable)
      (show Measurable fun ω => nodeIncr T (n + 1) (X ω) from
        continuous_nodeIncr.measurable.comp hX)]
    rfl
  simp_rw [hn]
  rw [lintegral_map hf hX]
  refine tendsto_lintegral_of_dominated_convergence (fun _ => ((nndist f 0 : ℝ≥0) : ℝ≥0∞))
    (fun n => hf.comp (continuous_polyInterp.measurable.comp hX))
    (fun n => Eventually.of_forall fun ω =>
      ENNReal.coe_le_coe.mpr (BoundedContinuousFunction.NNReal.upper_bound f _))
    (by simp [lintegral_const]) ?_
  filter_upwards [hXB, hB.eval_zero_ae_eq_zero] with ω hω h0
  have hX0 : pathExt (X ω) 0 0 = 0 := by
    rw [pathExt_of_mem _ ⟨le_rfl, T.coe_nonneg⟩, hω]
    exact h0
  have ht := (tendsto_polyInterp hT (X ω) hX0).comp (tendsto_add_atTop_nat 1)
  exact (ENNReal.continuous_coe.comp f.continuous).continuousAt.tendsto.comp ht

/-- **Uniqueness of the law of a version**: two measurable path-space versions of pre-Brownian
motions on `[0, T]`, on any probability spaces, have the same law on `C([0, T])` (their
polygonal interpolations have the same Gaussian laws, `map_polyNoise`, and converge). -/
@[tmio T, powerlib_foundation] theorem map_version_eq {Ω' : Type*} {_ : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {B' : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hB' : IsPreBrownianReal B' P') {T : ℝ≥0} (hT : 0 < (T : ℝ))
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω)
    {X' : Ω' → C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hX' : Measurable X')
    (hXB' : ∀ᵐ ω ∂P', ∀ t : Icc (0 : ℝ) T, X' ω t 0 = B' ⟨t, t.2.1⟩ ω) :
    P.map X = P'.map X' :=
  ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f =>
    tendsto_nhds_unique (tendsto_lintegral_version hB hT hX hXB f)
      (tendsto_lintegral_version hB' hT hX' hXB' f)

end Law

/-! ## The Markov property -/

section Markov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Markov property at a deterministic time**: for a version `X` of a Brownian motion on
`[0, T₁ + T₂]`, the solution `x = S(x₀, c X)`, measurable sets `A` of paths on `[0, T₁]` and `C`
of paths on `[0, T₂]`, and any version `X'` of the Brownian motion on `[0, T₂]`,
`P(x|[0, T₁] ∈ A, x(T₁ + ·) ∈ C) = ∫_{x|[0, T₁] ∈ A} P'(S(x(T₁), c X') ∈ C) dP`. -/
@[tmio T, powerlib_foundation] theorem measure_solMap_markov [IsProbabilityMeasure P]
    [CompleteSpace E] (hB : IsBrownianReal B P) {T₁ T₂ : ℝ≥0} (hT₁ : 0 < (T₁ : ℝ))
    (hT₂ : 0 < (T₂ : ℝ))
    [MeasurableSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T₁, E)] [BorelSpace C(Icc (0 : ℝ) T₁, E)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, E)] [BorelSpace C(Icc (0 : ℝ) T₂, E)]
    {K : ℝ≥0} {b : E → E} (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    {X : Ω → C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), X ω t 0 = B ⟨t, t.2.1⟩ ω)
    {X' : Ω → C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)} (hX' : Measurable X')
    (hXB' : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T₂, X' ω t 0 = B ⟨t, t.2.1⟩ ω)
    {A : Set C(Icc (0 : ℝ) T₁, E)} (hA : MeasurableSet A) {C : Set C(Icc (0 : ℝ) T₂, E)}
    (hC : MeasurableSet C) :
    P {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A ∧
        restartPath T₁ T₂ (solMap b N x₀ (c • X ω)) ∈ C} =
      ∫⁻ ω in {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A},
        P {ω' | solMap b N (pathExt (solMap b N x₀ (c • X ω)) T₁) (c • X' ω') ∈ C} ∂P := by
  set Y₁ : Ω → C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) := fun ω => restrictPath le_self_add (X ω)
    with hY₁
  set Y₂ : Ω → C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) := fun ω => shiftPath T₁ T₂ (X ω) with hY₂
  have hY₁m : Measurable Y₁ := (continuous_restrictPath _).measurable.comp hX
  have hY₂m : Measurable Y₂ := (continuous_shiftPath T₁ T₂).measurable.comp hX
  have hind : IndepFun Y₁ Y₂ P :=
    indepFun_restrictPath_shiftPath hB.toIsPreBrownianReal hT₁ hT₂ hXB
  have hlaw : P.map Y₂ = P.map X' :=
    map_version_eq (hB.toIsPreBrownianReal.shift T₁) hB.toIsPreBrownianReal hT₂ hY₂m
      (shiftPath_version hXB) hX' hXB'
  set e : C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) → E := fun a => pathExt (solMap b N x₀ (c • a)) T₁
    with he_def
  have he : Continuous e :=
    (continuous_eval_const _).comp
      ((continuous_solMap hb N x₀).comp (continuous_const_smul c))
  have hT₁mem : (T₁ : ℝ) ∈ Icc (0 : ℝ) T₁ := ⟨T₁.coe_nonneg, le_rfl⟩
  have hend : ∀ ω, pathExt (solMap b N x₀ (c • X ω)) T₁ = e (Y₁ ω) := by
    intro ω
    rw [← pathExt_restrictPath le_self_add _ hT₁mem, restrictPath_solMap hb,
      restrictPath_smul]
  set D : Set (C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) × C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)) :=
    {p | solMap b N x₀ (c • p.1) ∈ A ∧ solMap b N (e p.1) (c • p.2) ∈ C} with hD_def
  have hD : MeasurableSet D := by
    have h1 : Measurable fun p : C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) × C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) =>
        solMap b N x₀ (c • p.1) :=
      ((continuous_solMap hb N x₀).comp ((continuous_const_smul c).comp continuous_fst)).measurable
    have h2 : Measurable fun p : C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) × C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) =>
        solMap b N (e p.1) (c • p.2) :=
      ((continuous_solMap_uncurry hb N).comp ((he.comp continuous_fst).prodMk
        ((continuous_const_smul c).comp continuous_snd))).measurable
    exact (h1 hA).inter (h2 hC)
  have hAm : MeasurableSet {a : C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) | solMap b N x₀ (c • a) ∈ A} :=
    ((continuous_solMap hb N x₀).comp (continuous_const_smul c)).measurable hA
  have hev : {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A ∧
      restartPath T₁ T₂ (solMap b N x₀ (c • X ω)) ∈ C} = (fun ω => (Y₁ ω, Y₂ ω)) ⁻¹' D := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hD_def]
    rw [restrictPath_solMap hb, restrictPath_smul, restartPath_solMap hb, shiftPath_smul,
      hend ω]
  have hS : {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A} =
      Y₁ ⁻¹' {a | solMap b N x₀ (c • a) ∈ A} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [restrictPath_solMap hb, restrictPath_smul]
  rw [hev, ← Measure.map_apply (hY₁m.prodMk hY₂m) hD,
    (indepFun_iff_map_prod_eq_prod_map_map hY₁m.aemeasurable hY₂m.aemeasurable).mp hind,
    Measure.prod_apply hD, lintegral_map (measurable_measure_prodMk_left hD) hY₁m, hS,
    ← lintegral_indicator (hY₁m hAm)]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ Y₁ ⁻¹' {a | solMap b N x₀ (c • a) ∈ A}
  · have hslice : Prod.mk (Y₁ ω) ⁻¹' D = {w | solMap b N (e (Y₁ ω)) (c • w) ∈ C} := by
      ext w
      simp only [mem_preimage, mem_ofPred_eq, hD_def]
      exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩
    have hm : MeasurableSet {w : C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) |
        solMap b N (e (Y₁ ω)) (c • w) ∈ C} :=
      ((continuous_solMap hb N _).comp (continuous_const_smul c)).measurable hC
    rw [indicator_of_mem hω, hlaw, hend ω, hslice, Measure.map_apply hX' hm]
    rfl
  · rw [indicator_of_notMem hω]
    convert measure_empty (μ := P.map Y₂)
    ext w
    simp only [mem_preimage, mem_ofPred_eq, hD_def, mem_empty_iff_false, iff_false, not_and]
    exact fun h => absurd h hω

/-- **Markov property, bound form**: if every path of `A` ends in `Kset` at `T₁` and
`P'(S(y, c X') ∈ C) ≤ q` for every `y ∈ Kset`, then
`P(x|[0, T₁] ∈ A, x(T₁ + ·) ∈ C) ≤ q P(x|[0, T₁] ∈ A)`. -/
@[tmio T, powerlib_foundation] theorem measure_solMap_markov_le [IsProbabilityMeasure P]
    [CompleteSpace E] (hB : IsBrownianReal B P) {T₁ T₂ : ℝ≥0} (hT₁ : 0 < (T₁ : ℝ))
    (hT₂ : 0 < (T₂ : ℝ))
    [MeasurableSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T₁, E)] [BorelSpace C(Icc (0 : ℝ) T₁, E)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, E)] [BorelSpace C(Icc (0 : ℝ) T₂, E)]
    {K : ℝ≥0} {b : E → E} (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    {X : Ω → C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), X ω t 0 = B ⟨t, t.2.1⟩ ω)
    {X' : Ω → C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)} (hX' : Measurable X')
    (hXB' : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T₂, X' ω t 0 = B ⟨t, t.2.1⟩ ω)
    {A : Set C(Icc (0 : ℝ) T₁, E)} (hA : MeasurableSet A) {C : Set C(Icc (0 : ℝ) T₂, E)}
    (hC : MeasurableSet C) {Kset : Set E} {q : ℝ≥0∞}
    (hAK : ∀ φ ∈ A, φ ⟨T₁, right_mem_Icc.mpr T₁.coe_nonneg⟩ ∈ Kset)
    (hq : ∀ y ∈ Kset, P {ω' | solMap b N y (c • X' ω') ∈ C} ≤ q) :
    P {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A ∧
        restartPath T₁ T₂ (solMap b N x₀ (c • X ω)) ∈ C} ≤
      q * P {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A} := by
  rw [measure_solMap_markov hB hT₁ hT₂ hb N x₀ c hX hXB hX' hXB' hA hC, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun ω hω => hq _ ?_
  have h := hAK _ hω
  rwa [← pathExt_restrictPath le_self_add _ ⟨T₁.coe_nonneg, le_rfl⟩,
    pathExt_of_mem _ ⟨T₁.coe_nonneg, le_rfl⟩]

end Markov

end powerlib.Stochastic.LDP
