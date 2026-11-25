import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.AdditiveMarkov
import Mathlib.MeasureTheory.Function.Floor

/-! # The strong Markov property of the additive-noise solution

For a version `X` of a Brownian motion on `[0, H]` (`Stochastic.LDP.exists_version`) and the
pathwise solution `x = S(x₀, c X)` of `x(t) = x₀ + c N X(t) + ∫₀ᵗ b(x)` (`b` globally
Lipschitz): the Markov property at a deterministic time in expectation form, for past events of
the driving path, and the **strong Markov property** at bounded stopping times of the natural
filtration `F_t = σ(X|[0, t])`: for `A ∈ F_τ` and a bounded continuous functional `F` of the
paths on `[0, T₂]`, `∫_A F(x(τ + ·)) dP = ∫_A E'[F(S(x(τ), c X'))] dP` with `X'` a version on
`[0, T₂]`, i.e. after `τ` the solution restarts afresh from `x(τ)`. The proof discretises
`τ_n = (⌈2^{n+1} τ⌉ + 1)/2^{n+1}` (dyadic values, `τ < τ_n ≤ τ + 2^{−n}`; the event
`{τ_n = (j + 1)/2^{n+1}} ∩ A` lies in `F_{(j + 1)/2^{n+1}}` because `A ∈ F_τ`), applies the Markov
property at each dyadic value, and passes to the limit `n → ∞` by continuity of the paths, of the
restart map `(s, φ) ↦ φ(s + ·)` and of `y ↦ E'[F(S(y, c X'))]`, and dominated convergence.

Scope.
* Generic: `E` a real Banach space, `N : (Fin 1 → ℝ) →L[ℝ] E`, `B` a Brownian motion (Mathlib's
  `IsBrownianReal`), measurable versions on path spaces with their Borel σ-algebras. Stopping
  times bounded by `T₀` with `H ≥ T₀ + 1 + T₂`; the filtration is the natural filtration of the
  version (`{τ ≤ t}` and `A ∩ {τ ≤ t}` are events of `X|[0, t]`), stated through
  `MeasurableSpace.comap` (no completion). Test functionals bounded and continuous (they
  determine the conditional law). Unbounded stopping times and the hitting-time applications are
  not stated.

Source: I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed. (1991),
§2.6 (the strong Markov property of Brownian motion, by dyadic approximation of the stopping
time); M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2 (the strong Markov property at hitting times in the exit problem).

Results.
* `integral_solMap_markov` (**Markov property, expectation form**, past events of the driving
  path: `∫_{X|[0, T₁] ∈ A} F(x(T₁ + ·)) dP = ∫_{X|[0, T₁] ∈ A} E'[F(S(x(T₁), c X'))] dP`).
* `restartAt` (the restart map `(s, φ) ↦ φ(s + ·)`, jointly continuous), `restartAt_apply`,
  `restartPath_restrictPath`; `natCeil_eq_iff_forall`.
* `integral_solMap_strongMarkov` (**strong Markov property** at bounded stopping times).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Markov property, expectation form, with events of the driving path**: for a version `X` of
a Brownian motion on `[0, T₁ + T₂]`, a measurable set `A` of driving paths on `[0, T₁]`, a
version `X'` on `[0, T₂]` and a bounded continuous `F` on the paths of `[0, T₂]`,
`∫_{X|[0, T₁] ∈ A} F(x(T₁ + ·)) dP = ∫_{X|[0, T₁] ∈ A} E'[F(S(x(T₁), c X'))] dP`. -/
@[tmio T, powerlib_foundation] theorem integral_solMap_markov [IsProbabilityMeasure P]
    [CompleteSpace E] (hB : IsBrownianReal B P) {T₁ T₂ : ℝ≥0} (hT₁ : 0 < (T₁ : ℝ))
    (hT₂ : 0 < (T₂ : ℝ))
    [MeasurableSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)]
    {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    {X : Ω → C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), X ω t 0 = B ⟨t, t.2.1⟩ ω)
    {X' : Ω → C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)} (hX' : Measurable X')
    (hXB' : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T₂, X' ω t 0 = B ⟨t, t.2.1⟩ ω)
    {A : Set C(Icc (0 : ℝ) T₁, Fin 1 → ℝ)} (hA : MeasurableSet A)
    (F : C(Icc (0 : ℝ) T₂, E) →ᵇ ℝ) :
    ∫ ω in {ω | restrictPath le_self_add (X ω) ∈ A},
        F (restartPath T₁ T₂ (solMap b N x₀ (c • X ω))) ∂P =
      ∫ ω in {ω | restrictPath le_self_add (X ω) ∈ A},
        (∫ ω', F (solMap b N (pathExt (solMap b N x₀ (c • X ω)) T₁) (c • X' ω')) ∂P) ∂P := by
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
  have hrest : ∀ ω, restartPath T₁ T₂ (solMap b N x₀ (c • X ω)) =
      solMap b N (e (Y₁ ω)) (c • Y₂ ω) := by
    intro ω
    rw [restartPath_solMap hb, shiftPath_smul, hend]
  -- the integrand on the product of the past and the increments
  set Φ : C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) × C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) → ℝ :=
    fun z => F (solMap b N (e z.1) (c • z.2)) with hΦ
  have hΦc : Continuous Φ :=
    F.continuous.comp ((continuous_solMap_uncurry hb N).comp ((he.comp continuous_fst).prodMk
      ((continuous_const_smul c).comp continuous_snd)))
  set G := fun z : C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) × C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) =>
    A.indicator (fun _ => (1 : ℝ)) z.1 * Φ z with hG
  have hGm : StronglyMeasurable G :=
    ((stronglyMeasurable_const.indicator hA).comp_measurable measurable_fst).mul
      hΦc.stronglyMeasurable
  have hGb : ∀ z, ‖G z‖ ≤ ‖F‖ := by
    intro z
    simp only [hG, norm_mul]
    by_cases hz : z.1 ∈ A
    · rw [indicator_of_mem hz, norm_one, one_mul]; exact F.norm_coe_le_norm _
    · rw [indicator_of_notMem hz, norm_zero, zero_mul]; exact norm_nonneg _
  have hGi : Integrable G ((P.map Y₁).prod (P.map Y₂)) :=
    (integrable_const ‖F‖).mono' hGm.aestronglyMeasurable (Eventually.of_forall hGb)
  -- the inner integral
  set g : E → ℝ := fun y => ∫ ω', F (solMap b N y (c • X' ω')) ∂P with hg
  have hinner : ∀ a, ∫ w, G (a, w) ∂(P.map Y₂) = A.indicator (fun _ => (1 : ℝ)) a * g (e a) := by
    intro a
    simp only [hG]
    rw [integral_const_mul, hlaw, integral_map (f := fun w => Φ (a, w)) hX'.aemeasurable
      (hΦc.comp (Continuous.prodMk_right a)).aestronglyMeasurable]
  have hinm : StronglyMeasurable fun a => ∫ w, G (a, w) ∂(P.map Y₂) :=
    hGm.integral_prod_right'
  calc ∫ ω in {ω | Y₁ ω ∈ A}, F (restartPath T₁ T₂ (solMap b N x₀ (c • X ω))) ∂P
      = ∫ ω, G (Y₁ ω, Y₂ ω) ∂P := by
        rw [← integral_indicator (show MeasurableSet {ω | Y₁ ω ∈ A} from hY₁m hA)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        by_cases hω : Y₁ ω ∈ A
        · rw [indicator_of_mem (show ω ∈ {ω | Y₁ ω ∈ A} from hω)]
          simp only [hG, indicator_of_mem hω, one_mul, hΦ, hrest]
        · rw [indicator_of_notMem (show ω ∉ {ω | Y₁ ω ∈ A} from hω)]
          simp only [hG, indicator_of_notMem hω, zero_mul]
    _ = ∫ z, G z ∂(P.map fun ω => (Y₁ ω, Y₂ ω)) :=
        (integral_map (hY₁m.prodMk hY₂m).aemeasurable hGm.aestronglyMeasurable).symm
    _ = ∫ z, G z ∂((P.map Y₁).prod (P.map Y₂)) := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map hY₁m.aemeasurable hY₂m.aemeasurable).mp hind]
    _ = ∫ a, ∫ w, G (a, w) ∂(P.map Y₂) ∂(P.map Y₁) := integral_prod G hGi
    _ = ∫ ω, ∫ w, G (Y₁ ω, w) ∂(P.map Y₂) ∂P :=
        integral_map hY₁m.aemeasurable hinm.aestronglyMeasurable
    _ = ∫ ω in {ω | Y₁ ω ∈ A}, g (pathExt (solMap b N x₀ (c • X ω)) T₁) ∂P := by
        rw [← integral_indicator (show MeasurableSet {ω | Y₁ ω ∈ A} from hY₁m hA)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [hinner, hend]
        by_cases hω : Y₁ ω ∈ A
        · rw [indicator_of_mem (show ω ∈ {ω | Y₁ ω ∈ A} from hω), indicator_of_mem hω, one_mul]
        · rw [indicator_of_notMem (show ω ∉ {ω | Y₁ ω ∈ A} from hω), indicator_of_notMem hω,
            zero_mul]

omit [NormedSpace ℝ E] in
/-- The path `t ↦ φ(s + t)` on `[0, T₂]` of a path `φ` on `[0, H]` (extended by its end values),
jointly continuous in the time `s` and the path. -/
def restartAt (H T₂ : ℝ≥0) : C(ℝ × C(Icc (0 : ℝ) H, E), C(Icc (0 : ℝ) T₂, E)) :=
  ContinuousMap.curry ⟨fun p => pathExt p.1.2 (p.1.1 + p.2), by
    show Continuous fun p : (ℝ × C(Icc (0 : ℝ) H, E)) × Icc (0 : ℝ) T₂ =>
      p.1.2 (projIcc (0 : ℝ) (H : ℝ) H.coe_nonneg (p.1.1 + p.2))
    have hp := continuous_projIcc (a := (0 : ℝ)) (b := (H : ℝ)) (h := H.coe_nonneg)
    exact continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
      (hp.comp ((continuous_fst.comp continuous_fst).add
        (continuous_subtype_val.comp continuous_snd))))⟩

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem restartAt_apply (H T₂ : ℝ≥0) (s : ℝ)
    (φ : C(Icc (0 : ℝ) H, E)) (t : Icc (0 : ℝ) T₂) :
    restartAt H T₂ (s, φ) t = pathExt φ (s + t) := rfl

omit [NormedSpace ℝ E] in
/-- The restart after `T₁` of the restriction to `[0, T₁ + T₂]` is the restart at `T₁`. -/
@[tmio T, powerlib_foundation] theorem restartPath_restrictPath {T₁ T₂ H : ℝ≥0}
    (h : T₁ + T₂ ≤ H) (φ : C(Icc (0 : ℝ) H, E)) :
    restartPath T₁ T₂ (restrictPath h φ) = restartAt H T₂ ((T₁ : ℝ), φ) := by
  ext t
  show pathExt (restrictPath h φ) (T₁ + t) = pathExt φ (T₁ + t)
  exact pathExt_restrictPath h φ ⟨by linarith [t.2.1, T₁.coe_nonneg],
    by rw [NNReal.coe_add]; linarith [t.2.2]⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `⌈x⌉₊ = j` iff `x ≤ j` and `x > i` for every `i < j`. -/
@[tmio T, powerlib_foundation] theorem natCeil_eq_iff_forall {x : ℝ≥0} {j : ℕ} :
    ⌈x⌉₊ = j ↔ x ≤ j ∧ ∀ i < j, ¬ x ≤ i := by
  constructor
  · rintro rfl
    exact ⟨Nat.le_ceil x, fun i hi hx => absurd (Nat.ceil_le.mpr hx) (not_le.mpr hi)⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (Nat.ceil_le.mpr h1) (not_lt.mp fun hlt => h2 _ hlt (Nat.le_ceil x))

/-- **Strong Markov property of the additive-noise solution** (expectation form): for a version
`X` of a Brownian motion on `[0, H]` and its natural filtration `F_t = σ(X|[0, t])`, a stopping
time `τ ≤ T₀` (`{τ ≤ t} ∈ F_t`), an event `A ∈ F_τ` (`A ∩ {τ ≤ t} ∈ F_t`), `H ≥ T₀ + 1 + T₂`, a
version `X'` on `[0, T₂]` and a bounded continuous `F` on the paths of `[0, T₂]`, the solution
`x = S(x₀, c X)` satisfies `∫_A F(x(τ + ·)) dP = ∫_A E'[F(S(x(τ), c X'))] dP`. The proof
discretises `τ_n = (⌈2^{n+1} τ⌉ + 1)/2^{n+1}` (a stopping time with countably many values,
`F_τ ⊆ F_{τ_n}`), applies the Markov property at each value (`integral_solMap_markov`), and
passes to the limit by path continuity and dominated convergence (`y ↦ E'[F(S(y, c X'))]` is
continuous). -/
@[tmio T, powerlib_foundation] theorem integral_solMap_strongMarkov [IsProbabilityMeasure P]
    [CompleteSpace E] (hB : IsBrownianReal B P) {T₀ T₂ H : ℝ≥0} (hT₂ : 0 < (T₂ : ℝ))
    (hH : T₀ + 1 + T₂ ≤ H)
    [MeasurableSpace C(Icc (0 : ℝ) H, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) H, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)]
    {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    {X : Ω → C(Icc (0 : ℝ) H, Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) H, X ω t 0 = B ⟨t, t.2.1⟩ ω)
    {X' : Ω → C(Icc (0 : ℝ) T₂, Fin 1 → ℝ)} (hX' : Measurable X')
    (hXB' : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T₂, X' ω t 0 = B ⟨t, t.2.1⟩ ω)
    {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T₀)
    (hτ : ∀ (t : ℝ≥0) (ht : t ≤ H), MeasurableSet[(borel C(Icc (0 : ℝ) t, Fin 1 → ℝ)).comap
      fun ω => restrictPath ht (X ω)] {ω | τ ω ≤ t})
    {A : Set Ω} (hA : ∀ (t : ℝ≥0) (ht : t ≤ H), MeasurableSet[(borel C(Icc (0 : ℝ) t,
      Fin 1 → ℝ)).comap fun ω => restrictPath ht (X ω)] (A ∩ {ω | τ ω ≤ t}))
    (F : C(Icc (0 : ℝ) T₂, E) →ᵇ ℝ) :
    ∫ ω in A, F (restartAt H T₂ ((τ ω : ℝ), solMap b N x₀ (c • X ω))) ∂P =
      ∫ ω in A, (∫ ω', F (solMap b N (pathExt (solMap b N x₀ (c • X ω)) (τ ω))
        (c • X' ω')) ∂P) ∂P := by
  classical
  let _ : MeasurableSpace C(Icc (0 : ℝ) H, E) := borel _
  have : BorelSpace C(Icc (0 : ℝ) H, E) := ⟨rfl⟩
  set Fil : ∀ t : ℝ≥0, t ≤ H → MeasurableSpace Ω := fun t ht =>
    (borel C(Icc (0 : ℝ) t, Fin 1 → ℝ)).comap fun ω => restrictPath ht (X ω) with hFil
  have hT₀H : T₀ ≤ H := le_trans (le_trans le_self_add le_self_add) hH
  -- the filtration
  have hle : ∀ t (ht : t ≤ H), Fil t ht ≤ mΩ := by
    intro t ht
    let _ : MeasurableSpace C(Icc (0 : ℝ) t, Fin 1 → ℝ) := borel _
    have : BorelSpace C(Icc (0 : ℝ) t, Fin 1 → ℝ) := ⟨rfl⟩
    exact ((continuous_restrictPath ht).measurable.comp hX).comap_le
  have hmono : ∀ r s (hr : r ≤ H) (hs : s ≤ H), r ≤ s → Fil r hr ≤ Fil s hs := by
    intro r s hr hs hrs
    let _ : MeasurableSpace C(Icc (0 : ℝ) r, Fin 1 → ℝ) := borel _
    have : BorelSpace C(Icc (0 : ℝ) r, Fin 1 → ℝ) := ⟨rfl⟩
    let _ : MeasurableSpace C(Icc (0 : ℝ) s, Fin 1 → ℝ) := borel _
    have : BorelSpace C(Icc (0 : ℝ) s, Fin 1 → ℝ) := ⟨rfl⟩
    have e : (fun ω => restrictPath hr (X ω)) =
        restrictPath hrs ∘ fun ω => restrictPath hs (X ω) := rfl
    simp only [hFil]
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (continuous_restrictPath hrs).measurable.comap_le
  have hτm : Measurable τ := by
    refine measurable_of_Iic fun t => ?_
    by_cases ht : t ≤ H
    · exact hle t ht _ (hτ t ht)
    · have : τ ⁻¹' Iic t = univ := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (hτT ω).trans (hT₀H.trans (not_le.mp ht).le)
      rw [this]
      exact MeasurableSet.univ
  have hAm : MeasurableSet A := by
    have : A = A ∩ {ω | τ ω ≤ T₀} := by
      ext ω; exact ⟨fun h => ⟨h, hτT ω⟩, fun h => h.1⟩
    rw [this]
    exact hle T₀ hT₀H _ (hA T₀ hT₀H)
  -- the solution and the inner expectation
  set S : Ω → C(Icc (0 : ℝ) H, E) := fun ω => solMap b N x₀ (c • X ω) with hS
  have hSm : Measurable S :=
    ((continuous_solMap hb N x₀).comp (continuous_const_smul c)).measurable.comp hX
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, g = fun y => ∫ ω', F (solMap b N y (c • X' ω')) ∂P :=
    ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hg]
    refine continuous_of_dominated (bound := fun _ => ‖F‖) (fun y => ?_)
      (fun y => Eventually.of_forall fun ω' => F.norm_coe_le_norm _) (integrable_const _)
      (Eventually.of_forall fun ω' => ?_)
    · exact (F.continuous.comp ((continuous_solMap hb N y).comp
        (continuous_const_smul c))).measurable.comp hX' |>.aestronglyMeasurable
    · exact F.continuous.comp ((continuous_solMap_uncurry hb N).comp
        (continuous_id.prodMk continuous_const))
  have hgb : ∀ y, ‖g y‖ ≤ ‖F‖ := by
    intro y
    rw [hg]
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (Eventually.of_forall fun ω' => F.norm_coe_le_norm (solMap b N y (c • X' ω')))
    simpa using h
  have hev : Continuous fun q : C(Icc (0 : ℝ) H, E) × ℝ => pathExt q.1 q.2 := by
    show Continuous fun q : C(Icc (0 : ℝ) H, E) × ℝ =>
      q.1 (projIcc (0 : ℝ) (H : ℝ) H.coe_nonneg q.2)
    have hp := continuous_projIcc (a := (0 : ℝ)) (b := (H : ℝ)) (h := H.coe_nonneg)
    exact continuous_eval.comp (continuous_fst.prodMk (hp.comp continuous_snd))
  -- the dyadic approximations
  set d : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) / 2 ^ (n + 1) with hd
  set κ : ℕ → Ω → ℕ := fun n ω => ⌈(2 : ℝ≥0) ^ (n + 1) * τ ω⌉₊ with hκ
  set τn : ℕ → Ω → ℝ≥0 := fun n ω => d n (κ n ω + 1) with hτn
  have h2 : ∀ n : ℕ, (0 : ℝ≥0) < 2 ^ (n + 1) := fun n => by positivity
  have hτn_ge : ∀ n ω, τ ω ≤ τn n ω := by
    intro n ω
    simp only [hτn, hd, hκ]
    rw [le_div_iff₀ (h2 n), mul_comm]
    exact (Nat.le_ceil _).trans (by push_cast; exact le_self_add)
  have hτn_le : ∀ n ω, τn n ω ≤ τ ω + 1 / 2 ^ n := by
    intro n ω
    simp only [hτn, hd, hκ]
    rw [div_le_iff₀ (h2 n)]
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ 2 ^ (n + 1) * τ ω from zero_le)
    have e : (τ ω + 1 / 2 ^ n) * 2 ^ (n + 1) = 2 ^ (n + 1) * τ ω + 2 := by
      rw [add_mul, mul_comm, one_div, pow_succ, ← mul_assoc, inv_mul_cancel₀ (by positivity),
        one_mul]
    rw [e]
    push_cast
    calc (⌈(2 : ℝ≥0) ^ (n + 1) * τ ω⌉₊ : ℝ≥0) + 1 ≤ (2 ^ (n + 1) * τ ω + 1) + 1 :=
          add_le_add h1.le le_rfl
      _ = _ := by ring
  have hτn_T : ∀ n ω, τn n ω ≤ T₀ + 1 := by
    intro n ω
    refine (hτn_le n ω).trans (add_le_add (hτT ω) ?_)
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ one_le_two
  have hτn_tend : ∀ ω, Tendsto (fun n => (τn n ω : ℝ)) atTop (𝓝 (τ ω)) := by
    intro ω
    have hlim : Tendsto (fun n : ℕ => (τ ω : ℝ) + 1 / 2 ^ n) atTop (𝓝 (τ ω)) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_add (τ ω : ℝ)
      rw [add_zero] at h
      refine h.congr fun n => ?_
      rw [one_div_pow]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => NNReal.coe_le_coe.mpr (hτn_ge n ω)) (fun n => ?_)
    have := NNReal.coe_le_coe.mpr (hτn_le n ω)
    push_cast at this
    exact this
  have hκm : ∀ n, Measurable (κ n) := fun n => (Nat.measurable_ceil).comp (measurable_const.mul hτm)
  have hτnm : ∀ n, Measurable (τn n) := fun n =>
    (measurable_from_nat (f := fun k => d n (k + 1))).comp (hκm n)
  have hdmono : ∀ n {i j : ℕ}, i ≤ j → d n i ≤ d n j := by
    intro n i j hij
    simp only [hd]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (h2 n).le
  -- the pieces of `A` on which `τ_n` is constant
  set piece : ℕ → ℕ → Set Ω := fun n j => A ∩ {ω | κ n ω = j} with hpiece
  have hpieceF : ∀ n j (hj : d n j ≤ H), MeasurableSet[Fil (d n j) hj] (piece n j) := by
    intro n j hj
    have hiff : ∀ ω i, (τ ω ≤ d n i ↔ (2 : ℝ≥0) ^ (n + 1) * τ ω ≤ i) := fun ω i => by
      simp only [hd]; rw [le_div_iff₀ (h2 n), mul_comm]
    have e : piece n j = (A ∩ {ω | τ ω ≤ d n j}) \
        ⋃ i ∈ Finset.range j, {ω | τ ω ≤ d n i} := by
      ext ω
      simp only [hpiece, hκ, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, mem_iUnion,
        Finset.mem_range, not_exists]
      constructor
      · rintro ⟨hA', hk⟩
        obtain ⟨h1, h3⟩ := natCeil_eq_iff_forall.mp hk
        exact ⟨⟨hA', (hiff ω j).mpr h1⟩, fun i hi hle => h3 i hi ((hiff ω i).mp hle)⟩
      · rintro ⟨⟨hA', h1⟩, h3⟩
        exact ⟨hA', natCeil_eq_iff_forall.mpr
          ⟨(hiff ω j).mp h1, fun i hi hle => h3 i hi ((hiff ω i).mpr hle)⟩⟩
    rw [e]
    refine (hA (d n j) hj).diff (Finset.measurableSet_biUnion _ fun i hi => ?_)
    have hij : d n i ≤ d n j := hdmono n (Finset.mem_range.mp hi).le
    exact hmono _ _ (hij.trans hj) hj hij _ (hτ (d n i) (hij.trans hj))
  -- the Markov property on one piece
  have hpiece_markov : ∀ n j, d n (j + 1) + T₂ ≤ H →
      ∫ ω in piece n j, F (restartAt H T₂ ((d n (j + 1) : ℝ), S ω)) ∂P =
        ∫ ω in piece n j, g (pathExt (S ω) (d n (j + 1))) ∂P := by
    intro n j h
    set s := d n (j + 1) with hs_def
    have hs0 : 0 < (s : ℝ) := by
      simp only [hs_def, hd]
      have : (0 : ℝ≥0) < ((j + 1 : ℕ) : ℝ≥0) / 2 ^ (n + 1) := by positivity
      exact_mod_cast this
    have hsH : s ≤ H := le_trans le_self_add h
    have hjs : d n j ≤ s := hdmono n (Nat.le_succ j)
    let _ : MeasurableSpace C(Icc (0 : ℝ) s, Fin 1 → ℝ) := borel _
    have : BorelSpace C(Icc (0 : ℝ) s, Fin 1 → ℝ) := ⟨rfl⟩
    let _ : MeasurableSpace C(Icc (0 : ℝ) (s + T₂ : ℝ≥0), Fin 1 → ℝ) := borel _
    have : BorelSpace C(Icc (0 : ℝ) (s + T₂ : ℝ≥0), Fin 1 → ℝ) := ⟨rfl⟩
    obtain ⟨A', hA'm, hA'eq⟩ := MeasurableSpace.measurableSet_comap.mp
      (hmono _ _ (hjs.trans hsH) hsH hjs _ (hpieceF n j (hjs.trans hsH)))
    set Xs : Ω → C(Icc (0 : ℝ) (s + T₂ : ℝ≥0), Fin 1 → ℝ) := fun ω => restrictPath h (X ω)
      with hXs
    have hXsm : Measurable Xs := (continuous_restrictPath h).measurable.comp hX
    have hXsB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (s + T₂ : ℝ≥0), Xs ω t 0 = B ⟨t, t.2.1⟩ ω := by
      filter_upwards [hXB] with ω hω t
      exact hω _
    have hM := integral_solMap_markov hB hs0 hT₂ hb N x₀ c hXsm hXsB hX' hXB' hA'm F
    have hset : {ω | restrictPath le_self_add (Xs ω) ∈ A'} = piece n j := hA'eq
    have e1 : ∀ ω, solMap b N x₀ (c • Xs ω) = restrictPath h (S ω) := fun ω => by
      simp only [hXs, hS]
      rw [restrictPath_solMap hb, restrictPath_smul]
    have hsm : (s : ℝ) ∈ Icc (0 : ℝ) (s + T₂ : ℝ≥0) :=
      ⟨s.coe_nonneg, by rw [NNReal.coe_add]; linarith [T₂.coe_nonneg]⟩
    rw [hset] at hM
    simp only [e1, restartPath_restrictPath, pathExt_restrictPath h _ hsm] at hM
    rw [hg]
    exact hM
  -- the identity at each dyadic level
  have hlevel : ∀ n, ∫ ω in A, F (restartAt H T₂ ((τn n ω : ℝ), S ω)) ∂P =
      ∫ ω in A, g (pathExt (S ω) (τn n ω)) ∂P := by
    intro n
    have hpm : ∀ j, MeasurableSet (piece n j) := fun j =>
      hAm.inter (hκm n (measurableSet_singleton j))
    have hU : A = ⋃ j, piece n j := by
      ext ω
      simp only [hpiece, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨κ n ω, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
    have hdisj : Pairwise (Function.onFun Disjoint (piece n)) := fun i j hij =>
      Set.disjoint_left.mpr fun ω h1 h2 => hij (h1.2.symm.trans h2.2)
    have hFm : Measurable fun ω => F (restartAt H T₂ ((τn n ω : ℝ), S ω)) :=
      (F.continuous.comp (restartAt H T₂).continuous).measurable.comp
        ((NNReal.continuous_coe.measurable.comp (hτnm n)).prodMk hSm)
    have hgm : Measurable fun ω => g (pathExt (S ω) (τn n ω)) :=
      (hgc.comp hev).measurable.comp (hSm.prodMk (NNReal.continuous_coe.measurable.comp
        (hτnm n)))
    have hFi : IntegrableOn (fun ω => F (restartAt H T₂ ((τn n ω : ℝ), S ω))) (⋃ j, piece n j)
        P := ((integrable_const ‖F‖).mono' hFm.aestronglyMeasurable
          (Eventually.of_forall fun ω => F.norm_coe_le_norm _)).integrableOn
    have hgi : IntegrableOn (fun ω => g (pathExt (S ω) (τn n ω))) (⋃ j, piece n j) P :=
      ((integrable_const ‖F‖).mono' hgm.aestronglyMeasurable
        (Eventually.of_forall fun ω => hgb _)).integrableOn
    rw [hU, integral_iUnion hpm hdisj hFi, integral_iUnion hpm hdisj hgi]
    refine tsum_congr fun j => ?_
    have hval : ∀ ω ∈ piece n j, τn n ω = d n (j + 1) := fun ω hω => by
      simp only [hτn]; rw [hω.2]
    rw [setIntegral_congr_fun (hpm j)
        (g := fun ω => F (restartAt H T₂ ((d n (j + 1) : ℝ), S ω)))
        (fun ω hω => by simp only [hval ω hω]),
      setIntegral_congr_fun (hpm j) (f := fun ω => g (pathExt (S ω) (τn n ω)))
        (g := fun ω => g (pathExt (S ω) (d n (j + 1))))
        (fun ω hω => by simp only [hval ω hω])]
    by_cases hjH : d n (j + 1) + T₂ ≤ H
    · exact hpiece_markov n j hjH
    · have hemp : piece n j = ∅ := by
        ext ω
        simp only [mem_empty_iff_false, iff_false]
        intro hω
        apply hjH
        rw [← hval ω hω]
        exact (add_le_add (hτn_T n ω) le_rfl).trans hH
      rw [hemp, setIntegral_empty, setIntegral_empty]
  -- the limit
  have hL : Tendsto (fun n => ∫ ω in A, F (restartAt H T₂ ((τn n ω : ℝ), S ω)) ∂P) atTop
      (𝓝 (∫ ω in A, F (restartAt H T₂ ((τ ω : ℝ), S ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => F.norm_coe_le_norm _)
      (Eventually.of_forall fun ω => ?_)
    · exact ((F.continuous.comp (restartAt H T₂).continuous).measurable.comp
        ((NNReal.continuous_coe.measurable.comp (hτnm n)).prodMk hSm)).aestronglyMeasurable
    · exact ((F.continuous.comp (restartAt H T₂).continuous).tendsto ((τ ω : ℝ), S ω)).comp
        ((hτn_tend ω).prodMk_nhds tendsto_const_nhds)
  have hR : Tendsto (fun n => ∫ ω in A, g (pathExt (S ω) (τn n ω)) ∂P) atTop
      (𝓝 (∫ ω in A, g (pathExt (S ω) (τ ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => hgb _)
      (Eventually.of_forall fun ω => ?_)
    · exact ((hgc.comp hev).measurable.comp (hSm.prodMk
        (NNReal.continuous_coe.measurable.comp (hτnm n)))).aestronglyMeasurable
    · exact ((hgc.comp hev).tendsto (S ω, (τ ω : ℝ))).comp
        (tendsto_const_nhds.prodMk_nhds (hτn_tend ω))
  simp_rw [hlevel] at hL
  rw [tendsto_nhds_unique hL hR, hg]

end powerlib.Stochastic.LDP
