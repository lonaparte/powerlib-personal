import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ExitTime
import theorem.Stochastic.UniformLDP
import theorem.Stochastic.LDPContraction

/-! # The Markov step on the paths of a Brownian motion and explicit large-deviation bounds

For a Brownian motion `B` all of whose paths are continuous and the solution
`S(y, c B) = solMap b N y (c • brownPath B hBc T)` of `x(t) = y + c N B(t) + ∫₀ᵗ b(x)` on
`[0, T]` (`b` globally Lipschitz): the Markov property at a deterministic time written on the
paths of `B` themselves (no version in the statement), so that the time blocks `[kT, (k + 1)T]`
of one solution can be chained; the explicit form of the uniform large-deviation upper bound
(`P(S(y, √ε B) ∈ A) ≤ e^{−(v − γ)/ε}` for all small `ε`, uniformly over a compact set of initial
points, whenever the Freidlin–Wentzell rate is at least `v` on `cl A`); and the size of a driving
path of small Schilder rate.

Scope.
* Generic: `E` a real Banach space, one noise column `N : (Fin 1 → ℝ) →L[ℝ] E`, `B` a Brownian
  motion (Mathlib's `IsBrownianReal`) all of whose paths are continuous, path spaces with their
  Borel σ-algebras. Deterministic times only; events of the solution paths (not general events
  of the Brownian filtration).

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 3 §3 (uniformity in the initial point) and Ch. 4 §2 (time blocks); A. Dembo, O. Zeitouni,
*Large Deviations Techniques and Applications*, 2nd ed. (1998), Cor. 5.6.15.

Results.
* `sq_le_of_schilderRate_lt`, `norm_le_of_schilderRate_lt`: `schilderRate T w < c` gives
  `w(t)² ≤ 2ct` and `‖w‖ ≤ √(2cT)` (Cauchy–Schwarz).
* `nullMeasurableSet_brownPath`: the event `S(y, c B) ∈ A` is null-measurable for measurable `A`.
* `measure_brownPath_markov` (**Markov property on the paths of `B`**):
  `P(S_{T₁} ∈ A, x(T₁ + ·) ∈ C) = ∫_{S_{T₁} ∈ A} P(S(x(T₁), c B|[0, T₂]) ∈ C) dP`.
* `eventually_measure_brownPath_le` (**explicit uniform upper bound**).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Size of a driving path of small rate**: `schilderRate T w < c` gives `w(t)² ≤ 2 c t`. -/
@[tmio T, powerlib_foundation] theorem sq_le_of_schilderRate_lt {T : ℝ≥0}
    {w : C(Icc (0 : ℝ) T, Fin 1 → ℝ)} {c : ℝ} (h : schilderRate T w < ENNReal.ofReal c)
    (t : Icc (0 : ℝ) T) : w t 0 ^ 2 ≤ 2 * c * t := by
  simp only [schilderRate, iInf_lt_iff] at h
  obtain ⟨u, ⟨hu, hu2, hxu⟩, hact⟩ := h
  have hT0 := T.coe_nonneg
  set v : ℝ → ℝ := fun r => u r 0 with hv
  have hvi : IntervalIntegrable v volume 0 T :=
    ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp hu.1,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp hu.2⟩
  have hv2 : IntervalIntegrable (fun r => v r ^ 2) volume 0 T := by simpa [hv] using hu2
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le t.2.1, uIcc_of_le hT0]; exact Icc_subset_Icc_right t.2.2
  have hxv : w t 0 = ∫ s in (0 : ℝ)..t, v s := by
    rw [hxu]
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
      ).intervalIntegral_comp_comm (hu.mono_set hsub)).symm
  rw [hxv]
  have hcs := sq_integral_le t.2.1 (hvi.mono_set hsub) (hv2.mono_set hsub)
  have hmono : ∫ r in (0 : ℝ)..t, v r ^ 2 ≤ ∫ r in (0 : ℝ)..T, v r ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl t.2.1 t.2.2
      (Eventually.of_forall fun r => sq_nonneg _) hv2
  have hca : controlAction u T = 1 / 2 * ∫ r in (0 : ℝ)..T, v r ^ 2 := by
    unfold controlAction; congr 1; simp [hv]
  have hact' : controlAction u T < c := (ENNReal.ofReal_lt_ofReal_iff'.mp hact).1
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  calc (∫ s in (0 : ℝ)..t, v s) ^ 2 ≤ ((t : ℝ) - 0) * ∫ r in (0 : ℝ)..t, v r ^ 2 := hcs
    _ ≤ (t : ℝ) * ∫ r in (0 : ℝ)..T, v r ^ 2 := by
        rw [sub_zero]; exact mul_le_mul_of_nonneg_left hmono ht0
    _ ≤ (t : ℝ) * (2 * c) := mul_le_mul_of_nonneg_left (by linarith) ht0
    _ = 2 * c * t := by ring

/-- `schilderRate T w < c` gives `‖w‖ ≤ √(2 c T)`. -/
@[tmio T, powerlib_foundation] theorem norm_le_of_schilderRate_lt {T : ℝ≥0}
    {w : C(Icc (0 : ℝ) T, Fin 1 → ℝ)} {c : ℝ} (h : schilderRate T w < ENNReal.ofReal c) :
    ‖w‖ ≤ Real.sqrt (2 * c * T) := by
  have hc0 : 0 < c := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le h)
  refine (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr fun t => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Subsingleton.elim i 0, Real.norm_eq_abs]
  refine Real.abs_le_sqrt ((sq_le_of_schilderRate_lt h t).trans ?_)
  have := t.2.2
  nlinarith

section Markov

variable [CompleteSpace E]

/-- The event that `S(y, c B)` lies in a measurable set of paths is null-measurable. -/
@[tmio T, powerlib_foundation] theorem nullMeasurableSet_brownPath [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, E)] [BorelSpace C(Icc (0 : ℝ) T, E)]
    {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) (y : E) (c : ℝ)
    {A : Set C(Icc (0 : ℝ) T, E)} (hA : MeasurableSet A) :
    NullMeasurableSet {ω | solMap b N y (c • brownPath B hBc T ω) ∈ A} P := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := ⟨rfl⟩
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT
  have hm : MeasurableSet {ω | solMap b N y (c • X ω) ∈ A} :=
    ((continuous_solMap hb N y).comp (continuous_const_smul c)).measurable.comp hX hA
  have hae : {ω | solMap b N y (c • brownPath B hBc T ω) ∈ A} =ᵐ[P]
      {ω | solMap b N y (c • X ω) ∈ A} := by
    filter_upwards [brownPath_ae_eq hBc hXB] with ω hω
    simp only [hω]
  exact hm.nullMeasurableSet.congr hae.symm

/-- **Markov property on the paths of `B`** at a deterministic time `T₁`:
`P(S_{T₁} ∈ A, x(T₁ + ·) ∈ C) = ∫_{S_{T₁} ∈ A} P(S(x(T₁), c B|[0, T₂]) ∈ C) dP`. -/
@[tmio T, powerlib_foundation] theorem measure_brownPath_markov [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T₁ T₂ : ℝ≥0}
    (hT₁ : 0 < (T₁ : ℝ)) (hT₂ : 0 < (T₂ : ℝ))
    [MeasurableSpace C(Icc (0 : ℝ) T₁, E)] [BorelSpace C(Icc (0 : ℝ) T₁, E)]
    [MeasurableSpace C(Icc (0 : ℝ) T₂, E)] [BorelSpace C(Icc (0 : ℝ) T₂, E)]
    {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    {A : Set C(Icc (0 : ℝ) T₁, E)} (hA : MeasurableSet A) {C : Set C(Icc (0 : ℝ) T₂, E)}
    (hC : MeasurableSet C) :
    P {ω | solMap b N x₀ (c • brownPath B hBc T₁ ω) ∈ A ∧
        restartPath T₁ T₂ (solMap b N x₀ (c • brownPath B hBc (T₁ + T₂) ω)) ∈ C} =
      ∫⁻ ω in {ω | solMap b N x₀ (c • brownPath B hBc T₁ ω) ∈ A},
        P {ω' | solMap b N (pathExt (solMap b N x₀ (c • brownPath B hBc T₁ ω)) T₁)
          (c • brownPath B hBc T₂ ω') ∈ C} ∂P := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ) := ⟨rfl⟩
  have hT : 0 < ((T₁ + T₂ : ℝ≥0) : ℝ) := by push_cast; linarith
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT
  obtain ⟨X', hX', -, hXB'⟩ := exists_version (P := P) hB hT₂
  have hmk := measure_solMap_markov hB hT₁ hT₂ hb N x₀ c hX hXB hX' hXB' hA hC
  have hfull : ∀ᵐ ω ∂P, brownPath B hBc (T₁ + T₂) ω = X ω := brownPath_ae_eq hBc hXB
  have hpast : ∀ᵐ ω ∂P, restrictPath le_self_add (solMap b N x₀ (c • X ω)) =
      solMap b N x₀ (c • brownPath B hBc T₁ ω) := by
    filter_upwards [hfull] with ω hω
    rw [restrictPath_solMap hb, restrictPath_smul, ← hω, restrictPath_brownPath]
  have hfut : ∀ y, P {ω' | solMap b N y (c • X' ω') ∈ C} =
      P {ω' | solMap b N y (c • brownPath B hBc T₂ ω') ∈ C} := by
    intro y
    refine measure_congr ?_
    filter_upwards [brownPath_ae_eq hBc hXB'] with ω hω
    simp only [hω]
  have hset : {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A} =ᵐ[P]
      {ω | solMap b N x₀ (c • brownPath B hBc T₁ ω) ∈ A} := by
    filter_upwards [hpast] with ω hω
    simp only [hω]
  have hT₁mem : (T₁ : ℝ) ∈ Icc (0 : ℝ) T₁ := ⟨T₁.coe_nonneg, le_rfl⟩
  calc _ = P {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈ A ∧
        restartPath T₁ T₂ (solMap b N x₀ (c • X ω)) ∈ C} := by
        refine measure_congr ?_
        filter_upwards [hpast, hfull] with ω h1 h2
        simp only [h1, h2]
    _ = _ := hmk
    _ = _ := by
        rw [Measure.restrict_congr_set hset]
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hpast] with ω hω
        rw [← pathExt_restrictPath le_self_add _ hT₁mem, hω, hfut]

/-- **Explicit uniform upper bound**: if the Freidlin–Wentzell rate is at least `v` on `cl A`
from every point of a compact `Kc`, then for every `γ > 0`, eventually in `ε → 0⁺`,
`P(S(y, √ε B) ∈ A) ≤ e^{−(v − γ)/ε}` for all `y ∈ Kc`. -/
@[tmio T, powerlib_foundation] theorem eventually_measure_brownPath_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) {Kc : Set E} (hKc : IsCompact Kc) (A : Set C(Icc (0 : ℝ) T, E))
    {v : ℝ} (hv : ∀ y ∈ Kc, ∀ φ ∈ closure A,
      ENNReal.ofReal v ≤ pushRate (solMap b N y) (schilderRate T) φ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Kc, P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈ A} ≤
      ENNReal.ofReal (Real.exp (-(v - γ) / ε)) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := ⟨rfl⟩
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ id ε :=
    eventually_nhdsWithin_of_forall fun ε hε => le_of_lt hε
  have hu := (isLDP_schilder hB hT hX hXB).limsup_iSup_solMap_le hs hb N hKc A
  have hinf : ((v : ℝ) : EReal) ≤ ⨅ y ∈ Kc, ⨅ φ ∈ closure A,
      ((pushRate (solMap b N y) (schilderRate T) φ : ℝ≥0∞) : EReal) := by
    refine le_iInf₂ fun y hy => le_iInf₂ fun φ hφ => ?_
    refine le_trans ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hv y hy φ hφ))
    rw [EReal.coe_ennreal_ofReal]
    exact_mod_cast le_max_left v 0
  have hlt : limsup (fun ε : ℝ => ((id ε : ℝ) : EReal) * ENNReal.log
      (⨆ y ∈ Kc, (P.map fun ω => √ε • X ω) (solMap b N y ⁻¹' A))) (𝓝[>] 0) <
      ((-(v - γ) : ℝ) : EReal) := by
    refine lt_of_le_of_lt hu (lt_of_le_of_lt (EReal.neg_le_neg_iff.mpr hinf) ?_)
    rw [← EReal.coe_neg]
    exact_mod_cast (by linarith : -v < -(v - γ))
  filter_upwards [eventually_lt_of_limsup_lt hlt, self_mem_nhdsWithin] with ε hε (hε0 : 0 < ε)
    y hy
  refine le_trans ?_ (le_exp_of_mul_log_le hε0 hε.le)
  refine le_trans ?_ (le_iSup₂ (f := fun y _ => (P.map fun ω => √ε • X ω) (solMap b N y ⁻¹' A))
    y hy)
  refine (le_of_eq (measure_congr ?_)).trans
    (Measure.le_map_apply (hX.const_smul (√ε)).aemeasurable _)
  filter_upwards [brownPath_ae_eq hBc hXB] with ω hω
  show (solMap b N y (√ε • brownPath B hBc T ω) ∈ A) = (solMap b N y (√ε • X ω) ∈ A)
  rw [hω]

end Markov

end powerlib.Stochastic.LDP
