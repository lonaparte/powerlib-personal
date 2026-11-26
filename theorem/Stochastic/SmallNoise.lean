import theorem.Dynamics.Locality
import dependencies.LeanForControl

/-! # Additive-noise ODEs: existence, uniqueness and the small-noise expansion

The random ODE `dx = f(x) dt + σ dw` with additive noise, read path by path as the integral
equation `x(t) = a + ∫₀ᵗ f(x(s)) ds + σ(w(t) − w(0))` on `[0, T]` for a continuous noise path `w`:
uniqueness for `C¹` fields, existence for `C¹` fields with a one-sided growth bound (no blow-up),
existence for the variational equation along a curve, and the uniform first-order expansion
`x_σ = x₀ + σ ζ + O(σ²)` for `C²` fields.

Scope.
* State `Dynamics.State n = EuclideanSpace ℝ (Fin n)`, autonomous field `f : ℝⁿ → ℝⁿ`, noise
  intensity `σ ∈ ℝ`, noise path `w : ℝ → ℝⁿ` (continuous where stated; uniqueness needs no
  regularity of `w`), finite horizon `[0, T]`, solutions continuous on `ℝ` and solving the
  equation on `[0, T]`. Deterministic analysis, sample path by sample path: no probability, no
  Itô calculus (for additive noise none is needed: `x − σ(w − w(0))` solves a classical ODE with
  continuous time dependence).
* Existence uses the growth bound `⟪y, f(y + e)⟫ ≤ K‖y‖² + K'` for `‖e‖ ≤ m` (constants depending
  on `m`), proved for the supercritical Hopf normal form in `theorem/Stochastic/NoisyHopf.lean`.
  The proof extends `f` outside a ball to a globally Lipschitz field
  (`Dynamics.exists_contDiff_lipschitz_extension`), solves the extended equation
  (LeanForControl `exists_isIntegralCurveOn_Icc`) and shows by the first-exit argument
  (`Dynamics.forall_lt_of_first_exit`) and the Grönwall bound that the solution never leaves the
  ball.
* The expansion is local in the noise intensity: it holds for `|σ| ≤ σ₀` with explicit constants
  from bounds of `f'` and `f''` on a ball around the noise-free solution.
* Generic mathematics; no model.

Source: the small-noise (linear-response) expansion behind the amplitude–phase description of a
noisy limit cycle, IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.1,
eqs. (3-26)–(3-28) (`z = (√γ + p) e^{iφ}` with `p` an OU process and `φ` a Brownian phase).

Results.
* `eqOn_of_additiveNoise` — two continuous solutions of the integral equation coincide on
  `[0, T]` (`C¹` field; Mathlib's `ODE_solution_unique_of_mem_Icc_right` for the extended field).
* `exists_additiveNoise` — existence of a continuous solution on `[0, T]` under the growth bound.
* `exists_variational` — the linear equation `ζ(t) = ∫₀ᵗ f'(x₀(s)) ζ(s) ds + (w(t) − w(0))` has a
  continuous solution on `[0, T]`.
* `norm_sub_sub_smul_le` — **small-noise expansion**: for `C²` `f` there are `σ₀ > 0` and `C`
  with `‖x_σ(t) − x₀(t) − σ ζ(t)‖ ≤ C σ²` on `[0, T]` for every solution `x_σ`, `|σ| ≤ σ₀`.
-/

noncomputable section
namespace powerlib.Stochastic.SmallNoise

open Set Filter Topology Metric
open powerlib.Dynamics (State)

variable {n : ℕ}

local notation "ℝⁿ" => State n

/-- A continuous curve is bounded on a compact interval. -/
@[tmio T, powerlib_foundation] private theorem exists_norm_le_Icc {T : ℝ} {x : ℝ → ℝⁿ}
    (hx : ContinuousOn x (Icc 0 T)) : ∃ R, ∀ t ∈ Icc (0 : ℝ) T, ‖x t‖ ≤ R :=
  (isCompact_Icc.exists_bound_of_continuousOn hx)

/-- Translating the argument keeps a Lipschitz constant. -/
@[tmio T, powerlib_foundation] private theorem lipschitzWith_comp_add {g : ℝⁿ → ℝⁿ} {K : NNReal}
    (hg : LipschitzWith K g) (c : ℝⁿ) : LipschitzWith K fun y => g (y + c) :=
  LipschitzWith.of_dist_le_mul fun y y' => by
    simpa [dist_add_right] using hg.dist_le_mul (y + c) (y' + c)

/-- **Uniqueness for an additive-noise ODE.** For a `C¹` field `f`, any noise path `w` and
`σ ∈ ℝ`, two continuous solutions of `x(t) = a + ∫₀ᵗ f(x(s)) ds + σ(w(t) − w(0))` on
`[0, T]` coincide there. -/
@[tmio T, powerlib_foundation] theorem eqOn_of_additiveNoise {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 1 f)
    {a : ℝⁿ} {σ : ℝ} {w : ℝ → ℝⁿ} {T : ℝ} {x₁ x₂ : ℝ → ℝⁿ}
    (hx₁ : Continuous x₁) (hx₂ : Continuous x₂)
    (h₁ : ∀ t ∈ Icc 0 T, x₁ t = a + (∫ s in (0 : ℝ)..t, f (x₁ s)) + σ • (w t - w 0))
    (h₂ : ∀ t ∈ Icc 0 T, x₂ t = a + (∫ s in (0 : ℝ)..t, f (x₂ s)) + σ • (w t - w 0)) :
    EqOn x₁ x₂ (Icc 0 T) := by
  obtain ⟨R₁, hR₁⟩ := exists_norm_le_Icc (T := T) hx₁.continuousOn
  obtain ⟨R₂, hR₂⟩ := exists_norm_le_Icc (T := T) hx₂.continuousOn
  obtain ⟨g, -, ⟨K, hK⟩, hgf⟩ := Dynamics.exists_contDiff_lipschitz_extension hf (max R₁ R₂)
  set e : ℝ → ℝⁿ := fun t => σ • (w t - w 0)
  set Y₁ : ℝ → ℝⁿ := fun t => a + ∫ s in (0 : ℝ)..t, f (x₁ s)
  set Y₂ : ℝ → ℝⁿ := fun t => a + ∫ s in (0 : ℝ)..t, f (x₂ s)
  have hY₁ : ∀ t, HasDerivAt Y₁ (f (x₁ t)) t := fun t =>
    (((hf.continuous.comp hx₁).integral_hasStrictDerivAt 0 t).hasDerivAt).const_add a
  have hY₂ : ∀ t, HasDerivAt Y₂ (f (x₂ t)) t := fun t =>
    (((hf.continuous.comp hx₂).integral_hasStrictDerivAt 0 t).hasDerivAt).const_add a
  have hx₁Y : ∀ t ∈ Icc 0 T, x₁ t = Y₁ t + e t := h₁
  have hx₂Y : ∀ t ∈ Icc 0 T, x₂ t = Y₂ t + e t := h₂
  have hv : ∀ t ∈ Ico (0 : ℝ) T, LipschitzOnWith K (fun y => g (y + e t)) univ := fun t _ =>
    (lipschitzWith_comp_add hK (e t)).lipschitzOnWith
  have hYeq : EqOn Y₁ Y₂ (Icc 0 T) := by
    refine ODE_solution_unique_of_mem_Icc_right (v := fun t y => g (y + e t)) hv
      (continuous_iff_continuousAt.2 fun t => (hY₁ t).continuousAt).continuousOn
      (fun t ht => ?_) (fun _ _ => mem_univ _)
      (continuous_iff_continuousAt.2 fun t => (hY₂ t).continuousAt).continuousOn
      (fun t ht => ?_) (fun _ _ => mem_univ _) (by simp [Y₁, Y₂])
    · have htI : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have : g (Y₁ t + e t) = f (x₁ t) := by
        rw [← hx₁Y t htI]; exact hgf _ ((hR₁ t htI).trans (le_max_left _ _))
      rw [this]; exact (hY₁ t).hasDerivWithinAt
    · have htI : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have : g (Y₂ t + e t) = f (x₂ t) := by
        rw [← hx₂Y t htI]; exact hgf _ ((hR₂ t htI).trans (le_max_right _ _))
      rw [this]; exact (hY₂ t).hasDerivWithinAt
  intro t ht
  rw [hx₁Y t ht, hx₂Y t ht, hYeq ht]

/-- **Existence for a dissipative additive-noise ODE.** Let `f` be a `C¹` field with the one-sided
growth bound `⟪y, f(y + e)⟫ ≤ K‖y‖² + K'` for `‖e‖ ≤ m` (constants depending on `m`). Then for
every continuous noise path `w`, `σ ∈ ℝ`, `a` and `T ≥ 0` the integral equation
`x(t) = a + ∫₀ᵗ f(x(s)) ds + σ(w(t) − w(0))` has a continuous solution on `[0, T]` (unique by
`eqOn_of_additiveNoise`). The growth bound excludes blow-up: `‖x − σ(w − w(0))‖²` obeys
`V̇ ≤ 2K V + 2K'` on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem exists_additiveNoise {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 1 f)
    (hdiss : ∀ m : ℝ, ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧
      ∀ y e : ℝⁿ, ‖e‖ ≤ m → inner ℝ y (f (y + e)) ≤ K * ‖y‖ ^ 2 + K')
    (a : ℝⁿ) (σ : ℝ) {w : ℝ → ℝⁿ} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x : ℝ → ℝⁿ, Continuous x ∧
      ∀ t ∈ Icc 0 T, x t = a + (∫ s in (0 : ℝ)..t, f (x s)) + σ • (w t - w 0) := by
  -- the noise, frozen outside `[0, T]`
  set e : ℝ → ℝⁿ := fun t => σ • (w (projIcc 0 T hT t) - w 0) with he
  have hec : Continuous e := by
    have h1 : Continuous fun t => w (projIcc 0 T hT t) :=
      hw.comp (continuous_subtype_val.comp continuous_projIcc)
    exact (continuous_const (y := σ)).smul (h1.sub continuous_const)
  have heI : ∀ t ∈ Icc 0 T, e t = σ • (w t - w 0) := fun t ht => by
    simp [he, projIcc_of_mem hT ht]
  obtain ⟨m, hm⟩ : ∃ m, ∀ t, ‖e t‖ ≤ m := by
    obtain ⟨m, hm⟩ := isCompact_Icc.exists_bound_of_continuousOn (hec.continuousOn (s := Icc 0 T))
    refine ⟨m, fun t => ?_⟩
    have : e t = e (projIcc 0 T hT t) := by simp [he]
    rw [this]; exact hm _ (projIcc 0 T hT t).2
  obtain ⟨K, K', hK, hK', hb⟩ := hdiss m
  set B := gronwallBound (‖a‖ ^ 2) (2 * K) (2 * K') T
  have hB0 : 0 ≤ B := by
    have := gronwallBound_mono (sq_nonneg ‖a‖) (by positivity : (0 : ℝ) ≤ 2 * K')
      (by positivity : (0 : ℝ) ≤ 2 * K) hT
    rw [gronwallBound_x0] at this
    exact (sq_nonneg _).trans this
  set R := √B + m + 1
  obtain ⟨g, -, ⟨Kg, hKg⟩, hgf⟩ := Dynamics.exists_contDiff_lipschitz_extension hf R
  set G : ℝ → ℝⁿ → ℝⁿ := fun t y => g (y + e t)
  have hGc : Continuous (Function.uncurry G) :=
    hKg.continuous.comp (continuous_snd.add (hec.comp continuous_fst))
  obtain ⟨α, hα0, hα⟩ := exists_isIntegralCurveOn_Icc hGc
    (fun t => lipschitzWith_comp_add hKg (e t)) 0 T a
  have hαc : ContinuousOn α (Icc 0 T) := hα.continuousOn
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0)
  have he0 : e 0 = 0 := by rw [heI 0 ⟨le_rfl, hT⟩]; simp
  -- derivative of `α` within `[u, ∞)` for `u ∈ [0, T)`
  have hαd : ∀ u ∈ Ico 0 T, HasDerivWithinAt α (G u (α u)) (Ici u) u := fun u hu =>
    (hα u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hu)
  -- bootstrap: the solution of the extended field stays in the ball where `g = f`
  have hball : ∀ u ∈ Icc 0 T, ‖α u + e u‖ < R := by
    refine Dynamics.forall_lt_of_first_exit (φ := fun u => α u + e u) continuous_norm
      (hαc.add hec.continuousOn) ?_ ?_
    · simp only [hα0, he0, add_zero]
      have h1 : ‖a‖ ≤ √B := by
        have h2 : ‖a‖ ^ 2 ≤ B := by
          have := gronwallBound_mono (sq_nonneg ‖a‖) (by positivity : (0 : ℝ) ≤ 2 * K')
            (by positivity : (0 : ℝ) ≤ 2 * K) hT
          rwa [gronwallBound_x0] at this
        exact Real.le_sqrt_of_sq_le h2
      linarith
    · intro s hs hle
      have hsT : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hs.2
      have hV : ∀ u ∈ Ico 0 s, HasDerivWithinAt (fun u => ‖α u‖ ^ 2)
          (2 * inner ℝ (α u) (G u (α u))) (Ici u) u := fun u hu =>
        (hαd u ⟨hu.1, hu.2.trans_le hs.2⟩).norm_sq
      have hgr := le_gronwallBound_of_liminf_deriv_right_le (f := fun u => ‖α u‖ ^ 2)
        (f' := fun u => 2 * inner ℝ (α u) (G u (α u))) (δ := ‖a‖ ^ 2) (K := 2 * K)
        (ε := 2 * K') (a := 0) (b := s) ((hαc.mono hsT).norm.pow 2)
        (fun u hu r hr => (hV u hu).liminf_right_slope_le hr) (by simp [hα0])
        (fun u hu => by
          have hgu : G u (α u) = f (α u + e u) :=
            hgf _ (hle u (Ico_subset_Icc_self hu))
          rw [hgu]
          have := hb (α u) (e u) (hm u)
          linarith) s (right_mem_Icc.2 hs.1)
      have hVs : ‖α s‖ ^ 2 ≤ B := by
        refine hgr.trans ?_
        rw [sub_zero]
        exact gronwallBound_mono (sq_nonneg ‖a‖) (by positivity : (0 : ℝ) ≤ 2 * K')
          (by positivity : (0 : ℝ) ≤ 2 * K) hs.2
      have h1 : ‖α s‖ ≤ √B := Real.le_sqrt_of_sq_le hVs
      calc ‖α s + e s‖ ≤ ‖α s‖ + ‖e s‖ := norm_add_le _ _
        _ ≤ √B + m := add_le_add h1 (hm s)
        _ < R := by linarith
  have hGf : ∀ u ∈ Icc 0 T, G u (α u) = f (α u + e u) := fun u hu =>
    hgf _ (hball u hu).le
  refine ⟨fun t => α (projIcc 0 T hT t) + σ • (w t - w 0), ?_, fun t ht => ?_⟩
  · exact (hαc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun t => (projIcc 0 T hT t).2).add
      ((continuous_const (y := σ)).smul (hw.sub continuous_const))
  · simp only [projIcc_of_mem hT ht]
    congr 1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hαc.mono (Icc_subset_Icc le_rfl ht.2))
      (fun u hu => ((hα u ⟨hu.1.le, hu.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2))).hasDerivWithinAt)
      ((hKg.continuous.comp_continuousOn
        ((hαc.mono (Icc_subset_Icc le_rfl ht.2)).add hec.continuousOn)).intervalIntegrable_of_Icc
        ht.1)
    have hint : ∫ s in (0 : ℝ)..t, G s (α s) =
        ∫ s in (0 : ℝ)..t, f (α (projIcc 0 T hT s) + σ • (w s - w 0)) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le ht.1] at hu
      have huT : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
      simp only [projIcc_of_mem hT huT]
      rw [hGf u huT, heI u huT]
    rw [← hint, hFTC, hα0]
    abel

/-- **Existence for the variational equation.** For a `C¹` field `f`, a continuous curve `x₀` and a
continuous noise path `w`, the linear equation `ζ(t) = ∫₀ᵗ f'(x₀(s)) ζ(s) ds + (w(t) − w(0))` has a
continuous solution on `[0, T]` (unique by the linear case of `eqOn_of_additiveNoise`). -/
@[tmio T, powerlib_foundation] theorem exists_variational {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 1 f)
    {x₀ : ℝ → ℝⁿ} (hx₀ : Continuous x₀) {w : ℝ → ℝⁿ} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    ∃ ζ : ℝ → ℝⁿ, Continuous ζ ∧
      ∀ t ∈ Icc 0 T, ζ t = (∫ s in (0 : ℝ)..t, fderiv ℝ f (x₀ s) (ζ s)) + (w t - w 0) := by
  have hp : Continuous fun t => (projIcc 0 T hT t : ℝ) := continuous_subtype_val.comp continuous_projIcc
  set A : ℝ → ℝⁿ →L[ℝ] ℝⁿ := fun t => fderiv ℝ f (x₀ (projIcc 0 T hT t))
  have hA : Continuous A := (hf.continuous_fderiv one_ne_zero).comp (hx₀.comp hp)
  set v : ℝ → ℝⁿ := fun t => w (projIcc 0 T hT t) - w 0
  have hv : Continuous v := (hw.comp hp).sub continuous_const
  obtain ⟨K', hK'⟩ : ∃ K', ∀ t, ‖A t‖ ≤ K' := by
    obtain ⟨K', hK'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc 0 T))
    refine ⟨K', fun t => ?_⟩
    have : A t = A (projIcc 0 T hT t) := by simp [A]
    rw [this]; exact hK' _ (projIcc 0 T hT t).2
  set G : ℝ → ℝⁿ → ℝⁿ := fun t y => A t (y + v t)
  have hGc : Continuous (Function.uncurry G) :=
    (hA.comp continuous_fst).clm_apply (continuous_snd.add (hv.comp continuous_fst))
  have hGl : ∀ t, LipschitzWith (Real.toNNReal K') (G t) := fun t =>
    LipschitzWith.of_dist_le_mul fun y y' => by
      simp only [G, dist_eq_norm, ← map_sub, add_sub_add_right_eq_sub]
      exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        ((hK' t).trans (Real.le_coe_toNNReal K')) (norm_nonneg _))
  obtain ⟨η, hη0, hη⟩ := exists_isIntegralCurveOn_Icc hGc hGl 0 T 0
  have hηc : ContinuousOn η (Icc 0 T) := hη.continuousOn
  refine ⟨fun t => η (projIcc 0 T hT t) + (w t - w 0), (hηc.comp_continuous hp
    fun t => (projIcc 0 T hT t).2).add (hw.sub continuous_const), fun t ht => ?_⟩
  simp only [projIcc_of_mem hT ht]
  congr 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (hηc.mono (Icc_subset_Icc le_rfl ht.2))
    (fun u hu => ((hη u ⟨hu.1.le, hu.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2))).hasDerivWithinAt)
    ((hGc.comp_continuousOn ((continuousOn_id.prodMk
      (hηc.mono (Icc_subset_Icc le_rfl ht.2))))).intervalIntegrable_of_Icc ht.1)
  have hint : ∫ s in (0 : ℝ)..t, G s (η s) =
      ∫ s in (0 : ℝ)..t, fderiv ℝ f (x₀ s) (η (projIcc 0 T hT s) + (w s - w 0)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht.1] at hu
    have huT : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
    simp [G, A, v, projIcc_of_mem hT huT]
  rw [← hint, hFTC, hη0, sub_zero]

/-! ## Small-noise expansion -/

/-- `gronwallBound 0 K ε x ≤ (ε/K) e^{KT}` for `K > 0`, `ε ≥ 0`, `x ≤ T`. -/
@[tmio T, powerlib_foundation] private theorem gronwallBound_zero_le {K ε x T : ℝ} (hK : 0 < K)
    (hε : 0 ≤ ε) (hxT : x ≤ T) : gronwallBound 0 K ε x ≤ ε / K * Real.exp (K * T) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  simp only [zero_mul, zero_add]
  have h1 : Real.exp (K * x) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxT hK.le)
  have h2 : 0 ≤ ε / K := div_nonneg hε hK.le
  nlinarith [Real.exp_pos (K * x)]

/-- Second-order Taylor bound on a convex set from a bound on the second derivative:
`‖f y − f x − f'(x)(y − x)‖ ≤ L₂ ‖y − x‖²`. -/
@[tmio T, powerlib_foundation] private theorem norm_taylor_le {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 2 f)
    {s : Set ℝⁿ} (hs : Convex ℝ s) {L₂ : ℝ} (hL₂ : ∀ u ∈ s, ‖fderiv ℝ (fderiv ℝ f) u‖ ≤ L₂)
    {x y : ℝⁿ} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ L₂ * ‖y - x‖ ^ 2 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hL₂0 : 0 ≤ L₂ := (by positivity : (0 : ℝ) ≤ ‖fderiv ℝ (fderiv ℝ f) x‖).trans (hL₂ x hx)
  have hLip : ∀ u ∈ s, ‖fderiv ℝ f u - fderiv ℝ f x‖ ≤ L₂ * ‖u - x‖ := fun u hu =>
    hs.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hDf.differentiable one_ne_zero) z) hL₂
      hx hu
  have hφ : ∀ u ∈ segment ℝ x y, HasFDerivWithinAt (fun u => f u - fderiv ℝ f x u)
      (fderiv ℝ f u - fderiv ℝ f x) (segment ℝ x y) u := fun u _ =>
    (((hf1.differentiable one_ne_zero) u).hasFDerivAt.sub
      (fderiv ℝ f x).hasFDerivAt).hasFDerivWithinAt
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le hφ
    (C := L₂ * ‖y - x‖) (fun u hu => (hLip u (hs.segment_subset hx hy hu)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hu) hL₂0))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have e : f y - fderiv ℝ f x y - (f x - fderiv ℝ f x x) = f y - f x - fderiv ℝ f x (y - x) := by
    rw [map_sub]; abel
  rw [e] at h
  calc _ ≤ L₂ * ‖y - x‖ * ‖y - x‖ := h
    _ = L₂ * ‖y - x‖ ^ 2 := by ring

/-- **Small-noise expansion of an additive-noise ODE** (the rigorous content of a first-order
noise expansion). Let `f` be `C²`, `x₀` the noise-free solution of `x₀(t) = a + ∫₀ᵗ f(x₀)` on
`[0, T]`, and `ζ` a continuous solution of the variational equation
`ζ(t) = ∫₀ᵗ f'(x₀(s)) ζ(s) ds + (w(t) − w(0))` along it. Then there are `σ₀ > 0` and `C` such that
for `|σ| ≤ σ₀` every continuous solution `x_σ` of `x_σ(t) = a + ∫₀ᵗ f(x_σ) + σ(w(t) − w(0))`
satisfies `‖x_σ(t) − x₀(t) − σ ζ(t)‖ ≤ C σ²` uniformly on `[0, T]`: `x_σ = x₀ + σζ + O(σ²)`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_sub_smul_le {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 2 f)
    {a : ℝⁿ} {w : ℝ → ℝⁿ} (hw : Continuous w) {T : ℝ} {x₀ : ℝ → ℝⁿ} (hx₀ : Continuous x₀)
    (h₀ : ∀ t ∈ Icc 0 T, x₀ t = a + ∫ s in (0 : ℝ)..t, f (x₀ s))
    {ζ : ℝ → ℝⁿ} (hζ : Continuous ζ)
    (hζeq : ∀ t ∈ Icc 0 T, ζ t = (∫ s in (0 : ℝ)..t, fderiv ℝ f (x₀ s) (ζ s)) + (w t - w 0)) :
    ∃ σ₀ > 0, ∃ C, ∀ σ : ℝ, |σ| ≤ σ₀ → ∀ x : ℝ → ℝⁿ, Continuous x →
      (∀ t ∈ Icc 0 T, x t = a + (∫ s in (0 : ℝ)..t, f (x s)) + σ • (w t - w 0)) →
      ∀ t ∈ Icc 0 T, ‖x t - x₀ t - σ • ζ t‖ ≤ C * σ ^ 2 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨R₀, hR₀⟩ := exists_norm_le_Icc (T := T) hx₀.continuousOn
  set Bs : Set ℝⁿ := closedBall 0 (R₀ + 1)
  have hBc : IsCompact Bs := isCompact_closedBall _ _
  have hBconv : Convex ℝ Bs := convex_closedBall _ _
  obtain ⟨L', hL'⟩ := hBc.exists_bound_of_continuousOn (hf1.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨L₂', hL₂'⟩ :=
    hBc.exists_bound_of_continuousOn (hDf.continuous_fderiv one_ne_zero).continuousOn
  set L := max L' 0 + 1
  set L₂ := max L₂' 0
  have hL : 0 < L := by positivity
  have hL₂ : 0 ≤ L₂ := le_max_right _ _
  have hDfB : ∀ u ∈ Bs, ‖fderiv ℝ f u‖ ≤ L := fun u hu =>
    (hL' u hu).trans ((le_max_left _ _).trans (by linarith))
  have hD2B : ∀ u ∈ Bs, ‖fderiv ℝ (fderiv ℝ f) u‖ ≤ L₂ := fun u hu =>
    (hL₂' u hu).trans (le_max_left _ _)
  have hLip : ∀ u ∈ Bs, ∀ v ∈ Bs, ‖f v - f u‖ ≤ L * ‖v - u‖ := fun u hu v hv =>
    hBconv.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hf1.differentiable one_ne_zero) z)
      hDfB hu hv
  obtain ⟨m', hm'⟩ := exists_norm_le_Icc (T := T) (x := fun t => w t - w 0)
    (hw.sub continuous_const).continuousOn
  set m := max m' 0
  have hm : ∀ t ∈ Icc 0 T, ‖w t - w 0‖ ≤ m := fun t ht => (hm' t ht).trans (le_max_left _ _)
  have hm0 : 0 ≤ m := le_max_right _ _
  set E := Real.exp (L * T)
  have hE : 0 < E := Real.exp_pos _
  set c₂ := m * E + m
  have hc₂ : 0 ≤ c₂ := by positivity
  set σ₀ := 1 / (2 * (c₂ + 1))
  refine ⟨σ₀, by positivity, L₂ * c₂ ^ 2 * E / L, fun σ hσ x hx hxeq => ?_⟩
  have hσc : |σ| * c₂ < 1 := by
    have h1 : |σ| * c₂ ≤ σ₀ * c₂ := mul_le_mul_of_nonneg_right hσ hc₂
    have h2 : σ₀ * c₂ < 1 := by
      simp only [σ₀]
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    linarith
  have hx₀B : ∀ t ∈ Icc 0 T, x₀ t ∈ Bs := fun t ht =>
    mem_closedBall_zero_iff.2 ((hR₀ t ht).trans (by linarith))
  set D : ℝ → ℝⁿ := fun t => ∫ s in (0 : ℝ)..t, (f (x s) - f (x₀ s))
  have hD : ∀ t, HasDerivAt D (f (x t) - f (x₀ t)) t := fun t =>
    ((hf1.continuous.comp hx).sub (hf1.continuous.comp hx₀)).integral_hasStrictDerivAt 0 t
      |>.hasDerivAt
  have hxD : ∀ t ∈ Icc 0 T, x t - x₀ t = D t + σ • (w t - w 0) := by
    intro t ht
    rw [hxeq t ht, h₀ t ht]
    simp only [D]
    have i1 : IntervalIntegrable (fun s => f (x s)) MeasureTheory.volume 0 t :=
      (hf1.continuous.comp hx).intervalIntegrable 0 t
    have i2 : IntervalIntegrable (fun s => f (x₀ s)) MeasureTheory.volume 0 t :=
      (hf1.continuous.comp hx₀).intervalIntegrable 0 t
    rw [intervalIntegral.integral_sub i1 i2]
    abel
  -- the deviation `D` while `x` stays in the ball
  have hDbound : ∀ s ∈ Icc 0 T, (∀ u ∈ Icc 0 s, x u ∈ Bs) →
      ∀ u ∈ Icc 0 s, ‖D u‖ ≤ |σ| * m * E := by
    intro s hs hin u hu
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := D)
      (f' := fun t => f (x t) - f (x₀ t)) (δ := 0) (K := L) (ε := L * (|σ| * m)) (a := 0) (b := s)
      (continuous_iff_continuousAt.2 fun t => (hD t).continuousAt).continuousOn
      (fun t _ => (hD t).hasDerivWithinAt) (by simp [D])
      (fun t ht => by
        have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.le.trans hs.2⟩
        calc ‖f (x t) - f (x₀ t)‖ ≤ L * ‖x t - x₀ t‖ :=
              hLip _ (hx₀B t htT) _ (hin t (Ico_subset_Icc_self ht))
          _ = L * ‖D t + σ • (w t - w 0)‖ := by rw [hxD t htT]
          _ ≤ L * (‖D t‖ + |σ| * m) := by
              refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hL.le
              rw [norm_smul, Real.norm_eq_abs]
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hm t htT) (abs_nonneg _))
          _ = L * ‖D t‖ + L * (|σ| * m) := by ring) u hu
    rw [sub_zero] at hgr
    refine hgr.trans ((gronwallBound_zero_le hL (by positivity) (hu.2.trans hs.2)).trans ?_)
    rw [mul_div_cancel_left₀ _ hL.ne']
  have hxB : ∀ t ∈ Icc 0 T, ‖x t‖ < R₀ + 1 := by
    rcases lt_or_ge T 0 with hT | hT
    · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.2 hT)
    refine Dynamics.forall_lt_of_first_exit (φ := x) continuous_norm hx.continuousOn ?_ ?_
    · have h0 : x 0 = a := by
        rw [hxeq 0 ⟨le_rfl, hT⟩]; simp
      have ha : ‖a‖ ≤ R₀ := by
        have := hR₀ 0 ⟨le_rfl, hT⟩
        rwa [h₀ 0 ⟨le_rfl, hT⟩, intervalIntegral.integral_same, add_zero] at this
      rw [h0]; linarith
    · intro s hs hle
      have hin : ∀ u ∈ Icc 0 s, x u ∈ Bs := fun u hu => mem_closedBall_zero_iff.2 (hle u hu)
      have h1 := hDbound s hs hin s (right_mem_Icc.2 hs.1)
      calc ‖x s‖ = ‖x₀ s + (D s + σ • (w s - w 0))‖ := by rw [← hxD s hs]; abel_nf
        _ ≤ ‖x₀ s‖ + (‖D s‖ + |σ| * m) := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans ?_))
            rw [norm_smul, Real.norm_eq_abs]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hm s hs) (abs_nonneg _))
        _ ≤ R₀ + (|σ| * m * E + |σ| * m) := add_le_add (hR₀ s hs) (add_le_add h1 le_rfl)
        _ = R₀ + |σ| * c₂ := by ring
        _ < R₀ + 1 := by linarith
  have hxBs : ∀ t ∈ Icc 0 T, x t ∈ Bs := fun t ht => mem_closedBall_zero_iff.2 (hxB t ht).le
  have hxx₀ : ∀ t ∈ Icc 0 T, ‖x t - x₀ t‖ ≤ |σ| * c₂ := by
    intro t ht
    have h1 := hDbound t ht (fun u hu => hxBs u ⟨hu.1, hu.2.trans ht.2⟩) t (right_mem_Icc.2 ht.1)
    rw [hxD t ht]
    calc ‖D t + σ • (w t - w 0)‖ ≤ ‖D t‖ + |σ| * m := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hm t ht) (abs_nonneg _)
      _ ≤ |σ| * m * E + |σ| * m := add_le_add h1 le_rfl
      _ = |σ| * c₂ := by ring
  -- the remainder `r = x − x₀ − σζ`
  have hcont_lin : Continuous fun s => fderiv ℝ f (x₀ s) (ζ s) :=
    ((hf1.continuous_fderiv one_ne_zero).comp hx₀).clm_apply hζ
  set η : ℝ → ℝⁿ := fun t => ∫ s in (0 : ℝ)..t, fderiv ℝ f (x₀ s) (ζ s)
  set r : ℝ → ℝⁿ := fun t => D t - σ • η t
  have hr : ∀ t, HasDerivAt r (f (x t) - f (x₀ t) - σ • fderiv ℝ f (x₀ t) (ζ t)) t := fun t =>
    (hD t).sub ((hcont_lin.integral_hasStrictDerivAt 0 t).hasDerivAt.const_smul σ)
  have hrx : ∀ t ∈ Icc 0 T, x t - x₀ t - σ • ζ t = r t := by
    intro t ht
    rw [hxD t ht, hζeq t ht]
    simp only [r, η, smul_add]
    abel
  intro t ht
  rcases lt_or_ge T 0 with hT | hT
  · exact absurd (ht.1.trans ht.2) (not_le.2 hT)
  rw [hrx t ht]
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := r)
    (f' := fun t => f (x t) - f (x₀ t) - σ • fderiv ℝ f (x₀ t) (ζ t)) (δ := 0) (K := L)
    (ε := L₂ * c₂ ^ 2 * σ ^ 2) (a := 0) (b := T)
    (continuous_iff_continuousAt.2 fun t => (hr t).continuousAt).continuousOn
    (fun t _ => (hr t).hasDerivWithinAt) (by simp [r, D, η])
    (fun u hu => by
      have huT : u ∈ Icc 0 T := Ico_subset_Icc_self hu
      have e : f (x u) - f (x₀ u) - σ • fderiv ℝ f (x₀ u) (ζ u) =
          fderiv ℝ f (x₀ u) (r u) + (f (x u) - f (x₀ u) - fderiv ℝ f (x₀ u) (x u - x₀ u)) := by
        rw [← hrx u huT, map_sub, map_sub, map_smul]
        abel
      rw [e]
      have h1 : ‖fderiv ℝ f (x₀ u) (r u)‖ ≤ L * ‖r u‖ :=
        ((fderiv ℝ f (x₀ u)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hDfB _ (hx₀B u huT)) (norm_nonneg _))
      have h2 : ‖f (x u) - f (x₀ u) - fderiv ℝ f (x₀ u) (x u - x₀ u)‖ ≤ L₂ * c₂ ^ 2 * σ ^ 2 := by
        refine (norm_taylor_le hf hBconv hD2B (hx₀B u huT) (hxBs u huT)).trans ?_
        have h3 := hxx₀ u huT
        have h4 : ‖x u - x₀ u‖ ^ 2 ≤ (|σ| * c₂) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
        calc L₂ * ‖x u - x₀ u‖ ^ 2 ≤ L₂ * (|σ| * c₂) ^ 2 := mul_le_mul_of_nonneg_left h4 hL₂
          _ = L₂ * c₂ ^ 2 * σ ^ 2 := by rw [mul_pow, sq_abs]; ring
      exact (norm_add_le _ _).trans (add_le_add h1 h2)) t ht
  rw [sub_zero] at hgr
  refine hgr.trans ((gronwallBound_zero_le hL (by positivity) ht.2).trans (le_of_eq ?_))
  ring

end powerlib.Stochastic.SmallNoise
