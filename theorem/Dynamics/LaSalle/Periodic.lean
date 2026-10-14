import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import theorem.Dynamics.LaSalle.Basin
import theorem.Dynamics.Coordinates
import theorem.Dynamics.Calculus

/-! # LaSalle through a periodic coordinate, angle lifts and attraction through a reduction

Model boundary. Generic: autonomous continuous-time ODEs `ẋ = f x` on
`Dynamics.State n = EuclideanSpace ℝ (Fin n)`; no input, delay, switching or time-variation.
Solutions are `IsIntegralCurveOn` curves (one-sided derivatives at endpoints), `V̇ x` is
`fderiv ℝ V x (f x)`. No model family is defined or fixed: every theorem is a generic
implication about arbitrary fields, maps and functions, hence a foundation result (Rules §3).

Purpose. A field that is `2π`-periodic in an angle `θ` has unbounded sublevel sets of every
periodic energy, so the compact-set hypothesis of LaSalle's principle fails on `ℝⁿ`. The standard
remedy is to map the state through a `C¹` map `P` (for an angle, `θ ↦ (cos θ, sin θ)`) that
carries solutions of `f` to solutions of a field `g` on which the image of the dynamics lies in an
invariant level set `{h = c₀}` (the cylinder `c² + s² = 1`) of a first integral `h`, where the
energy sublevel sets are compact. The results below are the generic pieces of that argument.

Results. (The calculus of curves in `State n` it uses — `fderiv_apply_eq_of_hasDerivAt_line`,
`hasDerivWithinAt_euclidean_of_coord`, `tendsto_euclidean_of_coord`, `norm_le_sum_abs` — is in
`theorem/Dynamics/Coordinates.lean`; the scalar Grönwall and drift bounds —
`HasDerivWithinAt.eq_zero_of_eqOn_Icc`, `le_exp_mul_of_hasDerivWithinAt`, `abs_le_of_sq_le_exp`,
`abs_sub_le_of_abs_deriv_le_exp`, `exists_tendsto_of_abs_deriv_le_exp` — are in
`theorem/Dynamics/Calculus.lean`.)
* `isIntegralCurveOn_comp_of_fderiv`: if `DP x (f x) = g (P x)` for every `x`, then `P` maps
  integral curves of `f` to integral curves of `g` (semiconjugacy).
* `isPositivelyInvariant_levelSet`: the level sets of a first integral (`ḣ = 0` everywhere) are
  positively invariant; `IsPositivelyInvariant.sep_sublevel`: a sublevel set of `V` inside a
  positively invariant set `Z` on which `V̇ ≤ 0` is positively invariant.
* `lasalle_levelSet`: LaSalle's principle (the `C¹` version
  `lasalle_invariance_principle_of_contDiff`, no global Lipschitz hypothesis) on the compact set
  `{h = c₀, V ≤ c}`, where `V̇ ≤ 0` is required only on the level set `{h = c₀}`.
  `exists_isIntegralCurveOn_of_isCompact`: a forward solution on `[0, ∞)` from every point of a
  compact positively invariant set of a `C¹` field.
* `lasalle_condition_of_lieDeriv_mem`: the set version of `lasalle_condition_of_lieDeriv` (every
  positively invariant subset of `E ⊆ {h = 0}` lies in `M` when `ḣ = 0` on `E` forces `M`);
  `lasalle_condition_of_trajectories_mem`: the set version of
  `lasalle_condition_of_trajectories` (solution segments staying in `E` start in `M`).
* `tendsto_zero_of_tendsto_nhdsSet`: convergence to a set `M` gives convergence to `0` of every
  continuous function vanishing on `M`.
* `abs_sub_le_of_abs_lt_pi_div_two` (`|x| ≤ (π/2) |sin x|` for `|x| < π/2`) and
  `exists_int_tendsto_of_tendsto_sin`: a continuous angle whose sine tends to `0` converges to a
  single multiple `j π` (no drift between the zeros of `sin`).
* `exists_cos_sin`, `exists_angle_lift`: a point of the unit circle has an angle; a solution
  `(c, s)` of `c' = −s w`, `s' = c w` on `[0, ∞)` is `(cos θ, sin θ)` for `θ = θ₀ + ∫ w`
  (lifting a cylinder solution back to the angle).
* `infDist_le_of_reduction`, `infDist_le_of_reduction'`: if a reduction `red` maps the solutions
  of `F` that start in `L` to solutions of a globally exponentially stable field `f` (and keeps them
  in `L`), and the distance to a set `O` is comparable with `‖red X − x*‖` on `L`, then every
  solution of `F` starting in `L` approaches `O` exponentially (stationary-frame attraction of a
  steady-state orbit from global exponential stability in rotating coordinates).

Connection architecture. Generic implications only (no Family): `@[powerlib_foundation]`. The
predicates are LeanForControl's `IsPositivelyInvariant`, `IsTrajectoryOn`, `LieDerivZeroSet` and
the Flow sentence `Flow.GloballyExponentiallyStable`, used in hypotheses; conclusions are
integral-curve, convergence and distance statements about the arbitrary data. Set attraction and
regions of attraction are outside the sentence language of the library; model families that use
these tools keep their trajectory-level conclusions as private implementation evidence.

Searched and not found (Rules §15): Mathlib and LeanForControl have no LaSalle principle on an
invariant manifold or modulo a period, no ω-limit result for non-compact sublevel sets, no angle
lift for ODE solutions on the circle, and no set-attraction transfer through a reduction.
Reused: LeanForControl `antitoneOn_V_comp_traj`, `IsPositivelyInvariant`, `LieDerivZeroSet`;
this library's `lasalle_invariance_principle_of_contDiff`, `exists_globalization`
(`theorem/Dynamics/LaSalle/Basin.lean`), `Flow.forwardComplete_of_lipschitzWith`; Mathlib
`Real.mul_le_sin`, `Real.sin_sub_int_mul_pi`, `intermediate_value_Icc`, `Complex.cos_arg`,
`Continuous.integral_hasStrictDerivAt`, `constant_of_has_deriv_right_zero`,
`Continuous.tendsto_nhdsSet_nhds`.

Source: Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.4 (LaSalle) applied on the cylinder
`S¹ × ℝⁿ⁻¹`, as in the energy-shaping argument of Arghir–Dörfler (IEEE TPEL 35(4), 2020,
appendix); interface for `theorem.DCLink.MatchingLaSalle` and `theorem.DCLink.MatchingClosedLoop`.
-/

noncomputable section
namespace powerlib.Dynamics.LaSalle
open Set Filter Topology Metric

/-! ## Calculus of curves in `State n` -/

/-- **Semiconjugacy.** If `DP x (f x) = g (P x)` for every `x`, then `P` maps integral curves of
`f` to integral curves of `g`. -/
@[powerlib_foundation] theorem isIntegralCurveOn_comp_of_fderiv {n m : ℕ} {f : State n → State n}
    {g : State m → State m} {P : State n → State m} (hP : Differentiable ℝ P)
    (hconj : ∀ x, fderiv ℝ P x (f x) = g (P x)) {φ : ℝ → State n} {s : Set ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) s) :
    IsIntegralCurveOn (fun t => P (φ t)) (fun _ y => g y) s := by
  intro t ht
  have h := (hP (φ t)).hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)
  rw [Function.comp_def, hconj] at h
  exact h

/-! ## Invariant level sets and LaSalle on them -/

/-- The level sets of a first integral are positively invariant. -/
@[powerlib_foundation] theorem isPositivelyInvariant_levelSet {m : ℕ} {g : State m → State m}
    {h : State m → ℝ} (c : ℝ) (hh : Differentiable ℝ h) (hlie : ∀ y, fderiv ℝ h y (g y) = 0) :
    IsPositivelyInvariant {y | h y = c} g := by
  intro t₀ t₁ ψ hψ hψ0 t ht
  have ht₀ : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  have h1 : AntitoneOn (h ∘ ψ) (Icc t₀ t₁) :=
    antitoneOn_V_comp_traj hh hh.continuous (convex_Icc t₀ t₁) hψ (fun s _ => (hlie _).le)
  have hn : Differentiable ℝ (fun y => -h y) := hh.neg
  have h2 : AntitoneOn ((fun y => -h y) ∘ ψ) (Icc t₀ t₁) :=
    antitoneOn_V_comp_traj hn hn.continuous (convex_Icc t₀ t₁) hψ (fun s _ => by
      rw [fderiv_fun_neg]
      simp [hlie])
  have a := h1 ht₀ ht ht.1
  have b := h2 ht₀ ht ht.1
  simp only [Function.comp, Set.mem_ofPred_eq] at a b hψ0 ⊢
  linarith

/-- A sublevel set of `V` inside a positively invariant set on which `V̇ ≤ 0` is positively
invariant. -/
@[powerlib_foundation] theorem IsPositivelyInvariant.sep_sublevel {m : ℕ} {g : State m → State m}
    {V : State m → ℝ} {Z : Set (State m)} (c : ℝ) (hZ : IsPositivelyInvariant Z g)
    (hV : Differentiable ℝ V) (hlie : ∀ y ∈ Z, fderiv ℝ V y (g y) ≤ 0) :
    IsPositivelyInvariant {y | y ∈ Z ∧ V y ≤ c} g := by
  rintro t₀ t₁ ψ hψ ⟨hψZ, hψV⟩ t ht
  have hstay := hZ t₀ t₁ ψ hψ hψZ
  have hanti : AntitoneOn (V ∘ ψ) (Icc t₀ t₁) :=
    antitoneOn_V_comp_traj hV hV.continuous (convex_Icc t₀ t₁) hψ
      (fun s hs => hlie _ (hstay s (interior_subset hs)))
  exact ⟨hstay t ht, (hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1).trans hψV⟩

/-- The set `{h = c₀, V ≤ c}` is positively invariant when `h` is a first integral and `V̇ ≤ 0` on
the level set `{h = c₀}`. -/
@[powerlib_foundation] theorem isPositivelyInvariant_levelSet_sublevel {m : ℕ}
    {g : State m → State m} {h V : State m → ℝ} {c₀ c : ℝ} (hh : Differentiable ℝ h)
    (hV : Differentiable ℝ V) (hh_lie : ∀ y, fderiv ℝ h y (g y) = 0)
    (hV_lie : ∀ y, h y = c₀ → fderiv ℝ V y (g y) ≤ 0) :
    IsPositivelyInvariant {y | h y = c₀ ∧ V y ≤ c} g :=
  IsPositivelyInvariant.sep_sublevel c (isPositivelyInvariant_levelSet c₀ hh hh_lie) hV hV_lie

/-- **LaSalle on an invariant level set.** `g` is `C¹`, `h` a first integral, `V̇ ≤ 0` on the
level set `{h = c₀}` and `Ω = {h = c₀, V ≤ c}` compact. Every forward solution starting in `Ω`
converges to every set `M` that contains the positively invariant subsets of
`{y ∈ Ω | V̇ y = 0}`. No global Lipschitz bound and no sign of `V̇` off the level set are needed. -/
@[powerlib_foundation] theorem lasalle_levelSet {m : ℕ} {g : State m → State m}
    {h V : State m → ℝ} {c₀ c : ℝ} {M : Set (State m)} (hg : ContDiff ℝ 1 g)
    (hh : Differentiable ℝ h) (hV : ContDiff ℝ 1 V) (hh_lie : ∀ y, fderiv ℝ h y (g y) = 0)
    (hV_lie : ∀ y, h y = c₀ → fderiv ℝ V y (g y) ≤ 0)
    (hΩ : IsCompact {y | h y = c₀ ∧ V y ≤ c})
    (hM : ∀ N ⊆ LieDerivZeroSet g V {y | h y = c₀ ∧ V y ≤ c}, IsPositivelyInvariant N g →
      N ⊆ M)
    {ψ : ℝ → State m} (hψ : IsIntegralCurveOn ψ (fun _ y => g y) (Ici 0))
    (hψ0 : h (ψ 0) = c₀) (hψc : V (ψ 0) ≤ c) :
    Tendsto ψ atTop (𝓝ˢ M) :=
  lasalle_invariance_principle_of_contDiff hΩ
    (isPositivelyInvariant_levelSet_sublevel hh (hV.differentiable (by norm_num)) hh_lie hV_lie)
    hg hV (fun y hy => hV_lie y hy.1) hψ ⟨hψ0, hψc⟩ hM

/-- A forward solution on `[0, ∞)` from every point of a compact positively invariant set of a
`C¹` field; it stays in the set. -/
@[powerlib_foundation] theorem exists_isIntegralCurveOn_of_isCompact {m : ℕ}
    {g : State m → State m} {Ω : Set (State m)} (hg : ContDiff ℝ 1 g) (hΩ : IsCompact Ω)
    (hinv : IsPositivelyInvariant Ω g) {y₀ : State m} (hy₀ : y₀ ∈ Ω) :
    ∃ ψ : ℝ → State m, ψ 0 = y₀ ∧ IsIntegralCurveOn ψ (fun _ y => g y) (Ici 0) ∧
      ∀ t, 0 ≤ t → ψ t ∈ Ω := by
  obtain ⟨g', -, ⟨K, hlip⟩, -, -, -, -, hgf⟩ := exists_globalization hg hΩ hinv
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hlip 0 y₀
  have hψ' := hgf hψ (hψ0 ▸ hy₀)
  exact ⟨ψ, hψ0, hψ', fun t ht =>
    hinv 0 t ψ (hψ'.mono Icc_subset_Ici_self) (hψ0 ▸ hy₀) t ⟨ht, le_rfl⟩⟩

/-- Set version of `lasalle_condition_of_lieDeriv`: if `E` lies in the zero set of a `C¹`
function `h`, and at a point of `E` the derivative of `h` along `f` vanishes only in `M`, then
every positively invariant subset of `E` lies in `M`. -/
@[powerlib_foundation] theorem lasalle_condition_of_lieDeriv_mem {n : ℕ} {f : State n → State n}
    {E M : Set (State n)} (hf_c1 : ContDiff ℝ 1 f) {h : State n → ℝ} (hh : ContDiff ℝ 1 h)
    (hE : ∀ x ∈ E, h x = 0) (hpt : ∀ x ∈ E, fderiv ℝ h x (f x) = 0 → x ∈ M) :
    ∀ N ⊆ E, IsPositivelyInvariant N f → N ⊆ M := by
  intro N hNE hN x hx
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ := (hf_c1.contDiffAt (x := x)).exists_isIntegralCurveOn_Icc
  have hstay : ∀ t ∈ Icc 0 T, ψ t ∈ N := hN 0 T ψ hψ (hψ0 ▸ hx)
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hchain : HasDerivWithinAt (h ∘ ψ) (fderiv ℝ h (ψ 0) (f (ψ 0))) (Icc 0 T) 0 :=
    (hh.differentiable (by norm_num) (ψ 0)).hasFDerivAt.comp_hasDerivWithinAt 0 (hψ 0 hmem0)
  have hzero : HasDerivWithinAt (h ∘ ψ) 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) _ (0 : ℝ)).congr (fun s hs => hE _ (hNE (hstay s hs)))
      (hE _ (hNE (hstay 0 hmem0)))
  have hx0 : ψ 0 ∈ E := hNE (hstay 0 hmem0)
  rw [← hψ0]
  exact hpt _ hx0 ((uniqueDiffOn_Icc hT 0 hmem0).eq_deriv _ hchain hzero)

/-- Set version of `lasalle_condition_of_trajectories`: if every solution segment of positive
length that stays in `E` starts in `M`, then every positively invariant subset of `E` lies in
`M`. -/
@[powerlib_foundation] theorem lasalle_condition_of_trajectories_mem {n : ℕ}
    {f : State n → State n} {E M : Set (State n)} (hf_c1 : ContDiff ℝ 1 f)
    (h : ∀ (T : ℝ) (φ : ℝ → State n), 0 < T → IsTrajectoryOn φ f 0 T →
      (∀ t ∈ Icc 0 T, φ t ∈ E) → φ 0 ∈ M) :
    ∀ N ⊆ E, IsPositivelyInvariant N f → N ⊆ M := by
  intro N hNE hN x hx
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ := (hf_c1.contDiffAt (x := x)).exists_isIntegralCurveOn_Icc
  have hstay : ∀ t ∈ Icc 0 T, ψ t ∈ N := hN 0 T ψ hψ (hψ0 ▸ hx)
  rw [← hψ0]
  exact h T ψ hT hψ fun t ht => hNE (hstay t ht)

/-- Convergence to a set gives convergence to `0` of every continuous function vanishing on it. -/
@[powerlib_foundation] theorem tendsto_zero_of_tendsto_nhdsSet {n : ℕ} {α : Type*}
    {l : Filter α} {ψ : α → State n} {M : Set (State n)} (hψ : Tendsto ψ l (𝓝ˢ M))
    {h : State n → ℝ} (hh : Continuous h) (hM : ∀ y ∈ M, h y = 0) :
    Tendsto (fun t => h (ψ t)) l (𝓝 0) :=
  (hh.tendsto_nhdsSet_nhds fun y hy => hM y hy).comp hψ

/-! ## Angles -/

private theorem abs_sin_sub_int_mul_pi (x : ℝ) (j : ℤ) :
    |Real.sin (x - j * Real.pi)| = |Real.sin x| := by
  rw [Real.sin_sub_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]

/-- Jordan's inequality in absolute value: `|x| ≤ (π/2) |sin x|` for `|x| ≤ π/2`. -/
@[powerlib_foundation] theorem abs_le_of_abs_le_pi_div_two {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |x| ≤ Real.pi / 2 * |Real.sin x| := by
  have hπ := Real.pi_pos
  rcases le_total 0 x with h0 | h0
  · have h1 := Real.mul_le_sin h0 (by rwa [abs_of_nonneg h0] at hx)
    rw [abs_of_nonneg h0, abs_of_nonneg (by have := mul_nonneg (by positivity : (0:ℝ) ≤ 2 / Real.pi) h0; linarith)]
    have : Real.pi / 2 * (2 / Real.pi * x) = x := by field_simp
    nlinarith
  · have h1 := Real.mul_le_sin (neg_nonneg.mpr h0) (by rw [abs_of_nonpos h0] at hx; exact hx)
    rw [Real.sin_neg] at h1
    rw [abs_of_nonpos h0, abs_of_nonpos (by have := mul_nonneg (by positivity : (0:ℝ) ≤ 2 / Real.pi) (neg_nonneg.mpr h0); linarith)]
    have : Real.pi / 2 * (2 / Real.pi * -x) = -x := by field_simp
    nlinarith

/-- **No drift between the zeros of `sin`.** A continuous angle whose sine tends to `0` converges
to a single multiple `j π`. -/
@[powerlib_foundation] theorem exists_int_tendsto_of_tendsto_sin {θ : ℝ → ℝ} {a : ℝ}
    (hθ : ContinuousOn θ (Ici a)) (hsin : Tendsto (fun t => Real.sin (θ t)) atTop (𝓝 0)) :
    ∃ j : ℤ, Tendsto θ atTop (𝓝 (j * Real.pi)) := by
  have hπ := Real.pi_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hsin.eventually (Metric.ball_mem_nhds 0 one_pos))
  set T' := max T a with hT'
  have hlt : ∀ t, T' ≤ t → |Real.sin (θ t)| < 1 := fun t ht => by
    have := hT t ((le_max_left _ _).trans ht)
    simpa [Real.dist_eq] using this
  set j : ℤ := round (θ T' / Real.pi)
  have hj0 : |θ T' - j * Real.pi| ≤ Real.pi / 2 := by
    have h := abs_sub_round (θ T' / Real.pi)
    have e : θ T' - j * Real.pi = Real.pi * (θ T' / Real.pi - j) := by field_simp
    rw [e, abs_mul, abs_of_pos hπ]
    nlinarith
  -- the angle never reaches `j π ± π/2` after `T'`
  have hne : ∀ t, T' ≤ t → θ t ≠ j * Real.pi + Real.pi / 2 ∧ θ t ≠ j * Real.pi - Real.pi / 2 := by
    intro t ht
    have h := hlt t ht
    constructor <;> intro he <;> rw [← abs_sin_sub_int_mul_pi _ j, he] at h <;> simp at h
  have hcont : ∀ t, T' ≤ t → ContinuousOn θ (Icc T' t) := fun t _ =>
    hθ.mono fun s hs => (le_max_right _ _).trans hs.1
  have hwin : ∀ t, T' ≤ t → |θ t - j * Real.pi| < Real.pi / 2 := by
    intro t ht
    rw [abs_lt]
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    rcases hc with hc | hc
    · -- θ t ≤ j π − π/2 ≤ θ T'
      have hmem : j * Real.pi - Real.pi / 2 ∈ Icc (θ t) (θ T') := by
        constructor
        · linarith
        · linarith [(abs_le.mp hj0).1]
      obtain ⟨s, hs, hse⟩ := intermediate_value_Icc' ht (hcont t ht) hmem
      exact (hne s hs.1).2 hse
    · have hmem : j * Real.pi + Real.pi / 2 ∈ Icc (θ T') (θ t) := by
        constructor
        · linarith [(abs_le.mp hj0).2]
        · linarith
      obtain ⟨s, hs, hse⟩ := intermediate_value_Icc ht (hcont t ht) hmem
      exact (hne s hs.1).1 hse
  refine ⟨j, ?_⟩
  rw [← tendsto_sub_nhds_zero_iff]
  have hlim : Tendsto (fun t => Real.pi / 2 * |Real.sin (θ t)|) atTop (𝓝 0) := by
    simpa using (hsin.abs).const_mul (Real.pi / 2)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop T'] with t ht
  rw [Real.norm_eq_abs, ← abs_sin_sub_int_mul_pi (θ t) j]
  exact abs_le_of_abs_le_pi_div_two (hwin t ht).le

/-- A point of the unit circle has an angle. -/
@[powerlib_foundation] theorem exists_cos_sin {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  set z : ℂ := ⟨a, b⟩
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]
    rw [show a * a + b * b = 1 by nlinarith, Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz
    exact zero_ne_one hz
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hz, div_one]
  · rw [Complex.sin_arg, hz, div_one]

/-- **Angle lift.** If `(c, s)` solves `c' = −s w`, `s' = c w` on `[0, ∞)` with `w` continuous
there and starts at `(cos θ₀, sin θ₀)`, then `θ = θ₀ + ∫₀ᵗ w` has derivative `w` and
`(cos θ, sin θ) = (c, s)` on `[0, ∞)`. -/
@[powerlib_foundation] theorem exists_angle_lift {c s w : ℝ → ℝ} {θ₀ : ℝ}
    (hw : ContinuousOn w (Ici 0))
    (hc : ∀ t, 0 ≤ t → HasDerivWithinAt c (-(s t) * w t) (Ici 0) t)
    (hs : ∀ t, 0 ≤ t → HasDerivWithinAt s (c t * w t) (Ici 0) t)
    (h0c : c 0 = Real.cos θ₀) (h0s : s 0 = Real.sin θ₀) :
    ∃ θ : ℝ → ℝ, θ 0 = θ₀ ∧ (∀ t, 0 ≤ t → HasDerivWithinAt θ (w t) (Ici 0) t) ∧
      ∀ t, 0 ≤ t → Real.cos (θ t) = c t ∧ Real.sin (θ t) = s t := by
  set w' : ℝ → ℝ := fun t => w (max t 0) with hw'
  have hw'c : Continuous w' :=
    hw.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
  have hw'e : ∀ t, 0 ≤ t → w' t = w t := fun t ht => by simp [hw', max_eq_left ht]
  set θ : ℝ → ℝ := fun t => θ₀ + ∫ τ in (0 : ℝ)..t, w' τ with hθ
  have hθd : ∀ t, 0 ≤ t → HasDerivWithinAt θ (w t) (Ici 0) t := fun t ht => by
    rw [← hw'e t ht]
    exact ((hw'c.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add θ₀).hasDerivWithinAt
  refine ⟨θ, by simp [hθ], hθd, ?_⟩
  set F : ℝ → ℝ := fun t => (c t - Real.cos (θ t)) ^ 2 + (s t - Real.sin (θ t)) ^ 2 with hF
  have hFd : ∀ t, 0 ≤ t → HasDerivWithinAt F 0 (Ici 0) t := by
    intro t ht
    have h1 := ((hc t ht).sub (hθd t ht).cos).pow 2
    have h2 := ((hs t ht).sub (hθd t ht).sin).pow 2
    convert h1.add h2 using 1
    simp only [Pi.sub_apply, Nat.cast_ofNat]
    ring
  have hF0 : F 0 = 0 := by simp [hF, hθ, h0c, h0s]
  intro t ht
  have hFc : ContinuousOn F (Icc 0 t) := fun x hx => (hFd x hx.1).continuousWithinAt.mono
    Icc_subset_Ici_self
  have hFt : F t = 0 := by
    have := constant_of_has_deriv_right_zero hFc (fun x hx =>
      (hFd x hx.1).mono (Ici_subset_Ici.mpr hx.1)) t ⟨ht, le_rfl⟩
    rw [this, hF0]
  have e1 : (c t - Real.cos (θ t)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (c t - Real.cos (θ t)), sq_nonneg (s t - Real.sin (θ t))]
  have e2 : (s t - Real.sin (θ t)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (c t - Real.cos (θ t)), sq_nonneg (s t - Real.sin (θ t))]
  constructor
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1
    linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2
    linarith


/-! ## Attraction of a set through a reduction -/

/-- **Exponential attraction through a reduction.** `f` is globally exponentially stable at `x*`;
the reduction `red` maps every solution segment of `F` starting in `L` to a solution segment of
`f`, and the segment stays in `L`; on `L` the distance to `O` is at most `A ‖red X − x*‖`. Then
every solution segment of `F` starting in `L` approaches `O` exponentially, with the rate of `f`. -/
@[powerlib_foundation] theorem infDist_le_of_reduction {N n : ℕ} {F : State N → State N}
    {f : State n → State n} {red : State N → State n} {x : State n} {L O : Set (State N)}
    {A : ℝ} (hA : 0 ≤ A) (hf : Flow.GloballyExponentiallyStable f x)
    (hred : ∀ (t₀ t₁ : ℝ) (X : ℝ → State N), IsTrajectoryOn X F t₀ t₁ → X t₀ ∈ L →
      IsTrajectoryOn (fun t => red (X t)) f t₀ t₁ ∧ ∀ t ∈ Icc t₀ t₁, X t ∈ L)
    (hO : ∀ X ∈ L, infDist X O ≤ A * ‖red X - x‖) :
    ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ (t₀ t₁ : ℝ) (X : ℝ → State N), IsTrajectoryOn X F t₀ t₁ →
      X t₀ ∈ L → ∀ t ∈ Icc t₀ t₁,
        infDist (X t) O ≤ C * Real.exp (-a * (t - t₀)) * ‖red (X t₀) - x‖ := by
  obtain ⟨-, -, C, a, hC, ha, hb⟩ := hf
  refine ⟨A * C, a, mul_nonneg hA (by linarith), ha, fun t₀ t₁ X hX hX0 t ht => ?_⟩
  obtain ⟨hr, hL⟩ := hred t₀ t₁ X hX hX0
  have h1 := hO (X t) (hL t ht)
  have h2 := hb t₀ t₁ _ hr t ht
  calc infDist (X t) O ≤ A * ‖red (X t) - x‖ := h1
    _ ≤ A * (C * Real.exp (-a * (t - t₀)) * ‖red (X t₀) - x‖) :=
        mul_le_mul_of_nonneg_left h2 hA
    _ = A * C * Real.exp (-a * (t - t₀)) * ‖red (X t₀) - x‖ := by ring

/-- The same with the initial distance to `O` on the right, when on `L` also
`‖red X − x*‖ ≤ B · dist(X, O)`: the set `O` is exponentially stable relative to `L`. -/
@[powerlib_foundation] theorem infDist_le_of_reduction' {N n : ℕ} {F : State N → State N}
    {f : State n → State n} {red : State N → State n} {x : State n} {L O : Set (State N)}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : Flow.GloballyExponentiallyStable f x)
    (hred : ∀ (t₀ t₁ : ℝ) (X : ℝ → State N), IsTrajectoryOn X F t₀ t₁ → X t₀ ∈ L →
      IsTrajectoryOn (fun t => red (X t)) f t₀ t₁ ∧ ∀ t ∈ Icc t₀ t₁, X t ∈ L)
    (hO : ∀ X ∈ L, infDist X O ≤ A * ‖red X - x‖)
    (hO' : ∀ X ∈ L, ‖red X - x‖ ≤ B * infDist X O) :
    ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ (t₀ t₁ : ℝ) (X : ℝ → State N), IsTrajectoryOn X F t₀ t₁ →
      X t₀ ∈ L → ∀ t ∈ Icc t₀ t₁,
        infDist (X t) O ≤ C * Real.exp (-a * (t - t₀)) * infDist (X t₀) O := by
  obtain ⟨C, a, hC, ha, h⟩ := infDist_le_of_reduction hA hf hred hO
  refine ⟨C * B, a, mul_nonneg hC hB, ha, fun t₀ t₁ X hX hX0 t ht => ?_⟩
  have h1 := h t₀ t₁ X hX hX0 t ht
  have h2 := hO' (X t₀) hX0
  have hp : 0 ≤ C * Real.exp (-a * (t - t₀)) := mul_nonneg hC (Real.exp_pos _).le
  calc infDist (X t) O ≤ C * Real.exp (-a * (t - t₀)) * ‖red (X t₀) - x‖ := h1
    _ ≤ C * Real.exp (-a * (t - t₀)) * (B * infDist (X t₀) O) :=
        mul_le_mul_of_nonneg_left h2 hp
    _ = C * B * Real.exp (-a * (t - t₀)) * infDist (X t₀) O := by ring

end powerlib.Dynamics.LaSalle
