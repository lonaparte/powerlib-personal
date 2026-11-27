import theorem.ParametricResonance.StableHurwitz

/-! # Forced orbit of a stable field, the Jacobian along it, and the averaged 2:1 pair

`SmoothForcedOrbit` treats a field whose Jacobian has a critical pair `±jω/2`. When the Jacobian is
Hurwitz instead, the same construction gives the forced orbit for every drive frequency. This file
also turns the definition of the modulation `A₁` into a theorem about the actual orbit,
`J(t) = A₀ + ε Re{A₁ e^{jωt}} + O(ε²)`. Finally it gives the eigenvalues and the instability index
of the averaged 2:1 matrix of a mode pair.

Model boundary.
* `F : ℝ^X × ℝ → ℝ^X`, `ContDiffAt ℝ 3 F q₀`, `F q₀ = 0`, drive `w₀ + ε V̂ cos ωt`.
* The orbit theorem asks `∂ₓF(q₀)` Hurwitz (`LinearSystems.IsHurwitz`: every complex eigenvalue
  has negative real part), any `ω > 0`.
* The averaged pair is the matrix `[[−σ + jΔ, εg/2], [εg*/2, −σ − jΔ]]` of the source's first-order
  averaging; statements are inside that matrix. The Floquet statements for the actual system are
  `smooth_orbit_floquet_stable` and `smooth_orbit_floquet_unstable`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1–§2.2. Also the slides
"Hidden Instability of Grid-Following Converters Under Small Grid Angle Variations" (KTH,
2026-11-27): pp. 10, 15, 26–28 (forced response, definition of `A₁`, growth rates, instability
index, appendix on the first-order response).

Results.
* `exists_minv_of_hurwitz`: `I − e^{TA}` is invertible for Hurwitz `A`.
* `smooth_forced_orbit_hurwitz`: for all small `ε > 0`, existence of the periodic orbit in the
  ball of radius `cε`, uniqueness there, and `‖y − ε Re{z e^{jωt}}‖ ≤ Cε²`.
* `jac_orbit_expansion`: `‖J(y(t)) − A₀ − ε Re{A₁ e^{jωt}}‖ ≤ Kε²` along every
  `y = ε Re{z e^{jωt}} + O(ε²)`.
* `slow_det`, `slow_re_max`: the characteristic polynomial `(μ + σ)² + Δ² − ε²|g|²/4`. Its largest
  real part is `−σ + √(ε²|g|²/4 − Δ²)`, attained by a root.
* `slow_growth_iff`, `slow_crit_tuned`: `Re μ₊ > 0 ⟺ ε𝒜 > 1` with `𝒜 = |g|/(2√(σ² + Δ²))`;
  at exact tuning `ε_crit = 2σ/|g|`.

Corrections.
None.

Family and connection conclusions.
None: static evidence on periodically forced ODEs and on the averaged 2:1 matrix.
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix Set Filter Topology Metric
open scoped Matrix.Norms.Operator
open BlockAveraging (expS modX)

/-- For a Hurwitz matrix `A` and `T > 0`, `I − e^{TA}` is invertible: the monodromy of the linear
part has no multiplier `1`. -/
@[tmio T, powerlib_foundation] theorem exists_minv_of_hurwitz {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : LinearSystems.IsHurwitz A) {T : ℝ} (hT : 0 < T) :
    ∃ Minv : Matrix (Fin m) (Fin m) ℝ, Minv * (1 - expS A T) = 1 ∧ (1 - expS A T) * Minv = 1 := by
  have hsr := spectralRadius_expS_of_hurwitz hA hT
  have h1 : (1 : ℂ) ∉ spectrum ℂ ((expS A T).map (algebraMap ℝ ℂ)) := by
    intro hmem
    have hle : ((‖(1 : ℂ)‖₊ : NNReal) : ENNReal) ≤
        spectralRadius ℂ ((expS A T).map (algebraMap ℝ ℂ)) := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ ((expS A T).map (algebraMap ℝ ℂ))) =>
        ((‖k‖₊ : NNReal) : ENNReal)) 1 hmem
    rw [nnnorm_one, ENNReal.coe_one] at hle
    exact absurd hsr (not_lt.2 hle)
  rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, one_smul,
    Matrix.isUnit_iff_isUnit_det] at h1
  have hmap : (1 : Matrix (Fin m) (Fin m) ℂ) - (expS A T).map (algebraMap ℝ ℂ) =
      (1 - expS A T).map (algebraMap ℝ ℂ) := by
    ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
  rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero,
    map_ne_zero] at h1
  have hu : IsUnit (1 - expS A T).det := isUnit_iff_ne_zero.2 h1
  exact ⟨(1 - expS A T)⁻¹, Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu⟩

/-- The forced orbit of a `C³` field with a Hurwitz Jacobian, for any drive frequency: for all
small `ε > 0` the drive `w₀ + ε V̂ cos ωt` has a `2π/ω`-periodic solution in the ball of radius
`cε`, unique there, and every such solution is `ε Re{z e^{jωt}} + O(ε²)`, `z` the first-order
forced response. -/
@[tmio T, powerlib_foundation] theorem smooth_forced_orbit_hurwitz {m : ℕ}
    {F : (Fin m → ℝ) × ℝ → Fin m → ℝ} {q0 : (Fin m → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0)
    (hF0 : F q0 = 0) (hA : LinearSystems.IsHurwitz (matX F q0)) {Vh ω : ℝ} (hω : 0 < ω)
    {z : Fin m → ℂ} (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) :
    ∃ c C ε1, 0 ≤ c ∧ 0 ≤ C ∧ 0 < ε1 ∧ ∀ ε, 0 < ε → ε ≤ ε1 →
      (∃ y : ℝ → Fin m → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t)))) t) ∧
      (∀ y1 y2 : ℝ → Fin m → ℝ, (∀ t, y1 (t + 2 * Real.pi / ω) = y1 t) →
        (∀ t, ‖y1 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y1 (F (q0.1 + y1 t, q0.2 + ε * (Vh * Real.cos (ω * t)))) t) →
        (∀ t, y2 (t + 2 * Real.pi / ω) = y2 t) → (∀ t, ‖y2 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y2 (F (q0.1 + y2 t, q0.2 + ε * (Vh * Real.cos (ω * t)))) t) →
        y1 = y2) ∧
      ∀ y : ℝ → Fin m → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t)))) t) →
        ∀ t, ‖y t - ε • harm z ω t‖ ≤ C * ε ^ 2 := by
  obtain ⟨K, ρ, ε0, -, -, hK, hρ, hε0, -, -, hNc, hN0, hNL, -, -, -⟩ :=
    smooth_estimates hF hF0 Vh ω 0
  obtain ⟨Minv, hL, hR⟩ := exists_minv_of_hurwitz hA (T := 2 * Real.pi / ω) (by positivity)
  obtain ⟨hb, hbp, hNp, -, hpp, hpd, -⟩ := smooth_link F q0 hω.ne' hz 0
  obtain ⟨c, C, ε1, hc, hC, hε1, -, -, H⟩ :=
    forced_orbit (by positivity) hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL
  have e : ∀ ε t y, matX F q0 *ᵥ y + (ε • smB F q0 Vh ω t + smN F q0 Vh ω 0 ε t y) =
      F (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) := by
    intro ε t y
    rw [smN_rhs]
    simp
  refine ⟨c, C, ε1, hc, hC, hε1, fun ε hε hε' => ?_⟩
  obtain ⟨⟨y, hy1, hy2, hy3⟩, huniq, hexp⟩ := H ε hε hε'
  refine ⟨⟨y, hy1, hy2, fun t => by rw [← e]; exact hy3 t⟩,
    fun y1 y2 h1 h2 h3 h4 h5 h6 => huniq y1 y2 h1 h2 (fun t => by rw [e]; exact h3 t) h4 h5
      (fun t => by rw [e]; exact h6 t),
    fun y hy1 hy2 hy3 t => hexp y hy1 hy2 (fun t => by rw [e]; exact hy3 t) (harm z ω) hpp hpd t⟩

/-- Along any state `y = ε Re{z e^{jωt}} + O(ε²)` (in particular along the forced orbit), the
Jacobian is `A₀ + ε Re{A₁ e^{jωt}} + O(ε²)`, `A₁ = smA1` the modulation of `smooth_link`. -/
@[tmio T, powerlib_foundation] theorem jac_orbit_expansion {X : Type*} [Fintype X] [DecidableEq X]
    {F : (X → ℝ) × ℝ → X → ℝ} {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0)
    {Vh ω : ℝ} (hω : ω ≠ 0) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) {c C : ℝ} (hc : 0 ≤ c) :
    ∃ K ε2, 0 ≤ K ∧ 0 < ε2 ∧ ∀ ε, 0 ≤ ε → ε ≤ ε2 → ∀ (t : ℝ) (y : X → ℝ), ‖y‖ ≤ c * ε →
      ‖y - ε • harm z ω t‖ ≤ C * ε ^ 2 →
      ‖matX F (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) - matX F q0 -
        ε • modX (smA1 F q0 Vh z) ω t‖ ≤ K * ε ^ 2 := by
  obtain ⟨-, ρ, ε0, KJ, KD, -, hρ, hε0, hKJ, hKD, -, -, -, hDx, -, hJ⟩ :=
    smooth_estimates hF hF0 Vh ω 0
  obtain ⟨-, -, -, -, -, -, hlink⟩ := smooth_link F q0 hω hz 0
  refine ⟨KJ * (c ^ 2 + 1) + KD * |C|, min ε0 (ρ / (c + 1)), by positivity,
    lt_min hε0 (by positivity), fun ε hε hε2 t y hy hye => ?_⟩
  have hε0' : ε ≤ ε0 := hε2.trans (min_le_left _ _)
  have hyρ : ‖y‖ ≤ ρ := by
    have h1 : ε ≤ ρ / (c + 1) := hε2.trans (min_le_right _ _)
    have h2 : c * ε ≤ ρ := by
      calc c * ε ≤ (c + 1) * ε := by nlinarith
        _ ≤ (c + 1) * (ρ / (c + 1)) := by gcongr
        _ = ρ := by field_simp
    linarith
  have hj := hJ ε hε hε0' t y hyρ
  have hl := hlink t
  have key : matX F (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) - matX F q0 -
      ε • modX (smA1 F q0 Vh z) ω t =
      (smJ F q0 Vh ω 0 ε t y - matX F q0 - smDx F q0 y - ε • smDu F q0 Vh ω 0 t) +
        smDx F q0 (y - ε • harm z ω t) := by
    rw [map_sub, map_smul]
    have e2 : modX (smA1 F q0 Vh z) ω t = smDx F q0 (harm z ω t) + smDu F q0 Vh ω 0 t := by
      rw [hl, zero_add]
    rw [e2, smJ, smul_zero, add_zero, smul_add]
    abel
  rw [key]
  calc _ ≤ ‖smJ F q0 Vh ω 0 ε t y - matX F q0 - smDx F q0 y - ε • smDu F q0 Vh ω 0 t‖ +
        ‖smDx F q0 (y - ε • harm z ω t)‖ := norm_add_le _ _
    _ ≤ KJ * (‖y‖ ^ 2 + ε ^ 2) + KD * ‖y - ε • harm z ω t‖ := add_le_add hj (hDx _)
    _ ≤ KJ * ((c * ε) ^ 2 + ε ^ 2) + KD * (|C| * ε ^ 2) := by
        gcongr
        · exact (le_abs_self C).trans le_rfl |> fun h => hye.trans (by nlinarith [sq_nonneg ε])
    _ = (KJ * (c ^ 2 + 1) + KD * |C|) * ε ^ 2 := by ring

/-! ### The averaged 2:1 pair -/

/-- The characteristic polynomial of the averaged 2:1 matrix
`M = [[−σ + jΔ, εg/2], [εg*/2, −σ − jΔ]]` of the pair `(c, c*)`. -/
@[tmio T, powerlib_foundation] theorem slow_det (σ Δ ε : ℝ) (g μ : ℂ) :
    (!![-(σ : ℂ) + Δ * I, ε * g / 2; ε * (starRingEnd ℂ) g / 2, -(σ : ℂ) - Δ * I] -
      μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      (μ + σ) ^ 2 + Δ ^ 2 - (ε : ℂ) ^ 2 * (‖g‖ : ℂ) ^ 2 / 4 := by
  rw [Matrix.det_fin_two]
  simp
  have h : g * (starRingEnd ℂ) g = (‖g‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  linear_combination (-(ε : ℂ) ^ 2 / 4) * h - (Δ : ℂ) ^ 2 * Complex.I_sq

/-- The roots of the averaged pair: the largest real part is `−σ + √(ε²|g|²/4 − Δ²)` (the
square root of a negative number read as `0`), attained by `μ₊`. -/
@[tmio T, powerlib_foundation] theorem slow_re_max (σ Δ ε : ℝ) (g : ℂ) :
    (∀ μ : ℂ, (μ + σ) ^ 2 + Δ ^ 2 - (ε : ℂ) ^ 2 * (‖g‖ : ℂ) ^ 2 / 4 = 0 →
      μ.re ≤ -σ + Real.sqrt (ε ^ 2 * ‖g‖ ^ 2 / 4 - Δ ^ 2)) ∧
    ∃ μ : ℂ, (μ + σ) ^ 2 + Δ ^ 2 - (ε : ℂ) ^ 2 * (‖g‖ : ℂ) ^ 2 / 4 = 0 ∧
      μ.re = -σ + Real.sqrt (ε ^ 2 * ‖g‖ ^ 2 / 4 - Δ ^ 2) := by
  set R := ε ^ 2 * ‖g‖ ^ 2 / 4 - Δ ^ 2 with hR
  have hRc : (R : ℂ) = (ε : ℂ) ^ 2 * (‖g‖ : ℂ) ^ 2 / 4 - (Δ : ℂ) ^ 2 := by
    rw [hR]; push_cast; ring
  constructor
  · intro μ hμ
    have h : (μ + σ) ^ 2 = (R : ℂ) := by linear_combination hμ - hRc
    set w := μ + σ
    have hre : w.re ^ 2 - w.im ^ 2 = R := by
      have := congrArg Complex.re h; simp [pow_two] at this; linarith
    have him : w.re * w.im = 0 := by
      have := congrArg Complex.im h; simp [pow_two] at this; linarith
    have hw : μ.re = -σ + w.re := by simp [w]
    rw [hw]
    rcases mul_eq_zero.1 him with h0 | h0
    · rw [h0]; linarith [Real.sqrt_nonneg R]
    · rw [h0] at hre
      have : w.re ^ 2 = R := by linarith
      have hs : Real.sqrt R = |w.re| := by rw [← this, Real.sqrt_sq_eq_abs]
      linarith [le_abs_self w.re]
  · by_cases h0 : 0 ≤ R
    · refine ⟨-σ + Real.sqrt R, ?_, by simp⟩
      have hsq : (Real.sqrt R : ℂ) ^ 2 = R := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt h0]
      linear_combination hsq + hRc
    · refine ⟨-σ + Real.sqrt (-R) * I, ?_, ?_⟩
      · have hsq : (Real.sqrt (-R) : ℂ) ^ 2 = -R := by
          rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
        linear_combination (Real.sqrt (-R) : ℂ) ^ 2 * Complex.I_sq - hsq + hRc
      · simp [Real.sqrt_eq_zero'.2 (le_of_lt (not_le.1 h0))]

/-- The instability index: `Re μ₊ > 0 ⟺ ε 𝒜 > 1`, `𝒜 = |g|/(2√(σ² + Δ²))`, for `σ > 0`,
`ε ≥ 0`; the threshold is `ε_crit = 1/𝒜`, `2σ/|g|` at exact tuning. -/
@[tmio T, powerlib_foundation] theorem slow_growth_iff {σ Δ ε : ℝ} (g : ℂ) (hσ : 0 < σ)
    (hε : 0 ≤ ε) :
    0 < -σ + Real.sqrt (ε ^ 2 * ‖g‖ ^ 2 / 4 - Δ ^ 2) ↔
      1 < ε * (‖g‖ / (2 * Real.sqrt (σ ^ 2 + Δ ^ 2))) := by
  have hs : 0 < Real.sqrt (σ ^ 2 + Δ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have e1 : (0 < -σ + Real.sqrt (ε ^ 2 * ‖g‖ ^ 2 / 4 - Δ ^ 2)) ↔
      σ < Real.sqrt (ε ^ 2 * ‖g‖ ^ 2 / 4 - Δ ^ 2) := by
    constructor <;> intro h <;> linarith
  rw [e1, Real.lt_sqrt hσ.le, mul_div_assoc', one_lt_div (by positivity)]
  constructor
  · intro h
    have h1 : (2 * Real.sqrt (σ ^ 2 + Δ ^ 2)) ^ 2 < (ε * ‖g‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
  · intro h
    have h1 := pow_lt_pow_left₀ h (by positivity) two_ne_zero
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)] at h1
    nlinarith

/-- At exact tuning the threshold is `ε_crit = 2σ/|g|`. -/
@[tmio T, powerlib_foundation] theorem slow_crit_tuned {σ : ℝ} (g : ℂ) (hσ : 0 < σ) :
    1 / (‖g‖ / (2 * Real.sqrt (σ ^ 2 + 0 ^ 2))) = 2 * σ / ‖g‖ := by
  rw [show σ ^ 2 + (0 : ℝ) ^ 2 = σ ^ 2 by ring, Real.sqrt_sq hσ.le]
  field_simp

end powerlib.ParametricResonance.ForcedOrbit
