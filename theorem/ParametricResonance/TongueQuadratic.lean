import theorem.ParametricResonance.SlowFlow

/-! # The second-order slow flow and the tongue-centre quadratic

Foundation layer: exact real-algebra statements **inside the second-order slow flow**. They are
not Floquet stability boundaries of a converter: the coefficients `α₀`, `c_α`, `c_ω`, `|𝒢|²`
are treated as given real numbers, and the passage from a periodic orbit of a converter model to
this slow flow (projection, averaging, truncation at second order) is not formalized.

Model boundary. Second-order slow flow (source §6–§7): the first-order slow flow of
`SlowFlow.lean` with amplitude-dependent damping and detuning,
`Ȧ = −(a(y) + j(Δ + c_ω y)) A + g A*`, `a(y) = α₀ − c_α y`, `|g|² = |𝒢|² y / 4`,
`y = δ̂₁²` the squared modulation amplitude (`secondOrderMatrix`, and the linear field
`secondOrderSystem` on `ℝ²`). We write `g2 = |𝒢|² > 0`,
`S = c_α² + c_ω²`, `Q = g2/4 + 2α₀c_α`.

Results.
* §6–§7: `det` of the second-order slow flow is `a² + (Δ + c_ω y)² − g2 y/4`; at the tongue
  centre `Δ = 0` it equals `q(y) = S y² − Q y + α₀² = a(y)² − h(y)²` with
  `h² = g2 y/4 − c_ω² y²` (`σ₊σ₋ = q`); exponential stability of the second-order slow flow is
  exactly the corrected criterion (`secondOrder_exponentiallyStable_iff`); the larger exponent
  `σ₊ = −a + h` is positive iff `a < 0 ∨ q(y) < 0` (`sigmaPlus_pos_iff`).
* §8: `Λ* < 1 ↔ disc > 0` (`lamStar_lt_one_iff`, needs `α₀ > 0`, `g2 > 0`, `S > 0`);
  `q < 0` exactly on `(y₋, y₊)`; Theorem 1 (`tongue_root_split`, `sqrt_root_le`); Theorem 2
  (`pumpQ_bounds`, `tongue_root_pos`); the identity `q(α₀/c_α) = (α₀/c_α)(c_ω²α₀/c_α − g2/4)`;
  the ordering `√y₋ ≤ √y₊ ≤ |𝒢|/(2c_ω) < √(α₀/c_α)` under the side condition, and its
  breakdown `y₋ < α₀/c_α < y₊`; `a(y₋) > 0` whenever `disc ≥ 0`.
* §8 detuned boundary: the flip set `ℱ = {(y, Δ) : D ≥ 0 ∧ √D > a}`, `D = g2 y/4 − (Δ + c_ω y)²`.
  Its `Δ`-projection over `y > 0` is exactly `(Δ*₋, Δ*₊)` for `c_α < 0`, and
  `(−∞, g2/(16c_ω) − 4c_ωα₀²/g2)` for `c_α = 0`; for `c_α > 0` in the high-gain case
  `|𝒢| > 4c_ω√(α₀/c_α)` its supremum `g2/(16c_ω)` is attained and it is unbounded below; the
  two `c_α > 0` branches agree on the switching surface (`deltaStarPlus_switch`). In the
  low-gain case `|𝒢| ≤ 4c_ω√(α₀/c_α)` the projection contains `(Δ*₋, Δ*₊)` and lies below `Δ*₊`
  (`flipProjection_calpha_pos_lowGain`), so `Δ_sup = Δ*₊`, not attained
  (`flipProjection_calpha_pos_lowGain_isLUB`). The proof uses the detuned quadratic
  `P(Δ) = c_α²Δ² + Qc_ωΔ − (Q² − 4Sα₀²)/4 = min_y S(a² − D)` (`detunedP_eq`, `detunedP_neg_iff`).
  Limit `c_α → 0`: `Δ*₊ = (Q² − 4Sα₀²)/(2(√S√(Q² − 4c_α²α₀²) + c_ωQ))` (`deltaStarPlus_eq_rat`)
  tends to the `c_α = 0` value `g2/(16c_ω) − 4c_ωα₀²/g2` (`tendsto_deltaStarPlus`), and
  `c_α ↦ Δ_sup = sSup (Δ-projection)` is continuous at `0` (`continuousAt_sSup_flipProjection`;
  for small `c_α > 0` the low-gain branch applies).
* §9 two-circle criterion: `q(y₀)/α₀² = R² − 2Λ_α`, `4q'(y₀)/g2 = 2R² − 1 − 2Λ_α`
  (`y₀ = 4α₀²/g2`); `Λ* = 2(R − Λ_α)`, `Λ* < 1 ↔ Λ² < 1/4 + Λ_α`; `y₋ < y₀` iff
  `R² < 2Λ_α ∨ 2R² > 1 + 2Λ_α` (`yMinus_lt_y0_iff`); `c_α < 0` and `Λ* < 1` force every root
  above `y₀`, i.e. `e(0) < 0` (`y0_lt_root_of_calpha_neg`); `t = y₋/y₀` solves
  `R² t² − (1 + 2Λ_α) t + 1 = 0`.

Source: work-sync projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md §6 (corrected criterion), §7 (two exponents), §8 (tongue-centre
quadratic, all corollaries, detuned boundary, including the low-gain `c_α > 0` branch and the
continuity of `Δ_sup` at `c_α = 0`), §9 (two-circle criterion). The note's §8 is
recorded as hand-checked; every identity is re-proved here.

Architecture: real algebra inside an averaged model, no model family; all results remain public
foundation support. Exponential stability of the second-order slow flow is
`Flow.GloballyExponentiallyStable` of its linear field (through `slowFlow_exponentiallyStable_iff`).
-/

noncomputable section
namespace powerlib.ParametricResonance

open Set Filter Topology

/-! ## A quadratic helper -/

/-- For `a > 0`, `a x² + b x + c < 0` iff `x` lies strictly between the two roots. -/
@[powerlib_foundation] theorem quad_neg_iff {a b c x : ℝ} (ha : 0 < a) :
    a * x ^ 2 + b * x + c < 0 ↔
      (-b - √(b ^ 2 - 4 * a * c)) / (2 * a) < x ∧ x < (-b + √(b ^ 2 - 4 * a * c)) / (2 * a) := by
  have h : a * x ^ 2 + b * x + c < 0 ↔ (2 * a * x + b) ^ 2 < b ^ 2 - 4 * a * c := by
    constructor <;> intro h <;> nlinarith
  rw [h, Real.sq_lt, div_lt_iff₀ (by positivity), lt_div_iff₀ (by positivity)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- For `a ≠ 0` and nonnegative discriminant, `(−b ± √D)/(2a)` are roots. -/
@[powerlib_foundation] theorem quad_root {a b c : ℝ} (ha : a ≠ 0) (hD : 0 ≤ b ^ 2 - 4 * a * c)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    a * ((-b + σ * √(b ^ 2 - 4 * a * c)) / (2 * a)) ^ 2 +
      b * ((-b + σ * √(b ^ 2 - 4 * a * c)) / (2 * a)) + c = 0 := by
  have hs := Real.sq_sqrt hD
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set r := √(b ^ 2 - 4 * a * c) with hr
  have key : a * ((-b + σ * r) / (2 * a)) ^ 2 + b * ((-b + σ * r) / (2 * a)) + c =
      (σ ^ 2 * r ^ 2 - (b ^ 2 - 4 * a * c)) / (4 * a) := by
    field_simp; ring
  rw [key, hσ2, hs]; simp

/-! ## The second-order slow flow (§6–§7) -/

variable (α₀ cα cω g2 : ℝ)

/-- Amplitude-dependent damping `a(y) = α₀ − c_α y`. -/
def damping (y : ℝ) : ℝ := α₀ - cα * y

/-- Square of the splitting `h(y)² = g2 y/4 − c_ω² y²` (tongue centre). -/
def splitSq (y : ℝ) : ℝ := g2 * y / 4 - cω ^ 2 * y ^ 2

/-- `Q = g2/4 + 2α₀c_α`. -/
def pumpQ : ℝ := g2 / 4 + 2 * α₀ * cα

/-- The tongue-centre quadratic `q(y) = (c_α² + c_ω²) y² − Q y + α₀²`. -/
def tongue (y : ℝ) : ℝ := (cα ^ 2 + cω ^ 2) * y ^ 2 - pumpQ α₀ cα g2 * y + α₀ ^ 2

/-- Discriminant `Q² − 4(c_α² + c_ω²)α₀²`. -/
def tongueDisc : ℝ := pumpQ α₀ cα g2 ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2

/-- Existence index `Λ* = 8α₀(√(c_α² + c_ω²) − c_α)/g2`. -/
def lamStar : ℝ := 8 * α₀ * (√(cα ^ 2 + cω ^ 2) - cα) / g2

/-- Smaller root `y₋`. -/
def yMinus : ℝ := (pumpQ α₀ cα g2 - √(tongueDisc α₀ cα cω g2)) / (2 * (cα ^ 2 + cω ^ 2))

/-- Larger root `y₊`. -/
def yPlus : ℝ := (pumpQ α₀ cα g2 + √(tongueDisc α₀ cα cω g2)) / (2 * (cα ^ 2 + cω ^ 2))

/-- State matrix of the second-order slow flow at squared amplitude `y`, detuning `Δ` and pump
coefficient `g` (`|g|² = g2 y/4` in the source). -/
def secondOrderMatrix (Δ y : ℝ) (g : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  slowFlowMatrix (damping α₀ cα y) (Δ + cω * y) g

/-- The second-order slow flow as a linear field on `ℝ²`. -/
def secondOrderSystem (Δ y : ℝ) (g : ℂ) : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  slowFlowSystem (damping α₀ cα y) (Δ + cω * y) g

variable {α₀ cα cω g2}

/-- `q(y) = a(y)² − h(y)²` (`σ₊σ₋ = q` for `σ_± = −a ± h`). -/
@[powerlib_foundation] theorem tongue_eq_damping_sq_sub_splitSq (y : ℝ) :
    tongue α₀ cα cω g2 y = damping α₀ cα y ^ 2 - splitSq cω g2 y := by
  simp only [tongue, damping, splitSq, pumpQ]; ring

@[powerlib_foundation] theorem sigma_mul (y h : ℝ) (hh : h ^ 2 = splitSq cω g2 y) :
    (-damping α₀ cα y + h) * (-damping α₀ cα y - h) = tongue α₀ cα cω g2 y := by
  rw [tongue_eq_damping_sq_sub_splitSq, ← hh]; ring

@[powerlib_foundation] theorem det_secondOrderMatrix (Δ y : ℝ) (g : ℂ)
    (hg : ‖g‖ ^ 2 = g2 * y / 4) :
    (secondOrderMatrix α₀ cα cω Δ y g).det =
      damping α₀ cα y ^ 2 + (Δ + cω * y) ^ 2 - g2 * y / 4 := by
  simp only [secondOrderMatrix, det_slowFlowMatrix, hg]

/-- At the tongue centre the determinant of the second-order slow flow is `q(y)`. -/
@[powerlib_foundation] theorem det_secondOrderMatrix_centre (y : ℝ) (g : ℂ)
    (hg : ‖g‖ ^ 2 = g2 * y / 4) :
    (secondOrderMatrix α₀ cα cω 0 y g).det = tongue α₀ cα cω g2 y := by
  rw [det_secondOrderMatrix 0 y g hg, tongue_eq_damping_sq_sub_splitSq]
  simp only [splitSq]; ring

/-- The corrected criterion (§6) is exactly exponential stability of the second-order slow
flow: `a(y) > 0 ∧ (δ̂₁|𝒢|/2)² < a(y)² + (Δ + c_ω y)²`. -/
@[powerlib_foundation] theorem secondOrder_exponentiallyStable_iff (Δ y : ℝ) (g : ℂ)
    (hg : ‖g‖ ^ 2 = g2 * y / 4) :
    Flow.GloballyExponentiallyStable (secondOrderSystem α₀ cα cω Δ y g) 0 ↔
      0 < damping α₀ cα y ∧ g2 * y / 4 < damping α₀ cα y ^ 2 + (Δ + cω * y) ^ 2 := by
  rw [secondOrderSystem, slowFlow_exponentiallyStable_iff, hg]

/-- `σ₊ = −a + h > 0` iff `a < 0` or `q(y) < 0` (`h = √(h²)`; in the complex regime
`h² < 0` the real part `−a` is what matters and `√` returns `0`). -/
@[powerlib_foundation] theorem sigmaPlus_pos_iff (y : ℝ) :
    0 < -damping α₀ cα y + √(splitSq cω g2 y) ↔
      damping α₀ cα y < 0 ∨ tongue α₀ cα cω g2 y < 0 := by
  rw [tongue_eq_damping_sq_sub_splitSq]
  have hs := Real.sqrt_nonneg (splitSq cω g2 y)
  constructor
  · intro h
    rcases lt_or_ge (damping α₀ cα y) 0 with ha | ha
    · exact Or.inl ha
    · right
      have : damping α₀ cα y < √(splitSq cω g2 y) := by linarith
      have := (Real.lt_sqrt ha).mp this
      linarith
  · rintro (ha | hq)
    · linarith
    · rcases lt_or_ge (damping α₀ cα y) 0 with ha | ha
      · linarith
      · have : damping α₀ cα y < √(splitSq cω g2 y) := (Real.lt_sqrt ha).mpr (by linarith)
        linarith

/-! ## The tongue-centre quadratic (§8) -/

/-- `q(y) < 0` exactly strictly between the two roots. -/
@[powerlib_foundation] theorem tongue_neg_iff (hS : 0 < cα ^ 2 + cω ^ 2) (y : ℝ) :
    tongue α₀ cα cω g2 y < 0 ↔ yMinus α₀ cα cω g2 < y ∧ y < yPlus α₀ cα cω g2 := by
  have h := quad_neg_iff (a := cα ^ 2 + cω ^ 2) (b := -pumpQ α₀ cα g2) (c := α₀ ^ 2) (x := y) hS
  have hd : (-pumpQ α₀ cα g2) ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2 = tongueDisc α₀ cα cω g2 := by
    simp only [tongueDisc]; ring
  rw [hd, neg_neg] at h
  simp only [tongue, yMinus, yPlus]
  rw [show (cα ^ 2 + cω ^ 2) * y ^ 2 - pumpQ α₀ cα g2 * y + α₀ ^ 2 =
    (cα ^ 2 + cω ^ 2) * y ^ 2 + -pumpQ α₀ cα g2 * y + α₀ ^ 2 by ring]
  exact h

@[powerlib_foundation] theorem tongue_yMinus (hS : 0 < cα ^ 2 + cω ^ 2)
    (hd : 0 ≤ tongueDisc α₀ cα cω g2) : tongue α₀ cα cω g2 (yMinus α₀ cα cω g2) = 0 := by
  have hd' : 0 ≤ (-pumpQ α₀ cα g2) ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2 := by
    simp only [tongueDisc] at hd; linarith
  have h := quad_root hS.ne' hd' (-1) (Or.inr rfl)
  have he : (-pumpQ α₀ cα g2) ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2 = tongueDisc α₀ cα cω g2 := by
    simp only [tongueDisc]; ring
  rw [he] at h
  simp only [tongue, yMinus]
  linear_combination h

@[powerlib_foundation] theorem tongue_yPlus (hS : 0 < cα ^ 2 + cω ^ 2)
    (hd : 0 ≤ tongueDisc α₀ cα cω g2) : tongue α₀ cα cω g2 (yPlus α₀ cα cω g2) = 0 := by
  have hd' : 0 ≤ (-pumpQ α₀ cα g2) ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2 := by
    simp only [tongueDisc] at hd; linarith
  have h := quad_root hS.ne' hd' 1 (Or.inl rfl)
  have he : (-pumpQ α₀ cα g2) ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2 = tongueDisc α₀ cα cω g2 := by
    simp only [tongueDisc]; ring
  rw [he] at h
  simp only [tongue, yPlus]
  linear_combination h

@[powerlib_foundation] theorem yMinus_le_yPlus (hS : 0 < cα ^ 2 + cω ^ 2) :
    yMinus α₀ cα cω g2 ≤ yPlus α₀ cα cω g2 := by
  simp only [yMinus, yPlus]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [Real.sqrt_nonneg (tongueDisc α₀ cα cω g2)]

/-- The flip sector `{q < 0}` is nonempty iff the discriminant is positive. -/
@[powerlib_foundation] theorem exists_tongue_neg_iff (hS : 0 < cα ^ 2 + cω ^ 2) :
    (∃ y, tongue α₀ cα cω g2 y < 0) ↔ 0 < tongueDisc α₀ cα cω g2 := by
  constructor
  · rintro ⟨y, hy⟩
    by_contra h
    push Not at h
    have hk : 4 * (cα ^ 2 + cω ^ 2) * tongue α₀ cα cω g2 y =
        (2 * (cα ^ 2 + cω ^ 2) * y - pumpQ α₀ cα g2) ^ 2 - tongueDisc α₀ cα cω g2 := by
      simp only [tongue, tongueDisc]; ring
    nlinarith [sq_nonneg (2 * (cα ^ 2 + cω ^ 2) * y - pumpQ α₀ cα g2)]
  · intro h
    refine ⟨pumpQ α₀ cα g2 / (2 * (cα ^ 2 + cω ^ 2)), ?_⟩
    have hk : 4 * (cα ^ 2 + cω ^ 2) *
        tongue α₀ cα cω g2 (pumpQ α₀ cα g2 / (2 * (cα ^ 2 + cω ^ 2))) =
        -tongueDisc α₀ cα cω g2 := by
      simp only [tongue, tongueDisc]; field_simp; ring
    nlinarith

/-- `Λ* < 1 ↔ disc > 0` (`α₀ > 0`, `|𝒢| > 0`, `c_α² + c_ω² > 0`). -/
@[powerlib_foundation] theorem lamStar_lt_one_iff (hα : 0 < α₀) (hg : 0 < g2)
    (hS : 0 < cα ^ 2 + cω ^ 2) :
    lamStar α₀ cα cω g2 < 1 ↔ 0 < tongueDisc α₀ cα cω g2 := by
  set r := √(cα ^ 2 + cω ^ 2) with hr
  have hr2 : r ^ 2 = cα ^ 2 + cω ^ 2 := Real.sq_sqrt hS.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hS
  have hrα : |cα| ≤ r := Real.abs_le_sqrt (by nlinarith [sq_nonneg cω])
  have hQlow : -(2 * α₀ * r) < pumpQ α₀ cα g2 := by
    simp only [pumpQ]
    have := neg_abs_le cα
    nlinarith
  have hdisc : tongueDisc α₀ cα cω g2 =
      (pumpQ α₀ cα g2 - 2 * α₀ * r) * (pumpQ α₀ cα g2 + 2 * α₀ * r) := by
    simp only [tongueDisc]; rw [← hr2]; ring
  rw [lamStar, div_lt_one hg, hdisc]
  constructor
  · intro h
    have : 2 * α₀ * r < pumpQ α₀ cα g2 := by simp only [pumpQ]; linarith
    exact mul_pos (by linarith) (by linarith)
  · intro h
    have hpos : 0 < pumpQ α₀ cα g2 + 2 * α₀ * r := by linarith
    have : 0 < pumpQ α₀ cα g2 - 2 * α₀ * r := (pos_iff_pos_of_mul_pos h).mpr hpos
    simp only [pumpQ] at this
    linarith

/-- Degenerate linear case `c_α = c_ω = 0`: `q(y) = α₀² − g2 y/4`, single threshold
`y* = 4α₀²/g2`. -/
@[powerlib_foundation] theorem tongue_linear (hg : 0 < g2) (y : ℝ) :
    tongue α₀ 0 0 g2 y < 0 ↔ 4 * α₀ ^ 2 / g2 < y := by
  simp only [tongue, pumpQ]
  rw [div_lt_iff₀ hg]
  constructor <;> intro h <;> nlinarith

/-- Theorem 1: every root satisfies `c_ω² y² ≤ g2 y/4`, with equality iff `α₀ = c_α y`. -/
@[powerlib_foundation] theorem tongue_root_split {y : ℝ} (h : tongue α₀ cα cω g2 y = 0) :
    cω ^ 2 * y ^ 2 ≤ g2 * y / 4 ∧ (cω ^ 2 * y ^ 2 = g2 * y / 4 ↔ α₀ = cα * y) := by
  have he : g2 * y / 4 = (α₀ - cα * y) ^ 2 + cω ^ 2 * y ^ 2 := by
    simp only [tongue, pumpQ] at h; linarith
  refine ⟨by nlinarith [sq_nonneg (α₀ - cα * y)], ?_⟩
  constructor
  · intro h2
    have : (α₀ - cα * y) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro h2
    rw [he, h2]; ring

/-- Theorem 1, amplitude form: every positive root has `√y ≤ |𝒢|/(2c_ω)` (`c_ω > 0`). -/
@[powerlib_foundation] theorem sqrt_root_le (hcω : 0 < cω) {y : ℝ} (hy : 0 < y)
    (h : tongue α₀ cα cω g2 y = 0) : √y ≤ √g2 / (2 * cω) := by
  have h1 := (tongue_root_split h).1
  have hy' : y ≤ g2 / (4 * cω ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  rw [le_div_iff₀ (by positivity)]
  calc √y * (2 * cω) = √(y * (4 * cω ^ 2)) := by
        rw [Real.sqrt_mul hy.le, show (4 : ℝ) * cω ^ 2 = (2 * cω) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
    _ ≤ √g2 := Real.sqrt_le_sqrt (by rwa [le_div_iff₀ (by positivity)] at hy')

/-- Theorem 2 (first part): a nonnegative discriminant forces `Q ≥ 2√(c_α² + c_ω²) α₀ > 0`. -/
@[powerlib_foundation] theorem pumpQ_bounds (hα : 0 < α₀) (hg : 0 < g2)
    (hS : 0 < cα ^ 2 + cω ^ 2) (hd : 0 ≤ tongueDisc α₀ cα cω g2) :
    2 * √(cα ^ 2 + cω ^ 2) * α₀ ≤ pumpQ α₀ cα g2 ∧ 0 < pumpQ α₀ cα g2 := by
  set r := √(cα ^ 2 + cω ^ 2) with hr
  have hr2 : r ^ 2 = cα ^ 2 + cω ^ 2 := Real.sq_sqrt hS.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hS
  have hrα : |cα| ≤ r := Real.abs_le_sqrt (by nlinarith [sq_nonneg cω])
  have hQlow : -(2 * α₀ * r) < pumpQ α₀ cα g2 := by
    simp only [pumpQ]
    have := neg_abs_le cα
    nlinarith
  have hdisc : tongueDisc α₀ cα cω g2 =
      (pumpQ α₀ cα g2 - 2 * α₀ * r) * (pumpQ α₀ cα g2 + 2 * α₀ * r) := by
    simp only [tongueDisc]; rw [← hr2]; ring
  have hpos : 0 < pumpQ α₀ cα g2 + 2 * α₀ * r := by linarith
  have h1 : 0 ≤ pumpQ α₀ cα g2 - 2 * α₀ * r := by
    rw [hdisc] at hd
    exact nonneg_of_mul_nonneg_left hd hpos
  constructor
  · linarith
  · nlinarith

/-- Theorem 2 (second part): every real root of `q` is positive. -/
@[powerlib_foundation] theorem tongue_root_pos (hα : 0 < α₀) (hg : 0 < g2) {y : ℝ}
    (h : tongue α₀ cα cω g2 y = 0) : 0 < y := by
  have he : g2 * y / 4 = (α₀ - cα * y) ^ 2 + cω ^ 2 * y ^ 2 := by
    simp only [tongue, pumpQ] at h; linarith
  by_contra hy
  push Not at hy
  have h1 : g2 * y / 4 ≤ 0 := by nlinarith
  have h2 : (α₀ - cα * y) ^ 2 = 0 := by nlinarith [sq_nonneg (α₀ - cα * y), sq_nonneg (cω * y)]
  have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have h4 : cα * y ≤ 0 ∨ 0 ≤ cα * y := le_total _ _
  have : y = 0 := by nlinarith [sq_nonneg (cω * y)]
  subst this
  simp at h3
  linarith

/-- The NS side condition as the sign of `q` at the NS amplitude:
`q(α₀/c_α) = (α₀/c_α)(c_ω² α₀/c_α − g2/4)`. -/
@[powerlib_foundation] theorem tongue_at_ns (hcα : cα ≠ 0) :
    tongue α₀ cα cω g2 (α₀ / cα) = α₀ / cα * (cω ^ 2 * α₀ / cα - g2 / 4) := by
  simp only [tongue, pumpQ]
  field_simp
  ring

/-- For `c_α, c_ω > 0`: `q(α₀/c_α) < 0` iff the side condition is broken,
`√(α₀/c_α) < |𝒢|/(2c_ω)`. -/
@[powerlib_foundation] theorem tongue_at_ns_neg_iff (hα : 0 < α₀) (hcα : 0 < cα)
    (hcω : 0 < cω) :
    tongue α₀ cα cω g2 (α₀ / cα) < 0 ↔ √(α₀ / cα) < √g2 / (2 * cω) := by
  rw [tongue_at_ns hcα.ne']
  have hy : 0 < α₀ / cα := div_pos hα hcα
  rw [mul_neg_iff]
  have key : cω ^ 2 * α₀ / cα - g2 / 4 < 0 ↔ α₀ / cα * (2 * cω) ^ 2 < g2 := by
    constructor <;> intro h
    · have : cω ^ 2 * α₀ / cα = cω ^ 2 * (α₀ / cα) := by ring
      nlinarith
    · have : cω ^ 2 * α₀ / cα = cω ^ 2 * (α₀ / cα) := by ring
      nlinarith
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · rw [lt_div_iff₀ (by positivity)]
      have := key.mp h
      calc √(α₀ / cα) * (2 * cω) = √(α₀ / cα * (2 * cω) ^ 2) := by
            rw [Real.sqrt_mul hy.le, Real.sqrt_sq (by positivity)]
        _ < √g2 := Real.sqrt_lt_sqrt (by positivity) this
    · linarith
  · intro h
    left
    refine ⟨hy, key.mpr ?_⟩
    rw [lt_div_iff₀ (by positivity)] at h
    have h' : √(α₀ / cα * (2 * cω) ^ 2) < √g2 := by
      rw [Real.sqrt_mul hy.le, Real.sqrt_sq (by positivity)]; exact h
    exact (Real.sqrt_lt_sqrt_iff (by positivity)).mp h'

/-- Side condition broken ⇔ `y₋ < α₀/c_α < y₊`. -/
@[powerlib_foundation] theorem side_broken_iff (hα : 0 < α₀) (hcα : 0 < cα) (hcω : 0 < cω) :
    √(α₀ / cα) < √g2 / (2 * cω) ↔
      yMinus α₀ cα cω g2 < α₀ / cα ∧ α₀ / cα < yPlus α₀ cα cω g2 := by
  rw [← tongue_at_ns_neg_iff hα hcα hcω, tongue_neg_iff (by positivity)]

/-- Ordering under the side condition (`c_α, c_ω > 0`, `disc ≥ 0`):
`√y₋ ≤ √y₊ ≤ |𝒢|/(2c_ω) < √(α₀/c_α) = δ̂₁^{NS}`. -/
@[powerlib_foundation] theorem ordering (hα : 0 < α₀) (hg : 0 < g2) (hcα : 0 < cα)
    (hcω : 0 < cω) (hd : 0 ≤ tongueDisc α₀ cα cω g2) (hside : √g2 / (2 * cω) < √(α₀ / cα)) :
    √(yMinus α₀ cα cω g2) ≤ √(yPlus α₀ cα cω g2) ∧ √(yPlus α₀ cα cω g2) ≤ √g2 / (2 * cω) ∧
      √g2 / (2 * cω) < √(α₀ / cα) := by
  have hS : 0 < cα ^ 2 + cω ^ 2 := by positivity
  have hp := tongue_yPlus hS hd
  refine ⟨Real.sqrt_le_sqrt (yMinus_le_yPlus hS), ?_, hside⟩
  exact sqrt_root_le hcω (tongue_root_pos hα hg hp) hp

/-- `a(y₋) > 0` whenever the discriminant is nonnegative: `√y₋` is always an up-crossing of
`σ₊`. -/
@[powerlib_foundation] theorem damping_yMinus_pos (hα : 0 < α₀) (hg : 0 < g2)
    (hS : 0 < cα ^ 2 + cω ^ 2) (hd : 0 ≤ tongueDisc α₀ cα cω g2) :
    0 < damping α₀ cα (yMinus α₀ cα cω g2) := by
  set y := yMinus α₀ cα cω g2 with hy
  have hq := tongue_yMinus hS hd
  have hypos := tongue_root_pos hα hg hq
  have hvert : 2 * (cα ^ 2 + cω ^ 2) * y ≤ pumpQ α₀ cα g2 := by
    simp only [hy, yMinus]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    · nlinarith [Real.sqrt_nonneg (tongueDisc α₀ cα cω g2)]
  have he : g2 * y / 4 = (α₀ - cα * y) ^ 2 + cω ^ 2 * y ^ 2 := by
    simp only [tongue, pumpQ] at hq; linarith
  simp only [damping]
  by_contra hneg
  push Not at hneg
  simp only [pumpQ] at hvert
  -- multiply the vertex bound by `y > 0` and use the root identity
  have h1 : (cα ^ 2 + cω ^ 2) * y ^ 2 ≤ α₀ ^ 2 := by nlinarith
  have h2 : α₀ ^ 2 ≤ (cα * y) ^ 2 := by nlinarith
  have h3 : cω ^ 2 * y ^ 2 ≤ 0 := by nlinarith
  have h4 : (α₀ - cα * y) ^ 2 = 0 := by nlinarith [sq_nonneg (cω * y)]
  have h5 : g2 * y / 4 = 0 := by nlinarith [sq_nonneg (cω * y)]
  have : 0 < g2 * y / 4 := by positivity
  linarith

/-! ## The detuned flip boundary (§8) -/

/-- `D(y, Δ) = g2 y/4 − (Δ + c_ω y)²`. -/
def detunedD (cω g2 Δ y : ℝ) : ℝ := g2 * y / 4 - (Δ + cω * y) ^ 2

/-- The flip-form instability set `ℱ = {(y, Δ) : D ≥ 0 ∧ √D > a}`. -/
def flipSet (α₀ cα cω g2 : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ detunedD cω g2 p.2 p.1 ∧ damping α₀ cα p.1 < √(detunedD cω g2 p.2 p.1)}

/-- `Δ`-projection of the flip set over positive amplitudes: the image of `ℱ ∩ {y > 0}` under
`(y, Δ) ↦ Δ` (`mem_flipProjection`). A static set in the parameter plane `(y, Δ)`. -/
def flipProjection (α₀ cα cω g2 : ℝ) : Set ℝ :=
  Prod.snd '' (flipSet α₀ cα cω g2 ∩ Prod.fst ⁻¹' Ioi 0)

/-- `Δ*_± = (±√(c_α² + c_ω²) √(Q² − 4c_α²α₀²) − c_ω Q)/(2c_α²)`. -/
def deltaStarPlus (α₀ cα cω g2 : ℝ) : ℝ :=
  (√(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) - cω * pumpQ α₀ cα g2) /
    (2 * cα ^ 2)

def deltaStarMinus (α₀ cα cω g2 : ℝ) : ℝ :=
  (-(√(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2)) - cω * pumpQ α₀ cα g2) /
    (2 * cα ^ 2)

/-- Where `a > 0`, membership in `ℱ` is `a² < D`, i.e. the detuned quadratic
`S y² − (Q − 2c_ωΔ) y + α₀² + Δ²` is negative. -/
@[powerlib_foundation] theorem mem_flipSet_of_damping_pos {y Δ : ℝ}
    (ha : 0 < damping α₀ cα y) :
    (y, Δ) ∈ flipSet α₀ cα cω g2 ↔
      (cα ^ 2 + cω ^ 2) * y ^ 2 - (pumpQ α₀ cα g2 - 2 * cω * Δ) * y + (α₀ ^ 2 + Δ ^ 2) < 0 := by
  have hk : (cα ^ 2 + cω ^ 2) * y ^ 2 - (pumpQ α₀ cα g2 - 2 * cω * Δ) * y + (α₀ ^ 2 + Δ ^ 2) =
      damping α₀ cα y ^ 2 - detunedD cω g2 Δ y := by
    simp only [damping, detunedD, pumpQ]; ring
  rw [hk, flipSet, Set.mem_ofPred_eq]
  simp only
  constructor
  · rintro ⟨hD, hlt⟩
    have := (Real.lt_sqrt ha.le).mp hlt
    linarith
  · intro h
    refine ⟨by nlinarith, (Real.lt_sqrt ha.le).mpr (by linarith)⟩

/-- `Δ` lies in the projection iff `(y, Δ) ∈ ℱ` for some amplitude `y > 0`. -/
@[powerlib_foundation] theorem mem_flipProjection {Δ : ℝ} :
    Δ ∈ flipProjection α₀ cα cω g2 ↔ ∃ y, 0 < y ∧ (y, Δ) ∈ flipSet α₀ cα cω g2 := by
  constructor
  · rintro ⟨⟨y, Δ'⟩, ⟨hmem, hy⟩, rfl⟩
    exact ⟨y, hy, hmem⟩
  · rintro ⟨y, hy, hmem⟩
    exact ⟨(y, Δ), ⟨hmem, hy⟩, rfl⟩

/-- Case `c_α < 0`: the `Δ`-projection of `ℱ` is exactly `(Δ*₋, Δ*₊)` (both ends finite). -/
@[powerlib_foundation] theorem flipProjection_calpha_neg (hα : 0 < α₀) (hg : 0 < g2)
    (hcα : cα < 0) (hcω : 0 < cω) :
    flipProjection α₀ cα cω g2 = Ioo (deltaStarMinus α₀ cα cω g2) (deltaStarPlus α₀ cα cω g2) := by
  set S := cα ^ 2 + cω ^ 2 with hSdef
  set Q := pumpQ α₀ cα g2 with hQdef
  have hS : 0 < S := by positivity
  have hca2 : 0 < cα ^ 2 := by nlinarith
  have hrS : √S ^ 2 = S := Real.sq_sqrt hS.le
  have hcωS : cω < √S := by
    rw [show cω = √(cω ^ 2) from (Real.sqrt_sq hcω.le).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by simp only [hSdef]; linarith)
  have hdamp : ∀ y, 0 < y → 0 < damping α₀ cα y := fun y hy => by
    simp only [damping]; nlinarith
  -- the discriminant in `Δ` of the detuned quadratic
  have hQpos_of : ∀ K, 0 < K → K = Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 → 0 < Q := by
    intro K hK hKdef
    have hQlow : -(2 * α₀ * (-cα)) < Q := by simp only [hQdef, pumpQ]; nlinarith
    nlinarith
  ext Δ
  simp only [mem_flipProjection, mem_Ioo]
  constructor
  · rintro ⟨y, hy, hmem⟩
    rw [mem_flipSet_of_damping_pos (hdamp y hy)] at hmem
    -- the `y`-discriminant is positive and `Q − 2c_ωΔ > 0`
    have hb : 0 < Q - 2 * cω * Δ := by nlinarith [sq_nonneg Δ, sq_nonneg α₀]
    have hdisc : 4 * S * (α₀ ^ 2 + Δ ^ 2) < (Q - 2 * cω * Δ) ^ 2 := by
      nlinarith [sq_nonneg (2 * S * y - (Q - 2 * cω * Δ))]
    -- as a quadratic in `Δ`: `cα² Δ² + Q c_ω Δ − (Q² − 4 S α₀²)/4 < 0`
    have hq : cα ^ 2 * Δ ^ 2 + (Q * cω) * Δ + (-(Q ^ 2 - 4 * S * α₀ ^ 2) / 4) < 0 := by
      simp only [hSdef] at hdisc ⊢; nlinarith
    have h := (quad_neg_iff hca2).mp hq
    have hD : (Q * cω) ^ 2 - 4 * cα ^ 2 * (-(Q ^ 2 - 4 * S * α₀ ^ 2) / 4) =
        S * (Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) := by simp only [hSdef]; ring
    rw [hD, Real.sqrt_mul hS.le] at h
    simp only [deltaStarMinus, deltaStarPlus, ← hQdef, ← hSdef]
    constructor
    · convert h.1 using 1; ring
    · convert h.2 using 1; ring
  · rintro ⟨h1, h2⟩
    have hlt : deltaStarMinus α₀ cα cω g2 < deltaStarPlus α₀ cα cω g2 := h1.trans h2
    have hK : 0 < Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 := by
      by_contra hneg
      push Not at hneg
      have : √(Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) = 0 := Real.sqrt_eq_zero'.mpr hneg
      simp only [deltaStarMinus, deltaStarPlus, ← hQdef, ← hSdef, this, mul_zero] at hlt
      linarith
    have hQ : 0 < Q := hQpos_of _ hK rfl
    have hD : (Q * cω) ^ 2 - 4 * cα ^ 2 * (-(Q ^ 2 - 4 * S * α₀ ^ 2) / 4) =
        S * (Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) := by simp only [hSdef]; ring
    have hq : cα ^ 2 * Δ ^ 2 + (Q * cω) * Δ + (-(Q ^ 2 - 4 * S * α₀ ^ 2) / 4) < 0 := by
      rw [quad_neg_iff hca2, hD, Real.sqrt_mul hS.le]
      simp only [deltaStarMinus, deltaStarPlus, ← hQdef, ← hSdef] at h1 h2
      constructor
      · convert h1 using 1; ring
      · convert h2 using 1; ring
    have hdisc : 4 * S * (α₀ ^ 2 + Δ ^ 2) < (Q - 2 * cω * Δ) ^ 2 := by
      simp only [hSdef] at hq ⊢; nlinarith
    -- `Q − 2c_ωΔ > 0` because `Δ < Δ*₊ < Q/(2c_ω)`
    have hsK : √(Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) < Q := by
      rw [Real.sqrt_lt' hQ]
      have : 0 < cα ^ 2 * α₀ ^ 2 := by positivity
      linarith
    have hsK0 := Real.sqrt_nonneg (Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2)
    have hsS0 := Real.sqrt_nonneg S
    have hDP : deltaStarPlus α₀ cα cω g2 < Q / (2 * cω) := by
      simp only [deltaStarPlus, ← hQdef, ← hSdef]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have : cω * √(Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) < √S * Q := by
        calc cω * √(Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) ≤ cω * Q := by
              exact mul_le_mul_of_nonneg_left hsK.le hcω.le
          _ < √S * Q := mul_lt_mul_of_pos_right hcωS hQ
      nlinarith
    have hb : 0 < Q - 2 * cω * Δ := by
      have := h2.trans hDP
      rw [lt_div_iff₀ (by positivity)] at this
      linarith
    refine ⟨(Q - 2 * cω * Δ) / (2 * S), by positivity, ?_⟩
    rw [mem_flipSet_of_damping_pos (hdamp _ (by positivity))]
    have hk : 4 * S * (S * ((Q - 2 * cω * Δ) / (2 * S)) ^ 2 -
        (Q - 2 * cω * Δ) * ((Q - 2 * cω * Δ) / (2 * S)) + (α₀ ^ 2 + Δ ^ 2)) =
        4 * S * (α₀ ^ 2 + Δ ^ 2) - (Q - 2 * cω * Δ) ^ 2 := by
      field_simp; ring
    nlinarith

/-- Case `c_α = 0`: the `Δ`-projection of `ℱ` is `(−∞, g2/(16c_ω) − 4c_ωα₀²/g2)`:
`Δ_sup = |𝒢|²/(16c_ω) − 4c_ωα₀²/|𝒢|²`, `Δ_inf = −∞`. -/
@[powerlib_foundation] theorem flipProjection_calpha_zero (hα : 0 < α₀) (hg : 0 < g2)
    (hcω : 0 < cω) :
    flipProjection α₀ 0 cω g2 = Iio (g2 / (16 * cω) - 4 * cω * α₀ ^ 2 / g2) := by
  have hdamp : ∀ y, damping α₀ 0 y = α₀ := fun y => by simp [damping]
  have hQ : pumpQ α₀ 0 g2 = g2 / 4 := by simp [pumpQ]
  ext Δ
  simp only [mem_flipProjection, mem_Iio]
  have hmem : ∀ y, (y, Δ) ∈ flipSet α₀ 0 cω g2 ↔
      cω ^ 2 * y ^ 2 - (g2 / 4 - 2 * cω * Δ) * y + (α₀ ^ 2 + Δ ^ 2) < 0 := by
    intro y
    rw [mem_flipSet_of_damping_pos (by rw [hdamp]; exact hα), hQ]
    simp
  simp only [hmem]
  have hbound : g2 / (16 * cω) - 4 * cω * α₀ ^ 2 / g2 =
      ((g2 / 4) ^ 2 - 4 * cω ^ 2 * α₀ ^ 2) / (4 * (g2 / 4) * cω) := by
    field_simp; ring
  rw [hbound]
  constructor
  · rintro ⟨y, hy, h⟩
    have hb : 0 < g2 / 4 - 2 * cω * Δ := by nlinarith [sq_nonneg Δ, sq_nonneg α₀]
    have hdisc : 4 * cω ^ 2 * (α₀ ^ 2 + Δ ^ 2) < (g2 / 4 - 2 * cω * Δ) ^ 2 := by
      have hm := mul_neg_of_pos_of_neg (show (0 : ℝ) < 4 * cω ^ 2 by positivity) h
      nlinarith [sq_nonneg (2 * cω ^ 2 * y - (g2 / 4 - 2 * cω * Δ))]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · intro h
    rw [lt_div_iff₀ (by positivity)] at h
    have hdisc : 4 * cω ^ 2 * (α₀ ^ 2 + Δ ^ 2) < (g2 / 4 - 2 * cω * Δ) ^ 2 := by nlinarith
    have hb : 0 < g2 / 4 - 2 * cω * Δ := by nlinarith [sq_nonneg α₀, sq_nonneg cω]
    refine ⟨(g2 / 4 - 2 * cω * Δ) / (2 * cω ^ 2), by positivity, ?_⟩
    have hk : 4 * cω ^ 2 * (cω ^ 2 * ((g2 / 4 - 2 * cω * Δ) / (2 * cω ^ 2)) ^ 2 -
        (g2 / 4 - 2 * cω * Δ) * ((g2 / 4 - 2 * cω * Δ) / (2 * cω ^ 2)) + (α₀ ^ 2 + Δ ^ 2)) =
        4 * cω ^ 2 * (α₀ ^ 2 + Δ ^ 2) - (g2 / 4 - 2 * cω * Δ) ^ 2 := by
      field_simp; ring
    have : 0 < 4 * cω ^ 2 := by positivity
    nlinarith

/-- On the `a < 0` segment the upper boundary is `Δ₊(y) = −c_ω y + |𝒢|√y/2`, maximal at
`y* = g2/(16c_ω²)` with value `g2/(16c_ω)`. -/
@[powerlib_foundation] theorem upper_branch_le (hcω : 0 < cω) (hg : 0 ≤ g2) {y : ℝ} (hy : 0 ≤ y) :
    -cω * y + √g2 * √y / 2 ≤ g2 / (16 * cω) ∧
      -cω * (g2 / (16 * cω ^ 2)) + √g2 * √(g2 / (16 * cω ^ 2)) / 2 = g2 / (16 * cω) := by
  have hg2 : √g2 ^ 2 = g2 := Real.sq_sqrt hg
  have hy2 : √y ^ 2 = y := Real.sq_sqrt hy
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have key : (-cω * y + √g2 * √y / 2) * (16 * cω) = g2 - (4 * cω * √y - √g2) ^ 2 := by
      linear_combination (16 * cω ^ 2) * hy2 + hg2
    rw [key]
    nlinarith [sq_nonneg (4 * cω * √y - √g2)]
  · rw [Real.sqrt_div' _ (by positivity), show (16 : ℝ) * cω ^ 2 = (4 * cω) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    have hm : √g2 * √g2 = g2 := Real.mul_self_sqrt hg
    rw [show -cω * (g2 / (4 * cω) ^ 2) + √g2 * (√g2 / (4 * cω)) / 2 =
      -cω * (g2 / (4 * cω) ^ 2) + (√g2 * √g2) / (8 * cω) by field_simp; ring, hm]
    field_simp; ring

/-- Case `c_α > 0`, high gain `|𝒢| > 4c_ω √(α₀/c_α)` (i.e. `y* > α₀/c_α`): the supremum of the
`Δ`-projection is `g2/(16c_ω)` and is attained (independent of `α₀, c_α`). -/
@[powerlib_foundation] theorem flipProjection_calpha_pos_isGreatest (hg : 0 < g2)
    (hcα : 0 < cα) (hcω : 0 < cω) (hhigh : α₀ / cα < g2 / (16 * cω ^ 2)) :
    IsGreatest (flipProjection α₀ cα cω g2) (g2 / (16 * cω)) := by
  have hg2 : √g2 ^ 2 = g2 := Real.sq_sqrt hg.le
  constructor
  · -- attained at `y* = g2/(16 c_ω²)`, where `a < 0` and `D = 0`
    set y := g2 / (16 * cω ^ 2) with hydef
    refine mem_flipProjection.2 ⟨y, by positivity, ?_, ?_⟩
    · have hD : detunedD cω g2 (g2 / (16 * cω)) y = 0 := by
        simp only [detunedD, hydef]; field_simp; ring
      simp only; rw [hD]
    · have hD : detunedD cω g2 (g2 / (16 * cω)) y = 0 := by
        simp only [detunedD, hydef]; field_simp; ring
      simp only; rw [hD, Real.sqrt_zero]
      simp only [damping]
      have := (div_lt_iff₀ hcα).mp hhigh
      nlinarith
  · intro Δ hΔ
    obtain ⟨y, hy, hD, hlt⟩ := mem_flipProjection.1 hΔ
    simp only at hD hlt
    -- from `D ≥ 0`: `(Δ + c_ω y)² ≤ g2 y/4`, hence `Δ ≤ −c_ω y + √g2 √y/2 ≤ g2/(16c_ω)`
    have hsq : (Δ + cω * y) ^ 2 ≤ (√g2 * √y / 2) ^ 2 := by
      have : (√g2 * √y / 2) ^ 2 = g2 * y / 4 := by
        rw [div_pow, mul_pow, hg2, Real.sq_sqrt hy.le]; ring
      rw [this]; simp only [detunedD] at hD; linarith
    have h1 : Δ + cω * y ≤ √g2 * √y / 2 := (abs_le_of_sq_le_sq' hsq (by positivity)).2
    have := (upper_branch_le hcω hg.le hy.le).1
    linarith

/-- For `c_α > 0` the projection is unbounded below (`Δ_inf = −∞`). -/
@[powerlib_foundation] theorem flipProjection_calpha_pos_not_bddBelow (hg : 0 < g2)
    (hcα : 0 < cα) (hcω : 0 < cω) : ¬BddBelow (flipProjection α₀ cα cω g2) := by
  rintro ⟨m, hm⟩
  -- take `y` large with `a(y) < 0` and `Δ = −c_ω y` (so `D = g2 y/4 ≥ 0`)
  set y := max 1 ((|α₀| + 1) / cα + |m| / cω + 1) with hydef
  have hy1 : 1 ≤ y := le_max_left _ _
  have hy2 : (|α₀| + 1) / cα + |m| / cω + 1 ≤ y := le_max_right _ _
  have hmem : -(cω * y) ∈ flipProjection α₀ cα cω g2 := by
    refine mem_flipProjection.2 ⟨y, by linarith, ?_, ?_⟩
    · simp only [detunedD]; nlinarith
    · simp only [damping]
      have : (|α₀| + 1) / cα < y := by
        have := div_nonneg (abs_nonneg m) hcω.le; linarith
      rw [div_lt_iff₀ hcα] at this
      have := le_abs_self α₀
      have := Real.sqrt_nonneg (detunedD cω g2 (-(cω * y)) y)
      nlinarith
  have := hm hmem
  have h3 : |m| / cω < y := by
    have := div_nonneg (abs_nonneg α₀ |>.trans (le_add_of_nonneg_right zero_le_one)) hcα.le
    linarith
  rw [div_lt_iff₀ hcω] at h3
  have := neg_abs_le m
  nlinarith

/-- Switching surface `y* = α₀/c_α` (`|𝒢| = 4c_ω√(α₀/c_α)`, `c_α > 0`): the two branches agree,
`Δ*₊ = Δ₊(y*) = c_ω y_a`. -/
@[powerlib_foundation] theorem deltaStarPlus_switch (hα : 0 < α₀) (hcα : 0 < cα) (hcω : 0 < cω)
    (hsw : g2 = 16 * cω ^ 2 * (α₀ / cα)) :
    deltaStarPlus α₀ cα cω g2 = cω * (α₀ / cα) ∧ g2 / (16 * cω) = cω * (α₀ / cα) := by
  set ya := α₀ / cα with hya
  have hya0 : 0 < ya := div_pos hα hcα
  have hα' : α₀ = cα * ya := by rw [hya]; field_simp
  constructor
  · have hQ : pumpQ α₀ cα g2 = 4 * cω ^ 2 * ya + 2 * cα ^ 2 * ya := by
      simp only [pumpQ, hsw, hα']; ring
    have hK : pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 =
        (4 * cω ^ 2 * ya) * (4 * cω ^ 2 * ya + 4 * cα ^ 2 * ya) := by
      rw [hQ, hα']; ring
    have hsq : √(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) =
        2 * cω * ya * (2 * (cα ^ 2 + cω ^ 2)) := by
      rw [hK, ← Real.sqrt_mul (by positivity)]
      rw [show (cα ^ 2 + cω ^ 2) * (4 * cω ^ 2 * ya * (4 * cω ^ 2 * ya + 4 * cα ^ 2 * ya)) =
        (2 * cω * ya * (2 * (cα ^ 2 + cω ^ 2))) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    simp only [deltaStarPlus]
    rw [hsq, hQ]
    field_simp
    ring
  · rw [hsw]; field_simp

/-! ## The low-gain branch `c_α > 0` and the limit `c_α → 0` (§8) -/

/-- The detuned quadratic in `Δ`, `P(Δ) = c_α² Δ² + Q c_ω Δ − (Q² − 4(c_α² + c_ω²)α₀²)/4`, whose
roots are `Δ*_±` (`detunedP_neg_iff`). -/
def detunedP (α₀ cα cω g2 Δ : ℝ) : ℝ :=
  cα ^ 2 * Δ ^ 2 + pumpQ α₀ cα g2 * cω * Δ -
    (pumpQ α₀ cα g2 ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2) / 4

/-- `P(Δ) = S (a(y)² − D(y, Δ)) − (S y − (Q − 2c_ωΔ)/2)²` for every amplitude `y`
(`S = c_α² + c_ω²`): `P(Δ)/S` is the minimum over `y` of `a² − D`. -/
@[powerlib_foundation] theorem detunedP_eq (y Δ : ℝ) :
    detunedP α₀ cα cω g2 Δ =
      (cα ^ 2 + cω ^ 2) * (damping α₀ cα y ^ 2 - detunedD cω g2 Δ y) -
        ((cα ^ 2 + cω ^ 2) * y - (pumpQ α₀ cα g2 - 2 * cω * Δ) / 2) ^ 2 := by
  simp only [detunedP, damping, detunedD, pumpQ]; ring

/-- `P(Δ) ≤ S (a(y)² − D(y, Δ))` for every amplitude `y`. -/
@[powerlib_foundation] theorem detunedP_le (y Δ : ℝ) :
    detunedP α₀ cα cω g2 Δ ≤
      (cα ^ 2 + cω ^ 2) * (damping α₀ cα y ^ 2 - detunedD cω g2 Δ y) := by
  rw [detunedP_eq y Δ]
  nlinarith [sq_nonneg ((cα ^ 2 + cω ^ 2) * y - (pumpQ α₀ cα g2 - 2 * cω * Δ) / 2)]

/-- `a(y)² < D(y, Δ)` puts `(y, Δ)` in the flip set, whatever the sign of `a(y)`. -/
@[powerlib_foundation] theorem mem_flipSet_of_sq_lt {y Δ : ℝ}
    (h : damping α₀ cα y ^ 2 < detunedD cω g2 Δ y) : (y, Δ) ∈ flipSet α₀ cα cω g2 := by
  have hD : 0 ≤ detunedD cω g2 Δ y := (sq_nonneg _).trans h.le
  refine ⟨hD, ?_⟩
  calc damping α₀ cα y ≤ |damping α₀ cα y| := le_abs_self _
    _ = √(damping α₀ cα y ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ < √(detunedD cω g2 Δ y) := Real.sqrt_lt_sqrt (sq_nonneg _) h

/-- The roots of `P` are `Δ*_±`: for `c_α ≠ 0`, `P(Δ) < 0 ↔ Δ*₋ < Δ < Δ*₊`. -/
@[powerlib_foundation] theorem detunedP_neg_iff (hcα : cα ≠ 0) {Δ : ℝ} :
    detunedP α₀ cα cω g2 Δ < 0 ↔
      deltaStarMinus α₀ cα cω g2 < Δ ∧ Δ < deltaStarPlus α₀ cα cω g2 := by
  have hca2 : 0 < cα ^ 2 := by positivity
  have hS : 0 ≤ cα ^ 2 + cω ^ 2 := by positivity
  have h := quad_neg_iff (a := cα ^ 2) (b := pumpQ α₀ cα g2 * cω)
    (c := -(pumpQ α₀ cα g2 ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2) / 4) (x := Δ) hca2
  have hD : (pumpQ α₀ cα g2 * cω) ^ 2 -
      4 * cα ^ 2 * (-(pumpQ α₀ cα g2 ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2) / 4) =
      (cα ^ 2 + cω ^ 2) * (pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) := by ring
  rw [hD, Real.sqrt_mul hS] at h
  rw [show detunedP α₀ cα cω g2 Δ = cα ^ 2 * Δ ^ 2 + pumpQ α₀ cα g2 * cω * Δ +
      -(pumpQ α₀ cα g2 ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2) / 4 by simp only [detunedP]; ring, h]
  simp only [deltaStarMinus, deltaStarPlus]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor
  · convert h1 using 1; ring
  · convert h2 using 1; ring
  · convert h1 using 1; ring
  · convert h2 using 1; ring

/-- Beyond the larger root `P` is positive: `Δ*₊ < Δ → 0 < P(Δ)` (`c_α ≠ 0`). -/
@[powerlib_foundation] theorem detunedP_pos_of_gt (hcα : cα ≠ 0) {Δ : ℝ}
    (hΔ : deltaStarPlus α₀ cα cω g2 < Δ) : 0 < detunedP α₀ cα cω g2 Δ := by
  set S := cα ^ 2 + cω ^ 2 with hSdef
  set Q := pumpQ α₀ cα g2 with hQdef
  set K := Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 with hKdef
  have hca2 : 0 < cα ^ 2 := by positivity
  have hS : 0 ≤ S := by positivity
  have hr : 0 ≤ √S * √K := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- `2 c_α² Δ + Q c_ω > √S √K ≥ 0`
  have hlin : √S * √K < 2 * cα ^ 2 * Δ + Q * cω := by
    simp only [deltaStarPlus, ← hSdef, ← hQdef, ← hKdef] at hΔ
    rw [div_lt_iff₀ (by positivity)] at hΔ
    linarith
  have hk : 4 * cα ^ 2 * detunedP α₀ cα cω g2 Δ = (2 * cα ^ 2 * Δ + Q * cω) ^ 2 - S * K := by
    simp only [detunedP, ← hQdef, hSdef, hKdef]; ring
  have : S * K < (2 * cα ^ 2 * Δ + Q * cω) ^ 2 := by
    rcases le_total 0 K with hK | hK
    · have h1 : (√S * √K) ^ 2 = S * K := by
        rw [mul_pow, Real.sq_sqrt hS, Real.sq_sqrt hK]
      nlinarith
    · rw [Real.sqrt_eq_zero'.mpr hK, mul_zero] at hlin
      have h2 : 0 < (2 * cα ^ 2 * Δ + Q * cω) ^ 2 := by positivity
      nlinarith [mul_nonneg hS (neg_nonneg.mpr hK)]
  nlinarith

/-- `Δ*₊ < Q/(2c_ω)` when `c_α ≠ 0`, `c_ω > 0`, `Q > 0` and `c_α α₀ ≠ 0`; equivalently the
minimizing amplitude `(Q − 2c_ωΔ)/(2S)` is positive below `Δ*₊`. -/
@[powerlib_foundation] theorem deltaStarPlus_lt_div (hα : 0 < α₀) (hcα : cα ≠ 0) (hcω : 0 < cω)
    (hQ : 0 < pumpQ α₀ cα g2) :
    deltaStarPlus α₀ cα cω g2 < pumpQ α₀ cα g2 / (2 * cω) := by
  set S := cα ^ 2 + cω ^ 2 with hSdef
  set Q := pumpQ α₀ cα g2 with hQdef
  have hca2 : 0 < cα ^ 2 := by positivity
  have hS : 0 < S := by positivity
  have hcωS : cω < √S := by
    rw [show cω = √(cω ^ 2) from (Real.sqrt_sq hcω.le).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by simp only [hSdef]; linarith)
  have hsK : √(Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) < Q := by
    rw [Real.sqrt_lt' hQ]
    have : 0 < cα ^ 2 * α₀ ^ 2 := by positivity
    linarith
  have hsS0 := Real.sqrt_nonneg S
  simp only [deltaStarPlus, ← hQdef, ← hSdef]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : cω * √(Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) < √S * Q := by
    calc cω * √(Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) ≤ cω * Q :=
          mul_le_mul_of_nonneg_left hsK.le hcω.le
      _ < √S * Q := mul_lt_mul_of_pos_right hcωS hQ
  have hS' : √S ^ 2 = S := Real.sq_sqrt hS.le
  nlinarith [Real.sqrt_nonneg (Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2)]

/-- Every `Δ` with `P(Δ) < 0` below `Q/(2c_ω)` lies in the projection: at the amplitude
`y = (Q − 2c_ωΔ)/(2S)` one has `a² − D = P(Δ)/S < 0`. -/
@[powerlib_foundation] theorem mem_flipProjection_of_detunedP_neg (hcω : 0 < cω) {Δ : ℝ}
    (hP : detunedP α₀ cα cω g2 Δ < 0) (hΔ : Δ < pumpQ α₀ cα g2 / (2 * cω)) :
    Δ ∈ flipProjection α₀ cα cω g2 := by
  set S := cα ^ 2 + cω ^ 2 with hSdef
  have hS : 0 < S := by positivity
  have hB : 0 < pumpQ α₀ cα g2 - 2 * cω * Δ := by
    rw [lt_div_iff₀ (by positivity)] at hΔ; linarith
  refine mem_flipProjection.2 ⟨(pumpQ α₀ cα g2 - 2 * cω * Δ) / (2 * S), by positivity, ?_⟩
  apply mem_flipSet_of_sq_lt
  have h := detunedP_eq (α₀ := α₀) (cα := cα) (cω := cω) (g2 := g2)
    ((pumpQ α₀ cα g2 - 2 * cω * Δ) / (2 * S)) Δ
  rw [← hSdef, show S * ((pumpQ α₀ cα g2 - 2 * cω * Δ) / (2 * S)) -
    (pumpQ α₀ cα g2 - 2 * cω * Δ) / 2 = 0 by field_simp; ring] at h
  have : S * (damping α₀ cα ((pumpQ α₀ cα g2 - 2 * cω * Δ) / (2 * S)) ^ 2 -
      detunedD cω g2 Δ ((pumpQ α₀ cα g2 - 2 * cω * Δ) / (2 * S))) < 0 := by
    rw [h] at hP; simpa using hP
  have := (neg_of_mul_neg_right this hS.le)
  linarith

/-- Case `c_α > 0`, low gain `|𝒢| ≤ 4c_ω√(α₀/c_α)` (i.e. `y* = g2/(16c_ω²) ≤ α₀/c_α`): the
`Δ`-projection contains `(Δ*₋, Δ*₊)` and lies below `Δ*₊`. -/
@[powerlib_foundation] theorem flipProjection_calpha_pos_lowGain (hα : 0 < α₀) (hg : 0 < g2)
    (hcα : 0 < cα) (hcω : 0 < cω) (hlow : g2 / (16 * cω ^ 2) ≤ α₀ / cα) :
    Ioo (deltaStarMinus α₀ cα cω g2) (deltaStarPlus α₀ cα cω g2) ⊆ flipProjection α₀ cα cω g2 ∧
      flipProjection α₀ cα cω g2 ⊆ Iio (deltaStarPlus α₀ cα cω g2) := by
  set S := cα ^ 2 + cω ^ 2 with hSdef
  have hS : 0 < S := by positivity
  have hQ : 0 < pumpQ α₀ cα g2 := by simp only [pumpQ]; positivity
  refine ⟨fun Δ hΔ => ?_, fun Δ hΔ => ?_⟩
  · exact mem_flipProjection_of_detunedP_neg hcω ((detunedP_neg_iff hcα.ne').2 hΔ)
      (hΔ.2.trans (deltaStarPlus_lt_div hα hcα.ne' hcω hQ))
  obtain ⟨y, hy, hD, hlt⟩ := mem_flipProjection.1 hΔ
  simp only at hD hlt
  show Δ < deltaStarPlus α₀ cα cω g2
  by_cases hsq : damping α₀ cα y ^ 2 < detunedD cω g2 Δ y
  · -- `a² < D`: then `P(Δ) < 0`
    have h1 := detunedP_le (α₀ := α₀) (cα := cα) (cω := cω) (g2 := g2) y Δ
    have hP : detunedP α₀ cα cω g2 Δ < 0 := by
      have h2 : 0 < S * (detunedD cω g2 Δ y - damping α₀ cα y ^ 2) := by
        apply mul_pos hS; linarith
      have h3 : (cα ^ 2 + cω ^ 2) * (damping α₀ cα y ^ 2 - detunedD cω g2 Δ y) =
          -(S * (detunedD cω g2 Δ y - damping α₀ cα y ^ 2)) := by rw [hSdef]; ring
      linarith
    exact ((detunedP_neg_iff hcα.ne').1 hP).2
  · -- `D ≤ a²` and `a < √D`: then `a < 0`, i.e. `y > y_a = α₀/c_α`
    push Not at hsq
    have ha : damping α₀ cα y < 0 := by
      have h1 : √(detunedD cω g2 Δ y) ≤ |damping α₀ cα y| := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq
      rcases le_or_gt 0 (damping α₀ cα y) with h0 | h0
      · rw [abs_of_nonneg h0] at h1; linarith
      · exact h0
    set ya := α₀ / cα with hyadef
    have hya : 0 < ya := div_pos hα hcα
    have hyay : ya < y := by
      simp only [damping] at ha
      rw [hyadef, div_lt_iff₀ hcα]; linarith
    -- the upper branch `Δ₊(s) = −c_ω s² + (√g2/2) s` in `s = √y`
    set s := √y with hsdef
    set sa := √ya with hsadef
    have hs2 : s ^ 2 = y := Real.sq_sqrt hy.le
    have hsa2 : sa ^ 2 = ya := Real.sq_sqrt hya.le
    have hg2 : √g2 ^ 2 = g2 := Real.sq_sqrt hg.le
    have hsa0 : 0 < sa := Real.sqrt_pos.mpr hya
    have hsas : sa < s := Real.sqrt_lt_sqrt hya.le hyay
    have hg0 : 0 < √g2 := Real.sqrt_pos.mpr hg
    -- low gain: `√g2/(4c_ω) ≤ s_a`
    have hstar : √g2 ≤ 4 * cω * sa := by
      have h1 : g2 ≤ 16 * cω ^ 2 * ya := by
        rw [div_le_iff₀ (by positivity)] at hlow
        linarith [mul_comm (16 * cω ^ 2) ya]
      have h2 : √g2 ^ 2 ≤ (4 * cω * sa) ^ 2 := by
        rw [hg2, mul_pow, hsa2]; nlinarith
      exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
    -- `Δ ≤ Δ₊(s)` from `D ≥ 0`
    have hup : Δ + cω * y ≤ √g2 * s / 2 := by
      have hsq' : (Δ + cω * y) ^ 2 ≤ (√g2 * s / 2) ^ 2 := by
        rw [div_pow, mul_pow, hg2, hs2]; simp only [detunedD] at hD; linarith
      exact (abs_le_of_sq_le_sq' hsq' (by positivity)).2
    -- strict decrease of `Δ₊` beyond `s_a ≥ s*`
    have hdec : -cω * s ^ 2 + √g2 * s / 2 < -cω * sa ^ 2 + √g2 * sa / 2 := by
      have : 0 < (s - sa) * (cω * (s + sa) - √g2 / 2) := by
        apply mul_pos (by linarith)
        nlinarith
      nlinarith
    -- `Δ₊(s_a) ≤ Δ*₊`: `P(Δ₊(s_a)) ≤ S (a(y_a)² − D(y_a, Δ₊(s_a))) = 0`
    have hPa : detunedP α₀ cα cω g2 (-cω * sa ^ 2 + √g2 * sa / 2) ≤ 0 := by
      have h := detunedP_le (α₀ := α₀) (cα := cα) (cω := cω) (g2 := g2) ya
        (-cω * sa ^ 2 + √g2 * sa / 2)
      have hda : damping α₀ cα ya = 0 := by
        simp only [damping, hyadef]; field_simp; ring
      have hDa : detunedD cω g2 (-cω * sa ^ 2 + √g2 * sa / 2) ya = 0 := by
        simp only [detunedD]; rw [← hsa2]
        linear_combination (-(sa ^ 2) / 4) * hg2
      rw [hda, hDa] at h
      simpa using h
    have hle : -cω * sa ^ 2 + √g2 * sa / 2 ≤ deltaStarPlus α₀ cα cω g2 := by
      by_contra hcon
      push Not at hcon
      have := detunedP_pos_of_gt hcα.ne' hcon
      linarith
    rw [hs2] at hdec
    linarith

/-- Case `c_α > 0`, low gain: `Δ_sup = Δ*₊` and, unlike the high-gain branch, it is **not**
attained. -/
@[powerlib_foundation] theorem flipProjection_calpha_pos_lowGain_isLUB (hα : 0 < α₀)
    (hg : 0 < g2) (hcα : 0 < cα) (hcω : 0 < cω) (hlow : g2 / (16 * cω ^ 2) ≤ α₀ / cα) :
    IsLUB (flipProjection α₀ cα cω g2) (deltaStarPlus α₀ cα cω g2) ∧
      deltaStarPlus α₀ cα cω g2 ∉ flipProjection α₀ cα cω g2 := by
  obtain ⟨hsub, hsup⟩ := flipProjection_calpha_pos_lowGain hα hg hcα hcω hlow
  have hQ : 0 < pumpQ α₀ cα g2 := by simp only [pumpQ]; positivity
  have hK : 0 < pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 := by
    have h1 : 2 * cα * α₀ < pumpQ α₀ cα g2 := by simp only [pumpQ]; nlinarith
    have h2 : 0 < pumpQ α₀ cα g2 + 2 * cα * α₀ := by positivity
    nlinarith [mul_pos (sub_pos.2 h1) h2]
  have hlt : deltaStarMinus α₀ cα cω g2 < deltaStarPlus α₀ cα cω g2 := by
    simp only [deltaStarMinus, deltaStarPlus]
    apply div_lt_div_of_pos_right _ (by positivity)
    have : 0 < √(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) :=
      mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hK)
    linarith
  refine ⟨⟨fun Δ hΔ => (hsup hΔ).le, fun b hb => (isLUB_Ioo hlt).2 fun Δ hΔ => hb (hsub hΔ)⟩,
    fun h => lt_irrefl _ (mem_Iio.mp (hsup h))⟩

/-- Rationalized form `Δ*₊ = (Q² − 4Sα₀²) / (2(√S √(Q² − 4c_α²α₀²) + c_ω Q))`, regular at
`c_α = 0`. -/
@[powerlib_foundation] theorem deltaStarPlus_eq_rat (hcα : cα ≠ 0) (hcω : 0 < cω)
    (hQ : 0 < pumpQ α₀ cα g2) (hK : 0 ≤ pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) :
    deltaStarPlus α₀ cα cω g2 =
      (pumpQ α₀ cα g2 ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2) /
        (2 * (√(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) +
          cω * pumpQ α₀ cα g2)) := by
  set S := cα ^ 2 + cω ^ 2 with hSdef
  set Q := pumpQ α₀ cα g2 with hQdef
  set K := Q ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 with hKdef
  have hS : 0 ≤ S := by positivity
  have hca2 : 0 < cα ^ 2 := by positivity
  have hden : 0 < √S * √K + cω * Q :=
    add_pos_of_nonneg_of_pos (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_pos hcω hQ)
  have hprod : (√S * √K - cω * Q) * (√S * √K + cω * Q) = cα ^ 2 * (Q ^ 2 - 4 * S * α₀ ^ 2) := by
    have : (√S * √K) ^ 2 = S * K := by rw [mul_pow, Real.sq_sqrt hS, Real.sq_sqrt hK]
    linear_combination this
  simp only [deltaStarPlus, ← hQdef, ← hSdef, ← hKdef]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination 2 * hprod

/-- The limit `c_α → 0` of the low-gain / `c_α < 0` supremum:
`Δ*₊ → |𝒢|²/(16c_ω) − 4c_ωα₀²/|𝒢|²`, the `c_α = 0` value. -/
@[powerlib_foundation] theorem tendsto_deltaStarPlus (hg : 0 < g2) (hcω : 0 < cω) :
    Tendsto (fun cα => deltaStarPlus α₀ cα cω g2) (𝓝[≠] 0)
      (𝓝 (g2 / (16 * cω) - 4 * cω * α₀ ^ 2 / g2)) := by
  set F : ℝ → ℝ := fun cα => (pumpQ α₀ cα g2 ^ 2 - 4 * (cα ^ 2 + cω ^ 2) * α₀ ^ 2) /
      (2 * (√(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) +
        cω * pumpQ α₀ cα g2)) with hFdef
  have hQ0 : pumpQ α₀ 0 g2 = g2 / 4 := by simp [pumpQ]
  have hcontQ : Continuous fun cα : ℝ => pumpQ α₀ cα g2 := by
    unfold pumpQ; fun_prop
  have hden0 : 2 * (√(0 ^ 2 + cω ^ 2) * √(pumpQ α₀ 0 g2 ^ 2 - 4 * 0 ^ 2 * α₀ ^ 2) +
      cω * pumpQ α₀ 0 g2) = cω * g2 := by
    rw [hQ0]
    have e1 : √((0 : ℝ) ^ 2 + cω ^ 2) = cω := by
      rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq hcω.le]
    have e2 : √((g2 / 4) ^ 2 - 4 * (0 : ℝ) ^ 2 * α₀ ^ 2) = g2 / 4 := by
      rw [show (g2 / 4) ^ 2 - 4 * (0 : ℝ) ^ 2 * α₀ ^ 2 = (g2 / 4) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [e1, e2]; ring
  have hcont : ContinuousAt F 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    rw [hden0]; positivity
  have hval : F 0 = g2 / (16 * cω) - 4 * cω * α₀ ^ 2 / g2 := by
    simp only [hFdef]
    rw [hden0, hQ0]
    field_simp; ring
  rw [← hval]
  have hQev : ∀ᶠ cα in 𝓝 (0 : ℝ), 0 < pumpQ α₀ cα g2 :=
    hcontQ.continuousAt.eventually (lt_mem_nhds (by beta_reduce; rw [hQ0]; positivity))
  have hKev : ∀ᶠ cα in 𝓝 (0 : ℝ), 0 < pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 := by
    have hc : Continuous fun cα : ℝ => pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 := by
      unfold pumpQ; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by beta_reduce; rw [hQ0]; simp; positivity))
  apply (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [nhdsWithin_le_nhds hQev, nhdsWithin_le_nhds hKev, self_mem_nhdsWithin]
    with cα hQ hK hne
  exact (deltaStarPlus_eq_rat hne hcω hQ hK.le).symm

/-- `Δ_sup` is continuous in `c_α` at `0`: the supremum of the `Δ`-projection,
`Δ*₊` for `c_α < 0` and for small `c_α > 0` (low gain), and
`|𝒢|²/(16c_ω) − 4c_ωα₀²/|𝒢|²` at `c_α = 0`, tends to the `c_α = 0` value. -/
@[powerlib_foundation] theorem continuousAt_sSup_flipProjection (hα : 0 < α₀) (hg : 0 < g2)
    (hcω : 0 < cω) :
    ContinuousAt (fun cα => sSup (flipProjection α₀ cα cω g2)) 0 := by
  have hzero : sSup (flipProjection α₀ 0 cω g2) = g2 / (16 * cω) - 4 * cω * α₀ ^ 2 / g2 := by
    rw [flipProjection_calpha_zero hα hg hcω, csSup_Iio]
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hzero]
  apply (tendsto_deltaStarPlus (α₀ := α₀) hg hcω).congr'
  have hQ0 : pumpQ α₀ 0 g2 = g2 / 4 := by simp [pumpQ]
  have hKev : ∀ᶠ cα in 𝓝 (0 : ℝ), 0 < pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 := by
    have hc : Continuous fun cα : ℝ => pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2 := by
      unfold pumpQ; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by beta_reduce; rw [hQ0]; simp; positivity))
  have hlowev : ∀ᶠ cα in 𝓝 (0 : ℝ), cα < 16 * cω ^ 2 * α₀ / g2 :=
    eventually_lt_nhds (show (0 : ℝ) < 16 * cω ^ 2 * α₀ / g2 by positivity)
  filter_upwards [nhdsWithin_le_nhds hKev, nhdsWithin_le_nhds hlowev, self_mem_nhdsWithin]
    with cα hK hsmall hne
  rcases lt_or_gt_of_ne (show cα ≠ 0 from hne) with hneg | hpos
  · have hca2 : 0 < cα ^ 2 := by nlinarith
    have hlt : deltaStarMinus α₀ cα cω g2 < deltaStarPlus α₀ cα cω g2 := by
      simp only [deltaStarMinus, deltaStarPlus]
      apply div_lt_div_of_pos_right _ (by positivity)
      have : 0 < √(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) :=
        mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hK)
      linarith
    rw [flipProjection_calpha_neg hα hg hneg hcω, csSup_Ioo hlt]
  · have hlow : g2 / (16 * cω ^ 2) ≤ α₀ / cα := by
      rw [div_le_div_iff₀ (by positivity) hpos]
      rw [lt_div_iff₀ hg] at hsmall
      nlinarith
    obtain ⟨hlub, -⟩ := flipProjection_calpha_pos_lowGain_isLUB hα hg hpos hcω hlow
    obtain ⟨hsub, -⟩ := flipProjection_calpha_pos_lowGain hα hg hpos hcω hlow
    have hlt : deltaStarMinus α₀ cα cω g2 < deltaStarPlus α₀ cα cω g2 := by
      simp only [deltaStarMinus, deltaStarPlus]
      apply div_lt_div_of_pos_right _ (by positivity)
      have : 0 < √(cα ^ 2 + cω ^ 2) * √(pumpQ α₀ cα g2 ^ 2 - 4 * cα ^ 2 * α₀ ^ 2) :=
        mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hK)
      linarith
    exact (hlub.csSup_eq ((nonempty_Ioo.2 hlt).mono hsub)).symm

/-! ## The two-circle criterion (§9) -/

/-- Leading-order threshold `y₀ = (δ̂₁⁰)² = 4α₀²/g2`. -/
def y0 (α₀ g2 : ℝ) : ℝ := 4 * α₀ ^ 2 / g2

/-- `Λ_α = 4α₀c_α/g2`. -/
def lamAlpha (α₀ cα g2 : ℝ) : ℝ := 4 * α₀ * cα / g2

/-- `Λ = 4α₀c_ω/g2`. -/
def lamOmega (α₀ cω g2 : ℝ) : ℝ := 4 * α₀ * cω / g2

/-- `R² = Λ_α² + Λ²`. -/
def rSq (α₀ cα cω g2 : ℝ) : ℝ := lamAlpha α₀ cα g2 ^ 2 + lamOmega α₀ cω g2 ^ 2

/-- Derivative of the tongue quadratic, `q'(y) = 2(c_α² + c_ω²) y − Q`. -/
@[powerlib_foundation] theorem hasDerivAt_tongue (y : ℝ) :
    HasDerivAt (tongue α₀ cα cω g2)
      (2 * (cα ^ 2 + cω ^ 2) * y - pumpQ α₀ cα g2) y := by
  have h := (((hasDerivAt_pow 2 y).const_mul (cα ^ 2 + cω ^ 2)).sub
    ((hasDerivAt_id y).const_mul (pumpQ α₀ cα g2))).add_const (α₀ ^ 2)
  convert h using 1
  · funext z; simp [tongue]
  · simp; ring

/-- `q(y₀)/α₀² = R² − 2Λ_α`. -/
@[powerlib_foundation] theorem tongue_y0 (hα : α₀ ≠ 0) (hg : g2 ≠ 0) :
    tongue α₀ cα cω g2 (y0 α₀ g2) / α₀ ^ 2 = rSq α₀ cα cω g2 - 2 * lamAlpha α₀ cα g2 := by
  simp only [tongue, pumpQ, y0, rSq, lamAlpha, lamOmega]
  field_simp
  ring

/-- `4 q'(y₀)/g2 = 2R² − 1 − 2Λ_α`. -/
@[powerlib_foundation] theorem tongue_deriv_y0 (hg : g2 ≠ 0) :
    4 / g2 * (2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2) =
      2 * rSq α₀ cα cω g2 - 1 - 2 * lamAlpha α₀ cα g2 := by
  simp only [pumpQ, y0, rSq, lamAlpha, lamOmega]
  field_simp
  ring

/-- `Λ* = 2(R − Λ_α)`. -/
@[powerlib_foundation] theorem lamStar_eq (hα : 0 < α₀) (hg : 0 < g2) :
    lamStar α₀ cα cω g2 = 2 * (√(rSq α₀ cα cω g2) - lamAlpha α₀ cα g2) := by
  have hR : √(rSq α₀ cα cω g2) = 4 * α₀ / g2 * √(cα ^ 2 + cω ^ 2) := by
    rw [show rSq α₀ cα cω g2 = (4 * α₀ / g2) ^ 2 * (cα ^ 2 + cω ^ 2) by
      simp only [rSq, lamAlpha, lamOmega]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hR, lamStar, lamAlpha]
  field_simp
  ring

/-- `Λ* < 1` iff `(Λ_α, Λ)` lies inside the parabola `Λ² < 1/4 + Λ_α`. -/
@[powerlib_foundation] theorem lamStar_lt_one_iff_parabola (hα : 0 < α₀) (hg : 0 < g2) :
    lamStar α₀ cα cω g2 < 1 ↔ lamOmega α₀ cω g2 ^ 2 < 1 / 4 + lamAlpha α₀ cα g2 := by
  rw [lamStar_eq hα hg]
  have hR0 := Real.sqrt_nonneg (rSq α₀ cα cω g2)
  have hR2 : √(rSq α₀ cα cω g2) ^ 2 = lamAlpha α₀ cα g2 ^ 2 + lamOmega α₀ cω g2 ^ 2 :=
    Real.sq_sqrt (by simp only [rSq]; positivity)
  constructor
  · intro h
    have h1 : √(rSq α₀ cα cω g2) < 1 / 2 + lamAlpha α₀ cα g2 := by linarith
    nlinarith
  · intro h
    have hpos : 0 < 1 / 2 + lamAlpha α₀ cα g2 := by nlinarith [sq_nonneg (lamOmega α₀ cω g2)]
    have : √(rSq α₀ cα cω g2) < 1 / 2 + lamAlpha α₀ cα g2 := by
      rw [show rSq α₀ cα cω g2 = lamAlpha α₀ cα g2 ^ 2 + lamOmega α₀ cω g2 ^ 2 from rfl,
        Real.sqrt_lt' hpos]
      nlinarith
    linarith

/-- The two-circle criterion: with two distinct roots, `y₋ < y₀` (i.e. `e(0) > 0`) iff
`R² < 2Λ_α` (`C₁`) or `2R² > 1 + 2Λ_α` (`C₂`). -/
@[powerlib_foundation] theorem yMinus_lt_y0_iff (hα : 0 < α₀) (hg : 0 < g2)
    (hS : 0 < cα ^ 2 + cω ^ 2) (hd : 0 < tongueDisc α₀ cα cω g2) :
    yMinus α₀ cα cω g2 < y0 α₀ g2 ↔
      rSq α₀ cα cω g2 < 2 * lamAlpha α₀ cα g2 ∨
        1 + 2 * lamAlpha α₀ cα g2 < 2 * rSq α₀ cα cω g2 := by
  have hsd : 0 < √(tongueDisc α₀ cα cω g2) := Real.sqrt_pos.mpr hd
  have hv1 : yMinus α₀ cα cω g2 < pumpQ α₀ cα g2 / (2 * (cα ^ 2 + cω ^ 2)) := by
    simp only [yMinus]; apply div_lt_div_of_pos_right _ (by positivity); linarith
  have hv2 : pumpQ α₀ cα g2 / (2 * (cα ^ 2 + cω ^ 2)) < yPlus α₀ cα cω g2 := by
    simp only [yPlus]; apply div_lt_div_of_pos_right _ (by positivity); linarith
  have hq : tongue α₀ cα cω g2 (y0 α₀ g2) < 0 ↔ rSq α₀ cα cω g2 < 2 * lamAlpha α₀ cα g2 := by
    have h := tongue_y0 (cα := cα) (cω := cω) hα.ne' hg.ne'
    have hα2 : 0 < α₀ ^ 2 := by positivity
    have he : tongue α₀ cα cω g2 (y0 α₀ g2) =
        α₀ ^ 2 * (rSq α₀ cα cω g2 - 2 * lamAlpha α₀ cα g2) := by
      rw [← h]; field_simp
    rw [he]
    constructor
    · intro h1; by_contra hc; push Not at hc; nlinarith
    · intro h1; nlinarith
  have hq' : 0 < 2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2 ↔
      1 + 2 * lamAlpha α₀ cα g2 < 2 * rSq α₀ cα cω g2 := by
    have h := tongue_deriv_y0 (α₀ := α₀) (cα := cα) (cω := cω) hg.ne'
    have h4 : 0 < 4 / g2 := by positivity
    constructor
    · intro h1
      have : 0 < 4 / g2 * (2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2) := by positivity
      linarith
    · intro h1
      have : 0 < 4 / g2 * (2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2) := by linarith
      exact (pos_iff_pos_of_mul_pos this).mp h4
  have hvert : 0 < 2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2 ↔
      pumpQ α₀ cα g2 / (2 * (cα ^ 2 + cω ^ 2)) < y0 α₀ g2 := by
    rw [div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  rw [← hq, ← hq', tongue_neg_iff hS, hvert]
  constructor
  · intro h
    by_cases h' : y0 α₀ g2 < yPlus α₀ cα cω g2
    · exact Or.inl ⟨h, h'⟩
    · push Not at h'
      exact Or.inr (by linarith)
  · rintro (⟨h, -⟩ | h)
    · exact h
    · linarith

/-- Family corollary: `c_α < 0` and `Λ* < 1` force every root of `q` above `y₀`, so the
corrected threshold exceeds the leading one, `e(0) < 0`, without exception. -/
@[powerlib_foundation] theorem y0_lt_root_of_calpha_neg (hα : 0 < α₀) (hg : 0 < g2)
    (hcα : cα < 0) (hstar : lamStar α₀ cα cω g2 < 1) {y : ℝ}
    (hy : tongue α₀ cα cω g2 y = 0) : y0 α₀ g2 < y := by
  have hpar := (lamStar_lt_one_iff_parabola hα hg).mp hstar
  have hLa : lamAlpha α₀ cα g2 < 0 := by
    simp only [lamAlpha]; apply div_neg_of_neg_of_pos _ hg; nlinarith
  have hLa' : -(1 / 4) < lamAlpha α₀ cα g2 := by nlinarith [sq_nonneg (lamOmega α₀ cω g2)]
  -- `q(y₀) > 0` and `q'(y₀) < 0`
  have hq0 : 0 < tongue α₀ cα cω g2 (y0 α₀ g2) := by
    have := tongue_y0 (cα := cα) (cω := cω) hα.ne' hg.ne'
    have hR : 0 ≤ rSq α₀ cα cω g2 := by simp only [rSq]; positivity
    have h1 : 0 < tongue α₀ cα cω g2 (y0 α₀ g2) / α₀ ^ 2 := by rw [this]; linarith
    exact (div_pos_iff_of_pos_right (by positivity)).mp h1
  have hd0 : 2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2 < 0 := by
    have := tongue_deriv_y0 (α₀ := α₀) (cα := cα) (cω := cω) hg.ne'
    have h1 : 4 / g2 * (2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2) < 0 := by
      rw [this]; simp only [rSq]; nlinarith
    by_contra hc
    push Not at hc
    have := mul_nonneg (show (0 : ℝ) ≤ 4 / g2 by positivity) hc
    linarith
  by_contra hle
  push Not at hle
  -- convexity: `q(y) ≥ q(y₀) + q'(y₀)(y − y₀) > 0` for `y ≤ y₀`
  have hconv : tongue α₀ cα cω g2 y = tongue α₀ cα cω g2 (y0 α₀ g2) +
      (2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2) * (y - y0 α₀ g2) +
      (cα ^ 2 + cω ^ 2) * (y - y0 α₀ g2) ^ 2 := by
    simp only [tongue]; ring
  have : 0 < tongue α₀ cα cω g2 y := by
    rw [hconv]
    have h1 : 0 ≤ (2 * (cα ^ 2 + cω ^ 2) * y0 α₀ g2 - pumpQ α₀ cα g2) * (y - y0 α₀ g2) :=
      mul_nonneg_of_nonpos_of_nonpos hd0.le (by linarith)
    have h2 : 0 ≤ (cα ^ 2 + cω ^ 2) * (y - y0 α₀ g2) ^ 2 := by positivity
    linarith
  linarith

/-- `t = y/y₀` is a root ratio iff `R² t² − (1 + 2Λ_α) t + 1 = 0`. -/
@[powerlib_foundation] theorem ratio_equation (hα : α₀ ≠ 0) (hg : g2 ≠ 0) (t : ℝ) :
    tongue α₀ cα cω g2 (t * y0 α₀ g2) = 0 ↔
      rSq α₀ cα cω g2 * t ^ 2 - (1 + 2 * lamAlpha α₀ cα g2) * t + 1 = 0 := by
  have hk : tongue α₀ cα cω g2 (t * y0 α₀ g2) =
      α₀ ^ 2 * (rSq α₀ cα cω g2 * t ^ 2 - (1 + 2 * lamAlpha α₀ cα g2) * t + 1) := by
    simp only [tongue, pumpQ, y0, rSq, lamAlpha, lamOmega]
    field_simp
  rw [hk]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hα)
  · intro h; rw [h, mul_zero]

/-- `e(0) = δ̂₁⁰/δ̂₁* − 1 > 0` iff `y₋ < y₀` (`y₋ > 0`). -/
@[powerlib_foundation] theorem e0_pos_iff {ym y : ℝ} (hym : 0 < ym) :
    0 < √y / √ym - 1 ↔ ym < y := by
  rw [sub_pos, one_lt_div (Real.sqrt_pos.mpr hym)]
  exact Real.sqrt_lt_sqrt_iff hym.le

end powerlib.ParametricResonance
