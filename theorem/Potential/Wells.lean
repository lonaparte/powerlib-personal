import theorem.Attributes
import theorem.Potential.Barrier
import theorem.Potential.DoubleWell
import theorem.SpecialFunctions.Sinusoid
import theorem.Stochastic.FokkerPlanck
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # One-dimensional potential shapes: single well, double well, washboard

Critical points, minima, barriers, curvatures and Boltzmann weights of three scalar potentials
`V : ℝ → ℝ`: the quartic of `theorem/Potential/DoubleWell.lean` in its single-well and
double-well regimes, and the tilted washboard of `theorem/Potential/Barrier.lean`.

Scope.
* Algebraic and calculus facts about the potentials; no dynamics, noise model or engineering
  system is formalized here (no model family). The Boltzmann weight `e^{−V/D}` (`D > 0`) is only
  used as a function of `θ`.

Source: work-sync theory/T-potential-wells.md §1.1–1.5, §1.7 (assumptions on the tilted
washboard), theory/T-kramers-escape.md §1.4, §1.7–1.8, theory/T-nonlinear-phase-plane.md §1.4–1.5.

Results.
* Single well: the quartic `doubleWell a b` (`theorem/Potential/DoubleWell.lean`) with `a < 0 ≤ b`,
  i.e. `V = kθ²/2 + λθ⁴/4` with `k = −a > 0`, `λ = b ≥ 0`: unique critical point and strict global
  minimum at `0` (`doubleWell_single`); Gaussian normalization of the harmonic well
  `∫ e^{−kθ²/(2D)} dθ = √(2πD/k)` (Mathlib `integral_gaussian`; `singleWell_normalization`).
* Double well `V = −aθ²/2 + bθ⁴/4` (`a, b > 0`, `doubleWell`; its derivative, critical points,
  identity, minimum and barrier are in `theorem/Potential/DoubleWell.lean`):
  `V'' = −a` at `0`, `2a` at `±√(a/b)` (`doubleWell_curvatures`, `V'' = −a + 3bθ²` by
  `hasDerivAt_doubleWell_deriv`); for every `D > 0` the weight
  `e^{−V/D}` is
  strictly increasing on `(−∞, −r]`, decreasing on `[−r, 0]`, increasing on `[0, r]` and
  decreasing on `[r, ∞)` (`r = √(a/b)`): it stays bimodal (`doubleWell_weight_strictMonoOn_Iic`,
  `doubleWell_weight_strictAntiOn_Icc_neg`, `doubleWell_weight_strictMonoOn_Icc_pos`,
  `doubleWell_weight_strictAntiOn_Ici`; maxima `doubleWell_weight_max`, `doubleWell_weight_zero_lt`;
  for `V` itself `doubleWell_strictAntiOn_Iic`, `doubleWell_strictMonoOn_Icc_neg`,
  `doubleWell_strictAntiOn_Icc_pos`, `doubleWell_strictMonoOn_Ici`).
* Washboard `V = V₀ (−cos θ − αθ)` (`V₀ > 0`, `washboard`; defined as the washboard of
  `theorem/Potential/Barrier.lean` with `c = V₀α`, `A = V₀`, `φ = 0`, `washboard_eq`):
  `V' = V₀ (sin θ − α)` (`Barrier.hasDerivAt_washboard`); a critical point exists iff `|α| ≤ 1`
  (`washboard_critical_exists_iff`);
  `α > 1 ⇒ V' < 0` (`washboard_deriv_neg`); at `α = 1` the critical points are `π/2 + 2πk`, where
  also `V'' = 0` (well and barrier merge; `washboard_critical_merge`).
* `V(θ + 2πk) = V(θ) − 2πkV₀α` (`washboard_shift_int`): all wells are translates, with
  identical barrier heights (`washboard_barrier_translate`).
* For `|α| ≤ 1`, with `θ_min = arcsin α`, `θ_max = π − arcsin α`:
  `ΔV₊ = V₀[2√(1−α²) + α(2 arcsin α − π)]`, `ΔV₋ = V₀[2√(1−α²) + α(π + 2 arcsin α)]`
  (`washboard_barriers_eq`: the barriers `Barrier.barrierUp`, `Barrier.barrierDown` at
  `c = V₀α`, `A = V₀`, `φ = 0`, towards `π − arcsin α` and `−π − arcsin α`);
  `ΔV₊ = ΔV₋ = 2V₀` at `α = 0` and `ΔV₊ → 0`, `ΔV₋ → 2πV₀` at the fold
  (`Barrier.barrier_at_zero`, `Barrier.barrier_tendsto_fold`, `c → A⁻`).
* Curvatures `V''(θ_min) = V₀√(1−α²)`, `V''(θ_max) = −V₀√(1−α²)` and
  `√(V''(θ_min) |V''(θ_max)|) = V₀√(1−α²)` are `Barrier.washboard_curvatures` and
  `Barrier.washboard_prefactor` (`√(A² − c²) = V₀√(1−α²)`), so the Kramers prefactor is
  `2πγ / √(V''(θ_min) |V''(θ_max)|) = 2πγ / (V₀√(1−α²))`.
* For `α ≠ 0` the weight `e^{−V/D}` is not integrable on `ℝ`
  (`washboard_weight_not_integrable`, from `Stochastic.FP.gibbs_not_integrable`).

Potential shapes elsewhere: the washboard barrier with a phase shift, `V(θ) = −cθ − A cos(θ + φ)`,
its minimum over the two saddles and its fold asymptotics are in `theorem/Potential/Barrier.lean`;
the users of the double well are listed in `theorem/Potential/DoubleWell.lean`; the washboard
with `V₀ = A`, `α = B/A` is that of the Adler equation (`theorem/PhasePlane/Adler.lean`); the
fold normal form carries the potential `−μx + x³/3` (`theorem/NormalForm/Fold.lean`).

Corrections. (T-potential-wells §1.2–1.3):
* the double-well identity has the opposite sign: `V = +(a²/4b)[1 − (θ/√(a/b))²]² + const`
  (`doubleWell_identity`, `theorem/Potential/DoubleWell.lean`), not `−(a²/4b)[…]² + const`;
* "if `D ~ ΔV` the two peaks merge into one" is false: `e^{−V/D}` is bimodal for every `D > 0`
  (`doubleWell_weight_strictMonoOn_Iic`, `doubleWell_weight_strictAntiOn_Icc_neg`,
  `doubleWell_weight_strictMonoOn_Icc_pos`, `doubleWell_weight_strictAntiOn_Ici`);
* "for `0 < α < 1` the wells have different depths" is false: `V(θ + 2π) = V(θ) − 2πV₀α`, so every
  well has the same barriers `ΔV±` (`washboard_barrier_translate`).
-/

noncomputable section
namespace powerlib.Potential
open Set Filter Topology Real MeasureTheory

/-! ## Single well -/

/-- Single-well regime of the quartic (`a < 0 ≤ b`): `V = kθ²/2 + λθ⁴/4` with `k = −a > 0`,
`λ = b ≥ 0` (the harmonic well at `b = 0`, the anharmonic one at `b > 0`) has the unique critical
point `0` (`V' = −aθ + bθ³`, `hasDerivAt_doubleWell`), its strict global minimum. -/
@[tmio T, powerlib_foundation] theorem doubleWell_single {a b : ℝ} (ha : a < 0) (hb : 0 ≤ b)
    (θ : ℝ) : (-a * θ + b * θ ^ 3 = 0 ↔ θ = 0) ∧
      (θ ≠ 0 → doubleWell a b 0 < doubleWell a b θ) := by
  refine ⟨⟨fun h => ?_, fun h => by simp [h]⟩, fun hθ => ?_⟩
  · have : θ * (-a + b * θ ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · nlinarith [sq_nonneg θ]
  · simp only [doubleWell]
    have : 0 < θ ^ 2 := by positivity
    nlinarith [sq_nonneg (θ ^ 2)]

/-- Normalization of the Boltzmann weight of the harmonic well `kθ²/2 = doubleWell (−k) 0`:
`Z = √(2πD/k)`. -/
@[tmio T, powerlib_foundation] theorem singleWell_normalization {k D : ℝ} (hk : 0 < k) (hD : 0 < D) :
    ∫ θ, Real.exp (-doubleWell (-k) 0 θ / D) = √(2 * π * D / k) := by
  have h := integral_gaussian (k / (2 * D))
  have hfun : (fun θ => Real.exp (-doubleWell (-k) 0 θ / D)) =
      fun θ => Real.exp (-(k / (2 * D)) * θ ^ 2) := by
    funext θ; congr 1; simp only [doubleWell]; field_simp; ring
  rw [hfun, h]
  congr 1
  field_simp

/-! ## Double well -/

/-- Curvatures of the double well (`V'' = −a + 3bθ²`, `hasDerivAt_doubleWell_deriv`):
`V''(0) = −a` at the barrier top and `V''(±√(a/b)) = 2a` at the two wells. -/
@[tmio T, powerlib_foundation] theorem doubleWell_curvatures {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    -a + 3 * b * (0 : ℝ) ^ 2 = -a ∧ -a + 3 * b * √(a / b) ^ 2 = 2 * a ∧
      -a + 3 * b * (-√(a / b)) ^ 2 = 2 * a := by
  rw [neg_sq, Real.sq_sqrt (by positivity)]
  refine ⟨by ring, ?_, ?_⟩ <;> field_simp <;> ring

/-- The double well is strictly decreasing on `(−∞, −√(a/b)]`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_strictAntiOn_Iic {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : StrictAntiOn (doubleWell a b) (Iic (-√(a / b))) := by
  set r := √(a / b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : b * r ^ 2 = a := by rw [Real.sq_sqrt (by positivity)]; field_simp
  intro x hx y hy hxy
  have hx' : x ≤ -r := hx
  have hy' : y ≤ -r := hy
  have h := doubleWell_sub a b x y
  have hxy2 : y ^ 2 < x ^ 2 := by nlinarith
  have hy2 : r ^ 2 ≤ y ^ 2 := by nlinarith
  have : 0 < (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) := by
    apply mul_pos (by linarith)
    nlinarith
  linarith

/-- The double well is strictly increasing on `[−√(a/b), 0]`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_strictMonoOn_Icc_neg {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : StrictMonoOn (doubleWell a b) (Icc (-√(a / b)) 0) := by
  set r := √(a / b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : b * r ^ 2 = a := by rw [Real.sq_sqrt (by positivity)]; field_simp
  intro x hx y hy hxy
  have h := doubleWell_sub a b x y
  have hxy2 : y ^ 2 < x ^ 2 := by nlinarith [hx.1, hy.2]
  have hx2 : x ^ 2 ≤ r ^ 2 := by nlinarith [hx.1, hx.2]
  have : (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) < 0 := by
    apply mul_neg_of_pos_of_neg (by linarith)
    nlinarith
  linarith

/-- The double well is strictly decreasing on `[0, √(a/b)]`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_strictAntiOn_Icc_pos {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : StrictAntiOn (doubleWell a b) (Icc 0 √(a / b)) := by
  set r := √(a / b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : b * r ^ 2 = a := by rw [Real.sq_sqrt (by positivity)]; field_simp
  intro x hx y hy hxy
  have h := doubleWell_sub a b x y
  have hxy2 : x ^ 2 < y ^ 2 := by nlinarith [hx.1]
  have hy2 : y ^ 2 ≤ r ^ 2 := by nlinarith [hy.1, hy.2]
  have : (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) > 0 := by
    apply mul_pos_of_neg_of_neg (by linarith)
    nlinarith
  linarith

/-- The double well is strictly increasing on `[√(a/b), ∞)`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_strictMonoOn_Ici {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : StrictMonoOn (doubleWell a b) (Ici √(a / b)) := by
  set r := √(a / b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : b * r ^ 2 = a := by rw [Real.sq_sqrt (by positivity)]; field_simp
  intro x hx y hy hxy
  have hx' : r ≤ x := hx
  have h := doubleWell_sub a b x y
  have hxy2 : x ^ 2 < y ^ 2 := by nlinarith
  have hx2 : r ^ 2 ≤ x ^ 2 := by nlinarith
  have : (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) < 0 := by
    apply mul_neg_of_neg_of_pos (by linarith)
    nlinarith
  linarith

/-- The Boltzmann weight `v ↦ e^{−v/D}` (`D > 0`) is strictly decreasing in the energy. -/
@[tmio T, powerlib_foundation] private theorem strictAnti_exp_neg_div {D : ℝ} (hD : 0 < D) :
    StrictAnti (fun v : ℝ => Real.exp (-v / D)) := by
  intro u v huv
  apply Real.exp_lt_exp.mpr
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_right huv hD

/-- Correction (bimodality, first piece): for every `D > 0` the Boltzmann weight `e^{−V/D}` of the
double well is strictly increasing on `(−∞, −√(a/b)]`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_weight_strictMonoOn_Iic {a b D : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hD : 0 < D) :
    let p := fun θ => Real.exp (-doubleWell a b θ / D)
    StrictMonoOn p (Iic (-√(a / b))) := fun _ hx _ hy hxy =>
  strictAnti_exp_neg_div hD (doubleWell_strictAntiOn_Iic ha hb hx hy hxy)

/-- Correction (bimodality, second piece): for every `D > 0` the Boltzmann weight `e^{−V/D}` of
the double well is strictly decreasing on `[−√(a/b), 0]`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_weight_strictAntiOn_Icc_neg {a b D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    let p := fun θ => Real.exp (-doubleWell a b θ / D)
    StrictAntiOn p (Icc (-√(a / b)) 0) := fun _ hx _ hy hxy =>
  strictAnti_exp_neg_div hD (doubleWell_strictMonoOn_Icc_neg ha hb hx hy hxy)

/-- Correction (bimodality, third piece): for every `D > 0` the Boltzmann weight `e^{−V/D}` of the
double well is strictly increasing on `[0, √(a/b)]`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_weight_strictMonoOn_Icc_pos {a b D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    let p := fun θ => Real.exp (-doubleWell a b θ / D)
    StrictMonoOn p (Icc 0 √(a / b)) := fun _ hx _ hy hxy =>
  strictAnti_exp_neg_div hD (doubleWell_strictAntiOn_Icc_pos ha hb hx hy hxy)

/-- Correction (bimodality, fourth piece): for every `D > 0` the Boltzmann weight `e^{−V/D}` of
the double well is strictly decreasing on `[√(a/b), ∞)`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_weight_strictAntiOn_Ici {a b D : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hD : 0 < D) :
    let p := fun θ => Real.exp (-doubleWell a b θ / D)
    StrictAntiOn p (Ici √(a / b)) := fun _ hx _ hy hxy =>
  strictAnti_exp_neg_div hD (doubleWell_strictMonoOn_Ici ha hb hx hy hxy)

/-- For every `D > 0` the global maxima of the Boltzmann weight `e^{−V/D}` of the double well are
exactly `±√(a/b)`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_weight_max {a b D : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hD : 0 < D) :
    let p := fun θ => Real.exp (-doubleWell a b θ / D)
    ∀ θ, p θ ≤ p √(a / b) ∧ (p θ = p √(a / b) ↔ θ = √(a / b) ∨ θ = -√(a / b)) := by
  intro p θ
  have hanti := strictAnti_exp_neg_div hD
  have hrval : doubleWell a b √(a / b) = -a ^ 2 / (4 * b) :=
    (doubleWell_eq_min_iff ha hb √(a / b)).mpr (Or.inl rfl)
  refine ⟨hanti.antitone (by rw [hrval]; exact doubleWell_min hb θ), ?_⟩
  rw [hanti.injective.eq_iff, hrval]
  exact doubleWell_eq_min_iff ha hb θ

/-- For every `D > 0` the Boltzmann weight `e^{−V/D}` of the double well has a strict local minimum
at `0`, below its maxima at `±√(a/b)`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_weight_zero_lt {a b D : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hD : 0 < D) :
    let p := fun θ => Real.exp (-doubleWell a b θ / D)
    p 0 < p √(a / b) := by
  intro p
  apply strictAnti_exp_neg_div hD
  have hrval : doubleWell a b √(a / b) = -a ^ 2 / (4 * b) :=
    (doubleWell_eq_min_iff ha hb √(a / b)).mpr (Or.inl rfl)
  rw [hrval]
  have : doubleWell a b 0 = 0 := by simp [doubleWell]
  rw [this]
  have : 0 < a ^ 2 / (4 * b) := by positivity
  rw [neg_div]; linarith

/-! ## Washboard -/

/-- Tilted washboard `V₀ (−cos θ − αθ)`: the washboard `−cθ − A cos(θ + φ)` of
`theorem/Potential/Barrier.lean` with tilt `c = V₀α`, amplitude `A = V₀` and phase `φ = 0`. -/
def washboard (V₀ α θ : ℝ) : ℝ := Barrier.washboard (V₀ * α) V₀ 0 θ

@[tmio T, powerlib_foundation] theorem washboard_eq (V₀ α θ : ℝ) :
    washboard V₀ α θ = V₀ * (-Real.cos θ - α * θ) := by
  simp only [washboard, Barrier.washboard, add_zero]; ring

/-- A critical point of the washboard exists iff `|α| ≤ 1`: the zeros of the sinusoid
`α − sin θ` (`SpecialFunctions.exists_sinusoid_zero_iff`). -/
@[tmio T, powerlib_foundation] theorem washboard_critical_exists_iff {V₀ : ℝ} (hV : 0 < V₀) (α : ℝ) :
    (∃ θ, V₀ * (Real.sin θ - α) = 0) ↔ |α| ≤ 1 := by
  rw [← SpecialFunctions.exists_sinusoid_zero_iff (c := α) (φ := 0) one_pos]
  refine exists_congr fun θ => ?_
  rw [mul_eq_zero, or_iff_right hV.ne', add_zero, one_mul, sub_eq_zero, sub_eq_zero]
  exact eq_comm

/-- Strong tilt `α > 1`: the washboard is strictly decreasing (`V' < 0` everywhere). -/
@[tmio T, powerlib_foundation] theorem washboard_deriv_neg {V₀ α : ℝ} (hV : 0 < V₀) (hα : 1 < α) (θ : ℝ) :
    V₀ * (Real.sin θ - α) < 0 :=
  mul_neg_of_pos_of_neg hV (by linarith [Real.sin_le_one θ])

/-- Critical tilt `α = 1`: the critical points are `π/2 + 2πk`, where also `V'' = 0`. -/
@[tmio T, powerlib_foundation] theorem washboard_critical_merge {V₀ : ℝ} (hV : 0 < V₀) (θ : ℝ) :
    (V₀ * (Real.sin θ - 1) = 0 ↔ ∃ k : ℤ, θ = π / 2 + k * (2 * π)) ∧
      V₀ * Real.cos (π / 2) = 0 := by
  refine ⟨?_, by simp⟩
  rw [mul_eq_zero, or_iff_right hV.ne', sub_eq_zero, Real.sin_eq_one_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- The well and the barrier locations `arcsin α` and `π − arcsin α` both tend to `π/2`. -/
@[tmio T, powerlib_foundation] theorem washboard_extrema_tendsto :
    Tendsto Real.arcsin (𝓝[<] 1) (𝓝 (π / 2)) ∧
      Tendsto (fun α => π - Real.arcsin α) (𝓝[<] 1) (𝓝 (π / 2)) := by
  have h : Tendsto Real.arcsin (𝓝[<] 1) (𝓝 (π / 2)) := by
    rw [← Real.arcsin_one]
    exact Real.continuous_arcsin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨h, ?_⟩
  have := h.const_sub π
  convert this using 2; ring

/-- `V(θ + 2πk) = V(θ) − 2πkV₀α`: the tilted washboard is a periodic potential plus a ramp. -/
@[tmio T, powerlib_foundation] theorem washboard_shift_int (V₀ α θ : ℝ) (k : ℤ) :
    washboard V₀ α (θ + k * (2 * π)) = washboard V₀ α θ - k * (2 * π * V₀ * α) := by
  simp only [washboard_eq, Real.cos_add_int_mul_two_pi]; ring

/-- Correction: all wells are congruent — every barrier height is the same in every well. -/
@[tmio T, powerlib_foundation] theorem washboard_barrier_translate (V₀ α x y : ℝ) (k : ℤ) :
    washboard V₀ α (x + k * (2 * π)) - washboard V₀ α (y + k * (2 * π)) =
      washboard V₀ α x - washboard V₀ α y := by
  rw [washboard_shift_int, washboard_shift_int]; ring

/-- The barriers as functions of the tilt: at `c = V₀α`, `A = V₀`, `φ = 0` the barriers of
`theorem/Potential/Barrier.lean` towards `π − arcsin α` and `−π − arcsin α` are
`ΔV₊ = V₀[2√(1−α²) + α(2 arcsin α − π)]` (`Barrier.barrierUp`) and
`ΔV₋ = V₀[2√(1−α²) + α(π + 2 arcsin α)]` (`Barrier.barrierDown`). -/
@[tmio T, powerlib_foundation] theorem washboard_barriers_eq {V₀ : ℝ} (hV : 0 < V₀) (α : ℝ) :
    Barrier.barrierUp (V₀ * α) V₀ 0 = V₀ * (2 * √(1 - α ^ 2) + α * (2 * Real.arcsin α - π)) ∧
      Barrier.barrierDown (V₀ * α) V₀ 0 =
        V₀ * (2 * √(1 - α ^ 2) + α * (π + 2 * Real.arcsin α)) := by
  have hα : V₀ * α / V₀ = α := by field_simp
  have hs : √(V₀ ^ 2 - (V₀ * α) ^ 2) = V₀ * √(1 - α ^ 2) := by
    rw [show V₀ ^ 2 - (V₀ * α) ^ 2 = V₀ ^ 2 * (1 - α ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hV.le]
  rw [Barrier.barrierUp_eq hV, Barrier.barrierDown_eq hV, neg_div, hα, hs, Real.arccos_neg,
    Real.arccos_eq_pi_div_two_sub_arcsin]
  constructor <;> ring

/-- For `α ≠ 0` the Boltzmann weight `e^{−V/D}` of the tilted washboard is not integrable on `ℝ`
(`V ≤ V₀` on the half-line along the tilt; `Stochastic.FP.gibbs_not_integrable`). -/
@[tmio T, powerlib_foundation] theorem washboard_weight_not_integrable {V₀ α D : ℝ} (hV : 0 < V₀)
    (hα : α ≠ 0) (hD : 0 < D) :
    ¬ Integrable (fun θ => Real.exp (-washboard V₀ α θ / D)) := by
  -- on the half-line along the tilt `V ≤ V₀` (`Stochastic.FP.gibbs_not_integrable`)
  have key : ∀ θ, 0 ≤ α * θ → washboard V₀ α θ ≤ V₀ := fun θ h => by
    rw [washboard_eq]
    nlinarith [Real.neg_one_le_cos θ, mul_nonneg hV.le h]
  rcases lt_or_gt_of_ne hα with h | h
  · exact Stochastic.FP.gibbs_not_integrable hD measurableSet_Iic Real.volume_Iic
      fun θ hθ => key θ (mul_nonneg_of_nonpos_of_nonpos h.le hθ)
  · exact Stochastic.FP.gibbs_not_integrable hD measurableSet_Ici Real.volume_Ici
      fun θ hθ => key θ (mul_nonneg h.le hθ)

end powerlib.Potential
