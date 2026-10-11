import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # One-dimensional potential shapes: single well, double well, washboard

Foundation layer: algebraic and calculus facts about three scalar potentials `V : ℝ → ℝ`.
No dynamics, noise model or engineering system is formalized here; the Boltzmann weight
`e^{−V/D}` (`D > 0`) is only used as a function of `θ`.

Single well `V = kθ²/2` (`k > 0`) and the anharmonic well `kθ²/2 + λθ⁴/4` (`λ ≥ 0`): unique
critical point and strict global minimum at `0`; Gaussian normalization
`∫ e^{−kθ²/(2D)} dθ = √(2πD/k)` (Mathlib `integral_gaussian`).

Double well `V = −aθ²/2 + bθ⁴/4` (`a, b > 0`):
* critical points `0, ±√(a/b)`; `V'' = −a` at `0`, `2a` at `±√(a/b)`;
* identity `V = (a²/4b) [1 − bθ²/a]² − a²/4b` and global minimum value `−a²/4b`, attained
  exactly at `±√(a/b)`; barrier `V(0) − V(±√(a/b)) = a²/4b`;
* for every `D > 0` the weight `e^{−V/D}` is strictly increasing on `(−∞, −r]`, decreasing on
  `[−r, 0]`, increasing on `[0, r]` and decreasing on `[r, ∞)` (`r = √(a/b)`): it stays bimodal.

Washboard `V = V₀ (−cos θ − αθ)` (`V₀ > 0`):
* `V' = V₀ (sin θ − α)`; a critical point exists iff `|α| ≤ 1`; `α > 1 ⇒ V' < 0`;
  at `α = 1` the critical points are `π/2 + 2πk`, where also `V'' = 0` (well and barrier merge);
* `V(θ + 2π) = V(θ) − 2πV₀α`: all wells are translates, with identical barrier heights;
* for `|α| ≤ 1`, with `θ_min = arcsin α`, `θ_max = π − arcsin α`:
  `ΔV₊ = V₀[2√(1−α²) + α(2 arcsin α − π)]`, `ΔV₋ = V₀[2√(1−α²) + α(π + 2 arcsin α)]`,
  `ΔV₊ = ΔV₋ = 2V₀` at `α = 0`, `ΔV₊ → 0` and `ΔV₋ → 2πV₀` as `α → 1⁻`;
* curvatures `V''(θ_min) = V₀√(1−α²)`, `V''(θ_max) = −V₀√(1−α²)`, so the Kramers prefactor is
  `2πγ / √(V''(θ_min) |V''(θ_max)|) = 2πγ / (V₀√(1−α²))`;
* for `α ≠ 0` the weight `e^{−V/D}` is not integrable on `ℝ`.

Corrections (T-potential-wells §1.2–1.3):
* the double-well identity has the opposite sign: `V = +(a²/4b)[1 − (θ/√(a/b))²]² + const`
  (`doubleWell_identity`), not `−(a²/4b)[…]² + const`;
* "if `D ~ ΔV` the two peaks merge into one" is false: `e^{−V/D}` is bimodal for every `D > 0`
  (`doubleWell_weight_bimodal`);
* "for `0 < α < 1` the wells have different depths" is false: `V(θ + 2π) = V(θ) − 2πV₀α`, so every
  well has the same barriers `ΔV±` (`washboard_barrier_translate`).

Source: work-sync theory/T-potential-wells.md §1.1–1.5, §1.7 (assumptions on the tilted
washboard), theory/T-kramers-escape.md §1.4, §1.7–1.8, theory/T-nonlinear-phase-plane.md §1.4–1.5.
-/

noncomputable section
namespace powerlib.Potential
open Set Filter Topology Real MeasureTheory

/-! ## Single well -/

/-- Harmonic single well `kθ²/2`. -/
def singleWell (k θ : ℝ) : ℝ := k * θ ^ 2 / 2

/-- Anharmonic single well `kθ²/2 + λθ⁴/4`. -/
def anharmonicWell (k lam θ : ℝ) : ℝ := k * θ ^ 2 / 2 + lam * θ ^ 4 / 4

@[powerlib_foundation] theorem singleWell_min {k : ℝ} (hk : 0 < k) (θ : ℝ) :
    singleWell k 0 ≤ singleWell k θ ∧ (singleWell k θ = singleWell k 0 ↔ θ = 0) := by
  simp only [singleWell]
  refine ⟨by nlinarith [sq_nonneg θ], ?_⟩
  constructor
  · intro h
    have : θ ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · rintro rfl; simp

@[powerlib_foundation] theorem hasDerivAt_anharmonicWell (k lam θ : ℝ) :
    HasDerivAt (anharmonicWell k lam) (k * θ + lam * θ ^ 3) θ := by
  have h := (((hasDerivAt_pow 2 θ).const_mul k).div_const 2).add
    (((hasDerivAt_pow 4 θ).const_mul lam).div_const 4)
  unfold anharmonicWell
  convert h using 1
  push_cast; ring

/-- The anharmonic single well (`k > 0`, `λ ≥ 0`) has the unique critical point `0`, which is
its strict global minimum. -/
@[powerlib_foundation] theorem anharmonicWell_unique_min {k lam : ℝ} (hk : 0 < k) (hl : 0 ≤ lam) :
    (∀ θ, k * θ + lam * θ ^ 3 = 0 ↔ θ = 0) ∧ ∀ θ, θ ≠ 0 → anharmonicWell k lam 0 < anharmonicWell k lam θ := by
  refine ⟨fun θ => ⟨fun h => ?_, fun h => by simp [h]⟩, fun θ hθ => ?_⟩
  · have : θ * (k + lam * θ ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · nlinarith [sq_nonneg θ]
  · simp only [anharmonicWell]
    have : 0 < θ ^ 2 := by positivity
    nlinarith [sq_nonneg (θ ^ 2)]

/-- Normalization of the Boltzmann weight of the harmonic well: `Z = √(2πD/k)`. -/
@[powerlib_foundation] theorem singleWell_normalization {k D : ℝ} (hk : 0 < k) (hD : 0 < D) :
    ∫ θ, Real.exp (-singleWell k θ / D) = √(2 * π * D / k) := by
  have h := integral_gaussian (k / (2 * D))
  have hfun : (fun θ => Real.exp (-singleWell k θ / D)) = fun θ => Real.exp (-(k / (2 * D)) * θ ^ 2) := by
    funext θ; congr 1; simp only [singleWell]; field_simp
  rw [hfun, h]
  congr 1
  field_simp

/-! ## Double well -/

/-- Symmetric double well `−aθ²/2 + bθ⁴/4`. -/
def doubleWell (a b θ : ℝ) : ℝ := -a * θ ^ 2 / 2 + b * θ ^ 4 / 4

@[powerlib_foundation] theorem hasDerivAt_doubleWell (a b θ : ℝ) :
    HasDerivAt (doubleWell a b) (-a * θ + b * θ ^ 3) θ := by
  have h := (((hasDerivAt_pow 2 θ).const_mul (-a)).div_const 2).add
    (((hasDerivAt_pow 4 θ).const_mul b).div_const 4)
  unfold doubleWell
  convert h using 1
  push_cast; ring

/-- Correction: `V = (a²/4b)[1 − bθ²/a]² − a²/4b` (positive sign in front of the square). -/
@[powerlib_foundation] theorem doubleWell_identity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (θ : ℝ) :
    doubleWell a b θ = a ^ 2 / (4 * b) * (1 - b * θ ^ 2 / a) ^ 2 - a ^ 2 / (4 * b) := by
  simp only [doubleWell]; field_simp; ring

@[powerlib_foundation] theorem doubleWell_critical_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (θ : ℝ) :
    -a * θ + b * θ ^ 3 = 0 ↔ θ = 0 ∨ θ = √(a / b) ∨ θ = -√(a / b) := by
  have hr : √(a / b) ^ 2 = a / b := Real.sq_sqrt (by positivity)
  constructor
  · intro h
    have h' : θ * (θ ^ 2 - a / b) = 0 := by field_simp; linarith
    rcases mul_eq_zero.mp h' with h | h
    · exact Or.inl h
    · right
      have : θ ^ 2 = √(a / b) ^ 2 := by rw [hr]; linarith
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro (rfl | rfl | rfl)
    · ring
    · have : √(a / b) ^ 3 = a / b * √(a / b) := by rw [pow_succ, hr]
      rw [this]; field_simp; ring
    · have : (-√(a / b)) ^ 3 = -(a / b * √(a / b)) := by
        rw [show (-√(a / b)) ^ 3 = -(√(a / b) ^ 2 * √(a / b)) by ring, hr]
      rw [this]; field_simp; ring

@[powerlib_foundation] theorem doubleWell_curvatures {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (-a + 3 * b * (0 : ℝ) ^ 2 = -a) ∧ (-a + 3 * b * √(a / b) ^ 2 = 2 * a) ∧
      (-a + 3 * b * (-√(a / b)) ^ 2 = 2 * a) := by
  have hr : √(a / b) ^ 2 = a / b := Real.sq_sqrt (by positivity)
  refine ⟨by ring, ?_, ?_⟩
  · rw [hr]; field_simp; ring
  · rw [neg_sq, hr]; field_simp; ring

/-- Global minimum value `−a²/4b`, attained exactly at `±√(a/b)`. -/
@[powerlib_foundation] theorem doubleWell_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (θ : ℝ) :
    -a ^ 2 / (4 * b) ≤ doubleWell a b θ ∧
      (doubleWell a b θ = -a ^ 2 / (4 * b) ↔ θ = √(a / b) ∨ θ = -√(a / b)) := by
  have hr : √(a / b) ^ 2 = a / b := Real.sq_sqrt (by positivity)
  have hid := doubleWell_identity ha.ne' hb.ne' θ
  have hc : 0 < a ^ 2 / (4 * b) := by positivity
  have hn : -a ^ 2 / (4 * b) = -(a ^ 2 / (4 * b)) := neg_div _ _
  refine ⟨by rw [hid, hn]; nlinarith [mul_nonneg hc.le (sq_nonneg (1 - b * θ ^ 2 / a))], ?_⟩
  rw [hid]
  constructor
  · intro h
    have hsq : (1 - b * θ ^ 2 / a) ^ 2 = 0 := by
      have : a ^ 2 / (4 * b) * (1 - b * θ ^ 2 / a) ^ 2 = 0 := by
        linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    have h1 : 1 - b * θ ^ 2 / a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    have hθ : θ ^ 2 = √(a / b) ^ 2 := by rw [hr]; field_simp at h1 ⊢; linarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hθ
  · rintro (rfl | rfl) <;>
      simp only [neg_sq, hr] <;> field_simp <;> ring

/-- Barrier of the double well: `V(0) − V(±√(a/b)) = a²/4b`. -/
@[powerlib_foundation] theorem doubleWell_barrier {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    doubleWell a b 0 - doubleWell a b √(a / b) = a ^ 2 / (4 * b) ∧
      doubleWell a b 0 - doubleWell a b (-√(a / b)) = a ^ 2 / (4 * b) := by
  have h1 := ((doubleWell_min ha hb √(a / b)).2).mpr (Or.inl rfl)
  have h2 := ((doubleWell_min ha hb (-√(a / b))).2).mpr (Or.inr rfl)
  have h0 : doubleWell a b 0 = 0 := by simp [doubleWell]
  rw [h1, h2, h0]
  constructor <;> ring

@[powerlib_foundation] theorem doubleWell_sub (a b x y : ℝ) :
    doubleWell a b x - doubleWell a b y = (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) := by
  simp only [doubleWell]; ring

/-- Monotonicity pattern of the double well on the four intervals cut by `−r, 0, r`. -/
@[powerlib_foundation] theorem doubleWell_monotone {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictAntiOn (doubleWell a b) (Iic (-√(a / b))) ∧
      StrictMonoOn (doubleWell a b) (Icc (-√(a / b)) 0) ∧
      StrictAntiOn (doubleWell a b) (Icc 0 √(a / b)) ∧
      StrictMonoOn (doubleWell a b) (Ici √(a / b)) := by
  set r := √(a / b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : b * r ^ 2 = a := by rw [Real.sq_sqrt (by positivity)]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ≤ -r := hx
    have hy' : y ≤ -r := hy
    have h := doubleWell_sub a b x y
    have hxy2 : y ^ 2 < x ^ 2 := by nlinarith
    have hy2 : r ^ 2 ≤ y ^ 2 := by nlinarith
    have : 0 < (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) := by
      apply mul_pos (by linarith)
      nlinarith
    linarith
  · intro x hx y hy hxy
    have h := doubleWell_sub a b x y
    have hxy2 : y ^ 2 < x ^ 2 := by nlinarith [hx.1, hy.2]
    have hx2 : x ^ 2 ≤ r ^ 2 := by nlinarith [hx.1, hx.2]
    have : (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) < 0 := by
      apply mul_neg_of_pos_of_neg (by linarith)
      nlinarith
    linarith
  · intro x hx y hy hxy
    have h := doubleWell_sub a b x y
    have hxy2 : x ^ 2 < y ^ 2 := by nlinarith [hx.1]
    have hy2 : y ^ 2 ≤ r ^ 2 := by nlinarith [hy.1, hy.2]
    have : (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) > 0 := by
      apply mul_pos_of_neg_of_neg (by linarith)
      nlinarith
    linarith
  · intro x hx y hy hxy
    have hx' : r ≤ x := hx
    have h := doubleWell_sub a b x y
    have hxy2 : x ^ 2 < y ^ 2 := by nlinarith
    have hx2 : r ^ 2 ≤ x ^ 2 := by nlinarith
    have : (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) < 0 := by
      apply mul_neg_of_neg_of_pos (by linarith)
      nlinarith
    linarith

/-- Correction: for every temperature `D > 0` the Boltzmann weight `e^{−V/D}` of the double well
stays bimodal — increasing, decreasing, increasing, decreasing on the four intervals, with
global maxima exactly at `±√(a/b)` and a strict local minimum at `0`. -/
@[powerlib_foundation] theorem doubleWell_weight_bimodal {a b D : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hD : 0 < D) :
    let p := fun θ => Real.exp (-doubleWell a b θ / D)
    StrictMonoOn p (Iic (-√(a / b))) ∧ StrictAntiOn p (Icc (-√(a / b)) 0) ∧
      StrictMonoOn p (Icc 0 √(a / b)) ∧ StrictAntiOn p (Ici √(a / b)) ∧
      (∀ θ, p θ ≤ p √(a / b) ∧ (p θ = p √(a / b) ↔ θ = √(a / b) ∨ θ = -√(a / b))) ∧
      p 0 < p √(a / b) := by
  intro p
  obtain ⟨h1, h2, h3, h4⟩ := doubleWell_monotone ha hb
  have hanti : StrictAnti (fun v : ℝ => Real.exp (-v / D)) := by
    intro u v huv
    apply Real.exp_lt_exp.mpr
    rw [neg_div, neg_div, neg_lt_neg_iff]
    exact div_lt_div_of_pos_right huv hD
  have hmin := doubleWell_min ha hb
  have hrval : doubleWell a b √(a / b) = -a ^ 2 / (4 * b) := (hmin √(a / b)).2.mpr (Or.inl rfl)
  refine ⟨fun x hx y hy hxy => hanti (h1 hx hy hxy), fun x hx y hy hxy => hanti (h2 hx hy hxy),
    fun x hx y hy hxy => hanti (h3 hx hy hxy), fun x hx y hy hxy => hanti (h4 hx hy hxy), ?_, ?_⟩
  · intro θ
    refine ⟨hanti.antitone (by rw [hrval]; exact (hmin θ).1), ?_⟩
    rw [hanti.injective.eq_iff, hrval]
    exact (hmin θ).2
  · apply hanti
    rw [hrval]
    have : doubleWell a b 0 = 0 := by simp [doubleWell]
    rw [this]
    have : 0 < a ^ 2 / (4 * b) := by positivity
    rw [neg_div]; linarith

/-! ## Washboard -/

/-- Tilted washboard `V₀ (−cos θ − αθ)`. -/
def washboard (V₀ α θ : ℝ) : ℝ := V₀ * (-Real.cos θ - α * θ)

@[powerlib_foundation] theorem hasDerivAt_washboard (V₀ α θ : ℝ) :
    HasDerivAt (washboard V₀ α) (V₀ * (Real.sin θ - α)) θ := by
  have h : HasDerivAt (fun y => V₀ * (-Real.cos y - α * y)) (V₀ * (-(-Real.sin θ) - α * 1)) θ :=
    ((Real.hasDerivAt_cos θ).neg.sub ((hasDerivAt_id' θ).const_mul α)).const_mul V₀
  unfold washboard
  convert h using 1
  ring

@[powerlib_foundation] theorem hasDerivAt_washboard_deriv (V₀ α θ : ℝ) :
    HasDerivAt (fun θ => V₀ * (Real.sin θ - α)) (V₀ * Real.cos θ) θ := by
  simpa using ((Real.hasDerivAt_sin θ).sub_const α).const_mul V₀

/-- A critical point of the washboard exists iff `|α| ≤ 1`. -/
@[powerlib_foundation] theorem washboard_critical_exists_iff {V₀ : ℝ} (hV : 0 < V₀) (α : ℝ) :
    (∃ θ, V₀ * (Real.sin θ - α) = 0) ↔ |α| ≤ 1 := by
  constructor
  · rintro ⟨θ, h⟩
    have : Real.sin θ = α := by
      have := (mul_eq_zero.mp h).resolve_left hV.ne'; linarith
    rw [← this]; exact Real.abs_sin_le_one θ
  · intro h
    rw [abs_le] at h
    exact ⟨Real.arcsin α, by rw [Real.sin_arcsin h.1 h.2]; ring⟩

/-- Strong tilt `α > 1`: the washboard is strictly decreasing (`V' < 0` everywhere). -/
@[powerlib_foundation] theorem washboard_deriv_neg {V₀ α : ℝ} (hV : 0 < V₀) (hα : 1 < α) (θ : ℝ) :
    V₀ * (Real.sin θ - α) < 0 :=
  mul_neg_of_pos_of_neg hV (by linarith [Real.sin_le_one θ])

/-- Critical tilt `α = 1`: the critical points are `π/2 + 2πk`, where also `V'' = 0`. -/
@[powerlib_foundation] theorem washboard_critical_merge {V₀ : ℝ} (hV : 0 < V₀) (θ : ℝ) :
    (V₀ * (Real.sin θ - 1) = 0 ↔ ∃ k : ℤ, θ = π / 2 + k * (2 * π)) ∧
      V₀ * Real.cos (π / 2) = 0 := by
  refine ⟨?_, by simp⟩
  rw [mul_eq_zero, or_iff_right hV.ne', sub_eq_zero, Real.sin_eq_one_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- The well and the barrier locations `arcsin α` and `π − arcsin α` both tend to `π/2`. -/
@[powerlib_foundation] theorem washboard_extrema_tendsto :
    Tendsto Real.arcsin (𝓝[<] 1) (𝓝 (π / 2)) ∧
      Tendsto (fun α => π - Real.arcsin α) (𝓝[<] 1) (𝓝 (π / 2)) := by
  have h : Tendsto Real.arcsin (𝓝[<] 1) (𝓝 (π / 2)) := by
    rw [← Real.arcsin_one]
    exact Real.continuous_arcsin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨h, ?_⟩
  have := h.const_sub π
  convert this using 2; ring

/-- `V(θ + 2π) = V(θ) − 2πV₀α`: the tilted washboard is a periodic potential plus a ramp. -/
@[powerlib_foundation] theorem washboard_shift (V₀ α θ : ℝ) :
    washboard V₀ α (θ + 2 * π) = washboard V₀ α θ - 2 * π * V₀ * α := by
  simp only [washboard, Real.cos_add_two_pi]; ring

@[powerlib_foundation] theorem washboard_shift_int (V₀ α θ : ℝ) (k : ℤ) :
    washboard V₀ α (θ + k * (2 * π)) = washboard V₀ α θ - k * (2 * π * V₀ * α) := by
  simp only [washboard, Real.cos_add_int_mul_two_pi]; ring

/-- Correction: all wells are congruent — every barrier height is the same in every well. -/
@[powerlib_foundation] theorem washboard_barrier_translate (V₀ α x y : ℝ) (k : ℤ) :
    washboard V₀ α (x + k * (2 * π)) - washboard V₀ α (y + k * (2 * π)) =
      washboard V₀ α x - washboard V₀ α y := by
  rw [washboard_shift_int, washboard_shift_int]; ring

/-- Forward barrier `ΔV₊ = V(π − arcsin α) − V(arcsin α)`. -/
@[powerlib_foundation] theorem washboard_barrier_forward {V₀ α : ℝ} :
    washboard V₀ α (π - Real.arcsin α) - washboard V₀ α (Real.arcsin α) =
      V₀ * (2 * √(1 - α ^ 2) + α * (2 * Real.arcsin α - π)) := by
  simp only [washboard, Real.cos_pi_sub, Real.cos_arcsin]; ring

/-- Backward barrier `ΔV₋ = V(π − arcsin α − 2π) − V(arcsin α)`. -/
@[powerlib_foundation] theorem washboard_barrier_backward {V₀ α : ℝ} :
    washboard V₀ α (π - Real.arcsin α - 2 * π) - washboard V₀ α (Real.arcsin α) =
      V₀ * (2 * √(1 - α ^ 2) + α * (π + 2 * Real.arcsin α)) := by
  have h := washboard_shift V₀ α (π - Real.arcsin α - 2 * π)
  rw [sub_add_cancel] at h
  have hf := washboard_barrier_forward (V₀ := V₀) (α := α)
  linarith

/-- Closed-form barriers as functions of the tilt. -/
def barrierForward (V₀ α : ℝ) : ℝ := V₀ * (2 * √(1 - α ^ 2) + α * (2 * Real.arcsin α - π))
def barrierBackward (V₀ α : ℝ) : ℝ := V₀ * (2 * √(1 - α ^ 2) + α * (π + 2 * Real.arcsin α))

@[powerlib_foundation] theorem barrier_at_zero (V₀ : ℝ) :
    barrierForward V₀ 0 = 2 * V₀ ∧ barrierBackward V₀ 0 = 2 * V₀ := by
  refine ⟨?_, ?_⟩ <;>
    simp only [barrierForward, barrierBackward, Real.arcsin_zero, zero_mul, add_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Real.sqrt_one] <;> ring

/-- As `α → 1⁻` the forward barrier vanishes and the backward barrier tends to `2πV₀`. -/
@[powerlib_foundation] theorem barrier_tendsto_one (V₀ : ℝ) :
    Tendsto (barrierForward V₀) (𝓝[<] 1) (𝓝 0) ∧
      Tendsto (barrierBackward V₀) (𝓝[<] 1) (𝓝 (2 * π * V₀)) := by
  have hc : Continuous fun α : ℝ => √(1 - α ^ 2) := by fun_prop
  have hcF : Continuous (barrierForward V₀) := by
    unfold barrierForward; have := Real.continuous_arcsin; fun_prop
  have hcB : Continuous (barrierBackward V₀) := by
    unfold barrierBackward; have := Real.continuous_arcsin; fun_prop
  have hF1 : barrierForward V₀ 1 = 0 := by
    simp only [barrierForward, Real.arcsin_one, one_pow, sub_self, Real.sqrt_zero]; ring
  have hB1 : barrierBackward V₀ 1 = 2 * π * V₀ := by
    simp only [barrierBackward, Real.arcsin_one, one_pow, sub_self, Real.sqrt_zero]; ring
  refine ⟨?_, ?_⟩
  · rw [← hF1]; exact hcF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · rw [← hB1]; exact hcB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- Curvatures at the well and the barrier: `V''(arcsin α) = V₀√(1−α²)`,
`V''(π − arcsin α) = −V₀√(1−α²)`. -/
@[powerlib_foundation] theorem washboard_curvatures (V₀ α : ℝ) :
    V₀ * Real.cos (Real.arcsin α) = V₀ * √(1 - α ^ 2) ∧
      V₀ * Real.cos (π - Real.arcsin α) = -(V₀ * √(1 - α ^ 2)) := by
  rw [Real.cos_pi_sub, Real.cos_arcsin]; constructor <;> ring

/-- Kramers prefactor algebra: `√(V''(θ_min) |V''(θ_max)|) = V₀√(1−α²)`. -/
@[powerlib_foundation] theorem washboard_prefactor {V₀ : ℝ} (hV : 0 ≤ V₀) (α : ℝ) :
    √(V₀ * Real.cos (Real.arcsin α) * |V₀ * Real.cos (π - Real.arcsin α)|) =
      V₀ * √(1 - α ^ 2) := by
  obtain ⟨h1, h2⟩ := washboard_curvatures V₀ α
  rw [h1, h2, abs_neg, abs_of_nonneg (by positivity), ← sq, Real.sqrt_sq (by positivity)]

@[powerlib_foundation] theorem washboard_kramers_prefactor {V₀ γ : ℝ} (hV : 0 ≤ V₀) (α : ℝ) :
    2 * π * γ / √(V₀ * Real.cos (Real.arcsin α) * |V₀ * Real.cos (π - Real.arcsin α)|) =
      2 * π * γ / (V₀ * √(1 - α ^ 2)) := by
  rw [washboard_prefactor hV]

/-- For `α ≠ 0` the Boltzmann weight `e^{−V/D}` of the tilted washboard is not integrable on `ℝ`. -/
@[powerlib_foundation] theorem washboard_weight_not_integrable {V₀ α D : ℝ} (hV : 0 < V₀)
    (hα : α ≠ 0) (hD : 0 < D) :
    ¬ Integrable (fun θ => Real.exp (-washboard V₀ α θ / D)) := by
  intro hint
  set c := Real.exp (-V₀ / D)
  have hc : 0 < c := Real.exp_pos _
  -- on the half-line along the tilt the weight is at least `c`
  have key : ∀ s : Set ℝ, MeasurableSet s → volume s = ⊤ →
      (∀ θ ∈ s, 0 ≤ α * θ) → False := by
    intro s hs hvol hpos
    have hon : IntegrableOn (fun θ => Real.exp (-washboard V₀ α θ / D)) s := hint.integrableOn
    have hconst : IntegrableOn (fun _ : ℝ => c) s := by
      refine Integrable.mono' hon aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos hc]
      apply Real.exp_le_exp.mpr
      have hcos := Real.neg_one_le_cos θ
      have := hpos θ hθ
      rw [div_le_div_iff_of_pos_right hD]
      simp only [washboard]
      nlinarith
    rw [integrableOn_const_iff] at hconst
    rcases hconst with h | h
    · simp [hc.ne'] at h
    · rw [hvol] at h; exact lt_irrefl _ h
  rcases lt_or_gt_of_ne hα with h | h
  · exact key (Iic 0) measurableSet_Iic Real.volume_Iic
      (fun θ hθ => mul_nonneg_of_nonpos_of_nonpos h.le hθ)
  · exact key (Ici 0) measurableSet_Ici Real.volume_Ici
      (fun θ hθ => mul_nonneg h.le hθ)

end powerlib.Potential
