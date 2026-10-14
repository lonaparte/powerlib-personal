import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Closed-form current-limiting design formulas

All statements are algebraic or trigonometric facts (foundation) about the formulas of work-sync
T-current-limiting / T-gfm-control §1.10; none asserts stability of a converter.

Model boundary.
Static formulas only: a voltage source `E∠δ` behind `R + jX` against the grid `V∠0` (exit
angle), the grid-code power references, the adaptive virtual resistance and the HAC barrier
factor, each as a function of its arguments; no converter dynamics, mode switching or control
loop.

Source: work-sync `theory/T-current-limiting.md` §1.4–§1.7; `theory/T-gfm-control.md` §1.10.

Results.
* Exit angle of the current-limiting mode (T-current-limiting §1.6, Lyu et al. 2024). A voltage
  source `E∠δ` behind `R + jX` against the grid `V∠0` carries the current magnitude
  `|E e^{jδ} − V|/|R + jX|` (`currentMag`), and `currentMag_sq`:
  `|E e^{jδ} − V|² = E² + V² − 2 E V cos δ` (law of cosines).
  `deltaExit_current`: at `δ_exit = arccos((E² + V² − I_max²(R² + X²))/(2 E V))` the current
  equals `I_max`; `current_lt_iff`: on `[0, π]` the current is below `I_max` iff `δ < δ_exit`;
  `deltaExit_domain_iff`, `current_lt_of_large_limit`: the domain of the exit angle (Correction
  below).
* Grid-code power-reference rewrite (§1.5): `qStar` (`Q* = S_new` for `V_pu ≤ 0.5`,
  `2 S_new (1 − V_pu)` for `0.5 < V_pu ≤ 0.9`) satisfies `0 ≤ Q* ≤ S_new`, so
  `P* = √(S_new² − Q*²)` is real and `P*² + Q*² = S_new²` (`snew_circle`); the two segments
  agree at `V_pu = 0.5` (`qStar_half`). For the droop segment `V_pu > 0.9` the same holds
  under the premise `|Q_droop| ≤ S_new` (`pq_circle`).
* Adaptive virtual resistance (§1.4): `R_v = k (I_o − I_th)` above the threshold, `0` below,
  equals `k · max(I_o − I_th, 0)`; it is continuous (in particular at the threshold), and
  nonnegative and monotone for `k ≥ 0`.
* HAC barrier factor (§1.7): `Δ_μ = (1 − D_min) e^{β(‖i‖ − i_th)} /
  (1 + (1 − D_min)(e^{β(‖i‖ − i_th)} − 1))` takes values in `(0, 1)` for `0 < D_min < 1`,
  is strictly increasing in `‖i‖` for `β > 0`, and equals `1 − D_min` at `‖i‖ = i_th`.

Correction (T-current-limiting §1.6, exit angle): the note omits the domain premise of
`arccos`; it is `|E − V| ≤ I_max |Z| ≤ E + V` (`deltaExit_domain_iff`). Outside it there is no
exit angle: `current_lt_of_large_limit` (`I_max |Z| > E + V`: the limit is never reached).
-/

noncomputable section
namespace powerlib.Limiting

/-! ## Exit angle of the current-limiting mode -/

/-- Current magnitude of a source `E∠δ` behind `R + jX` against `V∠0`. -/
def currentMag (E V R X δ : ℝ) : ℝ :=
  ‖(E : ℂ) * Complex.exp (δ * Complex.I) - V‖ / ‖(⟨R, X⟩ : ℂ)‖

@[powerlib_foundation] theorem currentMag_sq_num (E V δ : ℝ) :
    ‖(E : ℂ) * Complex.exp (δ * Complex.I) - V‖ ^ 2 = E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((E : ℂ) * Complex.exp (δ * Complex.I) - V).re = E * Real.cos δ - V := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : ((E : ℂ) * Complex.exp (δ * Complex.I) - V).im = E * Real.sin δ := by
    simp [Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  have := Real.sin_sq_add_cos_sq δ
  linear_combination E ^ 2 * this

@[powerlib_foundation] theorem normZ_sq (R X : ℝ) : ‖(⟨R, X⟩ : ℂ)‖ ^ 2 = R ^ 2 + X ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Law of cosines for the current magnitude. -/
@[powerlib_foundation] theorem currentMag_sq (R X E V δ : ℝ) :
    currentMag E V R X δ ^ 2 = (E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ) / (R ^ 2 + X ^ 2) := by
  rw [currentMag, div_pow, currentMag_sq_num, normZ_sq]

/-- `δ_exit = arccos((E² + V² − I_max²(R² + X²))/(2 E V))`. -/
def deltaExit (E V R X Imax : ℝ) : ℝ :=
  Real.arccos ((E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V))

@[powerlib_foundation] private lemma currentMag_nonneg (E V R X δ : ℝ) :
    0 ≤ currentMag E V R X δ := div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- At `δ_exit` the current is exactly `I_max` (under the `arccos` domain premise). -/
@[powerlib_foundation] theorem deltaExit_current {E V R X Imax : ℝ} (hE : 0 < E) (hV : 0 < V)
    (hZ : 0 < R ^ 2 + X ^ 2) (hI : 0 ≤ Imax)
    (hdom1 : -1 ≤ (E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V))
    (hdom2 : (E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V) ≤ 1) :
    currentMag E V R X (deltaExit E V R X Imax) = Imax := by
  have hsq : currentMag E V R X (deltaExit E V R X Imax) ^ 2 = Imax ^ 2 := by
    rw [currentMag_sq, deltaExit, Real.cos_arccos hdom1 hdom2]
    field_simp
    ring
  exact (pow_left_inj₀ (currentMag_nonneg _ _ _ _ _) hI two_ne_zero).mp hsq

/-- The `arccos` argument lies in `[−1, 1]` iff `|E − V| ≤ I_max |Z| ≤ E + V`. -/
@[powerlib_foundation] theorem deltaExit_domain_iff {E V R X Imax : ℝ} (hE : 0 < E)
    (hV : 0 < V) :
    (-1 ≤ (E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V) ∧
        (E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V) ≤ 1) ↔
      (E - V) ^ 2 ≤ Imax ^ 2 * (R ^ 2 + X ^ 2) ∧ Imax ^ 2 * (R ^ 2 + X ^ 2) ≤ (E + V) ^ 2 := by
  have h2 : 0 < 2 * E * V := by positivity
  rw [le_div_iff₀ h2, div_le_iff₀ h2]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> nlinarith

/-- On `[0, π]` the current is below `I_max` iff `δ < δ_exit`. -/
@[powerlib_foundation] theorem current_lt_iff {E V R X Imax δ : ℝ} (hE : 0 < E) (hV : 0 < V)
    (hZ : 0 < R ^ 2 + X ^ 2) (hI : 0 ≤ Imax)
    (hdom1 : -1 ≤ (E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V))
    (hdom2 : (E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V) ≤ 1)
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    currentMag E V R X δ < Imax ↔ δ < deltaExit E V R X Imax := by
  set y := (E ^ 2 + V ^ 2 - Imax ^ 2 * (R ^ 2 + X ^ 2)) / (2 * E * V)
  have h2 : 0 < 2 * E * V := by positivity
  have hcur : currentMag E V R X δ < Imax ↔ y < Real.cos δ := by
    rw [← pow_lt_pow_iff_left₀ (currentMag_nonneg _ _ _ _ _) hI two_ne_zero,
      currentMag_sq, div_lt_iff₀ hZ, div_lt_iff₀ h2]
    constructor <;> intro h <;> nlinarith
  rw [hcur, deltaExit]
  constructor
  · intro h
    have := Real.arccos_lt_arccos hdom1 h (Real.cos_le_one δ)
    rwa [Real.arccos_cos hδ0 hδπ] at this
  · intro h
    have h' : Real.cos (Real.arccos y) < Real.cos δ :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hδ0 (Real.arccos_le_pi y) h
    rwa [Real.cos_arccos hdom1 hdom2] at h'

/-- If `I_max |Z| > E + V` the current limit is never reached: no exit angle exists. -/
@[powerlib_foundation] theorem current_lt_of_large_limit {E V R X Imax : ℝ} (hE : 0 ≤ E)
    (hV : 0 ≤ V) (hZ : 0 < R ^ 2 + X ^ 2) (hI : 0 ≤ Imax)
    (h : (E + V) ^ 2 < Imax ^ 2 * (R ^ 2 + X ^ 2)) (δ : ℝ) :
    currentMag E V R X δ < Imax := by
  rw [← pow_lt_pow_iff_left₀ (currentMag_nonneg _ _ _ _ _) hI two_ne_zero, currentMag_sq,
    div_lt_iff₀ hZ]
  have hc := Real.neg_one_le_cos δ
  have : E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ ≤ (E + V) ^ 2 := by nlinarith [mul_nonneg hE hV]
  linarith

/-! ## Grid-code `S_new` power-reference rewrite -/

/-- Real solution of `P*² + Q*² = S²` when `|Q*| ≤ S`. -/
@[powerlib_foundation] theorem pq_circle {S Q : ℝ} (hQ : |Q| ≤ S) :
    Real.sqrt (S ^ 2 - Q ^ 2) ^ 2 + Q ^ 2 = S ^ 2 := by
  have : Q ^ 2 ≤ S ^ 2 := sq_le_sq' (abs_le.mp hQ).1 (abs_le.mp hQ).2
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- Fault-mode reactive reference for `V_pu ≤ 0.9`. -/
def qStar (S Vpu : ℝ) : ℝ := if Vpu ≤ 1 / 2 then S else 2 * S * (1 - Vpu)

@[powerlib_foundation] theorem qStar_half (S : ℝ) : qStar S (1 / 2) = 2 * S * (1 - 1 / 2) := by
  simp [qStar]
  ring

@[powerlib_foundation] theorem qStar_bounds {S Vpu : ℝ} (hS : 0 ≤ S) (hV : Vpu ≤ 9 / 10) :
    0 ≤ qStar S Vpu ∧ qStar S Vpu ≤ S := by
  unfold qStar
  split_ifs with h
  · exact ⟨hS, le_rfl⟩
  · have h' := not_le.mp h
    constructor <;> nlinarith

/-- `S_new = V_pu S_n`, `P* = √(S_new² − Q*²)`: a real solution with `P*² + Q*² = S_new²`. -/
@[powerlib_foundation] theorem snew_circle {Sn Vpu : ℝ} (hSn : 0 ≤ Sn) (hV0 : 0 ≤ Vpu)
    (hV : Vpu ≤ 9 / 10) :
    let S := Vpu * Sn
    0 ≤ Real.sqrt (S ^ 2 - qStar S Vpu ^ 2) ∧
      Real.sqrt (S ^ 2 - qStar S Vpu ^ 2) ^ 2 + qStar S Vpu ^ 2 = S ^ 2 := by
  intro S
  have hS : 0 ≤ S := mul_nonneg hV0 hSn
  obtain ⟨h1, h2⟩ := qStar_bounds hS hV
  exact ⟨Real.sqrt_nonneg _, pq_circle (abs_le.mpr ⟨by linarith, h2⟩)⟩

/-! ## Adaptive virtual resistance -/

/-- `R_v = k (I_o − I_th)` for `I_o ≥ I_th`, `0` otherwise. -/
def adaptiveRv (k Ith Io : ℝ) : ℝ := if Ith ≤ Io then k * (Io - Ith) else 0

@[powerlib_foundation] theorem adaptiveRv_eq_max (k Ith Io : ℝ) :
    adaptiveRv k Ith Io = k * max (Io - Ith) 0 := by
  unfold adaptiveRv
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith), mul_zero]

/-- The adaptive virtual resistance is continuous (no jump at the threshold). -/
@[powerlib_foundation] theorem adaptiveRv_continuous (k Ith : ℝ) :
    Continuous (adaptiveRv k Ith) := by
  have : adaptiveRv k Ith = fun Io => k * max (Io - Ith) 0 :=
    funext (adaptiveRv_eq_max k Ith)
  rw [this]
  fun_prop

@[powerlib_foundation] theorem adaptiveRv_threshold (k Ith : ℝ) : adaptiveRv k Ith Ith = 0 := by
  simp [adaptiveRv]

@[powerlib_foundation] theorem adaptiveRv_nonneg {k : ℝ} (hk : 0 ≤ k) (Ith Io : ℝ) :
    0 ≤ adaptiveRv k Ith Io := by
  rw [adaptiveRv_eq_max]
  exact mul_nonneg hk (le_max_right _ _)

@[powerlib_foundation] theorem adaptiveRv_monotone {k : ℝ} (hk : 0 ≤ k) (Ith : ℝ) :
    Monotone (adaptiveRv k Ith) := by
  intro a b hab
  rw [adaptiveRv_eq_max, adaptiveRv_eq_max]
  exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hk

/-! ## HAC barrier factor -/

/-- `Δ_μ(‖i‖)` of the hybrid-angle-control barrier limiter. -/
def barrier (Dmin β ith x : ℝ) : ℝ :=
  (1 - Dmin) * Real.exp (β * (x - ith)) / (1 + (1 - Dmin) * (Real.exp (β * (x - ith)) - 1))

@[powerlib_foundation] theorem barrier_threshold (Dmin β ith : ℝ) :
    barrier Dmin β ith ith = 1 - Dmin := by
  simp [barrier]

@[powerlib_foundation] private lemma barrier_den_pos {Dmin : ℝ} (h0 : 0 < Dmin) (h1 : Dmin < 1)
    (u : ℝ) (hu : 0 < u) : 0 < 1 + (1 - Dmin) * (u - 1) := by
  nlinarith

@[powerlib_foundation] theorem barrier_mem {Dmin : ℝ} (h0 : 0 < Dmin) (h1 : Dmin < 1)
    (β ith x : ℝ) : 0 < barrier Dmin β ith x ∧ barrier Dmin β ith x < 1 := by
  have hu := Real.exp_pos (β * (x - ith))
  have hd := barrier_den_pos h0 h1 _ hu
  unfold barrier
  constructor
  · exact div_pos (mul_pos (by linarith) hu) hd
  · rw [div_lt_one hd]
    nlinarith

@[powerlib_foundation] theorem barrier_strictMono {Dmin β : ℝ} (h0 : 0 < Dmin) (h1 : Dmin < 1)
    (hβ : 0 < β) (ith : ℝ) : StrictMono (barrier Dmin β ith) := by
  intro x y hxy
  have hux := Real.exp_pos (β * (x - ith))
  have huy := Real.exp_pos (β * (y - ith))
  have hlt : Real.exp (β * (x - ith)) < Real.exp (β * (y - ith)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  unfold barrier
  rw [div_lt_div_iff₀ (barrier_den_pos h0 h1 _ hux) (barrier_den_pos h0 h1 _ huy)]
  have ha : 0 < (1 - Dmin) * Dmin := mul_pos (by linarith) h0
  nlinarith

end powerlib.Limiting
