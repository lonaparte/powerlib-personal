import theorem.CurrentControl.PILoop

/-! # PCC-voltage feedforward with a dedicated low-pass filter

Foundation part (T-voltage-feedforward §1.3–§1.4, §2.2).
* `lpf_transfer`: the first-order filter `τ dṽ/dt = v − ṽ` as an LTI realization has transfer
  `1/(1 + s τ)`.
* `residual_transfer`: the net uncancelled disturbance `v − ṽ` that enters the IN-positive
  closed loop has the high-pass transfer `s τ/(1 + s τ)`; the "LPF view" `ṽ − v` has
  `−s τ/(1 + s τ)` (`residualLPF_transfer`, the opposite output sign).
* `residual_norm`: on the imaginary axis the residual gain is `|ω| τ/√(1 + ω² τ²)` (`τ > 0`).
* `idealFeedforward_field`: with an unfiltered, exact measurement (`v^ff = v`) the disturbance
  cancels identically — the closed loop does not depend on `v` and equals the PI loop of
  `PILoop.lean`.

Domain part — model boundary.
* Single-axis PI current loop as in `PILoop.lean` (series R–L branch, `L > 0`, IN-positive
  current `i`, PLL-aligned axis, ideal decoupling, no delay / PWM / limits, continuous time),
  plus the feedforward filter state.
* State order `(i, ξ, ṽ)`: `ξ = ∫ (i* − i) dt`, `ṽ` the low-passed PCC voltage.
* Plant `L di/dt = v − v^conv − R i`; controller `v^conv = −(Kp (i* − i) + Ki ξ) + ṽ`;
  filter `τ dṽ/dt = v − ṽ` with an exact measurement `v^meas = v` (noise excluded).
* Inputs `(i*, v)`; held constant in the tracking theorem.

Results.
* `lpf_det_characteristicMatrix`: the closed loop is block triangular; its characteristic
  polynomial is the PI-loop polynomial times `(s + 1/τ)`, so the spectrum is the PI spectrum
  together with `−1/τ` (`characteristic_root_iff`).
* `isHurwitz_iff`, `exponentiallyStable_iff`: adding the low-pass feedforward does not change
  the stability of the PI loop: exponentially stable iff the PI loop is and `τ > 0`, i.e. iff
  `R + Kp > 0 ∧ Ki > 0 ∧ τ > 0`.
* `tracks_reference`: then `i → i*` and `ṽ → v` for constant `i*`, `v`.

Source: work-sync `theory/T-voltage-feedforward.md` §1.3, §1.4, §2.2;
`theory/T-gfl-control.md` §1.4.2, §1.4.4; `theory/T-gfl-reduced-order-dynamics.md` §1.2.7.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter
open scoped Topology

/-! ## The filter and its residual -/

/-- Low-pass realization `τ dṽ/dt = v − ṽ`, output `ṽ`. -/
def lpf (τ : ℝ) : LTI.Model (Fin 1) (Fin 1) := ⟨!![-1 / τ], !![1 / τ], !![1], !![0]⟩

/-- Same filter, output the uncancelled disturbance `v − ṽ`. -/
def residual (τ : ℝ) : LTI.Model (Fin 1) (Fin 1) := ⟨!![-1 / τ], !![1 / τ], !![-1], !![1]⟩

@[powerlib_foundation] private lemma pole_ne {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : 1 + s * τ ≠ 0) : s - ((-1 / τ : ℝ) : ℂ) ≠ 0 := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  intro h
  apply hs
  have : s = -1 / τ := by
    push_cast at h
    linear_combination h
  rw [this]
  field_simp
  ring

@[powerlib_foundation] theorem lpf_transfer {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ} (hs : 1 + s * τ ≠ 0) :
    LTI.transfer (lpf τ) s 0 0 = 1 / (1 + s * τ) := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  rw [lpf, transfer_fin_one _ _ _ _ (pole_ne hτ hs)]
  push_cast
  field_simp
  ring

@[powerlib_foundation] theorem residual_transfer {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : 1 + s * τ ≠ 0) :
    LTI.transfer (residual τ) s 0 0 = s * τ / (1 + s * τ) := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  rw [residual, transfer_fin_one _ _ _ _ (pole_ne hτ hs)]
  have hk : s - ((-1 / τ : ℝ) : ℂ) = (1 + s * τ) / τ := by
    push_cast
    field_simp
    ring
  have e1 : ((-1 : ℝ) : ℂ) * ((1 / τ : ℝ) : ℂ) / ((1 + s * τ) / τ) = -1 / (1 + s * τ) := by
    push_cast
    rw [div_div_eq_mul_div, mul_assoc, one_div_mul_cancel hτ', mul_one]
  rw [hk, e1, Complex.ofReal_one, div_add_one hs]
  congr 1
  ring

/-- LPF view `ṽ − v`: `−s τ/(1 + s τ)`. -/
@[powerlib_foundation] theorem residualLPF_transfer {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : 1 + s * τ ≠ 0) :
    LTI.transfer (negOutput (residual τ)) s 0 0 = -(s * τ / (1 + s * τ)) := by
  rw [transfer_negOutput, Matrix.neg_apply, residual_transfer hτ hs]

/-- High-pass gain on the imaginary axis: `|jωτ/(1 + jωτ)| = |ω| τ/√(1 + ω²τ²)`. -/
@[powerlib_foundation] theorem residual_norm {τ : ℝ} (hτ : 0 < τ) (ω : ℝ) :
    ‖LTI.transfer (residual τ) ((ω : ℂ) * Complex.I) 0 0‖ =
      |ω| * τ / Real.sqrt (1 + (ω * τ) ^ 2) := by
  have hs : 1 + (ω : ℂ) * Complex.I * τ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [residual_transfer hτ.ne' hs, norm_div]
  have h1 : ‖(ω : ℂ) * Complex.I * τ‖ = |ω| * τ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hτ, mul_one]
  have h2 : ‖1 + (ω : ℂ) * Complex.I * τ‖ = Real.sqrt (1 + (ω * τ) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [h1, h2]

/-! ## Ideal feedforward cancels the disturbance exactly -/

namespace PIParams

variable (p : PIParams)

/-- IN-positive plant `L di/dt = v − v^conv − R i`, integrator `dξ/dt = i* − i`, with the
converter command `v^conv = −(Kp (i* − i) + Ki ξ) + v^ff`. -/
def ffField (vff v iref : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(v - (-p.control iref x + vff) - p.R * x 0) / p.L, iref - x 0]

/-- With `v^ff = v` the PCC voltage disappears from the closed loop. -/
@[powerlib_foundation] theorem idealFeedforward_field (v iref : ℝ) (x : Fin 2 → ℝ) :
    p.ffField v v iref x = p.field iref x := by
  ext j
  fin_cases j <;> simp [ffField, field]
  ring

/-! ## Low-pass feedforward closed loop -/

/-- Closed loop `(di/dt, dξ/dt, dṽ/dt)` with inputs `i*`, `v`. -/
def lpfField (τ iref v : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(v - (-(p.Kp * (iref - x 0) + p.Ki * x 1) + x 2) - p.R * x 0) / p.L, iref - x 0,
    (v - x 2) / τ]

/-- Realization: inputs `(i*, v)`, outputs `(i, ṽ)`. -/
def lpfModel (τ : ℝ) : LTI.Model (Fin 3) (Fin 2) :=
  ⟨!![-(p.R + p.Kp) / p.L, p.Ki / p.L, -1 / p.L; -1, 0, 0; 0, 0, -1 / τ],
    !![p.Kp / p.L, 1 / p.L; 1, 0; 0, 1 / τ], !![1, 0, 0; 0, 0, 1], 0⟩

@[powerlib_foundation] theorem lpfModel_field (τ iref v : ℝ) (x : Fin 3 → ℝ) :
    (p.lpfModel τ).field x ![iref, v] = p.lpfField τ iref v x := by
  ext j
  fin_cases j <;>
    simp [LTI.Model.field, lpfModel, lpfField, dotProduct, Fin.sum_univ_three] <;> ring

/-- Block-triangular characteristic polynomial: PI loop times `(s + 1/τ)`. -/
@[powerlib_foundation] theorem lpf_det_characteristicMatrix (τ : ℝ) (s : ℂ) :
    (LTI.characteristicMatrix (p.lpfModel τ).A s).det =
      (LTI.characteristicMatrix p.model.A s).det * (s + ((1 / τ : ℝ) : ℂ)) := by
  simp only [model, det_characteristicMatrix_of]
  simp [LTI.characteristicMatrix, lpfModel, Matrix.det_fin_three]
  ring

/-- Spectrum: the PI-loop roots together with `−1/τ`. -/
@[powerlib_foundation] theorem characteristic_root_iff (τ : ℝ) (s : ℂ) :
    (LTI.characteristicMatrix (p.lpfModel τ).A s).det = 0 ↔
      (LTI.characteristicMatrix p.model.A s).det = 0 ∨ s = ((-1 / τ : ℝ) : ℂ) := by
  rw [p.lpf_det_characteristicMatrix, mul_eq_zero]
  apply or_congr_right
  rw [add_eq_zero_iff_eq_neg]
  push_cast
  ring_nf

/-- The low-pass feedforward loop is Hurwitz iff the PI loop is and `τ > 0`. -/
@[powerlib_foundation] theorem lpf_isHurwitz_iff (τ : ℝ) :
    LinearSystems.IsHurwitz (p.lpfModel τ).A ↔
      LinearSystems.IsHurwitz p.model.A ∧ 0 < τ := by
  simp only [Criteria.isHurwitz_iff_characteristic_roots, p.characteristic_root_iff]
  constructor
  · intro h
    refine ⟨fun s hs => h s (Or.inl hs), ?_⟩
    have := h _ (Or.inr rfl)
    simp only [Complex.ofReal_re] at this
    have h1 : 0 < 1 / τ := by linarith [neg_div τ 1]
    exact one_div_pos.mp h1
  · rintro ⟨h, hτ⟩ s (hs | hs)
    · exact h s hs
    · rw [hs, Complex.ofReal_re, neg_div]
      exact neg_neg_of_pos (one_div_pos.mpr hτ)

/-- Adding the low-pass PCC-voltage feedforward preserves exponential stability of the PI loop
exactly: stable iff `R + Kp > 0 ∧ Ki > 0 ∧ τ > 0`. -/
@[powerlib_domain] theorem lpf_exponentiallyStable_iff (hL : 0 < p.L) (τ : ℝ) :
    LTI.ExponentiallyStable (p.lpfModel τ).autonomous ↔
      (0 < p.R + p.Kp ∧ 0 < p.Ki) ∧ 0 < τ := by
  rw [LTI.exponentiallyStable_iff_isHurwitz]
  change LinearSystems.IsHurwitz (p.lpfModel τ).A ↔ _
  rw [p.lpf_isHurwitz_iff, p.isHurwitz_iff hL]

/-- Same statement in semantic form: the feedforward loop is exponentially stable iff the PI
loop without feedforward is and `τ > 0`. -/
@[powerlib_domain] theorem lpf_exponentiallyStable_iff_pi (hL : 0 < p.L) (τ : ℝ) :
    LTI.ExponentiallyStable (p.lpfModel τ).autonomous ↔
      LTI.ExponentiallyStable p.model.autonomous ∧ 0 < τ := by
  rw [p.lpf_exponentiallyStable_iff hL, p.exponentiallyStable_iff hL]

/-- Equilibrium for constant `i*`, `v`: `(i*, R i*/Ki, v)`. -/
def lpfEquilibrium (iref v : ℝ) : Fin 3 → ℝ := ![iref, p.R * iref / p.Ki, v]

@[powerlib_foundation] theorem lpf_isEquilibrium (hKi : p.Ki ≠ 0) (τ iref v : ℝ) :
    (p.lpfModel τ).IsEquilibrium ![iref, v] (p.lpfEquilibrium iref v) := by
  rw [LTI.Model.IsEquilibrium, lpfModel_field]
  ext j
  fin_cases j <;> simp [lpfField, lpfEquilibrium, mul_div_assoc', mul_div_cancel_left₀ _ hKi]

/-- Tracking with low-pass feedforward: `i → i*`, `ṽ → v`. -/
@[powerlib_domain] theorem lpf_tracks_reference (hL : 0 < p.L) (hR : 0 < p.R + p.Kp)
    (hKi : 0 < p.Ki) {τ : ℝ} (hτ : 0 < τ) {iref v : ℝ} {x : ℝ → Fin 3 → ℝ}
    (hx : ∀ t, HasDerivAt x (p.lpfField τ iref v (x t)) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 iref) ∧ Tendsto (fun t => x t 2) atTop (𝓝 v) := by
  have hs := (p.lpf_exponentiallyStable_iff hL τ).2 ⟨⟨hR, hKi⟩, hτ⟩
  have he := p.lpf_isEquilibrium hKi.ne' τ iref v
  have hx' : ∀ t, HasDerivAt x ((p.lpfModel τ).field (x t) ![iref, v]) t := by
    intro t
    rw [lpfModel_field]
    exact hx t
  exact ⟨by simpa [lpfEquilibrium] using tendsto_equilibrium _ hs he hx' 0,
    by simpa [lpfEquilibrium] using tendsto_equilibrium _ hs he hx' 2⟩

end PIParams

end powerlib.CurrentControl
