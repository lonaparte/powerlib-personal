import theorem.Criteria.Jacobian

/-! # Grid-forming converter in current saturation: equilibria and the optimal current angle

Foundation (`phiOpt_*`, T-current-limiting §1.3 / T-gfm-control §1.10).
The unsaturated power–angle curve is `P = P_max sin δ`, the saturated one
`P = P_sat cos(δ − φ)` (`P_sat = V_e I_maxSAT`). With the note's
`φ_opt = arccos(P₀/P_sat) + arcsin(P₀/P_max)` and `δ₀ = arcsin(P₀/P_max)`:
`phiOpt_intersection` — both curves pass through `(δ₀, P₀)`.
Correction: the note states the formula without premises; it needs
`|P₀| ≤ min(P_sat, P_max)` (`P_sat, P_max > 0`) for `arccos`/`arcsin` to be inverse
functions. `saturated_no_intersection`: if `P_sat < |P₀|` no angle `δ`, `φ` gives
`P_sat cos(δ − φ) = P₀`.

Domain — model boundary (saturated current-source GFM, export-positive P as in the GFM family,
work-sync `conventions.md` §D9):
* State order `(δ, ω)`: `δ` the angle of the converter's internal reference relative to the
  stiff grid voltage, `ω` its frequency deviation; continuous time.
* Outer loop: VSM / swing-type `δ' = ω`, `M ω' = P_ref − P_e − D ω` with `M > 0`, `D > 0`.
* Electrical power in saturation: the converter is a current source of fixed magnitude
  `I_maxSAT` at the controlled angle `φ` relative to its reference, so
  `P_e = P_sat cos(δ − φ)` (T-current-limiting §1.3). No mode switching (the converter is
  assumed to stay saturated), no inner-loop, PWM, delay or grid dynamics.
Results:
* `satField_eq_zero_iff`: equilibria are `(δ, 0)` with `P_sat cos(δ − φ) = P_ref`;
  `saturated_equilibrium_exists_iff`: an equilibrium exists iff `|P_ref| ≤ P_sat`.
* `saturated_stable_equilibrium`: for `|P_ref| < P_sat` the equilibrium
  `δ_s = φ − arccos(P_ref/P_sat)` is locally exponentially stable;
  `saturated_unstable_equilibrium`: `δ_u = φ + arccos(P_ref/P_sat)` is unstable (saddle).

Source: work-sync `theory/T-current-limiting.md` §1.3, §1.9; `theory/T-gfm-control.md` §1.10.
-/

noncomputable section
namespace powerlib.Limiting
open Matrix
open powerlib.Dynamics

/-! ## Optimal current reference angle -/

/-- `φ_opt = arccos(P₀/P_sat) + arcsin(P₀/P_max)`. -/
def phiOpt (P0 Psat Pmax : ℝ) : ℝ := Real.arccos (P0 / Psat) + Real.arcsin (P0 / Pmax)

@[powerlib_foundation] private lemma abs_div_le_one {a b : ℝ} (hb : 0 < b) (h : |a| ≤ b) :
    -1 ≤ a / b ∧ a / b ≤ 1 := by
  have := abs_le.mp h
  constructor
  · rw [le_div_iff₀ hb]
    linarith
  · rw [div_le_iff₀ hb]
    linarith

/-- With `|P₀| ≤ min(P_sat, P_max)` the unsaturated and saturated curves intersect at the
pre-fault operating point `(arcsin(P₀/P_max), P₀)` when `φ = φ_opt`. -/
@[powerlib_foundation] theorem phiOpt_intersection {P0 Psat Pmax : ℝ} (hsat : 0 < Psat)
    (hmax : 0 < Pmax) (h1 : |P0| ≤ Psat) (h2 : |P0| ≤ Pmax) :
    Pmax * Real.sin (Real.arcsin (P0 / Pmax)) = P0 ∧
      Psat * Real.cos (Real.arcsin (P0 / Pmax) - phiOpt P0 Psat Pmax) = P0 := by
  obtain ⟨a1, a2⟩ := abs_div_le_one hmax h2
  obtain ⟨b1, b2⟩ := abs_div_le_one hsat h1
  constructor
  · rw [Real.sin_arcsin a1 a2]
    field_simp
  · have : Real.arcsin (P0 / Pmax) - phiOpt P0 Psat Pmax = -Real.arccos (P0 / Psat) := by
      simp only [phiOpt]
      ring
    rw [this, Real.cos_neg, Real.cos_arccos b1 b2]
    field_simp

/-- Without `|P₀| ≤ P_sat` the saturated curve never reaches `P₀`. -/
@[powerlib_foundation] theorem saturated_no_intersection {P0 Psat : ℝ} (hsat : 0 ≤ Psat)
    (h : Psat < |P0|) (δ φ : ℝ) : Psat * Real.cos (δ - φ) ≠ P0 := by
  intro heq
  have : |Psat * Real.cos (δ - φ)| ≤ Psat := by
    rw [abs_mul, abs_of_nonneg hsat]
    exact mul_le_of_le_one_right hsat (Real.abs_cos_le_one _)
  rw [heq] at this
  linarith

/-! ## Saturated swing model -/

/-- Saturated GFM swing field, state `(δ, ω)`. -/
def satField (M D Pref Psat φ : ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![x 1, (Pref - Psat * Real.cos (x 0 - φ) - D * x 1) / M]

/-- The state `(δ, 0)`. -/
def angleState (δ : ℝ) : State 2 := WithLp.toLp 2 ![δ, 0]

@[powerlib_foundation] theorem satField_eq_zero_iff {M D Pref Psat φ : ℝ} (hM : M ≠ 0)
    (x : State 2) :
    satField M D Pref Psat φ x = 0 ↔ x 1 = 0 ∧ Psat * Real.cos (x 0 - φ) = Pref := by
  constructor
  · intro h
    have h0 := congrArg (fun y : State 2 => y 0) h
    have h1 := congrArg (fun y : State 2 => y 1) h
    simp [satField, hM] at h0 h1
    refine ⟨h0, ?_⟩
    rw [h0] at h1
    linarith
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [satField, h0, h1]

/-- In saturation an equilibrium exists iff `|P_ref| ≤ P_sat`. -/
@[powerlib_domain] theorem saturated_equilibrium_exists_iff {M D Pref Psat φ : ℝ} (hM : M ≠ 0)
    (hsat : 0 ≤ Psat) :
    (∃ x : State 2, satField M D Pref Psat φ x = 0) ↔ |Pref| ≤ Psat := by
  simp only [satField_eq_zero_iff hM]
  constructor
  · rintro ⟨x, -, hx⟩
    rw [← hx, abs_mul, abs_of_nonneg hsat]
    exact mul_le_of_le_one_right hsat (Real.abs_cos_le_one _)
  · intro h
    rcases hsat.lt_or_eq with hpos | hzero
    · obtain ⟨b1, b2⟩ := abs_div_le_one hpos h
      refine ⟨angleState (φ + Real.arccos (Pref / Psat)), by simp [angleState], ?_⟩
      simp only [angleState, PiLp.toLp_apply, Matrix.cons_val_zero, add_sub_cancel_left,
        Real.cos_arccos b1 b2]
      field_simp
    · refine ⟨angleState 0, by simp [angleState], ?_⟩
      rw [← hzero] at h ⊢
      simp only [zero_mul]
      exact (abs_nonpos_iff.mp h).symm

/-- Jacobian at `(δ, 0)`. -/
def satJacobian (M D Psat φ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; Psat * Real.sin (δ - φ) / M, -D / M]

@[powerlib_foundation] theorem satField_contDiff (M D Pref Psat φ : ℝ) :
    ContDiff ℝ 1 (satField M D Pref Psat φ) := by
  apply Criteria.contDiff_of_components
  intro i
  fin_cases i <;> simp [satField] <;> fun_prop

@[powerlib_foundation] theorem satField_fderiv (M D Pref Psat φ δ : ℝ) :
    fderiv ℝ (satField M D Pref Psat φ) (angleState δ) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (satJacobian M D Psat φ δ) := by
  set x := angleState δ
  have h0 := Criteria.hasFDerivAt_coord 0 x
  have h1 := Criteria.hasFDerivAt_coord 1 x
  have hc := ((h0.sub_const φ).cos.const_mul Psat)
  have hω := (((hc.const_sub Pref).sub (h1.const_mul D)).mul_const M⁻¹)
  refine Criteria.fderiv_eq_toEuclideanCLM_of_components _
    ![Criteria.coord 1, M⁻¹ • (-(Psat • -Real.sin (x 0 - φ) • Criteria.coord 0) -
      D • Criteria.coord 1)] ?_ ?_
  · intro i
    fin_cases i
    · simpa [satField] using h1
    · convert hω using 1
      · funext y
        simp [satField, div_eq_mul_inv]
      · rfl
  · intro i v
    fin_cases i
    · simp [satJacobian, Fin.sum_univ_two]
    · simp [satJacobian, Fin.sum_univ_two, x, angleState]
      ring

/-- Stable saturated equilibrium `δ_s = φ − arccos(P_ref/P_sat)` (`|P_ref| < P_sat`). -/
@[powerlib_domain] theorem saturated_stable_equilibrium {M D Pref Psat φ : ℝ} (hM : 0 < M)
    (hD : 0 < D) (hsat : 0 < Psat) (h : |Pref| < Psat) :
    Dynamics.LocallyExponentiallyStable (satField M D Pref Psat φ)
      (angleState (φ - Real.arccos (Pref / Psat))) := by
  obtain ⟨b1, b2⟩ := abs_div_le_one hsat h.le
  have hy : |Pref / Psat| < 1 := by
    rw [abs_div, abs_of_pos hsat, div_lt_one hsat]
    exact h
  have hsin : 0 < Real.sin (Real.arccos (Pref / Psat)) := by
    rw [Real.sin_arccos]
    apply Real.sqrt_pos.mpr
    nlinarith [abs_lt.mp hy, sq_abs (Pref / Psat)]
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_two _ (satField_contDiff _ _ _ _ _)
    ((satField_eq_zero_iff hM.ne' _).mpr ⟨by simp [angleState], ?_⟩) (satField_fderiv _ _ _ _ _ _)
    ?_ ?_
  · simp only [angleState, PiLp.toLp_apply, Matrix.cons_val_zero, sub_sub_cancel_left,
      Real.cos_neg, Real.cos_arccos b1 b2]
    field_simp
  · simp only [satJacobian, Matrix.trace_fin_two_of, zero_add]
    exact div_neg_of_neg_of_pos (by linarith) hM
  · have e : (satJacobian M D Psat φ (φ - Real.arccos (Pref / Psat))).det =
        Psat * Real.sin (Real.arccos (Pref / Psat)) / M := by
      simp only [satJacobian, Matrix.det_fin_two_of, sub_sub_cancel_left, Real.sin_neg]
      ring
    rw [e]
    exact div_pos (mul_pos hsat hsin) hM

/-- Dynamics.Unstable saturated equilibrium `δ_u = φ + arccos(P_ref/P_sat)` (`|P_ref| < P_sat`). -/
@[powerlib_domain] theorem saturated_unstable_equilibrium {M D Pref Psat φ : ℝ} (hM : 0 < M)
    (hsat : 0 < Psat) (h : |Pref| < Psat) :
    Dynamics.Unstable (satField M D Pref Psat φ) (angleState (φ + Real.arccos (Pref / Psat))) := by
  obtain ⟨b1, b2⟩ := abs_div_le_one hsat h.le
  have hy : |Pref / Psat| < 1 := by
    rw [abs_div, abs_of_pos hsat, div_lt_one hsat]
    exact h
  have hsin : 0 < Real.sin (Real.arccos (Pref / Psat)) := by
    rw [Real.sin_arccos]
    apply Real.sqrt_pos.mpr
    nlinarith [abs_lt.mp hy, sq_abs (Pref / Psat)]
  refine Criteria.unstable_of_jacobian_det_neg_fin_two _ (satField_contDiff _ _ _ _ _)
    ((satField_eq_zero_iff hM.ne' _).mpr ⟨by simp [angleState], ?_⟩) (satField_fderiv _ _ _ _ _ _)
    ?_
  · simp only [angleState, PiLp.toLp_apply, Matrix.cons_val_zero, add_sub_cancel_left,
      Real.cos_arccos b1 b2]
    field_simp
  · simp only [satJacobian, Matrix.det_fin_two_of, add_sub_cancel_left]
    have : 0 < Psat * Real.sin (Real.arccos (Pref / Psat)) / M := div_pos (mul_pos hsat hsin) hM
    nlinarith

end powerlib.Limiting
