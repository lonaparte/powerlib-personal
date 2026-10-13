import theorem.Criteria.Jacobian
import theorem.CurrentControl.SISO
import theorem.Dynamics.ConverseLinearization
import theorem.Flow.Shift
import theorem.Synchronous.Swing

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
  `saturated_equilibrium_exists_iff`: an equilibrium exists iff `|P_ref| ≤ P_sat` (static).

## Family and connection conclusions

`family : Family SatModel Spectral.Requirement 2 0` reads a saturated model together with a
selected angle `δ*` as its field translated so that `(δ*, 0)` is the origin
(`Spectral.localFamily`, `Flow.Property.holds_shift_iff`). Requirements (static, on the
Jacobian `[[0, 1], [P_sat sin(δ* − φ)/M, −D/M]]`): `stable` — `(δ*, 0)` is an equilibrium,
`M, D > 0` and `P_sat sin(δ* − φ) < 0`; `unstable` — an equilibrium, `M > 0` and
`P_sat sin(δ* − φ) > 0` (saddle). The local sentences translate into `stable`, instability into
`unstable`, passivity into nothing, the rest into the whole (inconsistent) language.
* `chain_le_semantics`, `exact_passive`.
* `saturated_stable_equilibrium` (connection): for `|P_ref| < P_sat` the equilibrium
  `δ_s = φ − arccos(P_ref/P_sat)` is locally exponentially stable;
  `saturated_unstable_equilibrium` (connection): `δ_u = φ + arccos(P_ref/P_sat)` is unstable
  (saddle).
* `mem_den_locallyExponentiallyStable_iff` (connection, member equivalence): with `M > 0`, local
  exponential stability of `(δ*, 0)` holds exactly when it is an equilibrium with `D > 0` and
  `P_sat sin(δ* − φ) < 0` (converse linearization,
  `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`): the translation is exact within
  positive inertia. `not_exact_locallyExponentiallyStable` (boundary witness): without that range
  it is not exact — the model `M = D = −1`, `P_sat = 1`, `φ = P_ref = 0`, `δ* = π/2` is locally
  exponentially stable (`negativeInertia_mem_den_locallyExponentiallyStable`).
* The saturated model is the canonical swing model with `k₁ = 0`, `k₂ = P_sat`, `k₃ = φ − π/2`
  (`SatModel.toSwing`, `satField_eq_swing`); on flow sentences the two families agree
  (`mem_den_flow_iff_swing`, a comparison of the two semantics connections). Through it, within
  positive inertia, `mem_den_locallyAsymptoticallyStable_iff`: local asymptotic stability holds
  exactly under the local exponential condition (the swing family's exactness,
  `Synchronous.Swing.exactUnder_locallyAsymptoticallyStable`, decides the degenerate slopes), and
  `mem_den_lyapunovStable_iff`: Lyapunov stability holds exactly at an equilibrium with `D ≥ 0` and
  `P_sat sin(δ* − φ) < 0`, or with `P_sat = 0` and `D > 0` — so the Lyapunov translation is not
  exact even within positive inertia. Without positive inertia neither is exact
  (`not_exact_locallyAsymptoticallyStable`, `not_exact_lyapunovStable`, the negative-inertia
  witness through `Spectral.local_not_exact_of_not_exact_les`).
* `not_exact_unstable` (boundary witness): instability is the failure of Lyapunov stability, so
  an unbalanced model (`offEquilibrium`) is unstable (`offEquilibrium_mem_den_unstable`,
  `Dynamics.unstable_of_ne_zero`) while the instability condition asks for an equilibrium.

Source: work-sync `theory/T-current-limiting.md` §1.3, §1.9; `theory/T-gfm-control.md` §1.10.
-/

noncomputable section
namespace powerlib.Limiting
open Matrix
open powerlib.Dynamics LinearSystems

/-! ## Optimal current reference angle -/

/-- `φ_opt = arccos(P₀/P_sat) + arcsin(P₀/P_max)`. -/
def phiOpt (P0 Psat Pmax : ℝ) : ℝ := Real.arccos (P0 / Psat) + Real.arcsin (P0 / Pmax)

private lemma abs_div_le_one {a b : ℝ} (hb : 0 < b) (h : |a| ≤ b) :
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

/-- In saturation an equilibrium exists iff `|P_ref| ≤ P_sat`. Static evidence on the model,
not a connection conclusion. -/
@[powerlib_foundation] theorem saturated_equilibrium_exists_iff {M D Pref Psat φ : ℝ} (hM : M ≠ 0)
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

/-- At an equilibrium `(δ, 0)` with `M, D > 0` and `P_sat sin(δ − φ) < 0` the saturated field is
locally exponentially stable (Jacobian trace `−D/M < 0`, determinant `−P_sat sin(δ − φ)/M > 0`).
Implementation evidence for the family's soundness. -/
private theorem satField_les_of {M D Pref Psat φ δ : ℝ} (hM : 0 < M) (hD : 0 < D)
    (heq : Psat * Real.cos (δ - φ) = Pref) (hsin : Psat * Real.sin (δ - φ) < 0) :
    LocallyExponentiallyStable (satField M D Pref Psat φ) (angleState δ) := by
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_two _ (satField_contDiff _ _ _ _ _)
    ((satField_eq_zero_iff hM.ne' _).mpr ⟨by simp [angleState], by simpa [angleState] using heq⟩)
    (satField_fderiv _ _ _ _ _ _) ?_ ?_
  · simp only [satJacobian, Matrix.trace_fin_two_of, zero_add]
    exact div_neg_of_neg_of_pos (by linarith) hM
  · simp only [satJacobian, Matrix.det_fin_two_of]
    have : Psat * Real.sin (δ - φ) / M < 0 := div_neg_of_neg_of_pos hsin hM
    linarith

/-- At an equilibrium `(δ, 0)` with `M > 0` and `P_sat sin(δ − φ) > 0` the saturated field is
unstable (saddle). Implementation evidence for the family's soundness. -/
private theorem satField_unstable_of {M D Pref Psat φ δ : ℝ} (hM : 0 < M)
    (heq : Psat * Real.cos (δ - φ) = Pref) (hsin : 0 < Psat * Real.sin (δ - φ)) :
    Unstable (satField M D Pref Psat φ) (angleState δ) := by
  refine Criteria.unstable_of_jacobian_det_neg_fin_two _ (satField_contDiff _ _ _ _ _)
    ((satField_eq_zero_iff hM.ne' _).mpr ⟨by simp [angleState], by simpa [angleState] using heq⟩)
    (satField_fderiv _ _ _ _ _ _) ?_
  simp only [satJacobian, Matrix.det_fin_two_of]
  have : 0 < Psat * Real.sin (δ - φ) / M := div_pos hsin hM
  linarith

/-! ## The saturated-GFM family -/

/-- A saturated GFM swing model with a selected angle `δ*` (point `(δ*, 0)`). -/
@[ext] structure SatModel where
  M : ℝ
  D : ℝ
  Pref : ℝ
  Psat : ℝ
  φ : ℝ
  /-- The selected angle `δ*`. -/
  δ : ℝ

namespace SatModel

/-- The saturated field translated so that `(δ*, 0)` is the origin. -/
def field (m : SatModel) (z : State 2) : State 2 :=
  satField m.M m.D m.Pref m.Psat m.φ (z + angleState m.δ)

/-- Stability condition: an equilibrium, `M, D > 0`, `P_sat sin(δ* − φ) < 0`. -/
def Stable (m : SatModel) : Prop :=
  m.Psat * Real.cos (m.δ - m.φ) = m.Pref ∧ 0 < m.M ∧ 0 < m.D ∧ m.Psat * Real.sin (m.δ - m.φ) < 0

/-- Instability condition: an equilibrium, `M > 0`, `P_sat sin(δ* − φ) > 0`. -/
def Unstable (m : SatModel) : Prop :=
  m.Psat * Real.cos (m.δ - m.φ) = m.Pref ∧ 0 < m.M ∧ 0 < m.Psat * Real.sin (m.δ - m.φ)

end SatModel

/-- The saturated-GFM family about a selected angle. -/
def family : Family SatModel Spectral.Requirement 2 0 :=
  Spectral.localFamily SatModel.field SatModel.Stable SatModel.Unstable

private theorem mem_den_flow {m : SatModel} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔
      P.holds (satField m.M m.D m.Pref m.Psat m.φ) (angleState m.δ) :=
  (Spectral.localFamily_isAutonomous _ _ _).mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Every translation of the saturated-GFM family is sound (local linearization at the
selected equilibrium). -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m h => ?_) (fun m h => ?_)
  · exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (satField_les_of h.2.1 h.2.2.1 h.1 h.2.2.2)
  · exact (Flow.Property.holds_shift_iff .unstable).mpr (satField_unstable_of h.2.1 h.1 h.2.2)

/-- Passivity is translated exactly: the autonomous model has no ports. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_exact_passive _ _ _

private lemma sin_arccos_pos {Pref Psat : ℝ} (hsat : 0 < Psat) (h : |Pref| < Psat) :
    0 < Real.sin (Real.arccos (Pref / Psat)) := by
  have hy : |Pref / Psat| < 1 := by
    rw [abs_div, abs_of_pos hsat, div_lt_one hsat]
    exact h
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  nlinarith [abs_lt.mp hy, sq_abs (Pref / Psat)]

/-- Stable saturated equilibrium `δ_s = φ − arccos(P_ref/P_sat)` (`|P_ref| < P_sat`). -/
@[powerlib_domain] theorem saturated_stable_equilibrium {M D Pref Psat φ : ℝ} (hM : 0 < M)
    (hD : 0 < D) (hsat : 0 < Psat) (h : |Pref| < Psat) :
    connection% (⟨M, D, Pref, Psat, φ, φ - Real.arccos (Pref / Psat)⟩ ∈
      family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨b1, b2⟩ := abs_div_le_one hsat h.le
  have hsin := sin_arccos_pos hsat h
  refine mem_den_flow.mpr (satField_les_of hM hD ?_ ?_)
  · rw [sub_sub_cancel_left, Real.cos_neg, Real.cos_arccos b1 b2]
    field_simp
  · rw [sub_sub_cancel_left, Real.sin_neg]
    nlinarith

/-- Unstable saturated equilibrium `δ_u = φ + arccos(P_ref/P_sat)` (`|P_ref| < P_sat`). -/
@[powerlib_domain] theorem saturated_unstable_equilibrium {M D Pref Psat φ : ℝ} (hM : 0 < M)
    (hsat : 0 < Psat) (h : |Pref| < Psat) :
    connection% (⟨M, D, Pref, Psat, φ, φ + Real.arccos (Pref / Psat)⟩ ∈
      family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨b1, b2⟩ := abs_div_le_one hsat h.le
  have hsin := sin_arccos_pos hsat h
  refine mem_den_flow.mpr (satField_unstable_of hM ?_ ?_)
  · rw [add_sub_cancel_left, Real.cos_arccos b1 b2]
    field_simp
  · rw [add_sub_cancel_left]
    positivity

/-! ## Exactness within positive inertia -/

/-- Positive inertia: local exponential stability of a saturated model at `(δ*, 0)` holds exactly
when `(δ*, 0)` is an equilibrium, `D > 0` and `P_sat sin(δ* − φ) < 0`. Converse linearization:
local exponential stability forces an equilibrium with a Hurwitz Jacobian. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : SatModel) (hM : 0 < m.M) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : SatModel | m.Psat * Real.cos (m.δ - m.φ) = m.Pref ∧ 0 < m.D ∧
        m.Psat * Real.sin (m.δ - m.φ) < 0}) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow, Set.mem_ofPred_eq]
  change LocallyExponentiallyStable _ _ ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (satField_contDiff _ _ _ _ _)
    (satField_fderiv _ _ _ _ _ _), satField_eq_zero_iff hM.ne', satJacobian,
    Criteria.isHurwitz_fin_two_of_iff]
  simp only [angleState, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, true_and, zero_add, zero_mul, zero_sub]
  constructor
  · rintro ⟨heq, htr, hdet⟩
    refine ⟨heq, ?_, ?_⟩
    · rw [neg_div, neg_lt_zero] at htr
      exact (div_pos_iff_of_pos_right hM).mp htr
    · have : m.Psat * Real.sin (m.δ - m.φ) / m.M < 0 := by linarith
      exact (div_neg_iff.mp this).elim (fun h => absurd hM (not_lt.mpr h.2.le)) (fun h => h.1)
  · rintro ⟨heq, hD, hs⟩
    refine ⟨heq, ?_, ?_⟩
    · rw [neg_div, neg_lt_zero]
      exact div_pos hD hM
    · have : m.Psat * Real.sin (m.δ - m.φ) / m.M < 0 := div_neg_of_neg_of_pos hs hM
      linarith

/-- Negative inertia and damping, `M = D = −1`, `P_sat = 1`, `φ = P_ref = 0`, at `δ* = π/2`. -/
def negativeInertia : SatModel := ⟨-1, -1, 0, 1, 0, Real.pi / 2⟩

/-- The negative-inertia saturated model is locally exponentially stable: its Jacobian
`[[0, 1], [−1, −1]]` is Hurwitz. -/
@[powerlib_domain] theorem negativeInertia_mem_den_locallyExponentiallyStable :
    connection% (negativeInertia ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow.mpr (Criteria.locallyExponentiallyStable_of_jacobian_fin_two _
    (satField_contDiff _ _ _ _ _) ((satField_eq_zero_iff (by norm_num [negativeInertia]) _).mpr
      ⟨by simp [angleState], by simp [negativeInertia, angleState]⟩) (satField_fderiv _ _ _ _ _ _)
    ?_ ?_)
  · simp [satJacobian, negativeInertia, Matrix.trace_fin_two_of]
  · simp [satJacobian, negativeInertia, Matrix.det_fin_two_of]

/-- The local exponential translation is sound but not exact: the negative-inertia model is
locally exponentially stable without positive inertia. -/
@[powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeInertia_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : SatModel.Stable negativeInertia := hmem .stable rfl
  have := hs.2.1
  norm_num [negativeInertia] at this

/-! ## The local asymptotic and Lyapunov sentences: the saturated model is a swing model -/

/-- The saturated model read as the canonical swing model: `k₁ = 0`, `k₂ = P_sat`,
`k₃ = φ − π/2`, so that `P_e = P_sat sin(δ − φ + π/2) = P_sat cos(δ − φ)`. -/
def SatModel.toSwing (m : SatModel) : Synchronous.Swing.Model :=
  ⟨⟨m.M, m.D, m.Pref, 0, m.Psat, m.φ - Real.pi / 2⟩, m.δ⟩

/-- The saturated field is the swing field of `toSwing`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem satField_eq_swing (m : SatModel) :
    satField m.M m.D m.Pref m.Psat m.φ = m.toSwing.p.field := by
  funext x
  ext i
  fin_cases i
  · simp [satField, Synchronous.SwingParams.field, SatModel.toSwing]
  · simp only [satField, Synchronous.SwingParams.field, SatModel.toSwing,
      Synchronous.SwingParams.accel, Synchronous.SwingParams.Pe]
    simp only [PiLp.toLp_apply, Synchronous.mkState,
      WithLp.equiv_symm_apply]
    rw [show x 0 - (m.φ - Real.pi / 2) = (x 0 - m.φ) + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two, zero_add]

/-- On flow sentences the saturated family agrees with the swing family: a saturated model
satisfies a flow sentence exactly when its swing reading does. A comparison of the two semantics
connections at the two members. -/
@[powerlib_domain] theorem mem_den_flow_iff_swing (m : SatModel) (P : Flow.Property) :
    connection% (m ∈ family.den (.flow P) ↔
      m.toSwing ∈ Synchronous.Swing.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow, Synchronous.Swing.family_isAutonomous.mem_den_flow,
    ← Flow.Property.holds_shift_iff, satField_eq_swing]
  have hpt : angleState m.δ = m.toSwing.point := by
    ext i
    fin_cases i <;> simp [angleState, Synchronous.Swing.Model.point, SatModel.toSwing]
  rw [hpt]
  rfl

private theorem toSwing_Pe (m : SatModel) :
    m.toSwing.p.Pe m.toSwing.δ = m.Psat * Real.cos (m.δ - m.φ) := by
  simp only [SatModel.toSwing, Synchronous.SwingParams.Pe, zero_add]
  rw [show m.δ - (m.φ - Real.pi / 2) = (m.δ - m.φ) + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two]

private theorem toSwing_syncCoeff (m : SatModel) :
    m.toSwing.p.syncCoeff m.toSwing.δ = -(m.Psat * Real.sin (m.δ - m.φ)) := by
  simp only [SatModel.toSwing, Synchronous.SwingParams.syncCoeff]
  rw [show m.δ - (m.φ - Real.pi / 2) = (m.δ - m.φ) + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two]
  ring

/-- Positive inertia: local asymptotic stability of a saturated model at `(δ*, 0)` holds exactly
when `(δ*, 0)` is an equilibrium, `D > 0` and `P_sat sin(δ* − φ) < 0` — the same condition as
local exponential stability. The linearization does not decide the degenerate cases; through the
swing reading (`mem_den_flow_iff_swing`) the swing family's exactness within positive inertia
applies (`Synchronous.Swing.exactUnder_locallyAsymptoticallyStable`: conserved energy for `D = 0`,
a continuum of equilibria for `P_sat = 0`, the dissipated energy at a fold of the curve). -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (m : SatModel) (hM : 0 < m.M) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : SatModel | m.Psat * Real.cos (m.δ - m.φ) = m.Pref ∧ 0 < m.D ∧
        m.Psat * Real.sin (m.δ - m.φ) < 0}) := by
  have hsw := mem_den_flow_iff_swing m .locallyAsymptoticallyStable
  have hex := Synchronous.Swing.exactUnder_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hsw hex ⊢
  unfold Family.ExactUnder TMIO.ExactUnder at hex
  rw [hsw, Set.mem_ofPred_eq]
  have hI : m.toSwing ∈ TMIO.realize Synchronous.Swing.family.meets {.inertia} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hM
  constructor
  · intro h
    have h' : m.toSwing ∈ TMIO.realize Synchronous.Swing.family.meets
        (Synchronous.Swing.family.translate (.flow .locallyAsymptoticallyStable) ∪
          {.inertia}) := by
      rw [hex]
      exact ⟨h, hI⟩
    rw [TMIO.mem_realize] at h'
    have hb : m.toSwing.p.Pe m.toSwing.δ = m.toSwing.p.Pm :=
      h' .balanced (by simp [Synchronous.Swing.family, Synchronous.Swing.translate])
    have hD : 0 < m.toSwing.p.D :=
      h' .damped (by simp [Synchronous.Swing.family, Synchronous.Swing.translate])
    have hK : 0 < m.toSwing.p.syncCoeff m.toSwing.δ :=
      h' .synchronizing (by simp [Synchronous.Swing.family, Synchronous.Swing.translate])
    rw [toSwing_Pe] at hb
    rw [toSwing_syncCoeff] at hK
    exact ⟨hb, hD, by linarith⟩
  · rintro ⟨hb, hD, hs⟩
    have h' : m.toSwing ∈ TMIO.realize Synchronous.Swing.family.meets
        (Synchronous.Swing.family.translate (.flow .locallyAsymptoticallyStable) ∪
          {.inertia}) := by
      rw [TMIO.mem_realize]
      intro q hq
      simp only [Synchronous.Swing.family, Synchronous.Swing.translate, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with ((rfl | rfl | rfl | rfl) | rfl)
      · show m.toSwing.p.Pe m.toSwing.δ = m.toSwing.p.Pm
        rw [toSwing_Pe]
        exact hb
      · exact hM
      · exact hD
      · show 0 < m.toSwing.p.syncCoeff m.toSwing.δ
        rw [toSwing_syncCoeff]
        linarith
      · exact hM
    rw [hex] at h'
    exact h'.1

/-- Positive inertia: Lyapunov stability of a saturated model at `(δ*, 0)` holds exactly at an
equilibrium with `D ≥ 0` and `P_sat sin(δ* − φ) < 0`, or with a zero saturated current
(`P_sat = 0`) and `D > 0` (`Synchronous.Swing.mem_den_lyapunovStable_iff_of_inertia`: a fold of
the curve is unstable for every `D ≥ 0`). -/
@[powerlib_domain] theorem mem_den_lyapunovStable_iff (m : SatModel) (hM : 0 < m.M) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : SatModel | m.Psat * Real.cos (m.δ - m.φ) = m.Pref ∧
        ((0 ≤ m.D ∧ m.Psat * Real.sin (m.δ - m.φ) < 0) ∨ (m.Psat = 0 ∧ 0 < m.D))}) := by
  have hsw := mem_den_flow_iff_swing m .lyapunovStable
  have hiff := Synchronous.Swing.mem_den_lyapunovStable_iff_of_inertia m.toSwing hM
  unfold powerlib.TMIO.Statement at hsw hiff ⊢
  rw [hsw, hiff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, toSwing_Pe, toSwing_syncCoeff]
  simp only [SatModel.toSwing]
  constructor
  · rintro ⟨hb, (⟨hD, hK⟩ | ⟨hk, hD⟩)⟩
    · exact ⟨hb, Or.inl ⟨hD, by linarith⟩⟩
    · exact ⟨hb, Or.inr ⟨hk, hD⟩⟩
  · rintro ⟨hb, (⟨hD, hK⟩ | ⟨hk, hD⟩)⟩
    · exact ⟨hb, Or.inl ⟨hD, by linarith⟩⟩
    · exact ⟨hb, Or.inr ⟨hk, hD⟩⟩

/-- Without positive inertia the local asymptotic translation is sound but not exact (the
negative-inertia model, `Spectral.local_not_exact_of_not_exact_les`). -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun m hm =>
    (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (satField_les_of hm.2.1 hm.2.2.1 hm.1 hm.2.2.2)) h (Or.inr rfl)

/-- The Lyapunov translation is sound but not exact: the negative-inertia model, and, within
positive inertia, a zero saturated current with `D > 0` (`mem_den_lyapunovStable_iff`). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun m hm =>
    (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (satField_les_of hm.2.1 hm.2.2.1 hm.1 hm.2.2.2)) h (Or.inl rfl)

/-! ## Instability away from equilibrium -/

/-- An unbalanced saturated model: `M = P_ref = 1`, `D = P_sat = φ = 0`, `δ* = 0`. -/
def offEquilibrium : SatModel := ⟨1, 0, 1, 0, 0, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow.mpr (Dynamics.unstable_of_ne_zero (satField_contDiff _ _ _ _ _)
    fun h => ?_)
  rw [satField_eq_zero_iff (by norm_num [offEquilibrium])] at h
  simp [offEquilibrium, angleState] at h

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the instability condition asks for an equilibrium. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : SatModel.Unstable offEquilibrium := hmem .unstable rfl
  have := hs.1
  simp [offEquilibrium] at this

end powerlib.Limiting
