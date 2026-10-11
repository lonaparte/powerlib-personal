import theorem.Criteria.Hurwitz2
import theorem.Dynamics.Stability

/-! # The sinusoidally coupled swing equation (canonical single-machine model)

Model boundary.
* State `x = (δ, ω) : Dynamics.State 2`, in this order: `δ` is the internal (rotor or virtual)
  angle relative to the synchronously rotating reference of an ideal infinite bus (rad), `ω`
  is the angular-frequency deviation `ω = δ̇` from the synchronous speed (rad/s).
* Continuous time, autonomous, no input: the mechanical/reference power `P_m` is constant.
* Dynamics `δ̇ = ω`, `M ω̇ = P_m − P_e(δ) − D ω` with the sinusoidal power-angle curve
  `P_e(δ) = k₁ + k₂ sin(δ − k₃)` (`k₁` = constant (loss/conductance) offset, `k₂` = amplitude,
  `k₃` = phase offset).  Power is export-positive: `P_e > 0` is power delivered by the machine
  to the bus (generator convention; for the GFM instances the GFM export-positive exception).
* Parameters `M, D, P_m, k₁, k₂, k₃ : ℝ` are free; every theorem lists its own sign
  assumptions (typically `0 < M`, `0 < k₂`, and `0 < D` or `0 ≤ D`).
* Excluded: flux / excitation / AVR / governor dynamics, PLL, delays, PWM, current limiting,
  network dynamics and any time-varying fault switching (the three-stage fault sequence is
  handled segment by segment in `theorem/Synchronous/EqualArea.lean`).
* Conclusions are about equilibria of the full nonlinear field (equilibrium set, local
  exponential stability, instability, Lyapunov stability via the energy function) and about
  the LTI linearization; global existence of solutions (forward completeness) is proved from
  a global Lipschitz bound.

Instances (`theorem/Synchronous/Instances.lean`): VSG / VSM on an infinite bus
(`k₁ = 0, k₃ = 0, k₂ = E V_g / X_g`), the classical SMIB model (`k₂ = E' V_∞ / X_d'`), and the
post-fault SMIB curve with line resistance.

Source: work-sync theory/T-vsg-control.md §1.2, §1.10; theory/T-sync-machine.md §1.9;
theory/T-transient-stability.md §1.3, §1.4, §1.7;
projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md §1–§3
(overdamping threshold).
-/

noncomputable section
namespace powerlib.Synchronous
open Set Filter Topology Matrix
open powerlib.Dynamics (State)

/-- Parameters of `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`. -/
structure SwingParams where
  M : ℝ
  D : ℝ
  Pm : ℝ
  k₁ : ℝ
  k₂ : ℝ
  k₃ : ℝ

/-- Coordinate projections of the two-dimensional state are smooth. -/
@[fun_prop, powerlib_foundation] theorem coord_contDiff {k : WithTop ℕ∞} (j : Fin 2) :
    ContDiff ℝ k (fun x : State 2 => x j) :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State 2 →L[ℝ] ℝ).contDiff

/-- The state `(δ, ω)`. -/
def mkState (δ ω : ℝ) : State 2 := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![δ, ω]

@[simp, powerlib_foundation] theorem mkState_zero (δ ω : ℝ) : mkState δ ω 0 = δ := by
  simp [mkState]

@[simp, powerlib_foundation] theorem mkState_one (δ ω : ℝ) : mkState δ ω 1 = ω := by
  simp [mkState]

@[powerlib_foundation] theorem state_ext {x y : State 2} (h0 : x 0 = y 0) (h1 : x 1 = y 1) :
    x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

@[powerlib_foundation] theorem eq_mkState (x : State 2) : x = mkState (x 0) (x 1) :=
  state_ext (by simp) (by simp)

@[powerlib_foundation] theorem norm_sq_state (x : State 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_succ, sq_abs]

@[powerlib_foundation] theorem norm_state_le (x : State 2) : ‖x‖ ≤ |x 0| + |x 1| := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have h : ‖x‖ ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
    rw [norm_sq_state]; nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg h0 h1]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

@[powerlib_foundation] theorem abs_coord_le (x : State 2) (j : Fin 2) : |x j| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le x j

@[powerlib_foundation] theorem toEuclideanCLM_apply_zero (A : Matrix (Fin 2) (Fin 2) ℝ)
    (v : State 2) :
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A v) 0 = A 0 0 * v 0 + A 0 1 * v 1 := by
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[powerlib_foundation] theorem toEuclideanCLM_apply_one (A : Matrix (Fin 2) (Fin 2) ℝ)
    (v : State 2) :
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A v) 1 = A 1 0 * v 0 + A 1 1 * v 1 := by
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

namespace SwingParams

variable (p : SwingParams)

/-- Electrical (export-positive) power-angle curve `P_e(δ) = k₁ + k₂ sin(δ − k₃)`. -/
def Pe (δ : ℝ) : ℝ := p.k₁ + p.k₂ * Real.sin (δ - p.k₃)

/-- Angular acceleration `ω̇ = (P_m − P_e(δ) − D ω) / M`. -/
def accel (δ ω : ℝ) : ℝ := (p.Pm - p.Pe δ - p.D * ω) / p.M

/-- The full nonlinear swing vector field on `(δ, ω)`. -/
def field (x : State 2) : State 2 := mkState (x 1) (p.accel (x 0) (x 1))

@[simp, powerlib_foundation] theorem field_apply_zero (x : State 2) : p.field x 0 = x 1 := by
  simp [field]

@[simp, powerlib_foundation] theorem field_apply_one (x : State 2) :
    p.field x 1 = p.accel (x 0) (x 1) := by
  simp [field]

/-- Synchronizing coefficient `K(δ) = P_e'(δ) = k₂ cos(δ − k₃)`. -/
def syncCoeff (δ : ℝ) : ℝ := p.k₂ * Real.cos (δ - p.k₃)

/-- Jacobian of the swing field at angle `δ` (it does not depend on `ω`). -/
def jacobian (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -p.syncCoeff δ / p.M, -p.D / p.M]

@[powerlib_foundation] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k p.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa using coord_contDiff (k := k) 1
  · simp only [Fin.mk_one, Fin.isValue, field_apply_one, accel, Pe]
    fun_prop

@[powerlib_foundation] theorem hasFDerivAt_field (x : State 2) :
    HasFDerivAt p.field (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (p.jacobian (x 0))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, field_apply_zero]
    convert h1 using 1
    · rfl
    apply ContinuousLinearMap.ext; intro v
    simp [jacobian, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp only [Fin.mk_one, Fin.isValue, field_apply_one]
    have hs := ((Real.hasDerivAt_sin (x 0 - p.k₃)).comp_hasFDerivAt x (h0.sub_const p.k₃))
    have h := (((hasFDerivAt_const p.Pm x).sub ((hasFDerivAt_const p.k₁ x).add
      (hs.const_mul p.k₂))).sub (h1.const_mul p.D)).const_mul p.M⁻¹
    convert h using 1
    · funext y; simp [accel, Pe, div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, syncCoeff, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      ring

@[powerlib_foundation] theorem fderiv_field (x : State 2) :
    fderiv ℝ p.field x = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (p.jacobian (x 0)) :=
  (p.hasFDerivAt_field x).fderiv

@[simp, powerlib_foundation] theorem trace_jacobian (δ : ℝ) :
    (p.jacobian δ).trace = -p.D / p.M := by
  simp [jacobian, Matrix.trace_fin_two]

@[simp, powerlib_foundation] theorem det_jacobian (δ : ℝ) :
    (p.jacobian δ).det = p.syncCoeff δ / p.M := by
  simp [jacobian, Matrix.det_fin_two]
  ring

/-! ## Equilibria -/

/-- Equilibria of the full field: zero frequency deviation and power balance. -/
@[powerlib_domain] theorem field_eq_zero_iff (hM : p.M ≠ 0) (x : State 2) :
    p.field x = 0 ↔ x 1 = 0 ∧ p.Pe (x 0) = p.Pm := by
  constructor
  · intro h
    have h0 := congrArg (fun y : State 2 => y 0) h
    have h1 := congrArg (fun y : State 2 => y 1) h
    simp only [field_apply_zero, field_apply_one, PiLp.zero_apply] at h0 h1
    refine ⟨h0, ?_⟩
    simp only [accel, h0, mul_zero, sub_zero, div_eq_zero_iff, hM, or_false] at h1
    linarith
  · rintro ⟨h0, h1⟩
    apply state_ext
    · simp [h0]
    · simp [accel, h0, h1]

/-- Equilibrium existence: the power-angle curve reaches the mechanical power,
`|P_m − k₁| ≤ k₂` (`k₂ > 0`). -/
@[powerlib_domain] theorem exists_equilibrium_iff (hM : p.M ≠ 0) (hk : 0 < p.k₂) :
    (∃ x, p.field x = 0) ↔ |p.Pm - p.k₁| ≤ p.k₂ := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨-, hP⟩ := (p.field_eq_zero_iff hM x).mp hx
    have hP' : p.Pm - p.k₁ = p.k₂ * Real.sin (x 0 - p.k₃) := by
      simp only [Pe] at hP; linarith
    rw [hP', abs_mul, abs_of_pos hk]
    exact mul_le_of_le_one_right hk.le (Real.abs_sin_le_one _)
  · intro h
    have ha : |(p.Pm - p.k₁) / p.k₂| ≤ 1 := by
      rw [abs_div, abs_of_pos hk, div_le_one hk]; exact h
    refine ⟨mkState (Real.arcsin ((p.Pm - p.k₁) / p.k₂) + p.k₃) 0, ?_⟩
    rw [p.field_eq_zero_iff hM]
    refine ⟨by simp, ?_⟩
    simp only [mkState_zero, Pe, add_sub_cancel_right]
    rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]
    field_simp
    ring

/-- Normalized load `a = (P_m − k₁) / k₂`. -/
def loadRatio : ℝ := (p.Pm - p.k₁) / p.k₂

/-- Closed-form stable equilibrium angle `δ_s = arcsin a + k₃`. -/
def deltaS : ℝ := Real.arcsin p.loadRatio + p.k₃

/-- Closed-form unstable equilibrium angle `δ_u = π − arcsin a + k₃`. -/
def deltaU : ℝ := Real.pi - Real.arcsin p.loadRatio + p.k₃

@[powerlib_foundation] theorem abs_loadRatio_le (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| ≤ p.k₂) :
    |p.loadRatio| ≤ 1 := by
  rw [loadRatio, abs_div, abs_of_pos hk, div_le_one hk]; exact h

@[powerlib_foundation] theorem abs_loadRatio_lt (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    |p.loadRatio| < 1 := by
  rw [loadRatio, abs_div, abs_of_pos hk, div_lt_one hk]; exact h

@[powerlib_foundation] theorem sin_loadRatio (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| ≤ p.k₂) :
    p.k₂ * Real.sin (Real.arcsin p.loadRatio) = p.Pm - p.k₁ := by
  have ha := p.abs_loadRatio_le hk h
  rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2, loadRatio]
  field_simp

@[powerlib_foundation] theorem Pe_deltaS (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| ≤ p.k₂) :
    p.Pe p.deltaS = p.Pm := by
  have := p.sin_loadRatio hk h
  simp only [Pe, deltaS, add_sub_cancel_right]; linarith

@[powerlib_foundation] theorem Pe_deltaU (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| ≤ p.k₂) :
    p.Pe p.deltaU = p.Pm := by
  have := p.sin_loadRatio hk h
  simp only [Pe, deltaU, add_sub_cancel_right, Real.sin_pi_sub]; linarith

/-- `cos(δ_s − k₃) = √(1 − a²) > 0` strictly inside the loadability limit. -/
@[powerlib_foundation] theorem syncCoeff_deltaS_pos (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    0 < p.syncCoeff p.deltaS := by
  have ha := p.abs_loadRatio_lt hk h
  simp only [syncCoeff, deltaS, add_sub_cancel_right, Real.cos_arcsin]
  apply mul_pos hk
  apply Real.sqrt_pos.mpr
  have : p.loadRatio ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg p.loadRatio]
  linarith

/-- `cos(δ_u − k₃) = −√(1 − a²) < 0` strictly inside the loadability limit. -/
@[powerlib_foundation] theorem syncCoeff_deltaU_neg (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    p.syncCoeff p.deltaU < 0 := by
  have hs := p.syncCoeff_deltaS_pos hk h
  simp only [syncCoeff, deltaS, deltaU, add_sub_cancel_right, Real.cos_pi_sub] at hs ⊢
  linarith

/-- The equilibrium set: `ω = 0` and `δ ∈ {δ_s + 2nπ} ∪ {δ_u + 2nπ}` (two equilibria per
period of the power-angle curve). -/
@[powerlib_domain] theorem field_eq_zero_iff_branches (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| ≤ p.k₂) (x : State 2) :
    p.field x = 0 ↔ x 1 = 0 ∧
      ∃ n : ℤ, x 0 = p.deltaS + 2 * n * Real.pi ∨ x 0 = p.deltaU + 2 * n * Real.pi := by
  rw [p.field_eq_zero_iff hM]
  apply and_congr_right
  intro _
  have hsin := p.sin_loadRatio hk h
  have hiff : p.Pe (x 0) = p.Pm ↔
      Real.sin (Real.arcsin p.loadRatio) = Real.sin (x 0 - p.k₃) := by
    simp only [Pe]
    constructor
    · intro he
      have : p.k₂ * Real.sin (x 0 - p.k₃) = p.k₂ * Real.sin (Real.arcsin p.loadRatio) := by
        linarith
      exact (mul_left_cancel₀ hk.ne' this).symm
    · intro he
      rw [← he]; linarith
  rw [hiff, Real.sin_eq_sin_iff]
  constructor
  · rintro ⟨n, hn | hn⟩
    · exact ⟨n, Or.inl (by simp only [deltaS]; linarith)⟩
    · exact ⟨n, Or.inr (by simp only [deltaU]; linarith)⟩
  · rintro ⟨n, hn | hn⟩
    · exact ⟨n, Or.inl (by simp only [deltaS] at hn; linarith)⟩
    · exact ⟨n, Or.inr (by simp only [deltaU] at hn; linarith)⟩

@[powerlib_domain] theorem field_mkState_deltaS (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| ≤ p.k₂) : p.field (mkState p.deltaS 0) = 0 :=
  (p.field_eq_zero_iff hM _).mpr ⟨by simp, by simpa using p.Pe_deltaS hk h⟩

@[powerlib_domain] theorem field_mkState_deltaU (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| ≤ p.k₂) : p.field (mkState p.deltaU 0) = 0 :=
  (p.field_eq_zero_iff hM _).mpr ⟨by simp, by simpa using p.Pe_deltaU hk h⟩

/-! ## Linearization -/

/-- The LTI linearization at angle `δ₀`, in the deviation coordinates `(Δδ, Δω)`. -/
def linearModel (δ₀ : ℝ) : LTI.AutonomousModel 2 := ⟨p.jacobian δ₀⟩

/-- `M · det(sI − J) = M s² + D s + K`, `K = k₂ cos(δ₀ − k₃)`. -/
@[powerlib_foundation] theorem characteristic_polynomial (hM : p.M ≠ 0) (δ₀ : ℝ) (s : ℂ) :
    (p.M : ℂ) * (LTI.characteristicMatrix (p.jacobian δ₀) s).det =
      (p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s + (p.syncCoeff δ₀ : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_two, trace_jacobian, det_jacobian]
  have hM' : (p.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp
  ring

/-- The linearization is Hurwitz iff all coefficients of `M s² + D s + K` are positive
(`M > 0`). -/
@[powerlib_foundation] theorem isHurwitz_jacobian_iff (hM : 0 < p.M) (δ₀ : ℝ) :
    LinearSystems.IsHurwitz (p.jacobian δ₀) ↔ 0 < p.D ∧ 0 < p.syncCoeff δ₀ := by
  rw [Criteria.isHurwitz_fin_two_iff, trace_jacobian, det_jacobian, neg_div,
    neg_lt_zero, div_pos_iff_of_pos_right hM, div_pos_iff_of_pos_right hM]

/-- Exponential stability of the LTI linearization iff `D > 0` and `K > 0` (`M > 0`). -/
@[powerlib_domain] theorem linearModel_exponentiallyStable_iff (hM : 0 < p.M) (δ₀ : ℝ) :
    LTI.ExponentiallyStable (p.linearModel δ₀) ↔ 0 < p.D ∧ 0 < p.syncCoeff δ₀ :=
  (LTI.exponentiallyStable_iff_isHurwitz _).trans (p.isHurwitz_jacobian_iff hM δ₀)

/-- The Jacobian of the nonlinear field is the state matrix of `linearModel`. -/
@[powerlib_foundation] theorem fderiv_field_eq_linearModel (x : State 2) :
    fderiv ℝ p.field x = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (p.linearModel (x 0)).A :=
  p.fderiv_field x

/-! ## Local stability and instability of the nonlinear field -/

/-- An equilibrium with positive synchronizing coefficient (`k₂ cos(δ₀ − k₃) > 0`) is locally
exponentially stable when `M > 0` and `D > 0`. -/
@[powerlib_domain] theorem locallyExponentiallyStable_of_syncCoeff_pos (hM : 0 < p.M)
    (hD : 0 < p.D) {x : State 2} (heq : p.field x = 0) (hK : 0 < p.syncCoeff (x 0)) :
    Dynamics.LocallyExponentiallyStable p.field x :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two (p.jacobian (x 0)) p.contDiff_field
    heq (p.fderiv_field x) (by rw [trace_jacobian, neg_div]; exact neg_neg_of_pos (div_pos hD hM))
    (by rw [det_jacobian]; exact div_pos hK hM)

/-- An equilibrium with negative synchronizing coefficient is unstable (saddle), for every
damping `D` (`M > 0`). -/
@[powerlib_domain] theorem unstable_of_syncCoeff_neg (hM : 0 < p.M) {x : State 2}
    (heq : p.field x = 0) (hK : p.syncCoeff (x 0) < 0) : Dynamics.Unstable p.field x :=
  Criteria.unstable_of_jacobian_det_neg_fin_two (p.jacobian (x 0)) p.contDiff_field heq
    (p.fderiv_field x) (by rw [det_jacobian]; exact div_neg_of_neg_of_pos hK hM)

/-- The closed-form stable equilibrium `(δ_s, 0)` is locally exponentially stable
(`M, D, k₂ > 0`, `|P_m − k₁| < k₂`). -/
@[powerlib_domain] theorem locallyExponentiallyStable_deltaS (hM : 0 < p.M) (hD : 0 < p.D)
    (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    Dynamics.LocallyExponentiallyStable p.field (mkState p.deltaS 0) :=
  p.locallyExponentiallyStable_of_syncCoeff_pos hM hD (p.field_mkState_deltaS hM.ne' hk h.le)
    (by simpa using p.syncCoeff_deltaS_pos hk h)

/-- The closed-form equilibrium `(δ_u, 0)` is unstable for every damping
(`M, k₂ > 0`, `|P_m − k₁| < k₂`). -/
@[powerlib_domain] theorem unstable_deltaU (hM : 0 < p.M) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) : Dynamics.Unstable p.field (mkState p.deltaU 0) :=
  p.unstable_of_syncCoeff_neg hM (p.field_mkState_deltaU hM.ne' hk h.le)
    (by simpa using p.syncCoeff_deltaU_neg hk h)

/-! ## Energy function and Lyapunov stability (including `D = 0`) -/

/-- Potential energy relative to `δ₀`: `U(δ) = ∫_{δ₀}^{δ} (P_e − P_m)`. -/
def potential (δ₀ δ : ℝ) : ℝ :=
  -(p.Pm - p.k₁) * (δ - δ₀) - p.k₂ * (Real.cos (δ - p.k₃) - Real.cos (δ₀ - p.k₃))

/-- Kinetic plus potential energy `W(δ, ω) = ½ M ω² + U(δ)`. -/
def energy (δ₀ : ℝ) (x : State 2) : ℝ := p.M / 2 * x 1 ^ 2 + p.potential δ₀ (x 0)

@[powerlib_foundation] theorem hasDerivAt_potential (δ₀ δ : ℝ) :
    HasDerivAt (p.potential δ₀) (p.Pe δ - p.Pm) δ := by
  have h := (((hasDerivAt_id δ).sub_const δ₀).const_mul (-(p.Pm - p.k₁))).sub
    ((((Real.hasDerivAt_cos (δ - p.k₃)).comp δ ((hasDerivAt_id δ).sub_const p.k₃)).sub_const
      (Real.cos (δ₀ - p.k₃))).const_mul p.k₂)
  convert h using 1
  · funext y; simp [potential]
  · simp [Pe]; ring

@[simp, powerlib_foundation] theorem potential_self (δ₀ : ℝ) : p.potential δ₀ δ₀ = 0 := by
  simp [potential]

@[powerlib_foundation] theorem contDiff_energy (δ₀ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (p.energy δ₀) := by
  unfold energy potential
  fun_prop

@[powerlib_foundation] theorem hasFDerivAt_energy (δ₀ : ℝ) (x : State 2) :
    HasFDerivAt (p.energy δ₀)
      ((p.M * x 1) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ) +
        (p.Pe (x 0) - p.Pm) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ))
      x := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hU := (p.hasDerivAt_potential δ₀ (x 0)).comp_hasFDerivAt x h0
  have h := ((h1.pow 2).const_mul (p.M / 2)).add hU
  convert h using 1
  · funext y; simp [energy]
  apply ContinuousLinearMap.ext; intro v
  simp
  ring

/-- Lie derivative of the energy along the full nonlinear field: `Ẇ = −D ω²`. -/
@[powerlib_foundation] theorem energy_lie (hM : p.M ≠ 0) (δ₀ : ℝ) (x : State 2) :
    fderiv ℝ (p.energy δ₀) x (p.field x) = -p.D * x 1 ^ 2 := by
  rw [(p.hasFDerivAt_energy δ₀ x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, PiLp.proj_apply,
    smul_eq_mul, field_apply_one, field_apply_zero, accel]
  field_simp
  ring

/-- The potential is positive on a punctured neighbourhood of an equilibrium angle where the
synchronizing coefficient stays positive. -/
@[powerlib_foundation] theorem potential_pos {δ₀ r δ : ℝ} (hbal : p.Pe δ₀ = p.Pm)
    (hr : ∀ θ, |θ - δ₀| < r → 0 < p.syncCoeff θ) (hδ : |δ - δ₀| < r) (hne : δ ≠ δ₀) :
    0 < p.potential δ₀ δ := by
  set g : ℝ → ℝ := fun θ => p.Pe θ - p.Pm with hg
  have hgd : ∀ θ, HasDerivAt g (p.syncCoeff θ) θ := by
    intro θ
    have h := (((Real.hasDerivAt_sin (θ - p.k₃)).comp θ ((hasDerivAt_id θ).sub_const p.k₃)).const_mul
      p.k₂).const_add p.k₁ |>.sub_const p.Pm
    convert h using 1
    · funext y; simp [hg, Pe]
    · simp [syncCoeff]
  have hg0 : g δ₀ = 0 := by simp [hg, hbal]
  have hgmono : StrictMonoOn g (Ioo (δ₀ - r) (δ₀ + r)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact fun θ _ => (hgd θ).continuousAt.continuousWithinAt
    · intro θ hθ
      rw [interior_Ioo] at hθ
      rw [(hgd θ).deriv]
      apply hr
      rw [abs_lt]; constructor <;> linarith [hθ.1, hθ.2]
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg _) hδ
  have hmem0 : δ₀ ∈ Ioo (δ₀ - r) (δ₀ + r) := ⟨by linarith, by linarith⟩
  obtain ⟨hδ1, hδ2⟩ := abs_lt.mp hδ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hanti : StrictAntiOn (p.potential δ₀) (Icc δ δ₀) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact fun θ _ => (p.hasDerivAt_potential δ₀ θ).continuousAt.continuousWithinAt
      · intro θ hθ
        rw [interior_Icc] at hθ
        rw [(p.hasDerivAt_potential δ₀ θ).deriv]
        have : g θ < g δ₀ := hgmono ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ hmem0 hθ.2
        simpa [hg, hbal] using this
    have := hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    simpa using this
  · have hmono : StrictMonoOn (p.potential δ₀) (Icc δ₀ δ) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact fun θ _ => (p.hasDerivAt_potential δ₀ θ).continuousAt.continuousWithinAt
      · intro θ hθ
        rw [interior_Icc] at hθ
        rw [(p.hasDerivAt_potential δ₀ θ).deriv]
        have : g δ₀ < g θ := hgmono hmem0 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ hθ.1
        simpa [hg, hbal] using this
    have := hmono ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt
    simpa using this

/-- With nonnegative damping (in particular `D = 0`, the conservative swing equation), every
equilibrium with positive synchronizing coefficient is Lyapunov stable: the energy
`½ M ω² + U(δ)` is a local Lyapunov function (`M > 0`). -/
@[powerlib_domain] theorem lyapunovStable_of_syncCoeff_pos (hM : 0 < p.M) (hD : 0 ≤ p.D)
    {x₀ : State 2} (heq : p.field x₀ = 0) (hK : 0 < p.syncCoeff (x₀ 0)) :
    Dynamics.LyapunovStable p.field x₀ := by
  obtain ⟨h1, hbal⟩ := (p.field_eq_zero_iff hM.ne' x₀).mp heq
  have hcont : Continuous p.syncCoeff := by unfold syncCoeff; fun_prop
  obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hcont) (x₀ 0) hK
  have hr' : ∀ θ, |θ - x₀ 0| < r → 0 < p.syncCoeff θ := fun θ hθ =>
    hr (by simpa [Real.dist_eq] using hθ)
  apply Dynamics.lyapunov_stable (D := {x : State 2 | |x 0 - x₀ 0| < r}) (V := p.energy (x₀ 0))
    (by norm_num)
  refine ⟨?_, ?_, (p.contDiff_energy (k := 1) _).continuous, (p.contDiff_energy (k := 1) _).differentiable
    (by norm_num), ?_, ?_, ?_⟩
  · exact isOpen_lt (by fun_prop) continuous_const
  · simpa using hr0
  · simp [energy, h1]
  · intro x hx hne
    have hx' : |x 0 - x₀ 0| < r := hx
    by_cases h0 : x 0 = x₀ 0
    · have h1' : x 1 ≠ 0 := by
        intro h1'; apply hne; exact state_ext h0 (by rw [h1', h1])
      have : 0 < p.M / 2 * x 1 ^ 2 := by positivity
      simpa [energy, h0] using this
    · have hU := p.potential_pos hbal hr' hx' h0
      have : 0 ≤ p.M / 2 * x 1 ^ 2 := by positivity
      simp only [energy]; linarith
  · intro x _
    rw [p.energy_lie hM.ne']
    nlinarith [sq_nonneg (x 1)]

/-- The closed-form stable equilibrium `(δ_s, 0)` is Lyapunov stable for every `D ≥ 0`,
in particular for the undamped swing equation. -/
@[powerlib_domain] theorem lyapunovStable_deltaS (hM : 0 < p.M) (hD : 0 ≤ p.D) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) : Dynamics.LyapunovStable p.field (mkState p.deltaS 0) :=
  p.lyapunovStable_of_syncCoeff_pos hM hD (p.field_mkState_deltaS hM.ne' hk h.le)
    (by simpa using p.syncCoeff_deltaS_pos hk h)

/-! ## Global existence of solutions -/

/-- The swing field is globally Lipschitz (`sin` is `1`-Lipschitz). -/
@[powerlib_foundation] theorem lipschitzWith_field :
    LipschitzWith ⟨1 + |p.D / p.M| + |p.k₂ / p.M|, by positivity⟩ p.field := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  have hx0 := abs_coord_le (x - y) 0
  have hx1 := abs_coord_le (x - y) 1
  simp only [PiLp.sub_apply] at hx0 hx1
  have hs := Real.abs_sin_sub_sin_le (x 0 - p.k₃) (y 0 - p.k₃)
  have hsub : x 0 - p.k₃ - (y 0 - p.k₃) = x 0 - y 0 := by ring
  rw [hsub] at hs
  refine (norm_state_le _).trans ?_
  simp only [PiLp.sub_apply, field_apply_zero, field_apply_one, accel, Pe]
  have he : (p.Pm - (p.k₁ + p.k₂ * Real.sin (x 0 - p.k₃)) - p.D * x 1) / p.M -
      (p.Pm - (p.k₁ + p.k₂ * Real.sin (y 0 - p.k₃)) - p.D * y 1) / p.M =
      -(p.k₂ / p.M) * (Real.sin (x 0 - p.k₃) - Real.sin (y 0 - p.k₃)) -
        (p.D / p.M) * (x 1 - y 1) := by ring
  rw [he]
  have h2 : |-(p.k₂ / p.M) * (Real.sin (x 0 - p.k₃) - Real.sin (y 0 - p.k₃)) -
      (p.D / p.M) * (x 1 - y 1)| ≤ |p.k₂ / p.M| * ‖x - y‖ + |p.D / p.M| * ‖x - y‖ := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hs.trans hx0) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
  change _ ≤ (1 + |p.D / p.M| + |p.k₂ / p.M|) * ‖x - y‖
  nlinarith [abs_nonneg (p.k₂ / p.M), abs_nonneg (p.D / p.M), norm_nonneg (x - y)]

/-- Every initial state has a solution on the whole forward time ray. -/
@[powerlib_domain] theorem forwardComplete : Dynamics.ForwardComplete p.field :=
  Dynamics.forwardComplete_of_lipschitzWith p.lipschitzWith_field

/-! ## Overdamping threshold -/

/-- At an equilibrium, all eigenvalues of the linearization are real (overdamped or critically
damped local response) iff `D² ≥ 4 M K`, `K = k₂ cos(δ₀ − k₃)` (`M > 0`). -/
@[powerlib_foundation] theorem eigenvalues_real_iff (hM : 0 < p.M) (δ₀ : ℝ) :
    (∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
        (p.jacobian δ₀).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.im = 0) ↔
      4 * p.M * p.syncCoeff δ₀ ≤ p.D ^ 2 := by
  rw [Criteria.eigenvalues_real_iff_discriminant_nonneg, trace_jacobian, det_jacobian]
  have hM2 : 0 < p.M ^ 2 := by positivity
  have he : (-p.D / p.M) ^ 2 - 4 * (p.syncCoeff δ₀ / p.M) =
      (p.D ^ 2 - 4 * p.M * p.syncCoeff δ₀) / p.M ^ 2 := by
    field_simp
  rw [he, div_nonneg_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · linarith
    · linarith
  · intro h; left; exact ⟨by linarith, hM2.le⟩

end SwingParams
end powerlib.Synchronous
