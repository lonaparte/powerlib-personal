import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.State
import theorem.Flow.Certificate
import theorem.Flow.Shift
import theorem.Linear.Family
import theorem.TMIO.ClaimElab

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
  handled segment by segment in `theorem/Synchronous/FaultSequence.lean`).
* Conclusions are about equilibria of the full nonlinear field (equilibrium set, local
  exponential stability, instability, Lyapunov stability via the energy function) and about
  the LTI linearization; global existence of solutions (forward completeness) follows from
  a global Lipschitz bound.

Family and connection conclusions.
* A complete system (`Swing.Model`) is a parameter set `p : SwingParams` together with a selected
  angle `δ*`; the system map reads it as the autonomous swing field translated so that the
  selected point `(δ*, 0)` is the origin, `z ↦ f(z + (δ*, 0))` (`Swing.family`). Every flow
  sentence is invariant under this translation (`Flow.Property.holds_shift_iff`), so the sentences
  speak about `(δ*, 0)` itself.
* The requirement language is static: power balance `P_e(δ*) = P_m`, positive inertia, positive or
  nonnegative damping, positive synchronizing coefficient `K = k₂ cos(δ* − k₃)`, and a
  destabilizing sign (`K < 0` or `D < 0`). Local exponential and local asymptotic stability
  translate into balance, inertia, damping and synchronization; Lyapunov stability into the same
  with nonnegative damping (the energy function, including the undamped machine); instability
  into balance, inertia and a destabilizing sign; passivity into nothing (exact); the global
  sentences, decay rates, sampled contraction and conservation into the whole, inconsistent,
  language (unavailable translation coverage).
* `Swing.chain_le_semantics`: the translation chain lies below the semantics connection.
  `Swing.not_exact_locallyExponentiallyStable` (and the Lyapunov / asymptotic versions) is a
  boundary witness: a model with negative inertia, negative damping and negative synchronizing
  coefficient is locally exponentially stable without meeting the requirements, so the local
  translations are sound but not exact. Within positive inertia the local exponential translation
  is exact (`Swing.exactUnder_locallyExponentiallyStable`): by the converse linearization theorem
  (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`) local exponential stability of
  `(δ*, 0)` holds exactly when it is an equilibrium (power balance) with a Hurwitz Jacobian
  (`D > 0`, `K > 0`). Exactness of the local asymptotic and Lyapunov translations under positive
  inertia is not claimed (UNPROVED: a degenerate slope `K = 0` or `D = 0` is not decided by the
  linearization). The instability translation is not exact (`Swing.not_exact_unstable`):
  instability is the failure of Lyapunov stability, so an unbalanced model
  (`Swing.offEquilibrium`) is unstable (`Swing.offEquilibrium_mem_den_unstable`,
  `Dynamics.unstable_of_ne_zero`) while the translation asks for power balance.
* The linearization at the selected angle is a second family on the same models
  (`Swing.Linearized.family`, the linear plant of the Jacobian). Within positive inertia its
  attractive sentences and sampled contraction are translated exactly
  (`Swing.Linearized.exactUnder_hurwitz`): `M s² + D s + K` is Hurwitz iff `D > 0` and `K > 0`
  (`Swing.Linearized.mem_den_iff`, formerly `linearModel_exponentiallyStable_iff`).
* The former public behavioural theorems on the untranslated field (`locallyExponentiallyStable_*`,
  `unstable_*`, `lyapunovStable_*`, `forwardComplete`) are private implementation evidence; their
  conclusions are published as the connection statements `Swing.mem_den_*`,
  `Swing.deltaS_mem_den_*`, `Swing.deltaU_mem_den_unstable`. The equilibrium-set theorems are
  static evidence on the model. Forward completeness is not a sentence; other modules obtain it
  from the public Lipschitz bound `lipschitzWith_field` and `Flow.forwardComplete_of_lipschitzWith`.
* The former LTI object `linearModel` is replaced by the linear plant `Swing.Linearized.plant`;
  `fderiv_point_eq_plant` identifies it with the Jacobian of the nonlinear field.

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

/-! ## Equilibria (static evidence) -/

/-- Equilibria of the full field: zero frequency deviation and power balance.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_iff (hM : p.M ≠ 0) (x : State 2) :
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
`|P_m − k₁| ≤ k₂` (`k₂ > 0`). Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem exists_equilibrium_iff (hM : p.M ≠ 0) (hk : 0 < p.k₂) :
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
period of the power-angle curve). Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_iff_branches (hM : p.M ≠ 0) (hk : 0 < p.k₂)
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

/-- `(δ_s, 0)` is an equilibrium. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_mkState_deltaS (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| ≤ p.k₂) : p.field (mkState p.deltaS 0) = 0 :=
  (p.field_eq_zero_iff hM _).mpr ⟨by simp, by simpa using p.Pe_deltaS hk h⟩

/-- `(δ_u, 0)` is an equilibrium. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_mkState_deltaU (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| ≤ p.k₂) : p.field (mkState p.deltaU 0) = 0 :=
  (p.field_eq_zero_iff hM _).mpr ⟨by simp, by simpa using p.Pe_deltaU hk h⟩

/-! ## Linearization (static) -/

/-- `M · det(sI − J) = M s² + D s + K`, `K = k₂ cos(δ₀ − k₃)`. -/
@[powerlib_foundation] theorem characteristic_polynomial (hM : p.M ≠ 0) (δ₀ : ℝ) (s : ℂ) :
    (p.M : ℂ) * (Linear.characteristicMatrix (p.jacobian δ₀) s).det =
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

/-! ## Local stability and instability of the nonlinear field (implementation evidence)

Behavioural theorems at an equilibrium of the untranslated field. They are private: the public
conclusions are the connection statements of `Swing.family` below. -/

/-- An equilibrium with positive synchronizing coefficient (`k₂ cos(δ₀ − k₃) > 0`) is locally
exponentially stable when `M > 0` and `D > 0`. -/
private theorem locallyExponentiallyStable_of_syncCoeff_pos (hM : 0 < p.M)
    (hD : 0 < p.D) {x : State 2} (heq : p.field x = 0) (hK : 0 < p.syncCoeff (x 0)) :
    LocallyExponentiallyStable p.field x :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two (p.jacobian (x 0)) p.contDiff_field
    heq (p.fderiv_field x) (by rw [trace_jacobian, neg_div]; exact neg_neg_of_pos (div_pos hD hM))
    (by rw [det_jacobian]; exact div_pos hK hM)

/-- An equilibrium with negative synchronizing coefficient is unstable (saddle), for every
damping `D` (`M > 0`). -/
private theorem unstable_of_syncCoeff_neg (hM : 0 < p.M) {x : State 2}
    (heq : p.field x = 0) (hK : p.syncCoeff (x 0) < 0) : Unstable p.field x :=
  Criteria.unstable_of_jacobian_det_neg_fin_two (p.jacobian (x 0)) p.contDiff_field heq
    (p.fderiv_field x) (by rw [det_jacobian]; exact div_neg_of_neg_of_pos hK hM)

/-- An equilibrium with negative damping is unstable (positive trace), for every synchronizing
coefficient (`M > 0`). -/
private theorem unstable_of_damping_neg (hM : 0 < p.M) {x : State 2}
    (heq : p.field x = 0) (hD : p.D < 0) : Unstable p.field x :=
  Criteria.unstable_of_jacobian_trace_pos_fin_two (p.jacobian (x 0)) p.contDiff_field heq
    (p.fderiv_field x) (by rw [trace_jacobian, neg_div]; exact neg_pos.mpr (div_neg_of_neg_of_pos hD hM))

/-! ## Energy function -/

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
`½ M ω² + U(δ)` is a local Lyapunov function (`M > 0`). Implementation evidence. -/
private theorem lyapunovStable_of_syncCoeff_pos (hM : 0 < p.M) (hD : 0 ≤ p.D)
    {x₀ : State 2} (heq : p.field x₀ = 0) (hK : 0 < p.syncCoeff (x₀ 0)) :
    LyapunovStable p.field x₀ := by
  obtain ⟨h1, hbal⟩ := (p.field_eq_zero_iff hM.ne' x₀).mp heq
  have hcont : Continuous p.syncCoeff := by unfold syncCoeff; fun_prop
  obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hcont) (x₀ 0) hK
  have hr' : ∀ θ, |θ - x₀ 0| < r → 0 < p.syncCoeff θ := fun θ hθ =>
    hr (by simpa [Real.dist_eq] using hθ)
  apply lyapunov_stable (D := {x : State 2 | |x 0 - x₀ 0| < r}) (V := p.energy (x₀ 0))
    (by norm_num)
  refine ⟨?_, ?_, (p.contDiff_energy (k := 1) _).continuous,
    (p.contDiff_energy (k := 1) _).differentiable (by norm_num), ?_, ?_, ?_⟩
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

/-- Every initial state has a solution on the whole forward time ray. Implementation evidence:
forward completeness is not a sentence; it is the generic `Flow.forwardComplete_of_lipschitzWith`
applied to the public bound `lipschitzWith_field`. -/
private theorem forwardComplete : Flow.ForwardComplete p.field :=
  Flow.forwardComplete_of_lipschitzWith p.lipschitzWith_field

/-! ## Overdamping threshold (static) -/

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

/-! ## The swing family -/

namespace Swing

/-- A swing model read about a selected operating point `(δ*, 0)`: the parameters and the
selected angle `δ*`. -/
structure Model where
  /-- The swing parameters. -/
  p : SwingParams
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The selected point `(δ*, 0)`. -/
def Model.point (m : Model) : State 2 := mkState m.δ 0

/-- The swing field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 2) : State 2 := m.p.field (z + m.point)

@[simp, powerlib_foundation] theorem Model.point_zero (m : Model) : m.point 0 = m.δ := by
  simp [Model.point]

@[simp, powerlib_foundation] theorem Model.point_one (m : Model) : m.point 1 = 0 := by
  simp [Model.point]

/-- The Jacobian of the nonlinear field at the selected point is the Jacobian at `δ*`. -/
@[powerlib_foundation] theorem Model.fderiv_point (m : Model) :
    fderiv ℝ m.p.field m.point =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (m.p.jacobian m.δ) := by
  rw [m.p.fderiv_field, Model.point_zero]

/-- Static requirements on swing models. -/
inductive Requirement
  /-- Power balance at the selected angle: `P_e(δ*) = P_m`. -/
  | balanced
  /-- Positive inertia `M > 0`. -/
  | inertia
  /-- Positive damping `D > 0`. -/
  | damped
  /-- Nonnegative damping `D ≥ 0` (includes the undamped machine). -/
  | dampingNonneg
  /-- No damping, `D = 0`. -/
  | undamped
  /-- Positive synchronizing coefficient `K = k₂ cos(δ* − k₃) > 0`. -/
  | synchronizing
  /-- A destabilizing sign: `K < 0` (saddle) or `D < 0` (negative damping). -/
  | destabilizing

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.p.Pe m.δ = m.p.Pm
  | .inertia => 0 < m.p.M
  | .damped => 0 < m.p.D
  | .dampingNonneg => 0 ≤ m.p.D
  | .undamped => m.p.D = 0
  | .synchronizing => 0 < m.p.syncCoeff m.δ
  | .destabilizing => m.p.syncCoeff m.δ < 0 ∨ m.p.D < 0

/-- The translation of the sentences for the nonlinear swing field: local exponential and local
asymptotic stability into balance, inertia, damping and synchronization; Lyapunov stability into
the same with nonnegative damping; instability into balance, inertia and a destabilizing sign;
passivity into nothing. The global sentences, decay rates, sampled contraction and conservation
are translated into the whole language, which no model meets (unavailable translation coverage,
not a usable translation). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable => {.balanced, .inertia, .dampingNonneg, .synchronizing}
  | .flow .locallyAsymptoticallyStable | .flow .locallyExponentiallyStable =>
      {.balanced, .inertia, .damped, .synchronizing}
  | .flow .unstable => {.balanced, .inertia, .destabilizing}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The swing family: every model read as its field translated to the selected point. -/
def family : Family Model Requirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

/-- A flow sentence of a model is the sentence of the untranslated field at the selected point. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

private theorem point_eq_zero {m : Model} (hM : 0 < m.p.M) (hb : m.p.Pe m.δ = m.p.Pm) :
    m.p.field m.point = 0 :=
  (m.p.field_eq_zero_iff hM.ne' _).mpr ⟨by simp, by simpa using hb⟩

private theorem les_of {m : Model} (hM : 0 < m.p.M) (hD : 0 < m.p.D)
    (hb : m.p.Pe m.δ = m.p.Pm) (hK : 0 < m.p.syncCoeff m.δ) :
    LocallyExponentiallyStable m.p.field m.point :=
  m.p.locallyExponentiallyStable_of_syncCoeff_pos hM hD (point_eq_zero hM hb) (by simpa using hK)

private theorem ls_of {m : Model} (hM : 0 < m.p.M) (hD : 0 ≤ m.p.D)
    (hb : m.p.Pe m.δ = m.p.Pm) (hK : 0 < m.p.syncCoeff m.δ) :
    LyapunovStable m.p.field m.point :=
  m.p.lyapunovStable_of_syncCoeff_pos hM hD (point_eq_zero hM hb) (by simpa using hK)

private theorem unstable_of {m : Model} (hM : 0 < m.p.M) (hb : m.p.Pe m.δ = m.p.Pm)
    (hs : m.p.syncCoeff m.δ < 0 ∨ m.p.D < 0) : Unstable m.p.field m.point := by
  rcases hs with hK | hD
  · exact m.p.unstable_of_syncCoeff_neg hM (point_eq_zero hM hb) (by simpa using hK)
  · exact m.p.unstable_of_damping_neg hM (point_eq_zero hM hb) hD

/-! ### Soundness of the translation -/

/-- No model is both damped and synchronizing while having a destabilizing sign: the whole
requirement language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : 0 < m.p.D := h .damped
  have h2 : 0 < m.p.syncCoeff m.δ := h .synchronizing
  rcases (h .destabilizing : Meets m .destabilizing) with h3 | h3 <;> linarith

/-- Every translation of the swing family is sound: its translation chain lies below its
semantics connection. Balance, inertia, damping and synchronization prove the local sentences by
linearization (LeanForControl's theorems at the selected point, moved to the origin); with
nonnegative damping the energy `½ M ω² + U(δ)` is a local Lyapunov function; a destabilizing sign
proves instability; passivity holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · rw [mem_den_flow_iff]
    cases P
    case lyapunovStable =>
      exact ls_of (hm .inertia (by simp [translate])) (hm .dampingNonneg (by simp [translate]))
        (hm .balanced (by simp [translate])) (hm .synchronizing (by simp [translate]))
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (les_of (hm .inertia (by simp [translate])) (hm .damped (by simp [translate]))
          (hm .balanced (by simp [translate])) (hm .synchronizing (by simp [translate])))
    case locallyExponentiallyStable =>
      exact les_of (hm .inertia (by simp [translate])) (hm .damped (by simp [translate]))
        (hm .balanced (by simp [translate])) (hm .synchronizing (by simp [translate]))
    case unstable =>
      exact unstable_of (hm .inertia (by simp [translate])) (hm .balanced (by simp [translate]))
        (hm .destabilizing (by simp [translate]))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-! ### Members of the local denotations -/

/-- Positive inertia, damping and synchronizing coefficient at a balanced angle place a swing
model in local exponential stability. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model) (hM : 0 < m.p.M)
    (hD : 0 < m.p.D) (hb : m.p.Pe m.δ = m.p.Pm) (hK : 0 < m.p.syncCoeff m.δ) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (les_of hM hD hb hK)

/-- The same conditions place a swing model in local asymptotic stability. -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable (m : Model) (hM : 0 < m.p.M)
    (hD : 0 < m.p.D) (hb : m.p.Pe m.δ = m.p.Pm) (hK : 0 < m.p.syncCoeff m.δ) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (Flow.locallyExponentiallyStable_localAsymptoticStable
    (les_of hM hD hb hK))

/-- With nonnegative damping — in particular the undamped swing equation — positive inertia and
synchronizing coefficient at a balanced angle place a swing model in Lyapunov stability (energy
function). -/
@[powerlib_domain] theorem mem_den_lyapunovStable (m : Model) (hM : 0 < m.p.M)
    (hD : 0 ≤ m.p.D) (hb : m.p.Pe m.δ = m.p.Pm) (hK : 0 < m.p.syncCoeff m.δ) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (ls_of hM hD hb hK)

/-- A balanced angle with negative synchronizing coefficient (saddle) places a swing model with
positive inertia in instability, for every damping. -/
@[powerlib_domain] theorem mem_den_unstable (m : Model) (hM : 0 < m.p.M)
    (hb : m.p.Pe m.δ = m.p.Pm) (hK : m.p.syncCoeff m.δ < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (unstable_of hM hb (Or.inl hK))

/-- Negative damping places a balanced swing model with positive inertia in instability, for
every synchronizing coefficient. -/
@[powerlib_domain] theorem mem_den_unstable_of_damping_neg (m : Model) (hM : 0 < m.p.M)
    (hb : m.p.Pe m.δ = m.p.Pm) (hD : m.p.D < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (unstable_of hM hb (Or.inr hD))

/-- The closed-form stable equilibrium `(δ_s, 0)` is locally exponentially stable
(`M, D, k₂ > 0`, `|P_m − k₁| < k₂`). -/
@[powerlib_domain] theorem deltaS_mem_den_locallyExponentiallyStable (p : SwingParams)
    (hM : 0 < p.M) (hD : 0 < p.D) (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    connection% (Model.mk p p.deltaS ∈ family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_locallyExponentiallyStable _ hM hD (p.Pe_deltaS hk h.le) (p.syncCoeff_deltaS_pos hk h)

/-- The closed-form equilibrium `(δ_u, 0)` is unstable for every damping
(`M, k₂ > 0`, `|P_m − k₁| < k₂`). -/
@[powerlib_domain] theorem deltaU_mem_den_unstable (p : SwingParams) (hM : 0 < p.M)
    (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    connection% (Model.mk p p.deltaU ∈ family.den (.flow .unstable)) :=
  mem_den_unstable _ hM (p.Pe_deltaU hk h.le) (p.syncCoeff_deltaU_neg hk h)

/-- The closed-form stable equilibrium `(δ_s, 0)` is Lyapunov stable for every `D ≥ 0`,
in particular for the undamped swing equation. -/
@[powerlib_domain] theorem deltaS_mem_den_lyapunovStable (p : SwingParams) (hM : 0 < p.M)
    (hD : 0 ≤ p.D) (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    connection% (Model.mk p p.deltaS ∈ family.den (.flow .lyapunovStable)) :=
  mem_den_lyapunovStable _ hM hD (p.Pe_deltaS hk h.le) (p.syncCoeff_deltaS_pos hk h)

/-! ### Exactness within positive inertia -/

/-- Within positive inertia, local exponential stability is translated exactly: a swing model with
`M > 0` is locally exponentially stable at `(δ*, 0)` exactly when the angle is balanced, damped and
synchronizing. Converse linearization: local exponential stability of the `C¹` swing field forces
an equilibrium whose Jacobian `[[0, 1], [−K/M, −D/M]]` is Hurwitz. -/
@[powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.inertia} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  unfold Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets ({.balanced, .inertia, .damped, .synchronizing} ∪ {.inertia}) = _
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_inter_iff]
  constructor
  · intro h
    have hM : 0 < m.p.M := h .inertia (by simp)
    refine ⟨mem_den_flow_iff.mpr ?_, fun q hq => by rw [hq]; exact hM⟩
    change LocallyExponentiallyStable _ _
    rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ m.p.contDiff_field
      m.fderiv_point, m.p.field_eq_zero_iff hM.ne', m.p.isHurwitz_jacobian_iff hM]
    have hb : m.p.Pe m.δ = m.p.Pm := h .balanced (by simp)
    exact ⟨⟨by simp [Model.point], by simpa [Model.point] using hb⟩,
      h .damped (by simp), h .synchronizing (by simp)⟩
  · rintro ⟨hd, hI⟩ q hq
    have hM : 0 < m.p.M := hI .inertia rfl
    have hles : LocallyExponentiallyStable m.p.field m.point := mem_den_flow_iff.mp hd
    rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ m.p.contDiff_field
      m.fderiv_point, m.p.field_eq_zero_iff hM.ne', m.p.isHurwitz_jacobian_iff hM] at hles
    obtain ⟨⟨-, hb⟩, hD, hK⟩ := hles
    rcases hq with ((rfl | rfl | rfl | rfl) | rfl)
    · show m.p.Pe m.δ = m.p.Pm
      simpa [Model.point] using hb
    · exact hM
    · exact hD
    · exact hK
    · exact hM

/-! ### Boundary witness: negative inertia -/

/-- A model with `M = D = k₂ = −1` (all three coefficients of `M s² + D s + K` negative), balanced
at `δ* = 0`. -/
def negativeInertia : Model := ⟨⟨-1, -1, 0, 0, -1, 0⟩, 0⟩

/-- The negative-inertia model is locally exponentially stable: its Jacobian `[[0, 1], [−1, −1]]`
is Hurwitz. -/
@[powerlib_domain] theorem negativeInertia_mem_den_locallyExponentiallyStable :
    connection% (negativeInertia ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr ?_
  have hp : negativeInertia.p.M ≠ 0 := by norm_num [negativeInertia]
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_two _ negativeInertia.p.contDiff_field
    ((negativeInertia.p.field_eq_zero_iff hp _).mpr ⟨by simp, by simp [negativeInertia,
      SwingParams.Pe]⟩) negativeInertia.fderiv_point ?_ ?_
  · rw [SwingParams.trace_jacobian]; norm_num [negativeInertia]
  · rw [SwingParams.det_jacobian]; norm_num [negativeInertia, SwingParams.syncCoeff]

private theorem negativeInertia_not_meets : ¬ Meets negativeInertia .inertia := by
  norm_num [Meets, negativeInertia]

/-- The local exponential translation is sound but not exact: the negative-inertia model is
locally exponentially stable without positive inertia. -/
@[powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeInertia_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  exact negativeInertia_not_meets (hmem .inertia (by simp [family, translate]))

/-- The local asymptotic translation is sound but not exact (the same witness). -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeInertia_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  have hmem' : negativeInertia ∈ family.den (.flow .locallyAsymptoticallyStable) :=
    family_isAutonomous.mem_den_flow.mpr (Flow.locallyExponentiallyStable_localAsymptoticStable
      (family_isAutonomous.mem_den_flow.mp hmem))
  rw [← h, TMIO.mem_realize] at hmem'
  exact negativeInertia_not_meets (hmem' .inertia (by simp [family, translate]))

/-- The Lyapunov translation is sound but not exact (the same witness). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeInertia_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  have hmem' : negativeInertia ∈ family.den (.flow .lyapunovStable) :=
    family_isAutonomous.mem_den_flow.mpr
      (LocallyExponentiallyStable.lyapunovStable (family_isAutonomous.mem_den_flow.mp hmem))
  rw [← h, TMIO.mem_realize] at hmem'
  exact negativeInertia_not_meets (hmem' .inertia (by simp [family, translate]))

/-! ## The linearized swing family

The same models read through the linear plant of the Jacobian at the selected angle,
`Δẋ = J(δ*) Δx` in the deviation coordinates `(Δδ, Δω)` (no ports). -/

namespace Linearized

/-- The linear plant of the Jacobian at the selected angle. -/
def plant (m : Model) : Linear.Plant 2 0 := ⟨m.p.jacobian m.δ, 0, 0, 0⟩

/-- The Jacobian of the nonlinear field at the selected point is the state matrix of the
linearized plant. -/
@[powerlib_foundation] theorem fderiv_point_eq_plant (m : Model) :
    fderiv ℝ m.p.field m.point = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (plant m).A :=
  m.fderiv_point

/-- The translation for the linearization: the attractive sentences, sampled contraction and
Lyapunov stability into positive inertia, damping and synchronization; instability into inertia
and a destabilizing sign; conservation into inertia, synchronization and zero damping; passivity
into nothing; decay rates into the whole, inconsistent, language. -/
def translate : Sentence → Set Requirement
  | .flow .unstable => {.inertia, .destabilizing}
  | .flow .conservative => {.inertia, .synchronizing, .undamped}
  | .flow (.decay _) => Set.univ
  | .flow _ => {.inertia, .damped, .synchronizing}
  | .passive => ∅

/-- The linearized swing family. -/
def family : Family Model Requirement 2 0 := ⟨fun m => (plant m).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear plant := fun _ => rfl

private theorem isHurwitz_iff {m : Model} (hM : 0 < m.p.M) :
    LinearSystems.IsHurwitz (plant m).A ↔ 0 < m.p.D ∧ 0 < m.p.syncCoeff m.δ :=
  m.p.isHurwitz_jacobian_iff hM m.δ

/-- The energy matrix `diag(K, M)` is conserved by the undamped linearization. -/
private theorem conserved {m : Model} (hD : m.p.D = 0) (hM : m.p.M ≠ 0) :
    (plant m).Aᵀ * !![m.p.syncCoeff m.δ, 0; 0, m.p.M] +
      !![m.p.syncCoeff m.δ, 0; 0, m.p.M] * (plant m).A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plant, SwingParams.jacobian, hD, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    ring

private theorem unstable_of {m : Model} (hM : 0 < m.p.M)
    (hs : m.p.syncCoeff m.δ < 0 ∨ m.p.D < 0) :
    Unstable (LinearSystems.affineLinearVectorField (plant m).A 0) 0 := by
  obtain ⟨μ, v, hv, heig, hre⟩ : ∃ (μ : ℂ) (v : Fin 2 → ℂ),
      v ≠ 0 ∧ (plant m).A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
    rcases hs with hK | hD
    · exact Criteria.exists_eigenvalue_re_pos_of_det_neg _
        (by rw [show (plant m).A = m.p.jacobian m.δ from rfl, SwingParams.det_jacobian]
            exact div_neg_of_neg_of_pos hK hM)
    · exact Criteria.exists_eigenvalue_re_pos_of_trace_pos _
        (by rw [show (plant m).A = m.p.jacobian m.δ from rfl, SwingParams.trace_jacobian, neg_div]
            exact neg_pos.mpr (div_neg_of_neg_of_pos hD hM))
  exact Linear.unstable_of_eigenvalue 0 hv heig hre

/-- The decay requirement is the whole language: damped and undamped are inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) :=
  Swing.realize_univ

/-- Every translation of the linearized swing family is sound: Hurwitz gives every attractive
sentence, sampled contraction and Lyapunov stability; a destabilizing sign gives an eigenvalue in
the open right half plane; the energy `½ K Δδ² + ½ M Δω²` is conserved without damping; a system
without ports is passive. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  rcases s with P | _
  · have hH : Meets m .inertia → Meets m .damped → Meets m .synchronizing →
        LinearSystems.IsHurwitz (plant m).A := fun hM hD hK => (isHurwitz_iff hM).mpr ⟨hD, hK⟩
    cases P
    case unstable =>
      exact family_isLinear.mem_den_flow.mpr
        (unstable_of (hm .inertia (by simp [translate])) (hm .destabilizing (by simp [translate])))
    case conservative =>
      have hM : 0 < m.p.M := hm .inertia (by simp [translate])
      have hK : 0 < m.p.syncCoeff m.δ := hm .synchronizing (by simp [translate])
      have hD : m.p.D = 0 := hm .undamped (by simp [translate])
      refine family_isLinear.mem_den_conservative (by ext i j; fin_cases i <;> fin_cases j <;> simp)
        (fun v hv => ?_) (conserved hD hM.ne')
      have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hv (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      rcases hv' with h0 | h1
      · have : 0 < v 0 * v 0 := mul_self_pos.mpr h0
        nlinarith [mul_self_nonneg (v 1)]
      · have : 0 < v 1 * v 1 := mul_self_pos.mpr h1
        nlinarith [mul_self_nonneg (v 0)]
    case decay a =>
      have h1 : 0 < m.p.D := hm .damped trivial
      have h2 : m.p.D = 0 := hm .undamped trivial
      exact absurd h2 h1.ne'
    case lyapunovStable =>
      exact family_isLinear.mem_den_flow.mpr (Linear.lyapunovStable_of_isHurwitz 0
        (hH (hm .inertia (by simp [translate])) (hm .damped (by simp [translate]))
          (hm .synchronizing (by simp [translate]))))
    all_goals
      rw [family_isLinear.den_hurwitz (by simp)]
      exact hH (hm .inertia (by simp [translate])) (hm .damped (by simp [translate]))
        (hm .synchronizing (by simp [translate]))
  · exact family.mem_den.mpr (Port.System.passive_of_noPorts _)

/-- Within positive inertia, the attractive sentences and sampled contraction of the linearized
swing equation are translated exactly: `M s² + D s + K` is Hurwitz iff `D > 0` and `K > 0`. -/
@[powerlib_domain] theorem exactUnder_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.ExactUnder {.inertia} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have ht : translate (.flow P) = {.inertia, .damped, .synchronizing} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact absurd hP id
    · rfl
  unfold Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets (translate (.flow P) ∪ {.inertia}) = _
  rw [ht, family_isLinear.den_hurwitz hP]
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    have hM : 0 < m.p.M := h .inertia (by simp)
    exact ⟨(isHurwitz_iff hM).mpr ⟨h .damped (by simp), h .synchronizing (by simp)⟩,
      fun q hq => by rw [hq]; exact hM⟩
  · rintro ⟨hH, hI⟩ q hq
    have hM : 0 < m.p.M := hI .inertia rfl
    obtain ⟨hD, hK⟩ := (isHurwitz_iff hM).mp hH
    rcases hq with ((rfl | rfl | rfl) | rfl)
    · exact hM
    · exact hD
    · exact hK
    · exact hM

/-- The linearization is exponentially stable iff `D > 0` and `K > 0` (`M > 0`); formerly
`linearModel_exponentiallyStable_iff`. -/
@[powerlib_domain] theorem mem_den_iff (m : Model) (hM : 0 < m.p.M) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable) ↔
      m ∈ {m : Model | 0 < m.p.D ∧ 0 < m.p.syncCoeff m.δ}) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz (Or.inl Flow.Property.attractive_globallyExponentiallyStable),
    Set.mem_ofPred_eq, isHurwitz_iff hM]
  rfl

/-- Passivity is translated exactly for the linearization. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  refine Family.exact_of_translate_eq_empty rfl ?_
  ext m
  simp only [Set.mem_univ, iff_true]
  exact family.mem_den.mpr (Port.System.passive_of_noPorts _)

end Linearized

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: `M = P_m = 1`, no damping or electrical power, `δ* = 0`. -/
def offEquilibrium : Model := ⟨⟨1, 0, 1, 0, 0, 0⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Dynamics.unstable_of_ne_zero offEquilibrium.p.contDiff_field
    fun h => ?_)
  rw [offEquilibrium.p.field_eq_zero_iff (by norm_num [offEquilibrium])] at h
  simp [offEquilibrium, Model.point, SwingParams.Pe] at h

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for a balanced angle. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hb : Meets offEquilibrium .balanced := hmem .balanced (by simp [family, translate])
  simp [Meets, offEquilibrium, SwingParams.Pe] at hb

end Swing

end powerlib.Synchronous
