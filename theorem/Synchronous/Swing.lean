import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.State
import theorem.PhasePlane.Planar
import theorem.Flow.Certificate
import theorem.Dynamics.Shift
import theorem.Linear.Family
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.Spectral.Local
import theorem.Spectral.LinearNamed
import theorem.Spectral.Equilibrium
import theorem.SpecialFunctions.Sinusoid

/-! # The sinusoidally coupled swing equation (canonical single-machine model)

The canonical single-machine swing model `SwingParams` with its equilibrium set, linearization and
energy function, read through two families: the nonlinear field about a selected angle
(`Swing.family`) and its linearization (`Swing.Linearized.family`). `Swing.family` is the
canonical family of the classical single machine on an infinite bus: the port-Hamiltonian
classical machine (`ClassicalSM.family`, `theorem/Synchronous/PH.lean`) takes its flow
conclusions from it.

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

Scaffold: `theorem/Swing.agda` (the hub content its spokes read: models, requirements,
translation, published laws); the readings through it are `theorem/DroopSwing.agda`,
`theorem/SaturationSwing.agda` and `theorem/ClassicalMachineSwing.agda`.

Source: work-sync `theory/T-vsg-control.md` §1.2, §1.10; `theory/T-sync-machine.md` §1.9;
`theory/T-transient-stability.md` §1.3, §1.4, §1.7;
`projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md` §1–§3
(overdamping threshold).

Results (static evidence on the model).
* `exists_equilibrium_iff`, `field_eq_zero_iff_branches` — equilibria exist iff the power-angle
  curve reaches `P_m`; the equilibrium set is `ω = 0`, `δ ∈ {δ_s + 2nπ} ∪ {δ_u + 2nπ}`, with
  `syncCoeff_deltaS_pos`, `syncCoeff_deltaU_neg` on the two branches.
* `characteristic_polynomial`, `isHurwitz_jacobian_iff`, `eigenvalues_real_iff` — the
  linearization has `M det(sI − J) = M s² + D s + K`, `K = k₂ cos(δ₀ − k₃)`; it is Hurwitz iff
  `D > 0` and `K > 0`; exact overdamping threshold.
* `energy_lie`, `potential_pos` — the energy `W = ½ M ω² + U(δ)` has `Ẇ = −D ω²`, and the
  potential is positive on a punctured neighbourhood of an equilibrium angle where the
  synchronizing coefficient stays positive.
* `lipschitzWith_field` — the field is globally Lipschitz.

Family and connection conclusions.
* A complete system (`Swing.Model`) is a parameter set `p : SwingParams` together with a selected
  angle `δ*`; the system map reads it as the autonomous swing field translated so that the
  selected point `(δ*, 0)` is the origin, `z ↦ f(z + (δ*, 0))` (`Swing.family`). Every flow
  sentence is invariant under this translation (`Flow.Property.holds_shift_iff`), so the sentences
  speak about `(δ*, 0)` itself.
* The requirement language is static: power balance `P_e(δ*) = P_m`, positive inertia, positive or
  nonnegative damping, positive synchronizing coefficient `K = k₂ cos(δ* − k₃)`, a destabilizing
  sign (`K < 0` or `D < 0`) and a curved power-angle curve (`k₂ ≠ 0`, a context of exactness that
  no local sentence translates into). Local exponential and local asymptotic stability
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
  (`D > 0`, `K > 0`). Within positive inertia the local asymptotic translation is exact as well
  (`Swing.exactUnder_locallyAsymptoticallyStable`), although the linearization does not decide
  the degenerate slopes: an undamped machine conserves its energy, a flat power-angle curve
  (`k₂ = 0`) has a continuum of equilibria, and at a fold of the curve the dissipated energy is
  negative on one side of `(δ*, 0)` (`Swing.potential_fold`,
  `Dynamics.not_localAsymptoticStable_of_lie_nonpos`). The Lyapunov translation is not exact even
  within positive inertia (`Swing.not_exactUnder_lyapunovStable`): the flat-curve machine
  `Swing.flatCurve` (`k₂ = 0`, `D > 0`) is Lyapunov stable with a zero synchronizing coefficient
  (`Swing.flatCurve_mem_den_lyapunovStable`). Within positive inertia its denotation is
  `Swing.mem_den_lyapunovStable_iff_of_inertia`: a balanced angle with `D ≥ 0` and `K > 0`, or a
  flat curve with `D > 0`; a fold of the curve is unstable for every `D ≥ 0`
  (`Swing.Pe_fold`, `Dynamics.unstable_of_lie_nonpos_of_lie_pos`) and an undamped flat curve
  drifts (`Dynamics.unstable_of_chetaev`). Within positive inertia and a curved power-angle curve
  the flat alternative is excluded and the Lyapunov translation is exact
  (`Swing.exactUnder_lyapunovStable`). The instability translation is not exact
  (`Swing.not_exact_unstable`): instability is the failure of Lyapunov stability, so every
  unbalanced model with `M ≠ 0` is unstable (`Swing.mem_den_unstable_of_not_balanced`,
  `Dynamics.unstable_of_ne_zero`), for instance `Swing.offEquilibrium`
  (`Swing.offEquilibrium_mem_den_unstable`), while the translation asks for power balance.
* The linearization at the selected angle is a second family on the same models
  (`Swing.Linearized.family`, the linear plant `Swing.Linearized.plant` of the Jacobian;
  `fderiv_point_eq_plant` identifies it with the Jacobian of the nonlinear field); its
  translation is the linear table (`Spectral.linearTable`). Within positive inertia its
  attractive sentences and sampled contraction are translated exactly
  (`Swing.Linearized.exactUnder_hurwitz`): `M s² + D s + K` is Hurwitz iff `D > 0` and `K > 0`
  (`Swing.Linearized.mem_den_iff`).
* The behavioural theorems on the untranslated field (`locallyExponentiallyStable_*`,
  `unstable_*`, `lyapunovStable_*`, `forwardComplete`) are private implementation evidence; their
  conclusions are published as the connection statements `Swing.mem_den_*`,
  `Swing.deltaS_mem_den_*`, `Swing.deltaU_mem_den_unstable`. The equilibrium-set theorems are
  static evidence on the model. Forward completeness is not a sentence; other modules obtain it
  from the public Lipschitz bound `lipschitzWith_field` and
  `Flow.forwardComplete_of_lipschitzWith`.
* Instances (`theorem/Synchronous/Instances.lean`): VSG / VSM on an infinite bus
  (`k₁ = 0, k₃ = 0, k₂ = E V_g / X_g`), the classical SMIB model (`k₂ = E' V_∞ / X_d'`), and the
  post-fault SMIB curve with line resistance.
* The classical machine on an infinite bus written as a nonlinear port-Hamiltonian system in
  `(δ, p = M ω)` with `P_e = b sin δ` and a mechanical-power port (`ClassicalSM.family`,
  `theorem/Synchronous/PH.lean`) is read through this family, the canonical one: its swing reading
  `ClassicalSM.Model.toSwing` is `⟨⟨M, D, P_m, 0, b, 0⟩, δ*⟩` (`M > 0`, `D ≥ 0`, `b > 0`), and on
  every flow sentence its denotation and its translation are the pullbacks of this family's
  (`ClassicalSM.den_flow_eq_preimage`, `ClassicalSM.mem_den_flow_iff_swing`,
  `ClassicalSM.realize_translate_flow_eq_preimage`, `ClassicalSM.exact_flow_iff`; the zero-input
  pH field is the swing field under `diag(1, M)`, `Dynamics.holds_transport_iff`). Its flow
  conclusions are derived from `Swing.chain_le_semantics`, `Swing.mem_den_*` and
  `Swing.exactUnder_*` (every reading has `M > 0` and `k₂ = b ≠ 0`). Only passivity differs:
  the pH machine is passive exactly when `P_m = 0`, while this family has no port
  (`ClassicalSM.not_den_eq_preimage`).
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

namespace SwingParams

variable (p : SwingParams)

/-- Electrical (export-positive) power-angle curve `P_e(δ) = k₁ + k₂ sin(δ − k₃)`. -/
def Pe (δ : ℝ) : ℝ := p.k₁ + p.k₂ * Real.sin (δ - p.k₃)

/-- Angular acceleration `ω̇ = (P_m − P_e(δ) − D ω) / M`. -/
def accel (δ ω : ℝ) : ℝ := (p.Pm - p.Pe δ - p.D * ω) / p.M

/-- The full nonlinear swing vector field on `(δ, ω)`. -/
def field (x : State 2) : State 2 := PhasePlane.mk (x 1) (p.accel (x 0) (x 1))

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
  · simpa using Dynamics.contDiff_coord (k := k) 1
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
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
    · simp [h0]
    · simp [accel, h0, h1]

/-- Equilibrium existence: the power-angle curve reaches the mechanical power,
`|P_m − k₁| ≤ k₂` (`k₂ > 0`): the zeros of the sinusoid `P_m − k₁ − k₂ sin(δ − k₃)`
(`SpecialFunctions.exists_sinusoid_zero_iff`). Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem exists_equilibrium_iff (hM : p.M ≠ 0) (hk : 0 < p.k₂) :
    (∃ x, p.field x = 0) ↔ |p.Pm - p.k₁| ≤ p.k₂ := by
  rw [← SpecialFunctions.exists_sinusoid_zero_iff (φ := -p.k₃) hk]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨-, hP⟩ := (p.field_eq_zero_iff hM x).mp hx
    refine ⟨x 0, ?_⟩
    rw [← sub_eq_add_neg]
    simp only [Pe] at hP
    linarith
  · rintro ⟨δ, hδ⟩
    refine ⟨PhasePlane.mk δ 0, (p.field_eq_zero_iff hM _).mpr ⟨by simp, ?_⟩⟩
    rw [← sub_eq_add_neg] at hδ
    simp only [PhasePlane.mk_apply_zero, Pe]
    linarith

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
    p.k₂ * Real.sin (Real.arcsin p.loadRatio) = p.Pm - p.k₁ :=
  SpecialFunctions.mul_sin_arcsin_div h hk

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
  simp only [syncCoeff, deltaS, add_sub_cancel_right]
  exact mul_pos hk (SpecialFunctions.cos_arcsin_div_pos h hk)

/-- `cos(δ_u − k₃) = −√(1 − a²) < 0` strictly inside the loadability limit. -/
@[powerlib_foundation] theorem syncCoeff_deltaU_neg (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    p.syncCoeff p.deltaU < 0 := by
  simp only [syncCoeff, deltaU, add_sub_cancel_right]
  exact mul_neg_of_pos_of_neg hk (SpecialFunctions.cos_pi_sub_arcsin_div_neg h hk)

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
    (h : |p.Pm - p.k₁| ≤ p.k₂) : p.field (PhasePlane.mk p.deltaS 0) = 0 :=
  (p.field_eq_zero_iff hM _).mpr ⟨by simp, by simpa using p.Pe_deltaS hk h⟩

/-- `(δ_u, 0)` is an equilibrium. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_mkState_deltaU (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| ≤ p.k₂) : p.field (PhasePlane.mk p.deltaU 0) = 0 :=
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
        intro h1'; apply hne; exact PhasePlane.ext_iff'.2 ⟨h0, by rw [h1', h1]⟩
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
  have hx0 := Dynamics.abs_apply_le_norm (x - y) 0
  have hx1 := Dynamics.abs_apply_le_norm (x - y) 1
  simp only [PiLp.sub_apply] at hx0 hx1
  have hs := Real.abs_sin_sub_sin_le (x 0 - p.k₃) (y 0 - p.k₃)
  have hsub : x 0 - p.k₃ - (y 0 - p.k₃) = x 0 - y 0 := by ring
  rw [hsub] at hs
  refine (Dynamics.norm_le_abs_add_abs_two _).trans ?_
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
def Model.point (m : Model) : State 2 := PhasePlane.mk m.δ 0

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
  /-- A curved power-angle curve: amplitude `k₂ ≠ 0` (the curve is not flat). -/
  | curved

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.p.Pe m.δ = m.p.Pm
  | .inertia => 0 < m.p.M
  | .damped => 0 < m.p.D
  | .dampingNonneg => 0 ≤ m.p.D
  | .undamped => m.p.D = 0
  | .synchronizing => 0 < m.p.syncCoeff m.δ
  | .destabilizing => m.p.syncCoeff m.δ < 0 ∨ m.p.D < 0
  | .curved => m.p.k₂ ≠ 0

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
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    family_isAutonomous

private theorem point_eq_zero {m : Model} (hM : 0 < m.p.M) (hb : m.p.Pe m.δ = m.p.Pm) :
    m.p.field m.point = 0 :=
  (m.p.field_eq_zero_iff hM.ne' _).mpr ⟨by simp, by simpa using hb⟩

/-- An equilibrium at the selected point is a balanced angle. -/
private theorem balanced_of {m : Model} (hM : m.p.M ≠ 0) (heq : m.p.field m.point = 0) :
    m.p.Pe m.δ = m.p.Pm := by
  simpa using ((m.p.field_eq_zero_iff hM _).mp heq).2

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
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
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
  refine Spectral.chain_le_semantics_of_localTable
    (Rl := {.balanced, .inertia, .dampingNonneg, .synchronizing})
    (Rs := {.balanced, .inertia, .damped, .synchronizing})
    (Ru := {.balanced, .inertia, .destabilizing}) (Rp := ∅) (fun s => ?_) realize_univ
    (fun m hm => ?_) (fun m hm => ?_) (fun m hm => ?_) fun m _ => ?_
  · rcases s with P | _
    · cases P <;> rfl
    · rfl
  · rw [TMIO.mem_realize] at hm
    exact mem_den_flow_iff.mpr (ls_of (hm .inertia (by simp)) (hm .dampingNonneg (by simp))
      (hm .balanced (by simp)) (hm .synchronizing (by simp)))
  · rw [TMIO.mem_realize] at hm
    exact mem_den_flow_iff.mpr (les_of (hm .inertia (by simp)) (hm .damped (by simp))
      (hm .balanced (by simp)) (hm .synchronizing (by simp)))
  · rw [TMIO.mem_realize] at hm
    exact mem_den_flow_iff.mpr (unstable_of (hm .inertia (by simp)) (hm .balanced (by simp))
      (hm .destabilizing (by simp)))
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

/-- A swing model with nonzero inertia whose selected angle is not balanced, `P_e(δ*) ≠ P_m`, is
unstable: `(δ*, 0)` is not an equilibrium of the `C¹` swing field, so the solution through it
leaves it (`Spectral.mem_den_unstable_of_ne_zero`). -/
@[powerlib_domain] theorem mem_den_unstable_of_not_balanced (m : Model) (hM : m.p.M ≠ 0)
    (hb : m.p.Pe m.δ ≠ m.p.Pm) : connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff) m.p.contDiff_field
    fun h => hb (balanced_of hM h)

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
  refine Spectral.exactUnder_les_of_jacobian (fun m P => mem_den_flow_iff) {.inertia}
    (fun m => m.p.jacobian m.δ) (fun m _ hm => ?_) (fun m _ => m.p.contDiff_field)
    (fun m _ => m.fderiv_point) fun m hI heq hH => ?_
  · rw [TMIO.mem_realize] at hm
    exact mem_den_flow_iff.mpr (les_of (hm .inertia (by simp [family, translate]))
      (hm .damped (by simp [family, translate])) (hm .balanced (by simp [family, translate]))
      (hm .synchronizing (by simp [family, translate])))
  have hM : 0 < m.p.M := (TMIO.mem_realize _ _ _).mp hI .inertia rfl
  rw [m.p.isHurwitz_jacobian_iff hM] at hH
  rw [TMIO.mem_realize]
  rintro q (rfl | rfl | rfl | rfl)
  · exact balanced_of hM.ne' heq
  · exact hM
  · exact hH.1
  · exact hH.2

/-! ### The local asymptotic and Lyapunov translations within positive inertia -/

/-- At a balanced angle with zero synchronizing coefficient the potential is
`U(δ* + s) = −(P_m − k₁)(s − sin s)`: a fold of the power-angle curve (`P_m − k₁ = ±k₂ ≠ 0`) or a
flat curve (`k₂ = 0`). Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem potential_fold (p : SwingParams) {δ₀ : ℝ} (hb : p.Pe δ₀ = p.Pm)
    (hK : p.syncCoeff δ₀ = 0) (s : ℝ) :
    p.potential δ₀ (δ₀ + s) = -(p.Pm - p.k₁) * (s - Real.sin s) := by
  have hc : Real.cos (δ₀ + s - p.k₃) =
      Real.cos (δ₀ - p.k₃) * Real.cos s - Real.sin (δ₀ - p.k₃) * Real.sin s := by
    rw [show δ₀ + s - p.k₃ = (δ₀ - p.k₃) + s by ring, Real.cos_add]
  have hK' : p.k₂ * Real.cos (δ₀ - p.k₃) = 0 := hK
  simp only [SwingParams.potential, SwingParams.Pe] at hb ⊢
  rw [hc, ← hb]
  linear_combination (1 - Real.cos s) * hK'

/-- With zero synchronizing coefficient and no load offset (`P_m = k₁`) at a balanced angle the
power-angle curve is flat: `k₂ = 0`. Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem k₂_eq_zero_of_flat (p : SwingParams) {δ₀ : ℝ}
    (hb : p.Pe δ₀ = p.Pm) (hK : p.syncCoeff δ₀ = 0) (ha : p.Pm - p.k₁ = 0) : p.k₂ = 0 := by
  have hK' : p.k₂ * Real.cos (δ₀ - p.k₃) = 0 := hK
  have hs : p.k₂ * Real.sin (δ₀ - p.k₃) = 0 := by
    simp only [SwingParams.Pe] at hb
    linarith
  have h := Real.sin_sq_add_cos_sq (δ₀ - p.k₃)
  have : p.k₂ ^ 2 = 0 := by
    calc p.k₂ ^ 2 = p.k₂ ^ 2 * (Real.sin (δ₀ - p.k₃) ^ 2 + Real.cos (δ₀ - p.k₃) ^ 2) := by
          rw [h, mul_one]
      _ = (p.k₂ * Real.sin (δ₀ - p.k₃)) ^ 2 + (p.k₂ * Real.cos (δ₀ - p.k₃)) ^ 2 := by ring
      _ = 0 := by rw [hs, hK']; ring
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

private theorem norm_mkState_sub_point (m : Model) (s t : ℝ) :
    ‖PhasePlane.mk (m.δ + s) t - m.point‖ ≤ |s| + |t| := by
  refine (Dynamics.norm_le_abs_add_abs_two _).trans (le_of_eq ?_)
  simp [Model.point]

private theorem energy_mkState (p : SwingParams) (δ₀ s : ℝ) :
    p.energy δ₀ (PhasePlane.mk (δ₀ + s) 0) = p.potential δ₀ (δ₀ + s) := by
  simp [SwingParams.energy]

/-- Within positive inertia, local asymptotic stability at a balanced angle forces positive
damping and a positive synchronizing coefficient. Negative damping or synchronization is unstable;
an undamped machine conserves its energy; a flat power-angle curve has a continuum of
equilibria; and at a fold of the curve the dissipated energy takes negative values next to
`(δ*, 0)`. -/
private theorem las_guard {m : Model} (hM : 0 < m.p.M) (hb : m.p.Pe m.δ = m.p.Pm)
    (hlas : LocalAsymptoticStable m.p.field m.point) :
    0 < m.p.D ∧ 0 < m.p.syncCoeff m.δ := by
  have hC : ContDiff ℝ 1 m.p.field := m.p.contDiff_field
  have hEd : Differentiable ℝ (m.p.energy m.δ) :=
    (m.p.contDiff_energy (k := 1) _).differentiable one_ne_zero
  have hE0 : m.p.energy m.δ m.point = 0 := by simp [SwingParams.energy, Model.point]
  have hD : 0 < m.p.D := by
    rcases lt_trichotomy m.p.D 0 with hD | hD | hD
    · exact absurd hlas.1 (unstable_of hM hb (Or.inr hD))
    · exfalso
      refine Dynamics.not_localAsymptoticStable_of_lie_nonpos
        (V := fun x => -m.p.energy m.δ x) (ρ := 1) hC hEd.neg one_pos (fun x _ => ?_)
        (fun ε hε => ⟨PhasePlane.mk (m.δ + 0) (ε / 2), ?_, ?_⟩) hlas
      · rw [fderiv_fun_neg]
        simp [m.p.energy_lie hM.ne', hD]
      · refine (norm_mkState_sub_point m 0 (ε / 2)).trans_lt ?_
        rw [abs_zero, zero_add, abs_of_pos (by linarith)]
        linarith
      · show -m.p.energy m.δ (PhasePlane.mk (m.δ + 0) (ε / 2)) < -m.p.energy m.δ m.point
        rw [hE0, neg_zero, neg_lt_zero]
        simp only [SwingParams.energy, PhasePlane.mk_apply_one, PhasePlane.mk_apply_zero, add_zero,
          SwingParams.potential_self]
        positivity
    · exact hD
  refine ⟨hD, ?_⟩
  rcases lt_trichotomy (m.p.syncCoeff m.δ) 0 with hK | hK | hK
  · exact absurd hlas.1 (unstable_of hM hb (Or.inl hK))
  · exfalso
    by_cases ha : m.p.Pm - m.p.k₁ = 0
    · have hk2 := k₂_eq_zero_of_flat m.p hb hK ha
      refine Dynamics.not_localAsymptoticStable_of_equilibria
        (fun ε hε => ⟨PhasePlane.mk (m.δ + ε / 2) 0, fun h => ?_, ?_, ?_⟩) hlas
      · have := congrArg (fun y : State 2 => y 0) h
        simp [Model.point] at this
        linarith
      · refine (norm_mkState_sub_point m (ε / 2) 0).trans_lt ?_
        rw [abs_zero, add_zero, abs_of_pos (by linarith)]
        linarith
      · rw [m.p.field_eq_zero_iff hM.ne']
        refine ⟨by simp, ?_⟩
        simp only [PhasePlane.mk_apply_zero, SwingParams.Pe, hk2, zero_mul, add_zero]
        linarith
    · refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := m.p.energy m.δ) (ρ := 1) hC
        hEd one_pos (fun x _ => ?_) (fun ε hε => ?_) hlas
      · rw [m.p.energy_lie hM.ne']
        nlinarith [sq_nonneg (x 1)]
      · rw [hE0]
        have hε2 : 0 < ε / 2 := by linarith
        rcases lt_or_gt_of_ne ha with hneg | hpos
        · refine ⟨PhasePlane.mk (m.δ + -(ε / 2)) 0, ?_, ?_⟩
          · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
            rw [abs_zero, add_zero, abs_neg, abs_of_pos hε2]
            linarith
          · rw [energy_mkState, potential_fold m.p hb hK, Real.sin_neg]
            have := Real.sin_lt hε2
            nlinarith
        · refine ⟨PhasePlane.mk (m.δ + ε / 2) 0, ?_, ?_⟩
          · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
            rw [abs_zero, add_zero, abs_of_pos hε2]
            linarith
          · rw [energy_mkState, potential_fold m.p hb hK]
            have := Real.sin_lt hε2
            nlinarith
  · exact hK

/-- Within positive inertia the local asymptotic translation is exact: a swing model with `M > 0`
is locally asymptotically stable at `(δ*, 0)` exactly when the angle is balanced, damped and
synchronizing. The linearization does not decide the degenerate cases, the model's structure
does: an undamped machine (`D = 0`) conserves its energy `½ M ω² + U(δ)`, so no nearby solution of
positive energy converges; a flat power-angle curve (`k₂ = 0`) has a continuum of equilibria; and
at a fold of the curve (`k₂ cos(δ* − k₃) = 0`, `k₂ ≠ 0`) the potential `−(P_m − k₁)(s − sin s)`
(`potential_fold`) is negative on one side of `δ*`, where the dissipated energy keeps every
solution away (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`); negative damping or a negative
synchronizing coefficient is unstable. A locally asymptotically stable point of the `C¹` field is
an equilibrium, so the guard `D > 0`, `K > 0` decides (`Spectral.exactUnder_of_equilibrium`). -/
@[powerlib_domain] theorem exactUnder_locallyAsymptoticallyStable :
    connection% (family.ExactUnder {.inertia} (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_of_equilibrium (fun m P => mem_den_flow_iff) (Or.inr (Or.inl rfl))
    {.inertia} (fun m => 0 < m.p.D ∧ 0 < m.p.syncCoeff m.δ) (fun m _ hm => ?_)
    (fun m _ => m.p.contDiff_field) (fun m hI heq hG hd => ?_) fun m hI heq hG => ?_
  · rw [TMIO.mem_realize] at hm
    exact Spectral.den_locallyExponentiallyStable_subset_las (mem_den_flow_iff.mpr
      (les_of (hm .inertia (by simp [family, translate])) (hm .damped (by simp [family, translate]))
        (hm .balanced (by simp [family, translate]))
        (hm .synchronizing (by simp [family, translate]))))
  · have hM : 0 < m.p.M := (TMIO.mem_realize _ _ _).mp hI .inertia rfl
    exact hG (las_guard hM (balanced_of hM.ne' heq) (mem_den_flow_iff.mp hd))
  · have hM : 0 < m.p.M := (TMIO.mem_realize _ _ _).mp hI .inertia rfl
    rw [TMIO.mem_realize]
    rintro q (rfl | rfl | rfl | rfl)
    · exact balanced_of hM.ne' heq
    · exact hM
    · exact hG.1
    · exact hG.2

/-- A flat power-angle curve: `M = D = 1`, `P_m = k₁ = k₂ = k₃ = 0`, `δ* = 0`. Every angle is
balanced; the field is `δ̇ = ω`, `ω̇ = −ω`. -/
def flatCurve : Model := ⟨⟨1, 1, 0, 0, 0, 0⟩, 0⟩

/-- The flat-curve machine is Lyapunov stable: `(δ + ω)² + ω²` does not increase (`δ + ω` is
conserved, `ω` decays), although its synchronizing coefficient is zero (the Jacobian
`[[0, 1], [0, −1]]` is not Hurwitz). -/
@[powerlib_domain] theorem flatCurve_mem_den_lyapunovStable :
    connection% (flatCurve ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  refine Dynamics.lyapunovStable_of_inner_nonpos two_pos
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 1; 0, 1]) (fun z w hzw => ?_)
    fun z => ?_
  · have h0 := congrArg (fun y : State 2 => y 0) hzw
    have h1 := congrArg (fun y : State 2 => y 1) hzw
    simp only [PhasePlane.toEuclideanCLM_apply_zero, PhasePlane.toEuclideanCLM_apply_one] at h0 h1
    simp at h0 h1
    exact PhasePlane.ext_iff'.2 ⟨by linarith, h1⟩
  · have hf0 : flatCurve.field z 0 = z 1 := by
      simp [Model.field, flatCurve, Model.point]
    have hf1 : flatCurve.field z 1 = -z 1 := by
      simp [Model.field, flatCurve, Model.point, SwingParams.accel, SwingParams.Pe]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, PhasePlane.toEuclideanCLM_apply_zero,
      PhasePlane.toEuclideanCLM_apply_one, hf0, hf1, RCLike.inner_apply, conj_trivial]
    simp
    nlinarith [sq_nonneg (z 1)]

/-- Within positive inertia the Lyapunov translation is not exact: the flat-curve machine has
positive inertia and is Lyapunov stable, but its synchronizing coefficient is zero. -/
@[powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.inertia} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exactUnder_of_witness ?_ flatCurve_mem_den_lyapunovStable
    (q := .synchronizing) (by simp [family, translate])
    (by simp [family, Meets, flatCurve, SwingParams.syncCoeff])
  rw [TMIO.mem_realize]
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  show (0 : ℝ) < 1
  norm_num

/-- At a balanced angle with zero synchronizing coefficient the accelerating power is
`P_m − P_e(δ* + s) = (P_m − k₁)(1 − cos s)`, of one sign on both sides of `δ*`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem Pe_fold (p : SwingParams) {δ₀ : ℝ} (hb : p.Pe δ₀ = p.Pm)
    (hK : p.syncCoeff δ₀ = 0) (s : ℝ) :
    p.Pm - p.Pe (δ₀ + s) = (p.Pm - p.k₁) * (1 - Real.cos s) := by
  have hK' : p.k₂ * Real.cos (δ₀ - p.k₃) = 0 := hK
  simp only [SwingParams.Pe] at hb ⊢
  rw [show δ₀ + s - p.k₃ = (δ₀ - p.k₃) + s by ring, Real.sin_add, ← hb]
  linear_combination (-Real.sin s) * hK'

private theorem cos_lt_one_of_abs_le_one {s : ℝ} (hs : s ≠ 0) (h : |s| ≤ 1) :
    Real.cos s < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one _) fun hc => hs ?_
  refine (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp hc
  · linarith [neg_abs_le s, Real.two_le_pi]
  · linarith [le_abs_self s, Real.two_le_pi]

/-- At a fold of the power-angle curve the energy takes values below its value at `(δ*, 0)`
arbitrarily close to it (on the side where the accelerating power pushes). -/
private theorem fold_seeds {m : Model} (hb : m.p.Pe m.δ = m.p.Pm)
    (hK : m.p.syncCoeff m.δ = 0) (ha : m.p.Pm - m.p.k₁ ≠ 0) :
    ∀ ε > 0, ∃ x, ‖x - m.point‖ < ε ∧ m.p.energy m.δ x < m.p.energy m.δ m.point := by
  intro ε hε
  have hE0 : m.p.energy m.δ m.point = 0 := by simp [SwingParams.energy, Model.point]
  rw [hE0]
  have hε2 : 0 < ε / 2 := by linarith
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · refine ⟨PhasePlane.mk (m.δ + -(ε / 2)) 0, ?_, ?_⟩
    · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
      rw [abs_zero, add_zero, abs_neg, abs_of_pos hε2]
      linarith
    · rw [energy_mkState, potential_fold m.p hb hK, Real.sin_neg]
      have := Real.sin_lt hε2
      nlinarith
  · refine ⟨PhasePlane.mk (m.δ + ε / 2) 0, ?_, ?_⟩
    · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
      rw [abs_zero, add_zero, abs_of_pos hε2]
      linarith
    · rw [energy_mkState, potential_fold m.p hb hK]
      have := Real.sin_lt hε2
      nlinarith

/-- Within positive inertia, Lyapunov stability of `(δ*, 0)` holds exactly at a balanced angle
with nonnegative damping and a positive synchronizing coefficient, or on a flat power-angle
curve (`k₂ = 0`) with positive damping. Negative damping or synchronization is unstable; a fold of
the curve (`k₂ cos(δ* − k₃) = 0`, `k₂ ≠ 0`) is unstable for every `D ≥ 0`: below the level of
`(δ*, 0)` the dissipated energy keeps the solution, and there `M ω + D δ` grows at the rate
`(P_m − k₁)(1 − cos(δ − δ*))` (`Dynamics.unstable_of_lie_nonpos_of_lie_pos`); an undamped flat
curve drifts (`(δ − δ*) ω` grows at the rate `ω²`, Chetaev's theorem). -/
@[powerlib_domain] theorem mem_den_lyapunovStable_iff_of_inertia (m : Model) (hM : 0 < m.p.M) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.p.Pe m.δ = m.p.Pm ∧
        ((0 ≤ m.p.D ∧ 0 < m.p.syncCoeff m.δ) ∨ (m.p.k₂ = 0 ∧ 0 < m.p.D))}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  have hC : ContDiff ℝ 1 m.p.field := m.p.contDiff_field
  have h0 := fun x : State 2 =>
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := fun x : State 2 =>
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  constructor
  · intro hm
    have hls : LyapunovStable m.p.field m.point := mem_den_flow_iff.mp hm
    have hb : m.p.Pe m.δ = m.p.Pm :=
      balanced_of hM.ne' (Dynamics.isEquilibrium_of_lyapunovStable hC hls)
    refine ⟨hb, ?_⟩
    have hD : 0 ≤ m.p.D := by
      by_contra hD
      exact (unstable_of hM hb (Or.inr (not_le.mp hD))) hls
    rcases lt_trichotomy (m.p.syncCoeff m.δ) 0 with hK | hK | hK
    · exact absurd hls (unstable_of hM hb (Or.inl hK))
    · by_cases ha : m.p.Pm - m.p.k₁ = 0
      · have hk2 := k₂_eq_zero_of_flat m.p hb hK ha
        rcases eq_or_lt_of_le hD with hD0 | hDpos
        · -- an undamped flat curve: `(δ − δ*) ω` grows at the rate `ω²`
          exfalso
          have hW : ContDiff ℝ 1 fun x : State 2 => (x 0 - m.δ) * x 1 :=
            ((Dynamics.contDiff_coord 0).sub contDiff_const).mul (Dynamics.contDiff_coord 1)
          refine Dynamics.unstable_of_chetaev (W := fun x : State 2 => (x 0 - m.δ) * x 1)
            (r := 1) hC hW one_pos (fun ε hε => ⟨PhasePlane.mk (m.δ + ε / 4) (ε / 4), ?_, ?_⟩)
            (fun x _ hWx => ?_) hls
          · refine (norm_mkState_sub_point m _ _).trans_lt ?_
            rw [abs_of_pos (by linarith)]
            linarith
          · simp only [PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, add_sub_cancel_left]
            positivity
          · have hd : HasFDerivAt (fun y : State 2 => (y 0 - m.δ) * y 1)
                ((x 0 - m.δ) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ) +
                  x 1 • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ)) x :=
              ((h0 x).sub_const m.δ).mul (h1 x)
            rw [hd.fderiv]
            have hx1 : x 1 ≠ 0 := by
              intro h
              simp only [h, mul_zero, lt_irrefl] at hWx
            have hacc : m.p.accel (x 0) (x 1) = 0 := by
              simp only [SwingParams.accel, SwingParams.Pe, hk2, ← hD0, zero_mul, add_zero]
              rw [show m.p.Pm - m.p.k₁ - 0 = 0 by linarith, zero_div]
            simp only [_root_.add_apply, _root_.smul_apply,
              PiLp.proj_apply, smul_eq_mul, SwingParams.field_apply_zero, SwingParams.field_apply_one, hacc, mul_zero,
              zero_add]
            exact mul_self_pos.mpr hx1
        · exact Or.inr ⟨hk2, hDpos⟩
      · -- a fold: below the level of `(δ*, 0)` the quantity `(P_m − k₁)(M ω + D δ)` grows
        exfalso
        set a := m.p.Pm - m.p.k₁ with ha_def
        have hW : ContDiff ℝ 1 fun x : State 2 => a * (m.p.M * x 1 + m.p.D * x 0) :=
          contDiff_const.mul ((contDiff_const.mul (Dynamics.contDiff_coord 1)).add
            (contDiff_const.mul (Dynamics.contDiff_coord 0)))
        refine Dynamics.unstable_of_lie_nonpos_of_lie_pos (E := m.p.energy m.δ)
          (W := fun x : State 2 => a * (m.p.M * x 1 + m.p.D * x 0)) (r := 1) hC
          (m.p.contDiff_energy _) hW one_pos (fun x _ => ?_) (fold_seeds hb hK ha)
          (fun x hx hEx => ?_) hls
        · rw [m.p.energy_lie hM.ne']
          nlinarith [sq_nonneg (x 1)]
        · have hd : HasFDerivAt (fun y : State 2 => a * (m.p.M * y 1 + m.p.D * y 0))
              (a • (m.p.M • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ) +
                m.p.D • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ))) x :=
            (((h1 x).const_mul m.p.M).add ((h0 x).const_mul m.p.D)).const_mul a
          rw [hd.fderiv]
          simp only [_root_.smul_apply, _root_.add_apply,
            PiLp.proj_apply, smul_eq_mul, SwingParams.field_apply_zero, SwingParams.field_apply_one, SwingParams.accel]
          have hMne := hM.ne'
          have hrate : m.p.M * ((m.p.Pm - m.p.Pe (x 0) - m.p.D * x 1) / m.p.M) + m.p.D * x 1 =
              m.p.Pm - m.p.Pe (x 0) := by field_simp; ring
          rw [hrate]
          set s₀ := x 0 - m.δ with hs₀
          have hx0 : x 0 = m.δ + s₀ := by rw [hs₀]; ring
          rw [hx0, Pe_fold m.p hb hK]
          have hs1 : |s₀| ≤ 1 := by
            have := Dynamics.abs_apply_le_norm (x - m.point) 0
            simp only [PiLp.sub_apply, Model.point_zero] at this
            linarith
          have hs0 : s₀ ≠ 0 := by
            intro h
            have hE0 : m.p.energy m.δ m.point = 0 := by simp [SwingParams.energy, Model.point]
            rw [hE0] at hEx
            have hEx' : m.p.M / 2 * x 1 ^ 2 + m.p.potential m.δ (x 0) < 0 := hEx
            rw [hx0, h, add_zero, SwingParams.potential_self] at hEx'
            have : 0 ≤ m.p.M / 2 * x 1 ^ 2 := by positivity
            linarith
          have hc := cos_lt_one_of_abs_le_one hs0 hs1
          have ha2 : 0 < a * a := mul_self_pos.mpr ha
          nlinarith
    · exact Or.inl ⟨hD, hK⟩
  · rintro ⟨hb, (⟨hD, hK⟩ | ⟨hk2, hD⟩)⟩
    · exact mem_den_flow_iff.mpr (ls_of hM hD hb hK)
    · -- a damped flat curve: `(δ + (M/D) ω)² + ω²` does not increase
      rw [family_isAutonomous.mem_den_flow]
      have hDne := hD.ne'
      have hMne := hM.ne'
      have hk1 : m.p.Pm = m.p.k₁ := by
        simp only [SwingParams.Pe, hk2, zero_mul, add_zero] at hb
        exact hb.symm
      refine Dynamics.lyapunovStable_of_inner_nonpos two_pos
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, m.p.M / m.p.D; 0, 1])
        (fun z w hzw => ?_) fun z => ?_
      · have hz0 := congrArg (fun y : State 2 => y 0) hzw
        have hz1 := congrArg (fun y : State 2 => y 1) hzw
        simp only [PhasePlane.toEuclideanCLM_apply_zero, PhasePlane.toEuclideanCLM_apply_one] at hz0 hz1
        simp at hz0 hz1
        refine PhasePlane.ext_iff'.2 ⟨?_, hz1⟩
        rw [hz1] at hz0
        linarith
      · have hf0 : m.field z 0 = z 1 := by simp [Model.field, Model.point]
        have hf1 : m.field z 1 = -(m.p.D / m.p.M) * z 1 := by
          simp only [Model.field, SwingParams.field_apply_one, SwingParams.accel, SwingParams.Pe, hk2,
            zero_mul, add_zero, hk1, sub_self, PiLp.add_apply, Model.point_one]
          field_simp
          ring
        simp only [PiLp.inner_apply, Fin.sum_univ_two, PhasePlane.toEuclideanCLM_apply_zero,
          PhasePlane.toEuclideanCLM_apply_one, hf0, hf1, RCLike.inner_apply, conj_trivial]
        simp
        have : 0 ≤ m.p.D / m.p.M := div_nonneg hD.le hM.le
        field_simp
        nlinarith [sq_nonneg (z 1), mul_pos hD hM]

/-- Within positive inertia and a curved power-angle curve (`k₂ ≠ 0`) the Lyapunov translation is
exact: a swing model with `M > 0`, `k₂ ≠ 0` is Lyapunov stable at `(δ*, 0)` exactly when the angle
is balanced, the damping nonnegative and the synchronizing coefficient positive. This is
`mem_den_lyapunovStable_iff_of_inertia` without its flat-curve alternative; on a flat curve the
translation is not exact (`not_exactUnder_lyapunovStable`). -/
@[powerlib_domain] theorem exactUnder_lyapunovStable :
    connection% (family.ExactUnder {.inertia, .curved} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_iff_forall.mpr fun m hΔ => ?_
  have hM : 0 < m.p.M := (TMIO.mem_realize _ _ _).mp hΔ .inertia (by simp)
  have hk : m.p.k₂ ≠ 0 := (TMIO.mem_realize _ _ _).mp hΔ .curved (by simp)
  have h := mem_den_lyapunovStable_iff_of_inertia m hM
  unfold powerlib.TMIO.Statement at h
  rw [h, Set.mem_ofPred_eq]
  simp only [TMIO.mem_realize, family, translate, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Meets]
  constructor
  · rintro ⟨hb, -, hD, hK⟩
    exact ⟨hb, Or.inl ⟨hD, hK⟩⟩
  · rintro ⟨hb, (⟨hD, hK⟩ | ⟨hk0, -⟩)⟩
    · exact ⟨hb, hM, hD, hK⟩
    · exact absurd hk0 hk

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
  exact Spectral.not_exact_of_witness negativeInertia_mem_den_locallyExponentiallyStable
    (q := .inertia) (by simp [family, translate]) negativeInertia_not_meets

/-- The local asymptotic translation is sound but not exact (the same witness). -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_les_witness negativeInertia_mem_den_locallyExponentiallyStable
    (Or.inr rfl) (q := Requirement.inertia) (by simp [family, translate]) negativeInertia_not_meets

/-- The Lyapunov translation is sound but not exact (the same witness). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_les_witness negativeInertia_mem_den_locallyExponentiallyStable
    (Or.inl rfl) (q := Requirement.inertia) (by simp [family, translate]) negativeInertia_not_meets

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

/-- The translation is the linear table (`Spectral.linearTable`). -/
private theorem translate_eq (s : Sentence) :
    family.translate s = Spectral.linearTable {.inertia, .damped, .synchronizing}
      {.inertia, .destabilizing} {.inertia, .synchronizing, .undamped} ∅ (fun _ => Set.univ) s := by
  rcases s with P | _
  · cases P <;> rfl
  · rfl

private theorem isHurwitz_iff {m : Model} (hM : 0 < m.p.M) :
    LinearSystems.IsHurwitz (plant m).A ↔ 0 < m.p.D ∧ 0 < m.p.syncCoeff m.δ :=
  m.p.isHurwitz_jacobian_iff hM m.δ

private theorem mem_realize_stable {m : Model} :
    m ∈ TMIO.realize Meets {.inertia, .damped, .synchronizing} ↔
      0 < m.p.M ∧ 0 < m.p.D ∧ 0 < m.p.syncCoeff m.δ := by
  simp only [TMIO.mem_realize, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  rfl

/-- The energy matrix `diag(K, M)` is conserved by the undamped linearization. -/
private theorem conserved {m : Model} (hD : m.p.D = 0) (hM : m.p.M ≠ 0) :
    (plant m).Aᵀ * !![m.p.syncCoeff m.δ, 0; 0, m.p.M] +
      !![m.p.syncCoeff m.δ, 0; 0, m.p.M] * (plant m).A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plant, SwingParams.jacobian, hD, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    ring

/-- A destabilizing sign gives a characteristic root in the open right half plane: `K < 0` makes
`det J < 0` (a positive real eigenvalue), `D < 0` makes `tr J > 0`. -/
private theorem exists_root {m : Model} (hM : 0 < m.p.M)
    (hs : m.p.syncCoeff m.δ < 0 ∨ m.p.D < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix (plant m).A s).det = 0 ∧ 0 < s.re := by
  rcases hs with hK | hD
  · obtain ⟨μ, v, hv, heig, hre⟩ := Criteria.exists_eigenvalue_re_pos_of_det_neg (plant m).A
      (by rw [show (plant m).A = m.p.jacobian m.δ from rfl, SwingParams.det_jacobian]
          exact div_neg_of_neg_of_pos hK hM)
    exact ⟨μ, Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _ hv heig, hre⟩
  · exact Criteria.exists_root_re_pos_of_trace_pos _
      (by rw [show (plant m).A = m.p.jacobian m.δ from rfl, SwingParams.trace_jacobian, neg_div]
          exact neg_pos.mpr (div_neg_of_neg_of_pos hD hM))

/-- The decay requirement is the whole language: damped and undamped are inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) :=
  Swing.realize_univ

/-- Every translation of the linearized swing family is sound (the linear table,
`Spectral.chain_le_semantics_of_linearTable`): positive inertia, damping and synchronization make
the Jacobian Hurwitz; a destabilizing sign gives a characteristic root in the open right half
plane; the energy `½ K Δδ² + ½ M Δω²` is conserved without damping; a system without ports is
passive; decay rates go to the inconsistent whole language. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_linearTable (F := family)
    (Rs := {.inertia, .damped, .synchronizing}) (Ru := {.inertia, .destabilizing})
    (Rc := {.inertia, .synchronizing, .undamped}) (Rp := ∅) (Rd := fun _ => Set.univ)
    family_isLinear translate_eq (fun m hm => ?_) (fun m hm => ?_)
    (fun _ => Spectral.realize_univ_subset_of_eq_empty realize_univ _) (fun m hm => ?_)
    fun m _ => family.mem_den.mpr (Port.System.passive_of_noPorts _)
  · obtain ⟨hM, hD, hK⟩ := mem_realize_stable.mp hm
    exact (isHurwitz_iff hM).mpr ⟨hD, hK⟩
  · rw [TMIO.mem_realize] at hm
    exact exists_root (hm .inertia (by simp)) (hm .destabilizing (by simp))
  · rw [TMIO.mem_realize] at hm
    have hM : 0 < m.p.M := hm .inertia (by simp)
    have hD : m.p.D = 0 := hm .undamped (by simp)
    refine family_isLinear.mem_den_conservative (by ext i j; fin_cases i <;> fin_cases j <;> simp)
      (fun v hv => ?_) (conserved hD hM.ne')
    have hK : 0 < m.p.syncCoeff m.δ := hm .synchronizing (by simp)
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

/-- Within positive inertia, the attractive sentences and sampled contraction of the linearized
swing equation are translated exactly: `M s² + D s + K` is Hurwitz iff `D > 0` and `K > 0`
(`Spectral.exactUnder_of_linearTable`). -/
@[powerlib_domain] theorem exactUnder_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.ExactUnder {.inertia} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_of_linearTable family_isLinear translate_eq {.inertia}
    (fun m hI => mem_realize_stable.trans ?_) hP
  have hM : 0 < m.p.M := (TMIO.mem_realize _ _ _).mp hI .inertia rfl
  rw [isHurwitz_iff hM]
  exact ⟨fun h => h.2, fun h => ⟨hM, h⟩⟩

/-- The linearization is exponentially stable iff `D > 0` and `K > 0` (`M > 0`). -/
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

/-- A point that is not an equilibrium is unstable: the solution through it leaves it
(`mem_den_unstable_of_not_balanced`, `P_e(0) = 0 ≠ 1 = P_m`). -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_not_balanced offEquilibrium (by norm_num [offEquilibrium])
    (by norm_num [offEquilibrium, SwingParams.Pe])

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for a balanced angle. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .balanced)
    (by simp [family, translate]) (by simp [family, Meets, offEquilibrium, SwingParams.Pe])

end Swing

end powerlib.Synchronous
