import theorem.PowerSystem.Synchronous.FluxDecay
import theorem.Spectral.Family
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Linearization
import theorem.Dynamics.Coordinates

/-! # The one-axis machine on an infinite bus and its Heffron–Phillips linearization

The nonlinear one-axis (flux-decay) model of a synchronous machine connected through a reactance
to an infinite bus, with constant mechanical torque and constant field voltage, read about a
selected operating point as a model family (`OneAxis.family`), and its connection to the
linearized Heffron–Phillips family `Synchronous.FluxDecay.family`
(`theorem/PowerSystem/Synchronous/FluxDecay.lean`): the Jacobian of the nonlinear field at a
point is the Heffron–Phillips state matrix whose coefficients `K₁ … K₄` are the partial
derivatives of the electrical torque and of the field EMF (`hasFDerivAt_field`), so at an
equilibrium local exponential stability of the nonlinear machine is that of its linearization
(converse linearization, `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`).

Model boundary.
* State `x = (δ, ω, E'_q) : Dynamics.State 3`, in this order: rotor angle relative to the
  infinite bus (rad), per-unit speed deviation, q-axis transient voltage (per unit); continuous
  time, autonomous.
* Dynamics `δ̇ = ω₀ω`, `2Hω̇ = T_m − T_e(δ, E'_q) − Dω`,
  `T'_{d0}Ė'_q = E_fd − E'_q − (X_d − X'_d) i_d` (`Machine.field`), with the stator and network
  algebraic: no stator resistance, no stator or network transients, a lossless external reactance
  `X_e` to a bus of constant voltage `V` and angle `0`; `i_d = (E'_q − V cos δ)/(X'_d + X_e)`,
  `i_q = V sin δ/(X_q + X_e)`, air-gap torque `T_e = E'_q i_q + (X_q − X'_d) i_d i_q`
  (`Machine.currentD`, `Machine.currentQ`, `Machine.torque`, `Machine.fieldEMF`; per-unit torque
  equal to per-unit power, `ω ≈ 1` in the stator voltages).
* Constant mechanical torque `T_m` and field voltage `E_fd`: no governor, AVR, exciter or PSS, no
  damper windings, no saturation; `D` lumps the damping torque of other origin.
* Parameters (`Model`): `H > 0`, `ω₀ > 0`, `T'_{d0} > 0`, `X'_d + X_e > 0`, `X_d + X_e > 0`,
  `X_q + X_e > 0`; the selected point is `(δ*, 0, E'_q*)`, not necessarily an equilibrium.

Source: W. G. Heffron, R. A. Phillips, AIEE Trans. PAS-71 (1952); F. P. deMello, C. Concordia,
"Concepts of synchronous machine stability as affected by excitation control", IEEE Trans. PAS-88
(1969) (the one-axis machine on an infinite bus and the coefficients `K₁ … K₄`); P. Kundur, *Power
System Stability and Control* (1994) §12.3 (the constants with zero stator and line resistance);
P. M. Anderson, A. A. Fouad, *Power System Control and Stability* (1977) ch. 4 (the one-axis
model). The Agda scaffold of the connection is
`theorem/PowerSystem/Synchronous/OneAxisLinearization.agda`.

Results.
* `Machine`, `Machine.currentD`, `Machine.currentQ`, `Machine.torque`, `Machine.fieldEMF`,
  `Machine.field` — the model; `Machine.torque_eq` (`T_e = E'_qV sin δ/(X'_d + X_e) −
  (X_q − X'_d)V² sin 2δ/(2(X_q + X_e)(X'_d + X_e))`), `Machine.fieldEMF_eq`.
* `Machine.K₁`, `Machine.K₂`, `Machine.K₃`, `Machine.K₄`, `Machine.linParams` — the
  Heffron–Phillips coefficients at `(δ, E'_q)`; `Machine.contDiff_field`,
  `Machine.hasFDerivAt_field`, `Machine.fderiv_field` (the Jacobian is
  `(linParams δ E'_q).stateMatrix`: the coefficients are the partial derivatives); `Machine.K₂_pos`,
  `Machine.K₄_pos` (`0 < δ < π`, `V > 0`, `X_d > X'_d`); `Machine.fluxTorque_eq`;
  `Machine.steadyE`, `Machine.fieldEMF_steadyE`, `Machine.hasDerivAt_steadyTorque` (the
  steady-state synchronizing coefficient `K₁ − K₂K₃K₄` is the slope of the torque along the
  field-EMF balance at constant field voltage: the Routh condition `a₀ > 0` is the classical
  steady-state stability limit).
* `Model`, `Model.point`, `Model.field`, `Model.linearization` (a member of
  `Synchronous.FluxDecay.family`), `Model.field_point_eq_zero_iff` (an equilibrium is torque and
  field-EMF balance).

Family and connection conclusions.
* `OneAxis.family : Family Model Spectral.Requirement 3 0` (`Spectral.localFamily`): every model
  read as its field translated to the selected point. `stable`: an equilibrium whose linearization
  satisfies the Routh–Hurwitz conditions; `unstable`: an equilibrium whose linearization strictly
  violates one. `chain_le_semantics` (every translation is sound, through
  `Spectral.chain_le_semantics_of_jacobian`), `exact_locallyExponentiallyStable` (local exponential
  stability is translated exactly, `Spectral.local_exact_of_jacobian`),
  `mem_den_unstable_of_not_equilibrium`.
* The linearization (two families): `mem_den_locallyExponentiallyStable_iff_linearization` — at an
  equilibrium, the nonlinear machine is locally exponentially stable exactly when its
  linearization satisfies the attractive sentences of `Synchronous.FluxDecay.family`;
  `mem_den_unstable_of_linearization` — a linearization meeting the instability requirement of
  `Synchronous.FluxDecay.family` makes the machine at an equilibrium unstable.
* `mem_den_undamped_iff` (through the linearization and
  `Synchronous.FluxDecay.mem_den_undamped_iff`):
  without damping torque (`D = 0`), at an equilibrium with `0 < δ* < π`, `V > 0` and `X_d > X'_d`,
  the machine is locally exponentially stable exactly when the steady-state synchronizing
  coefficient `K₁ − K₂K₃K₄` is positive: the field winding damps the machine wherever the
  steady-state stability limit is not exceeded.
-/

noncomputable section
namespace powerlib.Synchronous.OneAxis

open Matrix LinearSystems TMIO
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)

/-! ## The machine -/

/-- The one-axis machine on an infinite bus: inertia `H`, damping `D`, synchronous frequency
`ω₀`, open-circuit transient time constant `T'_{d0}`, reactances `X_d`, `X'_d`, `X_q`, external
reactance `X_e`, bus voltage `V`, mechanical torque `T_m`, field voltage `E_fd`. -/
structure Machine where
  H : ℝ
  D : ℝ
  ω₀ : ℝ
  Td0 : ℝ
  Xd : ℝ
  Xd' : ℝ
  Xq : ℝ
  Xe : ℝ
  V : ℝ
  Tm : ℝ
  Efd : ℝ

namespace Machine

variable (q : Machine)

/-- The d-axis armature current `i_d = (E'_q − V cos δ)/(X'_d + X_e)`. -/
def currentD (δ E : ℝ) : ℝ := (E - q.V * Real.cos δ) / (q.Xd' + q.Xe)

/-- The q-axis armature current `i_q = V sin δ/(X_q + X_e)`. -/
def currentQ (δ : ℝ) : ℝ := q.V * Real.sin δ / (q.Xq + q.Xe)

/-- The air-gap torque `T_e = E'_q i_q + (X_q − X'_d) i_d i_q`. -/
def torque (δ E : ℝ) : ℝ := E * q.currentQ δ + (q.Xq - q.Xd') * q.currentD δ E * q.currentQ δ

/-- The field EMF demand `E'_q + (X_d − X'_d) i_d` (the steady-state voltage behind `X_d`). -/
def fieldEMF (δ E : ℝ) : ℝ := E + (q.Xd - q.Xd') * q.currentD δ E

/-- The one-axis field on `(δ, ω, E'_q)`. -/
def field (x : State 3) : State 3 :=
  mk3 (q.ω₀ * x 1) ((q.Tm - q.torque (x 0) (x 2) - q.D * x 1) / (2 * q.H))
    ((q.Efd - q.fieldEMF (x 0) (x 2)) / q.Td0)

@[tmio M, simp, powerlib_domain] theorem field_apply_zero (x : State 3) :
    q.field x 0 = q.ω₀ * x 1 := by
  simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_one (x : State 3) :
    q.field x 1 = (q.Tm - q.torque (x 0) (x 2) - q.D * x 1) / (2 * q.H) := by
  simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_two (x : State 3) :
    q.field x 2 = (q.Efd - q.fieldEMF (x 0) (x 2)) / q.Td0 := by
  simp [field]

/-- The torque in closed form:
`T_e = E'_qV sin δ/(X'_d + X_e) − (X_q − X'_d)V² sin 2δ/(2(X_q + X_e)(X'_d + X_e))`. -/
@[tmio M, powerlib_domain] theorem torque_eq (hd : q.Xd' + q.Xe ≠ 0) (hq : q.Xq + q.Xe ≠ 0)
    (δ E : ℝ) :
    q.torque δ E = E * q.V * Real.sin δ / (q.Xd' + q.Xe) -
      (q.Xq - q.Xd') * q.V ^ 2 * Real.sin (2 * δ) / (2 * ((q.Xq + q.Xe) * (q.Xd' + q.Xe))) := by
  rw [Real.sin_two_mul]
  simp only [torque, currentD, currentQ]
  field_simp
  ring

/-- The field EMF in closed form:
`E'_q (X_d + X_e)/(X'_d + X_e) − (X_d − X'_d)V cos δ/(X'_d + X_e)`. -/
@[tmio M, powerlib_domain] theorem fieldEMF_eq (hd : q.Xd' + q.Xe ≠ 0) (δ E : ℝ) :
    q.fieldEMF δ E = E * ((q.Xd + q.Xe) / (q.Xd' + q.Xe)) -
      (q.Xd - q.Xd') * q.V * Real.cos δ / (q.Xd' + q.Xe) := by
  simp only [fieldEMF, currentD]
  field_simp
  ring

/-! ## The Heffron–Phillips coefficients -/

/-- `K₁ = ∂T_e/∂δ = E'_qV cos δ/(X'_d + X_e) − (X_q − X'_d)V² cos 2δ/((X_q + X_e)(X'_d + X_e))`. -/
def K₁ (δ E : ℝ) : ℝ :=
  E * q.V * Real.cos δ / (q.Xd' + q.Xe) -
    (q.Xq - q.Xd') * q.V ^ 2 * Real.cos (2 * δ) / ((q.Xq + q.Xe) * (q.Xd' + q.Xe))

/-- `K₂ = ∂T_e/∂E'_q = V sin δ/(X'_d + X_e)`. -/
def K₂ (δ : ℝ) : ℝ := q.V * Real.sin δ / (q.Xd' + q.Xe)

/-- `K₃ = (X'_d + X_e)/(X_d + X_e)`, the inverse of `∂(field EMF)/∂E'_q`. -/
def K₃ : ℝ := (q.Xd' + q.Xe) / (q.Xd + q.Xe)

/-- `K₄ = ∂(field EMF)/∂δ = (X_d − X'_d)V sin δ/(X'_d + X_e)`. -/
def K₄ (δ : ℝ) : ℝ := (q.Xd - q.Xd') * q.V * Real.sin δ / (q.Xd' + q.Xe)

/-- The Heffron–Phillips data at `(δ, E'_q)`. -/
def linParams (δ E : ℝ) : FluxDecayParametric.Params :=
  ⟨q.K₁ δ E, q.K₂ δ, q.K₃, q.K₄ δ, q.H, q.D, q.Td0, q.ω₀⟩

@[tmio M, powerlib_domain] theorem contDiff_field (hd : q.Xd' + q.Xe ≠ 0) (hq : q.Xq + q.Xe ≠ 0)
    {k : WithTop ℕ∞} : ContDiff ℝ k q.field := by
  rw [contDiff_euclidean]
  intro i
  have e : ∀ x : State 3, q.field x = mk3 (q.ω₀ * x 1)
      ((q.Tm - (x 2 * q.V * Real.sin (x 0) / (q.Xd' + q.Xe) -
        (q.Xq - q.Xd') * q.V ^ 2 * Real.sin (2 * x 0) / (2 * ((q.Xq + q.Xe) * (q.Xd' + q.Xe)))) -
          q.D * x 1) / (2 * q.H))
      ((q.Efd - (x 2 * ((q.Xd + q.Xe) / (q.Xd' + q.Xe)) -
        (q.Xd - q.Xd') * q.V * Real.cos (x 0) / (q.Xd' + q.Xe))) / q.Td0) := by
    intro x
    rw [field, q.torque_eq hd hq, q.fieldEMF_eq hd]
  have hf : q.field = fun x => _ := funext e
  rw [hf]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, mk3_zero]; fun_prop
  · simp only [Fin.mk_one, Fin.isValue, mk3_one]; fun_prop
  · simp only [Fin.reduceFinMk, Fin.isValue, mk3_two]; fun_prop

/-- **The Jacobian of the one-axis field is the Heffron–Phillips state matrix.** At every state
`x`, the derivative of the field is `(linParams (x 0) (x 2)).stateMatrix`: `K₁`, `K₂` are the
partial derivatives of the torque, `1/K₃`, `K₄` those of the field EMF. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field (hd : q.Xd' + q.Xe ≠ 0)
    (hq : q.Xq + q.Xe ≠ 0) (hH : q.H ≠ 0) (hT : q.Td0 ≠ 0) (x : State 3) :
    HasFDerivAt q.field
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (q.linParams (x 0) (x 2)).stateMatrix) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 : HasFDerivAt (fun y : State 3 => y 0)
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).hasFDerivAt
  have h1 : HasFDerivAt (fun y : State 3 => y 1)
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : State 3 => y 2)
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).hasFDerivAt
  have hH2 : 2 * q.H ≠ 0 := mul_ne_zero two_ne_zero hH
  fin_cases i
  · refine ((h1.const_mul q.ω₀).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
    · simp only [Fin.zero_eta, Fin.isValue, field_apply_zero]
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [FluxDecayParametric.Params.stateMatrix, linParams, toEuclideanCLM_apply3]
  · have hrow := (((((h2.fun_mul h0.sin).const_mul (q.V / (q.Xd' + q.Xe))).fun_sub
      ((h0.const_mul 2).sin.const_mul
        ((q.Xq - q.Xd') * q.V ^ 2 / (2 * ((q.Xq + q.Xe) * (q.Xd' + q.Xe)))))).const_sub
      q.Tm).fun_sub (h1.const_mul q.D)).const_mul (2 * q.H)⁻¹
    refine (hrow.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
    · simp only [Fin.mk_one, Fin.isValue, field_apply_one]
      rw [q.torque_eq hd hq]
      field_simp
    · refine ContinuousLinearMap.ext fun v => ?_
      simp only [_root_.smul_apply, _root_.sub_apply, _root_.add_apply, _root_.neg_apply,
        ContinuousLinearMap.comp_apply, PiLp.proj_apply, smul_eq_mul, toEuclideanCLM_apply3,
        FluxDecayParametric.Params.stateMatrix, linParams, K₁, K₂, Matrix.of_apply,
        Fin.mk_one, Fin.isValue,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
      generalize Real.cos (2 * x 0) = c2
      generalize Real.cos (x 0) = c
      generalize Real.sin (x 0) = sn
      field_simp
      ring
  · have hrow := ((((h2.const_mul ((q.Xd + q.Xe) / (q.Xd' + q.Xe))).fun_sub
      (h0.cos.const_mul ((q.Xd - q.Xd') * q.V / (q.Xd' + q.Xe)))).const_sub q.Efd).const_mul
      q.Td0⁻¹)
    refine (hrow.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
    · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two]
      rw [q.fieldEMF_eq hd]
      field_simp
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [FluxDecayParametric.Params.stateMatrix, linParams, K₃, K₄, toEuclideanCLM_apply3]
      generalize Real.sin (x 0) = sn
      field_simp
      ring

@[tmio M, powerlib_domain] theorem fderiv_field (hd : q.Xd' + q.Xe ≠ 0) (hq : q.Xq + q.Xe ≠ 0)
    (hH : q.H ≠ 0) (hT : q.Td0 ≠ 0) (x : State 3) :
    fderiv ℝ q.field x =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (q.linParams (x 0) (x 2)).stateMatrix :=
  (q.hasFDerivAt_field hd hq hH hT x).fderiv

/-- In the normal operating range `0 < δ < π`, `K₂ > 0` (`V > 0`, `X'_d + X_e > 0`). -/
@[tmio M, powerlib_domain] theorem K₂_pos (hd : 0 < q.Xd' + q.Xe) (hV : 0 < q.V) {δ : ℝ}
    (h0 : 0 < δ) (hπ : δ < Real.pi) : 0 < q.K₂ δ := by
  have := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  unfold K₂; positivity

/-- In the normal operating range `0 < δ < π`, `K₄ > 0` (`V > 0`, `X_d > X'_d`). -/
@[tmio M, powerlib_domain] theorem K₄_pos (hd : 0 < q.Xd' + q.Xe) (hV : 0 < q.V)
    (hX : q.Xd' < q.Xd) {δ : ℝ} (h0 : 0 < δ) (hπ : δ < Real.pi) : 0 < q.K₄ δ := by
  have := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have : 0 < q.Xd - q.Xd' := sub_pos.mpr hX
  unfold K₄; positivity

/-- The flux-decay torque coefficient in closed form:
`K₂K₃K₄ = (X_d − X'_d)V² sin²δ/((X'_d + X_e)(X_d + X_e))` — nonnegative when `X_d ≥ X'_d`, so the
steady-state synchronizing coefficient `K₁ − K₂K₃K₄` is at most `K₁`. -/
@[tmio M, powerlib_domain] theorem fluxTorque_eq (hd : q.Xd' + q.Xe ≠ 0) (hX : q.Xd + q.Xe ≠ 0)
    (δ : ℝ) :
    q.K₂ δ * q.K₃ * q.K₄ δ =
      (q.Xd - q.Xd') * q.V ^ 2 * Real.sin δ ^ 2 / ((q.Xd' + q.Xe) * (q.Xd + q.Xe)) := by
  simp only [K₂, K₃, K₄]
  field_simp

/-- The transient voltage at field-EMF balance, `E'_q(δ)` with `E'_q + (X_d − X'_d) i_d = E_fd`:
`E'_q(δ) = (E_fd(X'_d + X_e) + (X_d − X'_d)V cos δ)/(X_d + X_e)`. -/
def steadyE (δ : ℝ) : ℝ :=
  (q.Efd * (q.Xd' + q.Xe) + (q.Xd - q.Xd') * q.V * Real.cos δ) / (q.Xd + q.Xe)

@[tmio M, powerlib_domain] theorem fieldEMF_steadyE (hd : q.Xd' + q.Xe ≠ 0)
    (hX : q.Xd + q.Xe ≠ 0) (δ : ℝ) : q.fieldEMF δ (q.steadyE δ) = q.Efd := by
  rw [q.fieldEMF_eq hd, steadyE]
  field_simp
  ring

/-- **The steady-state synchronizing coefficient is the slope of the steady-state torque.** Along
the field-EMF balance (constant field voltage, `E'_q = E'_q(δ)`), the torque `T_e(δ, E'_q(δ))` has
the derivative `K₁ − K₂K₃K₄`: the Routh condition `a₀ > 0` of the linearization is the positive
slope of the steady-state power-angle curve, the classical steady-state stability limit. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_steadyTorque (hd : q.Xd' + q.Xe ≠ 0)
    (hq : q.Xq + q.Xe ≠ 0) (hX : q.Xd + q.Xe ≠ 0) (δ : ℝ) :
    HasDerivAt (fun θ => q.torque θ (q.steadyE θ))
      (q.K₁ δ (q.steadyE δ) - q.K₂ δ * q.K₃ * q.K₄ δ) δ := by
  have hE : HasDerivAt q.steadyE (-((q.Xd - q.Xd') * q.V * Real.sin δ) / (q.Xd + q.Xe)) δ := by
    have h := (((Real.hasDerivAt_cos δ).const_mul ((q.Xd - q.Xd') * q.V)).const_add
      (q.Efd * (q.Xd' + q.Xe))).div_const (q.Xd + q.Xe)
    exact (show HasDerivAt q.steadyE _ δ from h).congr_deriv (by ring)
  have hT := ((hE.fun_mul (Real.hasDerivAt_sin δ)).const_mul (q.V / (q.Xd' + q.Xe))).fun_sub
    (((hasDerivAt_id' δ).const_mul 2).sin.const_mul
      ((q.Xq - q.Xd') * q.V ^ 2 / (2 * ((q.Xq + q.Xe) * (q.Xd' + q.Xe)))))
  refine (hT.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ => ?_)).congr_deriv ?_
  · simp only
    rw [q.torque_eq hd hq]
    ring
  · rw [q.fluxTorque_eq hd hX]
    simp only [K₁]
    field_simp
    ring

end Machine

/-! ## The family -/

/-- A one-axis machine read about a selected operating point `(δ*, 0, E'_q*)`, with the sign
conditions `H, ω₀, T'_{d0} > 0` and positive reactance sums. -/
structure Model where
  /-- The machine. -/
  q : Machine
  /-- The selected angle `δ*`. -/
  δ : ℝ
  /-- The selected transient voltage `E'_q*`. -/
  E : ℝ
  H_pos : 0 < q.H
  ω₀_pos : 0 < q.ω₀
  Td0_pos : 0 < q.Td0
  Xd'_pos : 0 < q.Xd' + q.Xe
  Xd_pos : 0 < q.Xd + q.Xe
  Xq_pos : 0 < q.Xq + q.Xe

namespace Model

variable (x : Model)

/-- The selected point `(δ*, 0, E'_q*)`. -/
def point : State 3 := mk3 x.δ 0 x.E

/-- The field translated so that the selected point is the origin. -/
def field (z : State 3) : State 3 := x.q.field (z + x.point)

@[tmio M, powerlib_domain] private theorem K₃_pos : 0 < x.q.K₃ :=
  div_pos x.Xd'_pos x.Xd_pos

/-- The linearization at the selected point, a member of `Synchronous.FluxDecay.family`. -/
def linearization : FluxDecay.Model :=
  ⟨x.q.linParams x.δ x.E, x.H_pos, x.ω₀_pos, x.K₃_pos, x.Td0_pos⟩

/-- The selected point is an equilibrium exactly when the torque and the field EMF balance:
`T_e(δ*, E'_q*) = T_m`, `E'_q* + (X_d − X'_d) i_d = E_fd`. -/
@[tmio M, powerlib_domain] theorem field_point_eq_zero_iff :
    x.q.field x.point = 0 ↔ x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd := by
  have hH : 2 * x.q.H ≠ 0 := by have := x.H_pos; positivity
  have hT := x.Td0_pos.ne'
  constructor
  · intro h
    have e1 := congrArg (fun v : State 3 => v 1) h
    have e2 := congrArg (fun v : State 3 => v 2) h
    simp only [Machine.field, point, mk3_zero, mk3_one, mk3_two, PiLp.zero_apply, mul_zero,
      sub_zero] at e1 e2
    rw [div_eq_zero_iff] at e1 e2
    exact ⟨by linarith [e1.resolve_right hH], by linarith [e2.resolve_right hT]⟩
  · rintro ⟨h1, h2⟩
    refine state3_ext ?_ ?_ ?_ <;>
      simp [Machine.field, point, h1, h2]

@[tmio M, powerlib_domain] private theorem contDiff_field : ContDiff ℝ 1 x.q.field :=
  x.q.contDiff_field x.Xd'_pos.ne' x.Xq_pos.ne'

/-- The Jacobian at the selected point is the linearization's state matrix. -/
@[tmio M, powerlib_domain] theorem fderiv_point :
    fderiv ℝ x.q.field x.point =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) x.linearization.plant.A := by
  rw [x.q.fderiv_field x.Xd'_pos.ne' x.Xq_pos.ne' x.H_pos.ne' x.Td0_pos.ne']
  simp [point, linearization, FluxDecay.Model.plant]

@[tmio M, powerlib_domain] private theorem fderiv_field_zero :
    fderiv ℝ x.field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) x.linearization.plant.A := by
  have h : HasFDerivAt x.field
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) x.linearization.plant.A) 0 := by
    have hf : HasFDerivAt x.q.field
        (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) x.linearization.plant.A) (0 + x.point) := by
      rw [zero_add, ← x.fderiv_point]
      exact (x.contDiff_field.differentiable one_ne_zero x.point).hasFDerivAt
    have := hf.comp (0 : State 3) ((hasFDerivAt_id (0 : State 3)).add_const x.point)
    simp only [Function.comp_def, id, ContinuousLinearMap.comp_id] at this
    exact this
  exact h.fderiv

end Model

/-- The one-axis family (`Spectral.localFamily`): every model read as its field about the
selected point; `stable` an equilibrium whose linearization satisfies the Routh–Hurwitz
conditions, `unstable` an equilibrium whose linearization strictly violates one. -/
def family : Family Model Spectral.Requirement 3 0 :=
  Spectral.localFamily Model.field
    (fun x => (x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd) ∧
      0 < FluxDecay.coeff2 x.linearization.p ∧ 0 < FluxDecay.coeff0 x.linearization.p ∧
        0 < FluxDecay.routhQuantity x.linearization.p)
    (fun x => (x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd) ∧
      (FluxDecay.coeff0 x.linearization.p < 0 ∨ FluxDecay.coeff2 x.linearization.p < 0 ∨
        FluxDecay.routhQuantity x.linearization.p < 0))

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  Spectral.localFamily_isAutonomous _ _ _

/-- A flow sentence of a model is read on the untranslated field at the selected point. -/
@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {x : Model} {P : Flow.Property} :
    x ∈ family.den (.flow P) ↔ P.holds x.q.field x.point :=
  Spectral.mem_den_flow_iff_shift (f := fun x : Model => x.q.field) (pt := Model.point)
    family_isAutonomous

/-- Every translation of the one-axis family is sound (`Spectral.chain_le_semantics_of_jacobian`):
at an equilibrium the Routh–Hurwitz conditions of the linearization give local exponential
stability, a strict violation a characteristic root in the open right half plane, hence
instability. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_jacobian (F := family) (Rs := {.stable})
    (Ru := {.unstable}) (fun x P => mem_den_flow_iff) family_isAutonomous.den_passive
    (fun _ => rfl) (fun x => x.linearization.plant.A) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_)
  · have heq : x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd := by
      rcases hx with hx | hx
      · exact ((Spectral.mem_realize_singleton (meets := family.meets)).mp hx).1
      · exact ((Spectral.mem_realize_singleton (meets := family.meets)).mp hx).1
    exact ⟨x.contDiff_field, x.field_point_eq_zero_iff.mpr heq, x.fderiv_point⟩
  · have h := ((Spectral.mem_realize_singleton (meets := family.meets)).mp hx).2
    exact (FluxDecay.isHurwitz_stateMatrix_iff _ x.H_pos x.linearization.K₃_pos
      x.Td0_pos).mpr h
  · have h := ((Spectral.mem_realize_singleton (meets := family.meets)).mp hx).2
    exact FluxDecay.exists_root_of_unstable _ x.H_pos x.linearization.K₃_pos x.Td0_pos h

/-- Local exponential stability is translated exactly: a model is locally exponentially stable
exactly when the selected point is an equilibrium whose linearization satisfies the Routh–Hurwitz
conditions (converse linearization, `Spectral.local_exact_of_jacobian`). -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_exact_of_jacobian (fun x => x.linearization.plant.A)
    (fun x => ?_) (fun x => x.fderiv_field_zero) (fun x => ?_)
  · exact x.contDiff_field.comp (contDiff_id.add contDiff_const)
  · have h0 : x.field 0 = x.q.field x.point := by simp [Model.field]
    rw [h0, x.field_point_eq_zero_iff,
      show x.linearization.plant.A = x.linearization.p.stateMatrix from rfl,
      FluxDecay.isHurwitz_stateMatrix_iff _ x.H_pos x.linearization.K₃_pos x.Td0_pos]

/-- A selected point that is not an equilibrium is unstable
(`Spectral.mem_den_unstable_of_ne_zero`): the solution through it leaves it. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_not_equilibrium (x : Model)
    (h : ¬ (x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd)) :
    connection% (x ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.mem_den_unstable_of_ne_zero (fun x P => mem_den_flow_iff) x.contDiff_field
    fun h0 => h (x.field_point_eq_zero_iff.mp h0)

/-! ## The linearization -/

/-- **Local exponential stability through the linearization.** At an equilibrium, the one-axis
machine is locally exponentially stable exactly when its Heffron–Phillips linearization satisfies
the attractive sentences of `Synchronous.FluxDecay.family` (converse linearization,
`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_linearization
    (x : Model) (heq : x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable) ↔
      x.linearization ∈ FluxDecay.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff, (connection_proof% FluxDecay.family_isLinear.mem_den_hurwitz hP)]
  change LocallyExponentiallyStable x.q.field x.point ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ x.contDiff_field
    x.fderiv_point]
  exact ⟨fun h => h.2, fun h => ⟨x.field_point_eq_zero_iff.mpr heq, h⟩⟩

/-- **Instability through the linearization.** At an equilibrium whose linearization meets the
instability requirement of `Synchronous.FluxDecay.family` (a strict violation of a Routh
condition), the one-axis machine is unstable (`Dynamics.unstable_of_characteristic_root_re_pos`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_linearization (x : Model)
    (heq : x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd)
    (h : x.linearization ∈ realize FluxDecay.family.meets {.unstable}) :
    connection% (x ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨s, hs, hre⟩ := FluxDecay.exists_root_of_unstable _ x.H_pos x.linearization.K₃_pos
    x.Td0_pos ((Spectral.mem_realize_singleton (meets := FluxDecay.family.meets)).mp h)
  exact mem_den_flow_iff.mpr (Dynamics.unstable_of_characteristic_root_re_pos _ x.contDiff_field
    (x.field_point_eq_zero_iff.mpr heq) x.fderiv_point hs hre)

/-- **The field winding damps the undamped machine.** Without damping torque (`D = 0`), at an
equilibrium in the normal operating range `0 < δ* < π` with `V > 0` and `X_d > X'_d`, the one-axis
machine is locally exponentially stable exactly when the steady-state synchronizing coefficient
`K₁ − K₂K₃K₄` is positive (`K₂, K₄ > 0` there, `Synchronous.FluxDecay.mem_den_undamped_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_undamped_iff (x : Model)
    (heq : x.q.torque x.δ x.E = x.q.Tm ∧ x.q.fieldEMF x.δ x.E = x.q.Efd) (hD : x.q.D = 0)
    (hV : 0 < x.q.V) (hX : x.q.Xd' < x.q.Xd) (h0 : 0 < x.δ) (hπ : x.δ < Real.pi) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable) ↔
      x.q.K₂ x.δ * x.q.K₃ * x.q.K₄ x.δ < x.q.K₁ x.δ x.E) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_locallyExponentiallyStable_iff_linearization x heq
      (P := .locallyExponentiallyStable) (Or.inl trivial)),
    (connection_proof% FluxDecay.mem_den_undamped_iff x.linearization hD
      (P := .locallyExponentiallyStable) (Or.inl trivial))]
  have h24 : 0 < x.q.K₂ x.δ * x.q.K₄ x.δ :=
    mul_pos (x.q.K₂_pos x.Xd'_pos hV h0 hπ) (x.q.K₄_pos x.Xd'_pos hV hX h0 hπ)
  exact ⟨fun h => h.2, fun h => ⟨h24, h⟩⟩

end powerlib.Synchronous.OneAxis
