import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.LTI.Plant

/-! # Grid-forming synchronization following a moving grid: linearization and transfer functions

The grid-forming converter synchronizes by its own power loop (VSM, or droop with a power filter,
which is the same loop, `theorem/GridTiedConverter/GFM/DroopVSM.lean`), not by a phase detector.
This module formalizes the reduced loop with the grid angle as an input and derives, from the
model's linearization, the GFM counterparts of the PLL transfer functions `H_pll`
(`theorem/GridTiedConverter/PLL/Linear.lean`).

Model boundary.
* Reduced (quasi-static line) GFM of the base model: voltage source `E∠θ` behind `R + jX` to a
  stiff grid `V∠θ_g`, per unit, dq frame rotating at the nominal frequency `ω₀`; active power
  export-positive (`P_e(δ) = c₀ + A sin(δ − α)`, `c₀ = E²R/|Z|²`, `A = EV/|Z|`, `α = atan2(R, X)`,
  power angle `δ = θ − θ_g`). The power curve is the swing curve `SwingParams.Pe` with
  `k₁ = c₀`, `k₂ = A`, `k₃ = α` (`theorem/PowerSystem/Synchronous/Swing.lean`), the power reference
  is `P_m = P_ref`.
* Two-state loop, state `(θ, Δω)` in this order (converter angle and frequency deviation from
  `ω₀`), input the grid angle deviation `u = θ_g`: `θ̇ = Δω`, `M Δω̇ = P_ref − P_e(θ − u) − D Δω`
  (`angleField`). The same loop in the grid-angle state `(δ, Δω)`, input the grid frequency
  deviation `w = u̇`: `δ̇ = Δω − w`, `M Δω̇ = P_ref − P_e(δ) − D Δω` (`frequencyField`).
* Three-state loop (power filter, lossless line `P_e = K₀ sin δ`, the library model
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`): state `(θ, Δω, P_f)`, input `u`,
  `VSMLPF.fieldU` (`Ṗ_f = ω_c (K₀ sin(θ − u) − P_f)`); in the grid-angle state `(δ, Δω, P_f)`
  with input `w`: `filterFrequencyField`.
* Constant `E`, `P_ref`; excluded: line (electromagnetic) dynamics, voltage and current loops,
  Q–V droop, current limiting, delay, PWM; continuous time.
* Linearization at the operating point `(δ, 0)` (`(δ, 0, P_ref)` for three states) with grid angle
  `0`: the plants below have the Jacobians of these fields as state matrices
  (`SwingParams.jacobian`, `VSMLPF.jacobian`, from `fderiv`) and their input derivatives as input
  columns (`anglePlant_isLinearization`, `frequencyPlant_isLinearization`,
  `filterAnglePlant_isLinearization`, `filterFrequencyPlant_isLinearization`). Synchronizing
  coefficient `K = P_e'(δ) = A cos(δ − α)` (`K₀ cos δ` for three states).

Source: GFM counterpart study note t8 (tracking): derivation with the SymPy check
`s1_transfer.py` (outside the repository); Kundur, *Power System Stability and Control*
(1994) §5.1 (linearized swing equation); D'Arco, Suul, *Virtual synchronous machines —
classification of implementations and analysis of equivalence to droop controllers* (IEEE
PowerTech 2013) (VSM ≡ droop + LPF).

Results.
* Linearization: `hasFDerivAt_angleField`, `hasDerivAt_angleField_input`,
  `hasFDerivAt_frequencyField`, `hasDerivAt_frequencyField_input`, `hasDerivAt_fieldU_input`,
  `hasFDerivAt_filterFrequencyField`, `hasDerivAt_filterFrequencyField_input` and the plant
  readings `*_isLinearization`.
* Two-state transfer (both channels): `Δθ/Δθ_g = Δω/Δω_g = H(s) = K/(M s² + D s + K)`
  (`transfer_anglePlant`, `transfer_frequencyPlant`), `H(0) = 1` (`transferFn_zero`); on the
  infinite bus it is `VSMLPF.Tred` (`transfer_anglePlant_sinusoid`). Standard form
  `H = ω_n²/(s² + 2ζω_n s + ω_n²)` with `ω_n = √(K/M)` and `ζ = D/(2√(MK))` the natural frequency
  and damping ratio of the Jacobian (`transferFn_eq_standard`, `naturalFrequency_jacobian`;
  `SwingParams.dampingRatio_jacobian`); design `M = K/ω_b²`, `D = 2ζ₀K/ω_b` gives `ω_n = ω_b`,
  `ζ = ζ₀` (`tuning`). Unlike `H_pll` the GFM transfer has no zero: a pure second-order low-pass.
* Three-state transfer (both channels):
  `H₃(s) = ω_c K/((s + ω_c)(M s² + D s) + ω_c K)` (`transfer_filterAnglePlant`,
  `transfer_filterFrequencyPlant`), `H₃(0) = 1` (`filterTransferFn_zero`); at the loading angle it
  is `VSMLPF.Texact` (`transfer_filterAnglePlant_loading`), which `VSMLPF.lean` defines by its
  formula: this derives it from the model.

Family and connection conclusions.
No family: the results are linearizations and transfer functions of the formal model (static
evidence on the plants). The stability of the operating points is that of the swing and VSM +
filter families (`Synchronous.Swing.family`, `GFM.VSMLPF.family`); the tracking and
loss-of-synchronism conclusions are in `theorem/GridTiedConverter/GFM/Tracking/Synchronism.lean`.
-/

noncomputable section
namespace powerlib.GFM.Tracking
open Matrix
open powerlib.Dynamics (State mk3 mk3_zero state3_ext toEuclideanCLM_apply3)
open powerlib.Synchronous (SwingParams)

/-! ## The two-state loop with a moving grid -/

/-- The reduced GFM in the nominal frame with grid angle `u`: `θ̇ = Δω`,
`M Δω̇ = P_ref − P_e(θ − u) − D Δω`, i.e. the swing field at the power angle `θ − u`. -/
def angleField (p : SwingParams) (u : ℝ) (x : State 2) : State 2 :=
  p.field (x - PhasePlane.mk u 0)

/-- The same loop in the grid-angle state `(δ, Δω)` with the grid frequency deviation `w` as
input: `δ̇ = Δω − w`, `M Δω̇ = P_ref − P_e(δ) − D Δω`. -/
def frequencyField (p : SwingParams) (w : ℝ) (x : State 2) : State 2 :=
  p.field x - PhasePlane.mk w 0

@[tmio M, simp, powerlib_domain] theorem angleField_apply_zero (p : SwingParams) (u : ℝ)
    (x : State 2) : angleField p u x 0 = x 1 := by
  simp [angleField]

@[tmio M, simp, powerlib_domain] theorem angleField_apply_one (p : SwingParams) (u : ℝ)
    (x : State 2) : angleField p u x 1 = p.accel (x 0 - u) (x 1) := by
  simp [angleField]

@[tmio M, simp, powerlib_domain] theorem frequencyField_apply_zero (p : SwingParams) (w : ℝ)
    (x : State 2) : frequencyField p w x 0 = x 1 - w := by
  simp [frequencyField]

@[tmio M, simp, powerlib_domain] theorem frequencyField_apply_one (p : SwingParams) (w : ℝ)
    (x : State 2) : frequencyField p w x 1 = p.accel (x 0) (x 1) := by
  simp [frequencyField]

/-- State derivative of the angle loop: the swing Jacobian at the power angle `θ − u`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_angleField (p : SwingParams) (u : ℝ)
    (x : State 2) :
    HasFDerivAt (angleField p u)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (p.jacobian (x 0 - u))) x := by
  have h := (p.hasFDerivAt_field (x - PhasePlane.mk u 0)).comp x
    ((hasFDerivAt_id x).sub_const (PhasePlane.mk u 0))
  have he : (x - PhasePlane.mk u 0) 0 = x 0 - u := by simp
  rw [he, ContinuousLinearMap.comp_id] at h
  exact h

/-- The map `v ↦ x − (v, 0)` has the derivative `−(1, 0)`. -/
@[tmio T, powerlib_foundation] private lemma hasDerivAt_sub_mk (x : State 2) (u : ℝ) :
    HasDerivAt (fun v => x - PhasePlane.mk v 0) (-PhasePlane.mk 1 0) u := by
  have h : (fun v : ℝ => PhasePlane.mk v 0) = fun v => v • PhasePlane.mk 1 0 := by
    funext v
    refine PhasePlane.ext_iff'.2 ⟨by simp, by simp⟩
  have h1 : HasDerivAt (fun v : ℝ => PhasePlane.mk v 0) (PhasePlane.mk 1 0) u := by
    rw [h]
    simpa using (hasDerivAt_id u).smul_const (PhasePlane.mk 1 0)
  exact h1.const_sub x

/-- Input derivative of the angle loop: `∂f/∂u = (0, K(θ − u)/M)`, `K = P_e'`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_angleField_input (p : SwingParams) (u : ℝ)
    (x : State 2) :
    HasDerivAt (fun v => angleField p v x) (PhasePlane.mk 0 (p.syncCoeff (x 0 - u) / p.M)) u := by
  have h := (p.hasFDerivAt_field (x - PhasePlane.mk u 0)).comp_hasDerivAt u
    (hasDerivAt_sub_mk x u)
  have he : (x - PhasePlane.mk u 0) 0 = x 0 - u := by simp
  rw [he] at h
  refine h.congr_deriv (PhasePlane.ext_iff'.2 ⟨?_, ?_⟩)
  · simp [PhasePlane.toEuclideanCLM_apply_zero, SwingParams.jacobian]
  · simp [PhasePlane.toEuclideanCLM_apply_one, SwingParams.jacobian, neg_div]

/-- State derivative of the frequency loop: the swing Jacobian at `δ`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_frequencyField (p : SwingParams) (w : ℝ)
    (x : State 2) :
    HasFDerivAt (frequencyField p w)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (p.jacobian (x 0))) x :=
  (p.hasFDerivAt_field x).sub_const (PhasePlane.mk w 0)

/-- Input derivative of the frequency loop: `∂f/∂w = (−1, 0)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_frequencyField_input (p : SwingParams) (w : ℝ)
    (x : State 2) : HasDerivAt (fun v => frequencyField p v x) (PhasePlane.mk (-1) 0) w := by
  exact (hasDerivAt_sub_mk (p.field x) w).congr_deriv
    (PhasePlane.ext_iff'.2 ⟨by simp, by simp⟩)

/-! ## Linear plants of the two-state loop -/

/-- Grid-angle channel at the power angle `δ`: input `Δθ_g`, output converter angle `Δθ`. -/
def anglePlant (p : SwingParams) (δ : ℝ) : Linear.Plant 2 1 :=
  ⟨p.jacobian δ, !![0; p.syncCoeff δ / p.M], !![1, 0], 0⟩

/-- Grid-frequency channel at the power angle `δ`: state `(Δδ, Δω)`, input `Δω_g`, output the
converter frequency deviation `Δω`. -/
def frequencyPlant (p : SwingParams) (δ : ℝ) : Linear.Plant 2 1 :=
  ⟨p.jacobian δ, !![-1; 0], !![0, 1], 0⟩

@[tmio T, powerlib_foundation] private lemma toLp_col (a b : ℝ) :
    WithLp.toLp 2 (!![a; b] *ᵥ ![1]) = PhasePlane.mk a b := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;> simp [PhasePlane.mk, Matrix.mulVec, dotProduct]

/-- `anglePlant` is the linearization of `angleField` at `(δ, 0)` with grid angle `0`: its state
matrix is the state derivative and its input column the input derivative. -/
@[tmio M, powerlib_domain] theorem anglePlant_isLinearization (p : SwingParams) (δ : ℝ) :
    HasFDerivAt (angleField p 0) (Linear.op (anglePlant p δ).A) (PhasePlane.mk δ 0) ∧
      HasDerivAt (fun u => angleField p u (PhasePlane.mk δ 0))
        (WithLp.toLp 2 ((anglePlant p δ).B *ᵥ ![1])) 0 := by
  have h1 := hasFDerivAt_angleField p 0 (PhasePlane.mk δ 0)
  have h2 := hasDerivAt_angleField_input p 0 (PhasePlane.mk δ 0)
  rw [PhasePlane.mk_apply_zero, sub_zero] at h1 h2
  refine ⟨h1, ?_⟩
  rw [show (anglePlant p δ).B = !![0; p.syncCoeff δ / p.M] from rfl, toLp_col]
  exact h2

/-- `frequencyPlant` is the linearization of `frequencyField` at `(δ, 0)` with `w = 0`. -/
@[tmio M, powerlib_domain] theorem frequencyPlant_isLinearization (p : SwingParams) (δ : ℝ) :
    HasFDerivAt (frequencyField p 0) (Linear.op (frequencyPlant p δ).A) (PhasePlane.mk δ 0) ∧
      HasDerivAt (fun w => frequencyField p w (PhasePlane.mk δ 0))
        (WithLp.toLp 2 ((frequencyPlant p δ).B *ᵥ ![1])) 0 := by
  refine ⟨hasFDerivAt_frequencyField p 0 (PhasePlane.mk δ 0), ?_⟩
  rw [show (frequencyPlant p δ).B = !![-1; 0] from rfl, toLp_col]
  exact hasDerivAt_frequencyField_input p 0 (PhasePlane.mk δ 0)

/-- The GFM synchronization transfer `H(s) = K/(M s² + D s + K)`, `K = P_e'(δ)`. -/
def transferFn (p : SwingParams) (δ : ℝ) (s : ℂ) : ℂ :=
  (p.syncCoeff δ : ℂ) / ((p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s + (p.syncCoeff δ : ℂ))

@[tmio M, powerlib_domain] private lemma characteristicMatrix_jacobian (p : SwingParams)
    (δ : ℝ) (s : ℂ) :
    Linear.characteristicMatrix (p.jacobian δ) s =
      !![s, -1; (p.syncCoeff δ : ℂ) / p.M, s + (p.D : ℂ) / p.M] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Linear.characteristicMatrix, SwingParams.jacobian, neg_div, sub_eq_add_neg]

@[tmio M, powerlib_domain] private lemma det_characteristicMatrix_jacobian (p : SwingParams)
    {δ : ℝ} (hM : p.M ≠ 0) (s : ℂ) :
    (Linear.characteristicMatrix (p.jacobian δ) s).det =
      ((p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s + (p.syncCoeff δ : ℂ)) / p.M := by
  have hM' : (p.M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [eq_div_iff hM', mul_comm, p.characteristic_polynomial hM δ s]

@[tmio M, powerlib_domain] private lemma transfer_jacobian_model (p : SwingParams) {δ : ℝ}
    (hM : p.M ≠ 0) (B : Matrix (Fin 2) (Fin 1) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ) (s : ℂ) :
    Linear.transfer (⟨p.jacobian δ, B, C, 0⟩ : Linear.Plant 2 1) s =
      (((p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s + (p.syncCoeff δ : ℂ)) / p.M)⁻¹ •
        (Linear.complexify C * !![s + (p.D : ℂ) / p.M, 1; -((p.syncCoeff δ : ℂ) / p.M), s] *
          Linear.complexify B) := by
  rw [Linear.transfer_eq_adjugate]
  simp only
  rw [det_characteristicMatrix_jacobian p hM, characteristicMatrix_jacobian, adjugate_fin_two_of]
  simp [Linear.complexify]

/-- Grid angle to converter angle: `Δθ(s)/Δθ_g(s) = H(s) = K/(M s² + D s + K)` (`M ≠ 0`). -/
@[tmio M, powerlib_domain] theorem transfer_anglePlant (p : SwingParams) {δ : ℝ} (hM : p.M ≠ 0)
    (s : ℂ) : Linear.transfer (anglePlant p δ) s = !![transferFn p δ s] := by
  have hM' : (p.M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [anglePlant, transfer_jacobian_model p hM]
  ext i j; fin_cases i; fin_cases j
  simp [transferFn, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

/-- Grid frequency to converter frequency: `Δω(s)/Δω_g(s) = H(s)`, the same transfer. -/
@[tmio M, powerlib_domain] theorem transfer_frequencyPlant (p : SwingParams) {δ : ℝ}
    (hM : p.M ≠ 0) (s : ℂ) : Linear.transfer (frequencyPlant p δ) s = !![transferFn p δ s] := by
  have hM' : (p.M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [frequencyPlant, transfer_jacobian_model p hM]
  ext i j; fin_cases i; fin_cases j
  simp [transferFn, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

/-- Unit DC gain `H(0) = 1` (`K ≠ 0`): the converter follows a grid angle or frequency step. -/
@[tmio M, powerlib_domain] theorem transferFn_zero (p : SwingParams) {δ : ℝ}
    (hK : p.syncCoeff δ ≠ 0) : transferFn p δ 0 = 1 := by
  have hK' : (p.syncCoeff δ : ℂ) ≠ 0 := by exact_mod_cast hK
  simp [transferFn, hK']

/-- On the infinite bus (`P_e = K₀ sin δ`) at the loading angle the transfer is the second-order
swing reduction `VSMLPF.Tred` of the three-state model. -/
@[tmio M, powerlib_domain] theorem transfer_anglePlant_sinusoid (g : VSMLPF) (hM : g.M ≠ 0)
    (s : ℂ) :
    Linear.transfer (anglePlant (SwingParams.sinusoid g.M g.D g.P0 g.K0) g.δ0) s =
      !![g.Tred s] := by
  rw [transfer_anglePlant _ (by simpa using hM)]
  simp [transferFn, VSMLPF.Tred, VSMLPF.K]

/-- `ω_n = √(K/M)`: the natural frequency of the Jacobian (`det J = K/M`). -/
@[tmio M, powerlib_domain] theorem naturalFrequency_jacobian (p : SwingParams) (δ : ℝ) :
    Criteria.naturalFrequency (p.jacobian δ) = Real.sqrt (p.syncCoeff δ / p.M) := by
  rw [Criteria.naturalFrequency, SwingParams.det_jacobian]

/-- Standard second-order form `H(s) = ω_n²/(s² + 2ζω_n s + ω_n²)` with the natural frequency
and damping ratio of the Jacobian (`M > 0`, `K > 0`;
`Criteria.det_characteristicMatrix_standard`). -/
@[tmio M, powerlib_domain] theorem transferFn_eq_standard (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hK : 0 < p.syncCoeff δ) (s : ℂ) :
    transferFn p δ s =
      (Criteria.naturalFrequency (p.jacobian δ) : ℂ) ^ 2 /
        (s ^ 2 + 2 * (Criteria.dampingRatio (p.jacobian δ) : ℂ) *
          (Criteria.naturalFrequency (p.jacobian δ) : ℂ) * s +
          (Criteria.naturalFrequency (p.jacobian δ) : ℂ) ^ 2) := by
  have hdet : 0 < (p.jacobian δ).det := by rw [SwingParams.det_jacobian]; positivity
  rw [← Criteria.det_characteristicMatrix_standard _ hdet,
    det_characteristicMatrix_jacobian p hM.ne', ← Complex.ofReal_pow,
    Criteria.naturalFrequency_sq _ hdet.le, SwingParams.det_jacobian, transferFn]
  have hM' : (p.M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  rw [div_div_div_cancel_right₀ hM']

/-- Design rule: `M = K/ω_b²`, `D = 2ζ₀K/ω_b` give `ω_n = ω_b` and `ζ = ζ₀` (`K, ω_b > 0`). -/
@[tmio M, powerlib_domain] theorem tuning (p : SwingParams) {δ ωb ζ₀ : ℝ}
    (hK : 0 < p.syncCoeff δ) (hω : 0 < ωb) (hM : p.M = p.syncCoeff δ / ωb ^ 2)
    (hD : p.D = 2 * ζ₀ * p.syncCoeff δ / ωb) :
    Criteria.naturalFrequency (p.jacobian δ) = ωb ∧ Criteria.dampingRatio (p.jacobian δ) = ζ₀ := by
  have hM0 : 0 < p.M := by rw [hM]; positivity
  have hn : Criteria.naturalFrequency (p.jacobian δ) = ωb := by
    rw [naturalFrequency_jacobian, hM, show p.syncCoeff δ / (p.syncCoeff δ / ωb ^ 2) = ωb ^ 2 by
      field_simp, Real.sqrt_sq hω.le]
  refine ⟨hn, ?_⟩
  rw [p.dampingRatio_jacobian hM0 hK, hD, hM,
    show p.syncCoeff δ / ωb ^ 2 * p.syncCoeff δ = (p.syncCoeff δ / ωb) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  field_simp

/-! ## The three-state loop with a power filter -/

/-- Input derivative of the three-state loop `VSMLPF.fieldU`:
`∂f/∂u = (0, 0, −ω_c K₀ cos(θ − u))`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_fieldU_input (g : VSMLPF) (u : ℝ) (x : State 3) :
    HasDerivAt (fun v => g.fieldU v x) (mk3 0 0 (-(g.ωc * (g.K0 * Real.cos (x 0 - u))))) u := by
  have hsub : HasDerivAt (fun v => x - mk3 v 0 0) (-mk3 1 0 0) u := by
    have h : (fun v : ℝ => mk3 v 0 0) = fun v => v • mk3 1 0 0 := by
      funext v
      exact state3_ext (by simp) (by simp) (by simp)
    have h1 : HasDerivAt (fun v : ℝ => mk3 v 0 0) (mk3 1 0 0) u := by
      rw [h]
      simpa using (hasDerivAt_id u).smul_const (mk3 1 0 0)
    exact h1.const_sub x
  have h := (g.hasFDerivAt_field (x - mk3 u 0 0)).comp_hasDerivAt u hsub
  have he : (x - mk3 u 0 0) 0 = x 0 - u := by simp
  rw [he] at h
  refine h.congr_deriv (state3_ext ?_ ?_ ?_) <;> simp [toEuclideanCLM_apply3, VSMLPF.jacobian]

/-- The three-state loop in the grid-angle state `(δ, Δω, P_f)` with the grid frequency deviation
`w` as input: `δ̇ = Δω − w`, `M Δω̇ = P₀ − P_f − D Δω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)`. -/
def filterFrequencyField (g : VSMLPF) (w : ℝ) (x : State 3) : State 3 :=
  g.field x - mk3 w 0 0

@[tmio M, powerlib_domain] theorem hasFDerivAt_filterFrequencyField (g : VSMLPF) (w : ℝ)
    (x : State 3) :
    HasFDerivAt (filterFrequencyField g w)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (g.jacobian (x 0))) x :=
  (g.hasFDerivAt_field x).sub_const (mk3 w 0 0)

@[tmio M, powerlib_domain] theorem hasDerivAt_filterFrequencyField_input (g : VSMLPF) (w : ℝ)
    (x : State 3) : HasDerivAt (fun v => filterFrequencyField g v x) (mk3 (-1) 0 0) w := by
  have h : (fun v : ℝ => mk3 v 0 0) = fun v => v • mk3 1 0 0 := by
    funext v
    exact state3_ext (by simp) (by simp) (by simp)
  have h1 : HasDerivAt (fun v : ℝ => mk3 v 0 0) (mk3 1 0 0) w := by
    rw [h]
    simpa using (hasDerivAt_id w).smul_const (mk3 1 0 0)
  exact (h1.const_sub (g.field x)).congr_deriv (state3_ext (by simp) (by simp) (by simp))

/-- Grid-angle channel of the three-state loop at `δ`: input `Δθ_g`, output `Δθ`. -/
def filterAnglePlant (g : VSMLPF) (δ : ℝ) : Linear.Plant 3 1 :=
  ⟨g.jacobian δ, !![0; 0; -(g.ωc * (g.K0 * Real.cos δ))], !![1, 0, 0], 0⟩

/-- Grid-frequency channel of the three-state loop at `δ`: state `(Δδ, Δω, ΔP_f)`, input
`Δω_g`, output `Δω`. -/
def filterFrequencyPlant (g : VSMLPF) (δ : ℝ) : Linear.Plant 3 1 :=
  ⟨g.jacobian δ, !![-1; 0; 0], !![0, 1, 0], 0⟩

@[tmio T, powerlib_foundation] private lemma toLp_col3 (a b c : ℝ) :
    WithLp.toLp 2 (!![a; b; c] *ᵥ ![1]) = mk3 a b c := by
  refine state3_ext ?_ ?_ ?_ <;> simp [mk3, Matrix.mulVec, dotProduct]

/-- `filterAnglePlant` is the linearization of `VSMLPF.fieldU` at `(δ, 0, P₀)`, `u = 0`. -/
@[tmio M, powerlib_domain] theorem filterAnglePlant_isLinearization (g : VSMLPF) (δ : ℝ) :
    HasFDerivAt (g.fieldU 0) (Linear.op (filterAnglePlant g δ).A) (mk3 δ 0 g.P0) ∧
      HasDerivAt (fun u => g.fieldU u (mk3 δ 0 g.P0))
        (WithLp.toLp 2 ((filterAnglePlant g δ).B *ᵥ ![1])) 0 := by
  have he : g.fieldU 0 = g.field := by
    funext x
    rw [VSMLPF.fieldU, show x - mk3 0 0 0 = x from state3_ext (by simp) (by simp) (by simp)]
  have h1 := g.hasFDerivAt_field (mk3 δ 0 g.P0)
  have h2 := hasDerivAt_fieldU_input g 0 (mk3 δ 0 g.P0)
  rw [mk3_zero] at h1 h2
  rw [sub_zero] at h2
  refine ⟨he ▸ h1, ?_⟩
  rw [show (filterAnglePlant g δ).B = !![0; 0; -(g.ωc * (g.K0 * Real.cos δ))] from rfl,
    toLp_col3]
  exact h2

/-- `filterFrequencyPlant` is the linearization of `filterFrequencyField` at `(δ, 0, P₀)`. -/
@[tmio M, powerlib_domain] theorem filterFrequencyPlant_isLinearization (g : VSMLPF) (δ : ℝ) :
    HasFDerivAt (filterFrequencyField g 0) (Linear.op (filterFrequencyPlant g δ).A)
        (mk3 δ 0 g.P0) ∧
      HasDerivAt (fun w => filterFrequencyField g w (mk3 δ 0 g.P0))
        (WithLp.toLp 2 ((filterFrequencyPlant g δ).B *ᵥ ![1])) 0 := by
  have h1 := hasFDerivAt_filterFrequencyField g 0 (mk3 δ 0 g.P0)
  rw [mk3_zero] at h1
  refine ⟨h1, ?_⟩
  rw [show (filterFrequencyPlant g δ).B = !![-1; 0; 0] from rfl, toLp_col3]
  exact hasDerivAt_filterFrequencyField_input g 0 (mk3 δ 0 g.P0)

/-- The three-state synchronization transfer `H₃(s) = ω_c K/((s + ω_c)(M s² + D s) + ω_c K)`,
`K = K₀ cos δ`. -/
def filterTransferFn (g : VSMLPF) (δ : ℝ) (s : ℂ) : ℂ :=
  (g.ωc : ℂ) * ((g.K0 * Real.cos δ : ℝ) : ℂ) /
    ((s + (g.ωc : ℂ)) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) +
      (g.ωc : ℂ) * ((g.K0 * Real.cos δ : ℝ) : ℂ))

@[tmio M, powerlib_domain] private lemma filter_det (g : VSMLPF) {δ : ℝ} (hM : g.M ≠ 0)
    (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ) s).det =
      ((s + (g.ωc : ℂ)) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) +
        (g.ωc : ℂ) * ((g.K0 * Real.cos δ : ℝ) : ℂ)) / g.M := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [eq_div_iff hM', mul_comm, g.characteristic_polynomial hM δ s]
  push_cast
  ring

/-- Grid angle to converter angle, three states: `Δθ/Δθ_g = H₃(s)` (`M ≠ 0`). -/
@[tmio M, powerlib_domain] theorem transfer_filterAnglePlant (g : VSMLPF) {δ : ℝ}
    (hM : g.M ≠ 0) (s : ℂ) :
    Linear.transfer (filterAnglePlant g δ) s = !![filterTransferFn g δ s] := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [filterAnglePlant, Linear.transfer_eq_adjugate]
  simp only
  rw [filter_det g hM]
  ext i j; fin_cases i; fin_cases j
  simp [filterTransferFn, Linear.complexify, Linear.characteristicMatrix,
    VSMLPF.jacobian, Matrix.adjugate_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
  field_simp

/-- Grid frequency to converter frequency, three states: `Δω/Δω_g = H₃(s)`. -/
@[tmio M, powerlib_domain] theorem transfer_filterFrequencyPlant (g : VSMLPF) {δ : ℝ}
    (hM : g.M ≠ 0) (s : ℂ) :
    Linear.transfer (filterFrequencyPlant g δ) s = !![filterTransferFn g δ s] := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [filterFrequencyPlant, Linear.transfer_eq_adjugate]
  simp only
  rw [filter_det g hM]
  ext i j; fin_cases i; fin_cases j
  simp [filterTransferFn, Linear.complexify, Linear.characteristicMatrix,
    VSMLPF.jacobian, Matrix.adjugate_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
  field_simp

/-- Unit DC gain `H₃(0) = 1` (`ω_c K ≠ 0`). -/
@[tmio M, powerlib_domain] theorem filterTransferFn_zero (g : VSMLPF) {δ : ℝ}
    (h : g.ωc * (g.K0 * Real.cos δ) ≠ 0) : filterTransferFn g δ 0 = 1 := by
  have h' : (g.ωc : ℂ) * ((g.K0 * Real.cos δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
  unfold filterTransferFn
  rw [show ((0 : ℂ) + (g.ωc : ℂ)) * ((g.M : ℂ) * 0 ^ 2 + (g.D : ℂ) * 0) +
      (g.ωc : ℂ) * ((g.K0 * Real.cos δ : ℝ) : ℂ) = (g.ωc : ℂ) * ((g.K0 * Real.cos δ : ℝ) : ℂ) by
    ring]
  exact div_self h'

/-- At the loading angle the derived three-state transfer is `VSMLPF.Texact`. -/
@[tmio M, powerlib_domain] theorem transfer_filterAnglePlant_loading (g : VSMLPF) (hM : g.M ≠ 0)
    (s : ℂ) : Linear.transfer (filterAnglePlant g g.δ0) s = !![g.Texact s] := by
  rw [transfer_filterAnglePlant g hM]
  rfl

end powerlib.GFM.Tracking
