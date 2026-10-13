import theorem.CurrentControl.PILoop
import theorem.Criteria.Jacobian
import theorem.DCLink.Locality
import theorem.DCLink.PowerBalance
import theorem.Dynamics.ConverseLinearization
import theorem.Flow.Shift

/-! # Current loop feeding the DC link: the full `ΔV_dc/Δi_d*` transfer (domain)

Model boundary.
* System: the d-axis PI current loop of a grid-following VSC (the single-axis loop of
  `CurrentControl/PILoop.lean`: one series R–L filter `L > 0`, `R`, PI gains `Kp`, `Ki`, ideal
  PCC-voltage feedforward and cross-decoupling) whose bridge power charges the DC-link
  capacitor `C > 0` through a lossless bridge. No DC-voltage outer loop (the input is the
  current reference `i_d*`; the closed outer loop with ideal current tracking is
  `VoltageControl.lean`).
* Frame and directions: PLL-aligned dq frame (`v_q = 0`, no PLL dynamics), stiff PCC voltage
  `v_d = V_d0`, `i_q ≡ 0`; AC current IN-positive (work-sync `conventions.md` §D1); DC source
  current `i_src` injected into the capacitor node, constant. Per-unit (no `3/2` factor),
  continuous time.
* State order `(i_d, ξ, V_dc)`, `ξ = ∫ (i_d* − i_d) dt`; input `i_d*`; output `V_dc`.
* Equations (nonlinear, `field`): `L i_d' = −R i_d + Kp (i_d* − i_d) + Ki ξ`, `ξ' = i_d* − i_d`,
  `C V_dc' = i_src + P_bridge / V_dc` with `P_bridge = v^conv_d i_d`,
  `v^conv_d = V_d0 − (Kp (i_d* − i_d) + Ki ξ)` (T-vsc-dc-voltage-control §1.1 with the bridge
  power of §1.1.1, i.e. the filter loss `R i²` and the inductor energy `L i i'` are kept:
  `P_bridge = V_d0 i − R i² − L i i'`, `vconv_mul_eq_bridgePower`, cf. `bridgePower_of_kvl`).
  `G_dc = 0`; no delay, PWM or limits.
  The field contains `1/V_dc` and is used on the open set `V_dc > 0`.
* Operating point (`eqState`): `i_d = i_d* = I_d0`, `Ki ξ0 = R I_d0`, `V_dc = V0 > 0`, with the
  source current balancing it, `i_src = −I_dc0`, `I_dc0 = (V_d0 − R I_d0) I_d0 / V0`
  (`> 0` rectifier, `< 0` inverter).

Results.
* `jacobian_eq`, `input_hasDerivAt`: the small-signal realization `model` (`A`, `B`) is the
  Jacobian of the nonlinear field and its derivative in `i_d*`, computed with `fderiv`.
* `transfer_eq`: `ΔV_dc/Δi_d* = ((V_d0 − 2 R I_d0) − s L I_d0) (Kp s + Ki) /
  ((L s² + (R + Kp) s + Ki)(C V0 s + I_dc0))`: the bridge-power factor of `PowerBalance.lean`
  (`bridgeTransfer`, the right-half-plane zero `V_d0/(L I_d0)` of §1.5 in rectifier mode when
  `R = 0`, `bridgeZero_pos_iff`) times the current loop times the DC node.
  This is the "完整推导" that §1.5 only sketches (`∝ (V_d0 − s L_f I_d0)/(denominator)`).
* `det_characteristicMatrix`, `isHurwitz_iff` (static): the realization is Hurwitz iff the
  current loop is (`R + Kp > 0 ∧ Ki > 0`) and `I_dc0 > 0` (rectifier).

## Families and connection conclusions

* `linearizedFamily : Family CascadeParams Spectral.Requirement 3 1` reads the parameters as the
  port system of the small-signal plant `model` (input `Δi_d*`, output `ΔV_dc`;
  `Spectral.linearFamily`). Requirements: the PI loop's positive monic coefficients and a
  positive DC-node coefficient `I_dc0/(C V0)` (`stable`), or a negative one of them
  (`unstable`). `linearizedChain_le_semantics`, `linearizedExact`; `linearizedDen_eq`: its
  attractive denotation is the PI family's pulled back along `pi`, cut by `I_dc0/(C V0) > 0`;
  `linearized_mem_den_iff` (formerly `exponentiallyStable_iff`): with `L, C, V0 > 0`, stable iff
  `R + Kp > 0 ∧ Ki > 0 ∧ I_dc0 > 0`.
* `family : Family CascadeParams Spectral.Requirement 3 0` reads the parameters as the
  nonlinear field with `i_d* = I_d0` translated so that `eqState` is the origin
  (`Spectral.localFamily`, `Flow.Property.holds_shift_iff`). Requirements: `stable` —
  `L, C, V0 > 0`, `R + Kp > 0`, `Ki > 0`, `I_dc0 > 0`; `unstable` — `C, V0 > 0`, `Ki ≠ 0`,
  `I_dc0 < 0`. `chain_le_semantics`, `exact_passive`; `mem_den_locallyExponentiallyStable`
  (formerly `locallyExponentiallyStable`): rectifier mode with a stable current loop is locally
  exponentially stable; `mem_den_unstable_of_inverter` (formerly `unstable_of_inverter`): in
  inverter mode (`I_dc0 < 0`) the plant is unstable, whatever the current-loop gains (the
  open-loop pole `−I_dc0/(C V0)` of §1.4 survives the inner loop).
  Within `L, C, V0 > 0` the local exponential translation is exact
  (`mem_den_locallyExponentiallyStable_iff`: locally exponentially stable iff `R + Kp > 0`,
  `Ki > 0`, `I_dc0 > 0`; converse linearization for fields that are `C¹` on `V_dc > 0`,
  `Dynamics.isHurwitz_of_locallyExponentiallyStable_local`; with `Ki = 0` the integrator direction
  is killed by the Jacobian). Outside that range it is not exact
  (`not_exact_locallyExponentiallyStable`: the negative-inductance cascade
  `negativeInductance` is locally exponentially stable).
The Jacobian, the transfer function and its zeros are static evidence.

Source: work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.1.1, §1.4, §1.5;
`theory/T-gfl-control.md` §1.4.1.
-/

noncomputable section
namespace powerlib.DCLink
open Matrix Filter
open scoped Topology
open powerlib.Dynamics LinearSystems

/-- Parameters: the PI current loop, DC-link capacitance, PCC voltage, DC operating voltage
and operating d-axis current. -/
@[ext] structure CascadeParams where
  /-- Current-loop axis `(L, R, Kp, Ki)`. -/
  pi : CurrentControl.PIParams
  /-- DC-link capacitance. -/
  C : ℝ
  /-- Stiff PCC d-axis voltage. -/
  Vd0 : ℝ
  /-- DC operating voltage `V0`. -/
  V0 : ℝ
  /-- Operating d-axis current `I_d0`. -/
  Id0 : ℝ

namespace CascadeParams

variable (p : CascadeParams)

/-- DC-side operating current `I_dc0 = P_bridge,0 / V0 = (V_d0 − R I_d0) I_d0 / V0`. -/
def Idc0 : ℝ := (p.Vd0 - p.pi.R * p.Id0) * p.Id0 / p.V0

/-- Constant DC source current balancing the operating point. -/
def isrc : ℝ := -p.Idc0

/-- Bridge voltage `v^conv_d = V_d0 − (Kp (i* − i) + Ki ξ)`. -/
def vconv (r : ℝ) (x : State 3) : ℝ := p.Vd0 - (p.pi.Kp * (r - x 0) + p.pi.Ki * x 1)

/-- Nonlinear plant with reference `r = i_d*`, state `(i_d, ξ, V_dc)`. -/
def field (r : ℝ) (x : State 3) : State 3 :=
  WithLp.toLp 2 ![(-p.pi.R * x 0 + p.pi.Kp * (r - x 0) + p.pi.Ki * x 1) / p.pi.L, r - x 0,
    (p.isrc + p.vconv r x * x 0 / x 2) / p.C]

/-- The bridge power used by the field is the filter KVL bridge power `v^conv · i`
(`P_bridge = V_d0 i − R i² − L i i'`, `i_q = 0`). -/
@[powerlib_foundation] theorem vconv_mul_eq_bridgePower (hL : p.pi.L ≠ 0) (r : ℝ)
    (x : State 3) :
    p.vconv r x * x 0 =
      bridgePower p.Vd0 p.pi.R p.pi.L (x 0) 0 ((p.field r x) 0) 0 := by
  simp [vconv, bridgePower, field]
  field_simp
  ring

/-- Operating point `(I_d0, R I_d0/Ki, V0)`. -/
def eqState : State 3 := WithLp.toLp 2 ![p.Id0, p.pi.R * p.Id0 / p.pi.Ki, p.V0]

@[powerlib_foundation] theorem vconv_eqState (hKi : p.pi.Ki ≠ 0) :
    p.vconv p.Id0 p.eqState = p.Vd0 - p.pi.R * p.Id0 := by
  simp [vconv, eqState]
  field_simp

@[powerlib_foundation] theorem field_eqState (hKi : p.pi.Ki ≠ 0) :
    p.field p.Id0 p.eqState = 0 := by
  have hv := p.vconv_eqState hKi
  ext i
  fin_cases i
  · have h0 : -p.pi.R * p.Id0 + p.pi.Kp * (p.Id0 - p.Id0) +
        p.pi.Ki * (p.pi.R * p.Id0 / p.pi.Ki) = 0 := by
      field_simp
      ring
    simp only [field, eqState, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero,
      PiLp.zero_apply, Matrix.cons_val_one]
    rw [h0, zero_div]
  · simp [field, eqState]
  · simp only [field, PiLp.toLp_apply, PiLp.zero_apply]
    rw [hv]
    simp [isrc, Idc0, eqState]

/-! ## Small-signal realization -/

/-- State matrix (block lower triangular: current loop, then DC node). -/
def stateMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(p.pi.R + p.pi.Kp) / p.pi.L, p.pi.Ki / p.pi.L, 0;
    -1, 0, 0;
    (p.Vd0 - p.pi.R * p.Id0 + p.pi.Kp * p.Id0) / (p.C * p.V0),
      -(p.pi.Ki * p.Id0) / (p.C * p.V0), -(p.Idc0 / (p.C * p.V0))]

/-- Linearization with input `Δi_d*` and output `ΔV_dc`. -/
def model : Linear.Plant 3 1 :=
  ⟨p.stateMatrix, !![p.pi.Kp / p.pi.L; 1; -(p.pi.Kp * p.Id0) / (p.C * p.V0)], !![0, 0, 1],
    !![0]⟩

/-- `C¹` on `V_dc > 0`. -/
def posV : Set (State 3) := {x | 0 < x 2}

@[powerlib_foundation] theorem isOpen_posV : IsOpen posV :=
  isOpen_lt continuous_const ((EuclideanSpace.proj (2 : Fin 3)).continuous)

@[powerlib_foundation] theorem field_contDiffOn (r : ℝ) : ContDiffOn ℝ 1 (p.field r) posV := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  · simp only [field, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
    apply ContDiff.contDiffOn
    fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply ContDiff.contDiffOn
    fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.reduceFinMk, Matrix.cons_val]
    apply ContDiffOn.div_const
    apply contDiffOn_const.add
    apply ContDiffOn.div _ (Criteria.contDiff_coord 2).contDiffOn
    · intro x hx
      exact ne_of_gt hx
    · apply ContDiff.contDiffOn
      unfold vconv
      fun_prop

private lemma hasFDerivAt_coord_inv (i : Fin 3) {x : State 3}
    (hx : x i ≠ 0) :
    HasFDerivAt (fun y : State 3 => (y i)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((x i) ^ 2)⁻¹)).comp (Criteria.coord i)) x :=
  (hasFDerivAt_inv hx).comp x (Criteria.hasFDerivAt_coord i x)

/-- The state matrix is the Jacobian of the nonlinear plant at the operating point. -/
@[powerlib_foundation] theorem jacobian_eq (hKi : p.pi.Ki ≠ 0) (hV : p.V0 ≠ 0) :
    fderiv ℝ (p.field p.Id0) p.eqState =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) p.stateMatrix := by
  set x := p.eqState with hxdef
  have hx2 : x 2 ≠ 0 := by simpa [hxdef, eqState] using hV
  have h0 := Criteria.hasFDerivAt_coord (0 : Fin 3) x
  have h1 := Criteria.hasFDerivAt_coord (1 : Fin 3) x
  have hvc : HasFDerivAt (p.vconv p.Id0) (p.pi.Kp • Criteria.coord 0 - p.pi.Ki • Criteria.coord 1)
      x := by
    have h := (((h0.const_sub p.Id0).const_mul p.pi.Kp).add (h1.const_mul p.pi.Ki)).const_sub
      p.Vd0
    convert h using 1
    · funext v
      simp [vconv]
    · ext v
      simp
      ring
  have hA := ((((h0.const_mul (-p.pi.R)).add ((h0.const_sub p.Id0).const_mul p.pi.Kp)).add
    (h1.const_mul p.pi.Ki)).mul_const p.pi.L⁻¹)
  have hB := h0.const_sub p.Id0
  have hC := (((hvc.mul h0).mul (hasFDerivAt_coord_inv 2 hx2)).const_add p.isrc).mul_const p.C⁻¹
  refine Criteria.fderiv_eq_toEuclideanCLM_of_components _
    ![p.pi.L⁻¹ • ((-p.pi.R) • Criteria.coord 0 + p.pi.Kp • -Criteria.coord 0 +
        p.pi.Ki • Criteria.coord 1),
      -Criteria.coord 0,
      p.C⁻¹ • ((p.vconv p.Id0 x * x 0) •
          (ContinuousLinearMap.toSpanSingleton ℝ (-(x 2 ^ 2)⁻¹)).comp (Criteria.coord 2) +
        (x 2)⁻¹ • (p.vconv p.Id0 x • Criteria.coord 0 +
          x 0 • (p.pi.Kp • Criteria.coord 0 - p.pi.Ki • Criteria.coord 1)))] ?_ ?_
  · intro i
    fin_cases i
    · convert hA using 1
      · funext y
        simp [field, div_eq_mul_inv]
      · rfl
    · convert hB using 1
      · funext y
        simp [field]
      · rfl
    · convert hC using 1
      · funext y
        simp [field, div_eq_mul_inv, mul_assoc]
      · rfl
  · intro i v
    have hv : p.vconv p.Id0 x = p.Vd0 - p.pi.R * p.Id0 := p.vconv_eqState hKi
    fin_cases i
    · simp [stateMatrix, Fin.sum_univ_three]
      ring
    · simp [stateMatrix, Fin.sum_univ_three]
    · simp only [Fin.reduceFinMk, Matrix.cons_val, _root_.smul_apply, _root_.add_apply,
        _root_.sub_apply, hv]
      simp [stateMatrix, Fin.sum_univ_three, hxdef, eqState, Idc0]
      field_simp
      ring

/-- The input matrix is the derivative of the plant in the reference `i_d*`. -/
@[powerlib_foundation] theorem input_hasDerivAt (hKi : p.pi.Ki ≠ 0) (k : Fin 3) :
    HasDerivAt (fun r => p.field r p.eqState k) (p.model.B k 0) p.Id0 := by
  have hv := p.vconv_eqState hKi
  fin_cases k
  · have h := (((hasDerivAt_id p.Id0).sub_const p.Id0).const_mul p.pi.Kp).const_add
      (-p.pi.R * p.Id0 + p.pi.Ki * (p.pi.R * p.Id0 / p.pi.Ki)) |>.div_const p.pi.L
    convert h using 1
    · funext r
      simp [field, eqState]
      ring
    · simp [model]
  · have h := (hasDerivAt_id p.Id0).sub_const p.Id0
    convert h using 1
    · funext r
      simp [field, eqState]
    · simp [model]
  · have h := ((((((hasDerivAt_id p.Id0).sub_const p.Id0).const_mul p.pi.Kp).const_add
      (p.pi.Ki * (p.pi.R * p.Id0 / p.pi.Ki))).const_sub p.Vd0).mul_const (p.Id0 / p.V0)).const_add
      p.isrc |>.div_const p.C
    convert h using 1
    · funext r
      simp [field, eqState, vconv]
      ring
    · simp [model]
      ring

/-! ## Spectrum and exponential stability -/

/-- Block-triangular characteristic polynomial: the current loop times `(s + I_dc0/(C V0))`. -/
@[powerlib_foundation] theorem det_characteristicMatrix (s : ℂ) :
    (Linear.characteristicMatrix p.stateMatrix s).det =
      (Linear.characteristicMatrix p.pi.model.A s).det * (s + ((p.Idc0 / (p.C * p.V0) : ℝ) : ℂ)) := by
  simp only [CurrentControl.PIParams.model, CurrentControl.det_characteristicMatrix_of]
  simp [Linear.characteristicMatrix, stateMatrix, Matrix.det_fin_three]
  ring

@[powerlib_foundation] theorem characteristic_root_iff (s : ℂ) :
    (Linear.characteristicMatrix p.stateMatrix s).det = 0 ↔
      (Linear.characteristicMatrix p.pi.model.A s).det = 0 ∨
        s = ((-(p.Idc0 / (p.C * p.V0)) : ℝ) : ℂ) := by
  rw [p.det_characteristicMatrix, mul_eq_zero]
  apply or_congr_right
  rw [add_eq_zero_iff_eq_neg]
  push_cast
  rfl

/-- Hurwitz iff the current loop is Hurwitz and the DC node pole `−I_dc0/(C V0)` is stable. -/
@[powerlib_foundation] theorem isHurwitz_iff_pi :
    LinearSystems.IsHurwitz p.stateMatrix ↔
      LinearSystems.IsHurwitz p.pi.model.A ∧ 0 < p.Idc0 / (p.C * p.V0) := by
  simp only [Criteria.isHurwitz_iff_characteristic_roots, p.characteristic_root_iff]
  constructor
  · intro h
    refine ⟨fun s hs => h s (Or.inl hs), ?_⟩
    have := h _ (Or.inr rfl)
    rw [Complex.ofReal_re] at this
    linarith
  · rintro ⟨h, hb⟩ s (hs | hs)
    · exact h s hs
    · rw [hs, Complex.ofReal_re]
      linarith

/-- With `L, C, V0 > 0`: Hurwitz iff `R + Kp > 0`, `Ki > 0` and `I_dc0 > 0` (rectifier). Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem isHurwitz_iff (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0) :
    LinearSystems.IsHurwitz p.stateMatrix ↔
      (0 < p.pi.R + p.pi.Kp ∧ 0 < p.pi.Ki) ∧ 0 < p.Idc0 := by
  rw [p.isHurwitz_iff_pi, p.pi.isHurwitz_iff hL, div_pos_iff_of_pos_right (mul_pos hC hV)]

/-- Rectifier mode with a stable current loop: the nonlinear plant is locally exponentially
stable at the operating point (`i_d* = I_d0` held constant). Implementation evidence for
`mem_den_locallyExponentiallyStable`. -/
private theorem locallyExponentiallyStable (hL : 0 < p.pi.L) (hC : 0 < p.C)
    (hV : 0 < p.V0) (hR : 0 < p.pi.R + p.pi.Kp) (hKi : 0 < p.pi.Ki) (hI : 0 < p.Idc0) :
    LocallyExponentiallyStable (p.field p.Id0) p.eqState :=
  locallyExponentiallyStable_of_isHurwitz_jacobian_local isOpen_posV
    (by simpa [posV, eqState] using hV) _ (p.field_contDiffOn _)
    (p.field_eqState hKi.ne') (p.jacobian_eq hKi.ne' hV.ne')
    ((p.isHurwitz_iff hL hC hV).2 ⟨⟨hR, hKi⟩, hI⟩)

private lemma stateMatrix_eigen :
    p.stateMatrix.map (algebraMap ℝ ℂ) *ᵥ ![0, 0, 1] =
      (((-(p.Idc0 / (p.C * p.V0))) : ℝ) : ℂ) • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [stateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Inverter mode (`I_dc0 < 0`): the nonlinear plant is unstable for every current-loop
tuning — the inner loop does not move the DC-node pole. Implementation evidence for
`mem_den_unstable_of_inverter`. -/
private theorem unstable_of_inverter (hC : 0 < p.C) (hV : 0 < p.V0)
    (hKi : p.pi.Ki ≠ 0) (hI : p.Idc0 < 0) :
    Unstable (p.field p.Id0) p.eqState :=
  unstable_of_jacobian_eigenvalue_re_pos_local isOpen_posV
    (by simpa [posV, eqState] using hV) _ (p.field_contDiffOn _)
    (p.field_eqState hKi) (p.jacobian_eq hKi hV.ne')
    ⟨_, _, fun h => by simpa using congrFun h 2, p.stateMatrix_eigen, by
      rw [Complex.ofReal_re]
      exact neg_pos.mpr (div_neg_of_neg_of_pos hI (mul_pos hC hV))⟩

/-! ## Transfer function `ΔV_dc/Δi_d*` -/

/-- Closed form of `ΔV_dc/Δi_d*`: bridge-power factor × current loop × DC node. Static evidence
on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem transfer_eq (hL : p.pi.L ≠ 0) (hC : p.C ≠ 0) (hV : p.V0 ≠ 0) {s : ℂ}
    (hs1 : (p.pi.L : ℂ) * s ^ 2 + (p.pi.R + p.pi.Kp) * s + p.pi.Ki ≠ 0)
    (hs2 : (p.C : ℂ) * p.V0 * s + p.Idc0 ≠ 0) :
    Linear.transfer p.model s 0 0 =
      bridgeTransfer p.Vd0 p.pi.R p.pi.L p.Id0 s * (p.pi.Kp * s + p.pi.Ki) /
        (((p.pi.L : ℂ) * s ^ 2 + (p.pi.R + p.pi.Kp) * s + p.pi.Ki) * (p.C * p.V0 * s + p.Idc0)) := by
  have hL' : (p.pi.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hC' : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hV' : (p.V0 : ℂ) ≠ 0 := by exact_mod_cast hV
  set Δ : ℂ := (p.pi.L : ℂ) * s ^ 2 + (p.pi.R + p.pi.Kp) * s + p.pi.Ki with hΔ
  set E : ℂ := (p.C : ℂ) * p.V0 * s + p.Idc0 with hE
  set M := Linear.characteristicMatrix p.model.A s with hM
  -- the response vector `(Δi_d, Δξ, ΔV_dc)/Δi_d*`
  set X : Matrix (Fin 3) (Fin 1) ℂ :=
    !![(p.pi.Kp * s + p.pi.Ki) / Δ; (p.pi.L * s + p.pi.R) / Δ;
      bridgeTransfer p.Vd0 p.pi.R p.pi.L p.Id0 s * (p.pi.Kp * s + p.pi.Ki) / (Δ * E)] with hX
  have hdet : M.det ≠ 0 := by
    have h1 : (Linear.characteristicMatrix p.pi.model.A s).det = Δ / p.pi.L :=
      p.pi.det_characteristicMatrix hL s
    have h2 : s + ((p.Idc0 / (p.C * p.V0) : ℝ) : ℂ) = E / (p.C * p.V0) := by
      rw [hE]
      push_cast
      field_simp
    rw [hM, show p.model.A = p.stateMatrix from rfl, p.det_characteristicMatrix, h1, h2]
    exact mul_ne_zero (div_ne_zero hs1 hL') (div_ne_zero hs2 (mul_ne_zero hC' hV'))
  have hMX : M * X = Linear.complexify p.model.B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, hX, Linear.characteristicMatrix, model, stateMatrix, Matrix.mul_apply,
        Fin.sum_univ_three, bridgeTransfer] <;>
      field_simp <;> ring
  have hsol : M⁻¹ * Linear.complexify p.model.B = X := by
    rw [← hMX, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hdet)]
  rw [Linear.transfer, ← hM, Matrix.mul_assoc, hsol]
  simp [hX, model, Matrix.mul_apply, Fin.sum_univ_three]

/-- The transfer vanishes exactly at the bridge-power zero and the PI zero (off the poles). -/
@[powerlib_foundation] theorem transfer_eq_zero_iff (hL : p.pi.L ≠ 0) (hC : p.C ≠ 0)
    (hV : p.V0 ≠ 0) {s : ℂ}
    (hs1 : (p.pi.L : ℂ) * s ^ 2 + (p.pi.R + p.pi.Kp) * s + p.pi.Ki ≠ 0)
    (hs2 : (p.C : ℂ) * p.V0 * s + p.Idc0 ≠ 0) :
    Linear.transfer p.model s 0 0 = 0 ↔
      bridgeTransfer p.Vd0 p.pi.R p.pi.L p.Id0 s = 0 ∨ (p.pi.Kp : ℂ) * s + p.pi.Ki = 0 := by
  rw [p.transfer_eq hL hC hV hs1 hs2, div_eq_zero_iff, mul_eq_zero, mul_eq_zero]
  simp [hs1, hs2]

/-! ## The families -/

/-- Stability condition of the linearization: the PI loop's positive monic coefficients and a
positive DC-node coefficient. -/
def LinStable : Prop := p.pi.Stable ∧ 0 < p.Idc0 / (p.C * p.V0)

/-- Instability condition of the linearization: a negative PI monic coefficient or a negative
DC-node coefficient. -/
def LinUnstable : Prop := p.pi.Unstable ∨ p.Idc0 / (p.C * p.V0) < 0

@[powerlib_foundation] theorem isHurwitz_iff_linStable :
    IsHurwitz p.model.A ↔ p.LinStable := by
  change IsHurwitz p.stateMatrix ↔ _
  rw [p.isHurwitz_iff_pi, CurrentControl.PIParams.isHurwitz_iff_div]
  rfl

@[powerlib_foundation] theorem exists_root_of_linUnstable (h : p.LinUnstable) :
    ∃ s : ℂ, (Linear.characteristicMatrix p.model.A s).det = 0 ∧ 0 < s.re := by
  change ∃ s : ℂ, (Linear.characteristicMatrix p.stateMatrix s).det = 0 ∧ 0 < s.re
  rcases h with h | h
  · obtain ⟨s, hs, hre⟩ := p.pi.exists_root_of_unstable h
    exact ⟨s, (p.characteristic_root_iff s).mpr (Or.inl hs), hre⟩
  · refine ⟨((-(p.Idc0 / (p.C * p.V0))) : ℝ), (p.characteristic_root_iff _).mpr (Or.inr rfl), ?_⟩
    rw [Complex.ofReal_re]
    linarith

/-- The translated nonlinear field: `i_d* = I_d0` held, `eqState` moved to the origin. -/
def shiftedField (z : State 3) : State 3 := p.field p.Id0 (z + p.eqState)

/-- Stability condition of the nonlinear plant: `L, C, V0 > 0`, a stable current loop and
rectifier operation. -/
def Stable : Prop :=
  0 < p.pi.L ∧ 0 < p.C ∧ 0 < p.V0 ∧ 0 < p.pi.R + p.pi.Kp ∧ 0 < p.pi.Ki ∧ 0 < p.Idc0

/-- Instability condition of the nonlinear plant: `C, V0 > 0`, `Ki ≠ 0`, inverter operation. -/
def Unstable : Prop := 0 < p.C ∧ 0 < p.V0 ∧ p.pi.Ki ≠ 0 ∧ p.Idc0 < 0

end CascadeParams

/-- The linearized cascade: every parameter set read as the port system of its small-signal
plant (input `Δi_d*`, output `ΔV_dc`). -/
def linearizedFamily : Family CascadeParams Spectral.Requirement 3 1 :=
  Spectral.linearFamily CascadeParams.model CascadeParams.LinStable CascadeParams.LinUnstable

@[powerlib_foundation] theorem linearizedFamily_isLinear :
    linearizedFamily.IsLinear CascadeParams.model :=
  Spectral.linearFamily_isLinear _ _ _

private theorem linearizedDen_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    linearizedFamily.den (.flow P) = {p | p.LinStable} :=
  Spectral.linear_den (U := CascadeParams.LinUnstable)
    (fun p => (CascadeParams.isHurwitz_iff_linStable p).symm) hP

/-- Every translation of the linearized cascade is sound. -/
@[powerlib_domain] theorem linearizedChain_le_semantics :
    connection% (∀ P, linearizedFamily.chain P ≤ linearizedFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics
    (fun p h => (CascadeParams.isHurwitz_iff_linStable p).mpr h)
    (fun p h => p.exists_root_of_linUnstable h)

/-- The attractive sentences and sampled contraction of the linearized cascade are carved out
exactly. -/
@[powerlib_domain] theorem linearizedExact {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (linearizedFamily.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun p => (CascadeParams.isHurwitz_iff_linStable p).symm) hP

/-- The DC node does not change the current loop's stability but adds its own pole: the
attractive denotation of the linearized cascade is the PI family's pulled back along `pi`, cut
by a positive DC-node coefficient `I_dc0/(C V0)`. -/
@[powerlib_domain] theorem linearizedDen_eq {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (linearizedFamily.den (.flow P) =
      CascadeParams.pi ⁻¹' CurrentControl.PIParams.family.den (.flow P) ∩
        {p | 0 < p.Idc0 / (p.C * p.V0)}) := by
  unfold powerlib.TMIO.Statement
  rw [linearizedDen_flow hP, CurrentControl.PIParams.family_isLinear.den_hurwitz hP]
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [CurrentControl.PIParams.isHurwitz_iff_div]
  rfl

/-- With `L, C, V0 > 0` the linearized current-loop/DC-link cascade satisfies an attractive
sentence iff the current loop is stable and the converter rectifies (`I_dc0 > 0`). -/
@[powerlib_domain] theorem linearized_mem_den_iff (p : CascadeParams) (hL : 0 < p.pi.L)
    (hC : 0 < p.C) (hV : 0 < p.V0) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (p ∈ linearizedFamily.den (.flow P) ↔
      p ∈ {p : CascadeParams | (0 < p.pi.R + p.pi.Kp ∧ 0 < p.pi.Ki) ∧ 0 < p.Idc0}) := by
  unfold powerlib.TMIO.Statement
  rw [linearizedDen_flow hP]
  change p.LinStable ↔ _
  rw [← CascadeParams.isHurwitz_iff_linStable]
  exact p.isHurwitz_iff hL hC hV

/-- The nonlinear current-loop/DC-link cascade about its operating point. -/
def family : Family CascadeParams Spectral.Requirement 3 0 :=
  Spectral.localFamily CascadeParams.shiftedField CascadeParams.Stable CascadeParams.Unstable

private theorem mem_den_flow {p : CascadeParams} {P : Flow.Property} :
    p ∈ family.den (.flow P) ↔ P.holds (p.field p.Id0) p.eqState :=
  (Spectral.localFamily_isAutonomous _ _ _).mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Every translation of the nonlinear cascade family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun p h => ?_) (fun p h => ?_)
  · obtain ⟨hL, hC, hV, hR, hKi, hI⟩ := h
    exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (p.locallyExponentiallyStable hL hC hV hR hKi hI)
  · obtain ⟨hC, hV, hKi, hI⟩ := h
    exact (Flow.Property.holds_shift_iff .unstable).mpr (p.unstable_of_inverter hC hV hKi hI)

/-- Passivity is translated exactly: the autonomous cascade has no ports. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_exact_passive _ _ _

/-- Rectifier mode with a stable current loop: the nonlinear plant is locally exponentially
stable at the operating point (`i_d* = I_d0` held constant). -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (p : CascadeParams)
    (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0) (hR : 0 < p.pi.R + p.pi.Kp)
    (hKi : 0 < p.pi.Ki) (hI : 0 < p.Idc0) :
    connection% (p ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow.mpr (p.locallyExponentiallyStable hL hC hV hR hKi hI)

/-- Inverter mode (`I_dc0 < 0`): the nonlinear plant is unstable for every current-loop tuning —
the inner loop does not move the DC-node pole. -/
@[powerlib_domain] theorem mem_den_unstable_of_inverter (p : CascadeParams) (hC : 0 < p.C)
    (hV : 0 < p.V0) (hKi : p.pi.Ki ≠ 0) (hI : p.Idc0 < 0) :
    connection% (p ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow.mpr (p.unstable_of_inverter hC hV hKi hI)

/-! ## Exactness within the physical range -/

/-- With no integral gain the integrator direction is killed by the Jacobian. -/
private theorem cascade_fderiv_ki_zero {p : CascadeParams} (hKi : p.pi.Ki = 0) (hV : 0 < p.V0) :
    fderiv ℝ (p.field p.Id0) p.eqState (EuclideanSpace.single 1 1) = 0 := by
  have hx : p.eqState ∈ CascadeParams.posV := by
    simpa [CascadeParams.posV, CascadeParams.eqState] using hV
  have hdiff : DifferentiableAt ℝ (p.field p.Id0) p.eqState :=
    ((p.field_contDiffOn _).contDiffAt (CascadeParams.isOpen_posV.mem_nhds hx)).differentiableAt
      one_ne_zero
  have hconst : ∀ t : ℝ, p.field p.Id0 (p.eqState + t • EuclideanSpace.single 1 1) =
      p.field p.Id0 p.eqState := by
    intro t
    ext i
    fin_cases i <;> simp [CascadeParams.field, CascadeParams.vconv, hKi]
  have h1 : HasDerivAt (fun t : ℝ => p.field p.Id0 (p.eqState + t • EuclideanSpace.single 1 1))
      (fderiv ℝ (p.field p.Id0) p.eqState (EuclideanSpace.single 1 1)) 0 := by
    have h := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single 1 1 : State 3)).const_add
        p.eqState) (by simp)
    rw [one_smul] at h
    exact h
  have h2 : HasDerivAt (fun t : ℝ => p.field p.Id0 (p.eqState + t • EuclideanSpace.single 1 1))
      0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/-- With `L, C, V0 > 0` the nonlinear cascade is locally exponentially stable at its operating
point exactly when the current loop is stable (`R + Kp > 0`, `Ki > 0`) and the converter
rectifies (`I_dc0 > 0`). -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (p : CascadeParams) (hL : 0 < p.pi.L)
    (hC : 0 < p.C) (hV : 0 < p.V0) :
    connection% (p ∈ family.den (.flow .locallyExponentiallyStable) ↔
      p ∈ {p : CascadeParams | (0 < p.pi.R + p.pi.Kp ∧ 0 < p.pi.Ki) ∧ 0 < p.Idc0}) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow, Set.mem_ofPred_eq]
  have hx : p.eqState ∈ CascadeParams.posV := by
    simpa [CascadeParams.posV, CascadeParams.eqState] using hV
  constructor
  · intro h
    by_cases hKi : p.pi.Ki = 0
    · exact absurd h (Dynamics.not_locallyExponentiallyStable_of_fderiv_apply_eq_zero_local
        CascadeParams.isOpen_posV hx (p.field_contDiffOn _)
        (by intro h0; simpa using congrArg (fun v : State 3 => v 1) h0)
        (cascade_fderiv_ki_zero hKi hV))
    · exact (p.isHurwitz_iff hL hC hV).mp
        (Dynamics.isHurwitz_of_locallyExponentiallyStable_local CascadeParams.isOpen_posV hx _
          (p.field_contDiffOn _) (p.jacobian_eq hKi hV.ne') h)
  · rintro ⟨⟨hR, hKi⟩, hI⟩
    exact p.locallyExponentiallyStable hL hC hV hR hKi hI

/-- A negative-inductance cascade: `L = −1`, `R = 0`, `Kp = Ki = −1`, `C = V_d0 = V0 = I_d0 = 1`
(`I_dc0 = 1`). -/
def negativeInductance : CascadeParams := ⟨⟨-1, 0, -1, -1⟩, 1, 1, 1, 1⟩

/-- The negative-inductance cascade is locally exponentially stable: its current loop
`L s² + (R + Kp) s + Ki = −(s² + s + 1)` and its DC node are stable. -/
@[powerlib_domain] theorem negativeInductance_mem_den_locallyExponentiallyStable :
    connection% (negativeInductance ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hKi : negativeInductance.pi.Ki ≠ 0 := by norm_num [negativeInductance]
  have hV : negativeInductance.V0 ≠ 0 := by norm_num [negativeInductance]
  refine mem_den_flow.mpr (locallyExponentiallyStable_of_isHurwitz_jacobian_local
    CascadeParams.isOpen_posV
    (by simp [CascadeParams.posV, CascadeParams.eqState, negativeInductance]) _
    (negativeInductance.field_contDiffOn _) (negativeInductance.field_eqState hKi)
    (negativeInductance.jacobian_eq hKi hV) ?_)
  rw [CascadeParams.isHurwitz_iff_pi, CurrentControl.PIParams.isHurwitz_iff_div]
  norm_num [negativeInductance, CascadeParams.Idc0]

/-- The local exponential translation of the nonlinear cascade is sound but not exact: the
negative-inductance cascade is locally exponentially stable without `L > 0`. -/
@[powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeInductance_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : CascadeParams.Stable negativeInductance := hmem .stable rfl
  have := hs.1
  norm_num [negativeInductance] at this

end powerlib.DCLink
