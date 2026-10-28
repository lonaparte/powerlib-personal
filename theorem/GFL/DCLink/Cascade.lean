import theorem.CurrentControl.PILoop
import theorem.Dynamics.Coordinates
import theorem.Dynamics.Locality
import theorem.GFL.DCLink.PowerBalance
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.Dynamics.Shift

/-! # Current loop feeding the DC link: the full `ΔV_dc/Δi_d*` transfer

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

Source: work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.1.1, §1.4, §1.5;
`theory/T-gfl-control.md` §1.4.1.

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

Family and connection conclusions.
* `linearizedFamily : Family CascadeParams Spectral.Requirement 3 1` reads the parameters as the
  port system of the small-signal plant `model` (input `Δi_d*`, output `ΔV_dc`;
  `Spectral.linearFamily`). Requirements: the PI loop's positive monic coefficients and a
  positive DC-node coefficient `I_dc0/(C V0)` (`stable`), or a negative one of them
  (`unstable`). `linearizedChain_le_semantics`, `linearizedExact`; `linearizedDen_eq`: its
  attractive denotation is the PI family's pulled back along `pi`, cut by `I_dc0/(C V0) > 0`;
  `linearized_mem_den_iff`: with `L, C, V0 > 0`, stable iff
  `R + Kp > 0 ∧ Ki > 0 ∧ I_dc0 > 0`. Scaffold of the connection with the PI family:
  `theorem/CascadeCurrentLoop.agda`.
* `family : Family CascadeParams Spectral.Requirement 3 0` reads the parameters as the
  nonlinear field with `i_d* = I_d0` translated so that `eqState` is the origin
  (`Spectral.localFamily`, `Flow.Property.holds_shift_iff`). Requirements: `stable` —
  `L, C, V0 > 0`, `R + Kp > 0`, `Ki > 0`, `I_dc0 > 0`; `unstable` — `C, V0 > 0`, `Ki ≠ 0`,
  `I_dc0 < 0`. `chain_le_semantics`, `exact_passive`; `mem_den_locallyExponentiallyStable`:
  rectifier mode with a stable current loop is locally exponentially stable;
  `mem_den_unstable_of_inverter`: in
  inverter mode (`I_dc0 < 0`) the plant is unstable, whatever the current-loop gains (the
  open-loop pole `−I_dc0/(C V0)` of §1.4 survives the inner loop).
  Within `L, C, V0 > 0` the local exponential translation is exact
  (`mem_den_locallyExponentiallyStable_iff`: locally exponentially stable iff `R + Kp > 0`,
  `Ki > 0`, `I_dc0 > 0`; converse linearization for fields that are `C¹` on `V_dc > 0`,
  `Dynamics.isHurwitz_of_locallyExponentiallyStable_local`; with `Ki = 0` the integrator direction
  is killed by the Jacobian). Outside that range it is not exact
  (`not_exact_locallyExponentiallyStable`: the negative-inductance cascade
  `negativeInductance` is locally exponentially stable), and neither are the local asymptotic and
  Lyapunov translations (`not_exact_locallyAsymptoticallyStable`, `not_exact_lyapunovStable`,
  through `Spectral.local_not_exact_of_not_exact_les`).
* Within `L, C, V0 > 0`, boundary by boundary (the Jacobian is block triangular: current loop,
  then DC node): `R + Kp = 0`, `Ki > 0` is a purely imaginary pair of the linear current loop, a
  centre with the conserved energy `CascadeParams.loopEnergy` (`loopEnergy_lie`:
  `d/dt (L e²/2 + Ki η²/2) = −(R + Kp) e²`); `I_dc0 = 0` is a zero eigenvalue of the DC node with
  a line of equilibria `(I_d0, ξ0, V)`; `Ki = 0` is a zero eigenvalue in the integrator direction
  (no equilibrium, or a line of them). On `I_dc0 = 0` the capacitor energy corrected by the
  current loop is conserved: `CascadeParams.storage` (`R + Kp ≠ 0`, `storage_lie`:
  `d/dt = −I_dc0 (V_dc − V0)`) and `CascadeParams.centerStorage` (`R + Kp = 0`,
  `centerStorage_lie`: `d/dt = −I_dc0 (V_dc − V0) + (Kp/L) loopEnergy`).
* `mem_den_locallyAsymptoticallyStable_iff`: locally asymptotically stable iff `R + Kp > 0`,
  `Ki > 0`, `I_dc0 > 0`, so `exact_locallyAsymptoticallyStable_physical`: the local asymptotic
  translation is exact within the physical range.
* The Lyapunov translation is not exact within the physical range
  (`not_exact_lyapunovStable_physical`): the idle cascade `idle` (`I_d0 = 0`, so `I_dc0 = 0`) is
  Lyapunov stable (`idle_mem_den_lyapunovStable`, energy `(storage − storage(x*))² + loopEnergy`)
  and not locally asymptotically stable (`idle_not_mem_den_locallyAsymptoticallyStable`).
* `mem_den_lyapunovStable_iff` (complete Lyapunov membership within `L, C, V0 > 0`): Lyapunov
  stable iff either `Ki > 0` and (`R + Kp > 0 ∧ I_dc0 ≥ 0`, or `R + Kp = 0 ∧ I_dc0 > 0` — the
  undamped current loop driving a rectifying DC node, proved with the practical Lyapunov function
  `(max (u² − λ loopEnergy) 0)² + loopEnergy`, `u = centerStorage − centerStorage(x*)` — or
  `R = Kp = 0 ∧ I_dc0 = 0`), or `Ki = 0 ∧ R I_d0 = 0 ∧ R + Kp > 0 ∧ I_dc0 ≥ 0`
  (`ξ − L e/(R + Kp)` conserved, `CascadeParams.driftStorage`). Unstable boundary members:
  `R + Kp = 0`, `I_dc0 = 0`, `R ≠ 0` (the undamped loop pumps the capacitor:
  `d/dt (Kp centerStorage) = (Kp²/L) loopEnergy` on the conserved level,
  `Dynamics.unstable_of_lie_nonpos_of_lie_pos_local`); `Ki = 0` with `R + Kp < 0` (Chetaev `e²`),
  `R + Kp = 0` (Chetaev `−e ξ`, the integrator drifts) or `I_dc0 < 0` (Jacobian eigenvalue); and
  `Ki = 0`, `R I_d0 ≠ 0` is not an equilibrium.
The degenerate-equilibrium tools for the locally `C¹` field are in
`theorem/Dynamics/Instability.lean` and `theorem/Dynamics/Lyapunov.lean`.
The Jacobian, the transfer function and its zeros are static evidence.
-/

noncomputable section
namespace powerlib.GFL.DCLink
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
    apply ContDiffOn.div _ (Dynamics.contDiff_coord 2).contDiffOn
    · intro x hx
      exact ne_of_gt hx
    · apply ContDiff.contDiffOn
      unfold vconv
      fun_prop

/-- The state matrix is the Jacobian of the nonlinear plant at `eqState` whenever the bridge
voltage there is `V_d0 − R I_d0` (always for `Ki ≠ 0`; for `Ki = 0` iff `R I_d0 = 0`). -/
private theorem jacobian_eq_of_vconv (hv0 : p.vconv p.Id0 p.eqState = p.Vd0 - p.pi.R * p.Id0)
    (hV : p.V0 ≠ 0) :
    fderiv ℝ (p.field p.Id0) p.eqState =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) p.stateMatrix := by
  set x := p.eqState with hxdef
  have hx2 : x 2 ≠ 0 := by simpa [hxdef, eqState] using hV
  have h0 := Dynamics.hasFDerivAt_coord (0 : Fin 3) x
  have h1 := Dynamics.hasFDerivAt_coord (1 : Fin 3) x
  have hvc : HasFDerivAt (p.vconv p.Id0) (p.pi.Kp • Dynamics.coord 0 - p.pi.Ki • Dynamics.coord 1)
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
  have hC := (((hvc.mul h0).mul (hasFDerivAt_inv_coord 2 hx2)).const_add p.isrc).mul_const p.C⁻¹
  refine Dynamics.fderiv_eq_toEuclideanCLM_of_components _
    ![p.pi.L⁻¹ • ((-p.pi.R) • Dynamics.coord 0 + p.pi.Kp • -Dynamics.coord 0 +
        p.pi.Ki • Dynamics.coord 1),
      -Dynamics.coord 0,
      p.C⁻¹ • ((p.vconv p.Id0 x * x 0) •
          (ContinuousLinearMap.toSpanSingleton ℝ (-(x 2 ^ 2)⁻¹)).comp (Dynamics.coord 2) +
        (x 2)⁻¹ • (p.vconv p.Id0 x • Dynamics.coord 0 +
          x 0 • (p.pi.Kp • Dynamics.coord 0 - p.pi.Ki • Dynamics.coord 1)))] ?_ ?_
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
    have hv : p.vconv p.Id0 x = p.Vd0 - p.pi.R * p.Id0 := hv0
    fin_cases i
    · simp [stateMatrix, Fin.sum_univ_three]
      ring
    · simp [stateMatrix, Fin.sum_univ_three]
    · simp only [Fin.reduceFinMk, Matrix.cons_val, _root_.smul_apply, _root_.add_apply,
        _root_.sub_apply, hv]
      simp [stateMatrix, Fin.sum_univ_three, hxdef, eqState, Idc0]
      field_simp
      ring

/-- The state matrix is the Jacobian of the nonlinear plant at the operating point. -/
@[powerlib_foundation] theorem jacobian_eq (hKi : p.pi.Ki ≠ 0) (hV : p.V0 ≠ 0) :
    fderiv ℝ (p.field p.Id0) p.eqState =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) p.stateMatrix :=
  p.jacobian_eq_of_vconv (p.vconv_eqState hKi) hV

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
      (Linear.characteristicMatrix p.pi.model.A s).det *
        (s + ((p.Idc0 / (p.C * p.V0) : ℝ) : ℂ)) := by
  simp only [CurrentControl.PIParams.model, LTI.det_characteristicMatrix_of]
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
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local isOpen_posV
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
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local isOpen_posV
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
        (((p.pi.L : ℂ) * s ^ 2 + (p.pi.R + p.pi.Kp) * s + p.pi.Ki) *
          (p.C * p.V0 * s + p.Idc0)) := by
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
@[tmio TM]
@[powerlib_domain] theorem linearizedChain_le_semantics :
    connection% (∀ P, linearizedFamily.chain P ≤ linearizedFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics
    (fun p h => (CascadeParams.isHurwitz_iff_linStable p).mpr h)
    (fun p h => p.exists_root_of_linUnstable h)

/-- The attractive sentences and sampled contraction of the linearized cascade are carved out
exactly. -/
@[tmio TM]
@[powerlib_domain] theorem linearizedExact {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (linearizedFamily.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun p => (CascadeParams.isHurwitz_iff_linStable p).symm) hP

/-- The DC node does not change the current loop's stability but adds its own pole: the
attractive denotation of the linearized cascade is the PI family's pulled back along `pi`, cut
by a positive DC-node coefficient `I_dc0/(C V0)`. -/
@[tmio TM]
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
@[tmio TM]
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
  Spectral.mem_den_flow_iff_shift (f := fun p : CascadeParams => p.field p.Id0)
    (pt := CascadeParams.eqState) (Spectral.localFamily_isAutonomous _ _ _)

/-- Every translation of the nonlinear cascade family is sound. -/
@[tmio TM]
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
@[tmio TM]
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_exact_passive _ _ _

/-- Rectifier mode with a stable current loop: the nonlinear plant is locally exponentially
stable at the operating point (`i_d* = I_d0` held constant). -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (p : CascadeParams)
    (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0) (hR : 0 < p.pi.R + p.pi.Kp)
    (hKi : 0 < p.pi.Ki) (hI : 0 < p.Idc0) :
    connection% (p ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow.mpr (p.locallyExponentiallyStable hL hC hV hR hKi hI)

/-- Inverter mode (`I_dc0 < 0`): the nonlinear plant is unstable for every current-loop tuning —
the inner loop does not move the DC-node pole. -/
@[tmio TM]
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
@[tmio TM]
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (p : CascadeParams)
    (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0) :
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
@[tmio TM]
@[powerlib_domain] theorem negativeInductance_mem_den_locallyExponentiallyStable :
    connection% (negativeInductance ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hKi : negativeInductance.pi.Ki ≠ 0 := by norm_num [negativeInductance]
  have hV : negativeInductance.V0 ≠ 0 := by norm_num [negativeInductance]
  refine mem_den_flow.mpr (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local
    CascadeParams.isOpen_posV
    (by simp [CascadeParams.posV, CascadeParams.eqState, negativeInductance]) _
    (negativeInductance.field_contDiffOn _) (negativeInductance.field_eqState hKi)
    (negativeInductance.jacobian_eq hKi hV) ?_)
  rw [CascadeParams.isHurwitz_iff_pi, CurrentControl.PIParams.isHurwitz_iff_div]
  norm_num [negativeInductance, CascadeParams.Idc0]

/-- The local exponential translation of the nonlinear cascade is sound but not exact: the
negative-inductance cascade is locally exponentially stable without `L > 0`. -/
@[tmio TM]
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

/-! ## The local asymptotic and Lyapunov sentences -/

private theorem cascade_les_of {p : CascadeParams} (h : CascadeParams.Stable p) :
    LocallyExponentiallyStable (CascadeParams.shiftedField p) 0 := by
  obtain ⟨hL, hC, hV, hR, hKi, hI⟩ := h
  exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
    (p.locallyExponentiallyStable hL hC hV hR hKi hI)

/-- The local asymptotic translation of the nonlinear cascade is not exact (the
negative-inductance cascade). -/
@[tmio TM]
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun _ hm => cascade_les_of hm) h (Or.inr rfl)

/-- The Lyapunov translation of the nonlinear cascade is not exact (the negative-inductance
cascade). -/
@[tmio TM]
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun _ hm => cascade_les_of hm) h (Or.inl rfl)

/-! ## The boundaries `R + Kp = 0`, `I_dc0 = 0`, `Ki = 0`

The Jacobian is block triangular (current loop, then DC node), so the boundaries of the Hurwitz
region are: `R + Kp = 0`, `Ki > 0` (purely imaginary pair `±i √(Ki/L)` of the current loop, which
is linear: a centre with the conserved energy `CascadeParams.loopEnergy`); `I_dc0 = 0` (zero
eigenvalue of the DC node: with `Ki ≠ 0` every `(I_d0, ξ0, V)` is an equilibrium); `Ki = 0` (zero
eigenvalue in the integrator direction: either no equilibrium or a line of equilibria). On
`I_dc0 = 0` the capacitor energy corrected by the current loop (`CascadeParams.storage`,
`CascadeParams.centerStorage`) is conserved. -/

namespace CascadeParams

variable (p : CascadeParams)

/-- The current-loop energy `L e²/2 + Ki η²/2`, `e = i_d − I_d0`, `η = ξ − ξ0`. -/
def loopEnergy (x : State 3) : ℝ :=
  p.pi.L / 2 * (x 0 - p.Id0) ^ 2 + p.pi.Ki / 2 * (x 1 - p.pi.R * p.Id0 / p.pi.Ki) ^ 2

@[powerlib_foundation] theorem hasFDerivAt_loopEnergy (x : State 3) :
    HasFDerivAt p.loopEnergy
      ((p.pi.L * (x 0 - p.Id0)) • Dynamics.coord 0 +
        (p.pi.Ki * (x 1 - p.pi.R * p.Id0 / p.pi.Ki)) • Dynamics.coord 1) x := by
  have h0 := (Dynamics.hasFDerivAt_coord 0 x).sub_const p.Id0
  have h1 := (Dynamics.hasFDerivAt_coord 1 x).sub_const (p.pi.R * p.Id0 / p.pi.Ki)
  have h := ((h0.pow 2).const_mul (p.pi.L / 2)).add ((h1.pow 2).const_mul (p.pi.Ki / 2))
  convert h using 1
  · funext y; simp [loopEnergy]
  · ext v
    simp
    ring

/-- The current-loop energy decays at the rate `(R + Kp) e²`. -/
@[powerlib_foundation] theorem loopEnergy_lie (hL : p.pi.L ≠ 0) (hKi : p.pi.Ki ≠ 0)
    (x : State 3) :
    fderiv ℝ p.loopEnergy x (p.field p.Id0 x) = -(p.pi.R + p.pi.Kp) * (x 0 - p.Id0) ^ 2 := by
  rw [(p.hasFDerivAt_loopEnergy x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul, field,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

@[powerlib_foundation] theorem loopEnergy_nonneg (hL : 0 < p.pi.L) (hKi : 0 < p.pi.Ki)
    (x : State 3) : 0 ≤ p.loopEnergy x := by
  unfold loopEnergy
  positivity

private theorem eqState_mem (hV : 0 < p.V0) : p.eqState ∈ posV := by
  simpa [posV, eqState] using hV

/-- A Hurwitz-violating current loop (`Ki ≠ 0`) makes the cascade unstable. -/
private theorem unstable_of_pi_unstable (hV : 0 < p.V0) (hKi : p.pi.Ki ≠ 0)
    (h : p.pi.Unstable) : _root_.Unstable (p.field p.Id0) p.eqState := by
  obtain ⟨s, hs, hre⟩ := p.pi.exists_root_of_unstable h
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root ((p.characteristic_root_iff s).mpr
    (Or.inl hs))
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local isOpen_posV (p.eqState_mem hV) _
    (p.field_contDiffOn _) (p.field_eqState hKi) (p.jacobian_eq hKi hV.ne') ⟨s, v, hv, heig, hre⟩

/-- With no integral gain the field does not depend on `ξ`. -/
private theorem field_ki_zero_shift (hKi : p.pi.Ki = 0) (x : State 3) (t : ℝ) :
    p.field p.Id0 (x + t • EuclideanSpace.single 1 1) = p.field p.Id0 x := by
  ext i
  fin_cases i <;> simp [field, vconv, hKi]

/-- With no integral gain the cascade is not locally asymptotically stable. -/
private theorem not_las_ki_zero (hV : 0 < p.V0) (hKi : p.pi.Ki = 0) :
    ¬ LocalAsymptoticStable (p.field p.Id0) p.eqState := by
  intro h
  by_cases h0 : p.field p.Id0 p.eqState = 0
  · refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
      ⟨p.eqState + (ε / 2) • EuclideanSpace.single 1 1, ?_, ?_, ?_⟩) h
    · intro h'
      have := congrArg (fun y : State 3 => y 1) h'
      simp at this
      linarith
    · rw [add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · rw [p.field_ki_zero_shift hKi]
      exact h0
  · exact h0 (Dynamics.isEquilibrium_of_lyapunovStable_local isOpen_posV (p.eqState_mem hV)
      (p.field_contDiffOn _) h.1)

/-- With `I_dc0 = 0` every DC voltage is an equilibrium voltage. -/
private theorem field_idc_zero (hKi : p.pi.Ki ≠ 0) (hV : p.V0 ≠ 0) (hI : p.Idc0 = 0) (t : ℝ) :
    p.field p.Id0 (p.eqState + t • EuclideanSpace.single 2 1) = 0 := by
  have hP : (p.Vd0 - p.pi.R * p.Id0) * p.Id0 = 0 := by
    have : p.Idc0 * p.V0 = (p.Vd0 - p.pi.R * p.Id0) * p.Id0 := by
      simp only [Idc0]; field_simp
    rw [← this, hI, zero_mul]
  have heq := p.field_eqState hKi
  ext i
  fin_cases i
  · have h := congrArg (fun y : State 3 => y 0) heq
    simpa [field] using h
  · have h := congrArg (fun y : State 3 => y 1) heq
    simpa [field] using h
  · simp only [field, PiLp.toLp_apply, PiLp.zero_apply]
    simp [vconv, eqState, isrc, hI]
    field_simp
    rcases mul_eq_zero.mp hP with h | h <;> simp [h]

/-- With `I_dc0 = 0` the cascade is not locally asymptotically stable (a line of equilibria). -/
private theorem not_las_idc_zero (hKi : p.pi.Ki ≠ 0) (hV : p.V0 ≠ 0) (hI : p.Idc0 = 0) :
    ¬ LocalAsymptoticStable (p.field p.Id0) p.eqState :=
  Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
    ⟨p.eqState + (ε / 2) • EuclideanSpace.single 2 1, fun h' => by
      have := congrArg (fun y : State 3 => y 2) h'
      simp at this
      linarith, by
      rw [add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith, p.field_idc_zero hKi hV hI _⟩)

/-- On `R + Kp = 0` (undamped current loop) the cascade is not locally asymptotically stable:
the current-loop energy is conserved. -/
private theorem not_las_center (hL : 0 < p.pi.L) (hV : 0 < p.V0) (hKi : 0 < p.pi.Ki)
    (hR : p.pi.R + p.pi.Kp = 0) : ¬ LocalAsymptoticStable (p.field p.Id0) p.eqState := by
  refine Dynamics.not_localAsymptoticStable_of_lie_nonpos_local (V := fun x => -p.loopEnergy x)
    (ρ := 1) isOpen_posV (p.eqState_mem hV) (p.field_contDiffOn _)
    (fun x => (p.hasFDerivAt_loopEnergy x).differentiableAt.neg) one_pos
    (fun x _ _ => ?_) (fun ε hε => ⟨p.eqState + WithLp.toLp 2 ![ε / 2, 0, 0], ?_, ?_⟩)
  · rw [fderiv_fun_neg, _root_.neg_apply, p.loopEnergy_lie hL.ne' hKi.ne', hR]
    simp
  · rw [add_sub_cancel_left]
    refine (Dynamics.norm_le_abs_add_abs_three _).trans_lt ?_
    norm_num
    rw [abs_of_pos (half_pos hε)]
    linarith
  · have h0 : p.loopEnergy p.eqState = 0 := by simp [loopEnergy, eqState]
    simp only [h0, neg_zero, neg_lt_zero]
    simp [loopEnergy, eqState]
    positivity

/-- The capacitor energy corrected by the current loop, `C V²/2 − φ₁ − φ₂` with
`φ₁ = −L I_d0 e + (2 R I_d0 − V_d0) η`, `φ₂ = (−Kp L e² + Ki R η²)/(2 (R + Kp))`: for `R + Kp ≠ 0`
its derivative along the cascade is `−I_dc0 (V_dc − V0)`. -/
def storage (x : State 3) : ℝ :=
  p.C / 2 * x 2 ^ 2 - (-(p.pi.L * p.Id0) * (x 0 - p.Id0) +
      (2 * p.pi.R * p.Id0 - p.Vd0) * (x 1 - p.pi.R * p.Id0 / p.pi.Ki)) -
    1 / (2 * (p.pi.R + p.pi.Kp)) * (-(p.pi.Kp * p.pi.L) * (x 0 - p.Id0) ^ 2 +
      p.pi.Ki * p.pi.R * (x 1 - p.pi.R * p.Id0 / p.pi.Ki) ^ 2)

@[powerlib_foundation] theorem contDiff_storage : ContDiff ℝ 1 p.storage := by
  unfold storage; fun_prop

@[powerlib_foundation] theorem storage_lie (hL : p.pi.L ≠ 0) (hKi : p.pi.Ki ≠ 0)
    (hR : p.pi.R + p.pi.Kp ≠ 0) (hC : p.C ≠ 0) (hV : p.V0 ≠ 0) {x : State 3} (hx : x 2 ≠ 0) :
    fderiv ℝ p.storage x (p.field p.Id0 x) = -(p.Idc0 * (x 2 - p.V0)) := by
  have h0 := (Dynamics.hasFDerivAt_coord 0 x).sub_const p.Id0
  have h1 := (Dynamics.hasFDerivAt_coord 1 x).sub_const (p.pi.R * p.Id0 / p.pi.Ki)
  have h2 := Dynamics.hasFDerivAt_coord 2 x
  have h := (((h2.pow 2).const_mul (p.C / 2)).sub ((h0.const_mul (-(p.pi.L * p.Id0))).add
    (h1.const_mul (2 * p.pi.R * p.Id0 - p.Vd0)))).sub ((((h0.pow 2).const_mul
    (-(p.pi.Kp * p.pi.L))).add ((h1.pow 2).const_mul (p.pi.Ki * p.pi.R))).const_mul
    (1 / (2 * (p.pi.R + p.pi.Kp))))
  rw [show fderiv ℝ p.storage x = _ from h.fderiv]
  simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, Dynamics.coord_apply,
    smul_eq_mul, nsmul_eq_mul, field, vconv, isrc, Idc0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Nat.cast_ofNat, Nat.add_one_sub_one,
    pow_one]
  field_simp
  ring

/-- On `R + Kp = 0` the capacitor energy corrected by the undamped current loop,
`C V²/2 − φ₁ − Ki η²/2 + Kp e η/2`: its derivative along the cascade is
`−I_dc0 (V_dc − V0) + (Kp/L) (L e²/2 + Ki η²/2)`. -/
def centerStorage (x : State 3) : ℝ :=
  p.C / 2 * x 2 ^ 2 - (-(p.pi.L * p.Id0) * (x 0 - p.Id0) +
      (2 * p.pi.R * p.Id0 - p.Vd0) * (x 1 - p.pi.R * p.Id0 / p.pi.Ki)) -
    p.pi.Ki / 2 * (x 1 - p.pi.R * p.Id0 / p.pi.Ki) ^ 2 +
    p.pi.Kp / 2 * ((x 0 - p.Id0) * (x 1 - p.pi.R * p.Id0 / p.pi.Ki))

@[powerlib_foundation] theorem contDiff_centerStorage : ContDiff ℝ 1 p.centerStorage := by
  unfold centerStorage; fun_prop

@[powerlib_foundation] theorem centerStorage_lie (hL : p.pi.L ≠ 0) (hKi : p.pi.Ki ≠ 0)
    (hR : p.pi.R + p.pi.Kp = 0) (hC : p.C ≠ 0) (hV : p.V0 ≠ 0) {x : State 3} (hx : x 2 ≠ 0) :
    fderiv ℝ p.centerStorage x (p.field p.Id0 x) =
      -(p.Idc0 * (x 2 - p.V0)) + p.pi.Kp / p.pi.L * p.loopEnergy x := by
  have hKp : p.pi.Kp = -p.pi.R := by linarith
  have h0 := (Dynamics.hasFDerivAt_coord 0 x).sub_const p.Id0
  have h1 := (Dynamics.hasFDerivAt_coord 1 x).sub_const (p.pi.R * p.Id0 / p.pi.Ki)
  have h2 := Dynamics.hasFDerivAt_coord 2 x
  have h := ((((h2.pow 2).const_mul (p.C / 2)).sub ((h0.const_mul (-(p.pi.L * p.Id0))).add
    (h1.const_mul (2 * p.pi.R * p.Id0 - p.Vd0)))).sub ((h1.pow 2).const_mul (p.pi.Ki / 2))).add
    ((h0.mul h1).const_mul (p.pi.Kp / 2))
  rw [show fderiv ℝ p.centerStorage x = _ from h.fderiv]
  simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, Dynamics.coord_apply,
    smul_eq_mul, nsmul_eq_mul, field, vconv, isrc, Idc0, loopEnergy, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one]
  rw [hKp]
  field_simp
  ring

/-- An energy `(S − S(x*))² + L e²/2 + Ki η²/2`, with `S` reducing to `C V²/2` up to a constant on
`e = η = 0`, is positive away from the operating point on `V_dc > 0`. -/
private theorem sq_add_loopEnergy_pos (hL : 0 < p.pi.L) (hKi : 0 < p.pi.Ki) (hC : 0 < p.C)
    (hV : 0 < p.V0) {S : State 3 → ℝ}
    (hS : ∀ x : State 3, x 0 = p.Id0 → x 1 = p.pi.R * p.Id0 / p.pi.Ki →
      S x - S p.eqState = p.C / 2 * (x 2 ^ 2 - p.V0 ^ 2))
    {x : State 3} (hx : 0 < x 2) (hne : x ≠ p.eqState) :
    0 < (S x - S p.eqState) ^ 2 + p.loopEnergy x := by
  by_cases h : x 0 = p.Id0 ∧ x 1 = p.pi.R * p.Id0 / p.pi.Ki
  · have h2 : x 2 ≠ p.V0 := by
      intro h2
      apply hne
      ext i
      fin_cases i
      · simpa [eqState] using h.1
      · simpa [eqState] using h.2
      · simpa [eqState] using h2
    have hsq : x 2 ^ 2 - p.V0 ^ 2 ≠ 0 := by
      intro h0
      have : (x 2 - p.V0) * (x 2 + p.V0) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h3 | h3
      · exact h2 (by linarith)
      · linarith
    have hne' : S x - S p.eqState ≠ 0 := by
      rw [hS x h.1 h.2]
      exact mul_ne_zero (by positivity) hsq
    have := p.loopEnergy_nonneg hL hKi x
    positivity
  · have hpos : 0 < p.loopEnergy x := by
      rcases not_and_or.mp h with h0 | h1
      · have : 0 < (x 0 - p.Id0) ^ 2 := by
          have := sub_ne_zero.mpr h0
          positivity
        unfold loopEnergy
        have : 0 ≤ p.pi.Ki / 2 * (x 1 - p.pi.R * p.Id0 / p.pi.Ki) ^ 2 := by positivity
        nlinarith
      · have : 0 < (x 1 - p.pi.R * p.Id0 / p.pi.Ki) ^ 2 := by
          have := sub_ne_zero.mpr h1
          positivity
        unfold loopEnergy
        have : 0 ≤ p.pi.L / 2 * (x 0 - p.Id0) ^ 2 := by positivity
        nlinarith
    have := sq_nonneg (S x - S p.eqState)
    linarith

/-- A Lyapunov function `(S − S(x*))² + L e²/2 + Ki η²/2` on `V_dc > 0`. -/
private theorem lyapunovStable_of_storage (hL : 0 < p.pi.L) (hKi : 0 < p.pi.Ki) (hC : 0 < p.C)
    (hV : 0 < p.V0) {S : State 3 → ℝ} (hSd : ContDiff ℝ 1 S)
    (hS : ∀ x : State 3, x 0 = p.Id0 → x 1 = p.pi.R * p.Id0 / p.pi.Ki →
      S x - S p.eqState = p.C / 2 * (x 2 ^ 2 - p.V0 ^ 2))
    (hLie : ∀ x : State 3, 0 < x 2 →
      2 * (S x - S p.eqState) * fderiv ℝ S x (p.field p.Id0 x) +
        fderiv ℝ p.loopEnergy x (p.field p.Id0 x) ≤ 0) :
    LyapunovStable (p.field p.Id0) p.eqState := by
  have hSdiff : Differentiable ℝ S := hSd.differentiable one_ne_zero
  have hEdiff : Differentiable ℝ p.loopEnergy := fun x =>
    (p.hasFDerivAt_loopEnergy x).differentiableAt
  refine lyapunov_stable (V := fun x => (S x - S p.eqState) ^ 2 + p.loopEnergy x) (D := posV)
    three_pos ⟨isOpen_posV, p.eqState_mem hV, (hSdiff.continuous.sub continuous_const).pow 2 |>.add
      hEdiff.continuous, fun x => ((hSdiff x).sub_const _).pow 2 |>.add (hEdiff x), ?_,
      fun x hx hne => p.sq_add_loopEnergy_pos hL hKi hC hV hS hx hne, fun x hx => ?_⟩
  · simp [loopEnergy, eqState]
  · rw [Dynamics.fderiv_sq_sub_add_apply (hSdiff x) (hEdiff x)]
    exact hLie x hx

/-- `R + Kp > 0`, `Ki > 0`, `I_dc0 = 0`: Lyapunov stable (the corrected storage `storage` is
conserved and the current-loop energy does not increase). -/
private theorem lyapunovStable_idc_zero (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0)
    (hKi : 0 < p.pi.Ki) (hR : 0 < p.pi.R + p.pi.Kp) (hI : p.Idc0 = 0) :
    LyapunovStable (p.field p.Id0) p.eqState := by
  refine p.lyapunovStable_of_storage hL hKi hC hV p.contDiff_storage (fun x h0 h1 => ?_)
    (fun x hx => ?_)
  · simp [storage, eqState, h0, h1]
    ring
  · rw [p.storage_lie hL.ne' hKi.ne' hR.ne' hC.ne' hV.ne' (ne_of_gt hx),
      p.loopEnergy_lie hL.ne' hKi.ne', hI]
    nlinarith [sq_nonneg (x 0 - p.Id0)]

/-- `R = Kp = 0`, `Ki > 0`, `I_dc0 = 0`: Lyapunov stable (`centerStorage` and the current-loop
energy are both conserved). -/
private theorem lyapunovStable_center_idc_zero (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0)
    (hKi : 0 < p.pi.Ki) (hR0 : p.pi.R = 0) (hKp : p.pi.Kp = 0) (hI : p.Idc0 = 0) :
    LyapunovStable (p.field p.Id0) p.eqState := by
  have hR : p.pi.R + p.pi.Kp = 0 := by rw [hR0, hKp]; ring
  refine p.lyapunovStable_of_storage hL hKi hC hV p.contDiff_centerStorage (fun x h0 h1 => ?_)
    (fun x hx => ?_)
  · simp [centerStorage, eqState, h0, h1]
    ring
  · rw [p.centerStorage_lie hL.ne' hKi.ne' hR hC.ne' hV.ne' (ne_of_gt hx),
      p.loopEnergy_lie hL.ne' hKi.ne', hI, hR, hKp]
    simp

end CascadeParams

private theorem las_iff (p : CascadeParams) (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0) :
    LocalAsymptoticStable (p.field p.Id0) p.eqState ↔
      (0 < p.pi.R + p.pi.Kp ∧ 0 < p.pi.Ki) ∧ 0 < p.Idc0 := by
  constructor
  · intro h
    rcases lt_trichotomy p.pi.Ki 0 with hki | hki | hki
    · exact absurd h.1 (p.unstable_of_pi_unstable hV hki.ne (Or.inr (div_neg_of_neg_of_pos hki hL)))
    · exact absurd h (p.not_las_ki_zero hV hki)
    · rcases lt_trichotomy (p.pi.R + p.pi.Kp) 0 with hR | hR | hR
      · exact absurd h.1
          (p.unstable_of_pi_unstable hV hki.ne' (Or.inl (div_neg_of_neg_of_pos hR hL)))
      · exact absurd h (p.not_las_center hL hV hki hR)
      · rcases lt_trichotomy p.Idc0 0 with hI | hI | hI
        · exact absurd h.1 (p.unstable_of_inverter hC hV hki.ne' hI)
        · exact absurd h (p.not_las_idc_zero hki.ne' hV.ne' hI)
        · exact ⟨⟨hR, hki⟩, hI⟩
  · rintro ⟨⟨hR, hKi⟩, hI⟩
    exact Flow.locallyExponentiallyStable_localAsymptoticStable
      (p.locallyExponentiallyStable hL hC hV hR hKi hI)

/-- With `L, C, V0 > 0` the nonlinear cascade is locally asymptotically stable at its operating
point exactly when it is locally exponentially stable: `R + Kp > 0`, `Ki > 0`, `I_dc0 > 0`. On
`R + Kp = 0` the conserved current-loop energy keeps nearby solutions away, on `I_dc0 = 0` and on
`Ki = 0` (at an equilibrium) equilibria accumulate, and the remaining violations are unstable. -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (p : CascadeParams)
    (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0) :
    connection% (p ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      p ∈ {p : CascadeParams | (0 < p.pi.R + p.pi.Kp ∧ 0 < p.pi.Ki) ∧ 0 < p.Idc0}) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow, Set.mem_ofPred_eq]
  exact las_iff p hL hC hV

private theorem realize_stable (P : Flow.Property)
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable) :
    TMIO.realize family.meets (family.translate (.flow P)) =
      {p : CascadeParams | CascadeParams.Stable p} := by
  ext p
  rw [TMIO.mem_realize]
  rcases hP with rfl | rfl <;>
  · change (∀ q ∈ ({.stable} : Set Spectral.Requirement), Spectral.Meets _ _ p q) ↔ _
    simp

/-- Within `L, C, V0 > 0` the local asymptotic translation is exact: the generated space of its
translation (`stable`) is the local asymptotic denotation cut by the physical range. -/
@[tmio TM]
@[powerlib_domain] theorem exact_locallyAsymptoticallyStable_physical :
    connection% (TMIO.realize family.meets (family.translate (.flow .locallyAsymptoticallyStable)) =
      family.den (.flow .locallyAsymptoticallyStable) ∩
        {p : CascadeParams | 0 < p.pi.L ∧ 0 < p.C ∧ 0 < p.V0}) := by
  unfold powerlib.TMIO.Statement
  rw [realize_stable _ (Or.inr rfl)]
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [mem_den_flow]
  constructor
  · rintro ⟨hL, hC, hV, hR, hKi, hI⟩
    exact ⟨(las_iff p hL hC hV).mpr ⟨⟨hR, hKi⟩, hI⟩, hL, hC, hV⟩
  · rintro ⟨h, hL, hC, hV⟩
    obtain ⟨⟨hR, hKi⟩, hI⟩ := (las_iff p hL hC hV).mp h
    exact ⟨hL, hC, hV, hR, hKi, hI⟩

/-- An idle cascade: `L = Kp = Ki = C = V_d0 = V0 = 1`, `R = 0`, `I_d0 = 0` (`I_dc0 = 0`). -/
def idle : CascadeParams := ⟨⟨1, 0, 1, 1⟩, 1, 1, 1, 0⟩

/-- The idle cascade is Lyapunov stable: its current loop is stable and the corrected capacitor
energy `V²/2 + i²/2 + ξ` is conserved (`CascadeParams.storage`). -/
@[tmio TM]
@[powerlib_domain] theorem idle_mem_den_lyapunovStable :
    connection% (idle ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow.mpr (idle.lyapunovStable_idc_zero (by norm_num [idle]) (by norm_num [idle])
    (by norm_num [idle]) (by norm_num [idle]) (by norm_num [idle])
    (by norm_num [idle, CascadeParams.Idc0]))

/-- The idle cascade is not locally asymptotically stable (every DC voltage is an equilibrium
voltage). -/
@[tmio TM]
@[powerlib_domain] theorem idle_not_mem_den_locallyAsymptoticallyStable :
    connection% (idle ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow]
  exact idle.not_las_idc_zero (by norm_num [idle]) (by norm_num [idle])
    (by norm_num [idle, CascadeParams.Idc0])

/-- Within `L, C, V0 > 0` the Lyapunov translation is not exact: the idle cascade is physical and
Lyapunov stable but does not meet `stable` (`I_dc0 = 0`). -/
@[tmio TM]
@[powerlib_domain] theorem not_exact_lyapunovStable_physical :
    connection% (¬ TMIO.realize family.meets (family.translate (.flow .lyapunovStable)) =
      family.den (.flow .lyapunovStable) ∩
        {p : CascadeParams | 0 < p.pi.L ∧ 0 < p.C ∧ 0 < p.V0}) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := idle_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  have hin : idle ∈ family.den (.flow .lyapunovStable) ∩
      {p : CascadeParams | 0 < p.pi.L ∧ 0 < p.C ∧ 0 < p.V0} := ⟨hmem, by norm_num [idle]⟩
  rw [← h, realize_stable _ (Or.inl rfl)] at hin
  have := hin.2.2.2.2.2
  norm_num [idle, CascadeParams.Idc0] at this

/-! ## The Lyapunov sentence within the physical range

Every boundary member is decided. Lyapunov stable: `I_dc0 = 0` with a stable current loop
(`storage` conserved) or with `R = Kp = 0` (`centerStorage` and `loopEnergy` conserved); the
undamped loop `R + Kp = 0` with `I_dc0 > 0` (a centre driving a contracting DC node: the practical
Lyapunov function `(max (u² − λ loopEnergy) 0)² + loopEnergy`,
`u = centerStorage − centerStorage(x*)`,
`Dynamics.hasDerivAt_sq_max_zero`); `Ki = 0` at an equilibrium (`R I_d0 = 0`) with `R + Kp > 0`
and `I_dc0 ≥ 0` (`ξ − L e/(R + Kp)` conserved, `driftStorage`). Unstable: `R + Kp = 0`,
`I_dc0 = 0`, `R ≠ 0` (`Kp · centerStorage` grows at the rate `(Kp²/L) loopEnergy` on the conserved
level); `Ki = 0` with `R + Kp ≤ 0` or `I_dc0 < 0`. -/

namespace CascadeParams

variable (p : CascadeParams)

/-! ### `R + Kp = 0`, `I_dc0 = 0`, `R ≠ 0`: the undamped loop pumps the capacitor -/

/-- With an undamped current loop (`R + Kp = 0`, `R ≠ 0`, `Ki > 0`) and `I_dc0 = 0` the cascade is
unstable: the current-loop energy is conserved and `Kp · centerStorage` grows at the rate
`(Kp²/L) loopEnergy` (Chetaev's theorem on the conserved level). -/
private theorem unstable_center_idc_zero (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0)
    (hKi : 0 < p.pi.Ki) (hR : p.pi.R + p.pi.Kp = 0) (hR0 : p.pi.R ≠ 0) (hI : p.Idc0 = 0) :
    _root_.Unstable (p.field p.Id0) p.eqState := by
  have hKp : p.pi.Kp ≠ 0 := by
    intro h
    apply hR0
    linarith
  refine Dynamics.unstable_of_lie_nonpos_of_lie_pos_local (E := fun x => -p.loopEnergy x)
    (W := fun x => p.pi.Kp * p.centerStorage x) (r := 1) isOpen_posV (p.eqState_mem hV)
    (p.field_contDiffOn _) ?_ (contDiff_const.mul p.contDiff_centerStorage) one_pos
    (fun x _ _ => ?_) (fun ε hε => ⟨p.eqState + WithLp.toLp 2 ![ε / 2, 0, 0], ?_, ?_⟩)
    (fun x hx _ hE => ?_)
  · have : ContDiff ℝ 1 p.loopEnergy := by unfold loopEnergy; fun_prop
    exact this.neg
  · rw [fderiv_fun_neg, _root_.neg_apply, p.loopEnergy_lie hL.ne' hKi.ne', hR]
    simp
  · rw [add_sub_cancel_left]
    refine (Dynamics.norm_le_abs_add_abs_three _).trans_lt ?_
    norm_num
    rw [abs_of_pos (half_pos hε)]
    linarith
  · have h0 : p.loopEnergy p.eqState = 0 := by simp [loopEnergy, eqState]
    simp only [h0, neg_zero, neg_lt_zero]
    simp [loopEnergy, eqState]
    positivity
  · have hx' : 0 < x 2 := hx
    have h0 : p.loopEnergy p.eqState = 0 := by simp [loopEnergy, eqState]
    have hEpos : 0 < p.loopEnergy x := by simpa [h0] using hE
    rw [fderiv_const_mul (p.contDiff_centerStorage.differentiable one_ne_zero x), _root_.smul_apply,
      smul_eq_mul, p.centerStorage_lie hL.ne' hKi.ne' hR hC.ne' hV.ne' (ne_of_gt hx'), hI]
    have : 0 < p.pi.Kp * p.pi.Kp := mul_self_pos.mpr hKp
    have : 0 < p.pi.Kp * p.pi.Kp / p.pi.L * p.loopEnergy x := by positivity
    have heq : p.pi.Kp * (-(0 * (x 2 - p.V0)) + p.pi.Kp / p.pi.L * p.loopEnergy x) =
        p.pi.Kp * p.pi.Kp / p.pi.L * p.loopEnergy x := by ring
    rw [heq]
    exact this

/-! ### No integral gain -/

/-- With no integral gain the operating point is an equilibrium iff `R I_d0 = 0`. -/
private theorem field_eqState_ki_zero (hKi : p.pi.Ki = 0) (hL : p.pi.L ≠ 0) (hV : p.V0 ≠ 0) :
    p.field p.Id0 p.eqState = 0 ↔ p.pi.R * p.Id0 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun y : State 3 => y 0) h
    simp [field, eqState, hKi] at h0
    rcases h0 with h0 | h0
    · rcases h0 with h0 | h0 <;> simp [h0]
    · exact absurd h0 hL
  · intro h
    ext i
    fin_cases i
    · simp [field, eqState, hKi]
      rcases mul_eq_zero.mp h with h' | h' <;> simp [h']
    · simp [field, eqState]
    · simp [field, eqState, vconv, isrc, Idc0, hKi]
      field_simp
      left
      linear_combination p.Id0 * h

private theorem vconv_eqState_ki_zero (hKi : p.pi.Ki = 0) (h : p.pi.R * p.Id0 = 0) :
    p.vconv p.Id0 p.eqState = p.Vd0 - p.pi.R * p.Id0 := by
  simp [vconv, eqState, hKi, h]

/-- With no integral gain and `R I_d0 = 0` the current error obeys `L e' = −(R + Kp) e`. -/
private theorem field_zero_ki (hKi : p.pi.Ki = 0) (h : p.pi.R * p.Id0 = 0) (hL : p.pi.L ≠ 0)
    (x : State 3) : p.field p.Id0 x 0 = -(p.pi.R + p.pi.Kp) * (x 0 - p.Id0) / p.pi.L := by
  simp only [field, PiLp.toLp_apply, Matrix.cons_val_zero, hKi, zero_mul, add_zero]
  field_simp
  linear_combination (-1 : ℝ) * h

private theorem field_one (x : State 3) : p.field p.Id0 x 1 = -(x 0 - p.Id0) := by
  simp [field]

/-- `Ki = 0`, `R I_d0 = 0`, `R + Kp < 0`: the current error grows (Chetaev's function `e²`). -/
private theorem unstable_ki_zero_lt (hL : 0 < p.pi.L) (hV : 0 < p.V0) (hKi : p.pi.Ki = 0)
    (h : p.pi.R * p.Id0 = 0) (hR : p.pi.R + p.pi.Kp < 0) :
    _root_.Unstable (p.field p.Id0) p.eqState := by
  refine Dynamics.unstable_of_chetaev_local (W := fun x : State 3 => (x 0 - p.Id0) ^ 2) (r := 1)
    isOpen_posV (p.eqState_mem hV) (p.field_contDiffOn _) (by fun_prop) one_pos
    (fun ε hε => ⟨p.eqState + WithLp.toLp 2 ![ε / 2, 0, 0], ?_, ?_⟩) (fun x _ _ hW => ?_)
  · rw [add_sub_cancel_left]
    refine (Dynamics.norm_le_abs_add_abs_three _).trans_lt ?_
    norm_num
    rw [abs_of_pos (half_pos hε)]
    linarith
  · simp [eqState]
    positivity
  · have hd : HasFDerivAt (fun x : State 3 => (x 0 - p.Id0) ^ 2)
        ((2 * (x 0 - p.Id0)) • Dynamics.coord 0) x := by
      have h' := ((Dynamics.hasFDerivAt_coord 0 x).sub_const p.Id0).pow 2
      convert h' using 1
      ext v; simp
    rw [hd.fderiv]
    simp only [_root_.smul_apply, Dynamics.coord_apply, smul_eq_mul]
    rw [p.field_zero_ki hKi h hL.ne']
    have hW' : 0 < (x 0 - p.Id0) ^ 2 := hW
    have : 0 < -(p.pi.R + p.pi.Kp) * (x 0 - p.Id0) ^ 2 / p.pi.L := by
      have : 0 < -(p.pi.R + p.pi.Kp) := by linarith
      positivity
    have heq : 2 * (x 0 - p.Id0) * (-(p.pi.R + p.pi.Kp) * (x 0 - p.Id0) / p.pi.L) =
        2 * (-(p.pi.R + p.pi.Kp) * (x 0 - p.Id0) ^ 2 / p.pi.L) := by ring
    rw [heq]
    linarith

/-- `Ki = 0`, `R I_d0 = 0`, `R + Kp = 0`: the current error is frozen and the integrator drifts
(Chetaev's function `−e ξ`). -/
private theorem unstable_ki_zero_eq (hL : 0 < p.pi.L) (hV : 0 < p.V0) (hKi : p.pi.Ki = 0)
    (h : p.pi.R * p.Id0 = 0) (hR : p.pi.R + p.pi.Kp = 0) :
    _root_.Unstable (p.field p.Id0) p.eqState := by
  refine Dynamics.unstable_of_chetaev_local (W := fun x : State 3 => -((x 0 - p.Id0) * x 1))
    (r := 1) isOpen_posV (p.eqState_mem hV) (p.field_contDiffOn _) (by fun_prop) one_pos
    (fun ε hε => ⟨p.eqState + WithLp.toLp 2 ![ε / 4, -(ε / 4), 0], ?_, ?_⟩)
    (fun x _ _ hW => ?_)
  · rw [add_sub_cancel_left]
    refine (Dynamics.norm_le_abs_add_abs_three _).trans_lt ?_
    norm_num
    rw [abs_of_pos (by positivity : 0 < ε / 4)]
    linarith
  · simp [eqState, hKi]
    positivity
  · have hd : HasFDerivAt (fun x : State 3 => -((x 0 - p.Id0) * x 1))
        (-(x 1 • Dynamics.coord 0 + (x 0 - p.Id0) • Dynamics.coord 1)) x := by
      have h' := (((Dynamics.hasFDerivAt_coord 0 x).sub_const p.Id0).mul
        (Dynamics.hasFDerivAt_coord 1 x)).neg
      convert h' using 1
      ext v; simp; ring
    rw [hd.fderiv]
    simp only [_root_.neg_apply, _root_.add_apply, _root_.smul_apply, Dynamics.coord_apply,
      smul_eq_mul]
    rw [p.field_zero_ki hKi h hL.ne', p.field_one, hR]
    have he : x 0 - p.Id0 ≠ 0 := by
      intro he
      have : -((x 0 - p.Id0) * x 1) = 0 := by rw [he]; ring
      linarith
    have : 0 < (x 0 - p.Id0) * (x 0 - p.Id0) := mul_self_pos.mpr he
    have heq : -(x 1 * (-0 * (x 0 - p.Id0) / p.pi.L) + (x 0 - p.Id0) * -(x 0 - p.Id0)) =
        (x 0 - p.Id0) * (x 0 - p.Id0) := by ring
    rw [heq]
    exact this

/-- `Ki = 0`, `R I_d0 = 0`, `R + Kp > 0`, `I_dc0 < 0`: the DC node is unstable (Jacobian
eigenvalue `−I_dc0/(C V0) > 0`). -/
private theorem unstable_ki_zero_inverter (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0)
    (hKi : p.pi.Ki = 0) (h : p.pi.R * p.Id0 = 0) (hI : p.Idc0 < 0) :
    _root_.Unstable (p.field p.Id0) p.eqState :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local isOpen_posV (p.eqState_mem hV) _
    (p.field_contDiffOn _) ((p.field_eqState_ki_zero hKi hL.ne' hV.ne').mpr h)
    (p.jacobian_eq_of_vconv (p.vconv_eqState_ki_zero hKi h) hV.ne')
    ⟨_, _, fun h => by simpa using congrFun h 2, p.stateMatrix_eigen, by
      rw [Complex.ofReal_re]
      exact neg_pos.mpr (div_neg_of_neg_of_pos hI (mul_pos hC hV))⟩

/-! ### The cascade without integral gain at an equilibrium -/

/-- With no integral gain (`Ki = 0`, `R I_d0 = 0`, `R + Kp ≠ 0`) the capacitor energy corrected by
the current error, `C V²/2 + (L α/(R + Kp)) e + (L Kp/(2 (R + Kp))) e²`, `α = V_d0 + Kp I_d0`: its
derivative along the cascade is `−I_dc0 (V_dc − V0)`. -/
def driftStorage (x : State 3) : ℝ :=
  p.C / 2 * x 2 ^ 2 + p.pi.L * (p.Vd0 + p.pi.Kp * p.Id0) / (p.pi.R + p.pi.Kp) * (x 0 - p.Id0) +
    p.pi.L * p.pi.Kp / (2 * (p.pi.R + p.pi.Kp)) * (x 0 - p.Id0) ^ 2

@[powerlib_foundation] theorem contDiff_driftStorage : ContDiff ℝ 1 p.driftStorage := by
  unfold driftStorage; fun_prop

@[powerlib_foundation] theorem driftStorage_lie (hKi : p.pi.Ki = 0) (h : p.pi.R * p.Id0 = 0)
    (hL : p.pi.L ≠ 0) (hR : p.pi.R + p.pi.Kp ≠ 0) (hC : p.C ≠ 0) (hV : p.V0 ≠ 0) {x : State 3}
    (hx : x 2 ≠ 0) :
    fderiv ℝ p.driftStorage x (p.field p.Id0 x) = -(p.Idc0 * (x 2 - p.V0)) := by
  have h0 := (Dynamics.hasFDerivAt_coord 0 x).sub_const p.Id0
  have h2 := Dynamics.hasFDerivAt_coord 2 x
  have hd := (((h2.pow 2).const_mul (p.C / 2)).add (h0.const_mul
    (p.pi.L * (p.Vd0 + p.pi.Kp * p.Id0) / (p.pi.R + p.pi.Kp)))).add ((h0.pow 2).const_mul
    (p.pi.L * p.pi.Kp / (2 * (p.pi.R + p.pi.Kp))))
  rw [show fderiv ℝ p.driftStorage x = _ from hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  rw [p.field_zero_ki hKi h hL]
  simp only [field, vconv, isrc, Idc0, hKi, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, zero_mul, add_zero]
  field_simp
  linear_combination (p.Id0 * p.V0) * h

/-- The scalar inequality behind the Lyapunov function of the cascade without integral gain. -/
private theorem drift_ineq {I C V0 x2 w e a1 a2 k L : ℝ} (hI : 0 ≤ I) (hC : 0 < C) (hV : 0 < V0)
    (hx2 : 0 < x2) (hk : 0 < k) (hL : 0 < L) (he : e ^ 2 ≤ 1) :
    2 * (C / 2 * (x2 + V0) * w + (a1 * e + a2 * e ^ 2)) * -(I * w) +
      -(2 * (2 * I * (a1 ^ 2 + a2 ^ 2) * L / (C * V0 * k) + 1) * k / L * e ^ 2) ≤ 0 := by
  set φ := a1 * e + a2 * e ^ 2 with hφ
  have hCV : 0 < C * V0 := mul_pos hC hV
  have h1 : φ ^ 2 ≤ 2 * (a1 ^ 2 + a2 ^ 2) * e ^ 2 := by
    have hsq : 2 * (a1 * e) ^ 2 + 2 * (a2 * e ^ 2) ^ 2 - φ ^ 2 = (a1 * e - a2 * e ^ 2) ^ 2 := by
      rw [hφ]; ring
    have h2 : (a2 * e ^ 2) ^ 2 ≤ a2 ^ 2 * e ^ 2 := by
      have : (a2 * e ^ 2) ^ 2 = a2 ^ 2 * e ^ 2 * e ^ 2 := by ring
      rw [this]
      exact mul_le_of_le_one_right (by positivity) he
    have h3 : (a1 * e) ^ 2 = a1 ^ 2 * e ^ 2 := by ring
    have := sq_nonneg (a1 * e - a2 * e ^ 2)
    nlinarith
  have hamgm : -(2 * w * φ) ≤ C * V0 / 2 * w ^ 2 + 2 / (C * V0) * φ ^ 2 := by
    have h0 : 0 ≤ (C * V0 * w + 2 * φ) ^ 2 / (2 * (C * V0)) := by positivity
    have heq : (C * V0 * w + 2 * φ) ^ 2 / (2 * (C * V0)) =
        C * V0 / 2 * w ^ 2 + 2 / (C * V0) * φ ^ 2 + 2 * w * φ := by
      field_simp
      ring
    linarith
  have hφb : 2 / (C * V0) * φ ^ 2 ≤ 4 * (a1 ^ 2 + a2 ^ 2) / (C * V0) * e ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / (C * V0) by positivity)
    have heq : 2 / (C * V0) * (2 * (a1 ^ 2 + a2 ^ 2) * e ^ 2) =
        4 * (a1 ^ 2 + a2 ^ 2) / (C * V0) * e ^ 2 := by ring
    linarith
  have hmix : I * -(2 * w * φ) ≤
      I * (C * V0 / 2 * w ^ 2) + I * (4 * (a1 ^ 2 + a2 ^ 2) / (C * V0) * e ^ 2) := by
    have := mul_le_mul_of_nonneg_left (hamgm.trans (add_le_add le_rfl hφb)) hI
    linarith [mul_add I (C * V0 / 2 * w ^ 2) (4 * (a1 ^ 2 + a2 ^ 2) / (C * V0) * e ^ 2)]
  have hfirst : I * (C * V0 * w ^ 2) ≤ I * (C * (x2 + V0) * w ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hI
    have : 0 ≤ C * x2 * w ^ 2 := by positivity
    nlinarith
  have hexp : 2 * (C / 2 * (x2 + V0) * w + φ) * -(I * w) =
      -(I * (C * (x2 + V0) * w ^ 2)) + I * -(2 * w * φ) := by ring
  have hM : 2 * (2 * I * (a1 ^ 2 + a2 ^ 2) * L / (C * V0 * k) + 1) * k / L * e ^ 2 =
      I * (4 * (a1 ^ 2 + a2 ^ 2) / (C * V0) * e ^ 2) + 2 * k / L * e ^ 2 := by
    field_simp
    ring
  have hhalf : I * (C * V0 / 2 * w ^ 2) = I * (C * V0 * w ^ 2) / 2 := by ring
  have hpos1 : 0 ≤ I * (C * V0 * w ^ 2) := by positivity
  have hpos2 : 0 ≤ 2 * k / L * e ^ 2 := by positivity
  rw [hexp, hM]
  linarith

/-- `Ki = 0`, `R I_d0 = 0`, `R + Kp > 0`, `I_dc0 ≥ 0`: Lyapunov stable. The current error decays,
`ξ − L e/(R + Kp)` is conserved, and `(driftStorage − driftStorage(x*))² + M e² +
(ξ − L e/(R + Kp))²` does not increase near the operating point for `M` large. -/
private theorem lyapunovStable_ki_zero (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0)
    (hKi : p.pi.Ki = 0) (h : p.pi.R * p.Id0 = 0) (hR : 0 < p.pi.R + p.pi.Kp)
    (hI : 0 ≤ p.Idc0) : LyapunovStable (p.field p.Id0) p.eqState := by
  set a1 := p.pi.L * (p.Vd0 + p.pi.Kp * p.Id0) / (p.pi.R + p.pi.Kp) with ha1
  set a2 := p.pi.L * p.pi.Kp / (2 * (p.pi.R + p.pi.Kp)) with ha2
  set M := 2 * p.Idc0 * (a1 ^ 2 + a2 ^ 2) * p.pi.L / (p.C * p.V0 * (p.pi.R + p.pi.Kp)) + 1
    with hM
  have hM0 : 1 ≤ M := by
    have : 0 ≤ 2 * p.Idc0 * (a1 ^ 2 + a2 ^ 2) * p.pi.L / (p.C * p.V0 * (p.pi.R + p.pi.Kp)) := by
      positivity
    linarith
  set c := p.pi.L / (p.pi.R + p.pi.Kp) with hc
  set E2 : State 3 → ℝ := fun x => M * (x 0 - p.Id0) ^ 2 + (x 1 - c * (x 0 - p.Id0)) ^ 2 with hE2
  have hE2d : ∀ x : State 3, HasFDerivAt E2 ((2 * M * (x 0 - p.Id0)) • Dynamics.coord 0 +
      (2 * (x 1 - c * (x 0 - p.Id0))) • (Dynamics.coord 1 - c • Dynamics.coord 0)) x := by
    intro x
    have h0 := (Dynamics.hasFDerivAt_coord 0 x).sub_const p.Id0
    have h1 := Dynamics.hasFDerivAt_coord 1 x
    have hd := ((h0.pow 2).const_mul M).add ((h1.sub (h0.const_mul c)).pow 2)
    convert hd using 1
    ext v
    simp
    ring
  have hSd : Differentiable ℝ p.driftStorage := p.contDiff_driftStorage.differentiable one_ne_zero
  have hEq1 : p.eqState 1 = 0 := by simp [eqState, hKi]
  set D : Set (State 3) := {x | 0 < x 2} ∩ {x | |x 0 - p.Id0| < 1} with hD
  have hDo : IsOpen D :=
    (isOpen_lt continuous_const (Dynamics.contDiff_coord (k := 0) 2).continuous).inter
    (isOpen_lt ((continuous_abs.comp ((Dynamics.contDiff_coord (k := 0) 0).continuous.sub
      continuous_const))) continuous_const)
  refine lyapunov_stable (V := fun x => (p.driftStorage x - p.driftStorage p.eqState) ^ 2 + E2 x)
    (D := D) three_pos ⟨hDo, ⟨by simpa [eqState] using hV, by simp [eqState]⟩,
      (hSd.continuous.sub continuous_const).pow 2 |>.add
        (continuous_iff_continuousAt.mpr fun x => (hE2d x).continuousAt),
      fun x => ((hSd x).sub_const _).pow 2 |>.add (hE2d x).differentiableAt,
      by simp [hE2, eqState, hKi], fun x hx hne => ?_, fun x hx => ?_⟩
  · -- positivity away from the operating point
    obtain ⟨hx2, -⟩ := hx
    have hx2' : 0 < x 2 := hx2
    by_cases he : x 0 = p.Id0
    · by_cases h1 : x 1 = 0
      · have h2 : x 2 ≠ p.V0 := by
          intro h2
          apply hne
          ext i
          fin_cases i
          · simpa [eqState] using he
          · simp [eqState, hKi, h1]
          · simpa [eqState] using h2
        have hS : p.driftStorage x - p.driftStorage p.eqState = p.C / 2 * (x 2 ^ 2 - p.V0 ^ 2) := by
          simp [driftStorage, eqState, he]
          ring
        have hsq : x 2 ^ 2 - p.V0 ^ 2 ≠ 0 := by
          intro h0
          have : (x 2 - p.V0) * (x 2 + p.V0) = 0 := by linear_combination h0
          rcases mul_eq_zero.mp this with h3 | h3
          · exact h2 (by linarith)
          · linarith
        have : p.driftStorage x - p.driftStorage p.eqState ≠ 0 := by
          rw [hS]; exact mul_ne_zero (by positivity) hsq
        have : 0 ≤ E2 x := by simp only [hE2]; positivity
        positivity
      · have : 0 < E2 x := by
          simp only [hE2, he, sub_self, mul_zero]
          have : x 1 ≠ 0 := h1
          positivity
        positivity
    · have : 0 < E2 x := by
        simp only [hE2]
        have : 0 < (x 0 - p.Id0) ^ 2 := by
          have := sub_ne_zero.mpr he
          positivity
        have : 0 ≤ (x 1 - c * (x 0 - p.Id0)) ^ 2 := sq_nonneg _
        nlinarith
      positivity
  · -- the derivative along the field
    obtain ⟨hx2, hx0⟩ := hx
    have hx2' : 0 < x 2 := hx2
    have hx0' : |x 0 - p.Id0| < 1 := hx0
    rw [Dynamics.fderiv_sq_sub_add_apply (hSd x) (hE2d x).differentiableAt,
      (hE2d x).fderiv, p.driftStorage_lie hKi h hL.ne' hR.ne' hC.ne' hV.ne' (ne_of_gt hx2')]
    simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, Dynamics.coord_apply,
      smul_eq_mul]
    rw [p.field_zero_ki hKi h hL.ne', p.field_one]
    set e := x 0 - p.Id0 with he
    set w := x 2 - p.V0 with hw
    have hS : p.driftStorage x - p.driftStorage p.eqState =
        p.C / 2 * (x 2 + p.V0) * w + (a1 * e + a2 * e ^ 2) := by
      simp only [driftStorage, eqState, he, hw, ha1, ha2]
      simp
      ring
    rw [hS]
    have hcf : -(p.pi.R + p.pi.Kp) * e / p.pi.L * c = -e := by
      rw [hc]; field_simp
    have hbr : 2 * M * e * (-(p.pi.R + p.pi.Kp) * e / p.pi.L) +
        2 * (x 1 - c * e) * (-e - c * (-(p.pi.R + p.pi.Kp) * e / p.pi.L)) =
        -(2 * M * (p.pi.R + p.pi.Kp) / p.pi.L * e ^ 2) := by
      have : c * (-(p.pi.R + p.pi.Kp) * e / p.pi.L) = -e := by rw [mul_comm]; exact hcf
      rw [this]
      field_simp
      ring
    rw [hbr]
    have he1 : e ^ 2 ≤ 1 := by
      have := abs_lt.mp hx0'
      nlinarith
    exact drift_ineq hI hC hV hx2' hR hL he1

/-! ### The undamped current loop on a rectifying DC node -/

/-- Four-term Cauchy–Schwarz. -/
private theorem sq_add4_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- The quadratic correction of the undamped cascade is bounded by the current-loop energy. -/
private theorem psi_bound {L Ki Id0 b Kp e η : ℝ} (hL : 0 < L) (hKi : 0 < Ki) (hη : η ^ 2 ≤ 1) :
    (L * Id0 * e - b * η - Ki / 2 * η ^ 2 + Kp / 2 * (e * η)) ^ 2 ≤
      8 * ((L * Id0) ^ 2 + b ^ 2 + Ki ^ 2 / 4 + Kp ^ 2 / 4) * (1 / L + 1 / Ki) *
        (L / 2 * e ^ 2 + Ki / 2 * η ^ 2) := by
  set B := (L * Id0) ^ 2 + b ^ 2 + Ki ^ 2 / 4 + Kp ^ 2 / 4 with hB
  have h4 := sq_add4_le (L * Id0 * e) (-(b * η)) (-(Ki / 2 * η ^ 2)) (Kp / 2 * (e * η))
  have hrw : L * Id0 * e + -(b * η) + -(Ki / 2 * η ^ 2) + Kp / 2 * (e * η) =
      L * Id0 * e - b * η - Ki / 2 * η ^ 2 + Kp / 2 * (e * η) := by ring
  rw [hrw] at h4
  have h3 : (-(Ki / 2 * η ^ 2)) ^ 2 ≤ Ki ^ 2 / 4 * η ^ 2 := by
    have : (-(Ki / 2 * η ^ 2)) ^ 2 = Ki ^ 2 / 4 * η ^ 2 * η ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hη
  have h5 : (Kp / 2 * (e * η)) ^ 2 ≤ Kp ^ 2 / 4 * e ^ 2 := by
    have : (Kp / 2 * (e * η)) ^ 2 = Kp ^ 2 / 4 * e ^ 2 * η ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hη
  have h1 : (L * Id0 * e) ^ 2 = (L * Id0) ^ 2 * e ^ 2 := by ring
  have h2 : (-(b * η)) ^ 2 = b ^ 2 * η ^ 2 := by ring
  have hsum : (L * Id0 * e) ^ 2 + (-(b * η)) ^ 2 + (-(Ki / 2 * η ^ 2)) ^ 2 + (Kp / 2 * (e * η)) ^ 2
      ≤ B * (e ^ 2 + η ^ 2) := by
    have he2 := sq_nonneg e
    have hη2 := sq_nonneg η
    have : B * (e ^ 2 + η ^ 2) = (L * Id0) ^ 2 * e ^ 2 + b ^ 2 * η ^ 2 + Ki ^ 2 / 4 * η ^ 2 +
        Kp ^ 2 / 4 * e ^ 2 + ((L * Id0) ^ 2 + Kp ^ 2 / 4) * η ^ 2 +
        (b ^ 2 + Ki ^ 2 / 4) * e ^ 2 := by rw [hB]; ring
    have : 0 ≤ ((L * Id0) ^ 2 + Kp ^ 2 / 4) * η ^ 2 := by positivity
    have : 0 ≤ (b ^ 2 + Ki ^ 2 / 4) * e ^ 2 := by positivity
    linarith
  have hEb : e ^ 2 + η ^ 2 ≤ 2 * (1 / L + 1 / Ki) * (L / 2 * e ^ 2 + Ki / 2 * η ^ 2) := by
    have heq : 2 * (1 / L + 1 / Ki) * (L / 2 * e ^ 2 + Ki / 2 * η ^ 2) =
        e ^ 2 + η ^ 2 + (Ki / L) * η ^ 2 + (L / Ki) * e ^ 2 := by
      field_simp
      ring
    have : 0 ≤ (Ki / L) * η ^ 2 := by positivity
    have : 0 ≤ (L / Ki) * e ^ 2 := by positivity
    linarith
  have hB0 : 0 ≤ B := by positivity
  have := mul_le_mul_of_nonneg_left hEb hB0
  have heq : B * (2 * (1 / L + 1 / Ki) * (L / 2 * e ^ 2 + Ki / 2 * η ^ 2)) =
      8 * B * (1 / L + 1 / Ki) * (L / 2 * e ^ 2 + Ki / 2 * η ^ 2) / 4 := by ring
  nlinarith

/-- The scalar inequality behind the practical Lyapunov function of the undamped cascade. -/
private theorem center_ineq {I C V0 x2 w u ψ E K k : ℝ} (hI : 0 < I) (hC : 0 < C) (hV : 0 < V0)
    (hx2 : 0 < x2) (hx2' : x2 < 2 * V0) (hK : 0 ≤ K) (hE : 0 ≤ E) (hψ : ψ ^ 2 ≤ K * E)
    (hu : u = C / 2 * (x2 + V0) * w + ψ) (hg : (4 * K + 1) * E < u ^ 2)
    (hμ : |u| < I * (4 * K + 1) / (4 * (3 * C * V0 / 2) * |k| + 1)) :
    u * (-(I * w) + k * E) ≤ 0 := by
  set lam := 4 * K + 1 with hlam
  set A0 := 3 * C * V0 / 2 with hA0
  set a := C / 2 * (x2 + V0) with ha
  have ha0 : 0 < a := by positivity
  have haA : a ≤ A0 := by rw [ha, hA0]; nlinarith
  have hlam0 : 0 < lam := by positivity
  -- E ≤ u²/λ
  have hEu : lam * E ≤ u ^ 2 := hg.le
  -- u ψ ≤ u²/2
  have huψ : u * ψ ≤ u ^ 2 / 2 := by
    have h1 : u * ψ ≤ u ^ 2 / 4 + ψ ^ 2 := by nlinarith [sq_nonneg (u / 2 - ψ)]
    have h2 : 4 * (K * E) ≤ u ^ 2 := by nlinarith
    nlinarith
  -- a k u E ≤ I u²/4
  have hk : a * k * u * E ≤ I * u ^ 2 / 4 := by
    have h1 : a * k * u * E ≤ a * |k| * |u| * E := by
      have : a * k * u * E ≤ |a * k * u * E| := le_abs_self _
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos ha0, abs_of_nonneg hE] at this
      exact this
    have hden : 0 < 4 * A0 * |k| + 1 := by positivity
    have h2 : a * |k| * |u| * E ≤ A0 * |k| * |u| * E := by
      have : 0 ≤ |k| * |u| * E := by positivity
      nlinarith
    have h3 : A0 * |k| * |u| * E * lam ≤ A0 * |k| * |u| * u ^ 2 := by
      have : 0 ≤ A0 * |k| * |u| := by positivity
      nlinarith
    have h4 : A0 * |k| * |u| ≤ I * lam / 4 := by
      have hμ' : |u| * (4 * A0 * |k| + 1) < I * lam := by
        rw [lt_div_iff₀ hden] at hμ
        exact hμ
      nlinarith [abs_nonneg u, abs_nonneg k]
    have h5 : A0 * |k| * |u| * u ^ 2 ≤ I * lam / 4 * u ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg u)
    have h6 : A0 * |k| * |u| * E ≤ I * u ^ 2 / 4 := by
      have : A0 * |k| * |u| * E * lam ≤ I * u ^ 2 / 4 * lam := by nlinarith
      exact le_of_mul_le_mul_right this hlam0
    linarith
  -- multiply by a
  have hw : a * w = u - ψ := by rw [hu]; ring
  have key : a * (u * (-(I * w) + k * E)) = -(I * u ^ 2) + I * (u * ψ) + a * k * u * E := by
    have : a * (u * (-(I * w) + k * E)) = -(I * u * (a * w)) + a * k * u * E := by ring
    rw [this, hw]
    ring
  have hfin : a * (u * (-(I * w) + k * E)) ≤ 0 := by
    rw [key]
    have : I * (u * ψ) ≤ I * (u ^ 2 / 2) := mul_le_mul_of_nonneg_left huψ hI.le
    have : 0 ≤ I * u ^ 2 := by positivity
    linarith
  by_contra hcon
  have := mul_pos ha0 (not_le.mp hcon)
  linarith

/-- `R + Kp = 0`, `Ki > 0`, `I_dc0 > 0`: Lyapunov stable. The current loop is a centre (its energy
`loopEnergy` is conserved) and the DC node contracts; with `u = centerStorage − centerStorage(x*)`
the practical Lyapunov function `(max (u² − λ loopEnergy) 0)² + loopEnergy` does not increase near
the operating point (`u u̇ ≤ 0` wherever `u² > λ loopEnergy`). -/
private theorem lyapunovStable_center (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0)
    (hKi : 0 < p.pi.Ki) (hR : p.pi.R + p.pi.Kp = 0) (hI : 0 < p.Idc0) :
    LyapunovStable (p.field p.Id0) p.eqState := by
  set ξ0 := p.pi.R * p.Id0 / p.pi.Ki with hξ0
  set b := 2 * p.pi.R * p.Id0 - p.Vd0 with hb
  set K := 8 * ((p.pi.L * p.Id0) ^ 2 + b ^ 2 + p.pi.Ki ^ 2 / 4 + p.pi.Kp ^ 2 / 4) *
    (1 / p.pi.L + 1 / p.pi.Ki) with hK
  have hK0 : 0 ≤ K := by positivity
  set k := p.pi.Kp / p.pi.L with hk
  set μ := p.Idc0 * (4 * K + 1) / (4 * (3 * p.C * p.V0 / 2) * |k| + 1) with hμ
  have hμ0 : 0 < μ := by positivity
  set cs0 := p.centerStorage p.eqState with hcs0
  have hcsd : Differentiable ℝ p.centerStorage :=
    p.contDiff_centerStorage.differentiable one_ne_zero
  have hEd : Differentiable ℝ p.loopEnergy := fun x =>
    (p.hasFDerivAt_loopEnergy x).differentiableAt
  have hlamEd : Differentiable ℝ (fun y => -(4 * K + 1) * p.loopEnergy y) :=
    fun x => (hEd x).const_mul _
  set g : State 3 → ℝ := fun y => (p.centerStorage y - cs0) ^ 2 + -(4 * K + 1) * p.loopEnergy y
    with hg
  have hgd : Differentiable ℝ g := fun x => ((hcsd x).sub_const cs0).pow 2 |>.add (hlamEd x)
  have hc0 : Continuous fun x : State 3 => x 0 := (Dynamics.contDiff_coord (k := 0) 0).continuous
  have hc1 : Continuous fun x : State 3 => x 1 := (Dynamics.contDiff_coord (k := 0) 1).continuous
  have hc2 : Continuous fun x : State 3 => x 2 := (Dynamics.contDiff_coord (k := 0) 2).continuous
  set D : Set (State 3) := {x | |x 0 - p.Id0| < 1} ∩ {x | |x 1 - ξ0| < 1} ∩ {x | 0 < x 2} ∩
    {x | x 2 < 2 * p.V0} ∩ {x | |p.centerStorage x - cs0| < μ} with hD
  have hDo : IsOpen D :=
    ((((isOpen_lt (continuous_abs.comp (hc0.sub continuous_const)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (hc1.sub continuous_const)) continuous_const)).inter
      (isOpen_lt continuous_const hc2)).inter (isOpen_lt hc2 continuous_const)).inter
      (isOpen_lt (continuous_abs.comp (hcsd.continuous.sub continuous_const)) continuous_const)
  have hEeq : p.loopEnergy p.eqState = 0 := by simp [loopEnergy, eqState]
  refine lyapunov_stable (V := fun y => max (g y) 0 ^ 2 + p.loopEnergy y) (D := D) three_pos
    ⟨hDo, ?_, (Dynamics.contDiff_one_sq_max_zero.continuous.comp hgd.continuous).add
      hEd.continuous, fun x => ((Dynamics.hasDerivAt_sq_max_zero (g x)).comp_hasFDerivAt x
        (hgd x).hasFDerivAt).differentiableAt.add (hEd x), ?_, fun x hx hne => ?_,
      fun x hx => ?_⟩
  · refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [eqState]
    · simp [eqState, hξ0]
    · simpa [eqState] using hV
    · show p.eqState 2 < 2 * p.V0
      simp [eqState]
      linarith
    · show |p.centerStorage p.eqState - cs0| < μ
      simpa [hcs0] using hμ0
  · simp [hg, hEeq, hcs0]
  · -- positivity away from the operating point
    obtain ⟨⟨⟨⟨-, -⟩, hx2⟩, -⟩, -⟩ := hx
    have hx2' : 0 < x 2 := hx2
    have hE0 := p.loopEnergy_nonneg hL hKi x
    rcases hE0.lt_or_eq with hEpos | hEz
    · have := sq_nonneg (max (g x) 0)
      linarith
    · have hEz' : p.pi.L / 2 * (x 0 - p.Id0) ^ 2 + p.pi.Ki / 2 * (x 1 - ξ0) ^ 2 = 0 :=
        hEz.symm
      have ha : 0 ≤ p.pi.L / 2 * (x 0 - p.Id0) ^ 2 := by positivity
      have hb' : 0 ≤ p.pi.Ki / 2 * (x 1 - ξ0) ^ 2 := by positivity
      have h0 : x 0 = p.Id0 := by
        have : (x 0 - p.Id0) ^ 2 = 0 := by
          have : p.pi.L / 2 * (x 0 - p.Id0) ^ 2 = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · exact h
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        linarith
      have h1 : x 1 = ξ0 := by
        have : (x 1 - ξ0) ^ 2 = 0 := by
          have : p.pi.Ki / 2 * (x 1 - ξ0) ^ 2 = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · exact h
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        linarith
      have h2 : x 2 ≠ p.V0 := by
        intro h2
        apply hne
        ext i
        fin_cases i
        · simpa [eqState] using h0
        · simpa [eqState, hξ0] using h1
        · simpa [eqState] using h2
      have hu : p.centerStorage x - cs0 = p.C / 2 * (x 2 ^ 2 - p.V0 ^ 2) := by
        simp [hcs0, centerStorage, eqState, h0, h1, hξ0]
        ring
      have hsq : x 2 ^ 2 - p.V0 ^ 2 ≠ 0 := by
        intro h0'
        have : (x 2 - p.V0) * (x 2 + p.V0) = 0 := by linear_combination h0'
        rcases mul_eq_zero.mp this with h3 | h3
        · exact h2 (by linarith)
        · linarith
      have hune : p.centerStorage x - cs0 ≠ 0 := by
        rw [hu]; exact mul_ne_zero (by positivity) hsq
      have hgx : g x = (p.centerStorage x - cs0) ^ 2 := by
        simp only [hg, ← hEz]; ring
      have hgpos : 0 < g x := by rw [hgx]; positivity
      rw [max_eq_left hgpos.le, ← hEz]
      positivity
  · -- the derivative along the field
    obtain ⟨⟨⟨⟨hx0, hx1⟩, hx2⟩, hx2'⟩, hxu⟩ := hx
    have hx0' : |x 0 - p.Id0| < 1 := hx0
    have hx1' : |x 1 - ξ0| < 1 := hx1
    have hx2p : 0 < x 2 := hx2
    have hx2l : x 2 < 2 * p.V0 := hx2'
    have hxu' : |p.centerStorage x - cs0| < μ := hxu
    rw [Dynamics.fderiv_sq_max_add_apply (hgd x) (hEd x), p.loopEnergy_lie hL.ne' hKi.ne', hR]
    rw [show g = fun y => (p.centerStorage y - cs0) ^ 2 + (fun y => -(4 * K + 1) * p.loopEnergy y) y
      from rfl, Dynamics.fderiv_sq_sub_add_apply (hcsd x) (hlamEd x),
      fderiv_const_mul (hEd x), _root_.smul_apply, smul_eq_mul,
      p.loopEnergy_lie hL.ne' hKi.ne', hR,
      p.centerStorage_lie hL.ne' hKi.ne' hR hC.ne' hV.ne' (ne_of_gt hx2p)]
    rcases le_or_gt (g x) 0 with hgx | hgx
    · rw [max_eq_right hgx]
      simp
    · rw [max_eq_left hgx.le]
      have hη : (x 1 - ξ0) ^ 2 ≤ 1 := by
        have := abs_lt.mp hx1'
        nlinarith
      have hψ := psi_bound (Id0 := p.Id0) (b := b) (Kp := p.pi.Kp) (e := x 0 - p.Id0) hL hKi hη
      have hu : p.centerStorage x - cs0 = p.C / 2 * (x 2 + p.V0) * (x 2 - p.V0) +
          (p.pi.L * p.Id0 * (x 0 - p.Id0) - b * (x 1 - ξ0) - p.pi.Ki / 2 * (x 1 - ξ0) ^ 2 +
            p.pi.Kp / 2 * ((x 0 - p.Id0) * (x 1 - ξ0))) := by
        simp only [hcs0, centerStorage, eqState, hb, hξ0]
        simp
        ring
      have hgx' : (4 * K + 1) * p.loopEnergy x < (p.centerStorage x - cs0) ^ 2 := by
        simp only [hg] at hgx
        linarith
      have hineq := center_ineq hI hC hV hx2p hx2l hK0 (p.loopEnergy_nonneg hL hKi x)
        (by simpa only [loopEnergy, hξ0, hK] using hψ) hu hgx' hxu'
      have hpos : 0 ≤ g x := hgx.le
      have : 2 * g x * (2 * (p.centerStorage x - cs0) *
          (-(p.Idc0 * (x 2 - p.V0)) + p.pi.Kp / p.pi.L * p.loopEnergy x) +
            -(4 * K + 1) * (-0 * (x 0 - p.Id0) ^ 2)) + -0 * (x 0 - p.Id0) ^ 2 =
          4 * g x * ((p.centerStorage x - cs0) *
            (-(p.Idc0 * (x 2 - p.V0)) + k * p.loopEnergy x)) := by
        rw [hk]; ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hineq

end CascadeParams

private theorem ls_iff (p : CascadeParams) (hL : 0 < p.pi.L) (hC : 0 < p.C) (hV : 0 < p.V0) :
    LyapunovStable (p.field p.Id0) p.eqState ↔
      (0 < p.pi.Ki ∧ ((0 < p.pi.R + p.pi.Kp ∧ 0 ≤ p.Idc0) ∨
        (p.pi.R + p.pi.Kp = 0 ∧ (0 < p.Idc0 ∨ (p.pi.R = 0 ∧ p.Idc0 = 0))))) ∨
      (p.pi.Ki = 0 ∧ p.pi.R * p.Id0 = 0 ∧ 0 < p.pi.R + p.pi.Kp ∧ 0 ≤ p.Idc0) := by
  constructor
  · intro h
    rcases lt_trichotomy p.pi.Ki 0 with hki | hki | hki
    · exact absurd h (p.unstable_of_pi_unstable hV hki.ne (Or.inr (div_neg_of_neg_of_pos hki hL)))
    · have hRI : p.pi.R * p.Id0 = 0 := (p.field_eqState_ki_zero hki hL.ne' hV.ne').mp
        (Dynamics.isEquilibrium_of_lyapunovStable_local CascadeParams.isOpen_posV
          (p.eqState_mem hV) (p.field_contDiffOn _) h)
      refine Or.inr ⟨hki, hRI, ?_, ?_⟩
      · rcases lt_trichotomy (p.pi.R + p.pi.Kp) 0 with hR | hR | hR
        · exact absurd h (p.unstable_ki_zero_lt hL hV hki hRI hR)
        · exact absurd h (p.unstable_ki_zero_eq hL hV hki hRI hR)
        · exact hR
      · exact not_lt.mp fun hI => p.unstable_ki_zero_inverter hL hC hV hki hRI hI h
    · have hI0 : 0 ≤ p.Idc0 := not_lt.mp fun hI => p.unstable_of_inverter hC hV hki.ne' hI h
      refine Or.inl ⟨hki, ?_⟩
      rcases lt_trichotomy (p.pi.R + p.pi.Kp) 0 with hR | hR | hR
      · exact absurd h
          (p.unstable_of_pi_unstable hV hki.ne' (Or.inl (div_neg_of_neg_of_pos hR hL)))
      · refine Or.inr ⟨hR, ?_⟩
        rcases hI0.lt_or_eq with hI | hI
        · exact Or.inl hI
        · refine Or.inr ⟨?_, hI.symm⟩
          by_contra hR0
          exact p.unstable_center_idc_zero hL hC hV hki hR hR0 hI.symm h
      · exact Or.inl ⟨hR, hI0⟩
  · rintro (⟨hKi, ⟨hR, hI⟩ | ⟨hR, hI | ⟨hR0, hI⟩⟩⟩ | ⟨hKi, hRI, hR, hI⟩)
    · rcases hI.lt_or_eq with hI | hI
      · exact (p.locallyExponentiallyStable hL hC hV hR hKi hI).lyapunovStable
      · exact p.lyapunovStable_idc_zero hL hC hV hKi hR hI.symm
    · exact p.lyapunovStable_center hL hC hV hKi hR hI
    · exact p.lyapunovStable_center_idc_zero hL hC hV hKi hR0 (by linarith) hI
    · exact p.lyapunovStable_ki_zero hL hC hV hKi hRI hR hI

/-- With `L, C, V0 > 0` the nonlinear cascade is Lyapunov stable at its operating point exactly
when either `Ki > 0` and (`R + Kp > 0` with `I_dc0 ≥ 0`, or the undamped loop `R + Kp = 0` with
`I_dc0 > 0`, or `R = Kp = 0` with `I_dc0 = 0`), or `Ki = 0`, `R I_d0 = 0` (the operating point is an
equilibrium), `R + Kp > 0` and `I_dc0 ≥ 0`. In particular the undamped current loop is Lyapunov
stable on a rectifying DC node but unstable on an idle one when `R ≠ 0`. -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_lyapunovStable_iff (p : CascadeParams) (hL : 0 < p.pi.L)
    (hC : 0 < p.C) (hV : 0 < p.V0) :
    connection% (p ∈ family.den (.flow .lyapunovStable) ↔
      p ∈ {p : CascadeParams | (0 < p.pi.Ki ∧ ((0 < p.pi.R + p.pi.Kp ∧ 0 ≤ p.Idc0) ∨
        (p.pi.R + p.pi.Kp = 0 ∧ (0 < p.Idc0 ∨ (p.pi.R = 0 ∧ p.Idc0 = 0))))) ∨
        (p.pi.Ki = 0 ∧ p.pi.R * p.Id0 = 0 ∧ 0 < p.pi.R + p.pi.Kp ∧ 0 ≤ p.Idc0)}) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow, Set.mem_ofPred_eq]
  exact ls_iff p hL hC hV

end powerlib.GFL.DCLink
