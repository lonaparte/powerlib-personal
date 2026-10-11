import theorem.Criteria.Jacobian
import theorem.DCLink.Locality
import theorem.CurrentControl.SISO

/-! # DC-link voltage of a grid-following VSC: open loop and PI outer loop (domain)

Model boundary.
* System: the DC-link capacitor of a two-level VSC whose AC side is an ideal current source.
  Per-unit (system base, no `3/2` factor), continuous time, nonlinear (bilinear power balance).
* Direction (work-sync `conventions.md` §D1/§D3/§D9): AC current `i_d` IN-positive, AC power
  absorb-positive `P_ac = V_d i_d` (`V_q = 0`, PLL aligned); `i_src` is the DC source current
  injected into the capacitor node. DC node: `C dV_dc/dt = i_src + P_ac / V_dc`
  (T-vsc-dc-voltage-control §1.1 boxed, lossless bridge `P_bridge = P_ac`).
* Idealizations: ideal current tracking `i_d = i_d*` (inner loop, PWM, delay eliminated);
  stiff PCC voltage `V_d > 0` constant; no PLL dynamics; DC leakage `G_dc = 0`; filter losses
  and inductor energy neglected (`P_bridge = P_PCC`, see `PowerBalance.lean` for the exact
  relation); no current or modulation limits. The field is defined on `V_dc > 0` (it contains
  `1/V_dc`); the linearization theorems use the local versions of `Locality.lean`.
* Operating point: `V_dc = V0 > 0`, AC current `I_d0`, DC-side current
  `I_dc0 = V_d I_d0 / V0 = P_ac0 / V0` (`> 0` rectifier, `< 0` inverter); the source current is
  `i_src = −I_dc0`.

Open loop (`openField`, state `(V_dc)`, `i_d = I_d0` frozen): the Jacobian is
`−I_dc0 / (C V0)` (the pole `s_ol` of §1.4). `openLoop_locallyExponentiallyStable`: rectifier
(`I_dc0 > 0`) ⇒ locally exponentially stable; `openLoop_unstable`: inverter (`I_dc0 < 0`, the
VSC is a constant-power load on the DC side) ⇒ unstable.

PI outer loop (`closedField`, state order `(V_dc, ζ)` with `ζ = ∫ (V_dc − V_dc*) dt`):
`i_d = −Kp (V_dc − V_dc*) − Ki ζ + i_ff` (§1.3 boxed), equilibrium `V_dc = V_dc*`.
* `closedJacobian`: Jacobian `!![−(a Kp + b), −a Ki; 1, 0]`, `a = V_d/(V_dc* C)`,
  `b = I_dc0/(V_dc* C)`, computed with `fderiv` from the nonlinear field.
* `closed_isHurwitz_iff`: with `V_d > 0`, `C > 0`, `V_dc* > 0`:
  Hurwitz ⇔ `Kp > −I_dc0/V_d ∧ Ki > 0` (§1.4 boxed, plus `Ki > 0` made explicit).
* `closedLoop_locallyExponentiallyStable`: then the nonlinear closed loop is locally
  exponentially stable at `(V_dc*, ζ0)`; `closedLoop_unstable_of_kp`, `closedLoop_unstable_of_ki`:
  `Kp < −I_dc0/V_d` or `Ki < 0` ⇒ unstable.
* `smallSignal_transfer`: the linearized loop with input `ΔV_dc*` has transfer
  `a (Kp s + Ki)/(s² + (a Kp + b) s + a Ki)`; `naturalFrequency_damping`:
  `ω_n = √(a Ki)`, `2 ζ ω_n = a Kp + b`.

Source: work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.3, §1.4;
`theory/T-gfl-reduced-order-dynamics.md` §1.2.1, §1.2.4.
-/

noncomputable section
namespace powerlib.DCLink
open Matrix Filter
open scoped Topology
open powerlib.Dynamics

/-! ## Scalar helpers -/

@[powerlib_foundation] private lemma isHurwitz_fin_one_iff (a : ℝ) :
    LinearSystems.IsHurwitz !![a] ↔ a < 0 := by
  rw [Criteria.isHurwitz_iff_characteristic_roots]
  have hdet : ∀ s : ℂ, (LTI.characteristicMatrix !![a] s).det = s - a := by
    intro s
    simp [LTI.characteristicMatrix, Matrix.det_unique]
  simp only [hdet, sub_eq_zero]
  constructor
  · intro h
    simpa using h a rfl
  · rintro h s rfl
    simpa using h

@[powerlib_foundation] private lemma eigenpair_fin_one (a : ℝ) :
    (!![a] : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ) *ᵥ (fun _ => (1 : ℂ)) =
      (a : ℂ) • (fun _ => (1 : ℂ)) := by
  ext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]

/-- The open set `V_dc > 0` of DC states. -/
def posDC (n : ℕ) [NeZero n] : Set (State n) := {x | 0 < x 0}

@[powerlib_foundation] theorem isOpen_posDC (n : ℕ) [NeZero n] : IsOpen (posDC n) :=
  isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin n)).continuous)

/-! ## Open loop -/

/-- Open-loop DC node: `C dV/dt = i_src + P / V` with constant `P = V_d I_d0`. -/
def openField (C isrc P : ℝ) (x : State 1) : State 1 :=
  WithLp.toLp 2 ![(isrc + P / x 0) / C]

/-- Equilibrium state `V_dc = V0`. -/
def dcState (V0 : ℝ) : State 1 := WithLp.toLp 2 ![V0]

@[powerlib_foundation] theorem openField_eq_zero {C P V0 : ℝ} (_hV : V0 ≠ 0) :
    openField C (-(P / V0)) P (dcState V0) = 0 := by
  ext i
  fin_cases i
  simp [openField, dcState]

@[powerlib_foundation] private lemma hasFDerivAt_inv_coord {n : ℕ} (i : Fin n)
    {x : State n} (hx : x i ≠ 0) :
    HasFDerivAt (fun y : State n => (y i)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((x i) ^ 2)⁻¹)).comp (Criteria.coord i)) x :=
  (hasFDerivAt_inv hx).comp x (Criteria.hasFDerivAt_coord i x)

@[powerlib_foundation] theorem openField_contDiffOn (C isrc P : ℝ) :
    ContDiffOn ℝ 1 (openField C isrc P) (posDC 1) := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  simp only [openField, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
  apply ContDiffOn.div_const
  apply contDiffOn_const.add
  apply ContDiffOn.div contDiffOn_const (Criteria.contDiff_coord 0).contDiffOn
  intro x hx
  exact (ne_of_gt hx)

/-- Open-loop Jacobian `−P/(C V0²) = −I_dc0/(C V0)`. -/
@[powerlib_foundation] theorem openJacobian {C isrc P V0 : ℝ} (hV : V0 ≠ 0) :
    fderiv ℝ (openField C isrc P) (dcState V0) =
      Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) !![-(P / V0) / (C * V0)] := by
  have hx : (dcState V0) 0 ≠ 0 := by simpa [dcState] using hV
  have h := (((hasFDerivAt_inv_coord 0 hx).const_mul P).const_add isrc).mul_const C⁻¹
  refine Criteria.fderiv_eq_toEuclideanCLM_of_components _
    (fun _ => C⁻¹ • (P • (ContinuousLinearMap.toSpanSingleton ℝ (-((dcState V0) 0 ^ 2)⁻¹)).comp
      (Criteria.coord 0))) ?_ ?_
  · intro i
    fin_cases i
    convert h using 1
    funext y
    simp [openField, div_eq_mul_inv]
  · intro i v
    fin_cases i
    simp [dcState]
    field_simp

/-- Rectifier (`I_dc0 = P/V0 > 0`): the open-loop DC voltage is locally exponentially
stable. -/
@[powerlib_domain] theorem openLoop_locallyExponentiallyStable {C P V0 : ℝ} (hC : 0 < C)
    (hV : 0 < V0) (hP : 0 < P / V0) :
    Dynamics.LocallyExponentiallyStable (openField C (-(P / V0)) P) (dcState V0) := by
  refine locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_posDC 1)
    (by simpa [posDC, dcState] using hV) _ (openField_contDiffOn _ _ _)
    (openField_eq_zero hV.ne') (openJacobian hV.ne') ?_
  rw [isHurwitz_fin_one_iff, neg_div]
  exact neg_neg_of_pos (div_pos hP (mul_pos hC hV))

/-- Inverter (`I_dc0 = P/V0 < 0`, constant-power load on the DC side): the open-loop DC
voltage is unstable. -/
@[powerlib_domain] theorem openLoop_unstable {C P V0 : ℝ} (hC : 0 < C) (hV : 0 < V0)
    (hP : P / V0 < 0) : Dynamics.Unstable (openField C (-(P / V0)) P) (dcState V0) := by
  refine unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_posDC 1)
    (by simpa [posDC, dcState] using hV) _ (openField_contDiffOn _ _ _)
    (openField_eq_zero hV.ne') (openJacobian hV.ne')
    ⟨_, _, fun h => one_ne_zero (congrFun h 0), eigenpair_fin_one _, ?_⟩
  rw [Complex.ofReal_re, neg_div]
  exact neg_pos.mpr (div_neg_of_neg_of_pos hP (mul_pos hC hV))

/-! ## PI outer loop -/

/-- Parameters of the DC-voltage outer loop around the operating point. -/
@[ext] structure DCParams where
  /-- DC-link capacitance. -/
  C : ℝ
  /-- Stiff PCC d-axis voltage. -/
  Vd : ℝ
  /-- DC voltage reference `V_dc*`. -/
  Vref : ℝ
  Kp : ℝ
  Ki : ℝ
  /-- AC current feedforward `i_ff`. -/
  iff : ℝ
  /-- Equilibrium AC current `I_d0`. -/
  Id0 : ℝ

namespace DCParams

variable (p : DCParams)

/-- DC-side equilibrium current `I_dc0 = V_d I_d0 / V_dc*`. -/
def Idc0 : ℝ := p.Vd * p.Id0 / p.Vref

/-- Source current balancing the operating point: `i_src = −I_dc0`. -/
def isrc : ℝ := -p.Idc0

/-- Current reference of the PI outer loop (ideal current tracking `i_d = i_d*`). -/
def idRef (x : State 2) : ℝ := -p.Kp * (x 0 - p.Vref) - p.Ki * x 1 + p.iff

/-- Closed loop `(dV_dc/dt, dζ/dt)`. -/
def closedField (x : State 2) : State 2 :=
  WithLp.toLp 2 ![(p.isrc + p.Vd * p.idRef x / x 0) / p.C, x 0 - p.Vref]

/-- Equilibrium `(V_dc*, ζ0)` with `i_ff − Ki ζ0 = I_d0`. -/
def eqState : State 2 := WithLp.toLp 2 ![p.Vref, (p.iff - p.Id0) / p.Ki]

@[powerlib_foundation] theorem idRef_eqState (hKi : p.Ki ≠ 0) : p.idRef p.eqState = p.Id0 := by
  simp [idRef, eqState]
  field_simp
  ring

@[powerlib_foundation] theorem closedField_eqState (hKi : p.Ki ≠ 0) (_hV : p.Vref ≠ 0) :
    p.closedField p.eqState = 0 := by
  ext i
  fin_cases i
  · have h := p.idRef_eqState hKi
    simp only [closedField, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero,
      PiLp.zero_apply]
    rw [h]
    simp [isrc, Idc0, eqState]
  · simp [closedField, eqState]

/-- `a = V_d/(V_dc* C)`. -/
def a : ℝ := p.Vd / (p.Vref * p.C)

/-- `b = I_dc0/(V_dc* C)`. -/
def b : ℝ := p.Idc0 / (p.Vref * p.C)

/-- Jacobian matrix of the closed loop at the equilibrium. -/
def jacobian : Matrix (Fin 2) (Fin 2) ℝ := !![-(p.a * p.Kp + p.b), -(p.a * p.Ki); 1, 0]

@[powerlib_foundation] theorem closedField_contDiffOn :
    ContDiffOn ℝ 1 p.closedField (posDC 2) := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  · simp only [closedField, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
    apply ContDiffOn.div_const
    apply contDiffOn_const.add
    apply ContDiffOn.div _ (Criteria.contDiff_coord 0).contDiffOn
    · intro x hx
      exact ne_of_gt hx
    · apply ContDiff.contDiffOn
      unfold idRef
      fun_prop
  · simp only [closedField, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact ((Criteria.contDiff_coord 0).sub contDiff_const).contDiffOn

/-- The Jacobian of the nonlinear closed loop, computed with `fderiv`. -/
@[powerlib_foundation] theorem closedJacobian (hKi : p.Ki ≠ 0) (hV : p.Vref ≠ 0)
    (hC : p.C ≠ 0) :
    fderiv ℝ p.closedField p.eqState =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) p.jacobian := by
  have hx : p.eqState 0 ≠ 0 := by simpa [eqState] using hV
  have hid : HasFDerivAt p.idRef
      (-p.Kp • Criteria.coord 0 - p.Ki • Criteria.coord 1) p.eqState := by
    have h := (((Criteria.hasFDerivAt_coord 0 p.eqState).sub_const p.Vref).const_mul
      (-p.Kp)).sub ((Criteria.hasFDerivAt_coord 1 p.eqState).const_mul p.Ki) |>.add_const p.iff
    convert h using 1
    funext v
    simp only [idRef, Pi.sub_apply]
  have h0 := (((hid.const_mul p.Vd).mul (hasFDerivAt_inv_coord 0 hx)).const_add p.isrc).mul_const
    p.C⁻¹
  have h1' := (Criteria.hasFDerivAt_coord 0 p.eqState).sub_const p.Vref
  refine Criteria.fderiv_eq_toEuclideanCLM_of_components _
    ![p.C⁻¹ • ((p.Vd * p.idRef p.eqState) •
        (ContinuousLinearMap.toSpanSingleton ℝ (-(p.eqState 0 ^ 2)⁻¹)).comp (Criteria.coord 0) +
      (p.eqState 0)⁻¹ • p.Vd • (-p.Kp • Criteria.coord 0 - p.Ki • Criteria.coord 1)),
      Criteria.coord 0] ?_ ?_
  · intro i
    fin_cases i
    · convert h0 using 1
      · funext y
        simp [closedField, div_eq_mul_inv, mul_assoc]
      · rfl
    · convert h1' using 1
      · funext y
        simp [closedField]
      · rfl
  · intro i v
    have hid0 := p.idRef_eqState hKi
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, _root_.smul_apply, _root_.add_apply, hid0]
      simp [jacobian, a, b, Idc0, Fin.sum_univ_two, eqState]
      field_simp
      ring
    · simp [jacobian, Fin.sum_univ_two]

@[powerlib_foundation] theorem jacobian_trace : p.jacobian.trace = -(p.a * p.Kp + p.b) := by
  simp [jacobian, Matrix.trace_fin_two]

@[powerlib_foundation] theorem jacobian_det : p.jacobian.det = p.a * p.Ki := by
  simp [jacobian, Matrix.det_fin_two]

/-- Closed-loop Routh–Hurwitz (§1.4 boxed): `Kp > −I_dc0/V_d ∧ Ki > 0`. -/
@[powerlib_domain] theorem closed_isHurwitz_iff (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) :
    LinearSystems.IsHurwitz p.jacobian ↔ -(p.Idc0 / p.Vd) < p.Kp ∧ 0 < p.Ki := by
  rw [Criteria.isHurwitz_fin_two_iff, jacobian_trace, jacobian_det]
  have hVC : 0 < p.Vref * p.C := mul_pos hV hC
  have ha : 0 < p.a := div_pos hVd hVC
  have hsum : p.a * p.Kp + p.b = (p.Vd * p.Kp + p.Idc0) / (p.Vref * p.C) := by
    simp only [a, b]
    field_simp
  have key : -(p.Idc0 / p.Vd) < p.Kp ↔ 0 < p.Vd * p.Kp + p.Idc0 := by
    rw [← neg_div, div_lt_iff₀ hVd]
    constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · rintro ⟨htr, hdet⟩
    refine ⟨(div_pos_iff_of_pos_right hVC).mp (by rw [← hsum]; linarith),
      pos_of_mul_pos_right hdet ha.le⟩
  · rintro ⟨hkp, hki⟩
    refine ⟨?_, mul_pos ha hki⟩
    have : 0 < p.a * p.Kp + p.b := by rw [hsum]; exact div_pos hkp hVC
    linarith

/-- The nonlinear DC-voltage loop is locally exponentially stable at `(V_dc*, ζ0)` when
`Kp > −I_dc0/V_d` and `Ki > 0`. -/
@[powerlib_domain] theorem closedLoop_locallyExponentiallyStable (hVd : 0 < p.Vd)
    (hV : 0 < p.Vref) (hC : 0 < p.C) (hkp : -(p.Idc0 / p.Vd) < p.Kp) (hki : 0 < p.Ki) :
    Dynamics.LocallyExponentiallyStable p.closedField p.eqState :=
  locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_posDC 2)
    (by simpa [posDC, eqState] using hV) _ p.closedField_contDiffOn
    (p.closedField_eqState hki.ne' hV.ne') (p.closedJacobian hki.ne' hV.ne' hC.ne')
    ((p.closed_isHurwitz_iff hVd hV hC).2 ⟨hkp, hki⟩)

/-- `Kp < −I_dc0/V_d` (insufficient proportional gain in inverter mode): unstable. -/
@[powerlib_domain] theorem closedLoop_unstable_of_kp (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : p.Ki ≠ 0) (hkp : p.Kp < -(p.Idc0 / p.Vd)) :
    Dynamics.Unstable p.closedField p.eqState := by
  refine unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_posDC 2)
    (by simpa [posDC, eqState] using hV) _ p.closedField_contDiffOn
    (p.closedField_eqState hKi hV.ne') (p.closedJacobian hKi hV.ne' hC.ne')
    (Criteria.exists_eigenvalue_re_pos_of_trace_pos _ ?_)
  rw [jacobian_trace]
  have hVC : 0 < p.Vref * p.C := mul_pos hV hC
  have hsum : p.a * p.Kp + p.b = (p.Vd * p.Kp + p.Idc0) / (p.Vref * p.C) := by
    simp only [a, b]
    field_simp
  rw [← neg_div, lt_div_iff₀ hVd] at hkp
  have h2 : p.Vd * p.Kp + p.Idc0 < 0 := by linarith
  rw [hsum]
  exact neg_pos.mpr (div_neg_of_neg_of_pos h2 hVC)

/-- `Ki < 0`: unstable (saddle). -/
@[powerlib_domain] theorem closedLoop_unstable_of_ki (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hki : p.Ki < 0) : Dynamics.Unstable p.closedField p.eqState :=
  unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_posDC 2)
    (by simpa [posDC, eqState] using hV) _ p.closedField_contDiffOn
    (p.closedField_eqState hki.ne hV.ne') (p.closedJacobian hki.ne hV.ne' hC.ne')
    (Criteria.exists_eigenvalue_re_pos_of_det_neg _ (by
      rw [jacobian_det]
      exact mul_neg_of_pos_of_neg (div_pos hVd (mul_pos hV hC)) hki))

/-! ## Small-signal transfer function -/

/-- Linearized loop with input `ΔV_dc*` and output `ΔV_dc`. -/
def smallSignal : LTI.Model (Fin 2) (Fin 1) :=
  ⟨p.jacobian, !![p.a * p.Kp; -1], !![1, 0], !![0]⟩

@[powerlib_foundation] theorem smallSignal_transfer {s : ℂ}
    (hs : s ^ 2 + (p.a * p.Kp + p.b) * s + p.a * p.Ki ≠ 0) :
    LTI.transfer p.smallSignal s 0 0 =
      p.a * (p.Kp * s + p.Ki) / (s ^ 2 + (p.a * p.Kp + p.b) * s + p.a * p.Ki) := by
  have hden : (s - ((-(p.a * p.Kp + p.b) : ℝ) : ℂ)) * (s - ((0 : ℝ) : ℂ)) -
      ((-(p.a * p.Ki) : ℝ) : ℂ) * ((1 : ℝ) : ℂ) =
      s ^ 2 + (p.a * p.Kp + p.b) * s + p.a * p.Ki := by
    push_cast
    ring
  rw [smallSignal, jacobian, CurrentControl.transfer_fin_two _ _ _ _ _ _ _ _ _ (by rwa [hden]),
    hden]
  push_cast
  ring

/-- Standard second-order form: `ω_n² = a Ki`, `2 ζ ω_n = a Kp + b`. -/
@[powerlib_foundation] theorem naturalFrequency_damping (hdet : 0 < p.a * p.Ki) :
    let ωn := Real.sqrt (p.a * p.Ki)
    let ζ := (p.a * p.Kp + p.b) / (2 * ωn)
    ωn ^ 2 = p.a * p.Ki ∧ 2 * ζ * ωn = p.a * p.Kp + p.b := by
  intro ωn ζ
  have hω : 0 < ωn := Real.sqrt_pos.mpr hdet
  refine ⟨Real.sq_sqrt hdet.le, ?_⟩
  simp only [ζ]
  field_simp

end DCParams

end powerlib.DCLink
