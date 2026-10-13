import theorem.Criteria.Jacobian
import theorem.DCLink.Locality
import theorem.CurrentControl.SISO
import theorem.Dynamics.ConverseLinearization
import theorem.Flow.Shift

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
`−I_dc0 / (C V0)` (the pole `s_ol` of §1.4). `openLoop_mem_den_locallyExponentiallyStable`
(formerly `openLoop_locallyExponentiallyStable`): rectifier (`I_dc0 > 0`) ⇒ locally
exponentially stable; `openLoop_mem_den_unstable` (formerly `openLoop_unstable`): inverter
(`I_dc0 < 0`, the VSC is a constant-power load on the DC side) ⇒ unstable.

PI outer loop (`closedField`, state order `(V_dc, ζ)` with `ζ = ∫ (V_dc − V_dc*) dt`):
`i_d = −Kp (V_dc − V_dc*) − Ki ζ + i_ff` (§1.3 boxed), equilibrium `V_dc = V_dc*`.
* `closedJacobian`: Jacobian `!![−(a Kp + b), −a Ki; 1, 0]`, `a = V_d/(V_dc* C)`,
  `b = I_dc0/(V_dc* C)`, computed with `fderiv` from the nonlinear field.
* `closed_isHurwitz_iff` (static): with `V_d > 0`, `C > 0`, `V_dc* > 0`:
  Hurwitz ⇔ `Kp > −I_dc0/V_d ∧ Ki > 0` (§1.4 boxed, plus `Ki > 0` made explicit).
* `closedLoop_mem_den_locallyExponentiallyStable` (formerly
  `closedLoop_locallyExponentiallyStable`): then the nonlinear closed loop is locally
  exponentially stable at `(V_dc*, ζ0)`; `closedLoop_mem_den_unstable_of_kp`,
  `closedLoop_mem_den_unstable_of_ki`: `Kp < −I_dc0/V_d` or `Ki < 0` ⇒ unstable.
* `smallSignal_transfer`: the linearized loop with input `ΔV_dc*` has transfer
  `a (Kp s + Ki)/(s² + (a Kp + b) s + a Ki)`; `naturalFrequency_damping`:
  `ω_n = √(a Ki)`, `2 ζ ω_n = a Kp + b`.

## Families and connection conclusions

Both loops are local spectral families (`Spectral.localFamily`): every complete system is read
as its nonlinear field translated so that the selected operating point is the origin
(`Flow.Property.holds_shift_iff` moves every sentence back to the operating point).
* `openFamily : Family OpenLoop Spectral.Requirement 1 0` — parameters `C`, `P = V_d I_d0` and
  the operating voltage `V0`, the source current `i_src = −P/V0` balancing it. Requirements:
  `stable` — `V0 > 0` and a negative Jacobian `−(P/V0)/(C V0)`; `unstable` — `V0 > 0` and a
  positive one.
* `closedFamily : Family DCParams Spectral.Requirement 2 0` — the PI outer loop about
  `(V_dc*, ζ0)`. Requirements: `stable` — `V_d, V_dc*, C > 0`, `Kp > −I_dc0/V_d`, `Ki > 0`;
  `unstable` — `V_d, V_dc*, C > 0` and `Kp < −I_dc0/V_d` with `Ki ≠ 0`, or `Ki < 0`.
The local sentences translate into `stable`, instability into `unstable`, passivity into nothing
and the global sentences, decay rates, sampled contraction and conservation into the whole
(inconsistent) language. Connection conclusions: `openChain_le_semantics`,
`closedChain_le_semantics` (soundness), `openExact_passive`, `closedExact_passive`, and the
memberships listed above. Exactness within the physical range (converse linearization for fields
that are `C¹` on `V_dc > 0`, `Dynamics.isHurwitz_of_locallyExponentiallyStable_local`):
`openLoop_mem_den_locallyExponentiallyStable_iff` (`C, V0 > 0`: locally exponentially stable iff
rectifier, `P/V0 > 0`) and `closedLoop_mem_den_locallyExponentiallyStable_iff`
(`V_d, V_dc*, C > 0`: iff `Kp > −I_dc0/V_d ∧ Ki > 0`; with `Ki = 0` the integrator direction is
killed by the Jacobian). Outside that range the local exponential translations are not exact:
`openNot_exact_locallyExponentiallyStable` and `closedNot_exact_locallyExponentiallyStable`
(negative-capacitance witnesses). The same witnesses make the local asymptotic and Lyapunov
translations inexact (`openNot_exact_locallyAsymptoticallyStable`, `openNot_exact_lyapunovStable`,
`closedNot_exact_locallyAsymptoticallyStable`, `closedNot_exact_lyapunovStable`, through
`Spectral.local_not_exact_of_not_exact_les`). Within the physical range the open loop is decided
exactly: `openLoop_mem_den_locallyAsymptoticallyStable_iff` (iff rectifier, `P/V0 > 0`; with no AC
power every voltage is an equilibrium) and `openLoop_mem_den_lyapunovStable_iff` (iff `P/V0 ≥ 0`:
the node with no AC power is Lyapunov stable, so that translation is not exact even there). For
the closed loop within the physical range, exactness of the local asymptotic translation is not
claimed (UNPROVED: on `Kp = −I_dc0/V_d`, `Ki > 0` the Jacobian has a purely imaginary pair, decided
only by the nonlinear terms). The Jacobians, Hurwitz criteria and the small-signal transfer function
are static evidence.

Source: work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.3, §1.4;
`theory/T-gfl-reduced-order-dynamics.md` §1.2.1, §1.2.4.
-/

noncomputable section
namespace powerlib.DCLink
open Matrix Filter
open scoped Topology
open powerlib.Dynamics LinearSystems

/-! ## Scalar helpers -/

private lemma isHurwitz_fin_one_iff (a : ℝ) :
    LinearSystems.IsHurwitz !![a] ↔ a < 0 := by
  rw [Criteria.isHurwitz_iff_characteristic_roots]
  have hdet : ∀ s : ℂ, (Linear.characteristicMatrix !![a] s).det = s - a := by
    intro s
    simp [Linear.characteristicMatrix, Matrix.det_unique]
  simp only [hdet, sub_eq_zero]
  constructor
  · intro h
    simpa using h a rfl
  · rintro h s rfl
    simpa using h

private lemma eigenpair_fin_one (a : ℝ) :
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

private lemma hasFDerivAt_inv_coord {n : ℕ} (i : Fin n)
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
stable. Implementation evidence for `openLoop_mem_den_locallyExponentiallyStable`. -/
private theorem openLoop_locallyExponentiallyStable {C P V0 : ℝ} (hC : 0 < C)
    (hV : 0 < V0) (hP : 0 < P / V0) :
    LocallyExponentiallyStable (openField C (-(P / V0)) P) (dcState V0) := by
  refine locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_posDC 1)
    (by simpa [posDC, dcState] using hV) _ (openField_contDiffOn _ _ _)
    (openField_eq_zero hV.ne') (openJacobian hV.ne') ?_
  rw [isHurwitz_fin_one_iff, neg_div]
  exact neg_neg_of_pos (div_pos hP (mul_pos hC hV))

/-- Inverter (`I_dc0 = P/V0 < 0`, constant-power load on the DC side): the open-loop DC
voltage is unstable. Implementation evidence for `openLoop_mem_den_unstable`. -/
private theorem openLoop_unstable {C P V0 : ℝ} (hC : 0 < C) (hV : 0 < V0)
    (hP : P / V0 < 0) : Unstable (openField C (-(P / V0)) P) (dcState V0) := by
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

/-- Closed-loop Routh–Hurwitz (§1.4 boxed): `Kp > −I_dc0/V_d ∧ Ki > 0`. Static evidence on the
model, not a connection conclusion. -/
@[powerlib_foundation] theorem closed_isHurwitz_iff (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
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
`Kp > −I_dc0/V_d` and `Ki > 0`. Implementation evidence for
`closedLoop_mem_den_locallyExponentiallyStable`. -/
private theorem closedLoop_locallyExponentiallyStable (hVd : 0 < p.Vd)
    (hV : 0 < p.Vref) (hC : 0 < p.C) (hkp : -(p.Idc0 / p.Vd) < p.Kp) (hki : 0 < p.Ki) :
    LocallyExponentiallyStable p.closedField p.eqState :=
  locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_posDC 2)
    (by simpa [posDC, eqState] using hV) _ p.closedField_contDiffOn
    (p.closedField_eqState hki.ne' hV.ne') (p.closedJacobian hki.ne' hV.ne' hC.ne')
    ((p.closed_isHurwitz_iff hVd hV hC).2 ⟨hkp, hki⟩)

/-- `Kp < −I_dc0/V_d` (insufficient proportional gain in inverter mode): unstable.
Implementation evidence for `closedLoop_mem_den_unstable_of_kp`. -/
private theorem closedLoop_unstable_of_kp (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : p.Ki ≠ 0) (hkp : p.Kp < -(p.Idc0 / p.Vd)) :
    Unstable p.closedField p.eqState := by
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

/-- `Ki < 0`: unstable (saddle). Implementation evidence for
`closedLoop_mem_den_unstable_of_ki`. -/
private theorem closedLoop_unstable_of_ki (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hki : p.Ki < 0) : Unstable p.closedField p.eqState :=
  unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_posDC 2)
    (by simpa [posDC, eqState] using hV) _ p.closedField_contDiffOn
    (p.closedField_eqState hki.ne hV.ne') (p.closedJacobian hki.ne hV.ne' hC.ne')
    (Criteria.exists_eigenvalue_re_pos_of_det_neg _ (by
      rw [jacobian_det]
      exact mul_neg_of_pos_of_neg (div_pos hVd (mul_pos hV hC)) hki))

/-! ## Small-signal transfer function -/

/-- Linearized loop with input `ΔV_dc*` and output `ΔV_dc`. -/
def smallSignal : Linear.Plant 2 1 :=
  ⟨p.jacobian, !![p.a * p.Kp; -1], !![1, 0], !![0]⟩

@[powerlib_foundation] theorem smallSignal_transfer {s : ℂ}
    (hs : s ^ 2 + (p.a * p.Kp + p.b) * s + p.a * p.Ki ≠ 0) :
    Linear.transfer p.smallSignal s 0 0 =
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

/-! ## The families -/

/-- The open-loop DC node about a selected operating voltage. -/
@[ext] structure OpenLoop where
  /-- DC-link capacitance. -/
  C : ℝ
  /-- AC power `P = V_d I_d0`. -/
  P : ℝ
  /-- Selected operating voltage `V0`. -/
  V0 : ℝ

namespace OpenLoop

/-- The open-loop field translated so that the operating voltage is the origin, with the source
current `i_src = −P/V0` balancing it. -/
def field (m : OpenLoop) (z : State 1) : State 1 :=
  openField m.C (-(m.P / m.V0)) m.P (z + dcState m.V0)

/-- Stability condition: rectifier operation `P/V0 > 0` at a positive voltage, `C > 0`. -/
def Stable (m : OpenLoop) : Prop := 0 < m.V0 ∧ 0 < m.C ∧ 0 < m.P / m.V0

/-- Instability condition: inverter operation `P/V0 < 0` at a positive voltage, `C > 0`. -/
def Unstable (m : OpenLoop) : Prop := 0 < m.V0 ∧ 0 < m.C ∧ m.P / m.V0 < 0

end OpenLoop

/-- The open-loop DC-node family. -/
def openFamily : Family OpenLoop Spectral.Requirement 1 0 :=
  Spectral.localFamily OpenLoop.field OpenLoop.Stable OpenLoop.Unstable

private theorem open_mem_den_flow {m : OpenLoop} {P : Flow.Property} :
    m ∈ openFamily.den (.flow P) ↔
      P.holds (openField m.C (-(m.P / m.V0)) m.P) (dcState m.V0) :=
  (Spectral.localFamily_isAutonomous _ _ _).mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Every translation of the open-loop family is sound: rectifier operation gives local
exponential stability, inverter operation instability (local linearization on `V_dc > 0`). -/
@[powerlib_domain] theorem openChain_le_semantics :
    connection% (∀ P, openFamily.chain P ≤ openFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m h => ?_) (fun m h => ?_)
  · exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (openLoop_locallyExponentiallyStable h.2.1 h.1 h.2.2)
  · exact (Flow.Property.holds_shift_iff .unstable).mpr (openLoop_unstable h.2.1 h.1 h.2.2)

/-- Passivity is translated exactly: the autonomous DC node has no ports. -/
@[powerlib_domain] theorem openExact_passive : connection% (openFamily.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_exact_passive _ _ _

/-- Rectifier (`I_dc0 = P/V0 > 0`): the open-loop DC voltage is locally exponentially stable. -/
@[powerlib_domain] theorem openLoop_mem_den_locallyExponentiallyStable (m : OpenLoop)
    (hC : 0 < m.C) (hV : 0 < m.V0) (hP : 0 < m.P / m.V0) :
    connection% (m ∈ openFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact open_mem_den_flow.mpr (openLoop_locallyExponentiallyStable hC hV hP)

/-- Inverter (`I_dc0 = P/V0 < 0`, constant-power load on the DC side): the open-loop DC
voltage is unstable. -/
@[powerlib_domain] theorem openLoop_mem_den_unstable (m : OpenLoop) (hC : 0 < m.C)
    (hV : 0 < m.V0) (hP : m.P / m.V0 < 0) :
    connection% (m ∈ openFamily.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact open_mem_den_flow.mpr (openLoop_unstable hC hV hP)

namespace DCParams

/-- The closed-loop field translated so that `(V_dc*, ζ0)` is the origin. -/
def shiftedField (p : DCParams) (z : State 2) : State 2 := p.closedField (z + p.eqState)

/-- Stability condition: `V_d, V_dc*, C > 0`, `Kp > −I_dc0/V_d`, `Ki > 0`. -/
def Stable (p : DCParams) : Prop :=
  0 < p.Vd ∧ 0 < p.Vref ∧ 0 < p.C ∧ -(p.Idc0 / p.Vd) < p.Kp ∧ 0 < p.Ki

/-- Instability condition: `V_d, V_dc*, C > 0` and either `Kp < −I_dc0/V_d` with `Ki ≠ 0`, or
`Ki < 0`. -/
def Unstable (p : DCParams) : Prop :=
  0 < p.Vd ∧ 0 < p.Vref ∧ 0 < p.C ∧ ((p.Ki ≠ 0 ∧ p.Kp < -(p.Idc0 / p.Vd)) ∨ p.Ki < 0)

end DCParams

/-- The DC-voltage outer-loop family about `(V_dc*, ζ0)`. -/
def closedFamily : Family DCParams Spectral.Requirement 2 0 :=
  Spectral.localFamily DCParams.shiftedField DCParams.Stable DCParams.Unstable

private theorem closed_mem_den_flow {p : DCParams} {P : Flow.Property} :
    p ∈ closedFamily.den (.flow P) ↔ P.holds p.closedField p.eqState :=
  (Spectral.localFamily_isAutonomous _ _ _).mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Every translation of the DC-voltage loop family is sound: the §1.4 conditions give local
exponential stability, their strict violation instability. -/
@[powerlib_domain] theorem closedChain_le_semantics :
    connection% (∀ P, closedFamily.chain P ≤ closedFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun p h => ?_) (fun p h => ?_)
  · obtain ⟨hVd, hV, hC, hkp, hki⟩ := h
    exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (p.closedLoop_locallyExponentiallyStable hVd hV hC hkp hki)
  · obtain ⟨hVd, hV, hC, h | h⟩ := h
    · exact (Flow.Property.holds_shift_iff .unstable).mpr
        (p.closedLoop_unstable_of_kp hVd hV hC h.1 h.2)
    · exact (Flow.Property.holds_shift_iff .unstable).mpr
        (p.closedLoop_unstable_of_ki hVd hV hC h)

/-- Passivity is translated exactly: the autonomous closed loop has no ports. -/
@[powerlib_domain] theorem closedExact_passive : connection% (closedFamily.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_exact_passive _ _ _

/-- The nonlinear DC-voltage loop is locally exponentially stable at `(V_dc*, ζ0)` when
`Kp > −I_dc0/V_d` and `Ki > 0` (§1.4 boxed). -/
@[powerlib_domain] theorem closedLoop_mem_den_locallyExponentiallyStable (p : DCParams)
    (hVd : 0 < p.Vd) (hV : 0 < p.Vref) (hC : 0 < p.C) (hkp : -(p.Idc0 / p.Vd) < p.Kp)
    (hki : 0 < p.Ki) :
    connection% (p ∈ closedFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact closed_mem_den_flow.mpr (p.closedLoop_locallyExponentiallyStable hVd hV hC hkp hki)

/-- `Kp < −I_dc0/V_d` (insufficient proportional gain in inverter mode): unstable. -/
@[powerlib_domain] theorem closedLoop_mem_den_unstable_of_kp (p : DCParams) (hVd : 0 < p.Vd)
    (hV : 0 < p.Vref) (hC : 0 < p.C) (hKi : p.Ki ≠ 0) (hkp : p.Kp < -(p.Idc0 / p.Vd)) :
    connection% (p ∈ closedFamily.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact closed_mem_den_flow.mpr (p.closedLoop_unstable_of_kp hVd hV hC hKi hkp)

/-- `Ki < 0`: unstable (saddle). -/
@[powerlib_domain] theorem closedLoop_mem_den_unstable_of_ki (p : DCParams) (hVd : 0 < p.Vd)
    (hV : 0 < p.Vref) (hC : 0 < p.C) (hki : p.Ki < 0) :
    connection% (p ∈ closedFamily.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact closed_mem_den_flow.mpr (p.closedLoop_unstable_of_ki hVd hV hC hki)

/-! ## Exactness within the physical range -/

/-- Positive capacitance and operating voltage: the open-loop DC node is locally exponentially
stable exactly in rectifier operation, `P/V0 > 0`. -/
@[powerlib_domain] theorem openLoop_mem_den_locallyExponentiallyStable_iff (m : OpenLoop) (hC : 0 < m.C)
    (hV : 0 < m.V0) :
    connection% (m ∈ openFamily.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : OpenLoop | 0 < m.P / m.V0}) := by
  unfold powerlib.TMIO.Statement
  rw [open_mem_den_flow, Set.mem_ofPred_eq]
  change LocallyExponentiallyStable _ _ ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local (isOpen_posDC 1)
    (by simpa [posDC, dcState] using hV) _ (openField_contDiffOn _ _ _) (openJacobian hV.ne'),
    isHurwitz_fin_one_iff, neg_div, neg_lt_zero]
  have hCV : 0 < m.C * m.V0 := mul_pos hC hV
  constructor
  · rintro ⟨-, h⟩
    exact (div_pos_iff_of_pos_right hCV).mp h
  · intro h
    exact ⟨openField_eq_zero hV.ne', div_pos h hCV⟩

/-- A negative capacitance with negative power, `C = P = −1`, `V0 = 1`. -/
def negativeCapacitance : OpenLoop := ⟨-1, -1, 1⟩

/-- The negative-capacitance node is locally exponentially stable (Jacobian `−1`). -/
@[powerlib_domain] theorem negativeCapacitance_mem_den_locallyExponentiallyStable :
    connection% (negativeCapacitance ∈ openFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine open_mem_den_flow.mpr (locallyExponentiallyStable_of_isHurwitz_jacobian_local
    (isOpen_posDC 1) (by simp [posDC, dcState, negativeCapacitance]) _
    (openField_contDiffOn _ _ _) (openField_eq_zero (by norm_num [negativeCapacitance]))
    (openJacobian (by norm_num [negativeCapacitance])) ?_)
  rw [isHurwitz_fin_one_iff]
  norm_num [negativeCapacitance]

/-- The local exponential translation of the open-loop family is sound but not exact: the
negative-capacitance node is locally exponentially stable without `C > 0`. -/
@[powerlib_domain] theorem openNot_exact_locallyExponentiallyStable :
    connection% (¬ openFamily.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeCapacitance_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : OpenLoop.Stable negativeCapacitance := hmem .stable rfl
  have := hs.2.1
  norm_num [negativeCapacitance] at this

/-- With no integral gain the integrator direction is killed by the Jacobian. -/
private theorem closed_fderiv_ki_zero {p : DCParams} (hKi : p.Ki = 0) (hV : 0 < p.Vref) :
    fderiv ℝ p.closedField p.eqState (EuclideanSpace.single 1 1) = 0 := by
  have hx : p.eqState ∈ posDC 2 := by simpa [posDC, DCParams.eqState] using hV
  have hdiff : DifferentiableAt ℝ p.closedField p.eqState :=
    (p.closedField_contDiffOn.contDiffAt ((isOpen_posDC 2).mem_nhds hx)).differentiableAt
      one_ne_zero
  have hconst : ∀ t : ℝ, p.closedField (p.eqState + t • EuclideanSpace.single 1 1) =
      p.closedField p.eqState := by
    intro t
    ext i
    fin_cases i <;> simp [DCParams.closedField, DCParams.idRef, hKi]
  have h1 : HasDerivAt (fun t : ℝ => p.closedField (p.eqState + t • EuclideanSpace.single 1 1))
      (fderiv ℝ p.closedField p.eqState (EuclideanSpace.single 1 1)) 0 := by
    have h := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single 1 1 : State 2)).const_add
        p.eqState) (by simp)
    rw [one_smul] at h
    exact h
  have h2 : HasDerivAt (fun t : ℝ => p.closedField (p.eqState + t • EuclideanSpace.single 1 1))
      0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/-- Positive `V_d`, `V_dc*`, `C`: the nonlinear DC-voltage loop is locally exponentially stable
at `(V_dc*, ζ0)` exactly when `Kp > −I_dc0/V_d` and `Ki > 0` (§1.4 boxed, both directions). -/
@[powerlib_domain] theorem closedLoop_mem_den_locallyExponentiallyStable_iff (p : DCParams) (hVd : 0 < p.Vd)
    (hV : 0 < p.Vref) (hC : 0 < p.C) :
    connection% (p ∈ closedFamily.den (.flow .locallyExponentiallyStable) ↔
      p ∈ {p : DCParams | -(p.Idc0 / p.Vd) < p.Kp ∧ 0 < p.Ki}) := by
  unfold powerlib.TMIO.Statement
  rw [closed_mem_den_flow, Set.mem_ofPred_eq]
  have hx : p.eqState ∈ posDC 2 := by simpa [posDC, DCParams.eqState] using hV
  constructor
  · intro h
    by_cases hKi : p.Ki = 0
    · exact absurd h (Dynamics.not_locallyExponentiallyStable_of_fderiv_apply_eq_zero_local
        (isOpen_posDC 2) hx p.closedField_contDiffOn
        (by intro h0; simpa using congrArg (fun v : State 2 => v 1) h0)
        (closed_fderiv_ki_zero hKi hV))
    · exact (p.closed_isHurwitz_iff hVd hV hC).mp
        (Dynamics.isHurwitz_of_locallyExponentiallyStable_local (isOpen_posDC 2) hx _
          p.closedField_contDiffOn (p.closedJacobian hKi hV.ne' hC.ne') h)
  · rintro ⟨hkp, hki⟩
    exact p.closedLoop_locallyExponentiallyStable hVd hV hC hkp hki

/-- A negative-capacitance loop: `C = −1`, `V_d = V_dc* = 1`, `Kp = Ki = −1`, `i_ff = I_d0 = 0`. -/
def negativeCapacitanceLoop : DCParams := ⟨-1, 1, 1, -1, -1, 0, 0⟩

/-- The negative-capacitance loop is locally exponentially stable: its Jacobian
`[[−1, −1], [1, 0]]` is Hurwitz. -/
@[powerlib_domain] theorem negativeCapacitanceLoop_mem_den_locallyExponentiallyStable :
    connection% (negativeCapacitanceLoop ∈
      closedFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hKi : negativeCapacitanceLoop.Ki ≠ 0 := by norm_num [negativeCapacitanceLoop]
  have hV : negativeCapacitanceLoop.Vref ≠ 0 := by norm_num [negativeCapacitanceLoop]
  have hC : negativeCapacitanceLoop.C ≠ 0 := by norm_num [negativeCapacitanceLoop]
  refine closed_mem_den_flow.mpr (locallyExponentiallyStable_of_isHurwitz_jacobian_local
    (isOpen_posDC 2) (by simp [posDC, DCParams.eqState, negativeCapacitanceLoop]) _
    negativeCapacitanceLoop.closedField_contDiffOn
    (negativeCapacitanceLoop.closedField_eqState hKi hV)
    (negativeCapacitanceLoop.closedJacobian hKi hV hC) ?_)
  rw [Criteria.isHurwitz_fin_two_iff, DCParams.jacobian_trace, DCParams.jacobian_det]
  norm_num [negativeCapacitanceLoop, DCParams.a, DCParams.b, DCParams.Idc0]

/-- The local exponential translation of the DC-voltage loop family is sound but not exact: the
negative-capacitance loop is locally exponentially stable without `C > 0`. -/
@[powerlib_domain] theorem closedNot_exact_locallyExponentiallyStable :
    connection% (¬ closedFamily.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeCapacitanceLoop_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : DCParams.Stable negativeCapacitanceLoop := hmem .stable rfl
  have := hs.2.2.1
  norm_num [negativeCapacitanceLoop] at this

/-! ## The local asymptotic and Lyapunov sentences -/

/-- With no AC power (`P = 0`) the open-loop node has no dynamics: every voltage is an
equilibrium. -/
private theorem openField_P_zero {C P V0 : ℝ} (hP : P / V0 = 0) (hV : 0 < V0) (x : State 1) :
    openField C (-(P / V0)) P x = 0 := by
  have hP0 : P = 0 := by
    rcases div_eq_zero_iff.mp hP with h | h
    · exact h
    · exact absurd h hV.ne'
  subst hP0
  ext i
  fin_cases i
  simp [openField]

/-- Positive capacitance and operating voltage: the open-loop DC node is locally asymptotically
stable exactly in rectifier operation, `P/V0 > 0` — the local exponential condition. Inverter
operation is unstable, and with no AC power (`P = 0`) every voltage is an equilibrium
(`Dynamics.not_localAsymptoticStable_of_equilibria`). -/
@[powerlib_domain] theorem openLoop_mem_den_locallyAsymptoticallyStable_iff (m : OpenLoop)
    (hC : 0 < m.C) (hV : 0 < m.V0) :
    connection% (m ∈ openFamily.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : OpenLoop | 0 < m.P / m.V0}) := by
  unfold powerlib.TMIO.Statement
  rw [open_mem_den_flow, Set.mem_ofPred_eq]
  change LocalAsymptoticStable _ _ ↔ _
  constructor
  · intro h
    rcases lt_trichotomy (m.P / m.V0) 0 with hP | hP | hP
    · exact absurd h.1 (openLoop_unstable hC hV hP)
    · exfalso
      refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
        ⟨dcState (m.V0 + ε / 2), fun h' => ?_, ?_, openField_P_zero hP hV _⟩) h
      · have := congrArg (fun y : State 1 => y 0) h'
        simp [dcState] at this
        linarith
      · rw [EuclideanSpace.norm_eq]
        simp only [dcState, PiLp.sub_apply, Fin.sum_univ_one,
          Matrix.cons_val_zero, Real.norm_eq_abs, sq_abs, add_sub_cancel_left]
        rw [Real.sqrt_sq (by linarith)]
        linarith
    · exact hP
  · intro hP
    exact Flow.locallyExponentiallyStable_localAsymptoticStable
      (openLoop_locallyExponentiallyStable hC hV hP)

/-- Positive capacitance and operating voltage: the open-loop DC node is Lyapunov stable exactly
when `P/V0 ≥ 0` — rectifier operation, or no AC power, where the node has no dynamics. So the
Lyapunov translation is not exact even within the physical range. -/
@[powerlib_domain] theorem openLoop_mem_den_lyapunovStable_iff (m : OpenLoop) (hC : 0 < m.C)
    (hV : 0 < m.V0) :
    connection% (m ∈ openFamily.den (.flow .lyapunovStable) ↔
      m ∈ {m : OpenLoop | 0 ≤ m.P / m.V0}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  constructor
  · intro h
    rw [open_mem_den_flow] at h
    by_contra hP
    exact openLoop_unstable hC hV (not_le.mp hP) h
  · intro hP
    rcases eq_or_lt_of_le hP with hP | hP
    · refine ((Spectral.localFamily_isAutonomous OpenLoop.field OpenLoop.Stable
        OpenLoop.Unstable).mem_den_flow (P := .lyapunovStable) (x := m)).mpr ?_
      refine Dynamics.lyapunovStable_of_inner_nonpos one_pos
        (ContinuousLinearMap.id ℝ (State 1)) Function.injective_id fun z => ?_
      have hz : OpenLoop.field m z = 0 := openField_P_zero hP.symm hV _
      simp [hz]
    · rw [open_mem_den_flow]
      exact (openLoop_locallyExponentiallyStable hC hV hP).lyapunovStable

private theorem open_les_of {m : OpenLoop} (h : OpenLoop.Stable m) :
    LocallyExponentiallyStable (OpenLoop.field m) 0 :=
  (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
    (openLoop_locallyExponentiallyStable h.2.1 h.1 h.2.2)

/-- The local asymptotic translation of the open-loop family is not exact (the
negative-capacitance node). -/
@[powerlib_domain] theorem openNot_exact_locallyAsymptoticallyStable :
    connection% (¬ openFamily.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := openNot_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun _ hm => open_les_of hm) h (Or.inr rfl)

/-- The Lyapunov translation of the open-loop family is not exact (the negative-capacitance
node; within the physical range, the node with no AC power). -/
@[powerlib_domain] theorem openNot_exact_lyapunovStable :
    connection% (¬ openFamily.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := openNot_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun _ hm => open_les_of hm) h (Or.inl rfl)

private theorem closed_les_of {p : DCParams} (h : DCParams.Stable p) :
    LocallyExponentiallyStable (DCParams.shiftedField p) 0 := by
  obtain ⟨hVd, hV, hC, hkp, hki⟩ := h
  exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
    (p.closedLoop_locallyExponentiallyStable hVd hV hC hkp hki)

/-- The local asymptotic translation of the DC-voltage loop family is not exact (the
negative-capacitance loop). -/
@[powerlib_domain] theorem closedNot_exact_locallyAsymptoticallyStable :
    connection% (¬ closedFamily.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := closedNot_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun _ hm => closed_les_of hm) h (Or.inr rfl)

/-- The Lyapunov translation of the DC-voltage loop family is not exact (the
negative-capacitance loop). -/
@[powerlib_domain] theorem closedNot_exact_lyapunovStable :
    connection% (¬ closedFamily.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := closedNot_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h
  exact Spectral.local_not_exact_of_not_exact_les (fun _ hm => closed_les_of hm) h (Or.inl rfl)

end powerlib.DCLink
