import theorem.Dynamics.Coordinates
import theorem.Dynamics.Locality
import theorem.Spectral.Family
import theorem.LTI.Plant
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.Dynamics.Shift
import theorem.Criteria.Hurwitz2

/-! # DC-link voltage of a grid-following VSC: open loop and PI outer loop

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
  `1/V_dc`); the linearization theorems use the local versions of
  `theorem/Dynamics/Locality.lean`.
* Operating point: `V_dc = V0 > 0`, AC current `I_d0`, DC-side current
  `I_dc0 = V_d I_d0 / V0 = P_ac0 / V0` (`> 0` rectifier, `< 0` inverter); the source current is
  `i_src = −I_dc0`.

Source: work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.3, §1.4;
`theory/T-gfl-reduced-order-dynamics.md` §1.2.1, §1.2.4.

Results.
Open loop (`openField`, state `(V_dc)`, `i_d = I_d0` frozen): the Jacobian is
`−I_dc0 / (C V0)` (the pole `s_ol` of §1.4). `openLoop_mem_den_locallyExponentiallyStable`:
rectifier (`I_dc0 > 0`) ⇒ locally exponentially stable; `openLoop_mem_den_unstable`: inverter
(`I_dc0 < 0`, the VSC is a constant-power load on the DC side) ⇒ unstable.

PI outer loop (`closedField`, state order `(V_dc, ζ)` with `ζ = ∫ (V_dc − V_dc*) dt`):
`i_d = −Kp (V_dc − V_dc*) − Ki ζ + i_ff` (§1.3 boxed), equilibrium `V_dc = V_dc*`.
* `closedJacobian`: Jacobian `!![−(a Kp + b), −a Ki; 1, 0]`, `a = V_d/(V_dc* C)`,
  `b = I_dc0/(V_dc* C)`, computed with `fderiv` from the nonlinear field.
* `closed_isHurwitz_iff` (static): with `V_d > 0`, `C > 0`, `V_dc* > 0`:
  Hurwitz ⇔ `Kp > −I_dc0/V_d ∧ Ki > 0` (§1.4 boxed, plus `Ki > 0` made explicit).
* `closedLoop_mem_den_locallyExponentiallyStable`: then the nonlinear closed loop is locally
  exponentially stable at `(V_dc*, ζ0)`; `closedLoop_mem_den_unstable_of_kp`,
  `closedLoop_mem_den_unstable_of_ki`: `Kp < −I_dc0/V_d` or `Ki < 0` ⇒ unstable.
* `smallSignal_transfer`: the linearized loop with input `ΔV_dc*` has transfer
  `a (Kp s + Ki)/(s² + (a Kp + b) s + a Ki)`; `naturalFrequency_damping`:
  `ω_n = √(a Ki)`, `2 ζ ω_n = a Kp + b`.

Family and connection conclusions.
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
the node with no AC power is Lyapunov stable, so that translation is not exact even there).

The closed loop within the physical range (`V_d, V_dc*, C > 0`) is decided exactly as well:
* Boundary `Kp = −I_dc0/V_d`, `Ki > 0` (Jacobian with the purely imaginary pair `±i √(a Ki)`): the
  nonlinear loop `dv/dt = −(V_d Ki/C) z/(V_dc* + v)`, `dz/dt = v` is reversible and conserves
  `DCParams.centerEnergy` `= V_dc* v²/2 + v³/3 + (V_d Ki/(2C)) z²` (`DCParams.centerEnergy_lie`),
  a strict minimum on `V_dc > 0` (`DCParams.centerEnergy_pos`): a centre (first Lyapunov
  coefficient `0`, computed with SymPy and implied by the first integral) — Lyapunov stable, not
  locally asymptotically stable.
* `Ki = 0`: the integrator does not act on the loop; the operating point is an equilibrium iff
  `i_ff = I_d0`, and then every `(V_dc*, ζ)` is one.
* `closedLoop_mem_den_locallyAsymptoticallyStable_iff`: locally asymptotically stable iff
  `Kp > −I_dc0/V_d ∧ Ki > 0`, i.e. `closedExact_locallyAsymptoticallyStable_physical`: the
  generated space of the local asymptotic translation is its denotation cut by the physical range
  (the translation is exact there).
* `closedLoop_mem_den_lyapunovStable_iff`: Lyapunov stable iff `Ki > 0 ∧ Kp ≥ −I_dc0/V_d` (centre
  included) or `Ki = 0 ∧ i_ff = I_d0 ∧ Kp > −I_dc0/V_d` (`ζ + γ (V_dc* v + v²/2)` conserved, `v²`
  decaying); `Ki = 0` with `Kp ≤ −I_dc0/V_d` is unstable (Chetaev's theorem,
  `Dynamics.unstable_of_chetaev_local`). Hence `closedNot_exact_lyapunovStable_physical`: the
  Lyapunov translation is not exact within the physical range, witness `centerLoop`
  (`C = V_d = V_dc* = Ki = 1`, `Kp = i_ff = I_d0 = 0`; `centerLoop_mem_den_lyapunovStable`,
  `centerLoop_not_mem_den_locallyAsymptoticallyStable`).
The degenerate-equilibrium tools for the locally `C¹` field are in
`theorem/Dynamics/Instability.lean` and `theorem/Dynamics/Lyapunov.lean`.
The Jacobians, Hurwitz criteria and the small-signal transfer function are static evidence.
-/

noncomputable section
namespace powerlib.GFL.DCLink
open Matrix Filter
open scoped Topology
open powerlib.Dynamics LinearSystems

/-! ## Scalar helpers -/

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

@[powerlib_foundation] theorem openField_contDiffOn (C isrc P : ℝ) :
    ContDiffOn ℝ 1 (openField C isrc P) (posDC 1) := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  simp only [openField, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
  apply ContDiffOn.div_const
  apply contDiffOn_const.add
  apply ContDiffOn.div contDiffOn_const (Dynamics.contDiff_coord 0).contDiffOn
  intro x hx
  exact (ne_of_gt hx)

/-- Open-loop Jacobian `−P/(C V0²) = −I_dc0/(C V0)`. -/
@[powerlib_foundation] theorem openJacobian {C isrc P V0 : ℝ} (hV : V0 ≠ 0) :
    fderiv ℝ (openField C isrc P) (dcState V0) =
      Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) !![-(P / V0) / (C * V0)] := by
  have hx : (dcState V0) 0 ≠ 0 := by simpa [dcState] using hV
  have h := (((hasFDerivAt_inv_coord 0 hx).const_mul P).const_add isrc).mul_const C⁻¹
  refine Dynamics.fderiv_eq_toEuclideanCLM_of_components _
    (fun _ => C⁻¹ • (P • (ContinuousLinearMap.toSpanSingleton ℝ (-((dcState V0) 0 ^ 2)⁻¹)).comp
      (Dynamics.coord 0))) ?_ ?_
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
  refine Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_posDC 1)
    (by simpa [posDC, dcState] using hV) _ (openField_contDiffOn _ _ _)
    (openField_eq_zero hV.ne') (openJacobian hV.ne') ?_
  rw [Linear.isHurwitz_one_iff, neg_div]
  exact neg_neg_of_pos (div_pos hP (mul_pos hC hV))

/-- Inverter (`I_dc0 = P/V0 < 0`, constant-power load on the DC side): the open-loop DC
voltage is unstable. Implementation evidence for `openLoop_mem_den_unstable`. -/
private theorem openLoop_unstable {C P V0 : ℝ} (hC : 0 < C) (hV : 0 < V0)
    (hP : P / V0 < 0) : Unstable (openField C (-(P / V0)) P) (dcState V0) := by
  refine Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_posDC 1)
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
    apply ContDiffOn.div _ (Dynamics.contDiff_coord 0).contDiffOn
    · intro x hx
      exact ne_of_gt hx
    · apply ContDiff.contDiffOn
      unfold idRef
      fun_prop
  · simp only [closedField, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact ((Dynamics.contDiff_coord 0).sub contDiff_const).contDiffOn

/-- The Jacobian of the nonlinear closed loop, computed with `fderiv`. -/
@[powerlib_foundation] theorem closedJacobian (hKi : p.Ki ≠ 0) (hV : p.Vref ≠ 0)
    (hC : p.C ≠ 0) :
    fderiv ℝ p.closedField p.eqState =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) p.jacobian := by
  have hx : p.eqState 0 ≠ 0 := by simpa [eqState] using hV
  have hid : HasFDerivAt p.idRef
      (-p.Kp • Dynamics.coord 0 - p.Ki • Dynamics.coord 1) p.eqState := by
    have h := (((Dynamics.hasFDerivAt_coord 0 p.eqState).sub_const p.Vref).const_mul
      (-p.Kp)).sub ((Dynamics.hasFDerivAt_coord 1 p.eqState).const_mul p.Ki) |>.add_const p.iff
    convert h using 1
    funext v
    simp only [idRef, Pi.sub_apply]
  have h0 := (((hid.const_mul p.Vd).mul (hasFDerivAt_inv_coord 0 hx)).const_add p.isrc).mul_const
    p.C⁻¹
  have h1' := (Dynamics.hasFDerivAt_coord 0 p.eqState).sub_const p.Vref
  refine Dynamics.fderiv_eq_toEuclideanCLM_of_components _
    ![p.C⁻¹ • ((p.Vd * p.idRef p.eqState) •
        (ContinuousLinearMap.toSpanSingleton ℝ (-(p.eqState 0 ^ 2)⁻¹)).comp (Dynamics.coord 0) +
      (p.eqState 0)⁻¹ • p.Vd • (-p.Kp • Dynamics.coord 0 - p.Ki • Dynamics.coord 1)),
      Dynamics.coord 0] ?_ ?_
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
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_posDC 2)
    (by simpa [posDC, eqState] using hV) _ p.closedField_contDiffOn
    (p.closedField_eqState hki.ne' hV.ne') (p.closedJacobian hki.ne' hV.ne' hC.ne')
    ((p.closed_isHurwitz_iff hVd hV hC).2 ⟨hkp, hki⟩)

/-- `Kp < −I_dc0/V_d` (insufficient proportional gain in inverter mode): unstable.
Implementation evidence for `closedLoop_mem_den_unstable_of_kp`. -/
private theorem closedLoop_unstable_of_kp (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : p.Ki ≠ 0) (hkp : p.Kp < -(p.Idc0 / p.Vd)) :
    Unstable p.closedField p.eqState := by
  refine Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_posDC 2)
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
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_posDC 2)
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
  rw [smallSignal, jacobian, LTI.transfer_fin_two _ _ _ _ _ _ _ _ _ (by rwa [hden]),
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
  Spectral.mem_den_flow_iff_shift (f := fun m : OpenLoop => openField m.C (-(m.P / m.V0)) m.P)
    (pt := fun m => dcState m.V0) (Spectral.localFamily_isAutonomous _ _ _)

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
  Spectral.mem_den_flow_iff_shift (f := DCParams.closedField) (pt := DCParams.eqState)
    (Spectral.localFamily_isAutonomous _ _ _)

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
@[powerlib_domain] theorem openLoop_mem_den_locallyExponentiallyStable_iff (m : OpenLoop)
    (hC : 0 < m.C) (hV : 0 < m.V0) :
    connection% (m ∈ openFamily.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : OpenLoop | 0 < m.P / m.V0}) := by
  unfold powerlib.TMIO.Statement
  rw [open_mem_den_flow, Set.mem_ofPred_eq]
  change LocallyExponentiallyStable _ _ ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local (isOpen_posDC 1)
    (by simpa [posDC, dcState] using hV) _ (openField_contDiffOn _ _ _) (openJacobian hV.ne'),
    Linear.isHurwitz_one_iff, neg_div, neg_lt_zero]
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
  refine open_mem_den_flow.mpr (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local
    (isOpen_posDC 1) (by simp [posDC, dcState, negativeCapacitance]) _
    (openField_contDiffOn _ _ _) (openField_eq_zero (by norm_num [negativeCapacitance]))
    (openJacobian (by norm_num [negativeCapacitance])) ?_)
  rw [Linear.isHurwitz_one_iff]
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
@[powerlib_domain] theorem closedLoop_mem_den_locallyExponentiallyStable_iff (p : DCParams)
    (hVd : 0 < p.Vd) (hV : 0 < p.Vref) (hC : 0 < p.C) :
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
  refine closed_mem_den_flow.mpr (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local
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

/-! ## The boundary `Kp = −I_dc0/V_d` and the missing integral gain

On `Kp = −I_dc0/V_d`, `Ki > 0` the Jacobian `[[0, −a Ki], [1, 0]]` has the purely imaginary pair
`±i √(a Ki)`. The nonlinear loop is then `dv/dt = −(V_d Ki/C) z/(V_dc* + v)`, `dz/dt = v`, which
is reversible (`z ↦ −z`, `t ↦ −t`) and has the first integral `DCParams.centerEnergy`
(`V_dc* v²/2 + v³/3 + (V_d Ki/(2C)) z²`, a strict minimum on `V_dc > 0`): a centre, so the first
Lyapunov coefficient vanishes and the boundary is Lyapunov stable but not locally asymptotically
stable. With `Ki = 0` the integrator state does not act on the loop. -/

namespace DCParams

variable (p : DCParams)

/-- The conserved energy of the boundary loop `Kp = −I_dc0/V_d`:
`V_dc* v²/2 + v³/3 + (V_d Ki/(2C)) z²`, `v = V_dc − V_dc*`, `z = ζ − ζ0`. -/
def centerEnergy (x : State 2) : ℝ :=
  p.Vref / 2 * (x 0 - p.Vref) ^ 2 + 1 / 3 * (x 0 - p.Vref) ^ 3 +
    p.Vd * p.Ki / (2 * p.C) * (x 1 - (p.iff - p.Id0) / p.Ki) ^ 2

@[powerlib_foundation] theorem hasFDerivAt_centerEnergy (x : State 2) :
    HasFDerivAt p.centerEnergy
      ((p.Vref * (x 0 - p.Vref) + (x 0 - p.Vref) ^ 2) • Dynamics.coord 0 +
        (p.Vd * p.Ki / p.C * (x 1 - (p.iff - p.Id0) / p.Ki)) • Dynamics.coord 1) x := by
  have h0 := (Dynamics.hasFDerivAt_coord 0 x).sub_const p.Vref
  have h1 := (Dynamics.hasFDerivAt_coord 1 x).sub_const ((p.iff - p.Id0) / p.Ki)
  have h := (((h0.pow 2).const_mul (p.Vref / 2)).add ((h0.pow 3).const_mul (1 / 3))).add
    ((h1.pow 2).const_mul (p.Vd * p.Ki / (2 * p.C)))
  convert h using 1
  · funext y; simp [centerEnergy]
  · ext v
    simp
    field_simp

/-- On the boundary `Kp = −I_dc0/V_d` the energy is conserved on `V_dc ≠ 0`. -/
@[powerlib_foundation] theorem centerEnergy_lie (hVd : p.Vd ≠ 0) (hV : p.Vref ≠ 0)
    (hKi : p.Ki ≠ 0) (hkp : p.Kp = -(p.Idc0 / p.Vd)) {x : State 2} (hx : x 0 ≠ 0) :
    fderiv ℝ p.centerEnergy x (p.closedField x) = 0 := by
  rw [(p.hasFDerivAt_centerEnergy x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul, closedField,
    Matrix.cons_val_zero, Matrix.cons_val_one, idRef, isrc, Idc0]
  rw [hkp]
  simp only [Idc0]
  field_simp
  ring

/-- The boundary energy is positive away from the equilibrium on `V_dc > 0`. -/
@[powerlib_foundation] theorem centerEnergy_pos (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : 0 < p.Ki) {x : State 2} (hx : 0 < x 0) (hne : x ≠ p.eqState) :
    0 < p.centerEnergy x := by
  have hk : 0 < p.Vd * p.Ki / (2 * p.C) := by positivity
  have hform : p.centerEnergy x = (x 0 - p.Vref) ^ 2 * (p.Vref + 2 * x 0) / 6 +
      p.Vd * p.Ki / (2 * p.C) * (x 1 - (p.iff - p.Id0) / p.Ki) ^ 2 := by
    simp only [centerEnergy]; ring
  rw [hform]
  by_cases h0 : x 0 = p.Vref
  · have h1 : x 1 ≠ (p.iff - p.Id0) / p.Ki := by
      intro h1
      apply hne
      ext i
      fin_cases i
      · simpa [eqState] using h0
      · simpa [eqState] using h1
    have : 0 < (x 1 - (p.iff - p.Id0) / p.Ki) ^ 2 := by
      have := sub_ne_zero.mpr h1
      positivity
    have h2 : 0 ≤ (x 0 - p.Vref) ^ 2 * (p.Vref + 2 * x 0) / 6 := by
      have : 0 ≤ p.Vref + 2 * x 0 := by linarith
      positivity
    nlinarith
  · have : 0 < (x 0 - p.Vref) ^ 2 := by
      have := sub_ne_zero.mpr h0
      positivity
    have h2 : 0 < (x 0 - p.Vref) ^ 2 * (p.Vref + 2 * x 0) / 6 := by
      have : 0 < p.Vref + 2 * x 0 := by linarith
      positivity
    have : 0 ≤ p.Vd * p.Ki / (2 * p.C) * (x 1 - (p.iff - p.Id0) / p.Ki) ^ 2 := by positivity
    linarith

private theorem eqState_mem (hV : 0 < p.Vref) : p.eqState ∈ posDC 2 := by
  simpa [posDC, eqState] using hV

/-- On the boundary the loop is Lyapunov stable: the energy is conserved and has a strict
minimum. -/
private theorem closed_lyapunovStable_boundary (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : 0 < p.Ki) (hkp : p.Kp = -(p.Idc0 / p.Vd)) :
    LyapunovStable p.closedField p.eqState :=
  lyapunov_stable (V := p.centerEnergy) (D := posDC 2) two_pos
    ⟨isOpen_posDC 2, p.eqState_mem hV,
      continuous_iff_continuousAt.mpr fun x => (p.hasFDerivAt_centerEnergy x).continuousAt,
      fun x => (p.hasFDerivAt_centerEnergy x).differentiableAt,
      by simp [centerEnergy, eqState],
      fun x hx hne => p.centerEnergy_pos hVd hV hC hKi hx hne,
      fun x hx => (p.centerEnergy_lie hVd.ne' hV.ne' hKi.ne' hkp (ne_of_gt hx)).le⟩

/-- On the boundary the loop is not locally asymptotically stable: the conserved energy keeps
every nearby solution on its level. -/
private theorem closed_not_las_boundary (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : 0 < p.Ki) (hkp : p.Kp = -(p.Idc0 / p.Vd)) :
    ¬ LocalAsymptoticStable p.closedField p.eqState := by
  refine Dynamics.not_localAsymptoticStable_of_lie_nonpos_local (V := fun x => -p.centerEnergy x)
    (ρ := 1) (isOpen_posDC 2) (p.eqState_mem hV) p.closedField_contDiffOn
    (fun x => (p.hasFDerivAt_centerEnergy x).differentiableAt.neg) one_pos
    (fun x hx _ => ?_) (fun ε hε => ?_)
  · rw [fderiv_fun_neg, _root_.neg_apply,
      p.centerEnergy_lie hVd.ne' hV.ne' hKi.ne' hkp (ne_of_gt hx), neg_zero]
  · refine ⟨p.eqState + WithLp.toLp 2 ![ε / 2, 0], ?_, ?_⟩
    · rw [add_sub_cancel_left]
      refine (Dynamics.norm_le_abs_add_abs_two _).trans_lt ?_
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero, add_zero]
      rw [abs_of_pos (by positivity)]
      linarith
    · have hne : p.eqState + WithLp.toLp 2 ![ε / 2, 0] ≠ p.eqState := by
        intro h
        have := congrArg (fun y : State 2 => y 0) h
        simp at this
        linarith
      have hpos := p.centerEnergy_pos hVd hV hC hKi (by simp [eqState]; positivity) hne
      have h0 : p.centerEnergy p.eqState = 0 := by simp [centerEnergy, eqState]
      simp only [h0, neg_zero, neg_lt_zero]
      exact hpos

/-! ### No integral gain -/

/-- With no integral gain the field does not depend on `ζ`. -/
private theorem closedField_ki_zero_shift (hKi : p.Ki = 0) (x : State 2) (t : ℝ) :
    p.closedField (x + t • EuclideanSpace.single 1 1) = p.closedField x := by
  ext i
  fin_cases i <;> simp [closedField, idRef, hKi]

/-- With no integral gain the loop is not locally asymptotically stable: either the operating
point is not an equilibrium, or every `(V_dc*, ζ)` is one. -/
private theorem closed_not_las_ki_zero (hV : 0 < p.Vref) (hKi : p.Ki = 0) :
    ¬ LocalAsymptoticStable p.closedField p.eqState := by
  intro h
  by_cases h0 : p.closedField p.eqState = 0
  · refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
      ⟨p.eqState + (ε / 2) • EuclideanSpace.single 1 1, ?_, ?_, ?_⟩) h
    · intro h'
      have := congrArg (fun y : State 2 => y 1) h'
      simp at this
      linarith
    · rw [add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · rw [p.closedField_ki_zero_shift hKi]
      exact h0
  · exact h0 (Dynamics.isEquilibrium_of_lyapunovStable_local (isOpen_posDC 2) (p.eqState_mem hV)
      p.closedField_contDiffOn h.1)

/-- With no integral gain and `i_ff = I_d0` the DC equation is
`dV_dc/dt = −V_d (I_d0 + V_dc* Kp)(V_dc − V_dc*)/(V_dc* C V_dc)`. -/
private theorem closedField_zero_ki (hKi : p.Ki = 0) (hff : p.iff = p.Id0) (hV : p.Vref ≠ 0)
    (hC : p.C ≠ 0) {x : State 2} (hx : x 0 ≠ 0) :
    p.closedField x 0 =
      -(p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref)) / (p.Vref * p.C * x 0) := by
  simp only [closedField, PiLp.toLp_apply, Matrix.cons_val_zero, idRef, isrc, Idc0, hKi, hff]
  field_simp
  ring

private theorem closedField_one (x : State 2) : p.closedField x 1 = x 0 - p.Vref := by
  simp [closedField]

private theorem eqState_one_ki_zero (hKi : p.Ki = 0) : p.eqState 1 = 0 := by
  simp [eqState, hKi]

/-- The Lyapunov function of the loop without integral gain: `ζ + γ (V_dc* v + v²/2)` is
conserved, `v²` decays. -/
private def driftEnergy (γ : ℝ) (x : State 2) : ℝ :=
  (x 1 + γ * (p.Vref * (x 0 - p.Vref) + (x 0 - p.Vref) ^ 2 / 2)) ^ 2 + (x 0 - p.Vref) ^ 2

private theorem hasFDerivAt_driftEnergy (γ : ℝ) (x : State 2) :
    HasFDerivAt (p.driftEnergy γ)
      ((2 * (x 1 + γ * (p.Vref * (x 0 - p.Vref) + (x 0 - p.Vref) ^ 2 / 2)) *
          (γ * (p.Vref + (x 0 - p.Vref))) + 2 * (x 0 - p.Vref)) • Dynamics.coord 0 +
        (2 * (x 1 + γ * (p.Vref * (x 0 - p.Vref) + (x 0 - p.Vref) ^ 2 / 2))) •
          Dynamics.coord 1) x := by
  have h0 := (Dynamics.hasFDerivAt_coord 0 x).sub_const p.Vref
  have h1 := Dynamics.hasFDerivAt_coord 1 x
  have hin := h1.add (((h0.const_mul p.Vref).add ((h0.pow 2).const_mul (1 / 2))).const_mul γ)
  have h := (hin.pow 2).add (h0.pow 2)
  convert h using 1
  · funext y; simp [driftEnergy]; ring
  · ext v
    simp
    ring

/-- Without integral gain, with `i_ff = I_d0` and `Kp > −I_dc0/V_d`, the loop is Lyapunov
stable. -/
private theorem closed_lyapunovStable_ki_zero (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : p.Ki = 0) (hff : p.iff = p.Id0) (hβ : 0 < p.Id0 + p.Vref * p.Kp) :
    LyapunovStable p.closedField p.eqState := by
  set γ := p.C * p.Vref / (p.Vd * (p.Id0 + p.Vref * p.Kp)) with hγ
  refine lyapunov_stable (V := p.driftEnergy γ) (D := posDC 2) two_pos
    ⟨isOpen_posDC 2, p.eqState_mem hV,
      continuous_iff_continuousAt.mpr fun x => (p.hasFDerivAt_driftEnergy γ x).continuousAt,
      fun x => (p.hasFDerivAt_driftEnergy γ x).differentiableAt,
      by simp [driftEnergy, eqState, hKi], fun x hx hne => ?_, fun x hx => ?_⟩
  · have hx' : 0 < x 0 := hx
    by_cases h0 : x 0 = p.Vref
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hne
        ext i
        fin_cases i
        · simpa [eqState] using h0
        · simp [eqState, hKi, h1]
      rw [show p.driftEnergy γ x = x 1 ^ 2 by simp only [driftEnergy, h0]; ring]
      positivity
    · have : (x 0 - p.Vref) ^ 2 > 0 := by
        have := sub_ne_zero.mpr h0
        positivity
      simp only [driftEnergy]
      positivity
  · have hx' : 0 < x 0 := hx
    rw [(p.hasFDerivAt_driftEnergy γ x).fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul]
    rw [p.closedField_zero_ki hKi hff hV.ne' hC.ne' (ne_of_gt hx'), p.closedField_one]
    have hconv : p.Vref + (x 0 - p.Vref) = x 0 := by ring
    rw [hconv]
    have hcancel : γ * x 0 * (-(p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref)) /
        (p.Vref * p.C * x 0)) = -(x 0 - p.Vref) := by
      rw [hγ]
      field_simp
    have hdec : 2 * (x 0 - p.Vref) * (-(p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref)) /
        (p.Vref * p.C * x 0)) ≤ 0 := by
      have : 0 ≤ p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref) ^ 2 / (p.Vref * p.C * x 0) := by
        positivity
      have heq : 2 * (x 0 - p.Vref) * (-(p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref)) /
          (p.Vref * p.C * x 0)) =
          -(2 * (p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref) ^ 2 / (p.Vref * p.C * x 0))) := by
        ring
      rw [heq]
      linarith
    have key : (2 * (x 1 + γ * (p.Vref * (x 0 - p.Vref) + (x 0 - p.Vref) ^ 2 / 2)) * (γ * x 0) +
          2 * (x 0 - p.Vref)) *
        (-(p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref)) / (p.Vref * p.C * x 0)) +
      2 * (x 1 + γ * (p.Vref * (x 0 - p.Vref) + (x 0 - p.Vref) ^ 2 / 2)) * (x 0 - p.Vref) =
        2 * (x 0 - p.Vref) * (-(p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref)) /
          (p.Vref * p.C * x 0)) := by
      linear_combination (2 * (x 1 + γ * (p.Vref * (x 0 - p.Vref) + (x 0 - p.Vref) ^ 2 / 2))) *
        hcancel
    rw [key]
    exact hdec

/-- Without integral gain, with `i_ff = I_d0` and `Kp < −I_dc0/V_d`, the voltage error grows:
unstable (Chetaev's function `v²`). -/
private theorem closed_unstable_ki_zero_lt (hVd : 0 < p.Vd) (hV : 0 < p.Vref)
    (hC : 0 < p.C) (hKi : p.Ki = 0) (hff : p.iff = p.Id0) (hβ : p.Id0 + p.Vref * p.Kp < 0) :
    _root_.Unstable p.closedField p.eqState := by
  refine Dynamics.unstable_of_chetaev_local (W := fun x : State 2 => (x 0 - p.Vref) ^ 2)
    (r := 1) (isOpen_posDC 2) (p.eqState_mem hV) p.closedField_contDiffOn (by fun_prop) one_pos
    (fun ε hε => ⟨p.eqState + WithLp.toLp 2 ![ε / 2, 0], ?_, ?_⟩) (fun x hx _ hW => ?_)
  · rw [add_sub_cancel_left]
    refine (Dynamics.norm_le_abs_add_abs_two _).trans_lt ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero, add_zero]
    rw [abs_of_pos (by positivity)]
    linarith
  · simp [eqState]
    positivity
  · have hx' : 0 < x 0 := hx
    have hd : HasFDerivAt (fun x : State 2 => (x 0 - p.Vref) ^ 2)
        ((2 * (x 0 - p.Vref)) • Dynamics.coord 0) x := by
      have h := ((Dynamics.hasFDerivAt_coord 0 x).sub_const p.Vref).pow 2
      convert h using 1
      ext v; simp
    rw [hd.fderiv]
    simp only [_root_.smul_apply, Dynamics.coord_apply, smul_eq_mul]
    rw [p.closedField_zero_ki hKi hff hV.ne' hC.ne' (ne_of_gt hx')]
    have hW' : 0 < (x 0 - p.Vref) ^ 2 := hW
    have : 0 < -(p.Vd * (p.Id0 + p.Vref * p.Kp)) * (x 0 - p.Vref) ^ 2 / (p.Vref * p.C * x 0) := by
      have : 0 < -(p.Vd * (p.Id0 + p.Vref * p.Kp)) := by nlinarith
      positivity
    have heq : 2 * (x 0 - p.Vref) * (-(p.Vd * (p.Id0 + p.Vref * p.Kp) * (x 0 - p.Vref)) /
        (p.Vref * p.C * x 0)) =
        2 * (-(p.Vd * (p.Id0 + p.Vref * p.Kp)) * (x 0 - p.Vref) ^ 2 / (p.Vref * p.C * x 0)) := by
      ring
    rw [heq]
    linarith

/-- Without integral gain, with `i_ff = I_d0` and `Kp = −I_dc0/V_d`, the voltage error stays
constant and the integrator drifts: unstable (Chetaev's function `v z`). -/
private theorem closed_unstable_ki_zero_eq (hV : 0 < p.Vref) (hC : 0 < p.C) (hKi : p.Ki = 0)
    (hff : p.iff = p.Id0) (hβ : p.Id0 + p.Vref * p.Kp = 0) :
    _root_.Unstable p.closedField p.eqState := by
  refine Dynamics.unstable_of_chetaev_local (W := fun x : State 2 => (x 0 - p.Vref) * x 1)
    (r := 1) (isOpen_posDC 2) (p.eqState_mem hV) p.closedField_contDiffOn (by fun_prop) one_pos
    (fun ε hε => ⟨p.eqState + WithLp.toLp 2 ![ε / 4, ε / 4], ?_, ?_⟩) (fun x hx _ hW => ?_)
  · rw [add_sub_cancel_left]
    refine (Dynamics.norm_le_abs_add_abs_two _).trans_lt ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [abs_of_pos (by positivity)]
    linarith
  · simp [eqState, hKi]
    positivity
  · have hx' : 0 < x 0 := hx
    have hd : HasFDerivAt (fun x : State 2 => (x 0 - p.Vref) * x 1)
        (x 1 • Dynamics.coord 0 + (x 0 - p.Vref) • Dynamics.coord 1) x := by
      have h := ((Dynamics.hasFDerivAt_coord 0 x).sub_const p.Vref).mul
        (Dynamics.hasFDerivAt_coord 1 x)
      convert h using 1
      ext v; simp; ring
    rw [hd.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul]
    rw [p.closedField_zero_ki hKi hff hV.ne' hC.ne' (ne_of_gt hx'), p.closedField_one, hβ]
    have hv : x 0 - p.Vref ≠ 0 := by
      intro h
      have : (x 0 - p.Vref) * x 1 = 0 := by rw [h, zero_mul]
      linarith
    have : 0 < (x 0 - p.Vref) * (x 0 - p.Vref) := mul_self_pos.mpr hv
    simpa using this

/-- Without integral gain the operating point is an equilibrium exactly when the feedforward
matches the operating current, `i_ff = I_d0`. -/
private theorem closedField_eqState_ki_zero (hKi : p.Ki = 0) (hVd : p.Vd ≠ 0) (hV : p.Vref ≠ 0)
    (hC : p.C ≠ 0) : p.closedField p.eqState = 0 ↔ p.iff = p.Id0 := by
  constructor
  · intro h
    have h0 := congrArg (fun y : State 2 => y 0) h
    simp only [closedField, eqState, idRef, isrc, Idc0, hKi, PiLp.toLp_apply, Matrix.cons_val_zero,
      PiLp.zero_apply] at h0
    field_simp at h0
    have : p.Vd * (p.iff - p.Id0) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hVd
    · linarith
  · intro hff
    ext i
    fin_cases i
    · simp only [closedField, eqState, idRef, isrc, Idc0, hKi, hff, PiLp.toLp_apply,
        Fin.zero_eta, Matrix.cons_val_zero, PiLp.zero_apply]
      field_simp
      ring
    · simp [closedField, eqState]

/-- `Kp` against the boundary `−I_dc0/V_d`: the sign of `I_d0 + V_dc* Kp`. -/
private theorem kp_sub_boundary (hVd : 0 < p.Vd) (hV : 0 < p.Vref) :
    p.Vd * p.Kp + p.Idc0 = p.Vd / p.Vref * (p.Id0 + p.Vref * p.Kp) ∧
      (-(p.Idc0 / p.Vd) < p.Kp ↔ 0 < p.Vd * p.Kp + p.Idc0) ∧
      (-(p.Idc0 / p.Vd) = p.Kp ↔ p.Vd * p.Kp + p.Idc0 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Idc0]
    field_simp
    ring
  · rw [← neg_div, div_lt_iff₀ hVd]
    constructor <;> intro h <;> linarith
  · rw [← neg_div, div_eq_iff hVd.ne']
    constructor <;> intro h <;> linarith

end DCParams

private theorem closed_las_iff (p : DCParams) (hVd : 0 < p.Vd) (hV : 0 < p.Vref) (hC : 0 < p.C) :
    LocalAsymptoticStable p.closedField p.eqState ↔ -(p.Idc0 / p.Vd) < p.Kp ∧ 0 < p.Ki := by
  constructor
  · intro h
    rcases lt_trichotomy p.Ki 0 with hki | hki | hki
    · exact absurd h.1 (p.closedLoop_unstable_of_ki hVd hV hC hki)
    · exact absurd h (p.closed_not_las_ki_zero hV hki)
    · refine ⟨?_, hki⟩
      rcases lt_trichotomy p.Kp (-(p.Idc0 / p.Vd)) with hkp | hkp | hkp
      · exact absurd h.1 (p.closedLoop_unstable_of_kp hVd hV hC hki.ne' hkp)
      · exact absurd h (p.closed_not_las_boundary hVd hV hC hki hkp)
      · exact hkp
  · rintro ⟨hkp, hki⟩
    exact Flow.locallyExponentiallyStable_localAsymptoticStable
      (p.closedLoop_locallyExponentiallyStable hVd hV hC hkp hki)

private theorem closed_ls_iff (p : DCParams) (hVd : 0 < p.Vd) (hV : 0 < p.Vref) (hC : 0 < p.C) :
    LyapunovStable p.closedField p.eqState ↔ (0 < p.Ki ∧ -(p.Idc0 / p.Vd) ≤ p.Kp) ∨
      (p.Ki = 0 ∧ p.iff = p.Id0 ∧ -(p.Idc0 / p.Vd) < p.Kp) := by
  obtain ⟨hsplit, hlt, -⟩ := p.kp_sub_boundary hVd hV
  have hVV : 0 < p.Vd / p.Vref := div_pos hVd hV
  constructor
  · intro h
    rcases lt_trichotomy p.Ki 0 with hki | hki | hki
    · exact absurd h (p.closedLoop_unstable_of_ki hVd hV hC hki)
    · have hff : p.iff = p.Id0 := (p.closedField_eqState_ki_zero hki hVd.ne' hV.ne' hC.ne').mp
        (Dynamics.isEquilibrium_of_lyapunovStable_local (isOpen_posDC 2) (p.eqState_mem hV)
          p.closedField_contDiffOn h)
      refine Or.inr ⟨hki, hff, ?_⟩
      rw [hlt, hsplit]
      rcases lt_trichotomy (p.Id0 + p.Vref * p.Kp) 0 with hβ | hβ | hβ
      · exact absurd h (p.closed_unstable_ki_zero_lt hVd hV hC hki hff hβ)
      · exact absurd h (p.closed_unstable_ki_zero_eq hV hC hki hff hβ)
      · positivity
    · exact Or.inl ⟨hki, not_lt.mp fun hkp => p.closedLoop_unstable_of_kp hVd hV hC hki.ne' hkp h⟩
  · rintro (⟨hki, hkp⟩ | ⟨hki, hff, hkp⟩)
    · rcases hkp.lt_or_eq with hkp | hkp
      · exact (p.closedLoop_locallyExponentiallyStable hVd hV hC hkp hki).lyapunovStable
      · exact p.closed_lyapunovStable_boundary hVd hV hC hki hkp.symm
    · refine p.closed_lyapunovStable_ki_zero hVd hV hC hki hff ?_
      rw [hlt, hsplit] at hkp
      exact pos_of_mul_pos_right hkp hVV.le

/-- Positive `V_d`, `V_dc*`, `C`: the nonlinear DC-voltage loop is locally asymptotically stable
at `(V_dc*, ζ0)` exactly when `Kp > −I_dc0/V_d` and `Ki > 0` — the local exponential condition.
On the boundary `Kp = −I_dc0/V_d`, `Ki > 0` the conserved energy `DCParams.centerEnergy` keeps every
nearby solution on its level (a centre, first Lyapunov coefficient zero); with `Ki = 0` either the
operating point is not an equilibrium or every `(V_dc*, ζ)` is one; elsewhere the loop is
unstable. -/
@[powerlib_domain] theorem closedLoop_mem_den_locallyAsymptoticallyStable_iff (p : DCParams)
    (hVd : 0 < p.Vd) (hV : 0 < p.Vref) (hC : 0 < p.C) :
    connection% (p ∈ closedFamily.den (.flow .locallyAsymptoticallyStable) ↔
      p ∈ {p : DCParams | -(p.Idc0 / p.Vd) < p.Kp ∧ 0 < p.Ki}) := by
  unfold powerlib.TMIO.Statement
  rw [closed_mem_den_flow, Set.mem_ofPred_eq]
  exact closed_las_iff p hVd hV hC

/-- Positive `V_d`, `V_dc*`, `C`: the nonlinear DC-voltage loop is Lyapunov stable at
`(V_dc*, ζ0)` exactly when `Ki > 0` and `Kp ≥ −I_dc0/V_d` (the centre on the boundary included),
or `Ki = 0`, `i_ff = I_d0` (the operating point is an equilibrium) and `Kp > −I_dc0/V_d` (then
`ζ + γ (V_dc* v + v²/2)` is conserved and `v²` decays). With `Ki = 0`, `Kp = −I_dc0/V_d` the
voltage error is frozen and the integrator drifts; with `Kp < −I_dc0/V_d` the error grows
(Chetaev's theorem). -/
@[powerlib_domain] theorem closedLoop_mem_den_lyapunovStable_iff (p : DCParams) (hVd : 0 < p.Vd)
    (hV : 0 < p.Vref) (hC : 0 < p.C) :
    connection% (p ∈ closedFamily.den (.flow .lyapunovStable) ↔
      p ∈ {p : DCParams | (0 < p.Ki ∧ -(p.Idc0 / p.Vd) ≤ p.Kp) ∨
        (p.Ki = 0 ∧ p.iff = p.Id0 ∧ -(p.Idc0 / p.Vd) < p.Kp)}) := by
  unfold powerlib.TMIO.Statement
  rw [closed_mem_den_flow, Set.mem_ofPred_eq]
  exact closed_ls_iff p hVd hV hC

/-- The loop on the boundary: `C = V_d = V_dc* = Ki = 1`, `Kp = i_ff = I_d0 = 0` (`I_dc0 = 0`, so
`Kp = −I_dc0/V_d`). -/
def centerLoop : DCParams := ⟨1, 1, 1, 0, 1, 0, 0⟩

private theorem centerLoop_boundary :
    centerLoop.Kp = -(centerLoop.Idc0 / centerLoop.Vd) := by
  norm_num [centerLoop, DCParams.Idc0]

/-- The boundary loop is Lyapunov stable (a centre with the conserved energy
`v²/2 + v³/3 + z²/2`). -/
@[powerlib_domain] theorem centerLoop_mem_den_lyapunovStable :
    connection% (centerLoop ∈ closedFamily.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact closed_mem_den_flow.mpr (centerLoop.closed_lyapunovStable_boundary
    (by norm_num [centerLoop]) (by norm_num [centerLoop]) (by norm_num [centerLoop])
    (by norm_num [centerLoop]) centerLoop_boundary)

/-- The boundary loop is not locally asymptotically stable. -/
@[powerlib_domain] theorem centerLoop_not_mem_den_locallyAsymptoticallyStable :
    connection% (centerLoop ∉ closedFamily.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [closed_mem_den_flow]
  exact centerLoop.closed_not_las_boundary (by norm_num [centerLoop]) (by norm_num [centerLoop])
    (by norm_num [centerLoop]) (by norm_num [centerLoop]) centerLoop_boundary

private theorem closed_realize_stable :
    TMIO.realize closedFamily.meets (closedFamily.translate (.flow .locallyAsymptoticallyStable)) =
      {p : DCParams | DCParams.Stable p} := by
  ext p
  rw [TMIO.mem_realize]
  change (∀ q ∈ ({.stable} : Set Spectral.Requirement), Spectral.Meets _ _ p q) ↔ _
  simp

/-- Within positive `V_d`, `V_dc*`, `C` the local asymptotic translation is exact: the generated
space of its translation (`stable`) is the local asymptotic denotation cut by the physical
range. -/
@[powerlib_domain] theorem closedExact_locallyAsymptoticallyStable_physical :
    connection% (TMIO.realize closedFamily.meets
        (closedFamily.translate (.flow .locallyAsymptoticallyStable)) =
      closedFamily.den (.flow .locallyAsymptoticallyStable) ∩
        {p : DCParams | 0 < p.Vd ∧ 0 < p.Vref ∧ 0 < p.C}) := by
  unfold powerlib.TMIO.Statement
  rw [closed_realize_stable]
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [closed_mem_den_flow]
  constructor
  · rintro ⟨hVd, hV, hC, hkp, hki⟩
    exact ⟨(closed_las_iff p hVd hV hC).mpr ⟨hkp, hki⟩, hVd, hV, hC⟩
  · rintro ⟨h, hVd, hV, hC⟩
    obtain ⟨hkp, hki⟩ := (closed_las_iff p hVd hV hC).mp h
    exact ⟨hVd, hV, hC, hkp, hki⟩

/-- Within positive `V_d`, `V_dc*`, `C` the Lyapunov translation is not exact: the boundary loop
`centerLoop` is physical and Lyapunov stable but does not meet `stable`. -/
@[powerlib_domain] theorem closedNot_exact_lyapunovStable_physical :
    connection% (¬ TMIO.realize closedFamily.meets
        (closedFamily.translate (.flow .lyapunovStable)) =
      closedFamily.den (.flow .lyapunovStable) ∩
        {p : DCParams | 0 < p.Vd ∧ 0 < p.Vref ∧ 0 < p.C}) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := centerLoop_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  have hin : centerLoop ∈ closedFamily.den (.flow .lyapunovStable) ∩
      {p : DCParams | 0 < p.Vd ∧ 0 < p.Vref ∧ 0 < p.C} :=
    ⟨hmem, by norm_num [centerLoop]⟩
  rw [← h, TMIO.mem_realize] at hin
  have hs : DCParams.Stable centerLoop := hin .stable rfl
  have := hs.2.2.2.1
  norm_num [centerLoop, DCParams.Idc0] at this

end powerlib.GFL.DCLink
