import theorem.Attributes
import dependencies.Mathlib
import theorem.Passive.Dq
import theorem.Dynamics.State

/-! # Filter power balance, the DC node and the rectifier right-half-plane zero

These are domain model identities, not stability statements about a closed loop.

Model boundary.
One series R–L filter between the PCC and the converter bridge, dq frame rotating at
`ω`, IN-positive current (work-sync `conventions.md` §D1), per-unit (multiply every power by
`3/2` for SI amplitude-invariant quantities):
`L di_d/dt = v_d − v^conv_d − R i_d + ω L i_q`, `L di_q/dt = v_q − v^conv_q − R i_q − ω L i_d`.
`P_PCC = v_d i_d + v_q i_q`, `P_bridge = v^conv_d i_d + v^conv_q i_q`.
DC node (lossless capacitor `C`, no leakage): the source current `i` is injected into the node and
the converter absorbs the power `P` at the DC voltage `V`, `C dV/dt = i + P/V`.

Source: work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.1.1, §1.5, §2.5.

Results.
* Along any differentiable current trajectory satisfying the KVL,
  `P_PCC = P_bridge + R |i|² + L d(|i|²/2)/dt` exactly (the rotation terms
  `ω L (i_q i_d − i_d i_q)` cancel, T-vsc-dc-voltage-control §1.1.1 boxed): this is the filter
  branch's own law `Passive.SeriesRLC.dq_power_balance` (its SI form is the same identity times
  `3/2`). With `v_q = 0` the instantaneous form `Passive.SeriesRLC.dq_power_identity` gives the
  bridge power `v^conv·i = bridgePower V_d0 R L i_d i_q i_d' i_q'` below.
* `bridgePower_expansion`: with `v_q = 0`, `I_q0 = 0`, a constant operating current `I_d0` and
  a stiff `v_d = V_d0`, the bridge power is `P_b = V_d0 i_d − R |i|² − L (i_d i_d' + i_q i_q')`;
  its perturbation is exactly
  `ΔP_b = (V_d0 − 2 R I_d0) Δi_d − L I_d0 Δi_d' − [R(Δi_d² + Δi_q²) + L(Δi_d Δi_d' + Δi_q Δi_q')]`,
  so the linear part has the transfer `ΔP_b/ΔI_d = (V_d0 − 2 R I_d0) − s L I_d0`.
* `bridgeZero_eq`, `bridgeZero_pos_iff`: the zero of the transfer is
  `(V_d0 − 2 R I_d0)/(L I_d0)`; with `R = 0` (the note's §1.5 setting, which neglects `R`) the
  transfer is `V_d0 − s L I_d0` (`bridgeTransfer_R_zero`), its zero is `s_z = V_d0/(L I_d0)`, and
  for `V_d0 > 0`, `L > 0` it lies in the open right half-plane iff `I_d0 > 0` (rectifier mode;
  inverter mode `I_d0 < 0` gives a left-half-plane zero).
* The DC node: `nodeRate C i P V = (i + P/V)/C`, the law of every DC-link model of
  `GFL.DCLink` (`openField`, `DCParams.closedField`, `CascadeParams.field`, the `basin-guard`
  carrier); it is `C^m` along `C^m` data where `V ≠ 0` (`contDiffOn_nodeRate`) with the derivative
  `(i' + P'/V − P V'/V²)/C` (`hasFDerivAt_nodeRate`). `posDC k` is the open set where the DC
  voltage, coordinate `k` of the state, is positive (`isOpen_posDC`).
-/

noncomputable section
namespace powerlib.GFL.DCLink

/-- Bridge power as a function of current and current derivative (`v_q = 0`, stiff `v_d`). -/
def bridgePower (Vd0 R L id iq did diq : ℝ) : ℝ :=
  Vd0 * id - R * (id ^ 2 + iq ^ 2) - L * (id * did + iq * diq)

/-- Exact perturbation expansion around `(I_d0, 0)` with zero operating derivatives. -/
@[tmio M, powerlib_domain] theorem bridgePower_expansion (Vd0 R L Id0 δd δq δd' δq' : ℝ) :
    bridgePower Vd0 R L (Id0 + δd) δq δd' δq' - bridgePower Vd0 R L Id0 0 0 0 =
      ((Vd0 - 2 * R * Id0) * δd - L * Id0 * δd') -
        (R * (δd ^ 2 + δq ^ 2) + L * (δd * δd' + δq * δq')) := by
  simp only [bridgePower]
  ring

/-- Linear part `ΔP_b/ΔI_d = (V_d0 − 2 R I_d0) − s L I_d0`, `R = 0`: `V_d0 − s L I_d0`. -/
def bridgeTransfer (Vd0 R L Id0 : ℝ) (s : ℂ) : ℂ := (Vd0 - 2 * R * Id0) - s * L * Id0

@[tmio M, powerlib_domain] theorem bridgeTransfer_R_zero (Vd0 L Id0 : ℝ) (s : ℂ) :
    bridgeTransfer Vd0 0 L Id0 s = Vd0 - s * L * Id0 := by
  simp [bridgeTransfer]

/-- The zero of the bridge-power transfer is `(V_d0 − 2 R I_d0)/(L I_d0)`; with `R = 0` it is
`s_z = V_d0/(L I_d0)`. -/
@[tmio M, powerlib_domain] theorem bridgeZero_eq {Vd0 R L Id0 : ℝ} (hL : L ≠ 0) (hI : Id0 ≠ 0)
    (s : ℂ) :
    bridgeTransfer Vd0 R L Id0 s = 0 ↔ s = (((Vd0 - 2 * R * Id0) / (L * Id0) : ℝ) : ℂ) := by
  have hLI : ((L : ℂ) * Id0) ≠ 0 := by exact_mod_cast mul_ne_zero hL hI
  simp only [bridgeTransfer]
  push_cast
  constructor
  · intro h
    rw [eq_div_iff hLI]
    linear_combination -h
  · intro h
    rw [h, show ((Vd0 : ℂ) - 2 * R * Id0) / (L * Id0) * L * Id0 =
      ((Vd0 : ℂ) - 2 * R * Id0) / (L * Id0) * (L * Id0) by ring, div_mul_cancel₀ _ hLI,
      sub_self]

/-- Rectifier (`I_d0 > 0`) ⇔ the bridge-power zero is in the right half-plane (`V_d0, L > 0`). -/
@[tmio T, powerlib_foundation] theorem bridgeZero_pos_iff {Vd0 L Id0 : ℝ} (hV : 0 < Vd0) (hL : 0 < L) :
    0 < Vd0 / (L * Id0) ↔ 0 < Id0 := by
  constructor
  · intro h
    have h2 : 0 < L * Id0 := by
      by_contra hn0
      have hn := not_lt.mp hn0
      have : Vd0 / (L * Id0) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hV.le hn
      linarith
    exact pos_of_mul_pos_right h2 hL.le
  · intro h
    exact div_pos hV (mul_pos hL h)

/-! ## The DC node -/

/-- The DC-node law `dV/dt = (i + P/V)/C`: the DC-link capacitor `C` is fed by the source current
`i` and discharged by the converter, which absorbs the power `P` at the DC voltage `V`
(`C V dV/dt = V i + P`). -/
def nodeRate (C i P V : ℝ) : ℝ := (i + P / V) / C

/-- The open set `V_dc > 0` of states whose DC voltage is the coordinate `k`. -/
def posDC {n : ℕ} (k : Fin n) : Set (Dynamics.State n) := {x | 0 < x k}

@[tmio M, powerlib_domain] theorem isOpen_posDC {n : ℕ} (k : Fin n) : IsOpen (posDC k) :=
  isOpen_lt continuous_const ((EuclideanSpace.proj k).continuous)

section NodeLaws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ℝ) {i P V : E → ℝ}

/-- The DC-node rate along `C^m` data `i, P, V` is `C^m` where the DC voltage is nonzero. -/
@[tmio M, powerlib_domain] theorem contDiffOn_nodeRate {s : Set E} {m : WithTop ℕ∞}
    (hi : ContDiffOn ℝ m i s) (hP : ContDiffOn ℝ m P s) (hV : ContDiffOn ℝ m V s)
    (h0 : ∀ x ∈ s, V x ≠ 0) : ContDiffOn ℝ m (fun x => nodeRate C (i x) (P x) (V x)) s :=
  (hi.add (hP.div hV h0)).div_const C

/-- The derivative of the DC-node rate at a nonzero DC voltage: `(i' + P'/V − P V'/V²)/C`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_nodeRate {x : E} {i' P' V' : E →L[ℝ] ℝ}
    (hi : HasFDerivAt i i' x) (hP : HasFDerivAt P P' x) (hV : HasFDerivAt V V' x)
    (h0 : V x ≠ 0) :
    HasFDerivAt (fun y => nodeRate C (i y) (P y) (V y))
      (C⁻¹ • (i' + (V x)⁻¹ • P' - (P x / V x ^ 2) • V')) x := by
  have h := ((hi.add (hP.mul ((hasFDerivAt_inv h0).comp x hV))).mul_const C⁻¹)
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · ext v
    simp
    field_simp
    ring
  · simp [nodeRate, div_eq_mul_inv]

end NodeLaws

end powerlib.GFL.DCLink
