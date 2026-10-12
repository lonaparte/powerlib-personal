import theorem.Attributes
import dependencies.Mathlib

/-! # Filter power balance and the rectifier right-half-plane zero (foundation)

Setting: one series R–L filter between the PCC and the converter bridge, dq frame rotating at
`ω`, IN-positive current (work-sync `conventions.md` §D1), per-unit (multiply every power by
`3/2` for SI amplitude-invariant quantities; `pcc_eq_bridge_add_losses_si`):
`L di_d/dt = v_d − v^conv_d − R i_d + ω L i_q`, `L di_q/dt = v_q − v^conv_q − R i_q − ω L i_d`.
`P_PCC = v_d i_d + v_q i_q`, `P_bridge = v^conv_d i_d + v^conv_q i_q`.

* `pcc_eq_bridge_add_losses`: along any differentiable current trajectory satisfying the KVL,
  `P_PCC = P_bridge + R |i|² + L d(|i|²/2)/dt` exactly (the rotation terms
  `ω L (i_q i_d − i_d i_q)` cancel). T-vsc-dc-voltage-control §1.1.1 boxed.
* `bridgePower_expansion`: with `v_q = 0`, `I_q0 = 0`, a constant operating current `I_d0` and
  a stiff `v_d = V_d0`, the bridge power is `P_b = V_d0 i_d − R |i|² − L (i_d i_d' + i_q i_q')`;
  its perturbation is exactly
  `ΔP_b = (V_d0 − 2 R I_d0) Δi_d − L I_d0 Δi_d' − [R(Δi_d² + Δi_q²) + L(Δi_d Δi_d' + Δi_q Δi_q')]`,
  so the linear part has the transfer `ΔP_b/ΔI_d = (V_d0 − 2 R I_d0) − s L I_d0`.
* `bridgeZero_eq`, `bridgeZero_pos_iff`: with `R = 0` (the note's §1.5 setting) the transfer is
  `V_d0 − s L I_d0`, its zero is `s_z = V_d0/(L I_d0)`, and for `V_d0 > 0`, `L > 0` it lies in
  the open right half-plane iff `I_d0 > 0` (rectifier mode; inverter mode `I_d0 < 0` gives a
  left-half-plane zero). `bridgeZero_with_R`: with `R ≠ 0` the zero moves to
  `(V_d0 − 2 R I_d0)/(L I_d0)` (the note neglects `R`).

These are identities (foundation), not stability statements about a closed loop.

Source: work-sync `theory/T-vsc-dc-voltage-control.md` §1.1.1, §1.5, §2.5.
-/

noncomputable section
namespace powerlib.DCLink

/-- Exact power balance of the dq R–L filter along a trajectory. -/
@[powerlib_foundation] theorem pcc_eq_bridge_add_losses {L R ω : ℝ}
    {id iq : ℝ → ℝ} {vd vq vcd vcq id' iq' t : ℝ}
    (hd : HasDerivAt id id' t) (hq : HasDerivAt iq iq' t)
    (kvl_d : L * id' = vd - vcd - R * id t + ω * L * iq t)
    (kvl_q : L * iq' = vq - vcq - R * iq t - ω * L * id t) :
    HasDerivAt (fun s => (id s ^ 2 + iq s ^ 2) / 2) (id t * id' + iq t * iq') t ∧
      vd * id t + vq * iq t =
        (vcd * id t + vcq * iq t) + R * (id t ^ 2 + iq t ^ 2) +
          L * (id t * id' + iq t * iq') := by
  refine ⟨?_, ?_⟩
  · have h := ((hd.pow 2).add (hq.pow 2)).div_const 2
    convert h using 1
    push_cast
    ring
  · linear_combination (-(id t)) * kvl_d - iq t * kvl_q

/-- SI form with the amplitude-invariant `3/2` factor. -/
@[powerlib_foundation] theorem pcc_eq_bridge_add_losses_si {L R ω : ℝ}
    {id iq : ℝ → ℝ} {vd vq vcd vcq id' iq' t : ℝ}
    (hd : HasDerivAt id id' t) (hq : HasDerivAt iq iq' t)
    (kvl_d : L * id' = vd - vcd - R * id t + ω * L * iq t)
    (kvl_q : L * iq' = vq - vcq - R * iq t - ω * L * id t) :
    3 / 2 * (vd * id t + vq * iq t) =
      3 / 2 * (vcd * id t + vcq * iq t) + 3 / 2 * R * (id t ^ 2 + iq t ^ 2) +
        3 / 2 * L * (id t * id' + iq t * iq') := by
  have h := (pcc_eq_bridge_add_losses (ω := ω) hd hq kvl_d kvl_q).2
  linear_combination 3 / 2 * h

/-- Bridge power as a function of current and current derivative (`v_q = 0`, stiff `v_d`). -/
def bridgePower (Vd0 R L id iq did diq : ℝ) : ℝ :=
  Vd0 * id - R * (id ^ 2 + iq ^ 2) - L * (id * did + iq * diq)

/-- `P_bridge` from the KVL with `v_q = 0`: `v^conv · i = v_d i_d − R|i|² − L i · i'`. -/
@[powerlib_foundation] theorem bridgePower_of_kvl {L R ω Vd0 id iq did diq vcd vcq : ℝ}
    (kvl_d : L * did = Vd0 - vcd - R * id + ω * L * iq)
    (kvl_q : L * diq = 0 - vcq - R * iq - ω * L * id) :
    vcd * id + vcq * iq = bridgePower Vd0 R L id iq did diq := by
  simp only [bridgePower]
  linear_combination id * kvl_d + iq * kvl_q

/-- Exact perturbation expansion around `(I_d0, 0)` with zero operating derivatives. -/
@[powerlib_foundation] theorem bridgePower_expansion (Vd0 R L Id0 δd δq δd' δq' : ℝ) :
    bridgePower Vd0 R L (Id0 + δd) δq δd' δq' - bridgePower Vd0 R L Id0 0 0 0 =
      ((Vd0 - 2 * R * Id0) * δd - L * Id0 * δd') -
        (R * (δd ^ 2 + δq ^ 2) + L * (δd * δd' + δq * δq')) := by
  simp only [bridgePower]
  ring

/-- Linear part `ΔP_b/ΔI_d = (V_d0 − 2 R I_d0) − s L I_d0`, `R = 0`: `V_d0 − s L I_d0`. -/
def bridgeTransfer (Vd0 R L Id0 : ℝ) (s : ℂ) : ℂ := (Vd0 - 2 * R * Id0) - s * L * Id0

@[powerlib_foundation] theorem bridgeTransfer_R_zero (Vd0 L Id0 : ℝ) (s : ℂ) :
    bridgeTransfer Vd0 0 L Id0 s = Vd0 - s * L * Id0 := by
  simp [bridgeTransfer]

/-- The zero of `V_d0 − s L I_d0` is `s_z = V_d0/(L I_d0)`. -/
@[powerlib_foundation] theorem bridgeZero_eq {Vd0 L Id0 : ℝ} (hL : L ≠ 0) (hI : Id0 ≠ 0)
    (s : ℂ) : bridgeTransfer Vd0 0 L Id0 s = 0 ↔ s = ((Vd0 / (L * Id0) : ℝ) : ℂ) := by
  have hLI : ((L : ℂ) * Id0) ≠ 0 := by exact_mod_cast mul_ne_zero hL hI
  rw [bridgeTransfer_R_zero]
  push_cast
  constructor
  · intro h
    rw [eq_div_iff hLI]
    linear_combination -h
  · intro h
    rw [h, mul_assoc, div_mul_cancel₀ _ hLI, sub_self]

/-- With `R ≠ 0` the zero is `(V_d0 − 2 R I_d0)/(L I_d0)`. -/
@[powerlib_foundation] theorem bridgeZero_with_R {Vd0 R L Id0 : ℝ} (hL : L ≠ 0) (hI : Id0 ≠ 0)
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
@[powerlib_foundation] theorem bridgeZero_pos_iff {Vd0 L Id0 : ℝ} (hV : 0 < Vd0) (hL : 0 < L) :
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

end powerlib.DCLink
