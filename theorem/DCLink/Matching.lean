import theorem.Dynamics.Transport
import theorem.CurrentControl.SISO
import Mathlib.Analysis.Real.Pi.Bounds

/-! # DC-voltage based grid forming: DC energy balance, matching control, DC droop

Directions (work-sync T-dc-voltage-gfm §1.0): `v` is the DC-link voltage, `i_dc` the source
current injected into the capacitor (IN-positive), `i_x` the current the converter draws from
the capacitor to the AC side (positive when exporting), `G` the DC-link conductance; AC power
export-positive (`v i_x = P_ac,export`, lossless converter). Continuous time, per-unit or SI.

Foundation.
* `dcEnergy_balance`: along any solution of `C v' = i_dc − i_x − G v` the capacitor energy
  `H = C v²/2` satisfies `H' = P_src − P_ac − G v²` (`P_src = v i_dc`, `P_ac = v i_x`) (§1.1).
* `droop_transfer`, `droop_dcGain`: DC-voltage droop `ω − ω_s = K (v − v*)` on the linearized
  DC node `C Δv' = −(3/2) ΔP_export / v* − G Δv` has `Δω/ΔP_export = −(3/2) K /(v* (C s + G))`;
  its DC gain `−(3/2) K /(G v*)` needs `G ≠ 0` (§1.4). The small-signal model is
  exponentially stable iff `G > 0` (`droop_exponentiallyStable_iff`, `C > 0`).

Domain: matching control (§1.2, Arghir–Jouini–Dörfler).
* Model boundary: state order `(θ, v)` (converter modulation angle, DC voltage); matching law
  `θ' = η v`; DC node `C v' = i_dc − i_x(θ, v) − G v` with an **arbitrary** load-current law
  `i_x` (the AC network, filter and grid are hidden in `i_x`; no current limits, no PLL, no
  inner loops); `η, C ≠ 0`. Swing model: state `(θ, ω)`,
  `θ' = ω`, `M ω' = τ − P_e(θ, ω) − D ω`.
* `matching_eq_swing`: with `M = C/η²`, `D = G/η²`, `τ = i_dc/η`,
  `P_e(θ, ω) = i_x(θ, ω/η)/η`, the swing field is exactly the matching field in the
  coordinates `(θ, ω) = (θ, η v)`.
* `matching_trajectory_iff`: solutions correspond one to one (`φ ↦ (θ, η v)`), on every time
  interval; `matching_equilibrium_iff`, `matching_locallyExponentiallyStable_iff`,
  `matching_unstable_iff`: equilibria, local exponential stability and instability transfer
  both ways (via `Dynamics.Transport`).

Correction (T-dc-voltage-gfm §2.2 ROCOF). Exactly, `ω' = η v' = η (i_dc − i_x − G v)/C`; a
step `ΔP` of exported power from equilibrium gives the initial ROCOF `−η ΔP/(C v*)`
`= −ω_s ΔP/(C v*²)` (`matching_rocof`). With the note's data (`C = 20 mF`, `v* = 1500 V`,
`ω_s = 100π`, `ΔP = 100 kW`) this is `2000π/9 ≈ 698 rad/s²` (`rocof_note_data`), not
`∼10⁴ rad/s²`. The note's own formula `ΔP ω_s²/(C v*³)` evaluates to `400π²/27 ≈ 146`
(`note_formula_value`) but is dimensionally inconsistent (one factor `η = ω_s/v*` too many).
The ViSynC equivalence of §1.3 is not derived in the note and is not formalized.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.0–§1.2, §1.4, §2.2;
`theory/T-vsc-dc-voltage-control.md` §1.7.
-/

noncomputable section
namespace powerlib.DCLink
open Matrix Filter
open scoped Topology
open powerlib.Dynamics

/-! ## DC energy balance -/

/-- `d/dt (C v²/2) = v i_dc − v i_x − G v²` along `C v' = i_dc − i_x − G v`. -/
@[powerlib_foundation] theorem dcEnergy_balance {C G : ℝ} {v idc ix : ℝ → ℝ} {t v' : ℝ}
    (hv : HasDerivAt v v' t) (hnode : C * v' = idc t - ix t - G * v t) :
    HasDerivAt (fun s => C * v s ^ 2 / 2)
      (v t * idc t - v t * ix t - G * v t ^ 2) t := by
  have h := ((hv.pow 2).const_mul C).div_const 2
  convert h using 1
  push_cast
  linear_combination (-(v t)) * hnode

/-! ## Matching control ↔ swing equation -/

/-- Matching-control DC-link field, state `(θ, v)`. -/
def matchingField (C G η idc : ℝ) (ix : ℝ → ℝ → ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![η * x 1, (idc - ix (x 0) (x 1) - G * x 1) / C]

/-- Swing field, state `(θ, ω)`: `M ω' = τ − P_e(θ, ω) − D ω`. -/
def swingField (M D τ : ℝ) (Pe : ℝ → ℝ → ℝ) (y : State 2) : State 2 :=
  WithLp.toLp 2 ![y 1, (τ - Pe (y 0) (y 1) - D * y 1) / M]

/-- Scaling matrix `(θ, v) ↦ (θ, η v)`. -/
def scaleMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, η]

@[powerlib_foundation] theorem scaleMatrix_isUnit {η : ℝ} (hη : η ≠ 0) :
    IsUnit (scaleMatrix η) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simpa [scaleMatrix, Matrix.det_fin_two] using hη

@[powerlib_foundation] private lemma scaleMatrix_inv {η : ℝ} (hη : η ≠ 0) :
    (scaleMatrix η)⁻¹ = !![1, 0; 0, η⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scaleMatrix, hη]

/-- The coordinate change `(θ, v) ↦ (θ, η v)`. -/
def scaleCoord {η : ℝ} (hη : η ≠ 0) : State 2 ≃L[ℝ] State 2 :=
  matrixCoord (scaleMatrix η) (scaleMatrix_isUnit hη)

@[simp, powerlib_foundation] theorem scaleCoord_apply {η : ℝ} (hη : η ≠ 0) (x : State 2) :
    scaleCoord hη x = WithLp.toLp 2 ![x 0, η * x 1] := by
  ext i
  fin_cases i <;>
    simp [scaleCoord, scaleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp, powerlib_foundation] theorem scaleCoord_symm_apply {η : ℝ} (hη : η ≠ 0) (y : State 2) :
    (scaleCoord hη).symm y = WithLp.toLp 2 ![y 0, y 1 / η] := by
  ext i
  fin_cases i <;>
    simp [scaleCoord, scaleMatrix_inv hη, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      div_eq_inv_mul]

/-- Swing parameters of the matching law: `M = C/η²`, `D = G/η²`, `τ = i_dc/η`,
`P_e(θ, ω) = i_x(θ, ω/η)/η`. -/
def matchedSwing (C G η idc : ℝ) (ix : ℝ → ℝ → ℝ) : State 2 → State 2 :=
  swingField (C / η ^ 2) (G / η ^ 2) (idc / η) (fun θ ω => ix θ (ω / η) / η)

/-- The swing field is the matching field in the coordinates `(θ, η v)`. -/
@[powerlib_foundation] theorem matching_eq_swing {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) :
    transportField (scaleCoord hη) 0 (matchingField C G η idc ix) =
      matchedSwing C G η idc ix := by
  funext y
  ext i
  fin_cases i
  · simp [transportField, matchingField, matchedSwing, swingField]
    field_simp
  · simp [transportField, matchingField, matchedSwing, swingField]
    field_simp

@[powerlib_foundation] private lemma affineCoord_scale {η : ℝ} (hη : η ≠ 0) (x : State 2) :
    affineCoord (scaleCoord hη) 0 x = scaleCoord hη x := by
  simp [affineCoord]

/-- Solutions correspond one to one: `φ = (θ, v)` solves the matching model on `[a, b]` iff
`(θ, η v)` solves the matched swing model. -/
@[powerlib_domain] theorem matching_trajectory_iff {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) (φ : ℝ → State 2) (a b : ℝ) :
    Dynamics.IsTrajectoryOn φ (matchingField C G η idc ix) a b ↔
      Dynamics.IsTrajectoryOn (fun t => scaleCoord hη (φ t)) (matchedSwing C G η idc ix) a b := by
  constructor
  · intro h
    have h' := isTrajectoryOn_transport (scaleCoord hη) 0 h
    rw [matching_eq_swing hC hη] at h'
    simpa [affineCoord_scale] using h'
  · intro h
    have h1 : Dynamics.IsTrajectoryOn (fun t => affineCoord (scaleCoord hη) 0 (φ t))
        (transportField (scaleCoord hη) 0 (matchingField C G η idc ix)) a b := by
      rw [matching_eq_swing hC hη]
      simp only [affineCoord_scale]
      exact h
    have h2 := isTrajectoryOn_transport (scaleCoord hη).symm (-((scaleCoord hη).symm 0)) h1
    rw [transportField_symm_transportField] at h2
    simpa only [affineCoord_symm_affineCoord] using h2

/-- Equilibria correspond. -/
@[powerlib_domain] theorem matching_equilibrium_iff {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) (x : State 2) :
    matchedSwing C G η idc ix (scaleCoord hη x) = 0 ↔ matchingField C G η idc ix x = 0 := by
  rw [← matching_eq_swing hC hη, ← affineCoord_scale hη]
  exact transportField_affineCoord_eq_zero_iff _ _ _ _

/-- Local exponential stability transfers between the matching and swing models. -/
@[powerlib_domain] theorem matching_locallyExponentiallyStable_iff {C G η idc : ℝ}
    (hC : C ≠ 0) (hη : η ≠ 0) (ix : ℝ → ℝ → ℝ) (x : State 2) :
    Dynamics.LocallyExponentiallyStable (matchedSwing C G η idc ix) (scaleCoord hη x) ↔
      Dynamics.LocallyExponentiallyStable (matchingField C G η idc ix) x := by
  rw [← matching_eq_swing hC hη, ← affineCoord_scale hη]
  exact locallyExponentiallyStable_transport_iff _ _

/-- Instability transfers between the matching and swing models. -/
@[powerlib_domain] theorem matching_unstable_iff {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) (x : State 2) :
    Dynamics.Unstable (matchedSwing C G η idc ix) (scaleCoord hη x) ↔
      Dynamics.Unstable (matchingField C G η idc ix) x := by
  rw [← matching_eq_swing hC hη, ← affineCoord_scale hη]
  exact unstable_transport_iff _ _

/-! ## ROCOF of the matching law (Correction) -/

/-- Exact frequency derivative of the matching law: `ω' = η v' = η (i_dc − i_x − G v)/C`. -/
@[powerlib_domain] theorem matching_frequency_derivative {C G η idc : ℝ} (ix : ℝ → ℝ → ℝ)
    (x : State 2) :
    η * (matchingField C G η idc ix x) 1 = η * ((idc - ix (x 0) (x 1) - G * x 1) / C) := by
  simp [matchingField]

/-- Initial ROCOF after a step `ΔP` in exported power from equilibrium (`i_x = i_x0 + ΔP/v`):
`−η ΔP/(C v)`. -/
@[powerlib_foundation] theorem matching_rocof {C G η idc ix0 v ΔP : ℝ} (hC : C ≠ 0)
    (hv : v ≠ 0) (heq : idc - ix0 - G * v = 0) :
    η * ((idc - (ix0 + ΔP / v) - G * v) / C) = -(η * ΔP / (C * v)) := by
  have : idc - (ix0 + ΔP / v) - G * v = -(ΔP / v) := by linear_combination heq
  rw [this]
  field_simp

/-- With `η = ω_s/v*`: `|ROCOF| = ω_s ΔP/(C v*²)`. -/
@[powerlib_foundation] theorem matching_rocof_omega {C ωs v ΔP : ℝ} (hC : C ≠ 0) (hv : v ≠ 0) :
    ωs / v * ΔP / (C * v) = ωs * ΔP / (C * v ^ 2) := by
  field_simp

/-- The note's data: `ω_s ΔP/(C v*²) = 2000π/9 ∈ (698, 699)` rad/s². -/
@[powerlib_foundation] theorem rocof_note_data :
    (100 * Real.pi) * 100000 / ((20 / 1000) * 1500 ^ 2) = 2000 * Real.pi / 9 ∧
      698 < 2000 * Real.pi / 9 ∧ 2000 * Real.pi / 9 < 699 := by
  refine ⟨by ring, ?_, ?_⟩
  · have := Real.pi_gt_d6
    linarith
  · have := Real.pi_lt_d6
    linarith

/-- The note's formula `ΔP ω_s²/(C v*³)` with the same data: `400π²/27 ∈ (146, 147)`. -/
@[powerlib_foundation] theorem note_formula_value :
    100000 * (100 * Real.pi) ^ 2 / ((20 / 1000) * 1500 ^ 3) = 400 * Real.pi ^ 2 / 27 ∧
      146 < 400 * Real.pi ^ 2 / 27 ∧ 400 * Real.pi ^ 2 / 27 < 147 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  refine ⟨by ring, ?_, ?_⟩ <;> nlinarith

/-! ## DC-voltage droop small-signal model -/

/-- Linearized DC node with DC-voltage droop: state `Δv`, input `ΔP_export`, output `Δω`. -/
def droopModel (C G K vref : ℝ) : LTI.Model (Fin 1) (Fin 1) :=
  ⟨!![-G / C], !![-(3 / 2) / (C * vref)], !![K], !![0]⟩

@[powerlib_foundation] theorem droop_transfer {C G K vref : ℝ} (hC : C ≠ 0) (hv : vref ≠ 0)
    {s : ℂ} (hs : (C : ℂ) * s + G ≠ 0) :
    LTI.transfer (droopModel C G K vref) s 0 0 = -(3 / 2) * K / (vref * (C * s + G)) := by
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hv' : (vref : ℂ) ≠ 0 := by exact_mod_cast hv
  have hpole : s - ((-G / C : ℝ) : ℂ) ≠ 0 := by
    intro h
    apply hs
    push_cast at h
    field_simp at h
    linear_combination h
  rw [droopModel, CurrentControl.transfer_fin_one _ _ _ _ hpole]
  have e : s - ((-G / C : ℝ) : ℂ) = (C * s + G) / C := by
    push_cast
    field_simp
    ring
  rw [e]
  push_cast
  field_simp
  ring

/-- DC gain `Δω/ΔP_export (0) = −(3/2) K/(G v*)` (needs `G ≠ 0`). -/
@[powerlib_foundation] theorem droop_dcGain {C G K vref : ℝ} (hC : C ≠ 0) (hv : vref ≠ 0)
    (hG : G ≠ 0) :
    LTI.transfer (droopModel C G K vref) 0 0 0 = -(3 / 2) * K / (G * vref) := by
  have hG' : (G : ℂ) ≠ 0 := by exact_mod_cast hG
  rw [droop_transfer hC hv (by simpa using hG')]
  simp only [mul_zero, zero_add]
  ring

/-- The droop small-signal DC node is exponentially stable iff `G > 0` (`C > 0`). -/
@[powerlib_domain] theorem droop_exponentiallyStable_iff {C G K vref : ℝ} (hC : 0 < C) :
    LTI.ExponentiallyStable (droopModel C G K vref).autonomous ↔ 0 < G := by
  rw [LTI.exponentiallyStable_iff_isHurwitz, Criteria.isHurwitz_iff_characteristic_roots]
  have hdet : ∀ s : ℂ, (LTI.characteristicMatrix (droopModel C G K vref).autonomous.A s).det =
      s - ((-G / C : ℝ) : ℂ) := by
    intro s
    simp [LTI.characteristicMatrix, droopModel, LTI.Model.autonomous, Matrix.det_unique]
  simp only [hdet, sub_eq_zero]
  constructor
  · intro h
    have := h _ rfl
    rw [Complex.ofReal_re, neg_div, neg_lt_zero] at this
    exact (div_pos_iff_of_pos_right hC).mp this
  · rintro hG s rfl
    rw [Complex.ofReal_re, neg_div, neg_lt_zero]
    exact div_pos hG hC

end powerlib.DCLink
