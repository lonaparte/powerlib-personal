import dependencies.Mathlib
import theorem.Attributes
import theorem.Passive.Dq

/-! # dq impedance algebra of the GFL port

Algebraic model identities of the dq impedances of the GFL port, with a Correction of the
note's load model.

Model boundary.
Single L filter, grid line and shunt load of the GFL port; conventions: IN-positive port current
(work-sync `conventions.md` §D1), dq frame rotating counter-clockwise at the constant speed `ω` with
generator `J = [[0, −1], [1, 0]]` (§D4, `Transform.J`), complex 2×2 transfer matrices evaluated at a
fixed Laplace variable `s`.

Source: work-sync `theory/T-gfl-impedance.md` §1.1, §1.3, §1.7, §2.2;
`theory/T-gfl-control.md` §2.12; `theory/T-park-transformation.md` §1.4.

Results.
* The filter open-circuit impedance `Z_oc(s) = (sL + R) I + ωL J` is the dq impedance of the
  filter branch, `Passive.SeriesRLC.dqImpedance` (`theorem/Passive/Dq.lean`, with its determinant
  and inverse); `Gid_eq`: `G_id = −V_dc Z_oc⁻¹` in closed form (T-gfl-impedance §1.1 boxed).
* PLL frame projections (T-gfl-impedance §1.3, without any property of `G_pll`):
  `Transform.hasDerivAt_park_zero` (`theorem/Transform/Park.lean`):
  `d/dθ (park θ · x)|₀ = −J x`; hence to first order `x^pll = x^sys − Δθ J x₀` and
  `x^sys = x^pll + Δθ J x₀`. With `Δθ = G_pll ΔV_q`: `pllVoltage_proj` gives
  `G_v^pll = [[1, V_q0 G], [0, 1 − V_d0 G]]`, `pllCurrent_proj` gives
  `G_i^pll = [[0, −I_q0 G], [0, I_d0 G]]` (the same form is `G_d^pll` for duty cycles).
* dq ↔ complex-vector (sequence) form (T-gfl-control §2.12): `Transform.toSeq` and its
  entries, decoupling criterion and return-difference invariance are in
  `theorem/Transform/ComplexImpedance.lean`.
* `noteLoad_ne`: the corrected shunt load (Correction below). The load admittance is the dq
  admittance of the shunt, `Passive.ParallelRLC.dqAdmittance`; the network-side impedance
  `Z_ext = (Z_line⁻¹ + Y_load)⁻¹` is `Zext` in `theorem/Grid/GridImpedance.lean`.
* `Y^IN = −Y^OUT` is `LTI.transfer_negOutput` (`theorem/LTI/Plant.lean`).

Correction (T-gfl-impedance §1.7 parallel RC load): a shunt capacitor in the dq frame obeys
`C dv/dt = i − ω C J v` (`Passive.ParallelRLC.capacitor_dq`, derived from `C dv_αβ/dt = i_αβ` with
Park), so the dq admittance of the load `G_l ∥ C` (`G_l = 1/R_l`) is `(G_l + sC) I + ωC J`
(`Passive.ParallelRLC.dqAdmittance`); the note's `Z_load = R/(1 + sRC) I` omits the cross term
`ωC J`. `noteLoad_ne`: for a load without shunt inductor (`Γ = 0`) the two differ whenever `ωC ≠ 0`.
-/

noncomputable section
namespace powerlib.GFL.Impedance
open Matrix

/-- `J` over `ℂ`. -/
def Jc : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- `G_id = −V_dc Z_oc⁻¹`, `Z_oc` the dq impedance of the filter branch. -/
def Gid (b : Passive.SeriesRLC) (ω Vdc : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -((Vdc : ℂ) • (b.dqImpedance ω s)⁻¹)

@[tmio M, powerlib_domain] theorem Gid_eq {b : Passive.SeriesRLC} {ω Vdc : ℝ} {s : ℂ}
    (hS : b.S = 0) (h : (b.R + b.L * s) ^ 2 + (ω * b.L : ℂ) ^ 2 ≠ 0) :
    Gid b ω Vdc s =
      -((Vdc : ℂ) / ((b.R + b.L * s) ^ 2 + (ω * b.L) ^ 2)) •
        !![b.R + b.L * s, ω * b.L; -(ω * b.L), b.R + b.L * s] := by
  rw [Gid, Passive.SeriesRLC.dqImpedance_inv_of_noCap hS h, smul_smul, ← neg_smul, div_eq_mul_inv]

/-! ## PLL frame projections -/

/-- Voltage projection system → PLL frame: `ΔV^pll = ΔV − (G ΔV_q) J V₀ = G_v^pll ΔV`. -/
@[tmio T, powerlib_foundation] theorem pllVoltage_proj (V0 dV : Fin 2 → ℂ) (G : ℂ) :
    dV - (G * dV 1) • (Jc *ᵥ V0) = !![1, V0 1 * G; 0, 1 - V0 0 * G] *ᵥ dV := by
  ext k
  fin_cases k <;> simp [Jc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Current (and duty) projection: `ΔI^sys − ΔI^pll = (G ΔV_q) J I₀ = G_i^pll ΔV`. -/
@[tmio T, powerlib_foundation] theorem pllCurrent_proj (I0 dV : Fin 2 → ℂ) (G : ℂ) :
    (G * dV 1) • (Jc *ᵥ I0) = !![0, -(I0 1 * G); 0, I0 0 * G] *ᵥ dV := by
  ext k
  fin_cases k <;> simp [Jc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- PLL-aligned operating point (`V_q0 = 0`): `G_v^pll = diag(1, 1 − V_d0 G)`. -/
@[tmio T, powerlib_foundation] theorem pllVoltage_aligned (Vd0 G : ℂ) :
    (!![1, (0 : ℂ) * G; 0, 1 - Vd0 * G] : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![1, 1 - Vd0 * G] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ## Shunt capacitor in the dq frame (Correction) -/

/-- The note's load admittance `(G_l + sC) I` (cross term missing). -/
def YloadNote (load : Passive.ParallelRLC) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  load.admittance s • (1 : Matrix (Fin 2) (Fin 2) ℂ)

@[tmio M, powerlib_domain] theorem noteLoad_ne {load : Passive.ParallelRLC} {ω : ℝ}
    (hΓ : load.Γ = 0) (h : ω * load.C ≠ 0) (s : ℂ) : YloadNote load s ≠ load.dqAdmittance ω s := by
  intro heq
  have := congrFun (congrFun heq 1) 0
  simp [YloadNote, Passive.ParallelRLC.dqAdmittance_of_noInd hΓ] at this
  rcases this with h1 | h1 <;> simp [h1] at h

end powerlib.GFL.Impedance
