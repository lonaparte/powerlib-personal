import theorem.Transform.Park

/-! # dq impedance algebra of the GFL port (foundation, with Correction)

Conventions: IN-positive port current (work-sync `conventions.md` §D1), dq frame rotating
counter-clockwise at the constant speed `ω` with generator `J = [[0, −1], [1, 0]]` (§D4,
`Transform.J`), complex 2×2 transfer matrices evaluated at a fixed Laplace variable `s`.

* `Zoc_eq`, `det_Zoc`, `Zoc_inv`: filter open-circuit impedance
  `Z_oc(s) = (sL + R) I + ωL J = [[sL + R, −ωL], [ωL, sL + R]]`, its determinant
  `(sL + R)² + (ωL)²`, and its inverse `[[sL + R, ωL], [−ωL, sL + R]]/det`;
  `Gid_eq`: `G_id = −V_dc Z_oc⁻¹` in closed form (T-gfl-impedance §1.1 boxed).
* PLL frame projections (T-gfl-impedance §1.3, without any property of `G_pll`):
  `hasDerivAt_park_zero`: `d/dθ (park θ · x)|₀ = −J x`; hence to first order
  `x^pll = x^sys − Δθ J x₀` and `x^sys = x^pll + Δθ J x₀`. With `Δθ = G_pll ΔV_q`:
  `pllVoltage_proj` gives `G_v^pll = [[1, V_q0 G], [0, 1 − V_d0 G]]`, `pllCurrent_proj` gives
  `G_i^pll = [[0, −I_q0 G], [0, I_d0 G]]` (the same form is `G_d^pll` for duty cycles).
* dq ↔ complex-vector (sequence) form (T-gfl-control §2.12): `toSeq Y = A Y A⁻¹` with
  `A = [[1, j], [1, −j]]`; `toSeq_eq` gives its entries
  `Y± = ((Y_dd + Y_qq) ± j(Y_qd − Y_dq))/2` on the diagonal and the mirror couplings off it;
  `toSeq_offDiag_eq_zero_iff`: no ± coupling iff `Y_dd = Y_qq ∧ Y_dq = −Y_qd`;
  `returnDifference_toSeq`: `det(I + Z Y)` (hence the generalized Nyquist test) is the same in
  both forms.
* Correction (T-gfl-impedance §1.7 parallel RC load): a shunt capacitor in the dq frame obeys
  `C dv/dt = i − ω C J v` (`capacitor_dq`, derived from `C dv_αβ/dt = i_αβ` with Park), so its
  dq admittance is `sC I + ωC J`; the note's `Z_load = R/(1 + sRC) I` omits the cross term
  `ωC J`. `noteLoad_ne`: the two differ whenever `ωC ≠ 0`. With the corrected load,
  `Zext_eq`: `Z_ext = (Z_line⁻¹ + Y_load)⁻¹ = Z_line (I + Y_load Z_line)⁻¹`.
* `Y^IN = −Y^OUT` is `LTI.transfer_negOutput` (`theorem/LTI/Plant.lean`).

Source: work-sync `theory/T-gfl-impedance.md` §1.1, §1.3, §1.7, §2.2;
`theory/T-gfl-control.md` §2.12; `theory/T-park-transformation.md` §1.4.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix

/-- `J` over `ℂ`. -/
def Jc : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- `Z_oc(s) = (sL + R) I + ωL J`. -/
def Zoc (L R ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (s * L + R) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ((ω * L : ℝ) : ℂ) • Jc

@[powerlib_foundation] theorem Zoc_eq (L R ω : ℝ) (s : ℂ) :
    Zoc L R ω s = !![s * L + R, -(ω * L); ω * L, s * L + R] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zoc, Jc]

@[powerlib_foundation] theorem det_Zoc (L R ω : ℝ) (s : ℂ) :
    (Zoc L R ω s).det = (s * L + R) ^ 2 + (ω * L) ^ 2 := by
  rw [Zoc_eq, Matrix.det_fin_two_of]
  ring

/-- Closed-form inverse of `Z_oc`. -/
@[powerlib_foundation] theorem Zoc_inv {L R ω : ℝ} {s : ℂ}
    (h : (s * L + R) ^ 2 + (ω * L : ℂ) ^ 2 ≠ 0) :
    (Zoc L R ω s)⁻¹ =
      ((s * L + R) ^ 2 + (ω * L : ℂ) ^ 2)⁻¹ • !![s * L + R, ω * L; -(ω * L), s * L + R] := by
  apply Matrix.inv_eq_left_inv
  have hprod : !![s * L + R, (ω * L : ℂ); -(ω * L), s * L + R] * Zoc L R ω s =
      ((s * L + R) ^ 2 + (ω * L : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Zoc_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [Matrix.smul_mul, hprod, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- `G_id = −V_dc Z_oc⁻¹`. -/
def Gid (L R ω Vdc : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := -((Vdc : ℂ) • (Zoc L R ω s)⁻¹)

@[powerlib_foundation] theorem Gid_eq {L R ω Vdc : ℝ} {s : ℂ}
    (h : (s * L + R) ^ 2 + (ω * L : ℂ) ^ 2 ≠ 0) :
    Gid L R ω Vdc s =
      -((Vdc : ℂ) / ((s * L + R) ^ 2 + (ω * L) ^ 2)) •
        !![s * L + R, ω * L; -(ω * L), s * L + R] := by
  rw [Gid, Zoc_inv h, smul_smul, ← neg_smul, div_eq_mul_inv]

/-! ## PLL frame projections -/

/-- First-order rotation: `d/dθ (park θ · x)` at `θ = 0` is `−J x`. -/
@[powerlib_foundation] theorem hasDerivAt_park_zero (x : Fin 2 → ℝ) :
    HasDerivAt (fun θ => Transform.park θ *ᵥ x) (-(Transform.J *ᵥ x)) 0 := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simp only [Transform.park_apply_mulVec, Fin.zero_eta, Matrix.cons_val_zero]
    convert ((Real.hasDerivAt_cos 0).mul_const (x 0)).add
      ((Real.hasDerivAt_sin 0).mul_const (x 1)) using 1
    simp
  · simp only [Transform.park_apply_mulVec, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    convert ((Real.hasDerivAt_sin 0).neg.mul_const (x 0)).add
      ((Real.hasDerivAt_cos 0).mul_const (x 1)) using 1
    simp

/-- Voltage projection system → PLL frame: `ΔV^pll = ΔV − (G ΔV_q) J V₀ = G_v^pll ΔV`. -/
@[powerlib_foundation] theorem pllVoltage_proj (V0 dV : Fin 2 → ℂ) (G : ℂ) :
    dV - (G * dV 1) • (Jc *ᵥ V0) = !![1, V0 1 * G; 0, 1 - V0 0 * G] *ᵥ dV := by
  ext k
  fin_cases k <;> simp [Jc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Current (and duty) projection: `ΔI^sys − ΔI^pll = (G ΔV_q) J I₀ = G_i^pll ΔV`. -/
@[powerlib_foundation] theorem pllCurrent_proj (I0 dV : Fin 2 → ℂ) (G : ℂ) :
    (G * dV 1) • (Jc *ᵥ I0) = !![0, -(I0 1 * G); 0, I0 0 * G] *ᵥ dV := by
  ext k
  fin_cases k <;> simp [Jc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- PLL-aligned operating point (`V_q0 = 0`): `G_v^pll = diag(1, 1 − V_d0 G)`. -/
@[powerlib_foundation] theorem pllVoltage_aligned (Vd0 G : ℂ) :
    (!![1, (0 : ℂ) * G; 0, 1 - Vd0 * G] : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![1, 1 - Vd0 * G] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ## dq ↔ complex-vector (sequence) form -/

/-- `A = [[1, j], [1, −j]]`: `(x_d, x_q) ↦ (x_d + j x_q, x_d − j x_q)`. -/
def seqMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; 1, -Complex.I]

/-- `A⁻¹ = ½ [[1, 1], [−j, j]]`. -/
def seqMatrixInv : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • !![1, 1; -Complex.I, Complex.I]

@[powerlib_foundation] theorem seqMatrix_mul_inv : seqMatrix * seqMatrixInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seqMatrix, seqMatrixInv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq] <;> norm_num

@[powerlib_foundation] theorem seqMatrixInv_mul : seqMatrixInv * seqMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seqMatrix, seqMatrixInv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq]

/-- Complex-vector (modified sequence) form of a dq transfer matrix. -/
def toSeq (Y : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  seqMatrix * Y * seqMatrixInv

@[powerlib_foundation] theorem toSeq_eq (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    toSeq Y =
      !![((Y 0 0 + Y 1 1) + Complex.I * (Y 1 0 - Y 0 1)) / 2,
          ((Y 0 0 - Y 1 1) + Complex.I * (Y 1 0 + Y 0 1)) / 2;
        ((Y 0 0 - Y 1 1) - Complex.I * (Y 1 0 + Y 0 1)) / 2,
          ((Y 0 0 + Y 1 1) - Complex.I * (Y 1 0 - Y 0 1)) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toSeq, seqMatrix, seqMatrixInv, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- No coupling between the two complex-vector channels iff `Y_dd = Y_qq ∧ Y_dq = −Y_qd`. -/
@[powerlib_foundation] theorem toSeq_offDiag_eq_zero_iff (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (toSeq Y 0 1 = 0 ∧ toSeq Y 1 0 = 0) ↔ (Y 0 0 = Y 1 1 ∧ Y 0 1 = -Y 1 0) := by
  rw [toSeq_eq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨h1, h2⟩
    have hs : Y 0 0 - Y 1 1 = 0 := by linear_combination h1 + h2
    have hd : Complex.I * (Y 1 0 + Y 0 1) = 0 := by linear_combination h1 - h2
    have hd' : Y 1 0 + Y 0 1 = 0 := by simpa [Complex.I_ne_zero] using hd
    exact ⟨by linear_combination hs, by linear_combination hd'⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [h1, h2]; ring
    · rw [h1, h2]; ring

/-- The return difference `det(I + Z Y)` is the same in dq and complex-vector form. -/
@[powerlib_foundation] theorem returnDifference_toSeq (Z Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 + toSeq Z * toSeq Y).det = (1 + Z * Y).det := by
  have h : 1 + toSeq Z * toSeq Y = seqMatrix * (1 + Z * Y) * seqMatrixInv := by
    simp only [toSeq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [seqMatrix_mul_inv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc seqMatrixInv seqMatrix, seqMatrixInv_mul, Matrix.one_mul]
  rw [h, Matrix.det_mul, Matrix.det_mul, mul_comm (seqMatrix.det), mul_assoc,
    ← Matrix.det_mul, seqMatrix_mul_inv, Matrix.det_one, mul_one]

/-! ## Shunt capacitor in the dq frame (Correction) -/

/-- Park: if `C dv_αβ/dt = i_αβ` with `v_αβ = rot θ · v`, `i_αβ = rot θ · i`, `θ' = ω`, then
`C dv/dt = i − ω C J v`. -/
@[powerlib_foundation] theorem capacitor_dq {C : ℝ} {θ : ℝ → ℝ} {ω : ℝ} {v i : ℝ → Fin 2 → ℝ}
    {v' : Fin 2 → ℝ} {t : ℝ} (hθ : HasDerivAt θ ω t) (hv : HasDerivAt v v' t)
    (hαβ : HasDerivAt (fun s => Transform.rot (θ s) *ᵥ v s)
      (C⁻¹ • (Transform.rot (θ t) *ᵥ i t)) t) (hC : C ≠ 0) :
    C • v' = i t - (ω * C) • (Transform.J *ᵥ v t) := by
  have h := Transform.hasDerivAt_rot_mulVec hθ hv
  have heq := h.unique hαβ
  have h2 : v' + ω • (Transform.J *ᵥ v t) = C⁻¹ • i t := by
    have := congrArg (fun y => Transform.park (θ t) *ᵥ y) heq
    simp only [← Matrix.mulVec_smul, Transform.park_mulVec_rot_mulVec] at this
    rwa [Matrix.mulVec_smul] at this
  have h3 := congrArg (fun y => C • y) h2
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hC, one_smul] at h3
  rw [← h3, mul_comm ω C, ← smul_smul]
  abel

/-- Corrected parallel-RC load admittance in dq: `(1/R + sC) I + ωC J`. -/
def Yload (Rl C ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Rl + s * C) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ((ω * C : ℝ) : ℂ) • Jc

/-- The note's load admittance `(1/R + sC) I` (cross term missing). -/
def YloadNote (Rl C : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Rl + s * C) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

@[powerlib_foundation] theorem noteLoad_ne {Rl C ω : ℝ} (h : ω * C ≠ 0) (s : ℂ) :
    YloadNote Rl C s ≠ Yload Rl C ω s := by
  intro heq
  have := congrFun (congrFun heq 1) 0
  simp [YloadNote, Yload, Jc] at this
  rcases this with h1 | h1 <;> simp [h1] at h

/-- Corrected network-side impedance `Z_ext = (Z_line⁻¹ + Y_load)⁻¹`. -/
def Zext (Lg Rg Rl C ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Zoc Lg Rg ω s)⁻¹ + Yload Rl C ω s)⁻¹

/-- Parallel-connection identity `(Z⁻¹ + Y)⁻¹ = Z (I + Y Z)⁻¹` for invertible `Z`. -/
@[powerlib_foundation] theorem Zext_eq {Lg Rg Rl C ω : ℝ} {s : ℂ}
    (hZ : IsUnit (Zoc Lg Rg ω s).det) :
    Zext Lg Rg Rl C ω s = Zoc Lg Rg ω s * (1 + Yload Rl C ω s * Zoc Lg Rg ω s)⁻¹ := by
  set Z := Zoc Lg Rg ω s
  set Y := Yload Rl C ω s
  have hfac : Z⁻¹ + Y = (1 + Y * Z) * Z⁻¹ := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZ,
      Matrix.mul_one]
  rw [Zext, hfac, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZ]

end powerlib.CurrentControl
