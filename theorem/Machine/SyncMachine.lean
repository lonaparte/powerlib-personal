import dependencies.Mathlib
import theorem.Attributes

/-! # Synchronous machine: Park-transform algebra of the stator (foundation)

Model and conventions.
* Three-phase salient-pole synchronous machine, electrical rotor angle `θ` (`θ̇ = ω`), linear
  magnetics, sinusoidally distributed windings. Phase axes `φ_a = 0`, `φ_b = 2π/3`,
  `φ_c = −2π/3`.
* Stator self/mutual inductances (Kundur Ch. 3 form):
  `l_xy(θ) = L_ℓ δ_xy + L_A cos(φ_x − φ_y) + L_B cos(2θ − φ_x − φ_y)`
  (`statorInductance_apply`), i.e. `l_aa = L_aa0 + L_aa2 cos 2θ`, `l_ab = −L_ab0 + L_aa2 cos(2θ − 2π/3)`
  with `L_aa0 = L_ℓ + L_A`, `L_ab0 = L_A/2`, `L_aa2 = L_B`.
* Power-invariant Park matrix `T_P(θ)` with rows `√(2/3) cos(θ − φ_x)`, `−√(2/3) sin(θ − φ_x)`,
  `1/√3` (work-sync conventions §4).
* **Direction**: generator (OUT-positive) stator current, Kundur convention — the single
  exception to the work-sync IN-positive default (conventions §D2). Stator voltage
  `v_abc = dψ_abc/dt − r_s i_abc` (`e = pψ − R i`), flux `ψ_d = −L_d i_d + …`.

Contents.
* `parkMatrix_mul_transpose`: `T_P T_Pᵀ = I` (orthogonality; `T_P⁻¹ = T_Pᵀ`).
* `park_statorInductance`: `T_P(θ) L(θ) T_P(θ)ᵀ = diag(L_d, L_q, L_0)` with
  `L_d = L_ℓ + (3/2)(L_A + L_B)`, `L_q = L_ℓ + (3/2)(L_A − L_B)`, `L_0 = L_ℓ`, **independent
  of θ**; stator–rotor mutual inductances also become constant (`park_mutual_d`,
  `park_mutual_q`).
* `parkMatrix_mul_deriv_transpose`: `T_P (dT_P/dθ)ᵀ = J₀` (`J₀` = 90° rotation in the dq plane);
  the opposite order is not `J₀` (`deriv_transpose_mul_parkMatrix_ne`).
* `park_flux_hasDerivAt`, `dq0_voltage_equations`: from `v_abc = dψ_abc/dt − r i_abc`,
  `v_d = ψ̇_d − ω ψ_q − r i_d`, `v_q = ψ̇_q + ω ψ_d − r i_q`, `v_0 = ψ̇_0 − r i_0`.
* `park_power_invariant`, `power_dq0`: `v_abc·i_abc = v_dq0·i_dq0
  = Σ ψ̇ i − r|i|² + ω(ψ_d i_q − ψ_q i_d)`; the speed-voltage power defines
  `T_e = ψ_d i_q − ψ_q i_d`.
* `twoAxis_power`, `classical_power`, `classical_power_linearization`.

Source: work-sync theory/T-sync-machine.md §1.1–§1.5, §1.8, §1.9 (machine algebra only; SMIB
stability and pH passivity are formalized elsewhere).

Corrections.
* §1.1/§1.4: `v_abc = −r i − dψ/dt` together with §1.3's `ψ_d = −L_d i_d + …` mixes two sign
  conventions. In the Kundur generator convention used by §1.3 the stator equation is
  `v = dψ/dt − r i`, giving `v_d = −r i_d + ψ̇_d − ω ψ_q`, `v_q = −r i_q + ψ̇_q + ω ψ_d`
  (`dq0_voltage_equations`); the note's boxed `−ψ̇` terms have the wrong sign.
* §1.4: "`Ṫ_P⁻¹ T_P = ω J`" has the product in the wrong order: `T_P · d(T_P⁻¹)/dt = ω J₀`
  holds, `d(T_P⁻¹)/dt · T_P` does not (`deriv_transpose_mul_parkMatrix_ne`).
* §1.8: with the two-axis stator equations (`r_s = 0`) `v_d = E_d' + X_q' i_q`,
  `v_q = E_q' − X_d' i_d`, the reluctance term is `(X_q' − X_d') i_d i_q`, not
  `(X_d' − X_q') i_d i_q` (`twoAxis_power`).
* §1.9: the linearisation is `sin δ ≈ sin δ₀ + cos δ₀ Δδ` (`classical_power_linearization`), not
  `δ − δ₀ + cos δ₀ Δδ`.
-/

noncomputable section
namespace powerlib.Machine.SyncMachine

open Matrix Filter Asymptotics
open scoped Topology

/-- Phase-axis angles `φ_a = 0`, `φ_b = 2π/3`, `φ_c = −2π/3`. -/
def phase : Fin 3 → ℝ := ![0, 2 * Real.pi / 3, -(2 * Real.pi / 3)]

/-- `(cos(θ − φ_x))_x`. -/
def cvec (θ : ℝ) : Fin 3 → ℝ := fun x => Real.cos (θ - phase x)

/-- `(sin(θ − φ_x))_x`. -/
def svec (θ : ℝ) : Fin 3 → ℝ := fun x => Real.sin (θ - phase x)

@[powerlib_foundation] theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

@[powerlib_foundation] theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring

@[powerlib_foundation] theorem sin_two_pi_div_three :
    Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]

@[powerlib_foundation] theorem cvec_explicit (θ : ℝ) :
    cvec θ = ![Real.cos θ, -Real.cos θ / 2 + Real.sqrt 3 / 2 * Real.sin θ,
      -Real.cos θ / 2 - Real.sqrt 3 / 2 * Real.sin θ] := by
  ext x
  fin_cases x <;>
    simp [cvec, phase, Real.cos_sub, Real.cos_add, cos_two_pi_div_three, sin_two_pi_div_three,
] <;> ring

@[powerlib_foundation] theorem svec_explicit (θ : ℝ) :
    svec θ = ![Real.sin θ, -Real.sin θ / 2 - Real.sqrt 3 / 2 * Real.cos θ,
      -Real.sin θ / 2 + Real.sqrt 3 / 2 * Real.cos θ] := by
  ext x
  fin_cases x <;>
    simp [svec, phase, Real.sin_sub, Real.sin_add, cos_two_pi_div_three, sin_two_pi_div_three,
] <;> ring

section Dots

variable (θ : ℝ)

@[powerlib_foundation] theorem cvec_dot_cvec : cvec θ ⬝ᵥ cvec θ = 3 / 2 := by
  rw [cvec_explicit]
  simp [dotProduct, Fin.sum_univ_three]
  linear_combination (Real.sin θ ^ 2 / 2) * sqrt3_sq + (3 / 2) * Real.sin_sq_add_cos_sq θ

@[powerlib_foundation] theorem svec_dot_svec : svec θ ⬝ᵥ svec θ = 3 / 2 := by
  rw [svec_explicit]
  simp [dotProduct, Fin.sum_univ_three]
  linear_combination (Real.cos θ ^ 2 / 2) * sqrt3_sq + (3 / 2) * Real.sin_sq_add_cos_sq θ

@[powerlib_foundation] theorem cvec_dot_svec : cvec θ ⬝ᵥ svec θ = 0 := by
  rw [cvec_explicit, svec_explicit]
  simp [dotProduct, Fin.sum_univ_three]
  linear_combination (-(Real.sin θ * Real.cos θ) / 2) * sqrt3_sq

@[powerlib_foundation] theorem svec_dot_cvec : svec θ ⬝ᵥ cvec θ = 0 := by
  rw [dotProduct_comm, cvec_dot_svec]

@[powerlib_foundation] theorem cvec_sum : ∑ x, cvec θ x = 0 := by
  rw [cvec_explicit]; simp [Fin.sum_univ_three]; ring

@[powerlib_foundation] theorem svec_sum : ∑ x, svec θ x = 0 := by
  rw [svec_explicit]; simp [Fin.sum_univ_three]; ring

end Dots

/-- `k = √(2/3)`, the Park row scale. -/
def k : ℝ := Real.sqrt (2 / 3)

@[powerlib_foundation] theorem k_sq : k ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)

@[powerlib_foundation] theorem inv_sqrt3_sq : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
  rw [div_pow, sqrt3_sq]; norm_num

/-- Rows of the power-invariant Park matrix. -/
def parkRow (θ : ℝ) : Fin 3 → Fin 3 → ℝ := ![k • cvec θ, -k • svec θ, fun _ => 1 / Real.sqrt 3]

/-- Power-invariant Park matrix `T_P(θ)`. -/
def parkMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (parkRow θ)

/-- Rows of `dT_P/dθ`. -/
def parkDerivRow (θ : ℝ) : Fin 3 → Fin 3 → ℝ := ![-k • svec θ, -k • cvec θ, 0]

/-- `dT_P/dθ`. -/
def parkDeriv (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (parkDerivRow θ)

@[powerlib_foundation] theorem const_dotProduct (a : ℝ) (v : Fin 3 → ℝ) :
    (fun _ => a) ⬝ᵥ v = a * ∑ x, v x := by
  simp [dotProduct, Finset.mul_sum]

@[powerlib_foundation] theorem dotProduct_const (a : ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (fun _ => a) = a * ∑ x, v x := by
  rw [dotProduct_comm, const_dotProduct]

@[powerlib_foundation] theorem of_mul_transpose_apply (A B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    (Matrix.of A * (Matrix.of B)ᵀ) i j = A i ⬝ᵥ B j := by
  simp [Matrix.mul_apply, dotProduct]

@[powerlib_foundation] theorem parkMatrix_hasDerivAt (θ : ℝ) (i x : Fin 3) :
    HasDerivAt (fun φ => parkMatrix φ i x) (parkDeriv θ i x) θ := by
  fin_cases i
  · simpa [parkMatrix, parkDeriv, parkRow, parkDerivRow, cvec, svec] using
      ((Real.hasDerivAt_cos (θ - phase x)).comp θ
        ((hasDerivAt_id θ).sub_const (phase x))).const_mul k
  · simpa [parkMatrix, parkDeriv, parkRow, parkDerivRow, cvec, svec] using
      ((Real.hasDerivAt_sin (θ - phase x)).comp θ
        ((hasDerivAt_id θ).sub_const (phase x))).const_mul (-k)
  · simpa [parkMatrix, parkDeriv, parkRow, parkDerivRow] using
      hasDerivAt_const θ (1 / Real.sqrt 3)

@[powerlib_foundation] theorem parkMatrix_mulVec (θ : ℝ) (v : Fin 3 → ℝ) :
    parkMatrix θ *ᵥ v =
      ![k * (cvec θ ⬝ᵥ v), -k * (svec θ ⬝ᵥ v), 1 / Real.sqrt 3 * ∑ x, v x] := by
  ext i
  fin_cases i <;>
    simp [parkMatrix, parkRow, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Orthogonality `T_P T_Pᵀ = I`. -/
@[powerlib_foundation] theorem parkMatrix_mul_transpose (θ : ℝ) :
    parkMatrix θ * (parkMatrix θ)ᵀ = 1 := by
  have hk := k_sq
  have h3 := sqrt3_sq
  have h3p : 0 < Real.sqrt 3 := by positivity
  ext i j
  rw [parkMatrix, of_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [parkRow, smul_dotProduct, dotProduct_smul, const_dotProduct,
      dotProduct_const, cvec_dot_cvec, svec_dot_svec, cvec_dot_svec, svec_dot_cvec, cvec_sum,
      svec_sum] <;>
    first
    | linear_combination (3 / 2) * hk
    | (field_simp; linarith)

@[powerlib_foundation] theorem parkMatrix_transpose_mul (θ : ℝ) :
    (parkMatrix θ)ᵀ * parkMatrix θ = 1 :=
  mul_eq_one_comm.mp (parkMatrix_mul_transpose θ)

/-- `J₀`: 90° rotation in the dq plane, zero on the zero sequence. -/
def J0 : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

/-- `T_P (dT_P/dθ)ᵀ = J₀`. -/
@[powerlib_foundation] theorem parkMatrix_mul_deriv_transpose (θ : ℝ) :
    parkMatrix θ * (parkDeriv θ)ᵀ = J0 := by
  have hk := k_sq
  ext i j
  rw [parkMatrix, parkDeriv, of_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [parkRow, parkDerivRow, J0, smul_dotProduct, dotProduct_smul,
      const_dotProduct, cvec_dot_cvec, svec_dot_svec, cvec_dot_svec,
      svec_dot_cvec, cvec_sum, svec_sum] <;>
    linear_combination (3 / 2) * hk

/-- The reversed product `(dT_P/dθ)ᵀ T_P` is not `J₀` (entry `(a, b)` at `θ = 0` is `−1/√3`). -/
@[powerlib_foundation] theorem deriv_transpose_mul_parkMatrix_ne :
    (parkDeriv 0)ᵀ * parkMatrix 0 ≠ J0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  have hk := k_sq
  have h3 := sqrt3_sq
  simp [Matrix.mul_apply, Fin.sum_univ_three, parkMatrix, parkDeriv, parkRow, parkDerivRow, J0,
    cvec_explicit, svec_explicit] at h01
  -- h01 : k * k * (√3/2) ... = -1
  have : k ^ 2 * (Real.sqrt 3 / 2) = 1 := by linear_combination h01
  rw [hk] at this
  have : Real.sqrt 3 = 3 := by linarith
  rw [this] at h3
  norm_num at h3

/-! ## Inductances -/

/-- Salient-pole stator inductance matrix
`L(θ) = L_ℓ I + (L_A + L_B) c cᵀ + (L_A − L_B) s sᵀ`. -/
def statorInductance (Ll LA LB θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Ll • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (LA + LB) • vecMulVec (cvec θ) (cvec θ) +
    (LA - LB) • vecMulVec (svec θ) (svec θ)

/-- Entries of `L(θ)`: `L_ℓ δ_xy + L_A cos(φ_x − φ_y) + L_B cos(2θ − φ_x − φ_y)`. -/
@[powerlib_foundation] theorem statorInductance_apply (Ll LA LB θ : ℝ) (x y : Fin 3) :
    statorInductance Ll LA LB θ x y =
      (if x = y then Ll else 0) + LA * Real.cos (phase x - phase y) +
        LB * Real.cos (2 * θ - phase x - phase y) := by
  simp only [statorInductance, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    Matrix.one_apply, smul_eq_mul, cvec, svec]
  have key : ∀ u v : ℝ, (LA + LB) * (Real.cos u * Real.cos v) +
      (LA - LB) * (Real.sin u * Real.sin v) = LA * Real.cos (u - v) + LB * Real.cos (u + v) := by
    intro u v
    rw [Real.cos_sub, Real.cos_add]
    ring
  have h := key (θ - phase x) (θ - phase y)
  rw [show θ - phase x - (θ - phase y) = -(phase x - phase y) by ring, Real.cos_neg,
    show θ - phase x + (θ - phase y) = 2 * θ - phase x - phase y by ring] at h
  split_ifs <;> linarith

/-- **dq inductances are independent of the rotor angle.**
`T_P(θ) L(θ) T_P(θ)ᵀ = diag(L_ℓ + (3/2)(L_A + L_B), L_ℓ + (3/2)(L_A − L_B), L_ℓ)`. -/
@[powerlib_foundation] theorem park_statorInductance (Ll LA LB θ : ℝ) :
    parkMatrix θ * statorInductance Ll LA LB θ * (parkMatrix θ)ᵀ =
      diagonal ![Ll + 3 / 2 * (LA + LB), Ll + 3 / 2 * (LA - LB), Ll] := by
  have hc : parkMatrix θ *ᵥ cvec θ = ![k * (3 / 2), 0, 0] := by
    rw [parkMatrix_mulVec, cvec_dot_cvec, svec_dot_cvec, cvec_sum]
    simp
  have hs : parkMatrix θ *ᵥ svec θ = ![0, -k * (3 / 2), 0] := by
    rw [parkMatrix_mulVec, svec_dot_svec, cvec_dot_svec, svec_sum]
    simp
  have hk := k_sq
  simp only [statorInductance, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, parkMatrix_mul_transpose, mul_vecMulVec, vecMulVec_mul,
    Matrix.vecMul_transpose, hc, hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;>
    first
    | ring1
    | linear_combination (9 / 4 * (LA + LB)) * hk
    | linear_combination (9 / 4 * (LA - LB)) * hk

/-- Stator–field mutual inductance column `L_afd (cos(θ − φ_x))_x` maps to the constant
d-axis value `√(3/2) L_afd` (written `k · 3/2 · L_afd`). -/
@[powerlib_foundation] theorem park_mutual_d (Lafd θ : ℝ) :
    parkMatrix θ *ᵥ (Lafd • cvec θ) = ![k * (3 / 2) * Lafd, 0, 0] := by
  rw [Matrix.mulVec_smul, parkMatrix_mulVec, cvec_dot_cvec, svec_dot_cvec, cvec_sum]
  ext i
  fin_cases i <;> simp
  ring

/-- Stator–q-damper mutual inductance column `−L_akq (sin(θ − φ_x))_x` maps to the constant
q-axis value `√(3/2) L_akq`. -/
@[powerlib_foundation] theorem park_mutual_q (Lakq θ : ℝ) :
    parkMatrix θ *ᵥ (-Lakq • svec θ) = ![0, k * (3 / 2) * Lakq, 0] := by
  rw [Matrix.mulVec_smul, parkMatrix_mulVec, svec_dot_svec, cvec_dot_svec, svec_sum]
  ext i
  fin_cases i <;> simp
  ring

/-! ## Stator voltage equations in dq0 -/

/-- Derivative of the phase flux `ψ_abc = T_P(θ)ᵀ ψ_dq0` along a trajectory. -/
@[powerlib_foundation] theorem park_flux_hasDerivAt (θ : ℝ → ℝ) (ω : ℝ) (ψ : ℝ → Fin 3 → ℝ)
    (dψ : Fin 3 → ℝ) (t : ℝ) (hθ : HasDerivAt θ ω t) (hψ : HasDerivAt ψ dψ t) :
    HasDerivAt (fun s => (parkMatrix (θ s))ᵀ *ᵥ ψ s)
      ((parkMatrix (θ t))ᵀ *ᵥ dψ + ω • ((parkDeriv (θ t))ᵀ *ᵥ ψ t)) t := by
  rw [hasDerivAt_pi]
  intro x
  have hP : ∀ i, HasDerivAt (fun s => parkMatrix (θ s) i x) (parkDeriv (θ t) i x * ω) t :=
    fun i => (parkMatrix_hasDerivAt (θ t) i x).comp t hθ
  have hc : ∀ i, HasDerivAt (fun s => ψ s i) (dψ i) t := fun i => hasDerivAt_pi.mp hψ i
  have h := (((hP 0).mul (hc 0)).add ((hP 1).mul (hc 1))).add ((hP 2).mul (hc 2))
  convert h using 1
  · funext s
    simp [mulVec, dotProduct, Fin.sum_univ_three]
  · simp [mulVec, dotProduct, Fin.sum_univ_three]
    ring

/-- `T_P (d/dt)(T_Pᵀ ψ_dq0) = ψ̇_dq0 + ω J₀ ψ_dq0`. -/
@[powerlib_foundation] theorem park_apply_flux_derivative (θ ω : ℝ) (ψ dψ : Fin 3 → ℝ) :
    parkMatrix θ *ᵥ ((parkMatrix θ)ᵀ *ᵥ dψ + ω • ((parkDeriv θ)ᵀ *ᵥ ψ)) =
      dψ + ω • (J0 *ᵥ ψ) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    parkMatrix_mul_transpose, parkMatrix_mul_deriv_transpose, Matrix.one_mulVec]

/-- **dq0 stator voltage equations (Kundur generator convention).** If the phase quantities
satisfy `v_abc = dψ_abc/dt − r i_abc` with `ψ_abc = T_Pᵀ ψ_dq0`, `i_abc = T_Pᵀ i_dq0` and
`θ̇ = ω`, then `T_P v_abc = (ψ̇_d − ωψ_q − r i_d, ψ̇_q + ωψ_d − r i_q, ψ̇_0 − r i_0)`. -/
@[powerlib_foundation] theorem dq0_voltage_equations (r ω t : ℝ) (θ : ℝ → ℝ) (ψ : ℝ → Fin 3 → ℝ)
    (dψ idq : Fin 3 → ℝ) (dψabc vabc : Fin 3 → ℝ) (hθ : HasDerivAt θ ω t)
    (hψ : HasDerivAt ψ dψ t)
    (habc : HasDerivAt (fun s => (parkMatrix (θ s))ᵀ *ᵥ ψ s) dψabc t)
    (hv : vabc = dψabc - r • ((parkMatrix (θ t))ᵀ *ᵥ idq)) :
    parkMatrix (θ t) *ᵥ vabc =
      ![dψ 0 - ω * ψ t 1 - r * idq 0, dψ 1 + ω * ψ t 0 - r * idq 1, dψ 2 - r * idq 2] := by
  have hu := habc.unique (park_flux_hasDerivAt θ ω ψ dψ t hθ hψ)
  rw [hv, hu, Matrix.mulVec_sub, park_apply_flux_derivative, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, parkMatrix_mul_transpose, Matrix.one_mulVec]
  ext i
  fin_cases i <;> simp [J0, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]
  ring

/-! ## Power and torque -/

/-- Power invariance of `T_P`: `(T_P v)·(T_P i) = v·i`. -/
@[powerlib_foundation] theorem park_power_invariant (θ : ℝ) (v i : Fin 3 → ℝ) :
    (parkMatrix θ *ᵥ v) ⬝ᵥ (parkMatrix θ *ᵥ i) = v ⬝ᵥ i := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    parkMatrix_transpose_mul, Matrix.one_mulVec]

/-- Air-gap torque (power-invariant per-unit, per pole pair, generator convention). -/
def torque (ψd ψq id iq : ℝ) : ℝ := ψd * iq - ψq * id

/-- Output power in dq0: `v·i = Σ ψ̇ i − r |i|² + ω T_e`. -/
@[powerlib_foundation] theorem power_dq0 (r ω ψd ψq dψd dψq dψ0 id iq i0 : ℝ) :
    (dψd - ω * ψq - r * id) * id + (dψq + ω * ψd - r * iq) * iq + (dψ0 - r * i0) * i0 =
      (dψd * id + dψq * iq + dψ0 * i0) - r * (id ^ 2 + iq ^ 2 + i0 ^ 2) +
        ω * torque ψd ψq id iq := by
  unfold torque; ring

/-- Two-axis model (`r_s = 0`, Sauer–Pai stator algebra `v_d = E_d' + X_q' i_q`,
`v_q = E_q' − X_d' i_d`): `P_e = E_d' i_d + E_q' i_q + (X_q' − X_d') i_d i_q`. -/
@[powerlib_foundation] theorem twoAxis_power (Ed Eq Xd' Xq' id iq vd vq : ℝ)
    (hd : vd = Ed + Xq' * iq) (hq : vq = Eq - Xd' * id) :
    vd * id + vq * iq = Ed * id + Eq * iq + (Xq' - Xd') * id * iq := by
  subst hd hq; ring

/-- The note's reluctance coefficient `(X_d' − X_q')` disagrees with the stator algebra whenever
the machine is salient and `i_d i_q ≠ 0`. -/
@[powerlib_foundation] theorem twoAxis_noteSign_ne (Ed Eq Xd' Xq' id iq : ℝ) (hs : Xd' ≠ Xq')
    (hi : id * iq ≠ 0) :
    Ed * id + Eq * iq + (Xq' - Xd') * id * iq ≠ Ed * id + Eq * iq + (Xd' - Xq') * id * iq := by
  intro h
  have : (Xq' - Xd') * (id * iq) = 0 := by linear_combination h / 2
  rcases mul_eq_zero.mp this with h' | h'
  · exact hs (by linarith)
  · exact hi h'

/-- Classical model: internal EMF `E' e^{jδ}` behind `X_d'` connected to the infinite bus
`V∠0`. From `S = V I*` with `I = (E' e^{jδ} − V)/(jX)`, the active power delivered to the
bus is `E' V sin δ / X`. -/
@[powerlib_foundation] theorem classical_power (E V X δ : ℝ) (hX : X ≠ 0) :
    ((V : ℂ) * (starRingEnd ℂ) (((⟨E * Real.cos δ, E * Real.sin δ⟩ : ℂ) - V) /
      (Complex.I * X))).re = E * V / X * Real.sin δ := by
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have h : ((⟨E * Real.cos δ, E * Real.sin δ⟩ : ℂ) - V) / (Complex.I * X) =
      ⟨E * Real.sin δ / X, -(E * Real.cos δ - V) / X⟩ := by
    rw [div_eq_iff (mul_ne_zero Complex.I_ne_zero hX')]
    apply Complex.ext <;> simp <;> field_simp
    ring
  rw [h]
  simp
  ring

/-- Correct first-order expansion of the classical electrical power around `δ₀`:
`P_max sin(δ₀ + h) = P_max sin δ₀ + P_max cos δ₀ · h + o(h)`. -/
@[powerlib_foundation] theorem classical_power_linearization (Pmax δ₀ : ℝ) :
    (fun h => Pmax * Real.sin (δ₀ + h) - Pmax * Real.sin δ₀ - h * (Pmax * Real.cos δ₀)) =o[𝓝 0]
      fun h => h := by
  have hd : HasDerivAt (fun δ => Pmax * Real.sin δ) (Pmax * Real.cos δ₀) δ₀ :=
    (Real.hasDerivAt_sin δ₀).const_mul Pmax
  have := hasDerivAt_iff_isLittleO_nhds_zero.mp hd
  simpa [smul_eq_mul] using this

end powerlib.Machine.SyncMachine
