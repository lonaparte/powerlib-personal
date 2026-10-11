import theorem.Attributes
import dependencies.Mathlib

/-! # Complex power, P/Q in dq, current references and the P/Q Jacobians (foundation)

Derivation method of work-sync `conventions.md` §D0: start from `S̄ = V̄ Ī*` with
`V̄ = v_d + j v_q`, `Ī = i_d + j i_q`, `i` IN-positive (§D1), load convention (§D3): `P > 0`
absorbed by the converter.

* `complexPower_expand`: `V̄ Ī* = (v_d i_d + v_q i_q) + j (v_q i_d − v_d i_q)`;
  `activePower_eq_re`, `reactivePower_eq_im`: `P = (3/2) Re S̄`, `Q = (3/2) Im S̄` (SI,
  amplitude-invariant Park; the per-unit forms drop `3/2`).
* `currentRef_spec`, `currentRef_unique`: in the PLL-aligned frame (`v_q = 0`, `v_d ≠ 0`) the
  references `i_d* = 2 P*/(3 v_d)`, `i_q* = −2 Q*/(3 v_d)` give exactly `P = P*`, `Q = Q*`, and
  they are the only currents that do (T-gfl-control §1.5 boxed). `currentRef_export`: the
  export-positive dispatch form `i_d* = −2 P*_exp/(3 v_d)`, `i_q* = 2 Q*_exp/(3 v_d)`.
  `currentRef_sign`: for `v_d > 0`, absorbing reactive power (`Q* > 0`) means `i_q* < 0`.
* `pq_mulVec_current`, `pq_mulVec_voltage`, `pq_expansion`: per-unit `(P, Q)` is bilinear in
  `(v, i)`; its Jacobians are `∂(P,Q)/∂(i_d,i_q) = [[v_d0, v_q0], [v_q0, −v_d0]]` and
  `∂(P,Q)/∂(v_d,v_q) = [[i_d0, i_q0], [−i_q0, i_d0]]`, with the exact expansion
  `Δ(P,Q) = G_i Δi + G_v Δv + (P,Q)(Δv, Δi)` (T-gfl-control §1.5, T-gfl-impedance §1.5).
  `pq_hasFDerivAt`: the same Jacobian as a Fréchet derivative.

Source: work-sync `theory/T-gfl-control.md` §1.5; `theory/T-gfl-impedance.md` §1.5;
`theory/T-dc-voltage-gfm.md` §1.1 (same expansion); `conventions.md` §D0–§D3.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix ComplexConjugate

/-- `V̄ Ī*` expanded into real and imaginary parts. -/
@[powerlib_foundation] theorem complexPower_expand (vd vq id iq : ℝ) :
    (⟨vd, vq⟩ : ℂ) * conj (⟨id, iq⟩ : ℂ) = ⟨vd * id + vq * iq, vq * id - vd * iq⟩ := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring

/-- Active power `P = (3/2)(v_d i_d + v_q i_q)` (IN-positive, absorbed). -/
def activePower (vd vq id iq : ℝ) : ℝ := 3 / 2 * (vd * id + vq * iq)

/-- Reactive power `Q = (3/2)(v_q i_d − v_d i_q)` (IN-positive, absorbed). -/
def reactivePower (vd vq id iq : ℝ) : ℝ := 3 / 2 * (vq * id - vd * iq)

@[powerlib_foundation] theorem activePower_eq_re (vd vq id iq : ℝ) :
    activePower vd vq id iq = 3 / 2 * ((⟨vd, vq⟩ : ℂ) * conj (⟨id, iq⟩ : ℂ)).re := by
  rw [complexPower_expand]
  rfl

@[powerlib_foundation] theorem reactivePower_eq_im (vd vq id iq : ℝ) :
    reactivePower vd vq id iq = 3 / 2 * ((⟨vd, vq⟩ : ℂ) * conj (⟨id, iq⟩ : ℂ)).im := by
  rw [complexPower_expand]
  rfl

/-- PLL-aligned current references achieve the absorbed set points exactly. -/
@[powerlib_foundation] theorem currentRef_spec {vd : ℝ} (hvd : vd ≠ 0) (Pref Qref : ℝ) :
    activePower vd 0 (2 * Pref / (3 * vd)) (-(2 * Qref / (3 * vd))) = Pref ∧
      reactivePower vd 0 (2 * Pref / (3 * vd)) (-(2 * Qref / (3 * vd))) = Qref := by
  constructor <;> simp only [activePower, reactivePower] <;> field_simp <;> ring

/-- ... and they are the only currents that do. -/
@[powerlib_foundation] theorem currentRef_unique {vd id iq Pref Qref : ℝ} (hvd : vd ≠ 0)
    (hP : activePower vd 0 id iq = Pref) (hQ : reactivePower vd 0 id iq = Qref) :
    id = 2 * Pref / (3 * vd) ∧ iq = -(2 * Qref / (3 * vd)) := by
  simp only [activePower, reactivePower] at hP hQ
  constructor
  · field_simp
    linear_combination 2 * hP
  · field_simp
    linear_combination -2 * hQ

/-- Export-positive dispatch (`P_abs = −P_exp`, `Q_abs = −Q_exp`). -/
@[powerlib_foundation] theorem currentRef_export {vd : ℝ} (hvd : vd ≠ 0) (Pexp Qexp : ℝ) :
    activePower vd 0 (-(2 * Pexp / (3 * vd))) (2 * Qexp / (3 * vd)) = -Pexp ∧
      reactivePower vd 0 (-(2 * Pexp / (3 * vd))) (2 * Qexp / (3 * vd)) = -Qexp := by
  have h := currentRef_spec hvd (-Pexp) (-Qexp)
  simpa [neg_div, mul_neg] using h

/-- Sign check: with `v_d > 0`, absorbing reactive power (`Q* > 0`) means `i_q* < 0`, and
absorbing active power (`P* > 0`) means `i_d* > 0`. -/
@[powerlib_foundation] theorem currentRef_sign {vd Pref Qref : ℝ} (hvd : 0 < vd) :
    (0 < Qref ↔ -(2 * Qref / (3 * vd)) < 0) ∧ (0 < Pref ↔ 0 < 2 * Pref / (3 * vd)) := by
  have h3 : 0 < 3 * vd := by positivity
  constructor
  · rw [neg_lt_zero, div_pos_iff_of_pos_right h3]
    constructor <;> intro h <;> linarith
  · rw [div_pos_iff_of_pos_right h3]
    constructor <;> intro h <;> linarith

/-! ## Per-unit P/Q Jacobians -/

/-- Per-unit `(P, Q)` of voltage `v = (v_d, v_q)` and current `i = (i_d, i_q)`. -/
def pq (v i : Fin 2 → ℝ) : Fin 2 → ℝ := ![v 0 * i 0 + v 1 * i 1, v 1 * i 0 - v 0 * i 1]

/-- `∂(P,Q)/∂(i_d, i_q)`. -/
def Gi (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![v 0, v 1; v 1, -v 0]

/-- `∂(P,Q)/∂(v_d, v_q)`. -/
def Gv (i : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![i 0, i 1; -i 1, i 0]

@[powerlib_foundation] theorem pq_mulVec_current (v i : Fin 2 → ℝ) : pq v i = Gi v *ᵥ i := by
  ext k
  fin_cases k <;> simp [pq, Gi, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

@[powerlib_foundation] theorem pq_mulVec_voltage (v i : Fin 2 → ℝ) : pq v i = Gv i *ᵥ v := by
  ext k
  fin_cases k <;> simp [pq, Gv, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Exact expansion: `Δ(P,Q) = G_i(v₀) Δi + G_v(i₀) Δv + (P,Q)(Δv, Δi)`. -/
@[powerlib_foundation] theorem pq_expansion (v0 i0 dv di : Fin 2 → ℝ) :
    pq (v0 + dv) (i0 + di) - pq v0 i0 = Gi v0 *ᵥ di + Gv i0 *ᵥ dv + pq dv di := by
  ext k
  fin_cases k <;> simp [pq, Gi, Gv, dotProduct, Fin.sum_univ_two] <;> ring

/-- Fréchet derivative of `(v, i) ↦ (P, Q)` at `(v₀, i₀)`. -/
@[powerlib_foundation] theorem pq_hasFDerivAt (v0 i0 : Fin 2 → ℝ) :
    HasFDerivAt (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => pq z.1 z.2)
      ((Matrix.toLin' (Gv i0)).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _) +
        (Matrix.toLin' (Gi v0)).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ _ _))
      (v0, i0) := by
  have hb : IsBoundedBilinearMap ℝ (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => pq z.1 z.2) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y z
      ext k
      fin_cases k <;> simp [pq] <;> ring
    · intro c x y
      ext k
      fin_cases k <;> simp [pq] <;> ring
    · intro x y z
      ext k
      fin_cases k <;> simp [pq] <;> ring
    · intro x c y
      ext k
      fin_cases k <;> simp [pq] <;> ring
    · refine ⟨4, by norm_num, fun x y => ?_⟩
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro k
      have hx0 := norm_le_pi_norm x 0
      have hx1 := norm_le_pi_norm x 1
      have hy0 := norm_le_pi_norm y 0
      have hy1 := norm_le_pi_norm y 1
      simp only [Real.norm_eq_abs] at hx0 hx1 hy0 hy1 ⊢
      fin_cases k
      · simp only [pq, Fin.zero_eta, Matrix.cons_val_zero]
        calc |x 0 * y 0 + x 1 * y 1| ≤ |x 0| * |y 0| + |x 1| * |y 1| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by
              gcongr
          _ ≤ 4 * ‖x‖ * ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
      · simp only [pq, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        calc |x 1 * y 0 - x 0 * y 1| ≤ |x 1| * |y 0| + |x 0| * |y 1| := by
              rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
          _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by
              gcongr
          _ ≤ 4 * ‖x‖ * ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
  have h := hb.hasFDerivAt (v0, i0)
  convert h using 1
  refine ContinuousLinearMap.ext fun z => ?_
  funext k
  rw [IsBoundedBilinearMap.deriv_apply]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Matrix.toLin'_apply, Pi.add_apply]
  rw [← pq_mulVec_voltage, ← pq_mulVec_current]
  fin_cases k <;> simp [pq] <;> ring

end powerlib.CurrentControl
