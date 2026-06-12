/-
  L-filter GFL Hopf — 3-state reductions and the SCR_H1 boundary (separate formal problem).

  4-state field x = (i_d, i_q, η, θ_e); Schur reductions S₂ (PLL pendulum), S_iq, S_id, S₄.
  This file proves the parts that reduce to certified algebra (machine-verified, parametric):

    * Theorem 1 — the 2D PLL pendulum `[[0,H'],[−Ki_pll,−Kp_pll·H']]` is ALWAYS stable when `H'>0`:
      char poly `λ²+Kp_pll·H'·λ+Ki_pll·H'` (`pll_pendulum_charpoly`), all roots `Re<0`
      (`pll_pendulum_stable`, via `stable_deg2_of_pos`).  So the 2D PLL chassis cannot produce the
      engineering Hopf — that needs a root with `Re ≥ 0`, which the structure forbids.
    * Theorem 2.c / 3 — for a 3-state reduction with char poly `s³+A s²+B s+C` (`B>0`), a Hopf pair
      `±iω` is a root iff the surface `Σ := A·B − C = 0`, with frequency `ω = √B` (`hopf_cubic_surface`,
      = `hopf_deg3`); on the strong-grid side `Σ>0` it is Hurwitz (`cubic_stable_of_surface_pos`).

  The model-specific parts (`H'>0`; the explicit `Σ_iq, Σ_id`; existence/IVT in `Lg`; ordering
  `Lg_id*>Lg_iq*`; frequency limit `√(Vg·Ki_pll)`; 4D embedding) are symbolic derivations on the
  explicit field — see `derive_lfilter.py` (status reported there).  Those are NOT Lean certificates.
  No `sorry`.
-/
import GFL.Model
import GFL.HopfFold

namespace GFL

open Matrix

set_option linter.unusedSimpArgs false

/-- The Schur-reduced 2D PLL pendulum matrix `[[0, H],[−Ki, −Kp·H]]`. -/
noncomputable def pendulumMat (H Ki Kp : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (H : ℂ); -(Ki : ℂ), -(Kp : ℂ) * (H : ℂ)]

/-- **Theorem 1, char poly.**  `det(z·I − pendulumMat) = z² + (Kp·H)·z + (Ki·H)`. -/
theorem pll_pendulum_charpoly (H Ki Kp : ℝ) (z : ℂ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - pendulumMat H Ki Kp).det
      = z ^ 2 + ((Kp * H : ℝ) : ℂ) * z + ((Ki * H : ℝ) : ℂ) := by
  have hM : z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - pendulumMat H Ki Kp
      = !![z, -(H : ℂ); (Ki : ℂ), z + (Kp : ℂ) * (H : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pendulumMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [hM, Matrix.det_fin_two_of]
  push_cast; ring

/-- **Theorem 1 (2D PLL pendulum is always stable).**  If `H' > 0` (and `Ki_pll, Kp_pll > 0`) then
every root of the pendulum char poly `λ² + Kp_pll·H'·λ + Ki_pll·H'` has `Re < 0`.  (Apply
`stable_deg2_of_pos` with `a₁ = Kp_pll·H' > 0`, `a₂ = Ki_pll·H' > 0`.)  Hence the L-filter
quasi-static PLL reduction is structurally blind to the engineering Hopf. -/
theorem pll_pendulum_stable (H' Ki_pll Kp_pll : ℝ) (hH : 0 < H') (hKi : 0 < Ki_pll)
    (hKp : 0 < Kp_pll) (z : ℂ)
    (hz : z ^ 2 + ((Kp_pll * H' : ℝ) : ℂ) * z + ((Ki_pll * H' : ℝ) : ℂ) = 0) : z.re < 0 :=
  stable_deg2_of_pos (Kp_pll * H') (Ki_pll * H') (mul_pos hKp hH) (mul_pos hKi hH) z hz

/-- **Theorem 2.c / 3 (cubic Hopf surface).**  For a 3-state reduction with char poly
`s³ + A·s² + B·s + C` and `B > 0`: a pure-imaginary pair `±iω` is a root iff the Hopf surface
`Σ := A·B − C = 0`, and then the crossing frequency is `ω = √B`.  (= `hopf_deg3`.) -/
theorem hopf_cubic_surface (A B Cc : ℝ) (hB : 0 < B) :
    (∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 3 + (A : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + (B : ℂ) * ((ω : ℂ) * Complex.I) + (Cc : ℂ) = 0) ↔ Cc = A * B :=
  hopf_deg3 A B Cc hB

/-- **Theorem 2.c / 3, stability side.**  On the strong-grid side `Σ := A·B − C > 0` (with
`A, B, C > 0`) the 3-state reduction is Hurwitz (`stable_deg3_of_pos`); crossing `Σ = 0` is exactly
where a conjugate pair reaches the imaginary axis. -/
theorem cubic_stable_of_surface_pos (A B Cc : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < Cc)
    (hSig : 0 < A * B - Cc) (z : ℂ)
    (hz : z ^ 3 + (A : ℂ) * z ^ 2 + (B : ℂ) * z + (Cc : ℂ) = 0) : z.re < 0 :=
  stable_deg3_of_pos A B Cc hA hB hC (by linarith) z hz

end GFL
