/-
  Fold/Hopf separation — lossless L-filter GFL, P-only outer loop (anchored small models).

  Model (lossless Rf=Rg=0): state (i_d,i_q,η,θ_e).  Work point i_d*=P_ref/(1.5Vg), i_q*=−Q_ref/(1.5Vg),
  η*=0, θ_e* from v_cqc=0.  GUARD G1 (genuine equilibrium of each (A) submodel, retained-state RHS=0)
  is VERIFIED for the keep-i_q model M_3D^q (i_q RHS* = 2·P_ref·wn·(C²+S²−1)/(3Vg) = 0 on the unit
  circle) and FAILS for keep-i_d (i_d RHS* = −Kpi·i_d*/Lf ≠ 0) — so M_3D^q is the valid 3D model.
  (verify_fold_hopf.py / verify_fold_hopf_b.py; idealized dropped current = constant ⇒ submatrix, not
  the earlier non-fixed-point hybrid.)

  The sympy derivation (gen_lean_foldhopf.py) gives, at that point, the M_3D^q submatrix entries
    J11 = ∂F_iq/∂i_q  = −Kpi·(2C²+3C·Kp_P·Vg+2S²)/(2Lf)      (current-loop pole)
    J13 = ∂F_iq/∂θ_e  = 0                                    (q-current decouples from θ_e here)
    J21 = ∂v_cqc/∂i_q,  gθ = ∂v_cqc/∂θ_e = −Φ/(3Lf·Vg(Lf+Lg))   (PLL stiffness; Φ = fold factor)
  so M_3D^q = [[J11,0,0],[J21,0,gθ],[−Kp_pll·J21,−Ki_pll,−Kp_pll·gθ]].

  RESULTS (all machine-checked below; abstract in J11,J21,gθ,Kp_pll,Ki_pll):
  * (a) `fold_hopf_2D_no_isolated_hopf` — the 2D PLL reduction `λ²+Kp_pll·gθ·λ+Ki_pll·gθ` has NO
    genuine Hopf: any pure-imaginary root forces ω=0 ∧ gθ=0 (the degenerate FOLD det=0).
  * (b) `fold_hopf_3D_charpoly_factor` — BECAUSE J13=0 the 3D char poly FACTORS:
        det(λI−M_3D^q) = (λ − J11)·(λ² + Kp_pll·gθ·λ + Ki_pll·gθ),
    i.e. 3D spectrum = {current pole J11} ∪ {2D pendulum}.  The Routh–Hurwitz quantity factors as
        Σ := a1a2−a3 = Kp_pll·gθ·Ψ̃,   Ψ̃ := J11² − Kp_pll·J11·gθ + Ki_pll·gθ   (`fold_hopf_RH_factor`)
    with the fold factor gθ SHARED with the 2D fold (det = −a3 = J11·Ki_pll·gθ).
  * (c) `fold_hopf_current_pole` — a1(3D) − a1(2D) = −J11 = +Kpi·(2C²+3C·Kp_P·Vg+2S²)/(2Lf) > 0: the
    3D leading coefficient gains the current pole the 2D lacks (the source of the extra λ−J11 factor).

  HONEST SHARPENING of the problem's OPEN note (`fold_hopf_Psi_spurious`):  Ψ̃ = a2 + J11², so Ψ̃=0 ⟹
  a2 = −J11² ≤ 0 ⟹ the Hopf frequency ω²=a2 < 0 — NOT a genuine Hopf.  Together with the factorization,
  the (A) 3D model has NO isolated Hopf; the only imaginary-axis crossing is the fold gθ=0, exactly
  as in 2D.  So "Ψ=0 = independent Hopf" does NOT hold — Ψ is a spurious factor of Δ₂ here.  Moreover
  `J13 = ∂F_iq/∂θ_e = 0` at the work point holds even WITH losses (Rf,Rg≠0 — checked symbolically), so
  this is a structural feature of the IDEALISED-CURRENT (A) reduction, not of losslessness: a genuine
  3D Hopf needs the currents kept DYNAMIC (the full model, J13≠0), which stays OPEN.  No `sorry`.
-/
import GFL.LFilterHopf

namespace GFL

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### (a) 2D ideal-current PLL reduction — fold only, no isolated Hopf -/

/-- **(a) No isolated Hopf in 2D.**  The reduction `M_2D = [[0,gθ],[−Ki_pll,−Kp_pll·gθ]]` has char
poly `λ² + (Kp_pll·gθ)λ + (Ki_pll·gθ)` — both coefficients ∝ gθ.  Hence any pure-imaginary root `iω`
forces `ω = 0 ∧ gθ = 0`: the only imaginary-axis crossing is the degenerate origin (`det = Ki_pll·gθ
= 0`, a FOLD), never a genuine `ω ≠ 0` Hopf. -/
theorem fold_hopf_2D_no_isolated_hopf (gθ Kp_pll Ki_pll ω : ℝ)
    (hKp : 0 < Kp_pll) (hKi : 0 < Ki_pll)
    (h : ((ω : ℂ) * Complex.I) ^ 2 + ((Kp_pll * gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I)
        + ((Ki_pll * gθ : ℝ) : ℂ) = 0) :
    ω = 0 ∧ gθ = 0 := by
  have him : Kp_pll * gθ * ω = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] using this
  have hre : -(ω ^ 2) + Ki_pll * gθ = 0 := by
    have := congrArg Complex.re h
    simpa [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] using this
  have hgω : gθ * ω = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (ne_of_gt hKp)
      · exact mul_eq_zero.mpr (Or.inl h2)
    · exact mul_eq_zero.mpr (Or.inr h1)
  have hω : ω = 0 := by
    by_contra hω0
    have hg : gθ = 0 := by rcases mul_eq_zero.mp hgω with h2 | h2; exact h2; exact absurd h2 hω0
    rw [hg, mul_zero] at hre
    exact hω0 ((pow_eq_zero_iff two_ne_zero).mp (by linarith))
  refine ⟨hω, ?_⟩
  rw [hω] at hre
  have : Ki_pll * gθ = 0 := by simpa using hre
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd h2 (ne_of_gt hKi)
  · exact h2

/-! ### (b) The anchored 3D model M_3D^q — char poly factors (J13=0) -/

/-- The keep-`i_q` submatrix at the anchored equilibrium (rows/cols `i_q, η, θ_e`); `∂F_iq/∂θ_e = 0`. -/
noncomputable def M3q (J11 J21 gθ Kp_pll Ki_pll : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![J11, 0, 0; J21, 0, gθ; -Kp_pll * J21, -Ki_pll, -Kp_pll * gθ]

/-- **(b) 3D char poly FACTORS.**  Because `J13 = ∂F_iq/∂θ_e = 0`, the q-current row decouples and
`det(λI − M_3D^q) = (λ − J11)·(λ² + Kp_pll·gθ·λ + Ki_pll·gθ)` — the 3D spectrum is the current pole
`J11` together with the 2D PLL pendulum.  (Note: independent of `J21`.) -/
theorem fold_hopf_3D_charpoly_factor (J11 J21 gθ Kp_pll Ki_pll lam : ℝ) :
    (lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - M3q J11 J21 gθ Kp_pll Ki_pll).det
      = (lam - J11) * (lam ^ 2 + (Kp_pll * gθ) * lam + Ki_pll * gθ) := by
  have hM : lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - M3q J11 J21 gθ Kp_pll Ki_pll
      = !![lam - J11, 0, 0; -J21, lam, -gθ; Kp_pll * J21, Ki_pll, lam + Kp_pll * gθ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M3q, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [hM, Matrix.det_fin_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
    Matrix.cons_val', Matrix.head_fin_const]
  ring

/-- **(b) Routh–Hurwitz factorisation.**  With `a1 = Kp_pll·gθ − J11`, `a2 = Ki_pll·gθ − Kp_pll·J11·gθ`,
`a3 = −J11·Ki_pll·gθ` (the coefficients from the factored char poly), the cubic Hurwitz quantity is
`Σ = a1·a2 − a3 = Kp_pll·gθ·Ψ̃` with `Ψ̃ = J11² − Kp_pll·J11·gθ + Ki_pll·gθ`.  The fold factor `gθ` is
shared with the 2D fold; `Ψ̃` is the second (independent) factor. -/
theorem fold_hopf_RH_factor (J11 gθ Kp_pll Ki_pll : ℝ) :
    (Kp_pll * gθ - J11) * (Ki_pll * gθ - Kp_pll * J11 * gθ) - (-J11 * Ki_pll * gθ)
      = Kp_pll * gθ * (J11 ^ 2 - Kp_pll * J11 * gθ + Ki_pll * gθ) := by ring

/-- **Fold is `gθ = 0`, shared with 2D.**  `det(M_3D^q) = −a3 = J11·Ki_pll·gθ`, so the fold (`det = 0`)
is `gθ = 0` whenever `J11 ≠ 0, Ki_pll ≠ 0` — exactly the 2D fold condition. -/
theorem fold_hopf_fold_is_gθ (J11 gθ Kp_pll Ki_pll : ℝ) (hJ : J11 ≠ 0) (hKi : Ki_pll ≠ 0) :
    (-J11 * Ki_pll * gθ) = 0 ↔ gθ = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (by linarith : J11 = 0) hJ
      · exact absurd h2 hKi
    · exact h1
  · intro h; rw [h, mul_zero]

/-- **HONEST SHARPENING — Ψ̃ is spurious losslessly.**  `Ψ̃ = a2 + J11²`, so `Ψ̃ = 0 ⟹ a2 = −J11² ≤ 0`.
A genuine Hopf needs `ω² = a2 > 0`; hence `Ψ̃ = 0` is NOT a Hopf (no real crossing frequency).  Combined
with `fold_hopf_3D_charpoly_factor`, the lossless 3D model has no isolated Hopf — only the fold `gθ=0`. -/
theorem fold_hopf_Psi_spurious (J11 gθ Kp_pll Ki_pll : ℝ)
    (hΨ : J11 ^ 2 - Kp_pll * J11 * gθ + Ki_pll * gθ = 0) :
    (Ki_pll * gθ - Kp_pll * J11 * gθ) = -(J11 ^ 2) ∧ (Ki_pll * gθ - Kp_pll * J11 * gθ) ≤ 0 := by
  have ha2 : Ki_pll * gθ - Kp_pll * J11 * gθ = -(J11 ^ 2) := by linarith [hΨ]
  exact ⟨ha2, by rw [ha2]; nlinarith [sq_nonneg J11]⟩

/-! ### (c) The current pole — the term 3D has that 2D lacks -/

/-- **(c) Current pole.**  `a1(3D) − a1(2D) = (Kp_pll·gθ − J11) − Kp_pll·gθ = −J11`.  At the work point
`J11 = −Kpi·(2C²+3C·Kp_P·Vg+2S²)/(2Lf)`, so the extra coefficient `−J11 = Kpi·(…)/(2Lf) > 0` (with
`Kpi,Lf>0` and the bracket `> 0`) is the stabilizing current-loop pole absent from the 2D reduction. -/
theorem fold_hopf_current_pole (J11 gθ Kp_pll : ℝ) :
    (Kp_pll * gθ - J11) - Kp_pll * gθ = -J11 := by ring

theorem fold_hopf_current_pole_pos (C S Vg Lf Kpi Kp_P : ℝ)
    (hLf : 0 < Lf) (hKpi : 0 < Kpi) (hq : 0 < 2 * C ^ 2 + 3 * C * Kp_P * Vg + 2 * S ^ 2) :
    0 < Kpi * (2 * C ^ 2 + 3 * C * Kp_P * Vg + 2 * S ^ 2) / (2 * Lf) :=
  div_pos (mul_pos hKpi hq) (by linarith)

end GFL
