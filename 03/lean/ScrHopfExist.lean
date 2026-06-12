/-
  SCR-Hopf — existence + genuineness FROM THE STRUCTURE OF χₙ (no numerics, no operating point).

  The point the boundary question asks ("why 2D has no SCR-Hopf, 3D/4D do, and is it a GENUINE Hopf")
  is answered by the ALGEBRAIC FORM of the Routh–Hurwitz condition χₙ, parametrically:

   * `hopf_deg4` — the deg-4 GENUINE-Hopf guard (analogue of `hopf_deg3`): a pure-imaginary pair ±iω
     (ω>0) of `λ⁴+a₁λ³+a₂λ²+a₃λ+a₄` exists ⟺ `χ₄ := a₁a₂a₃ − a₃² − a₁²a₄ = 0`, GIVEN `a₁>0, a₃>0`;
     then `ω² = a₃/a₁ > 0`.  The `a₁,a₃>0` hypotheses EXCLUDE the spurious `ω²<0` case
     (`fold_hopf_Psi_spurious`).  Frequency is pinned: `ω=√(a₃/a₁)`.

   * `chi3_root_off_fold` — χ₃ is AFFINE in the error J13: `χ₃ = Kp_pll·gθ·Ψ̃ + J13·(slope)`, slope =
     `J21·(Kp_pll²·gθ − Kp_pll·J11 − Ki_pll)`.  When slope ≠ 0 it HAS a root `J13* = −Kp_pll·gθ·Ψ̃/slope`
     — and that root is at ARBITRARY gθ (including gθ≠0, i.e. OFF the fold gθ=0).  So 3D admits a Hopf
     surface distinct from the fold, by solving a LINEAR equation — no numerics, no implicit equilibrium.

   * `chi2_no_root_off_fold` — χ₂ = Kp_pll·gθ has NO error term, so χ₂ ≠ 0 whenever gθ ≠ 0: 2D's only
     boundary is the fold gθ=0.  This is the dimension dependence: the error term, which separates Hopf
     from fold, is structurally absent at deg 2 and appears from deg 3.

   * `chi3_genuine_hopf_off_fold` — combine: at `J13*`, if `a₂>0` (open domain) the 3D system has a
     GENUINE Hopf (`hopf_deg3`, ω=√a₂>0) at gθ≠0 — existence + genuineness, off the fold.

  All `ring` / `nlinarith` / re-im; abstract in the entries.  `#print axioms` clean, no `sorry`.
-/
import GFL.ScrHopf
import GFL.HopfFold

namespace GFL

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### Deg-4 genuine-Hopf guard (excludes spurious ω²<0) -/

/-- **`hopf_deg4` — genuine Hopf at deg 4.**  For `λ⁴+a₁λ³+a₂λ²+a₃λ+a₄` with `a₁>0, a₃>0`: a
pure-imaginary pair `±iω` (ω>0) is a root ⟺ the Routh–Hurwitz Hopf condition `χ₄ = a₁a₂a₃−a₃²−a₁²a₄ =
0`.  The crossing frequency is `ω = √(a₃/a₁) > 0` — the `a₁,a₃>0` hypotheses force `ω²=a₃/a₁>0`,
EXCLUDING the spurious `ω²<0` case.  (Deg-4 analogue of `hopf_deg3`; the genuine, not-spurious guard.) -/
theorem hopf_deg4 (a₁ a₂ a₃ a₄ : ℝ) (h₁ : 0 < a₁) (h₃ : 0 < a₃) :
    (∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 4 + (a₁ : ℂ) * ((ω : ℂ) * Complex.I) ^ 3
        + (a₂ : ℂ) * ((ω : ℂ) * Complex.I) ^ 2 + (a₃ : ℂ) * ((ω : ℂ) * Complex.I) + (a₄ : ℂ) = 0)
      ↔ a₁ * a₂ * a₃ - a₃ ^ 2 - a₁ ^ 2 * a₄ = 0 := by
  constructor
  · rintro ⟨ω, hω, hroot⟩
    have hre : ω ^ 4 - a₂ * ω ^ 2 + a₄ = 0 := by
      have h := congrArg Complex.re hroot
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, Complex.one_re,
        Complex.one_im, one_mul, Complex.zero_re, Complex.zero_im, mul_zero, mul_one,
        zero_mul, sub_zero, zero_sub, add_zero, zero_add] at h
      linear_combination h
    have him : ω * (a₃ - a₁ * ω ^ 2) = 0 := by
      have h := congrArg Complex.im hroot
      simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, Complex.one_re,
        Complex.one_im, one_mul, Complex.zero_re, Complex.zero_im, mul_zero, mul_one,
        zero_mul, sub_zero, zero_sub, add_zero, zero_add] at h
      linear_combination h
    have hω2 : a₁ * ω ^ 2 = a₃ := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h (ne_of_gt hω)
      · linarith
    linear_combination -a₁ ^ 2 * hre + (a₁ * ω ^ 2 + a₃ - a₁ * a₂) * hω2
  · intro hχ
    have ht : (0 : ℝ) < a₃ / a₁ := div_pos h₃ h₁
    have ha1 : a₁ ≠ 0 := ne_of_gt h₁
    set w := Real.sqrt (a₃ / a₁) with hw
    have hkey : a₁ * w ^ 2 = a₃ := by rw [hw, Real.sq_sqrt ht.le]; field_simp
    refine ⟨w, Real.sqrt_pos.mpr ht, ?_⟩
    have hre : w ^ 4 - a₂ * w ^ 2 + a₄ = 0 := by
      have h1 : a₁ ^ 2 * (w ^ 4 - a₂ * w ^ 2 + a₄) = 0 := by
        linear_combination (-1 : ℝ) * hχ + (2 * a₃ - a₂ * a₁ + a₁ * w ^ 2 - a₃) * hkey
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 ha1)
    rw [Complex.ext_iff]
    constructor
    · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, Complex.one_re,
        Complex.one_im, one_mul, Complex.zero_re, Complex.zero_im, mul_zero, mul_one,
        zero_mul, sub_zero, zero_sub, add_zero, zero_add]
      linear_combination hre
    · simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, Complex.one_re,
        Complex.one_im, one_mul, Complex.zero_re, Complex.zero_im, mul_zero, mul_one,
        zero_mul, sub_zero, zero_sub, add_zero, zero_add]
      linear_combination (-w) * hkey

/-! ### Existence of the Hopf off the fold, from the affine/linear structure of χ₃ -/

/-- **χ₃ has a root OFF the fold — by solving a linear equation.**  `χ₃ = Kp_pll·gθ·Ψ̃ + J13·slope` is
affine in the error `J13` (slope `= J21·(Kp_pll²·gθ − Kp_pll·J11 − Ki_pll)`).  If `slope ≠ 0` then
`J13* := −Kp_pll·gθ·Ψ̃ / slope` makes `χ₃ = 0` — for ARBITRARY `gθ` (in particular `gθ ≠ 0`, off the
fold).  So the 3D Hopf surface `{χ₃=0}` is non-empty and distinct from the fold `{gθ=0}` — purely from
the structure, no numerics. -/
theorem chi3_root_off_fold (J11 J21 gθ Kp_pll Ki_pll : ℝ)
    (hslope : J21 * (Kp_pll ^ 2 * gθ - Kp_pll * J11 - Ki_pll) ≠ 0) :
    ∃ J13 : ℝ, (Kp_pll * gθ - J11) * (Ki_pll * gθ - J11 * Kp_pll * gθ + J13 * J21 * Kp_pll)
        - (-Ki_pll * (J11 * gθ - J13 * J21))
      = 0 := by
  refine ⟨-(Kp_pll * gθ * (J11 ^ 2 - Kp_pll * J11 * gθ + Ki_pll * gθ))
            / (J21 * (Kp_pll ^ 2 * gθ - Kp_pll * J11 - Ki_pll)), ?_⟩
  rw [chi3_droop_decomp]
  have h1 : -(Kp_pll * gθ * (J11 ^ 2 - Kp_pll * J11 * gθ + Ki_pll * gθ))
              / (J21 * (Kp_pll ^ 2 * gθ - Kp_pll * J11 - Ki_pll))
            * J21 * (Kp_pll ^ 2 * gθ - Kp_pll * J11 - Ki_pll)
          = -(Kp_pll * gθ * (J11 ^ 2 - Kp_pll * J11 * gθ + Ki_pll * gθ)) := by
    rw [mul_assoc]
    exact div_mul_cancel₀ _ hslope
  linarith [h1]

/-- **2D has no root off the fold.**  `χ₂ = Kp_pll·gθ` has no error term, so `χ₂ ≠ 0` whenever
`gθ ≠ 0` and `Kp_pll ≠ 0`: the 2D boundary is exactly the fold `gθ = 0`, never a Hopf at `gθ ≠ 0`.
This is the dimension dependence — the separating error term is absent at deg 2. -/
theorem chi2_no_root_off_fold (gθ Kp_pll : ℝ) (hKp : Kp_pll ≠ 0) (hg : gθ ≠ 0) :
    Kp_pll * gθ ≠ 0 := mul_ne_zero hKp hg

/-- **3D genuine Hopf off the fold (existence + genuineness, from structure).**  At `J13*` (where
`χ₃=0`, `chi3_root_off_fold`), if `a₂ = Ki_pll·gθ − J11·Kp_pll·gθ + J13*·J21·Kp_pll > 0` then the cubic
`M_3D` has a GENUINE pure-imaginary pair `±i√a₂` (`hopf_deg3`) — a Hopf at `gθ ≠ 0`, off the fold, NOT
spurious.  (`a₂>0` is an open condition on the parameters; this is the parametric SCR-Hopf branch.) -/
theorem chi3_genuine_hopf_off_fold (J11 J13 J21 gθ Kp_pll Ki_pll : ℝ)
    (ha2 : 0 < Ki_pll * gθ - J11 * Kp_pll * gθ + J13 * J21 * Kp_pll)
    (hχ : (Kp_pll * gθ - J11) * (Ki_pll * gθ - J11 * Kp_pll * gθ + J13 * J21 * Kp_pll)
        - (-Ki_pll * (J11 * gθ - J13 * J21)) = 0) :
    ∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 3 + ((Kp_pll * gθ - J11 : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + ((Ki_pll * gθ - J11 * Kp_pll * gθ + J13 * J21 * Kp_pll : ℝ) : ℂ) * ((ω : ℂ) * Complex.I)
        + ((-Ki_pll * (J11 * gθ - J13 * J21) : ℝ) : ℂ) = 0 := by
  rw [hopf_deg3 _ _ _ ha2]
  linarith [hχ]

end GFL
