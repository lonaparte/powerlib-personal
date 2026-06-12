/-
  SCR-Hopf — the PARAMETRIC dimension-threshold theorem (the punchline), no embedded coefficients.
  This drops the ℤ[Lg]-oracle route (ScrHopfNumeric / ScrHopf3DNumeric, which pinned GFL params and
  norm_num'd a 600-digit polynomial).  Here every theorem is PARAMETRIC in the char-poly coefficient
  maps `aᵢ : ℝ → ℝ` (functions of the grid parameter Lg, supplied by the model); the conclusion is
  existence + genuineness of a Hopf at a POSITIVE SCR.  GFL/lossy/lossless/3D are then APPLICATIONS:
  instantiate the `aᵢ` and discharge a handful of structural inequalities — the specific SCR number is
  NOT in any Lean statement (it is computed externally by sympy/Singular/simulation).

   * `hopf3_root_ivt` — cubic analogue of ScrAxis.`hopf_root_ivt`: a sign change of `χ₃ = a₁a₂ − a₃`
     gives an interior root (IVT).
   * `scr_genuine_hopf_3D_of_lg` — 3D parametric SCR-Hopf: sign change of χ₃ + `a₂>0` ⟹ a GENUINE
     pure-imaginary pair (`hopf_deg3`, ω=√a₂) at a positive `SCR = scrOfLg Lg*`.
   * (4D is `ScrAxis.scr_genuine_hopf_of_lg`, already proved — the deg-4 analogue.)
   * `scr_hopf_dim_threshold` — THE PUNCHLINE: parametrically, (2D) any pure-imaginary root forces the
     fold `gθ=0` (NO isolated Hopf, unconditional, `fold_hopf_2D_no_isolated_hopf`); while (3D) and (4D)
     DO admit a genuine Hopf at a positive SCR (non-vacuous witnesses).  "2D impossible; 3D, 4D possible."

  SCOPE (honest).  The coefficient maps `aᵢ(Lg)`, the sign change, and the positivity are HYPOTHESES —
  the model layer supplies the `aᵢ`; for GFL they are algebraic in Lg (the equilibrium), satisfy the
  hypotheses numerically (committed ScrHopfNumeric/ScrHopf3DNumeric give the concrete roots SCR≈0.0378
  (4D) / 0.0377 (3D), cross-validated).  The witnesses below are MINIMAL configurations proving the
  parametric theorems fire (non-vacuous).  Unconditional/parametric here: the IVT existence, the
  genuine-Hopf guards (`hopf_deg{3,4}`), the SCR positivity/monotonicity, and the 2D impossibility.
-/
import GFL.ScrAxis

namespace GFL

open Set

set_option linter.unusedVariables false

/-! ### Cubic IVT engine (3D), analogue of `hopf_root_ivt` -/

/-- **Cubic Hopf-root IVT.**  For continuous `a₁,a₂,a₃ : ℝ → ℝ`, if the deg-3 Routh–Hurwitz quantity
`χ₃(x) = a₁a₂ − a₃` is negative at `x₀` and positive at `x₁ > x₀`, it vanishes in `(x₀,x₁)`. -/
theorem hopf3_root_ivt (a₁ a₂ a₃ : ℝ → ℝ)
    (h1 : Continuous a₁) (h2 : Continuous a₂) (h3 : Continuous a₃)
    {x₀ x₁ : ℝ} (hlt : x₀ < x₁)
    (hlo : a₁ x₀ * a₂ x₀ - a₃ x₀ < 0) (hhi : 0 < a₁ x₁ * a₂ x₁ - a₃ x₁) :
    ∃ x ∈ Set.Ioo x₀ x₁, a₁ x * a₂ x - a₃ x = 0 := by
  have hcont : Continuous (fun x => a₁ x * a₂ x - a₃ x) := (h1.mul h2).sub h3
  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun x => a₁ x * a₂ x - a₃ x) x₀)
      ((fun x => a₁ x * a₂ x - a₃ x) x₁) := ⟨hlo, hhi⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hlt.le hcont.continuousOn hmem
  exact ⟨x, hx, hfx⟩

/-! ### 3D parametric SCR-Hopf (deg-3 analogue of `scr_genuine_hopf_of_lg`) -/

/-- **3D parametric SCR-Hopf existence + genuineness.**  Coefficient maps `a₁,a₂,a₃ : ℝ → ℝ` of the grid
parameter Lg; if `χ₃ = a₁a₂ − a₃` changes sign across `[Lg₀,Lg₁] ⊂ (0,∞)` and `a₂ > 0` there, then there
is a GENUINE pure-imaginary pair `±iω` (ω=√a₂>0, `hopf_deg3`) at a POSITIVE `SCR = scrOfLg Lg*`. -/
theorem scr_genuine_hopf_3D_of_lg (Vn Sn wn zfac : ℝ) (hVn : 0 < Vn) (hSn : 0 < Sn) (hwn : 0 < wn)
    (hz : 0 < zfac) (a₁ a₂ a₃ : ℝ → ℝ)
    (h1 : Continuous a₁) (h2 : Continuous a₂) (h3 : Continuous a₃)
    {Lg₀ Lg₁ : ℝ} (hLg0 : 0 < Lg₀) (hlt : Lg₀ < Lg₁)
    (hlo : a₁ Lg₀ * a₂ Lg₀ - a₃ Lg₀ < 0) (hhi : 0 < a₁ Lg₁ * a₂ Lg₁ - a₃ Lg₁)
    (hpos2 : ∀ Lg ∈ Set.Ioo Lg₀ Lg₁, 0 < a₂ Lg) :
    ∃ Lg, Lg ∈ Set.Ioo Lg₀ Lg₁ ∧ 0 < scrOfLg Vn Sn wn zfac Lg ∧
      ∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 3 + ((a₁ Lg : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + ((a₂ Lg : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((a₃ Lg : ℝ) : ℂ) = 0 := by
  obtain ⟨Lg, hLg, hroot⟩ := hopf3_root_ivt a₁ a₂ a₃ h1 h2 h3 hlt hlo hhi
  have hLgpos : (0 : ℝ) < Lg := lt_trans hLg0 hLg.1
  refine ⟨Lg, hLg, scrOfLg_pos Vn Sn wn zfac Lg hVn hSn hwn hz hLgpos, ?_⟩
  exact (hopf_deg3 (a₁ Lg) (a₂ Lg) (a₃ Lg) (hpos2 Lg hLg)).mpr (by linarith [hroot])

/-! ### The dimension-threshold theorem (punchline) -/

/-- **SCR-Hopf dimension threshold (parametric punchline).**  In ONE statement, parametric in the PLL
gains and the SCR conversion parameters:
  * **2D** — any pure-imaginary root `iω` of the 2D PLL characteristic polynomial forces the fold
    `gθ = 0`: there is NO isolated Hopf at 2D (unconditional, `fold_hopf_2D_no_isolated_hopf`).
  * **3D** — a GENUINE Hopf at a positive SCR EXISTS (non-vacuous; minimal witness coefficients,
    `scr_genuine_hopf_3D_of_lg`).
  * **4D** — likewise a GENUINE Hopf at a positive SCR EXISTS (`scr_genuine_hopf_of_lg`).
"2D impossible; 3D already possible; 4D possible" — the dimension where the SCR-Hopf becomes possible. -/
theorem scr_hopf_dim_threshold (Kp_pll Ki_pll : ℝ) (hKp : 0 < Kp_pll) (hKi : 0 < Ki_pll)
    (Vn Sn wn zfac : ℝ) (hVn : 0 < Vn) (hSn : 0 < Sn) (hwn : 0 < wn) (hz : 0 < zfac) :
    -- 2D: no isolated Hopf (any pure-imaginary root ⟹ fold gθ=0)
    (∀ gθ ω : ℝ, ((ω : ℂ) * Complex.I) ^ 2 + ((Kp_pll * gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I)
        + ((Ki_pll * gθ : ℝ) : ℂ) = 0 → ω = 0 ∧ gθ = 0)
    -- 3D: a genuine Hopf at positive SCR exists (non-vacuous)
    ∧ (∃ Lg, 0 < scrOfLg Vn Sn wn zfac Lg ∧ ∃ ω : ℝ, 0 < ω ∧
        ((ω : ℂ) * Complex.I) ^ 3 + ((1 : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
          + ((1 : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((2 - 2 * Lg : ℝ) : ℂ) = 0)
    -- 4D: a genuine Hopf at positive SCR exists (non-vacuous)
    ∧ (∃ Lg, 0 < scrOfLg Vn Sn wn zfac Lg ∧ ∃ ω : ℝ, 0 < ω ∧
        ((ω : ℂ) * Complex.I) ^ 4 + ((1 : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 3
          + ((1 : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
          + ((1 : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((1 - 2 * Lg : ℝ) : ℂ) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- 2D
    intro gθ ω h
    exact fold_hopf_2D_no_isolated_hopf gθ Kp_pll Ki_pll ω hKp hKi h
  · -- 3D witness: a₁=a₂=1, a₃(Lg)=2−2Lg, on (1/4, 1); χ₃ = 1 − (2−2Lg) = 2Lg−1 (sign change), a₂=1>0
    obtain ⟨Lg, _, hscr, ω, hω, hpoly⟩ :=
      scr_genuine_hopf_3D_of_lg Vn Sn wn zfac hVn hSn hwn hz
        (fun _ => 1) (fun _ => 1) (fun Lg => 2 - 2 * Lg)
        continuous_const continuous_const (by fun_prop)
        (Lg₀ := 1/4) (Lg₁ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun _ _ => by norm_num)
    exact ⟨Lg, hscr, ω, hω, by simpa using hpoly⟩
  · -- 4D witness: a₁=a₂=a₃=1, a₄(Lg)=1−2Lg, on (1/4, 1); χ₄ = 1 − 1 − (1−2Lg) = 2Lg−1, a₁,a₃=1>0
    obtain ⟨Lg, _, hscr, ω, hω, hpoly⟩ :=
      scr_genuine_hopf_of_lg Vn Sn wn zfac hVn hSn hwn hz
        (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun Lg => 1 - 2 * Lg)
        continuous_const continuous_const continuous_const (by fun_prop)
        (Lg₀ := 1/4) (Lg₁ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun _ _ => ⟨by norm_num, by norm_num⟩)
    exact ⟨Lg, hscr, ω, hω, by simpa using hpoly⟩

/-! ### End-to-end 4D composition (anchor + genuineness + SCR positivity) -/

/-- **End-to-end 4D parametric SCR-Hopf (`scr_hopf_4D_full`).**  Composes the strong-grid-discharged
anchor + genuineness + SCR positivity into one statement: given the leading coefficient `L₃ > 0`, the
fold value `χ₄(0) < 0`, and Routh positivity `a₁,a₃ > 0` on the positives, there is a grid-stiffness
`gθ* > 0` carrying a GENUINE pure-imaginary pair `±iω` (hopf_deg4, ω²=a₃/a₁>0) AND the SCR formula is
positive there.  Parametric in the Jacobian entries; no embedded numbers.  (Bifurcation variable is the
grid-coupling stiffness gθ on which χ₄ is cubic; `scrOfLg` is the SCR map evaluated at it — the literal
gθ↔Lg identification is the model's J(Lg) relation, external.) -/
theorem scr_hopf_4D_full (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ)
    (Vn Sn wn zfac : ℝ) (hVn : 0 < Vn) (hSn : 0 < Sn) (hwn : 0 < wn) (hz : 0 < zfac)
    (hL3 : 0 < ((1:ℝ)*J01*J10*J11*Kp_pll^3 - (1:ℝ)*J00*J11^2*Kp_pll^3 + (1:ℝ)*J00*J01*J10*Kp_pll^3 - (1:ℝ)*J00^2*J11*Kp_pll^3 + (1:ℝ)*J11^2*Kp_pll^2*Ki_pll + (2:ℝ)*J00*J11*Kp_pll^2*Ki_pll + (1:ℝ)*J00^2*Kp_pll^2*Ki_pll - (1:ℝ)*J11*Kp_pll*Ki_pll^2 - (1:ℝ)*J00*Kp_pll*Ki_pll^2))
    (hfold : chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll 0 < 0)
    (hpos : ∀ g : ℝ, 0 < g → 0 < chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g ∧ 0 < chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g) :
    ∃ gθ, 0 < gθ ∧ 0 < scrOfLg Vn Sn wn zfac gθ ∧
      ∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 4 + ((chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 3
        + ((chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + ((chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) = 0 := by
  obtain ⟨gθ, hgθ, hhopf⟩ := chi4_genuine_hopf_leadingpos J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll hL3 hfold hpos
  exact ⟨gθ, hgθ, scrOfLg_pos Vn Sn wn zfac gθ hVn hSn hwn hz hgθ, hhopf⟩

end GFL
