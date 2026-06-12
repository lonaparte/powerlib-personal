/-
  SCR-Hopf — the PHYSICAL SCR axis, parametric.  The earlier chain (ScrHopfAnchor/ScrHopfCubic) puts
  the Hopf existence on the abstract gθ axis (one Jacobian entry).  The physical question is on the grid
  inductance Lg ↔ short-circuit ratio SCR.  This file adds the parametric physical layer — WITHOUT any
  operating-point numbers (no SCR ≈ 0.0346, no degree-22 oracle): the char-poly coefficients are abstract
  continuous functions `a₁..a₄ : ℝ → ℝ` of Lg (the model supplies them), and the SCR↔Lg conversion is a
  parametric strictly-decreasing map.

   * `scrOfLg` — SCR(Lg) = Vn²/(Sn·Lg·wn·zfac), parametric in the rated voltage `Vn`, rated power `Sn`,
     base frequency `wn`, and impedance factor `zfac = |Z|/(Lg·wn) = √(1+1/(X/R)²) ≥ 1`.
   * `scrOfLg_pos` / `scrOfLg_strictAntiOn` — SCR > 0, and SCR is STRICTLY DECREASING in Lg: a weaker grid
     (larger inductance) ⟺ smaller SCR.  This is the physical grid-strength ordering, parametric.
   * `scr_hopf_of_lg_hopf` — lift the Hopf existence to the physical axis: if χ₄ (in the Lg-dependent
     coefficients) changes sign across `[Lg₀,Lg₁] ⊂ (0,∞)`, there is a Hopf at some physical `Lg*∈(Lg₀,Lg₁)`,
     and the corresponding `SCR* = scrOfLg Lg*` lies in `(scrOfLg Lg₁, scrOfLg Lg₀)` — the strong/weak-grid
     SCR interval (note the anti-monotone flip).  The SCR-Hopf boundary is a parametric value, not a number.
   * `scr_genuine_hopf_of_lg` — that boundary is a GENUINE Hopf (`hopf_deg4`, ω²=a₃/a₁>0) at a positive SCR
     when `a₁,a₃>0` on the interval.  End-to-end physical-axis SCR-Hopf, parametric.

  SCOPE (honest).  `a₁..a₄(Lg)` (the J(Lg) coefficient maps), the sign change, and `a₁,a₃>0` are HYPOTHESES
  — the model layer supplies the maps; numerically they hold at the GFL baseline (the SCR≈0.0346 boundary),
  but here everything is symbolic.  UNCONDITIONAL and parametric: the SCR↔Lg conversion, its strict
  monotonicity, the interval lift, and genuineness via `hopf_deg4`.  No Singular oracle, no ℚ coefficients,
  no operating-point numbers — the physical SCR boundary as a parametric image of the Lg-Hopf existence.
-/
import GFL.ScrHopfCubic

namespace GFL

open Set

set_option linter.unusedVariables false

/-- **SCR as a function of grid inductance.**  `SCR(Lg) = Vn² / (Sn·Lg·wn·zfac)` — `Vn` rated (line-line)
voltage, `Sn` rated power, `wn` base angular frequency, `zfac = |Z|/(Lg·wn) ≥ 1` the impedance factor
(`= √(1+1/(X/R)²)`).  Parametric; no operating-point numbers. -/
noncomputable def scrOfLg (Vn Sn wn zfac Lg : ℝ) : ℝ := Vn ^ 2 / (Sn * Lg * wn * zfac)

/-- **SCR is positive** for positive parameters and grid inductance. -/
theorem scrOfLg_pos (Vn Sn wn zfac Lg : ℝ) (hVn : 0 < Vn) (hSn : 0 < Sn) (hwn : 0 < wn)
    (hz : 0 < zfac) (hLg : 0 < Lg) : 0 < scrOfLg Vn Sn wn zfac Lg := by
  unfold scrOfLg; positivity

/-- **SCR is strictly decreasing in Lg** (on `Lg > 0`).  A weaker grid (larger inductance) ⟺ a smaller
short-circuit ratio — the physical grid-strength ordering, parametric. -/
theorem scrOfLg_strictAntiOn (Vn Sn wn zfac : ℝ) (hVn : 0 < Vn) (hSn : 0 < Sn) (hwn : 0 < wn)
    (hz : 0 < zfac) : StrictAntiOn (scrOfLg Vn Sn wn zfac) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  simp only [scrOfLg]
  gcongr

/-- **Lift the Hopf existence to the physical SCR axis.**  If the Routh–Hurwitz quantity `χ₄` in the
Lg-dependent coefficients `a₁..a₄` changes sign across `[Lg₀,Lg₁] ⊂ (0,∞)`, then there is a Hopf at some
physical `Lg*∈(Lg₀,Lg₁)`, and the corresponding `SCR* = scrOfLg Lg*` lies in the SCR interval
`(scrOfLg Lg₁, scrOfLg Lg₀)` (anti-monotone: strong grid = small Lg = large SCR).  The SCR-Hopf boundary
is a parametric value `scrOfLg Lg*`, not an operating-point number. -/
theorem scr_hopf_of_lg_hopf (Vn Sn wn zfac : ℝ) (hVn : 0 < Vn) (hSn : 0 < Sn) (hwn : 0 < wn)
    (hz : 0 < zfac) (a₁ a₂ a₃ a₄ : ℝ → ℝ)
    (h1 : Continuous a₁) (h2 : Continuous a₂) (h3 : Continuous a₃) (h4 : Continuous a₄)
    {Lg₀ Lg₁ : ℝ} (hLg0 : 0 < Lg₀) (hlt : Lg₀ < Lg₁)
    (hlo : a₁ Lg₀ * a₂ Lg₀ * a₃ Lg₀ - a₃ Lg₀ ^ 2 - a₁ Lg₀ ^ 2 * a₄ Lg₀ < 0)
    (hhi : 0 < a₁ Lg₁ * a₂ Lg₁ * a₃ Lg₁ - a₃ Lg₁ ^ 2 - a₁ Lg₁ ^ 2 * a₄ Lg₁) :
    ∃ Lg, Lg ∈ Set.Ioo Lg₀ Lg₁ ∧
      a₁ Lg * a₂ Lg * a₃ Lg - a₃ Lg ^ 2 - a₁ Lg ^ 2 * a₄ Lg = 0 ∧
      scrOfLg Vn Sn wn zfac Lg ∈ Set.Ioo (scrOfLg Vn Sn wn zfac Lg₁) (scrOfLg Vn Sn wn zfac Lg₀) := by
  obtain ⟨Lg, hLg, hroot⟩ := hopf_root_ivt a₁ a₂ a₃ a₄ h1 h2 h3 h4 hlt hlo hhi
  have hanti := scrOfLg_strictAntiOn Vn Sn wn zfac hVn hSn hwn hz
  have hLgpos : (0 : ℝ) < Lg := lt_trans hLg0 hLg.1
  refine ⟨Lg, hLg, hroot, ?_, ?_⟩
  · exact hanti (Set.mem_Ioi.mpr hLgpos) (Set.mem_Ioi.mpr (lt_trans hLgpos hLg.2)) hLg.2
  · exact hanti (Set.mem_Ioi.mpr hLg0) (Set.mem_Ioi.mpr hLgpos) hLg.1

/-- **Genuine SCR-Hopf on the physical axis (parametric capstone).**  Under the sign change + `a₁,a₃>0`
on `(Lg₀,Lg₁)`, there is a physical `Lg*` with a GENUINE pure-imaginary pair `±iω` (ω²=a₃/a₁>0,
`hopf_deg4`) at a POSITIVE `SCR* = scrOfLg Lg* > 0`.  The end-to-end physical SCR-Hopf, parametric — the
boundary's SCR is the symbolic `scrOfLg Lg*`, not a reproduced number. -/
theorem scr_genuine_hopf_of_lg (Vn Sn wn zfac : ℝ) (hVn : 0 < Vn) (hSn : 0 < Sn) (hwn : 0 < wn)
    (hz : 0 < zfac) (a₁ a₂ a₃ a₄ : ℝ → ℝ)
    (h1 : Continuous a₁) (h2 : Continuous a₂) (h3 : Continuous a₃) (h4 : Continuous a₄)
    {Lg₀ Lg₁ : ℝ} (hLg0 : 0 < Lg₀) (hlt : Lg₀ < Lg₁)
    (hlo : a₁ Lg₀ * a₂ Lg₀ * a₃ Lg₀ - a₃ Lg₀ ^ 2 - a₁ Lg₀ ^ 2 * a₄ Lg₀ < 0)
    (hhi : 0 < a₁ Lg₁ * a₂ Lg₁ * a₃ Lg₁ - a₃ Lg₁ ^ 2 - a₁ Lg₁ ^ 2 * a₄ Lg₁)
    (hpos : ∀ Lg ∈ Set.Ioo Lg₀ Lg₁, 0 < a₁ Lg ∧ 0 < a₃ Lg) :
    ∃ Lg, Lg ∈ Set.Ioo Lg₀ Lg₁ ∧ 0 < scrOfLg Vn Sn wn zfac Lg ∧
      ∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 4 + ((a₁ Lg : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 3
        + ((a₂ Lg : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + ((a₃ Lg : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((a₄ Lg : ℝ) : ℂ) = 0 := by
  obtain ⟨Lg, hLg, hroot, _⟩ :=
    scr_hopf_of_lg_hopf Vn Sn wn zfac hVn hSn hwn hz a₁ a₂ a₃ a₄ h1 h2 h3 h4 hLg0 hlt hlo hhi
  obtain ⟨hp1, hp3⟩ := hpos Lg hLg
  have hLgpos : (0 : ℝ) < Lg := lt_trans hLg0 hLg.1
  refine ⟨Lg, hLg, scrOfLg_pos Vn Sn wn zfac Lg hVn hSn hwn hz hLgpos, ?_⟩
  exact (hopf_deg4 (a₁ Lg) (a₂ Lg) (a₃ Lg) (a₄ Lg) hp1 hp3).mpr hroot

end GFL
