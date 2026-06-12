/-
  SCR-Hopf — (a) fold-separation + (b) IVT existence of the boundary OFF the fold (T_chi4_droop_term_exists,
  T_scr_anchor).  Closes the last mile of ScrHopf4D: the χ₄ decomposition shows the droop term EXISTS; here
  we show it SEPARATES the Hopf from the fold and the boundary EXISTS strictly off the fold, parametrically.

  (a) `chi4_err0_at_fold` — the err=0 part vanishes at the fold gθ=0 (every err0 monomial carries gθ).
      Hence at the fold χ₄ = droop: the DROOP is exactly what survives at gθ=0, so it is the droop that
      can carry the Hopf condition χ₄=0 away from the fold.  (Deg-4 analogue of why err≠0 moves χ₃'s zero.)

  (b) `hopf_root_ivt` — the generic IVT engine, AXIS-AGNOSTIC (the variable may be gθ or SCR): for any
      continuous coefficient maps a₁..a₄ : ℝ→ℝ, if the Routh–Hurwitz quantity χ₄(x)=a₁a₂a₃−a₃²−a₁²a₄
      changes sign on [x₀,x₁] then it has a zero in the open interval (x₀,x₁) — `intermediate_value_Ioo`.
      `chi4_anchor_off_fold` — instantiate at the actual 4D coefficients as functions of gθ (each is AFFINE
      in gθ ⟹ continuous): given χ₄|_{gθ=0} < 0 < χ₄|_{gθ=g₁} (the sign change), there is gθ*∈(0,g₁) with
      χ₄(gθ*)=0 — a Hopf condition STRICTLY off the fold gθ=0.  `chi4_genuine_hopf_anchored` — that off-fold
      zero is a GENUINE Hopf (±iω, ω²=a₃/a₁>0) via `hopf_deg4`, when a₁,a₃>0 on the interval.

  SCOPE (honest, parametric).  The sign change `χ₄|_fold < 0 < χ₄|_strong` is a HYPOTHESIS — the structural
  stand-in for "χ₄ flips sign between the weak-grid (fold) end and the strong-grid end" (numerically
  satisfiable, verify_anchor.py / verify_scr_hopf.py; NON-vacuous).  Lean proves the CONDITIONAL: IF the
  sign change holds THEN the boundary exists off the fold and is a genuine Hopf.  The axis here is gθ (the
  grid-coupling stiffness, fold = {gθ=0}); a literal SCR axis (Lg = Vg²/(SCR·Sbase·ωₙ)) needs the model's
  J(Lg) entry map, which lives in the model layer, not this algebraic file — but `hopf_root_ivt` is
  axis-agnostic, so it yields the SCR anchor verbatim once that continuous J(SCR) map is supplied.
  Contrast deg 2: `chi2_no_root_off_fold` — χ₂ = Kp_pll·gθ has NO off-fold zero (dimension dependence).
-/
import GFL.ScrHopf4D
import Mathlib.Topology.Order.IntermediateValue

namespace GFL
open Matrix Set
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ### (a) The droop is what survives at the fold (err=0 part vanishes at gθ=0) -/

/-- **err=0 part vanishes at the fold.**  Every monomial of the err=0 part `err0` carries a factor
`gθ`, so `err0|_{gθ=0} = 0`.  Combined with `chi4_droop_decomp` (χ₄ = err0 + droop), this gives
`χ₄|_{gθ=0} = droop|_{gθ=0}`: at the fold the only surviving contribution to the Hopf quantity is the
DROOP — it is the droop (∝ J03,J13 ∝ tracking error) that can carry χ₄=0 off the fold gθ=0. -/
theorem chi4_err0_at_fold (J00 J01 J03 J10 J11 J13 J20 J21 gθ Kp_pll Ki_pll : ℝ) (hg : gθ = 0) :
    ((1:ℝ)*J01*J10*J11*gθ^3*Kp_pll^3 - (1:ℝ)*J00*J11^2*gθ^3*Kp_pll^3 + (1:ℝ)*J00*J01*J10*gθ^3*Kp_pll^3 - (1:ℝ)*J00^2*J11*gθ^3*Kp_pll^3 + (1:ℝ)*J11^2*gθ^3*Kp_pll^2*Ki_pll - (1:ℝ)*J01*J10*J11^2*gθ^2*Kp_pll^2 + (2:ℝ)*J00*J11*gθ^3*Kp_pll^2*Ki_pll + (1:ℝ)*J00*J11^3*gθ^2*Kp_pll^2 - (2:ℝ)*J00*J01*J10*J11*gθ^2*Kp_pll^2 + (1:ℝ)*J00^2*gθ^3*Kp_pll^2*Ki_pll + (2:ℝ)*J00^2*J11^2*gθ^2*Kp_pll^2 - (1:ℝ)*J00^2*J01*J10*gθ^2*Kp_pll^2 + (1:ℝ)*J00^3*J11*gθ^2*Kp_pll^2 - (1:ℝ)*J11*gθ^3*Kp_pll*Ki_pll^2 - (1:ℝ)*J11^3*gθ^2*Kp_pll*Ki_pll - (2:ℝ)*J01*J10*J11*gθ^2*Kp_pll*Ki_pll - (1:ℝ)*J01^2*J10^2*J11*gθ*Kp_pll - (1:ℝ)*J00*gθ^3*Kp_pll*Ki_pll^2 - (1:ℝ)*J00*J11^2*gθ^2*Kp_pll*Ki_pll - (2:ℝ)*J00*J01*J10*gθ^2*Kp_pll*Ki_pll + (2:ℝ)*J00*J01*J10*J11^2*gθ*Kp_pll - (1:ℝ)*J00*J01^2*J10^2*gθ*Kp_pll - (1:ℝ)*J00^2*J11*gθ^2*Kp_pll*Ki_pll - (1:ℝ)*J00^2*J11^3*gθ*Kp_pll + (2:ℝ)*J00^2*J01*J10*J11*gθ*Kp_pll - (1:ℝ)*J00^3*gθ^2*Kp_pll*Ki_pll - (1:ℝ)*J00^3*J11^2*gθ*Kp_pll) = 0 := by subst hg; ring

/-! ### (b) IVT existence of the χ₄=0 boundary off the fold (axis-agnostic) -/

/-- **Generic IVT engine for the Hopf boundary.**  For continuous coefficient maps `a₁..a₄ : ℝ → ℝ`,
if the deg-4 Routh–Hurwitz Hopf quantity `χ₄(x) = a₁a₂a₃ − a₃² − a₁²a₄` is negative at `x₀` and
positive at `x₁ > x₀`, then it vanishes somewhere in the OPEN interval `(x₀,x₁)`.  The variable `x`
is arbitrary — instantiate at `gθ` (`chi4_anchor_off_fold`) or at SCR once a continuous `J(SCR)` map
is supplied.  (`intermediate_value_Ioo`; χ₄ continuous as a polynomial in the coefficients.) -/
theorem hopf_root_ivt (a₁ a₂ a₃ a₄ : ℝ → ℝ)
    (h1 : Continuous a₁) (h2 : Continuous a₂) (h3 : Continuous a₃) (h4 : Continuous a₄)
    {x₀ x₁ : ℝ} (hlt : x₀ < x₁)
    (hlo : a₁ x₀ * a₂ x₀ * a₃ x₀ - a₃ x₀ ^ 2 - a₁ x₀ ^ 2 * a₄ x₀ < 0)
    (hhi : 0 < a₁ x₁ * a₂ x₁ * a₃ x₁ - a₃ x₁ ^ 2 - a₁ x₁ ^ 2 * a₄ x₁) :
    ∃ x ∈ Set.Ioo x₀ x₁, a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x = 0 := by
  have hcont : Continuous (fun x => a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x) := by
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun x => a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x) x₀)
      ((fun x => a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x) x₁) := ⟨hlo, hhi⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hlt.le hcont.continuousOn hmem
  exact ⟨x, hx, hfx⟩

/-- The 4D droop char-poly coefficient `a₁` as a function of the grid stiffness `gθ` (affine ⟹
continuous).  Other Jacobian entries are parameters. -/
noncomputable def chi4coeff1 (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : ℝ → ℝ := fun g => (1:ℝ)*g*Kp_pll - (1:ℝ)*J11 - (1:ℝ)*J00

/-- The 4D droop char-poly coefficient `a2` as a function of `gθ` (affine ⟹ continuous). -/
noncomputable def chi4coeff2 (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : ℝ → ℝ := fun g => (1:ℝ)*J13*J21*Kp_pll - (1:ℝ)*J11*g*Kp_pll + (1:ℝ)*J03*J20*Kp_pll - (1:ℝ)*J00*g*Kp_pll + (1:ℝ)*g*Ki_pll - (1:ℝ)*J01*J10 + (1:ℝ)*J00*J11

/-- The 4D droop char-poly coefficient `a3` as a function of `gθ` (affine ⟹ continuous). -/
noncomputable def chi4coeff3 (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : ℝ → ℝ := fun g => - (1:ℝ)*J03*J11*J20*Kp_pll + (1:ℝ)*J03*J10*J21*Kp_pll + (1:ℝ)*J01*J13*J20*Kp_pll - (1:ℝ)*J01*J10*g*Kp_pll - (1:ℝ)*J00*J13*J21*Kp_pll + (1:ℝ)*J00*J11*g*Kp_pll + (1:ℝ)*J13*J21*Ki_pll - (1:ℝ)*J11*g*Ki_pll + (1:ℝ)*J03*J20*Ki_pll - (1:ℝ)*J00*g*Ki_pll

/-- The 4D droop char-poly coefficient `a4` as a function of `gθ` (affine ⟹ continuous). -/
noncomputable def chi4coeff4 (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : ℝ → ℝ := fun g => - (1:ℝ)*J03*J11*J20*Ki_pll + (1:ℝ)*J03*J10*J21*Ki_pll + (1:ℝ)*J01*J13*J20*Ki_pll - (1:ℝ)*J01*J10*g*Ki_pll - (1:ℝ)*J00*J13*J21*Ki_pll + (1:ℝ)*J00*J11*g*Ki_pll

/-- `a1(gθ)` is continuous (affine in gθ). -/
theorem chi4coeff1_continuous (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : Continuous (chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) := by
  unfold chi4coeff1; fun_prop

/-- `a2(gθ)` is continuous (affine in gθ). -/
theorem chi4coeff2_continuous (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : Continuous (chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) := by
  unfold chi4coeff2; fun_prop

/-- `a3(gθ)` is continuous (affine in gθ). -/
theorem chi4coeff3_continuous (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : Continuous (chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) := by
  unfold chi4coeff3; fun_prop

/-- `a4(gθ)` is continuous (affine in gθ). -/
theorem chi4coeff4_continuous (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : Continuous (chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) := by
  unfold chi4coeff4; fun_prop

/-- The deg-4 Routh–Hurwitz Hopf quantity `χ₄(gθ) = a₁a₂a₃ − a₃² − a₁²a₄` as a function of the grid
stiffness `gθ` (a degree-3 polynomial in gθ, since each aᵢ is affine). -/
noncomputable def chi4f (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : ℝ → ℝ := fun g =>
  chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g * chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g * chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g
    - chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g ^ 2 - chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g ^ 2 * chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g

/-- **The SCR-Hopf boundary exists strictly OFF the fold (T_scr_anchor, parametric).**  Instantiating
the IVT engine at the actual 4D coefficients as functions of `gθ`: if the Hopf quantity is negative at
the fold `gθ=0` and positive at some `g₁>0` (the sign change between weak- and strong-grid ends), there
is `gθ*∈(0,g₁)` with `χ₄(gθ*)=0` — a Hopf condition at `gθ*>0`, SEPARATE from the fold `gθ=0`.  Since
`χ₄|_{gθ=0}=droop` (`chi4_err0_at_fold`), the fold-end sign IS the droop's: the droop is what anchors
this off-fold boundary.  (2D cannot: `chi2_no_root_off_fold`.) -/
theorem chi4_anchor_off_fold (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) (g₁ : ℝ) (hg₁ : 0 < g₁)
    (hfold : chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll 0 < 0) (hstrong : 0 < chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g₁) :
    ∃ gθ ∈ Set.Ioo (0 : ℝ) g₁, chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ = 0 := by
  simp only [chi4f] at hfold hstrong ⊢
  exact hopf_root_ivt (chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) (chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) (chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) (chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll)
    (chi4coeff1_continuous J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) (chi4coeff2_continuous J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) (chi4coeff3_continuous J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll)
    (chi4coeff4_continuous J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll) hg₁ hfold hstrong

/-- **The off-fold boundary is a GENUINE Hopf (T_scr_anchor + genuineness).**  At the IVT root `gθ*`
(where χ₄=0, off the fold), if `a₁(gθ*)>0` and `a₃(gθ*)>0` (here required on the whole interval), then
`hopf_deg4` upgrades it to a genuine pure-imaginary pair `±iω` with `ω²=a₃/a₁>0` — NOT spurious.  This
is the end-to-end parametric statement: under the sign change + positivity, the 4D droop system has a
genuine SCR-Hopf strictly off the fold. -/
theorem chi4_genuine_hopf_anchored (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) (g₁ : ℝ) (hg₁ : 0 < g₁)
    (hfold : chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll 0 < 0) (hstrong : 0 < chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g₁)
    (hpos : ∀ g ∈ Set.Ioo (0 : ℝ) g₁, 0 < chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g ∧ 0 < chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g) :
    ∃ gθ, gθ ∈ Set.Ioo (0 : ℝ) g₁ ∧ ∃ ω : ℝ, 0 < ω ∧
      ((ω : ℂ) * Complex.I) ^ 4 + ((chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 3
        + ((chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + ((chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) = 0 := by
  obtain ⟨gθ, hgθ, hroot⟩ := chi4_anchor_off_fold J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g₁ hg₁ hfold hstrong
  obtain ⟨hp1, hp3⟩ := hpos gθ hgθ
  simp only [chi4f] at hroot
  exact ⟨gθ, hgθ, (hopf_deg4 (chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ) (chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ) (chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ)
    (chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ) hp1 hp3).mpr hroot⟩

end GFL
