#!/usr/bin/env python3
"""Assemble GFL/ScrHopfAnchor.lean: the (a) fold-separation fact + (b) IVT existence of the
SCR-Hopf boundary off the fold, parametric (sign-change as hypothesis).  Reuses /tmp/chi4_lean.txt."""
b=open('/tmp/chi4_lean.txt').read()
def grab(tag):
    s=b.split(tag+':=\n',1)[1]; return s.split('\n\n',1)[0].strip()
A1,A2,A3,A4,ERR0=[grab(t) for t in ['A1','A2','A3','A4','ERR0']]
# coefficient functions of g := gθ : replace the gθ token by the bound variable g
def asg(e): return e.replace('gθ','g')
G1,G2,G3,G4=[asg(x) for x in (A1,A2,A3,A4)]
ARGS="J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll"   # NB: no gθ (it becomes the bound g)
DECL=ARGS+" : ℝ"
ENTg="J00 J01 J03 J10 J11 J13 J20 J21 gθ Kp_pll Ki_pll : ℝ"  # with gθ, for the err0-at-fold lemma

hdr='''/-
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

'''

s=hdr
# (a) err0 vanishes at the fold
s+="/-! ### (a) The droop is what survives at the fold (err=0 part vanishes at gθ=0) -/\n\n"
s+="/-- **err=0 part vanishes at the fold.**  Every monomial of the err=0 part `err0` carries a factor\n"
s+="`gθ`, so `err0|_{gθ=0} = 0`.  Combined with `chi4_droop_decomp` (χ₄ = err0 + droop), this gives\n"
s+="`χ₄|_{gθ=0} = droop|_{gθ=0}`: at the fold the only surviving contribution to the Hopf quantity is the\n"
s+="DROOP — it is the droop (∝ J03,J13 ∝ tracking error) that can carry χ₄=0 off the fold gθ=0. -/\n"
s+=f"theorem chi4_err0_at_fold ({ENTg}) (hg : gθ = 0) :\n"
s+=f"    ({ERR0}) = 0 := by subst hg; ring\n\n"

# (b) generic IVT engine
s+="/-! ### (b) IVT existence of the χ₄=0 boundary off the fold (axis-agnostic) -/\n\n"
s+="/-- **Generic IVT engine for the Hopf boundary.**  For continuous coefficient maps `a₁..a₄ : ℝ → ℝ`,\n"
s+="if the deg-4 Routh–Hurwitz Hopf quantity `χ₄(x) = a₁a₂a₃ − a₃² − a₁²a₄` is negative at `x₀` and\n"
s+="positive at `x₁ > x₀`, then it vanishes somewhere in the OPEN interval `(x₀,x₁)`.  The variable `x`\n"
s+="is arbitrary — instantiate at `gθ` (`chi4_anchor_off_fold`) or at SCR once a continuous `J(SCR)` map\n"
s+="is supplied.  (`intermediate_value_Ioo`; χ₄ continuous as a polynomial in the coefficients.) -/\n"
s+="theorem hopf_root_ivt (a₁ a₂ a₃ a₄ : ℝ → ℝ)\n"
s+="    (h1 : Continuous a₁) (h2 : Continuous a₂) (h3 : Continuous a₃) (h4 : Continuous a₄)\n"
s+="    {x₀ x₁ : ℝ} (hlt : x₀ < x₁)\n"
s+="    (hlo : a₁ x₀ * a₂ x₀ * a₃ x₀ - a₃ x₀ ^ 2 - a₁ x₀ ^ 2 * a₄ x₀ < 0)\n"
s+="    (hhi : 0 < a₁ x₁ * a₂ x₁ * a₃ x₁ - a₃ x₁ ^ 2 - a₁ x₁ ^ 2 * a₄ x₁) :\n"
s+="    ∃ x ∈ Set.Ioo x₀ x₁, a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x = 0 := by\n"
s+="  have hcont : Continuous (fun x => a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x) := by\n"
s+="    fun_prop\n"
s+="  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun x => a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x) x₀)\n"
s+="      ((fun x => a₁ x * a₂ x * a₃ x - a₃ x ^ 2 - a₁ x ^ 2 * a₄ x) x₁) := ⟨hlo, hhi⟩\n"
s+="  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hlt.le hcont.continuousOn hmem\n"
s+="  exact ⟨x, hx, hfx⟩\n\n"

# coefficient functions of gθ
s+="/-- The 4D droop char-poly coefficient `a₁` as a function of the grid stiffness `gθ` (affine ⟹\n"
s+="continuous).  Other Jacobian entries are parameters. -/\n"
for i,(nm,body) in enumerate([('chi4coeff1',G1),('chi4coeff2',G2),('chi4coeff3',G3),('chi4coeff4',G4)],1):
    if i>1:
        s+=f"/-- The 4D droop char-poly coefficient `a{i}` as a function of `gθ` (affine ⟹ continuous). -/\n"
    s+=f"noncomputable def {nm} ({DECL}) : ℝ → ℝ := fun g => {body}\n\n"
for i,nm in enumerate(['chi4coeff1','chi4coeff2','chi4coeff3','chi4coeff4'],1):
    s+=f"/-- `a{i}(gθ)` is continuous (affine in gθ). -/\n"
    s+=f"theorem {nm}_continuous ({DECL}) : Continuous ({nm} {ARGS}) := by\n"
    s+=f"  unfold {nm}; fun_prop\n\n"

# chi4f
s+="/-- The deg-4 Routh–Hurwitz Hopf quantity `χ₄(gθ) = a₁a₂a₃ − a₃² − a₁²a₄` as a function of the grid\n"
s+="stiffness `gθ` (a degree-3 polynomial in gθ, since each aᵢ is affine). -/\n"
s+=f"noncomputable def chi4f ({DECL}) : ℝ → ℝ := fun g =>\n"
s+=f"  chi4coeff1 {ARGS} g * chi4coeff2 {ARGS} g * chi4coeff3 {ARGS} g\n"
s+=f"    - chi4coeff3 {ARGS} g ^ 2 - chi4coeff1 {ARGS} g ^ 2 * chi4coeff4 {ARGS} g\n\n"

# concrete anchor
s+="/-- **The SCR-Hopf boundary exists strictly OFF the fold (T_scr_anchor, parametric).**  Instantiating\n"
s+="the IVT engine at the actual 4D coefficients as functions of `gθ`: if the Hopf quantity is negative at\n"
s+="the fold `gθ=0` and positive at some `g₁>0` (the sign change between weak- and strong-grid ends), there\n"
s+="is `gθ*∈(0,g₁)` with `χ₄(gθ*)=0` — a Hopf condition at `gθ*>0`, SEPARATE from the fold `gθ=0`.  Since\n"
s+="`χ₄|_{gθ=0}=droop` (`chi4_err0_at_fold`), the fold-end sign IS the droop's: the droop is what anchors\n"
s+="this off-fold boundary.  (2D cannot: `chi2_no_root_off_fold`.) -/\n"
s+=f"theorem chi4_anchor_off_fold ({DECL}) (g₁ : ℝ) (hg₁ : 0 < g₁)\n"
s+=f"    (hfold : chi4f {ARGS} 0 < 0) (hstrong : 0 < chi4f {ARGS} g₁) :\n"
s+=f"    ∃ gθ ∈ Set.Ioo (0 : ℝ) g₁, chi4f {ARGS} gθ = 0 := by\n"
s+="  simp only [chi4f] at hfold hstrong ⊢\n"
s+=f"  exact hopf_root_ivt (chi4coeff1 {ARGS}) (chi4coeff2 {ARGS}) (chi4coeff3 {ARGS}) (chi4coeff4 {ARGS})\n"
s+=f"    (chi4coeff1_continuous {ARGS}) (chi4coeff2_continuous {ARGS}) (chi4coeff3_continuous {ARGS})\n"
s+=f"    (chi4coeff4_continuous {ARGS}) hg₁ hfold hstrong\n\n"

# genuineness capstone
s+="/-- **The off-fold boundary is a GENUINE Hopf (T_scr_anchor + genuineness).**  At the IVT root `gθ*`\n"
s+="(where χ₄=0, off the fold), if `a₁(gθ*)>0` and `a₃(gθ*)>0` (here required on the whole interval), then\n"
s+="`hopf_deg4` upgrades it to a genuine pure-imaginary pair `±iω` with `ω²=a₃/a₁>0` — NOT spurious.  This\n"
s+="is the end-to-end parametric statement: under the sign change + positivity, the 4D droop system has a\n"
s+="genuine SCR-Hopf strictly off the fold. -/\n"
s+=f"theorem chi4_genuine_hopf_anchored ({DECL}) (g₁ : ℝ) (hg₁ : 0 < g₁)\n"
s+=f"    (hfold : chi4f {ARGS} 0 < 0) (hstrong : 0 < chi4f {ARGS} g₁)\n"
s+=f"    (hpos : ∀ g ∈ Set.Ioo (0 : ℝ) g₁, 0 < chi4coeff1 {ARGS} g ∧ 0 < chi4coeff3 {ARGS} g) :\n"
s+="    ∃ gθ, gθ ∈ Set.Ioo (0 : ℝ) g₁ ∧ ∃ ω : ℝ, 0 < ω ∧\n"
s+=f"      ((ω : ℂ) * Complex.I) ^ 4 + ((chi4coeff1 {ARGS} gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 3\n"
s+=f"        + ((chi4coeff2 {ARGS} gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2\n"
s+=f"        + ((chi4coeff3 {ARGS} gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((chi4coeff4 {ARGS} gθ : ℝ) : ℂ) = 0 := by\n"
s+=f"  obtain ⟨gθ, hgθ, hroot⟩ := chi4_anchor_off_fold {ARGS} g₁ hg₁ hfold hstrong\n"
s+="  obtain ⟨hp1, hp3⟩ := hpos gθ hgθ\n"
s+="  simp only [chi4f] at hroot\n"
s+=f"  exact ⟨gθ, hgθ, (hopf_deg4 (chi4coeff1 {ARGS} gθ) (chi4coeff2 {ARGS} gθ) (chi4coeff3 {ARGS} gθ)\n"
s+=f"    (chi4coeff4 {ARGS} gθ) hp1 hp3).mpr hroot⟩\n\n"

s+="end GFL\n"
open('GFL/ScrHopfAnchor.lean','w').write(s)
print("wrote GFL/ScrHopfAnchor.lean")
