/-
  SCR-Hopf — the strong-grid end DISCHARGED from structure (parametric).  `chi4_anchor_off_fold`
  (ScrHopfAnchor) needed a two-point sign change `χ₄|_0 < 0 < χ₄|_g₁` — the strong-grid value `χ₄|_g₁>0`
  was an assumption.  Here it is PROVED from the structure: `χ₄(gθ)` is a degree-3 polynomial in gθ
  whose leading coefficient is
      L₃ = −Kp_pll·(J00+J11)·(J00·J11·Kp_pll² − J00·Ki_pll·Kp_pll − J01·J10·Kp_pll² − J11·Ki_pll·Kp_pll + Ki_pll²),
  so `L₃ > 0` ⟹ χ₄(gθ) → +∞ as gθ → ∞ (`tendsto_atTop_of_leadingCoeff_nonneg`) ⟹ it is eventually
  positive — no second sign point need be assumed.  Combined with the fold value `χ₄|_0 = droop < 0`
  (`chi4_err0_at_fold`: the err=0 part vanishes at gθ=0), IVT gives a root `gθ*>0` strictly off the fold.

   * `chi4poly` — χ₄(gθ) as `Polynomial ℝ` (= C L₃·X³ + C L₂·X² + C L₁·X + C L₀); `chi4poly_eval` bridges
     `eval g chi4poly = chi4f g` (a `ring` identity tying the cubic to ScrHopfAnchor's coefficient form).
   * `chi4_anchor_leadingpos` — `L₃ > 0 ∧ χ₄(0) < 0 ⟹ ∃ gθ* > 0, χ₄(gθ*) = 0`.  Only TWO structural
     sign conditions (leading coefficient + fold/droop value); the strong-grid end is no longer assumed.
   * `chi4_genuine_hopf_leadingpos` — that off-fold root is a GENUINE Hopf (hopf_deg4) when `a₁,a₃ > 0`
     on the positives.  (Empirically the dominant genuine orientation is exactly `L₃>0 ∧ χ₄(0)<0`.)

  SCOPE (honest).  `L₃>0`, `χ₄(0)<0`, `a₁,a₃>0` remain HYPOTHESES — operating-point-dependent structural
  conditions (numerically the dominant genuine orientation; verify_cubic_anchor.py).  What is now
  UNCONDITIONAL is the strong-grid limit: positivity of the leading coefficient REPLACES the assumed
  second sign point.  Still parametric in the Jacobian entries; no operating-point numerics.
-/
import GFL.ScrHopfAnchor
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

namespace GFL
open Matrix Set Polynomial Filter
open scoped Topology
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-- **χ₄(gθ) as a `Polynomial ℝ`** in the grid stiffness, `C L₃·X³ + C L₂·X² + C L₁·X + C L₀`, with the
gθ-coefficients `L₀..L₃` (the CAS expansion of χ₄ in gθ; `L₃` = leading coefficient). -/
noncomputable def chi4poly (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) : Polynomial ℝ :=
  C ((1:ℝ)*J01*J10*J11*Kp_pll^3 - (1:ℝ)*J00*J11^2*Kp_pll^3 + (1:ℝ)*J00*J01*J10*Kp_pll^3 - (1:ℝ)*J00^2*J11*Kp_pll^3 + (1:ℝ)*J11^2*Kp_pll^2*Ki_pll + (2:ℝ)*J00*J11*Kp_pll^2*Ki_pll + (1:ℝ)*J00^2*Kp_pll^2*Ki_pll - (1:ℝ)*J11*Kp_pll*Ki_pll^2 - (1:ℝ)*J00*Kp_pll*Ki_pll^2) * X ^ 3
    + C ((1:ℝ)*J03*J11^2*J20*Kp_pll^3 - (1:ℝ)*J03*J10*J11*J21*Kp_pll^3 - (1:ℝ)*J01*J11*J13*J20*Kp_pll^3 - (1:ℝ)*J01*J10*J13*J21*Kp_pll^3 - (1:ℝ)*J01*J03*J10*J20*Kp_pll^3 + (2:ℝ)*J00*J11*J13*J21*Kp_pll^3 + (2:ℝ)*J00*J03*J11*J20*Kp_pll^3 - (1:ℝ)*J00*J03*J10*J21*Kp_pll^3 - (1:ℝ)*J00*J01*J13*J20*Kp_pll^3 + (1:ℝ)*J00^2*J13*J21*Kp_pll^3 - (2:ℝ)*J11*J13*J21*Kp_pll^2*Ki_pll - (2:ℝ)*J03*J11*J20*Kp_pll^2*Ki_pll - (1:ℝ)*J01*J10*J11^2*Kp_pll^2 - (2:ℝ)*J00*J13*J21*Kp_pll^2*Ki_pll + (1:ℝ)*J00*J11^3*Kp_pll^2 - (2:ℝ)*J00*J03*J20*Kp_pll^2*Ki_pll - (2:ℝ)*J00*J01*J10*J11*Kp_pll^2 + (2:ℝ)*J00^2*J11^2*Kp_pll^2 - (1:ℝ)*J00^2*J01*J10*Kp_pll^2 + (1:ℝ)*J00^3*J11*Kp_pll^2 + (1:ℝ)*J13*J21*Kp_pll*Ki_pll^2 - (1:ℝ)*J11^3*Kp_pll*Ki_pll + (1:ℝ)*J03*J20*Kp_pll*Ki_pll^2 - (2:ℝ)*J01*J10*J11*Kp_pll*Ki_pll - (1:ℝ)*J00*J11^2*Kp_pll*Ki_pll - (2:ℝ)*J00*J01*J10*Kp_pll*Ki_pll - (1:ℝ)*J00^2*J11*Kp_pll*Ki_pll - (1:ℝ)*J00^3*Kp_pll*Ki_pll) * X ^ 2
    + C (- (1:ℝ)*J03*J11*J13*J20*J21*Kp_pll^3 + (1:ℝ)*J03*J10*J13*J21^2*Kp_pll^3 - (1:ℝ)*J03^2*J11*J20^2*Kp_pll^3 + (1:ℝ)*J03^2*J10*J20*J21*Kp_pll^3 + (1:ℝ)*J01*J13^2*J20*J21*Kp_pll^3 + (1:ℝ)*J01*J03*J13*J20^2*Kp_pll^3 - (1:ℝ)*J00*J13^2*J21^2*Kp_pll^3 - (1:ℝ)*J00*J03*J13*J20*J21*Kp_pll^3 + (1:ℝ)*J13^2*J21^2*Kp_pll^2*Ki_pll + (2:ℝ)*J03*J13*J20*J21*Kp_pll^2*Ki_pll - (1:ℝ)*J03*J11^3*J20*Kp_pll^2 + (1:ℝ)*J03*J10*J11^2*J21*Kp_pll^2 + (1:ℝ)*J03^2*J20^2*Kp_pll^2*Ki_pll + (1:ℝ)*J01*J11^2*J13*J20*Kp_pll^2 + (1:ℝ)*J01*J10*J11*J13*J21*Kp_pll^2 + (1:ℝ)*J01*J03*J10^2*J21*Kp_pll^2 + (1:ℝ)*J01^2*J10*J13*J20*Kp_pll^2 - (2:ℝ)*J00*J11^2*J13*J21*Kp_pll^2 - (2:ℝ)*J00*J03*J11^2*J20*Kp_pll^2 + (1:ℝ)*J00*J03*J10*J11*J21*Kp_pll^2 + (1:ℝ)*J00*J01*J11*J13*J20*Kp_pll^2 + (1:ℝ)*J00*J01*J03*J10*J20*Kp_pll^2 - (2:ℝ)*J00^2*J11*J13*J21*Kp_pll^2 - (2:ℝ)*J00^2*J03*J11*J20*Kp_pll^2 + (1:ℝ)*J00^2*J03*J10*J21*Kp_pll^2 + (1:ℝ)*J00^2*J01*J13*J20*Kp_pll^2 - (1:ℝ)*J00^3*J13*J21*Kp_pll^2 + (2:ℝ)*J11^2*J13*J21*Kp_pll*Ki_pll - (1:ℝ)*J03*J11^2*J20*Kp_pll*Ki_pll + (3:ℝ)*J03*J10*J11*J21*Kp_pll*Ki_pll + (3:ℝ)*J01*J11*J13*J20*Kp_pll*Ki_pll + (1:ℝ)*J01*J10*J13*J21*Kp_pll*Ki_pll + (1:ℝ)*J01*J03*J10*J20*Kp_pll*Ki_pll - (1:ℝ)*J01^2*J10^2*J11*Kp_pll + (3:ℝ)*J00*J03*J10*J21*Kp_pll*Ki_pll + (3:ℝ)*J00*J01*J13*J20*Kp_pll*Ki_pll + (2:ℝ)*J00*J01*J10*J11^2*Kp_pll - (1:ℝ)*J00*J01^2*J10^2*Kp_pll - (1:ℝ)*J00^2*J13*J21*Kp_pll*Ki_pll - (1:ℝ)*J00^2*J11^3*Kp_pll + (2:ℝ)*J00^2*J03*J20*Kp_pll*Ki_pll + (2:ℝ)*J00^2*J01*J10*J11*Kp_pll - (1:ℝ)*J00^3*J11^2*Kp_pll + (1:ℝ)*J11*J13*J21*Ki_pll^2 + (1:ℝ)*J03*J11*J20*Ki_pll^2 + (1:ℝ)*J00*J13*J21*Ki_pll^2 + (1:ℝ)*J00*J03*J20*Ki_pll^2) * X
    + C ((1:ℝ)*J03*J11^2*J13*J20*J21*Kp_pll^2 - (1:ℝ)*J03*J10*J11*J13*J21^2*Kp_pll^2 + (1:ℝ)*J03^2*J10*J11*J20*J21*Kp_pll^2 - (1:ℝ)*J03^2*J10^2*J21^2*Kp_pll^2 - (1:ℝ)*J01*J11*J13^2*J20*J21*Kp_pll^2 + (1:ℝ)*J01*J03*J11*J13*J20^2*Kp_pll^2 - (2:ℝ)*J01*J03*J10*J13*J20*J21*Kp_pll^2 - (1:ℝ)*J01^2*J13^2*J20^2*Kp_pll^2 + (1:ℝ)*J00*J11*J13^2*J21^2*Kp_pll^2 + (1:ℝ)*J00*J03*J10*J13*J21^2*Kp_pll^2 + (1:ℝ)*J00*J03^2*J11*J20^2*Kp_pll^2 - (1:ℝ)*J00*J03^2*J10*J20*J21*Kp_pll^2 + (1:ℝ)*J00*J01*J13^2*J20*J21*Kp_pll^2 - (1:ℝ)*J00*J01*J03*J13*J20^2*Kp_pll^2 + (1:ℝ)*J00^2*J03*J13*J20*J21*Kp_pll^2 - (1:ℝ)*J11*J13^2*J21^2*Kp_pll*Ki_pll - (2:ℝ)*J03*J10*J13*J21^2*Kp_pll*Ki_pll + (1:ℝ)*J03^2*J11*J20^2*Kp_pll*Ki_pll - (2:ℝ)*J03^2*J10*J20*J21*Kp_pll*Ki_pll - (2:ℝ)*J01*J13^2*J20*J21*Kp_pll*Ki_pll - (2:ℝ)*J01*J03*J13*J20^2*Kp_pll*Ki_pll - (1:ℝ)*J01*J03*J10*J11^2*J20*Kp_pll + (1:ℝ)*J01*J03*J10^2*J11*J21*Kp_pll + (1:ℝ)*J01^2*J10*J11*J13*J20*Kp_pll + (1:ℝ)*J00*J13^2*J21^2*Kp_pll*Ki_pll + (1:ℝ)*J00*J03*J11^3*J20*Kp_pll - (1:ℝ)*J00*J03*J10*J11^2*J21*Kp_pll - (1:ℝ)*J00*J03^2*J20^2*Kp_pll*Ki_pll - (1:ℝ)*J00*J01*J11^2*J13*J20*Kp_pll - (1:ℝ)*J00*J01*J10*J11*J13*J21*Kp_pll - (1:ℝ)*J00*J01*J03*J10*J11*J20*Kp_pll + (1:ℝ)*J00*J01*J03*J10^2*J21*Kp_pll + (1:ℝ)*J00*J01^2*J10*J13*J20*Kp_pll + (1:ℝ)*J00^2*J11^2*J13*J21*Kp_pll + (1:ℝ)*J00^2*J03*J11^2*J20*Kp_pll - (1:ℝ)*J00^2*J03*J10*J11*J21*Kp_pll - (1:ℝ)*J00^2*J01*J11*J13*J20*Kp_pll - (1:ℝ)*J00^2*J01*J10*J13*J21*Kp_pll + (1:ℝ)*J00^3*J11*J13*J21*Kp_pll - (1:ℝ)*J13^2*J21^2*Ki_pll^2 - (2:ℝ)*J03*J13*J20*J21*Ki_pll^2 + (1:ℝ)*J03*J11^3*J20*Ki_pll - (1:ℝ)*J03*J10*J11^2*J21*Ki_pll - (1:ℝ)*J03^2*J20^2*Ki_pll^2 - (1:ℝ)*J01*J11^2*J13*J20*Ki_pll + (1:ℝ)*J01*J10*J11*J13*J21*Ki_pll + (1:ℝ)*J01*J03*J10*J11*J20*Ki_pll + (1:ℝ)*J00*J03*J11^2*J20*Ki_pll - (2:ℝ)*J00*J03*J10*J11*J21*Ki_pll - (2:ℝ)*J00*J01*J11*J13*J20*Ki_pll + (1:ℝ)*J00*J01*J10*J13*J21*Ki_pll + (1:ℝ)*J00*J01*J03*J10*J20*Ki_pll + (1:ℝ)*J00^2*J11*J13*J21*Ki_pll - (1:ℝ)*J00^2*J03*J10*J21*Ki_pll - (1:ℝ)*J00^2*J01*J13*J20*Ki_pll + (1:ℝ)*J00^3*J13*J21*Ki_pll)

/-- **Bridge `eval g chi4poly = chi4f g`** (a `ring` identity): the degree-3 polynomial in gθ equals
ScrHopfAnchor's coefficient-product form `a₁a₂a₃ − a₃² − a₁²a₄` as a function of gθ. -/
theorem chi4poly_eval (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ) (g : ℝ) :
    (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).eval g = chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g := by
  simp only [chi4poly, chi4f, chi4coeff1, chi4coeff2, chi4coeff3, chi4coeff4,
    eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- **Strong-grid end discharged from structure.**  If the leading coefficient `L₃ > 0` and the fold
value `χ₄(0) < 0` (= droop, `chi4_err0_at_fold`), then `χ₄` has a zero at some `gθ* > 0` — STRICTLY off
the fold.  The strong-grid sign `χ₄(g₁)>0` is no longer assumed: `L₃>0` forces `χ₄(gθ)→+∞`
(`tendsto_atTop_of_leadingCoeff_nonneg`), hence eventually positive, then IVT. -/
theorem chi4_anchor_leadingpos (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ)
    (hL3 : 0 < ((1:ℝ)*J01*J10*J11*Kp_pll^3 - (1:ℝ)*J00*J11^2*Kp_pll^3 + (1:ℝ)*J00*J01*J10*Kp_pll^3 - (1:ℝ)*J00^2*J11*Kp_pll^3 + (1:ℝ)*J11^2*Kp_pll^2*Ki_pll + (2:ℝ)*J00*J11*Kp_pll^2*Ki_pll + (1:ℝ)*J00^2*Kp_pll^2*Ki_pll - (1:ℝ)*J11*Kp_pll*Ki_pll^2 - (1:ℝ)*J00*Kp_pll*Ki_pll^2))
    (hfold : chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll 0 < 0) :
    ∃ gθ : ℝ, 0 < gθ ∧ chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ = 0 := by
  have ha : ((1:ℝ)*J01*J10*J11*Kp_pll^3 - (1:ℝ)*J00*J11^2*Kp_pll^3 + (1:ℝ)*J00*J01*J10*Kp_pll^3 - (1:ℝ)*J00^2*J11*Kp_pll^3 + (1:ℝ)*J11^2*Kp_pll^2*Ki_pll + (2:ℝ)*J00*J11*Kp_pll^2*Ki_pll + (1:ℝ)*J00^2*Kp_pll^2*Ki_pll - (1:ℝ)*J11*Kp_pll*Ki_pll^2 - (1:ℝ)*J00*Kp_pll*Ki_pll^2) ≠ 0 := ne_of_gt hL3
  have hdeg : (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).degree = 3 := by
    rw [chi4poly]; exact degree_cubic ha
  have hlc : (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).leadingCoeff = ((1:ℝ)*J01*J10*J11*Kp_pll^3 - (1:ℝ)*J00*J11^2*Kp_pll^3 + (1:ℝ)*J00*J01*J10*Kp_pll^3 - (1:ℝ)*J00^2*J11*Kp_pll^3 + (1:ℝ)*J11^2*Kp_pll^2*Ki_pll + (2:ℝ)*J00*J11*Kp_pll^2*Ki_pll + (1:ℝ)*J00^2*Kp_pll^2*Ki_pll - (1:ℝ)*J11*Kp_pll*Ki_pll^2 - (1:ℝ)*J00*Kp_pll*Ki_pll^2) := by
    rw [chi4poly]; exact leadingCoeff_cubic ha
  have hdeg0 : 0 < (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).degree := by rw [hdeg]; decide
  have hlcnn : 0 ≤ (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).leadingCoeff := by rw [hlc]; exact hL3.le
  have htend : Tendsto (fun x => (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).eval x) atTop atTop :=
    (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).tendsto_atTop_of_leadingCoeff_nonneg hdeg0 hlcnn
  have hev : ∀ᶠ x in atTop, 0 < (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).eval x ∧ 0 < x :=
    (htend.eventually_gt_atTop 0).and (eventually_gt_atTop 0)
  obtain ⟨g1, hg1e, hg1p⟩ := hev.exists
  have h0 : (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).eval 0 < 0 := by rw [chi4poly_eval]; exact hfold
  have hmem : (0 : ℝ) ∈ Set.Ioo ((chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).eval 0) ((chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).eval g1) := ⟨h0, hg1e⟩
  obtain ⟨g, hg, hge⟩ :=
    intermediate_value_Ioo hg1p.le (chi4poly J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll).continuous.continuousOn hmem
  exact ⟨g, hg.1, by rw [← chi4poly_eval]; exact hge⟩

/-- **Genuine off-fold Hopf from structure (capstone).**  Under `L₃>0`, `χ₄(0)<0` (existence of the
off-fold root) and `a₁,a₃>0` on the positives, the root `gθ*>0` is a GENUINE pure-imaginary pair `±iω`
(ω²=a₃/a₁>0, `hopf_deg4`) — the end-to-end parametric SCR-Hopf with the strong-grid end discharged. -/
theorem chi4_genuine_hopf_leadingpos (J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll : ℝ)
    (hL3 : 0 < ((1:ℝ)*J01*J10*J11*Kp_pll^3 - (1:ℝ)*J00*J11^2*Kp_pll^3 + (1:ℝ)*J00*J01*J10*Kp_pll^3 - (1:ℝ)*J00^2*J11*Kp_pll^3 + (1:ℝ)*J11^2*Kp_pll^2*Ki_pll + (2:ℝ)*J00*J11*Kp_pll^2*Ki_pll + (1:ℝ)*J00^2*Kp_pll^2*Ki_pll - (1:ℝ)*J11*Kp_pll*Ki_pll^2 - (1:ℝ)*J00*Kp_pll*Ki_pll^2))
    (hfold : chi4f J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll 0 < 0)
    (hpos : ∀ g : ℝ, 0 < g → 0 < chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g ∧ 0 < chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll g) :
    ∃ gθ, 0 < gθ ∧ ∃ ω : ℝ, 0 < ω ∧
      ((ω : ℂ) * Complex.I) ^ 4 + ((chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 3
        + ((chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + ((chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) + ((chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ : ℝ) : ℂ) = 0 := by
  obtain ⟨gθ, hgpos, hroot⟩ := chi4_anchor_leadingpos J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll hL3 hfold
  obtain ⟨hp1, hp3⟩ := hpos gθ hgpos
  simp only [chi4f] at hroot
  exact ⟨gθ, hgpos, (hopf_deg4 (chi4coeff1 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ) (chi4coeff2 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ) (chi4coeff3 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ)
    (chi4coeff4 J00 J01 J03 J10 J11 J13 J20 J21 Kp_pll Ki_pll gθ) hp1 hp3).mpr hroot⟩

end GFL
