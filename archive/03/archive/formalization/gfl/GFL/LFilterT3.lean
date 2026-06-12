import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 4000000

/-
  L-filter GFL — T3 (PARAMETRIC ALGEBRAIC IDENTITY).  ⚠ Scope first: these are identities about the
  Jacobian of the no-integrator field evaluated at a REFERENCE-CURRENT point that is NOT a fixed point
  of that field.  They are correct algebra; they are NOT a stability/Hopf statement.  Do not over-read.

  Object: 4-state no-integrator ("P-only") field F4d(i_d,i_q,η,θ_e); take its Jacobian J at the
  REFERENCE CURRENT i_d=P_ref/(1.5Vg), i_q=−Q_ref/(1.5Vg), η=0 (θ_e symbolic).  Schur-reduce to two
  3-state systems (eliminate i_d → keep {i_q,η,θ_e}; eliminate i_q → keep {i_d,η,θ_e}); for each cubic
  charpoly s³+A s²+B s+C form the Routh–Hurwitz combination Σ := A·B − C.  NUM := numerator(Σ_iq−Σ_id).

  MACHINE-CHECKED RING IDENTITY:  NUM = (Kp_P − Kp_Q) · G   (`sigma_diff_factor`)
  ⟹  Kp_P=Kp_Q ⟹ Σ_iq ≡ Σ_id  (`sigma_diff_zero_of_symmetric`), for ALL Q_ref.  And — proved
  separately, exact, 3-set cross-validated (T3_theta_lean_rational.py) — for ALL θ_e* too: θ_e* is
  COMMON-MODE (appears identically in Σ_iq and Σ_id, cancels in the difference).  [θ_e* is NOT the
  load-bearing assumption — an earlier worry of mine that the reviewer correctly refuted.]

  ⚠ CRITICAL SCOPE — ALGEBRA AT A NON-EQUILIBRIUM POINT, NOT A STABILITY RESULT (verify_nonfixedpoint.py):
  * The reference current is NOT a fixed point of F4d: ||F4d(P_ref/1.5Vg, 0, 0, θ_e)|| ≠ 0 for every
    θ_e (the current rows F0,F1 ≠ 0; choosing θ_e to zero v_cqc only zeroes the PLL row F2).  A Jacobian
    at a non-fixed-point carries no stability meaning, so Σ=A·B−C is NOT a Hopf surface of any
    equilibrium.  The i_d/i_q "interchangeability at symmetric gains" is a property of THIS reference
    substitution (i_q*=0, i_d*=P_ref/1.5Vg), NOT a robust property of the dynamics.
  * At F4d's OWN (proportional-droop) equilibrium (F4d=0; e.g. i_d≈0.019 ≪ ref 0.667), symmetric gains
    give Σ_iq ≠ Σ_id (rel.diff ≈ 12–14%).  The symmetry BREAKS off the reference point.
  * i_d=P_ref/1.5Vg is a true equilibrium ONLY of the FULL model (outer integrators pin it).  But an
    integrator state ζ has ∂ζ'/∂ζ=0 ⇒ Schur-IRREDUCIBLE (1×1 rem block = 0): one cannot have BOTH
    i_d=ref as a genuine equilibrium AND a 3-state reduction.  So the T3 object is intrinsically a
    HYBRID — "full-model operating point + no-integrator Jacobian" — corresponding to no single physical
    linearisation.  In the full model at its real equilibrium the symmetric-gain critical mode is mildly
    ASYMMETRIC (participation PF_iq ≳ PF_id, ∝ sin θ_e* — T3_participation2.py), which this reduction
    structurally cannot see.

  BOTTOM LINE: `sigma_diff_factor` is a correct parametric algebraic identity (and θ_e* is genuinely
  common-mode), but it does NOT establish i_d/i_q symmetry of the physical Hopf boundary SCR_H1 — its
  linearisation point is not an equilibrium.  The physical question needs the full (integrator) model,
  where the answer is mildly asymmetric.

  Verification: derive_lfilter_T3.py (NUM/G); T3_theta_lean_rational.py (θ_e* general, 3-set);
  T3_crosscheck.py (reproduces θ_e*=0); verify_nonfixedpoint.py (non-fixed-point + droop asymmetry +
  integrator irreducibility); T3_participation2.py (full-model PF asymmetry).  `ring`-checked, no `sorry`.
-/

namespace GFL

/-- **T3 central identity** (pure algebra; see header for scope).  For the Routh–Hurwitz combinations
`Σ = A·B − C` of the two 3-state Schur reductions of `J` at the REFERENCE-CURRENT point (NOT an
equilibrium of the field), `num(Σ_iq − Σ_id) = (Kp_P − Kp_Q)·G` — machine-checked by `ring`. -/
theorem sigma_diff_factor
    (Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll P_ref Q_ref : ℝ) :
    ((18:ℝ)*Kp_P^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 - (18:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Vg^4 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 + (24:ℝ)*Kp_P*Kp_pll*Kpi^3*Lg*P_ref*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Vg^3 + (48:ℝ)*Kp_P*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Rf*Vg^3 + (24:ℝ)*Kp_P*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 + (27:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Vg^4 - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 + (18:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Vg^4 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 - (24:ℝ)*Kp_Q*Kp_pll*Kpi^3*Lg*P_ref*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Vg^3 - (48:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Rf*Vg^3 - (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg)
      = (Kp_P - Kp_Q) * ((18:ℝ)*Kp_P*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_P*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 + (18:ℝ)*Kp_Q*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 + (16:ℝ)*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn + (16:ℝ)*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg + (24:ℝ)*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 - (16:ℝ)*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf - (8:ℝ)*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 - (16:ℝ)*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn - (24:ℝ)*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn - (8:ℝ)*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 - (24:ℝ)*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 - (18:ℝ)*Kp_pll^2*Kpi*Lf^2*Vg^4 + (16:ℝ)*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn + (16:ℝ)*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg + (24:ℝ)*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 + (24:ℝ)*Kp_pll*Kpi^3*Lg*P_ref*Vg - (24:ℝ)*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn - (24:ℝ)*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg - (36:ℝ)*Kp_pll*Kpi^2*Lf*Vg^3 + (48:ℝ)*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg - (24:ℝ)*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn - (24:ℝ)*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg - (36:ℝ)*Kp_pll*Kpi*Lf*Rf*Vg^3 + (24:ℝ)*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg) := by ring

/-- **`Σ_iq ≡ Σ_id  ⟸  Kp_P = Kp_Q`** at the reference-current point, for every `Q_ref` (and, per the
header, every θ_e*).  ⚠ This is an algebraic identity at a NON-EQUILIBRIUM point, not a stability/Hopf
statement: at the field's own droop equilibrium `Σ_iq ≠ Σ_id` (≈12–14%), and the full integrator model
is mildly asymmetric (PF_iq ≳ PF_id).  So it does NOT show i_d/i_q symmetry of the physical SCR_H1.
See header (verify_nonfixedpoint.py). -/
theorem sigma_diff_zero_of_symmetric
    (Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll P_ref Q_ref : ℝ) (h : Kp_P = Kp_Q) :
    ((18:ℝ)*Kp_P^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 - (18:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Vg^4 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 + (24:ℝ)*Kp_P*Kp_pll*Kpi^3*Lg*P_ref*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Vg^3 + (48:ℝ)*Kp_P*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Rf*Vg^3 + (24:ℝ)*Kp_P*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 + (27:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Vg^4 - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 + (18:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Vg^4 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 - (24:ℝ)*Kp_Q*Kp_pll*Kpi^3*Lg*P_ref*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Vg^3 - (48:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Rf*Vg^3 - (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg) = 0 := by subst h; ring

end GFL
