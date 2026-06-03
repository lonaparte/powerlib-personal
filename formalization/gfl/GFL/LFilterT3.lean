import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 4000000

/-
  L-filter GFL — T3: is "which of i_d, i_q is the essential 3rd state?" well-posed?

  Schur-reduce the 4-state reduced-model Jacobian J(i_d,i_q,η,θ_e) at the slice
  i_d*=P_ref/(1.5·Vg), i_q*=−Q_ref/(1.5·Vg), η*=0 (the full-model integrator equilibrium currents,
  hard-substituted; NUM/G below were GENERATED with θ_e*=0) to the two 3-state systems; form the
  cubic Hopf surfaces Σ_iq, Σ_id (Σ = A·B − C).  Numerator of the difference = NUM (poly in the
  parameters; independent of Ki_pll).

  CENTRAL RING IDENTITY (machine-checked by `ring`):  NUM = (Kp_P − Kp_Q) · G  (`sigma_diff_factor`)
  ⟹  Σ_iq ≡ Σ_id  ⟺  Kp_P = Kp_Q  (`sigma_diff_zero_of_symmetric`),  for ALL Q_ref.
  So T3a (Σ_iq|_{Q_ref=0} ≡ Σ_id|_{Q_ref=0}?) is FALSE for Kp_P ≠ Kp_Q.

  SCOPE — what this does and does NOT say (cross-checked numerically; do not over-read it):
  * NOT an artifact of θ_e*=0.  Re-derived with the power angle θ_e* kept SYMBOLIC (T3_theta2.py):
    (Kp_P−Kp_Q) still divides NUM, and D|_{Kp_P=Kp_Q} ≡ 0 for ALL θ_e* and ALL Q_ref.  Each Σ moves
    with θ_e*, but their DIFFERENCE does not — in this reduced model the d/q pair rotates as a clean
    common mode, so θ_e* cancels in the difference and only the outer-gain term Kp_P−Kp_Q survives.
  * Hence this is a statement about the reduced model's OUTER-LOOP structure, NOT a physical
    "i_d/i_q interchangeable at symmetric gains" claim.  In the FULL 10-state model (LCL caps, grid
    currents, inner-loop PI integrators, active damping) the i_d/i_q participation in the critical mode
    is NOT equal at symmetric gains once θ_e*≠0: PF_iq−PF_id ∝ sin θ_e* (≈0 at θ_e*=0, sign-flips with
    θ_e*, |gap| grows under both load and grid-strength sweeps — T3_participation2.py).  That asymmetry
    is driven by the POWER ANGLE θ_e* (set by P_ref and Lg/SCR) acting THROUGH the fast dynamics this
    reduction drops — NOT by the outer gains.  The reduced model literally cannot see it.
  * Caveat on the slice: i_d*=P_ref/(1.5Vg) is the FULL-model (integrator) equilibrium current; it is
    not the reduced model's own (proportional-droop) equilibrium.  At the latter D|_{Kp_P=Kp_Q}≠0 and
    grows with load (T3_trueeq_reduced.py) — another sign the symmetric-gain interchange is fragile.

  So: this file isolates the GAIN-asymmetry source; the full-model asymmetry adds a POWER-ANGLE source
  the reduction cannot represent.  Both are real and distinct.

  Derivation: derive_lfilter_T3.py (NUM/G at θ_e*=0).  θ_e*-general + full-model cross-checks:
  T3_theta2.py, T3_trueeq_reduced.py, T3_participation2.py.  Identity re-verified here by `ring`. No `sorry`.
-/

namespace GFL

/-- **T3 central identity.**  `Σ_iq − Σ_id` (numerator) `= (Kp_P − Kp_Q)·G` — machine-checked. -/
theorem sigma_diff_factor
    (Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll P_ref Q_ref : ℝ) :
    ((18:ℝ)*Kp_P^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 - (18:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Vg^4 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 + (24:ℝ)*Kp_P*Kp_pll*Kpi^3*Lg*P_ref*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Vg^3 + (48:ℝ)*Kp_P*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Rf*Vg^3 + (24:ℝ)*Kp_P*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 + (27:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Vg^4 - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 + (18:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Vg^4 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 - (24:ℝ)*Kp_Q*Kp_pll*Kpi^3*Lg*P_ref*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Vg^3 - (48:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Rf*Vg^3 - (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg)
      = (Kp_P - Kp_Q) * ((18:ℝ)*Kp_P*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_P*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 + (18:ℝ)*Kp_Q*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 + (16:ℝ)*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn + (16:ℝ)*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg + (24:ℝ)*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 - (16:ℝ)*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf - (8:ℝ)*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 - (16:ℝ)*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn - (24:ℝ)*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn - (8:ℝ)*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 - (24:ℝ)*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 - (18:ℝ)*Kp_pll^2*Kpi*Lf^2*Vg^4 + (16:ℝ)*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn + (16:ℝ)*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg + (24:ℝ)*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 + (24:ℝ)*Kp_pll*Kpi^3*Lg*P_ref*Vg - (24:ℝ)*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn - (24:ℝ)*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg - (36:ℝ)*Kp_pll*Kpi^2*Lf*Vg^3 + (48:ℝ)*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg - (24:ℝ)*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn - (24:ℝ)*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg - (36:ℝ)*Kp_pll*Kpi*Lf*Rf*Vg^3 + (24:ℝ)*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg) := by ring

/-- **`Σ_iq ≡ Σ_id  ⟸  Kp_P = Kp_Q`**: symmetric outer P/Q gains make the two 3-state reductions'
Hopf surfaces identical for every `Q_ref` (and, per the header, for every θ_e* too).  So in the
REDUCED model "i_d vs i_q" is ill-posed exactly on `Kp_P = Kp_Q`, independent of `Q_ref`/θ_e*.  Scope:
this is the reduced model's outer-loop structure only — the full model's i_d/i_q asymmetry ∝ sin θ_e*
(driven by the dropped fast dynamics × power angle) is NOT represented here.  See header. -/
theorem sigma_diff_zero_of_symmetric
    (Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll P_ref Q_ref : ℝ) (h : Kp_P = Kp_Q) :
    ((18:ℝ)*Kp_P^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn - (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 - (27:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lf*Vg^4 + (18:ℝ)*Kp_P^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 - (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 - (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 - (18:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf^2*Vg^4 + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn + (16:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg + (24:ℝ)*Kp_P*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 - (8:ℝ)*Kp_P*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 + (24:ℝ)*Kp_P*Kp_pll*Kpi^3*Lg*P_ref*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi^2*Lf*Vg^3 + (48:ℝ)*Kp_P*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn - (24:ℝ)*Kp_P*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg - (36:ℝ)*Kp_P*Kp_pll*Kpi*Lf*Rf*Vg^3 + (24:ℝ)*Kp_P*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^3*Lg*P_ref*Vg^2 + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg^2*wn + (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg^2 + (27:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lf*Vg^4 - (18:ℝ)*Kp_Q^2*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi^3*Lg^2*P_ref^2 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg^2*P_ref*Q_ref*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref^2*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lf*Lg*P_ref*Vg^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi^2*Lg^2*P_ref^2*Rf + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg^2*Q_ref^2*wn^2 + (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*P_ref*Q_ref*Rg*wn + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Lg*Q_ref*Vg^2*wn + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref^2*Rg^2 + (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*P_ref*Rg*Vg^2 + (18:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf^2*Vg^4 - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg^2*P_ref*Q_ref*Rf*wn - (16:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref^2*Rf*Rg - (24:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lf*Lg*P_ref*Rf*Vg^2 + (8:ℝ)*Kp_Q*Kp_pll^2*Kpi*Lg^2*P_ref^2*Rf^2 - (24:ℝ)*Kp_Q*Kp_pll*Kpi^3*Lg*P_ref*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Lg*Q_ref*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*P_ref*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lf*Vg^3 - (48:ℝ)*Kp_Q*Kp_pll*Kpi^2*Lg*P_ref*Rf*Vg + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Lg*Q_ref*Rf*Vg*wn + (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*P_ref*Rf*Rg*Vg + (36:ℝ)*Kp_Q*Kp_pll*Kpi*Lf*Rf*Vg^3 - (24:ℝ)*Kp_Q*Kp_pll*Kpi*Lg*P_ref*Rf^2*Vg) = 0 := by subst h; ring

end GFL
