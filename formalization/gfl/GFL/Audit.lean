/-
  Integrity audit.  `#print axioms` lists the axioms each declaration actually depends on.
  A clean proof shows only Lean/Mathlib's standard axioms
  `[propext, Classical.choice, Quot.sound]` and crucially NOT `sorryAx`
  (which would indicate a `sorry`/`admit` hole).  See `lake build GFL.Audit` output, and
  `scripts/check_axioms.sh` for the CI gate that fails on any deviation (A4).

  NOTE (D5): most entries are theorems; a few are `def`s carrying mathematical content whose
  axiom-trace is equally meaningful (`litInnerField`, `variantUField`, `slowModeH`).  These are
  flagged `[def]` in the comments.  `#print axioms` applies to both.
-/
import GFL.Model
import GFL.TheoremA
import GFL.TheoremB
import GFL.TheoremC
import GFL.Calculus
import GFL.AsymptoticB
import GFL.LiteralModel
import GFL.LossOfSync
import GFL.SyncEquilibrium
import GFL.SlowModeScalar

open GFL

-- §1–§5 : Lemma 0 + corollaries
#print axioms powerLock                  -- Lemma 0 (Power Lock) — the crux
#print axioms syncCoeff_zero             -- Corollary 0a (K = 0)
#print axioms equilib_relations          -- Corollary 0b (remaining relations)
#print axioms variantS_dw_zero           -- Corollary 0b, Variant S (dw* = 0)
-- §7 A : zero eigenvalue (Variant U) — split into single-conclusion lemmas (D6)
#print axioms variantU_left_eigenvector  -- Theorem A.1 (e₉ᵀ J = 0)
#print axioms variantU_det_zero          -- Theorem A.2 (det J = 0)
#print axioms variantU_basis_nonzero     -- Theorem A.3 (e₉ ≠ 0)
#print axioms variantU_zero_eigenvalue   -- Theorem A (0 ∈ spec) — assembled from the three above
#print axioms variantU_charpoly_factor   -- Theorem A, simple zero (exactly one)
#print axioms variantU_zero_right_eigenvector
-- §7 B : slow eigenvalue (Variant S)
#print axioms reduced_exact              -- Theorem B (reduced, exact)
#print axioms schur_term_zero            -- Theorem B (O(1) Schur term vanishes)
#print axioms variantS_schur_det         -- Theorem B (full-system Schur determinant)
-- §7 C : oscillation onset
#print axioms charpoly_eq                -- Theorem C (companion char. poly)
#print axioms thmC_Ks_zero               -- Theorem C, (C1)
#print axioms thmC_onset                 -- Theorem C, (C2)
#print axioms thmC_roots_exhaustive      -- Theorem C, (C2) exhaustiveness
#print axioms thmC_real_roots            -- Theorem C, (C2) overdamped real-root case
-- calculus completions (use Mathlib's analysis tower)
#print axioms syncCoeff_deriv_zero       -- Cor 0a as a literal derivative
#print axioms branch_iD_tangent_zero     -- v₀ = 0 (i_d-tangent)
#print axioms branch_linearization       -- IFT linearisation  A·v = −c
#print axioms schur_term_zero_of_branch  -- Thm B Schur term, derived from the C¹ branch
#print axioms branch_of_ift              -- W3 from the implicit function theorem (W2 + smoothness)
#print axioms branch_linearization_of_ift
-- A3 : Theorem A's `hbot` (zero last row) as a derived fact, not an axiom
#print axioms variantUField              -- [def] Variant-U field (inner field + F9_U ≡ 0)
#print axioms variantUField_last         -- F9_U component ≡ 0
#print axioms variantU_lastrow_fderiv_zero -- ∂(F9_U)/∂y = 0  ⟹  zero Jacobian last row (hbot)
#print axioms jacobianMatrix             -- [def] Jacobian matrix (i,j) = ∂Gᵢ/∂yⱼ
#print axioms variantU_jacobian_lastrow_zero -- concrete Variant-U Jacobian: last row = 0
#print axioms variantU_jacobian_zero_eigenvalue -- A3 end-to-end: hbot discharged on the matrix
-- P0 (Theorem B O(b²)) partial: algebraic core
#print axioms resolvent_id
#print axioms resolvent_sub              -- resolvent (second) identity = exact difference quotient
#print axioms schur_term_at_neg_b
#print axioms kappa_eq_const_mul_b
#print axioms schur_term_b_sq
-- C : Theorem B full-system slow mode as a SCALAR root problem (eigenvalue ⟺ scalar zero)
#print axioms slowModeH                  -- [def] scalar slow-mode function h(μ)
#print axioms slowMode_det_factor        -- det(J_S−μI) = det(A−μI)·h(μ)
#print axioms slowMode_det_zero_iff      -- μ∉spec(A) ⟹ (det(J_S−μI)=0 ↔ h(μ)=0)
#print axioms eigenvalue_of_slowMode_zero -- h(μ)=0 ⟹ μ is a genuine eigenvalue of J_S
#print axioms slowModeH_at_neg_b         -- h(−b) = O(b²) exactly (matrix-free residual)
#print axioms resolvent_continuousAt     -- C/T1: μ ↦ (A−μI)⁻¹ continuous (no operator norm needed)
#print axioms slowModeH_hasDerivAt       -- C/T1: h differentiable, h' = −1 − ρᵀ(A−νI)⁻²c
#print axioms exists_eigenvalue_of_slowMode_sign_change -- C: sign change of h ⟹ genuine eigenvalue
#print axioms exists_root_of_deriv_le    -- C/T6: deriv ≤ −m + |h ν₀| ≤ m·δ ⟹ root within δ (MVT+IVT)
#print axioms exists_eigenvalue_near_neg_b -- C/T6: |λ_slow + b| ≤ δ = O(b²)/m (quantitative bound)
-- P1 (literal model): InnerField instance + interface-landing evidence (A2) + C¹ smoothness
#print axioms litInnerField              -- [def] the literal model IS an InnerField
#print axioms F_inner_literal_contDiff   -- P1-C¹: the literal §3–§4 field is C¹ (no positivity needed)
#print axioms litF_errD_eq               -- F3 = e_d (explicit §3 form)
#print axioms litF_errQ_eq               -- F4 = e_q (explicit §3 form)
#print axioms litF_F6_eq                 -- F6 = −Kp_pll·v_cqc − Ki_pll·η − dw (v_cqc = F5)
#print axioms litF_eP_eq                 -- F7 = e_P (Power-Lock equation)
#print axioms litF_eQ_eq                 -- F8 = e_Q
-- R2b: loss of synchronism when the synchronous equilibrium disappears
#print axioms loss_of_sync_core
#print axioms exists_margin_of_no_zero
#print axioms loss_of_sync
-- R2a: saddle-node of the sync map (single-harmonic) + link to R2b
#print axioms amplitude_bound
#print axioms sync_pos_of_bias_gt_amp
#print axioms sync_loss_of_bias_gt_amp
#print axioms sync_equilibrium_of_amp_ge
