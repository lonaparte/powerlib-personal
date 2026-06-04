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
import GFL.LiteralJacobian
import GFL.LossOfSync
import GFL.SyncEquilibrium
import GFL.SlowModeScalar
import GFL.HopfFold
import GFL.LFilterHopf
import GFL.LFilterT3
import GFL.FoldHopf
import GFL.FoldHopfDecouple
import GFL.ScrHopf
import GFL.ScrHopfExist

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
-- P1-inv (PARTIAL): the sparse e_P/e_Q rows of the literal ∂F/∂z (the reduction angle's core)
#print axioms innerFieldZ                -- [def] inner field as a function of z (dw fixed)
#print axioms innerJac                   -- [def] the literal inner Jacobian ∂F/∂z
#print axioms innerJac_eP_row            -- ∂(e_P)/∂zⱼ = −1.5·Vg·[j=0]  (single nonzero entry)
#print axioms innerJac_eQ_row            -- ∂(e_Q)/∂zⱼ =  1.5·Vg·[j=1]  (single nonzero entry)
-- R2b: loss of synchronism when the synchronous equilibrium disappears
#print axioms loss_of_sync_core
#print axioms exists_margin_of_no_zero
#print axioms loss_of_sync
-- R2a: saddle-node of the sync map (single-harmonic) + link to R2b
#print axioms amplitude_bound
#print axioms sync_pos_of_bias_gt_amp
#print axioms sync_loss_of_bias_gt_amp
#print axioms sync_equilibrium_of_amp_ge
-- F-fold sub-block (F3, algebraic) + F-H deg-2 building blocks (weak-grid Hopf/fold boundaries)
#print axioms angle_fold_tangency        -- F-fold: saddle-node tangency at D²=A²+B² (G=0 ∧ G'=0)
#print axioms sync_window_equilibrium    -- F-fold: equilibrium exists within the sync window
#print axioms F3_drift_beyond_fold       -- F3: beyond the fold ⟹ unbounded angle drift (loss of sync)
#print axioms stable_deg2_of_pos         -- F-H: deg-2 Routh–Hurwitz (a₁,a₂>0 ⟹ Hurwitz) [= PLL block]
#print axioms hopf_deg2                  -- F-H: deg-2 Hopf onset (pure-imaginary pair ⟺ a₁=0, ω=√a₂)
#print axioms stable_deg3_of_pos         -- F-H: deg-3 Routh–Hurwitz (a₁,a₂,a₃>0 ∧ a₁a₂>a₃ ⟹ Hurwitz)
#print axioms hopf_deg3                  -- F-H: deg-3 Hopf onset (pure-imaginary pair ⟺ a₃=a₁a₂, ω=√a₂)
-- L-filter GFL 3-state reductions (separate problem): SCR_H1 boundary
#print axioms pll_pendulum_charpoly      -- Thm 1: det(zI − pendulum) = z²+Kp·H·z+Ki·H
#print axioms pll_pendulum_stable        -- Thm 1: 2D PLL pendulum always stable (H'>0)
#print axioms hopf_cubic_surface         -- Thm 2.c/3: cubic Hopf surface Σ=A·B−C=0, ω=√B
#print axioms cubic_stable_of_surface_pos -- Thm 2.c/3: strong-grid side Σ>0 ⟹ Hurwitz
-- L-filter T3: Σ_iq − Σ_id factors
#print axioms sigma_diff_factor          -- T3: NUM(Σ_iq−Σ_id) = (Kp_P−Kp_Q)·G (ring)
#print axioms sigma_diff_zero_of_symmetric -- T3: Kp_P=Kp_Q ⟹ Σ_iq≡Σ_id (all Q_ref)
-- Fold/Hopf separation (lossless GFL, anchored): 2D fold-only vs 3D char-poly factorisation
#print axioms fold_hopf_2D_no_isolated_hopf -- (a) 2D: pure-imag root ⟹ ω=0∧gθ=0 (fold, no Hopf)
#print axioms fold_hopf_3D_charpoly_factor  -- (b) J13=0 ⟹ det(λI−M3q)=(λ−J11)(λ²+Kp_pll·gθ·λ+Ki_pll·gθ)
#print axioms fold_hopf_RH_factor           -- (b) a1a2−a3 = Kp_pll·gθ·Ψ̃ (fold gθ × independent Ψ̃)
#print axioms fold_hopf_fold_is_gθ          -- fold (det=0) ⟺ gθ=0, shared with 2D
#print axioms fold_hopf_Psi_spurious        -- Ψ̃=a2+J11² ⟹ Ψ̃=0 gives a2≤0 (NOT a genuine Hopf)
#print axioms fold_hopf_current_pole        -- (c) a1(3D)−a1(2D) = −J11 (current pole)
#print axioms fold_hopf_current_pole_pos    -- (c) −J11 = Kpi·quad/(2Lf) > 0 (stabilizing)
-- Work-point decoupling: current↔PLL coupling ∝ tracking error ⟹ err=0 ⟹ 2D=3D=4D fold-only
#print axioms decouple_J13_errform          -- T1/T1': ∂F_iq/∂θ_e = −(Kpi/Lf)(Kp_P·C·err_P − Kp_Q·S·err_Q)
#print axioms decouple_J03_errform          -- T2: ∂F_id/∂θ_e = −(Kpi/Lf)(Kp_P·S·err_P + Kp_Q·C·err_Q)
#print axioms decouple_J13_at_equilibrium   -- T3: err_P=err_Q=0 (true eq) ⟹ ∂F_iq/∂θ_e = 0
#print axioms decouple_J03_at_equilibrium   -- T3: err_P=err_Q=0 (true eq) ⟹ ∂F_id/∂θ_e = 0
#print axioms Dpll_charpoly                 -- PLL block charpoly λ²+Kp_pll·gθ·λ+Ki_pll·gθ (= 2D)
#print axioms fold_hopf_4D_charpoly_factor  -- T4: decoupled ⟹ det(λI−M4)=det(λI−A)·(2D PLL charpoly)
#print axioms Bpll                          -- [def] explicit PLL↔current coupling block B (assembly (b))
#print axioms Bpll_pll_structure            -- B row 2 = −Kp_pll·(row 1) (the PLL multiplies v_cqc)
#print axioms fold_hopf_4D_equilibrium_factor -- (a) end-to-end: err=0 ⟹ actual J4 = fromBlocks A 0 B Dpll ⟹ factors
-- SCR-Hopf mechanism (P-only droop, err≠0): the tracking-error term that deg-2 Routh degenerates away
#print axioms M3droop                       -- [def] 3D droop Jacobian (i_q row [J11,0,J13], J13≠0)
#print axioms M3droop_charpoly              -- 3D droop char poly (J13·J21 = droop terms)
#print axioms chi3_droop_decomp             -- χ₃ = Kp·gθ·Ψ̃ + J13·J21·(Kp²gθ−Kp·J11−Ki)  (err term ∝ err_P*)
#print axioms chi3_err_zero_recovers_foldhopf -- J13=0 ⟹ χ₃ = Kp·gθ·Ψ̃ (recovers FoldHopf, fold-bound)
#print axioms chi2_eq                       -- χ₂ = Kp_pll·gθ (deg 2: no err term ⟹ Hopf ⟺ fold)
#print axioms a1_current_pole_by_dimension
#print axioms hopf_deg4                     -- deg-4 GENUINE Hopf guard: χ₄=0 ∧ a₁,a₃>0 ⟹ ω²=a₃/a₁>0 (not spurious)
-- SCR-Hopf existence + genuineness FROM STRUCTURE (no numerics)
#print axioms chi3_root_off_fold            -- χ₃ affine in J13 ⟹ root EXISTS off the fold (gθ≠0)
#print axioms chi2_no_root_off_fold         -- χ₂=Kp·gθ has no err term ⟹ 2D no Hopf off fold (dimension)
#print axioms chi3_genuine_hopf_off_fold  -- a₁(3D)−a₁(2D) = −J11 (current pole ∝Kpi/Lf enters at 3D)
