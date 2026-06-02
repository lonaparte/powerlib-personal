/-
  Integrity audit.  `#print axioms` lists the axioms each theorem actually depends on.
  A clean proof shows only Lean/Mathlib's standard axioms
  `[propext, Classical.choice, Quot.sound]` and crucially NOT `sorryAx`
  (which would indicate a `sorry`/`admit` hole).  See `lake build GFL.Audit` output.
-/
import GFL.Model
import GFL.TheoremA
import GFL.TheoremB
import GFL.TheoremC
import GFL.Calculus
import GFL.AsymptoticB
import GFL.LiteralModel
import GFL.LossOfSync

open GFL

#print axioms powerLock                  -- Lemma 0 (Power Lock)
#print axioms syncCoeff_zero             -- Corollary 0a (K = 0)
#print axioms equilib_relations          -- Corollary 0b (remaining relations)
#print axioms variantS_dw_zero           -- Corollary 0b, Variant S (dw* = 0)
#print axioms variantU_zero_eigenvalue   -- Theorem A (0 ∈ spec)
#print axioms variantU_charpoly_factor   -- Theorem A, simple zero (exactly one)
#print axioms reduced_exact              -- Theorem B (reduced, exact)
#print axioms schur_term_zero            -- Theorem B (O(1) Schur term vanishes)
#print axioms variantS_schur_det         -- Theorem B (full-system Schur determinant)
#print axioms charpoly_eq                -- Theorem C (companion char. poly)
#print axioms thmC_Ks_zero               -- Theorem C, (C1)
#print axioms thmC_onset                 -- Theorem C, (C2)
-- calculus completions (use Mathlib's analysis tower)
#print axioms syncCoeff_deriv_zero       -- Cor 0a as a literal derivative
#print axioms branch_iD_tangent_zero     -- v₀ = 0 (i_d-tangent)
#print axioms branch_linearization       -- IFT linearisation  A·v = −c
#print axioms schur_term_zero_of_branch  -- Thm B Schur term, derived from the C¹ branch
#print axioms variantU_zero_right_eigenvector
#print axioms thmC_roots_exhaustive
-- C2 overdamped (real-root) case + full discriminant coverage
#print axioms thmC_real_roots
-- W3 derived from the implicit function theorem (W2 + smoothness)
#print axioms branch_of_ift
#print axioms branch_linearization_of_ift
-- P0 (Theorem B O(b²)) partial: algebraic core
#print axioms resolvent_id
#print axioms schur_term_at_neg_b
#print axioms kappa_eq_const_mul_b
#print axioms schur_term_b_sq
-- P1 (literal model) partial: InnerField instance
#print axioms litInnerField
-- R2b: loss of synchronism when the synchronous equilibrium disappears
#print axioms loss_of_sync_core
#print axioms exists_margin_of_no_zero
#print axioms loss_of_sync
