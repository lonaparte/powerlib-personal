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
