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

#print axioms powerLock                 -- Lemma 0 (Power Lock)
#print axioms syncCoeff_zero            -- Corollary 0a (K = 0)
#print axioms variantU_zero_eigenvalue  -- Theorem A
#print axioms reduced_exact             -- Theorem B (reduced, exact)
#print axioms schur_term_zero           -- Theorem B (Schur term vanishes)
#print axioms charpoly_eq               -- Theorem C (companion char. poly)
#print axioms thmC_Ks_zero              -- Theorem C, (C1)
#print axioms thmC_onset                -- Theorem C, (C2)
