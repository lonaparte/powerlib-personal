/-
  Slow Frequency Mode of a Power-Locked GFL-VSC — formal proofs (Lean 4 + Mathlib).

  Root module: imports the model + the three theorems.

    GFL.Model     §1–§5  parameters, power algebra, Lemma 0 (Power Lock), Cor 0a
    GFL.TheoremA  §7 A   zero eigenvalue of the unanchored Jacobian (Variant U)
    GFL.TheoremB  §7 B   slow eigenvalue −b = −D/(2H): reduced exact + Schur term 0
    GFL.TheoremC  §7 C   oscillation onset: charpoly λ²+bλ+βKs, roots, β·Ks > b²/4
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
import GFL.ScrHopf4D
import GFL.ScrHopfAnchor
import GFL.ScrHopfCubic
import GFL.ScrAxis
import GFL.ScrHopfNumeric
import GFL.ScrHopf3DNumeric
import GFL.ScrHopfDim
