-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: e96a5ac2c6e824ec217b8acc1b43efc5dd966910c2cad07c691fc0ff6feba6d7
-- RL branch source SHA-256: aa6a54e56f903f4ff6c9d01798ea906c44724f739fe122319b0801be0ed697a1
import theorem.Attributes

/-! # Generated LCL parameter conversion

The executable conversion of the LCL filter between circuit parameters and state-space
parameters, generated from the Agda scaffold: the RL branch conversion on each of the two
branches and the reciprocal on the capacitance. The file is generated; Lean independently checks
the endpoint, not a translation of the Agda proof.

Model boundary.
* Parametric in the coefficient domain `Scalar` and the positive scaling factors `Unit`, with
  arbitrary operations `scale` and `reciprocal`; `theorem/Passive/LCL.lean` instantiates them on
  the reals.
* No dynamics: a map of parameters only.

Source: scaffold `theorem/Passive/LCLConversion.agda` (LCL filter: circuit parameters ↔ state-space
parameters), reusing the RL branch scaffold `theorem/Passive/Conversion.agda`, through the
Agda-normalized executable conversion; the comment lines at the top of this file record the
generator and the SHA-256 of both Agda sources.

Results.
* `convertLCL` and its endpoint contract `convertLCL_spec`.
-/

namespace powerlib.generated

def convertLCL {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : ((Scalar × Unit) × (Scalar × Unit)) × Unit) :
    ((Scalar × Unit) × (Scalar × Unit)) × Unit :=
  ((((scale x.1.1.1 (reciprocal x.1.1.2)), (reciprocal x.1.1.2)), ((scale x.1.2.1 (reciprocal x.1.2.2)), (reciprocal x.1.2.2))), (reciprocal x.2))

-- Lean independently checks the endpoint, not a translation of the Agda proof.
@[tmio T, simp, powerlib_foundation] theorem convertLCL_spec {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : ((Scalar × Unit) × (Scalar × Unit)) × Unit) :
    convertLCL scale reciprocal x =
      (((scale x.1.1.1 (reciprocal x.1.1.2), reciprocal x.1.1.2),
        (scale x.1.2.1 (reciprocal x.1.2.2), reciprocal x.1.2.2)), reciprocal x.2) := rfl

end powerlib.generated
