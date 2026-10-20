-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: bdb58c7794c9c616c0137b77cbda8b679ed140b5e05fe781e8743b8c4537fb23
-- RL branch source SHA-256: fab63f8295f1af1f25cb3a1616519bc805ac8f581afa41a23e8165b17f24fa95
import theorem.Attributes

/-! # Generated LCL parameter conversion

The executable conversion of the LCL filter between circuit parameters and state-space
parameters, generated from the Agda scaffold: the RL branch conversion on each of the two
branches and the reciprocal on the capacitance. The file is generated; Lean independently checks
the endpoint, not a translation of the Agda proof.

Model boundary.
* Parametric in the coefficient domain `Scalar` and the positive scaling factors `Unit`, with
  arbitrary operations `scale` and `reciprocal`; `theorem/Circuits/LCL.lean` instantiates them on
  the reals.
* No dynamics: a map of parameters only.

Source: scaffold `theorem/LCLConversion.agda` (LCL filter: circuit parameters ↔ state-space
parameters), reusing the RL branch scaffold `theorem/Conversion.agda`, through the
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
@[simp, powerlib_foundation] theorem convertLCL_spec {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : ((Scalar × Unit) × (Scalar × Unit)) × Unit) :
    convertLCL scale reciprocal x =
      (((scale x.1.1.1 (reciprocal x.1.1.2), reciprocal x.1.1.2),
        (scale x.1.2.1 (reciprocal x.1.2.2), reciprocal x.1.2.2)), reciprocal x.2) := rfl

end powerlib.generated
