-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: bdb58c7794c9c616c0137b77cbda8b679ed140b5e05fe781e8743b8c4537fb23
-- RL branch source SHA-256: fab63f8295f1af1f25cb3a1616519bc805ac8f581afa41a23e8165b17f24fa95
import theorem.Attributes

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
