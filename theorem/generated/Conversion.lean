-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: fab63f8295f1af1f25cb3a1616519bc805ac8f581afa41a23e8165b17f24fa95
import theorem.Attributes

namespace powerlib.generated

def convert {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : Scalar × Unit) : Scalar × Unit :=
  ((scale x.1 (reciprocal x.2)), (reciprocal x.2))

-- The independent endpoint contract is checked by the Lean kernel.
@[simp, powerlib_foundation] theorem convert_spec {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : Scalar × Unit) :
    convert scale reciprocal x = (scale x.1 (reciprocal x.2), reciprocal x.2) := rfl

end powerlib.generated
