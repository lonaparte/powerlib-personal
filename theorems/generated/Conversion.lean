-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: 65954bf2550bb61d55b6a146489e5bfa0ac8002cdac6d154d7ea9dd46a71bfca
import theorems.Attributes

namespace powerlib.generated

def convert {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : Scalar × Unit) : Scalar × Unit :=
  ((scale x.1 (reciprocal x.2)), (reciprocal x.2))

-- The independent endpoint contract is checked by the Lean kernel.
@[simp, powerlib_foundation] theorem convert_spec {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : Scalar × Unit) :
    convert scale reciprocal x = (scale x.1 (reciprocal x.2), reciprocal x.2) := rfl

end powerlib.generated
