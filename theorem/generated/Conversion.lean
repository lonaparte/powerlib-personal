-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: fab63f8295f1af1f25cb3a1616519bc805ac8f581afa41a23e8165b17f24fa95
import theorem.Attributes

/-! # Generated RL parameter conversion

The executable conversion of the RL branch between state-space parameters `(a, b)` and impedance
parameters `(R, L)`, generated from the Agda scaffold: one executable body serves both directions,
`(x, y) ↦ (scale x (reciprocal y), reciprocal y)`. The file is generated; only its endpoint
contract is checked here, by the Lean kernel.

Model boundary.
* Parametric in the coefficient domain `Scalar` and the positive scaling factors `Unit`, with
  arbitrary operations `scale` and `reciprocal`; `theorem/Circuits/RL.lean` instantiates them on
  the reals and proves the algebraic laws (involutive reciprocal, cancellation) there.
* No dynamics: a map of parameters only.

Source: scaffold `theorem/Conversion.agda` (RL branch: impedance parameters ↔ state-space
parameters), through the Agda-normalized executable conversion; the first two comment lines of
this file record the generator and the SHA-256 of the Agda source.

Results.
* `convert` and its endpoint contract `convert_spec`.
-/

namespace powerlib.generated

def convert {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : Scalar × Unit) : Scalar × Unit :=
  ((scale x.1 (reciprocal x.2)), (reciprocal x.2))

-- The independent endpoint contract is checked by the Lean kernel.
@[tmio T, simp, powerlib_foundation] theorem convert_spec {Scalar Unit : Type} (scale : Scalar → Unit → Scalar)
    (reciprocal : Unit → Unit) (x : Scalar × Unit) :
    convert scale reciprocal x = (scale x.1 (reciprocal x.2), reciprocal x.2) := rfl

end powerlib.generated
