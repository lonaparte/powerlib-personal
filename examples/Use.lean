import Powerlib

-- Reuse stability through the equivalence between the two model descriptions.
example (m : Powerlib.Impedance) :
    (Powerlib.toStateSpace m).Stable ↔ m.Stable :=
  Powerlib.stability_agrees m

-- A verified synthesized certificate provides a theorem about its exact model.
example (m : Powerlib.Impedance) (certificate : Powerlib.Accepted m) : m.Stable :=
  certificate.stable

-- The frequency-domain equations have the same voltage/current interpretation.
example (m : Powerlib.Impedance) (s current voltage : ℂ) :
    (s + ((Powerlib.toStateSpace m).decay : ℂ)) * current =
        ((Powerlib.toStateSpace m).inputGain.val : ℂ) * voltage ↔
      voltage = m.frequency s * current :=
  Powerlib.same_port_relation m s current voltage
