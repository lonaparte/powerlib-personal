import powerlib

-- Reuse stability through the equivalence between the two model descriptions.
example (m : powerlib.Impedance) :
    (powerlib.toStateSpace m).Stable ↔ m.Stable :=
  powerlib.stability_agrees m

-- A verified synthesized certificate provides a theorem about its exact model.
example (m : powerlib.Impedance) (certificate : powerlib.Accepted m) : m.Stable :=
  certificate.stable

-- The frequency-domain equations have the same voltage/current interpretation.
example (m : powerlib.Impedance) (s current voltage : ℂ) :
    (s + ((powerlib.toStateSpace m).decay : ℂ)) * current =
        ((powerlib.toStateSpace m).inputGain.val : ℂ) * voltage ↔
      voltage = m.frequency s * current :=
  powerlib.same_port_relation m s current voltage

-- Importing powerlib also registers its theorems for automatic proof search.
example (m : powerlib.Impedance) (certificate : powerlib.Accepted m) :
    powerlib.AsymptoticallyStable m 0 0 := by
  powerlib_auto

-- This is about every forward trajectory around any constant-input equilibrium.
example (m : powerlib.Impedance) (certificate : powerlib.Accepted m)
    (voltage equilibrium : ℝ) (he : powerlib.IsEquilibrium m voltage equilibrium) :
    powerlib.GloballyExponentiallyStable m voltage equilibrium := by
  powerlib_auto
