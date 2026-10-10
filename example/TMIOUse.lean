import powerlib

open powerlib powerlib.TMIO

-- One semantic map per edge; the forward map is generated, unique, and composes.
#check powerlib.TMIO.generate
#check powerlib.TMIO.generate_unique
#check powerlib.TMIO.Seed.generate_uTO
#check powerlib.TMIO.generate_transport
#check powerlib.TMIO.realize_max
#check powerlib.TMIO.relationalSeed_whole
#check powerlib.TMIO.relationalSeed_sound
#print axioms powerlib.TMIO.Seed.generate_uTO
#print axioms powerlib.Circuits.RL.dcTest_certifies

-- The generated space of a requirement set is the maximal legal family.
example (Γ : Set Circuits.RL.Requirement) (P : Set Circuits.RL.Impedance) :
    P ⊆ realize Circuits.RL.Meets Γ ↔
      Γ ⊆ satisfaction Circuits.RL.Meets (OrderDual.toDual P) :=
  realize_max Circuits.RL.Meets Γ P

-- The certified readings of every sentence come from the generated chain.
example (ε : ℝ) (P : Flow.Property) :
    OrderDual.ofDual (generate (Circuits.RL.seed ε).uTO {P}) =
      {r | Set.Icc (r - ε) (r + ε) ⊆ Circuits.RL.window P} :=
  Circuits.RL.certified_readings ε P

-- A DC test record proves every attractive sentence for every RL model that may produce it.
example (m : Circuits.RL.Impedance)
    (hm : |Data.Analysis.estimate Circuits.RL.dcTest - m.resistance| ≤ 1 / 2)
    {P : Flow.Property} (hP : P.Attractive) :
    P.holds (LinearSystems.affineLinearVectorField m.plant.A 0) 0 :=
  Circuits.RL.dcTest_certifies hm hP

-- The state-space representation is reached by transport, not by a second development.
example (ε : ℝ) (P : Flow.Property) :
    OrderDual.ofDual (generate (Circuits.RL.stateSpaceSeed ε).u₂ (Circuits.RL.translate P)) =
      Linear.den Circuits.RL.StateSpace.plant P :=
  Circuits.RL.stateSpace_space ε P
