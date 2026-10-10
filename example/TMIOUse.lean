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
#print axioms powerlib.TMIO.RL.dcTest_certifies

-- The generated space of a requirement set is the maximal legal family.
example (Γ : Set TMIO.RL.Requirement) (P : Set Impedance) :
    P ⊆ realize TMIO.RL.Meets Γ ↔ Γ ⊆ satisfaction TMIO.RL.Meets (OrderDual.toDual P) :=
  realize_max TMIO.RL.Meets Γ P

-- Added requirements reuse the generated conclusion.
example (Δ : Set TMIO.RL.Requirement) (m : Impedance)
    (hm : m ∈ realize TMIO.RL.Meets (TMIO.RL.translate .asymptoticallyStable ∪ Δ)) :
    AsymptoticallyStable m 0 0 :=
  TMIO.RL.realize_reuse Δ hm

-- A DC test record certifies asymptotic stability of the canonical RL model.
example (m : Impedance)
    (hm : |TMIO.Analysis.estimate TMIO.RL.dcTest - m.resistance| ≤ 1 / 2) :
    AsymptoticallyStable m 0 0 :=
  TMIO.RL.dcTest_certifies hm

-- The state-space representation is reached by transport, not by a second development.
example (ε : ℝ) (s : StateSpace)
    (hs : s ∈ OrderDual.ofDual (generate (TMIO.RL.stateSpaceSeed ε).u₂
      (TMIO.RL.translate .asymptoticallyStable))) : s.Stable :=
  TMIO.RL.stateSpace_space_stable ε hs
