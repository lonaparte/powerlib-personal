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
#check powerlib.TMIO.generate_inj
#check powerlib.TMIO.chain_eq_satisfaction_iff
#check powerlib.TMIO.chain_le_satisfaction_iff
#print axioms powerlib.TMIO.Seed.generate_uTO
#print axioms powerlib.Circuits.RL.dcTest_certified

-- The generated space of a requirement set is the maximal legal family.
example (Γ : Set Circuits.RL.Requirement) (P : Set Circuits.RL.Impedance) :
    P ⊆ realize Circuits.RL.Meets Γ ↔
      Γ ⊆ satisfaction Circuits.RL.Meets (OrderDual.toDual P) :=
  realize_max Circuits.RL.Meets Γ P

-- The certified readings of every sentence come from the generated chain.
example (ε : ℝ) (s : Sentence) :
    OrderDual.ofDual (generate (Circuits.RL.seed ε).uTO {s}) =
      {r | Set.Icc (r - ε) (r + ε) ⊆ Circuits.RL.window s} :=
  Circuits.RL.certified_readings ε s

-- A DC test record is certified for every attractive sentence, so every RL model that may produce
-- its estimate satisfies it.
example (m : Circuits.RL.Impedance)
    (hm : |Data.Analysis.estimate Circuits.RL.dcTest - m.resistance| ≤ 1 / 2)
    {P : Flow.Property} (hP : P.Attractive) : m ∈ Circuits.RL.family.den (.flow P) := by
  have hd := Circuits.RL.dcTest_certified (Or.inl hP)
  rw [Circuits.RL.certified_records, Set.mem_preimage] at hd
  exact Family.certifies
    (fun s _ => (Family.chain_eq_semantics_iff.mp Circuits.RL.chain_eq_semantics s).sound) hd hm
    _ rfl

-- The state-space representation is reached by transport, not by a second development.
example (s : Sentence) : (Circuits.RL.family.comap Circuits.RL.toImpedance).Exact s :=
  (Family.chain_eq_semantics_iff.mp Circuits.RL.chain_eq_semantics s).comap _
