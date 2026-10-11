import powerlib

/-! Public consumers of the library. -/

open powerlib LinearSystems

-- One semantics: a sentence is read through a family's system map, and the semantics connection
-- generates the denotations. Exactness and soundness compare the translation chain with it.
#check powerlib.Sentence.holds
#check powerlib.Family.semantics
#check powerlib.Family.chain
#check powerlib.Family.chain_eq_semantics_iff
#check powerlib.Family.chain_le_semantics_iff
#print axioms powerlib.Family.chain_eq_semantics_iff

-- The hub: the attractive sentences and sampled contraction of a linear field are the Hurwitz
-- property.
#check powerlib.Linear.holds_iff_isHurwitz
#check powerlib.Linear.sampledContraction_iff_isHurwitz
#print axioms powerlib.Linear.holds_iff_isHurwitz

-- RL: the translation chain is the semantics connection.
example : Circuits.RL.family.chain = Circuits.RL.family.semantics :=
  Circuits.RL.chain_eq_semantics

-- RL: decay at a rate is exactly a bound on the time constant, read off the faithful chain.
example (a : ℝ) (m : Circuits.RL.Impedance) :
    m ∈ Circuits.RL.family.den (.flow (.decay a)) ↔ a ≤ m.resistance / m.inductance.val := by
  rw [← (Family.chain_eq_semantics_iff.mp Circuits.RL.chain_eq_semantics
    (.flow (.decay a)) : Circuits.RL.family.Exact _)]
  simp [Circuits.RL.family, Circuits.RL.translate, Circuits.RL.Meets]

-- LCL: pole stability is exact for the attractive sentences and sampled contraction, for every
-- circuit; passivity is sound but not exact for Lyapunov stability; within passive circuits
-- conservation is losslessness.
#check powerlib.Circuits.LCL.exact_hurwitz
#check powerlib.Circuits.LCL.exact_passive
#check powerlib.Circuits.LCL.not_exact_lyapunovStable
#check powerlib.Circuits.LCL.exactUnder_conservative
#check powerlib.Circuits.LCL.not_exact_conservative
#check powerlib.Circuits.LCL.realize_passive_damped

-- Synthesis: the certificate computed from the submitted parameters places the model in a
-- denotation.
example (m : Circuits.RL.Impedance) (hR : 0 < m.resistance) {P : Flow.Property}
    (hP : P.Attractive) : m ∈ Circuits.RL.family.den (.flow P) := by
  rw [Circuits.RL.family_isLinear.den_hurwitz (Or.inl hP)]
  exact (Circuits.RL.synthesize m hR).isHurwitz

example (m : Circuits.LCL.Circuit) (hp : m.Passive) (hd : m.Damped) :
    m ∈ Circuits.LCL.family.den (.flow .contractive) := by
  rw [Circuits.LCL.family_isLinear.den_hurwitz (Or.inr rfl)]
  exact (Circuits.LCL.synthesize m hp hd).isHurwitz

-- Synthesis inside the kernel: only a rational matrix is submitted; acceptance is a requirement,
-- and the chain carries it to the sentence.
example : !![(-1 : ℚ), 10; 0, -1] ∈
    (Linear.Rational.family (n := 2)).den (.flow .globallyExponentiallyStable) := by
  rw [← Linear.Rational.exact_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)]
  refine Linear.Rational.realize_accepted ?_
  rw [TMIO.mem_realize]
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  change Linear.Synthesis.accepts _ = true
  decide +kernel

-- Multi-step goals close automatically from the reviewed rules.
example (m : Circuits.LCL.Circuit) (hp : m.Passive) (hd : m.Damped) :
    Flow.GloballyExponentiallyStable (affineLinearVectorField m.plant.A 0) 0 := by aesop

-- Passivity from stored energy, for every port-Hamiltonian plant.
example {n p : ℕ} (H : Port.PortHamiltonian n p) : H.plant.system.Passive :=
  ⟨_, H.passiveWith⟩

-- Interconnection: the impedance criterion is exact relative to component stability; port data
-- cannot certify the closed loop when a component hides a mode, and certify every flow sentence
-- when both components are minimal; closed-loop stability is no product of component
-- requirements.
#check powerlib.Circuits.Interconnection.exactUnder_hurwitz
#check powerlib.Circuits.Interconnection.soundUnder
#check powerlib.Circuits.Interconnection.portData_not_certified
#check powerlib.Circuits.Interconnection.portData_certified
#check powerlib.Circuits.Interconnection.transfer_closedLoop
#check powerlib.Circuits.Interconnection.closedLoop_not_separable
#check powerlib.Linear.similar_iff_transfer_eq
#check powerlib.Linear.transfer_certified
#check powerlib.Linear.Similar.holds_iff
#check powerlib.Linear.exists_minimal_realization
#print axioms powerlib.Linear.similar_iff_transfer_eq

-- A family supplies three semantic maps; certification, refutation and representation changes
-- are generated.
#check powerlib.Family
#check powerlib.Family.certifies
#check powerlib.Family.refutes
#check powerlib.Family.Exact.comap
#check powerlib.Family.Exact.extend

-- A Lyapunov certificate is a quadratic-decay certificate of the affine field.
#check powerlib.Linear.Certificate.toQuadraticDecay

-- Nonlinear: the cubic family is faithful, its decay rate set by the linear gain; the polynomial
-- family is sound, and cubic damping without a linear part marks where its translations stop being
-- exact.
#check powerlib.Nonlinear.Cubic.chain_eq_semantics
#check powerlib.Nonlinear.Polynomial2.chain_le_semantics
#check powerlib.Nonlinear.Polynomial2.not_exact_asymptotic
example (n : ℕ) : Flow.GloballyExponentiallyStable (Nonlinear.Cubic.field (n := n) 1) 0 :=
  Nonlinear.Cubic.globallyExponentiallyStable ⟨1, one_pos⟩
