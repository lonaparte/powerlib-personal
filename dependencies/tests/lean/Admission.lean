import powerlib

-- Certificate admission.
/-! Certificates are typed by the exact submitted model. The plant is reconstructed from the
submission by the family's plant map, and the certificate type is indexed by that plant's state
matrix or by the model itself; a certificate for another model does not typecheck. For RL and LCL
the witness is computed from the submitted parameters by the library's closed-form synthesizers;
for rational matrices and rational LCL parameters the kernel runs the generic synthesizer and its
check (S-level). For larger rational matrices the synthesizer is evaluated during elaboration and
the kernel only checks its proposal (S-level). For polynomial fields only the
polynomials are submitted and the kernel runs the sum-of-squares synthesizer and the coefficient
check (S-level); one polynomial fixture supplies its witness and tests verification only. -/

noncomputable section

open powerlib LinearSystems Matrix

-- RL: only `R = 2` and `L = 1` are submitted.
namespace RLAdmission

def submittedModel : Circuits.RL.Impedance := ⟨2, ⟨1, by norm_num⟩⟩

def accepted : Linear.Certificate submittedModel.plant.A :=
  Circuits.RL.synthesize submittedModel (by norm_num [submittedModel])

-- The synthesized witness is `p = 1/4`.
@[powerlib_foundation] theorem accepted_P : accepted.P = !![1 / 4] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [accepted, Circuits.RL.synthesize, submittedModel]

@[powerlib_domain] theorem globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable (affineLinearVectorField submittedModel.plant.A 0) 0 :=
  accepted.holds 0 (P := .globallyExponentiallyStable) trivial

@[powerlib_domain] theorem mem_den {P : Flow.Property} (hP : P.Attractive) :
    submittedModel ∈ Linear.den Circuits.RL.Impedance.plant P :=
  accepted.mem_den hP

-- The physical energy is a storage function: the branch is passive.
@[powerlib_domain] theorem passive : submittedModel.plant.system.Passive :=
  ⟨_, (Circuits.RL.kyp submittedModel (by norm_num [submittedModel])).passiveWith⟩

end RLAdmission

-- LCL: only the component values are submitted.
namespace LCLAdmission

def submittedModel : Circuits.LCL.Circuit :=
  ⟨⟨1, ⟨1, by norm_num⟩⟩, ⟨1, ⟨1, by norm_num⟩⟩, ⟨1, by norm_num⟩⟩

def accepted : Linear.Certificate submittedModel.plant.A :=
  Circuits.LCL.synthesize submittedModel
    (by norm_num [submittedModel, Circuits.LCL.Circuit.Passive])
    (by norm_num [submittedModel, Circuits.LCL.Circuit.Damped])

@[powerlib_domain] theorem globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable (affineLinearVectorField submittedModel.plant.A 0) 0 :=
  accepted.holds 0 (P := .globallyExponentiallyStable) trivial

@[powerlib_domain] theorem passive : submittedModel.plant.system.Passive :=
  ⟨_, (Circuits.LCL.kyp submittedModel
    (by norm_num [submittedModel, Circuits.LCL.Circuit.Passive])).passiveWith⟩

end LCLAdmission

-- LTI: only a rational matrix is submitted; the kernel runs the synthesizer and the check.
namespace LTIAdmission

def submittedMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 10; 0, -1]

def accepted : Linear.Certificate (Linear.Synthesis.real submittedMatrix) :=
  Linear.Synthesis.certificateOf submittedMatrix (by decide +kernel)

@[powerlib_foundation] theorem real_submittedMatrix :
    Linear.Synthesis.real submittedMatrix = !![(-1 : ℝ), 10; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [submittedMatrix]

@[powerlib_domain] theorem globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable (affineLinearVectorField !![(-1 : ℝ), 10; 0, -1] 0) 0 := by
  rw [← real_submittedMatrix]
  exact accepted.holds 0 (P := .globallyExponentiallyStable) trivial

-- The synthesized witness is the exact solution of the Lyapunov equation.
@[powerlib_foundation] theorem synthesized_P :
    (Linear.Synthesis.synth submittedMatrix).map (·.P) = some !![1 / 2, 5 / 2; 5 / 2, 51 / 2] := by
  decide +kernel

-- A matrix with an unstable mode is rejected by the kernel's run of the check.
@[powerlib_foundation] theorem unstable_rejected :
    Linear.Synthesis.accepts !![(1 : ℚ), 0; 0, -1] = false := by
  decide +kernel

-- An arbitrary proposal is rejected: the identity witness fails the check.
@[powerlib_foundation] theorem wrong_witness_rejected :
    ¬ (⟨1, 1, fun _ => 1⟩ : Linear.Synthesis.Witness 2).Valid submittedMatrix := by
  decide +kernel

def differentMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![-2, 10; 0, -1]

-- A certificate for another matrix is not a certificate for the submitted one.
@[powerlib_foundation] theorem another_model_rejected : True := by
  fail_if_success
    have wrong : Linear.Certificate (Linear.Synthesis.real differentMatrix) := accepted
  trivial

end LTIAdmission

-- A larger LTI submission: the synthesizer runs during elaboration, the kernel checks its proposal.
namespace LargeLTIAdmission

/-- Eight states, negative diagonal dominating the coupling. -/
def submittedMatrix : Matrix (Fin 8) (Fin 8) ℚ :=
  !![-8, 1, 0, 1, 0, 2, 0, 1; 0, -8, 1, 0, 1, 0, 1, 0; 1, 1, -8, 1, 0, 0, 0, 1;
    0, 1, 0, -8, 1, 1, 0, 0; 1, 0, 1, 0, -8, 1, 1, 0; 0, 2, 0, 1, 0, -8, 0, 1;
    1, 0, 0, 0, 1, 0, -8, 1; 0, 0, 1, 1, 0, 1, 0, -8]

def accepted : Linear.Certificate (Linear.Synthesis.real submittedMatrix) :=
  lyapunov_certificate% submittedMatrix

@[powerlib_domain] theorem globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable
      (affineLinearVectorField (Linear.Synthesis.real submittedMatrix) 0) 0 :=
  accepted.holds 0 (P := .globallyExponentiallyStable) trivial

-- A matrix with an unstable mode: the Lyapunov equation is solvable, but the solution is
-- indefinite and the kernel rejects the proposal.
@[powerlib_foundation] theorem indefinite_rejected : True := by
  fail_if_success
    have := lyapunov_certificate% (!![(1 : ℚ), 0; 0, -2])
  trivial

-- The proposal for that matrix does exist; only the check refuses it.
@[powerlib_foundation] theorem indefinite_proposed :
    (Linear.Synthesis.synth (!![(1 : ℚ), 0; 0, -2])).map (·.check !![(1 : ℚ), 0; 0, -2]) =
      some false := by
  decide +kernel

end LargeLTIAdmission

-- LCL with a negative resistance: only the rational parameters are submitted. The closed-form
-- synthesizer needs passivity; the kernel's run of the generic synthesizer does not.
namespace NegativeResistanceAdmission

def submitted : Circuits.LCL.RationalCircuit :=
  ⟨-1 / 10, 1, 1, 2, 1, by norm_num, by norm_num, by norm_num⟩

@[powerlib_foundation] theorem not_passive : ¬ submitted.circuit.Passive := by
  intro h
  have := h.1
  norm_num [submitted, Circuits.LCL.RationalCircuit.circuit] at this

def accepted : Linear.Certificate submitted.circuit.plant.A :=
  submitted.certificate (by decide +kernel)

@[powerlib_domain] theorem globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable (affineLinearVectorField submitted.circuit.plant.A 0) 0 :=
  accepted.holds 0 (P := .globallyExponentiallyStable) trivial

end NegativeResistanceAdmission

-- Polynomial family: only the fields are submitted; the kernel runs the synthesizer and the check.
namespace PolynomialAdmission

open Nonlinear.Polynomial2

/-- `x' = -x - x³`, `y' = -y`. -/
def submittedModel : Model := ⟨[⟨-1, (1, 0)⟩, ⟨-1, (3, 0)⟩], [⟨-1, (0, 1)⟩]⟩

def accepted : Certificate submittedModel := certificateOf submittedModel (by decide +kernel)

@[powerlib_domain] theorem globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable submittedModel.field 0 :=
  accepted.globallyExponentiallyStable

/-- `x' = -x - x³ + x y² / 2`, `y' = -y - y³ + x² y / 2`. -/
def coupledModel : Model :=
  ⟨[⟨-1, (1, 0)⟩, ⟨-1, (3, 0)⟩, ⟨1 / 2, (1, 2)⟩], [⟨-1, (0, 1)⟩, ⟨-1, (0, 3)⟩, ⟨1 / 2, (2, 1)⟩]⟩

def coupledAccepted : Certificate coupledModel := certificateOf coupledModel (by decide +kernel)

@[powerlib_domain] theorem coupled_globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable coupledModel.field 0 :=
  coupledAccepted.globallyExponentiallyStable

-- Its decay certificate needs a square mixing `x²` and `y²`: `(x² - y²/2)²`.
@[powerlib_foundation] theorem coupled_mixed_square :
    ((synth coupledModel).map fun w => w.decay_sos.map (·.poly)).any
      (·.contains [⟨1, (2, 0)⟩, ⟨-1 / 2, (0, 2)⟩]) = true := by
  decide +kernel

/-- `x' = -x + 2y - x y²`, `y' = -3y - x² y`: the Lyapunov energy of the non-normal linearization
leaves cubic cross terms; a diagonal energy of the family succeeds. -/
def nonnormalModel : Model :=
  ⟨[⟨-1, (1, 0)⟩, ⟨2, (0, 1)⟩, ⟨-1, (1, 2)⟩], [⟨-3, (0, 1)⟩, ⟨-1, (2, 1)⟩]⟩

def nonnormalAccepted : Certificate nonnormalModel :=
  certificateOf nonnormalModel (by decide +kernel)

@[powerlib_domain] theorem nonnormal_globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable nonnormalModel.field 0 :=
  nonnormalAccepted.globallyExponentiallyStable

/-- The cascade `x' = -2x + y²`, `y' = -y`: no energy of the family gives a decay identity, and the
synthesizer proposes nothing. This is unproved, not refuted. -/
def cascadeModel : Model := ⟨[⟨-2, (1, 0)⟩, ⟨1, (0, 2)⟩], [⟨-1, (0, 1)⟩]⟩

@[powerlib_foundation] theorem cascade_unproved : accepts cascadeModel = false := by
  decide +kernel

/-- A supplied witness passes the same check: verification, not synthesis. -/
def suppliedWitness : Witness := ⟨1, 0, 1, 1, 1, 2, [], [], [⟨2, [⟨1, (2, 0)⟩]⟩]⟩

def supplied : Certificate submittedModel := ⟨suppliedWitness, by decide +kernel⟩

-- The same witness is rejected for another model.
@[powerlib_foundation] theorem supplied_rejected_elsewhere :
    suppliedWitness.check coupledModel = false := by
  decide +kernel

-- A certificate for another model is not a certificate for the submitted one.
@[powerlib_foundation] theorem another_model_rejected : True := by
  fail_if_success
    have wrong : Certificate coupledModel := accepted
  trivial

end PolynomialAdmission

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let registered := powerlib.Registry.theoremNames env
  let admitted := registered.filter fun name =>
    #[`RLAdmission, `LCLAdmission, `LTIAdmission, `LargeLTIAdmission,
      `NegativeResistanceAdmission, `PolynomialAdmission].contains name.getRoot
  for name in admitted do
    if powerlib.Registry.kindOf? env name == some .domain then
      logInfo m!"POWERLIB_ADMITTED_THEOREM {name}"
    for ax in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected axiom {ax} in {name}"
  -- The synthesized certificates are computed by the library synthesizers from the submission;
  -- a certificate synthesized during elaboration is admitted only through the checked proposal.
  -- Proofs abstracted out of a certificate are followed.
  let used (certificate : Name) : CommandElabM (Array Name) := do
    let mut todo := #[certificate]
    let mut seen : Array Name := #[]
    while h : todo.size > 0 do
      let name := todo.back
      todo := todo.pop
      if seen.contains name then continue
      seen := seen.push name
      let some value := (← getConstInfo name).value? (allowOpaque := true) | continue
      for c in value.getUsedConstants do
        if certificate.isPrefixOf c then todo := todo.push c else seen := seen.push c
    return seen
  for (certificate, synthesizer) in #[(`RLAdmission.accepted, `powerlib.Circuits.RL.synthesize),
      (`LCLAdmission.accepted, `powerlib.Circuits.LCL.synthesize),
      (`LTIAdmission.accepted, `powerlib.Linear.Synthesis.certificateOf),
      (`LargeLTIAdmission.accepted, `powerlib.Linear.Synthesis.Witness.valid_of_check),
      (`NegativeResistanceAdmission.accepted,
        `powerlib.Circuits.LCL.RationalCircuit.certificate),
      (`PolynomialAdmission.accepted, `powerlib.Nonlinear.Polynomial2.certificateOf),
      (`PolynomialAdmission.coupledAccepted, `powerlib.Nonlinear.Polynomial2.certificateOf),
      (`PolynomialAdmission.nonnormalAccepted, `powerlib.Nonlinear.Polynomial2.certificateOf)] do
    unless (← used certificate).contains synthesizer do
      throwError "{certificate} was not produced by {synthesizer}"
  logInfo "POWERLIB_ADMISSION_OK"
