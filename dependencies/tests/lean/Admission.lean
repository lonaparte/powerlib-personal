import powerlib

-- Certificate admission.
/-! Certificates are typed by the exact submitted model. The plant is reconstructed from the
submission by the family's plant map, and the certificate type is indexed by that plant's state
matrix or by the model itself; a certificate for another model does not typecheck. For RL and LCL
the witness is computed from the submitted parameters by the library's closed-form synthesizers;
for rational matrices and rational LCL parameters the kernel runs the generic synthesizer and its
check (S-level). The polynomial fixture supplies its witness and therefore tests verification
only. -/

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

-- Polynomial family: a supplied sum-of-squares witness (verification).
namespace PolynomialAdmission

open Nonlinear.Polynomial2

/-- `x' = -x - x³`, `y' = -y`. -/
def submittedModel : Model := ⟨[⟨-1, (1, 0)⟩, ⟨-1, (3, 0)⟩], [⟨-1, (0, 1)⟩]⟩

def accepted : Accepted submittedModel where
  p00 := 1
  p01 := 0
  p11 := 1
  lower := 1
  upper := 1
  rate := 2
  lower_sos := []
  upper_sos := []
  decay_sos := [⟨2, [⟨1, (2, 0)⟩]⟩]
  lower_pos := by norm_num
  upper_pos := by norm_num
  rate_pos := by norm_num
  lower_nonneg := by simp
  upper_nonneg := by simp
  decay_nonneg := by norm_num
  field_zero := by
    ext i
    fin_cases i <;> simp [Model.field, submittedModel, eval]
  lower_identity x y := by
    simp [quadratic, sosEval]
  upper_identity x y := by
    simp [quadratic, sosEval]
  decay_identity x y := by
    simp [lie, quadratic, sosEval, eval, submittedModel]
    ring

@[powerlib_domain] theorem globallyExponentiallyStable :
    Flow.GloballyExponentiallyStable submittedModel.field 0 :=
  accepted.globallyExponentiallyStable

end PolynomialAdmission

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let registered := powerlib.Registry.theoremNames env
  let admitted := registered.filter fun name =>
    #[`RLAdmission, `LCLAdmission, `LTIAdmission, `NegativeResistanceAdmission,
      `PolynomialAdmission].contains name.getRoot
  for name in admitted do
    if powerlib.Registry.kindOf? env name == some .domain then
      logInfo m!"POWERLIB_ADMITTED_THEOREM {name}"
    for ax in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected axiom {ax} in {name}"
  -- The synthesized certificates are computed by the library synthesizers from the submission.
  for (certificate, synthesizer) in #[(`RLAdmission.accepted, `powerlib.Circuits.RL.synthesize),
      (`LCLAdmission.accepted, `powerlib.Circuits.LCL.synthesize),
      (`LTIAdmission.accepted, `powerlib.Linear.Synthesis.certificateOf),
      (`NegativeResistanceAdmission.accepted,
        `powerlib.Circuits.LCL.RationalCircuit.certificate)] do
    let info ← getConstInfo certificate
    let some value := info.value? (allowOpaque := true) | throwError "Missing {certificate}"
    unless value.getUsedConstants.contains synthesizer do
      throwError "{certificate} was not produced by {synthesizer}"
  logInfo "POWERLIB_ADMISSION_OK"
