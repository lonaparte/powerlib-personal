import powerlib
import theorems.Dynamics.PolynomialTactic

/-! Witness-free nonlinear synthesis through the public Lean tactic. Positive
inputs contain only the original rational polynomial vector fields. The tactic
must synthesize the quadratic energy, norm bounds, rate, and SOS decomposition,
then prove the model-indexed certificate and full trajectory semantics. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable section
namespace powerlib.Tests.PolynomialStability

open powerlib.Dynamics powerlib.Dynamics.Polynomial2

def coupled : Model :=
  ⟨[⟨-1, (1, 0)⟩, ⟨1, (0, 1)⟩, ⟨-1, (3, 0)⟩, ⟨-2, (1, 2)⟩],
   [⟨-2, (0, 1)⟩, ⟨-3, (2, 1)⟩, ⟨-1, (0, 3)⟩]⟩

-- The quartic dissipation is rank one. A rational Gram parameter of 5/3 is
-- required, so checking only the first few integer candidates is insufficient.
def rankOneCoupled : Model :=
  ⟨[⟨-1, (1, 0)⟩, ⟨1, (0, 1)⟩, ⟨-1, (3, 0)⟩,
     ⟨-3, (2, 1)⟩, ⟨-3, (1, 2)⟩, ⟨-1, (0, 3)⟩],
   [⟨-2, (0, 1)⟩, ⟨-2, (3, 0)⟩, ⟨-6, (2, 1)⟩,
     ⟨-6, (1, 2)⟩, ⟨-2, (0, 3)⟩]⟩

-- A different linear coupling produces a non-diagonal energy automatically.
def heldOut : Model :=
  ⟨[⟨-3, (1, 0)⟩, ⟨1, (0, 1)⟩, ⟨-1, (3, 0)⟩, ⟨-1, (1, 2)⟩],
   [⟨-2, (0, 1)⟩, ⟨-1, (2, 1)⟩, ⟨-1, (0, 3)⟩]⟩

def namedField0 : Polynomial := heldOut.field0
def namedField1 : Polynomial := heldOut.field1
def namedFields : Model := ⟨namedField0, namedField1⟩

-- Equality in all three certificate inequalities gives empty SOS lists.
def linearHalf : Model :=
  ⟨[⟨-1 / 2, (1, 0)⟩], [⟨-1 / 2, (0, 1)⟩]⟩

def coupledAccepted : Polynomial2.Accepted coupled := by polynomial_stability coupled
def rankOneAccepted : Polynomial2.Accepted rankOneCoupled := by polynomial_stability rankOneCoupled
def heldOutAccepted : Polynomial2.Accepted heldOut := by polynomial_stability heldOut
def linearHalfAccepted : Polynomial2.Accepted linearHalf := by polynomial_stability linearHalf

#guard ((Polynomial2.synthesize heldOut).map (fun w => decide (w.p01 ≠ 0))) == some true
#guard ((Polynomial2.synthesize linearHalf).map
  (fun w => w.lower_sos.isEmpty && w.upper_sos.isEmpty && w.decay_sos.isEmpty)) == some true

-- Exercise direct application to each semantic goal, rather than only Accepted.
theorem coupled_forward_complete : ForwardComplete coupled.field := by
  polynomial_stability coupled

theorem heldOut_exponentially_stable : Dynamics.GloballyExponentiallyStable heldOut.field 0 := by
  polynomial_stability heldOut

theorem rankOne_asymptotically_stable : Dynamics.GloballyAsymptoticallyStable rankOneCoupled.field 0 := by
  polynomial_stability rankOneCoupled

theorem let_bound_model_exponentially_stable : Dynamics.GloballyExponentiallyStable heldOut.field 0 := by
  let localModel : Model := heldOut
  have h : Dynamics.GloballyExponentiallyStable localModel.field 0 := by
    polynomial_stability localModel
  exact h

theorem named_field_definitions_exponentially_stable :
    Dynamics.GloballyExponentiallyStable namedFields.field 0 := by
  polynomial_stability namedFields

theorem coupled_semantics :
    ForwardComplete coupled.field ∧ Dynamics.GloballyExponentiallyStable coupled.field 0 ∧
      Dynamics.GloballyAsymptoticallyStable coupled.field 0 :=
  ⟨coupledAccepted.forwardComplete, coupledAccepted.globallyExponentiallyStable,
    coupledAccepted.globallyAsymptoticallyStable⟩

theorem rankOne_semantics :
    ForwardComplete rankOneCoupled.field ∧ Dynamics.GloballyExponentiallyStable rankOneCoupled.field 0 ∧
      Dynamics.GloballyAsymptoticallyStable rankOneCoupled.field 0 :=
  ⟨rankOneAccepted.forwardComplete, rankOneAccepted.globallyExponentiallyStable,
    rankOneAccepted.globallyAsymptoticallyStable⟩

theorem heldOut_semantics :
    ForwardComplete heldOut.field ∧ Dynamics.GloballyExponentiallyStable heldOut.field 0 ∧
      Dynamics.GloballyAsymptoticallyStable heldOut.field 0 :=
  ⟨heldOutAccepted.forwardComplete, heldOutAccepted.globallyExponentiallyStable,
    heldOutAccepted.globallyAsymptoticallyStable⟩

theorem linearHalf_semantics :
    ForwardComplete linearHalf.field ∧ Dynamics.GloballyExponentiallyStable linearHalf.field 0 ∧
      Dynamics.GloballyAsymptoticallyStable linearHalf.field 0 :=
  ⟨linearHalfAccepted.forwardComplete, linearHalfAccepted.globallyExponentiallyStable,
    linearHalfAccepted.globallyAsymptoticallyStable⟩

theorem all_finite_trajectories_decay {model : Model} (c : Polynomial2.Accepted model)
    {φ : ℝ → State 2} {a b t : ℝ}
    (hφ : IsTrajectoryOn φ model.field a b) (ht : t ∈ Set.Icc a b) :
    ‖φ t‖ ≤ Real.sqrt ((c.upper : ℝ) / (c.lower : ℝ)) *
      Real.exp (-((c.rate : ℝ) / 2 * (t - a))) * ‖φ a‖ := by
  simpa only [sub_zero] using c.quadraticDecayCertificate.norm_bound hφ ht

theorem heldOut_all_finite_trajectories_decay {φ : ℝ → State 2} {a b t : ℝ}
    (hφ : IsTrajectoryOn φ heldOut.field a b) (ht : t ∈ Set.Icc a b) :
    ‖φ t‖ ≤ Real.sqrt ((heldOutAccepted.upper : ℝ) / (heldOutAccepted.lower : ℝ)) *
      Real.exp (-((heldOutAccepted.rate : ℝ) / 2 * (t - a))) * ‖φ a‖ :=
  all_finite_trajectories_decay heldOutAccepted hφ ht

-- A Hurwitz linearization does not justify global stability of the full field.
def escaping : Model :=
  ⟨[⟨-1, (1, 0)⟩, ⟨1, (3, 0)⟩], [⟨-1, (0, 1)⟩]⟩

#guard (Polynomial2.synthesize escaping).isNone

example : True := by
  fail_if_success
    have : Polynomial2.Accepted escaping := by polynomial_stability escaping
  fail_if_success
    have : Dynamics.GloballyExponentiallyStable escaping.field 0 := by polynomial_stability escaping
  trivial

-- This stable field has quartic energy loss
-- (x² - 18*y²)² + (x*y)². Its PSD Gram parameter lies in [-18, -35/2],
-- outside the default numerator budget. Search failure is not a refutation.
def budgetLimited : Model :=
  ⟨[⟨-1, (1, 0)⟩, ⟨-1, (3, 0)⟩, ⟨35 / 2, (1, 2)⟩],
   [⟨-1, (0, 1)⟩, ⟨35 / 2, (2, 1)⟩, ⟨-324, (0, 3)⟩]⟩

#guard (Polynomial2.synthesize budgetLimited).isNone
#guard (Polynomial2.synthesizeWithLimits budgetLimited { numeratorBound := 18 }).isSome

example : True := by
  fail_if_success
    have : Polynomial2.Accepted budgetLimited := by polynomial_stability budgetLimited
  trivial

-- Model indexing blocks reuse of a valid certificate for a different field.
example : True := by
  fail_if_success
    have : Polynomial2.Accepted escaping := coupledAccepted
  fail_if_success
    have : Polynomial2.Accepted escaping := by polynomial_stability coupled
  fail_if_success
    have : Dynamics.GloballyExponentiallyStable escaping.field 0 := by polynomial_stability coupled
  trivial

-- Altering witness data cannot preserve the old dependent proof fields. These
-- are negative proposals; no witness is supplied to the synthesis tactic.
example : True := by
  fail_if_success
    have : Polynomial2.Accepted coupled := { coupledAccepted with p00 := coupledAccepted.p00 + 1 }
  fail_if_success
    have : Polynomial2.Accepted coupled := { coupledAccepted with rate := coupledAccepted.rate + 100 }
  fail_if_success
    have : Polynomial2.Accepted coupled :=
      { coupledAccepted with decay_sos := [⟨-1, [⟨1, (1, 0)⟩]⟩] }
  fail_if_success
    have : Polynomial2.Accepted coupled :=
      { coupledAccepted with decay_sos := [⟨1, [⟨2, (1, 0)⟩]⟩] }
  trivial

end powerlib.Tests.PolynomialStability

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let theoremRoots := #[
    `powerlib.Tests.PolynomialStability.coupled_forward_complete,
    `powerlib.Tests.PolynomialStability.heldOut_exponentially_stable,
    `powerlib.Tests.PolynomialStability.rankOne_asymptotically_stable,
    `powerlib.Tests.PolynomialStability.let_bound_model_exponentially_stable,
    `powerlib.Tests.PolynomialStability.named_field_definitions_exponentially_stable,
    `powerlib.Tests.PolynomialStability.coupled_semantics,
    `powerlib.Tests.PolynomialStability.rankOne_semantics,
    `powerlib.Tests.PolynomialStability.heldOut_semantics,
    `powerlib.Tests.PolynomialStability.linearHalf_semantics,
    `powerlib.Tests.PolynomialStability.all_finite_trajectories_decay,
    `powerlib.Tests.PolynomialStability.heldOut_all_finite_trajectories_decay]
  let roots := theoremRoots ++ #[
    `powerlib.Tests.PolynomialStability.coupledAccepted,
    `powerlib.Tests.PolynomialStability.rankOneAccepted,
    `powerlib.Tests.PolynomialStability.heldOutAccepted,
    `powerlib.Tests.PolynomialStability.linearHalfAccepted]
  for root in theoremRoots do
    match env.checked.get.find? root with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Polynomial stability semantic root is not a checked theorem: {root}"
  let mut auditedAxioms : Array Name := #[]
  for root in roots do
    unless (env.checked.get.find? root).isSome do
      throwError "Unknown polynomial stability audit root: {root}"
    auditedAxioms := auditedAxioms ++ powerlib.Search.declarationAxioms env root
  for axiomName in auditedAxioms do
    unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
      throwError "Unexpected polynomial stability axiom: {axiomName}"
  logInfo "POWERLIB_POLYNOMIAL_STABILITY_OK"
