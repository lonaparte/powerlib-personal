-- Automatically synthesized from component input without a supplied witness.
import powerlib
noncomputable section
open MeasureTheory
namespace Candidate
def model : powerlib.LCL.Circuit :=
  ⟨⟨(0 / 1 : ℝ), ⟨(2 / 1 : ℝ), by norm_num⟩⟩, ⟨(0 / 1 : ℝ), ⟨(3 / 1 : ℝ), by norm_num⟩⟩, ⟨(5 / 1 : ℝ), by norm_num⟩⟩
def certificate : powerlib.LCL.StorageAccepted model where
  p := ⟨(2 / 1 : ℝ), (0 / 1 : ℝ), (0 / 1 : ℝ), (5 / 1 : ℝ), (0 / 1 : ℝ), (3 / 1 : ℝ)⟩
  weights_exact := by norm_num [model, powerlib.LCL.physicalWeights]
  passive := by norm_num [model, powerlib.LCL.Circuit.Passive]
end Candidate
namespace Admission
def submittedModel : powerlib.LCL.Circuit :=
  ⟨⟨(0 / 1 : ℝ), ⟨(2 / 1 : ℝ), by norm_num⟩⟩, ⟨(0 / 1 : ℝ), ⟨(3 / 1 : ℝ), by norm_num⟩⟩, ⟨(5 / 1 : ℝ), by norm_num⟩⟩

def accepted : powerlib.LCL.StorageAccepted submittedModel := Candidate.certificate
def portStorage : powerlib.Passivity.QuadraticStorage (powerlib.LCL.portSystem submittedModel) :=
  accepted.portStorage
@[powerlib_domain] theorem passive_with_storage :
    powerlib.Passivity.PassiveWithStorage (powerlib.LCL.portSystem submittedModel)
      (powerlib.LCL.portEnergy submittedModel) := accepted.passiveWithStorage
@[powerlib_domain] theorem lyapunov_stable (u vg : ℝ) (e : powerlib.LCL.State)
    (he : powerlib.LCL.IsEquilibrium submittedModel u vg e) :
    powerlib.LCL.LyapunovStable submittedModel u vg e := accepted.lyapunovStable he
@[powerlib_domain] theorem zero_input_stable :
    powerlib.LCL.LyapunovStable submittedModel 0 0 0 := accepted.zeroInput_stable
@[powerlib_domain] theorem trajectory_exists (u vg : ℝ) (e initial : powerlib.LCL.State)
    (he : powerlib.LCL.IsEquilibrium submittedModel u vg e) :
    ∃ x, powerlib.LCL.IsTrajectory submittedModel u vg x ∧ x 0 = initial :=
  accepted.trajectory_exists he initial
@[powerlib_domain] theorem zero_input_trajectory_exists (initial : powerlib.LCL.State) :
    ∃ x, powerlib.LCL.IsTrajectory submittedModel 0 0 x ∧ x 0 = initial :=
  accepted.trajectory_exists (powerlib.LCL.zero_equilibrium submittedModel) initial
@[powerlib_domain] theorem trajectory_unique (u vg : ℝ) (e : powerlib.LCL.State)
    (x y : ℝ → powerlib.LCL.State) (he : powerlib.LCL.IsEquilibrium submittedModel u vg e)
    (hx : powerlib.LCL.IsTrajectory submittedModel u vg x)
    (hy : powerlib.LCL.IsTrajectory submittedModel u vg y) (h0 : x 0 = y 0) :
    Set.EqOn x y (Set.Ici 0) := accepted.trajectory_unique he hx hy h0
@[powerlib_domain] theorem integral_passivity (u : ℝ → powerlib.LCL.PortInput)
    (x : ℝ → powerlib.LCL.State) (hx : powerlib.LCL.IsPortTrajectory submittedModel u x)
    (t : ℝ) (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun s => u s 0 * x s 0 - u s 1 * x s 2) volume 0 t) :
    powerlib.LCL.portEnergy submittedModel (x t) - powerlib.LCL.portEnergy submittedModel (x 0) ≤
      ∫ s in (0 : ℝ)..t, u s 0 * x s 0 - u s 1 * x s 2 :=
  accepted.integral_passivity hx ht hsupply
@[powerlib_domain] theorem zero_input_energy_nonincreasing (x : ℝ → powerlib.LCL.State)
    (hx : powerlib.LCL.IsTrajectory submittedModel 0 0 x) :
    AntitoneOn (fun t => powerlib.LCL.portEnergy submittedModel (x t)) (Set.Ici 0) :=
  accepted.zeroInput_energy_nonincreasing hx
structure SemanticContract : Prop where
  passive_with_storage :
    powerlib.Passivity.PassiveWithStorage (powerlib.LCL.portSystem submittedModel)
      (powerlib.LCL.portEnergy submittedModel)
  lyapunov_stable : ∀ (u vg : ℝ) (e : powerlib.LCL.State),
    powerlib.LCL.IsEquilibrium submittedModel u vg e →
      powerlib.LCL.LyapunovStable submittedModel u vg e
  zero_input_stable : powerlib.LCL.LyapunovStable submittedModel 0 0 0
  trajectory_exists : ∀ (u vg : ℝ) (e initial : powerlib.LCL.State),
    powerlib.LCL.IsEquilibrium submittedModel u vg e →
      ∃ x, powerlib.LCL.IsTrajectory submittedModel u vg x ∧ x 0 = initial
  zero_input_trajectory_exists : ∀ initial : powerlib.LCL.State,
    ∃ x, powerlib.LCL.IsTrajectory submittedModel 0 0 x ∧ x 0 = initial
  trajectory_unique : ∀ (u vg : ℝ) (e : powerlib.LCL.State)
    (x y : ℝ → powerlib.LCL.State),
    powerlib.LCL.IsEquilibrium submittedModel u vg e →
    powerlib.LCL.IsTrajectory submittedModel u vg x →
    powerlib.LCL.IsTrajectory submittedModel u vg y → x 0 = y 0 →
      Set.EqOn x y (Set.Ici 0)
  integral_passivity : ∀ (u : ℝ → powerlib.LCL.PortInput)
    (x : ℝ → powerlib.LCL.State),
    powerlib.LCL.IsPortTrajectory submittedModel u x → ∀ t : ℝ, 0 ≤ t →
    IntervalIntegrable (fun s => u s 0 * x s 0 - u s 1 * x s 2) volume 0 t →
      powerlib.LCL.portEnergy submittedModel (x t) -
          powerlib.LCL.portEnergy submittedModel (x 0) ≤
        ∫ s in (0 : ℝ)..t, u s 0 * x s 0 - u s 1 * x s 2
  zero_input_energy_nonincreasing : ∀ x : ℝ → powerlib.LCL.State,
    powerlib.LCL.IsTrajectory submittedModel 0 0 x →
      AntitoneOn (fun t => powerlib.LCL.portEnergy submittedModel (x t)) (Set.Ici 0)

@[powerlib_domain] theorem semanticContract : SemanticContract := {
  passive_with_storage := Admission.passive_with_storage
  lyapunov_stable := Admission.lyapunov_stable
  zero_input_stable := Admission.zero_input_stable
  trajectory_exists := Admission.trajectory_exists
  zero_input_trajectory_exists := Admission.zero_input_trajectory_exists
  trajectory_unique := Admission.trajectory_unique
  integral_passivity := Admission.integral_passivity
  zero_input_energy_nonincreasing := Admission.zero_input_energy_nonincreasing
}

end Admission

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let registered := powerlib.Registry.theoremNames env
  for root in registered do
    if root.getRoot == `Admission then
      logInfo m!"POWERLIB_ADMITTED_THEOREM {root}"
  let mut roots : Array Name := #[`Admission.semanticContract] ++ registered
  for (root, info) in env.constants do
    if root.getRoot == `powerlib && !info.isUnsafe then
      roots := roots.push root
  roots := roots.qsort Name.lt
  let mut previous : Option Name := none
  for root in roots do
    if previous == some root then continue
    previous := some root
    unless (env.find? root).isSome do throwError "Missing audit root {root}"
    for ax in powerlib.Search.declarationAxioms env root do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected axiom {ax}"
  logInfo "POWERLIB_KERNEL_OK"
