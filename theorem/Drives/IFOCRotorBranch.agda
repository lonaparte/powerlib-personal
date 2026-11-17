{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Drives.IFOCRotorBranch where
-- Lean modules: theorem.Drives.InductionMachine

-- Scaffold of the reading of the IFOC rotor-flux family through the dq RL-branch family
-- (`Drives.InductionMachine.family` read through `Passive.DqRL.family`, in
-- `theorem/Drives/InductionMachine.lean`). The rotor of the machine is the R–L branch `r_r`, `L_r`
-- without capacitor (`Drives.InductionMachine.Params.rotorBranch`); read in the dq frame at the
-- slip speed it is the dq branch `Drives.InductionMachine.Drive.rotorBranch`. The rotor-flux field
-- is the field of that branch's dq plant under the constant voltage `r_r L_m i_s`
-- (`Drives.InductionMachine.fluxField_eq_inputField`), and the family reads each drive as this
-- field translated to its selected point. When the selected point is an equilibrium
-- (`Equilibrium`), the translated field is the branch's zero-input field (`linear`, Lean
-- `LTI.inputField_shift`), so on the drives with an equilibrium the two families agree on every
-- flow sentence (`reading`, `den↔`). Only the flow sentences are read: passivity is read on the
-- branch's ports, which the rotor-flux family does not have. The requirement languages take no
-- part in the connection and are left empty here. Lean: `ifoc-flow` is
-- `Family.IsAutonomous.mem_den_flow` (`Drives.InductionMachine.family_isAutonomous`),
-- `branch-flow` is `Family.IsLinear.mem_den_flow` (`Spectral.linearFamily_isLinear`), `den↔` is
-- `Drives.InductionMachine.mem_den_flow_iff_dqRL`; the attractive members follow from
-- `Passive.DqRL.mem_den_iff` (`Drives.InductionMachine.mem_den_attractive_iff`). Nothing here is
-- exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module Reading
  -- Systems of the semantic layer with their satisfaction; planar fields with the flow sentences
  -- of `ż = f z` at the origin.
  (Plant : Type) (holds : Plant → Sentence → Type)
  (Field : Type) (holdsField : Field → Sentence → Type)
  -- The drives with their translated rotor-flux fields and their systems; the dq branches with
  -- their zero-input fields and their plants; the rotor branch of a drive at its slip speed.
  (Drive : Type) (driveField : Drive → Field) (driveSystem : Drive → Plant)
  (Branch : Type) (zeroInput : Branch → Field) (branchPlant : Branch → Plant)
  (rotorBranch : Drive → Branch)
  -- The selected point of a drive is an equilibrium of its rotor-flux field.
  (Equilibrium : Drive → Type)
  where

  plantSemantics : Semantics
  plantSemantics = record { System = Plant ; Sentence = Sentence ; holds = holds }

  open Readings plantSemantics

  ifoc dqBranch : Family
  ifoc = record
    { Model = Drive ; Req = ⊥ ; system = driveSystem ; meets = λ _ () ; translate = λ _ () }
  dqBranch = record
    { Model = Branch ; Req = ⊥ ; system = branchPlant ; meets = λ _ () ; translate = λ _ () }

  -- What Lean proves.
  record Obligations : Type where
    field
      ifoc-flow : (d : Drive) (s : Sentence) → Flow s →
        holds (driveSystem d) s ≃ holdsField (driveField d) s
      branch-flow : (b : Branch) (s : Sentence) → Flow s →
        holds (branchPlant b) s ≃ holdsField (zeroInput b) s
      linear : (d : Drive) → Equilibrium d → driveField d ≡ zeroInput (rotorBranch d)

  module _ (ob : Obligations) where
    open Obligations ob

    onEquilibria : Family
    onEquilibria = restrictBy ifoc Equilibrium

    -- At an equilibrium a flow sentence of the drive is the same sentence of its rotor branch.
    readOn : (d : Drive) (e : Equilibrium d) (s : Sentence) → Flow s →
      holds (driveSystem d) s ≃ holds (branchPlant (rotorBranch d)) s
    readOn d e s f =
      compEquiv (ifoc-flow d s f)
        (compEquiv (pathToEquiv (cong (λ g → holdsField g s) (linear d e)))
          (invEquiv (branch-flow (rotorBranch d) s f)))

    reading : PartialHub Flow onEquilibria dqBranch
    reading = record
      { map = λ x → rotorBranch (fst x) ; read = λ x → readOn (fst x) (snd x) }

    -- On the drives with an equilibrium the drive and its rotor branch agree on every flow
    -- sentence.
    den↔ : (d : Drive) (e : Equilibrium d) (s : Sentence) → Flow s →
      den ifoc s d ↔ den dqBranch s (rotorBranch d)
    den↔ d e s f = ↔-of-≃ (PartialHub.read reading (d , e) s f)
