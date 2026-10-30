import theorem.Numerics.LinearSchemes
import theorem.Map.LinearReading
import theorem.Linear.Family
import theorem.Stack.Implementation

/-! # Implicit discretizations of linear designs (foundation)

The trapezoidal and backward-Euler schemes define genuine discrete implementations of a
continuous linear family. The system is their matrix step, read once by `Behaviour.discrete`.
The requirement language lifts the design requirements and adds positive step length and
invertibility of the implicit step. A singular inverse is never identified with a solution of
an implicit recursion: the exact trapezoidal comparison explicitly requires well-posedness.
Hurwitz designs make both schemes well posed and stable for every positive step. Backward
Euler is asserted sound only; unlike the trapezoidal rule, it can stabilize an unstable design.
Scaffold: `theorem/ImplicitDiscretization.agda`.

Scope. Arbitrary continuous linear families, arbitrary implementation carriers with a design
map and a real step length. Zero-input dynamics, exact arithmetic, fixed step, no solver error.
The templates also describe deviations from constant-input equilibria, whose linear matrix is
the design matrix; the instance must justify that coordinate reading.

Source: `Numerics/LinearSchemes`, `Map/LinearReading`, `Linear/Family`, `Stack/Implementation`.
Results: generated denotation criteria, pointwise realization soundness, trapezoidal realization
exactness within positive/well-posed steps and backward-Euler realization soundness.

Family and connection conclusions.
* `implicitFamily` reads the numerical step through the existing discrete semantics; its Schur
  criterion is a T–M interpretation of that implementation's mathematical model.
* `implicitRealization` uses the actual design projection. Its M–I laws compare the design and
  implementation denotations only for attractive flow sentences and sampled contraction, under
  the stated step constraints. They do not assert preservation of passivity or arbitrary sentences.
-/

noncomputable section

namespace powerlib.Numerics

open Matrix LinearSystems

/-- The two implicit integration methods treated here. -/
inductive ImplicitMethod
  | trapezoidal
  | backwardEuler

/-- The matrix of the actual numerical step. -/
def ImplicitMethod.matrix {n : ℕ} :
    ImplicitMethod → ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
  | .trapezoidal, h, A => trapezoidalMatrix h A
  | .backwardEuler, h, A => backwardEulerMatrix h A

/-- Invertibility required to solve the implicit step uniquely. -/
def ImplicitMethod.WellPosed {n : ℕ} :
    ImplicitMethod → ℝ → Matrix (Fin n) (Fin n) ℝ → Prop
  | .trapezoidal, h, A => IsUnit (1 - (h / 2) • A).det
  | .backwardEuler, h, A => IsUnit (1 - h • A).det

/-- Design requirements and the actual constraints of an implicit implementation. -/
inductive ImplicitRequirement (Q : Type*)
  | design (q : Q)
  | positiveStep
  | wellPosed

/-- A fixed positive-step implementation carries its actual continuous design. -/
structure ImplicitStep (X : Type*) where
  design : X
  h : ℝ
  pos : 0 < h

variable {X Y Q : Type*} {n p : ℕ}

/-- The discrete family of implicit steps, with its inherited design language. -/
def implicitFamily (method : ImplicitMethod) (F : Family X Q n p)
    (plant : X → Linear.Plant n p) (design : Y → X) (step : Y → ℝ) :
    Family Y (ImplicitRequirement Q) n 0 where
  system y := .discrete (Map.System.autonomous (step y)
    (Map.op (method.matrix (step y) (plant (design y)).A)))
  meets y
    | .design q => F.meets (design y) q
    | .positiveStep => 0 < step y
    | .wellPosed => method.WellPosed (step y) (plant (design y)).A
  translate s := ImplicitRequirement.design '' F.translate s

@[tmio M, powerlib_foundation] theorem implicitFamily_isAutonomousMap
    (method : ImplicitMethod) (F : Family X Q n p) (plant : X → Linear.Plant n p)
    (design : Y → X) (step : Y → ℝ) :
    (implicitFamily method F plant design step).IsAutonomousMap step
      (fun y => Map.op (method.matrix (step y) (plant (design y)).A)) := fun _ => rfl

/-- Every numerical implementation realizes the continuous model it was designed from. -/
def implicitRealization (method : ImplicitMethod) (F : Family X Q n p)
    (plant : X → Linear.Plant n p) (design : Y → X) (step : Y → ℝ) :
    Implementation X Q Y (ImplicitRequirement Q) n p n 0 where
  model := F
  impl := implicitFamily method F plant design step
  realizes := Implementation.ofDesign design

/-- Attractive sentences of the implementation are exactly the Schur condition on its step. -/
@[tmio TM, powerlib_foundation] theorem implicit_den_schurStable
    (method : ImplicitMethod) (F : Family X Q n p) (plant : X → Linear.Plant n p)
    (design : Y → X) (step : Y → ℝ) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((implicitFamily method F plant design step).den (.flow P) =
      {y | LTI.SchurStable (method.matrix (step y) (plant (design y)).A)}) := by
  exact (implicitFamily_isAutonomousMap method F plant design step).den_schurStable hP

variable {F : Family X Q n p} {plant : X → Linear.Plant n p}
  {design : Y → X} {step : Y → ℝ}

/-- Positive-step implicit discretizations preserve every attractive design sentence. -/
@[tmio MI, powerlib_foundation] theorem implicit_mem_den_of_design
    (method : ImplicitMethod) (hF : F.IsLinear plant) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) {y : Y} (hh : 0 < step y)
    (hy : design y ∈ F.den (.flow P)) :
    connection% (y ∈ (implicitFamily method F plant design step).den (.flow P)) := by
  unfold TMIO.Statement
  rw [implicit_den_schurStable method F plant design step hP]
  have hA := (hF.mem_den_hurwitz hP).mp hy
  cases method with
  | trapezoidal => exact trapezoidal_schurStable_of_isHurwitz hA hh
  | backwardEuler => exact backwardEuler_schurStable_of_isHurwitz hA hh

/-- Stability of the continuous design ensures that the implicit equation has a unique step. -/
@[tmio MI, powerlib_foundation] theorem implicit_mem_wellPosed_of_design
    (method : ImplicitMethod) (hF : F.IsLinear plant) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) {y : Y} (hh : 0 < step y)
    (hy : design y ∈ F.den (.flow P)) :
    connection% (y ∈ TMIO.realize (implicitFamily method F plant design step).meets
      {.wellPosed}) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq]
  have hA := (hF.mem_den_hurwitz hP).mp hy
  cases method with
  | trapezoidal => exact isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)
  | backwardEuler => exact isUnit_det_one_sub_smul_of_isHurwitz hA hh

/-- The well-posed trapezoidal implementation and its design satisfy the same attractive
sentence. This is a comparison of two relative roles, not just the platform's own criterion. -/
@[tmio MI, powerlib_foundation] theorem trapezoidal_mem_den_iff_design
    (hF : F.IsLinear plant) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive)
    {y : Y} (hh : 0 < step y)
    (hw : ImplicitMethod.trapezoidal.WellPosed (step y) (plant (design y)).A) :
    connection% (y ∈ (implicitFamily .trapezoidal F plant design step).den (.flow P) ↔
      design y ∈ F.den (.flow P)) := by
  unfold TMIO.Statement
  rw [implicit_den_schurStable .trapezoidal F plant design step hP]
  change LTI.SchurStable (trapezoidalMatrix (step y) (plant (design y)).A) ↔ _
  exact (trapezoidal_schurStable_iff_isHurwitz hh hw).trans (hF.mem_den_hurwitz hP).symm

/-- Trapezoidal realization is exact where the step is positive and well posed. -/
@[tmio MI, powerlib_foundation] theorem trapezoidal_realizationExactUnder
    (hF : F.IsLinear plant) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% ((implicitRealization .trapezoidal F plant design step).RealizationExactUnder
      {.positiveStep, .wellPosed} (.flow P)) := by
  unfold TMIO.Statement
  apply Implementation.realizationExactUnder_of_design rfl
  ext y
  constructor
  · rintro ⟨hy, hctx⟩
    have hh : 0 < step y := (TMIO.mem_realize _ _ _).mp hctx .positiveStep (by simp)
    have hw : ImplicitMethod.trapezoidal.WellPosed (step y) (plant (design y)).A :=
      (TMIO.mem_realize _ _ _).mp hctx .wellPosed (by simp)
    exact ⟨(trapezoidal_mem_den_iff_design hF hP hh hw).mp hy, hctx⟩
  · rintro ⟨hy, hctx⟩
    have hh : 0 < step y := (TMIO.mem_realize _ _ _).mp hctx .positiveStep (by simp)
    exact ⟨implicit_mem_den_of_design .trapezoidal hF hP hh hy, hctx⟩

/-- Backward Euler realizes attractive sentences soundly at every positive step. No converse
is claimed: backward Euler may damp a design with unstable continuous eigenvalues. -/
@[tmio MI, powerlib_foundation] theorem backwardEuler_realizationSoundUnder
    (hF : F.IsLinear plant) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% ((implicitRealization .backwardEuler F plant design step).RealizationSoundUnder
      {.positiveStep} (.flow P)) := by
  unfold TMIO.Statement
  intro y hy
  have hh : 0 < step y := (TMIO.mem_realize _ _ _).mp hy.2 .positiveStep (by simp)
  have hd : design y ∈ F.den (.flow P) := by
    have hcert := hy.1
    rw [Implementation.certify_realizes_of_design (I :=
      implicitRealization .backwardEuler F plant design step) rfl] at hcert
    exact hcert
  exact implicit_mem_den_of_design .backwardEuler hF hP hh hd

end powerlib.Numerics
