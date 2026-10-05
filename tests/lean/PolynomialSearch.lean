import theorems.Dynamics.PolynomialSynthesis

/-! Executable regressions for the untrusted rational proposal search. Inputs
contain only polynomial vector fields. These `#guard` commands check computation;
the separate stability consumer checks `Accepted` proofs and trajectory semantics.
-/

namespace powerlib.Tests.PolynomialSearch

open powerlib.Dynamics.Polynomial2

def coupled : Model where
  field0 := [⟨-1, (1, 0)⟩, ⟨1, (0, 1)⟩, ⟨-1, (3, 0)⟩, ⟨-2, (1, 2)⟩]
  field1 := [⟨-2, (0, 1)⟩, ⟨-1, (0, 3)⟩, ⟨-3, (2, 1)⟩]

def coupledVariant : Model where
  field0 := [⟨-2, (1, 0)⟩, ⟨2, (0, 1)⟩, ⟨-3, (3, 0)⟩, ⟨-4, (1, 2)⟩]
  field1 := [⟨-3, (0, 1)⟩, ⟨-2, (0, 3)⟩, ⟨-5, (2, 1)⟩]

def escaping : Model where
  field0 := [⟨-1, (1, 0)⟩, ⟨1, (3, 0)⟩]
  field1 := [⟨-1, (0, 1)⟩]

def gasWithoutExponentialRate : Model where
  field0 := [⟨-1, (3, 0)⟩]
  field1 := [⟨-1, (0, 3)⟩]

-- A different quadratic energy proves exponential decay for this field, while
-- the fixed-Q candidate fails. Search exhaustion must remain `none`.
def fixedQFailure : Model where
  field0 := [⟨-1, (1, 0)⟩, ⟨-2, (2, 1)⟩, ⟨-4, (0, 3)⟩]
  field1 := [⟨-1, (0, 1)⟩, ⟨1, (3, 0)⟩, ⟨2, (1, 2)⟩]

-- Unsupported quadratic terms must cause failure rather than be discarded.
def quadraticGES : Model where
  field0 := [⟨-1, (1, 0)⟩, ⟨-2, (1, 1)⟩]
  field1 := [⟨-1, (0, 1)⟩, ⟨1, (2, 0)⟩]

def rationalRankOne : Model where
  field0 := [⟨-1, (1, 0)⟩, ⟨1, (0, 1)⟩, ⟨-1, (3, 0)⟩,
    ⟨-3, (2, 1)⟩, ⟨-3, (1, 2)⟩, ⟨-1, (0, 3)⟩]
  field1 := [⟨-2, (0, 1)⟩, ⟨-2, (3, 0)⟩, ⟨-6, (2, 1)⟩,
    ⟨-6, (1, 2)⟩, ⟨-2, (0, 3)⟩]

-- The PSD Gram parameter lies in [-18, -35/2], beyond the default budget.
def searchBudgetControl : Model where
  field0 := [⟨-1, (1, 0)⟩, ⟨-1, (3, 0)⟩, ⟨35 / 2, (1, 2)⟩]
  field1 := [⟨-1, (0, 1)⟩, ⟨35 / 2, (2, 1)⟩, ⟨-324, (0, 3)⟩]

def witnessScalars (w : Witness) : List ℚ :=
  [w.p00, w.p01, w.p11, w.lower, w.upper, w.rate]

def squareData (square : WeightedSquare) : ℚ × List (ℚ × (ℕ × ℕ)) :=
  (square.weight, square.poly.map fun term => (term.coefficient, term.powers))

def rationalEval : Polynomial → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | term :: terms, x, y =>
      term.coefficient * x ^ term.powers.1 * y ^ term.powers.2 + rationalEval terms x y

def rationalSOS (squares : List WeightedSquare) (x y : ℚ) : ℚ :=
  squares.foldl (fun acc square => acc + square.weight * rationalEval square.poly x y ^ 2) 0

-- Independent executable checks on a 5×5 rational grid. The acceptance theorem
-- separately proves the three identities for all real states.
def rationalWitnessChecks (model : Model) (w : Witness) : Bool :=
  decide (0 < w.lower) && decide (0 < w.upper) && decide (0 < w.rate) &&
  (w.lower_sos ++ w.upper_sos ++ w.decay_sos).all (fun s => decide (0 ≤ s.weight)) &&
  (List.range 5).all (fun i => (List.range 5).all (fun j =>
    let x : ℚ := i
    let y : ℚ := j
    let value := w.p00 * x ^ 2 + 2 * w.p01 * x * y + w.p11 * y ^ 2
    let lie := (2 * w.p00 * x + 2 * w.p01 * y) * rationalEval model.field0 x y +
      (2 * w.p01 * x + 2 * w.p11 * y) * rationalEval model.field1 x y
    let norm := x ^ 2 + y ^ 2
    (value - w.lower * norm == rationalSOS w.lower_sos x y) &&
    (w.upper * norm - value == rationalSOS w.upper_sos x y) &&
    (-lie - w.rate * value == rationalSOS w.decay_sos x y)))

def hasRankOneQuartic (w : Witness) : Bool :=
  w.decay_sos.any (fun square =>
    square.weight == (5 / 3 : ℚ) && square.poly.length == 3 &&
    Synthesis.coefficient square.poly (2, 0) == 1 &&
    Synthesis.coefficient square.poly (1, 1) == 2 &&
    Synthesis.coefficient square.poly (0, 2) == 1)

#guard ((synthesize coupled).map witnessScalars) ==
  some [1 / 2, 1 / 6, 1 / 3, 1 / 8, 1, 1]
#guard ((synthesize coupledVariant).map witnessScalars) ==
  some [1 / 4, 1 / 10, 7 / 30, 1 / 8, 1, 1]
#guard (synthesize escaping).isNone
#guard (synthesize gasWithoutExponentialRate).isNone
#guard (synthesize fixedQFailure).isNone
#guard (synthesize quadraticGES).isNone
#guard (synthesize rationalRankOne).isSome
#guard (synthesize searchBudgetControl).isNone

#guard ((synthesize coupled).map (rationalWitnessChecks coupled)) == some true
#guard ((synthesize coupledVariant).map (rationalWitnessChecks coupledVariant)) == some true
#guard ((synthesize rationalRankOne).map hasRankOneQuartic) == some true
#guard ((synthesize rationalRankOne).map (rationalWitnessChecks rationalRankOne)) == some true
#guard (synthesizeWithLimits rationalRankOne { denominatorBound := 2 }).isNone
#guard (synthesizeWithLimits searchBudgetControl { numeratorBound := 18 }).isSome
#guard ((synthesizeWithLimits searchBudgetControl { numeratorBound := 18 }).map
  (rationalWitnessChecks searchBudgetControl)) == some true

#guard (Synthesis.ldlSOS
  #[#[0, 1, 0], #[1, 1, 0], #[0, 0, 1]] #[(2, 0), (1, 1), (0, 2)]).isNone
#guard (Synthesis.ldlSOS
  #[#[1, 0, 0], #[0, 0, 1], #[0, 1, 1]] #[(2, 0), (1, 1), (0, 2)]).isNone
#guard ((Synthesis.ldlSOS
  #[#[1, 0, 0], #[0, 0, 0], #[0, 0, 0]] #[(2, 0), (1, 1), (0, 2)]).map
  (fun squares => squares.map squareData)) == some [(1, [(1, (2, 0))])]

end powerlib.Tests.PolynomialSearch

open Lean Elab Command
run_cmd logInfo "POWERLIB_POLYNOMIAL_SEARCH_OK"
