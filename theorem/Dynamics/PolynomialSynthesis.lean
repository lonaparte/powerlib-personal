import theorem.Dynamics.Polynomial2

/-! Computable rational proposals for two-state polynomial Lyapunov certificates.
This bounded search is untrusted: the tactic must reconstruct `Accepted` proofs
for the original model before deriving any stability conclusion. Failure means
only that this search did not find a witness.
-/

namespace powerlib.Dynamics.Polynomial2
namespace Synthesis

abbrev RatMatrix := Array (Array ℚ)

def coefficient (p : Polynomial) (powers : ℕ × ℕ) : ℚ :=
  p.foldl (fun acc term => if term.powers = powers then acc + term.coefficient else acc) 0

def insertTerm (p : Polynomial) (term : Term) : Polynomial :=
  let value := coefficient p term.powers + term.coefficient
  let rest := p.filter (fun other => other.powers != term.powers)
  if value = 0 then rest else ⟨value, term.powers⟩ :: rest

def normalize (p : Polynomial) : Polynomial := p.foldl insertTerm []

def add (p q : Polynomial) : Polynomial := normalize (p ++ q)

def scale (a : ℚ) (p : Polynomial) : Polynomial :=
  normalize (p.map (fun term => ⟨a * term.coefficient, term.powers⟩))

def multiply (p q : Polynomial) : Polynomial :=
  normalize (p.flatMap (fun a => q.map (fun b =>
    ⟨a.coefficient * b.coefficient, (a.powers.1 + b.powers.1, a.powers.2 + b.powers.2)⟩)))

def derivative (p : Polynomial) (coordinate : Nat) : Polynomial :=
  normalize (p.filterMap (fun term =>
    let power := if coordinate = 0 then term.powers.1 else term.powers.2
    if power = 0 then none else
      some ⟨term.coefficient * (power : ℚ),
        if coordinate = 0 then (term.powers.1 - 1, term.powers.2)
        else (term.powers.1, term.powers.2 - 1)⟩))

def normSquared : Polynomial := [⟨1, (2, 0)⟩, ⟨1, (0, 2)⟩]

def energy (p00 p01 p11 : ℚ) : Polynomial :=
  normalize [⟨p00, (2, 0)⟩, ⟨2 * p01, (1, 1)⟩, ⟨p11, (0, 2)⟩]

def lieDerivative (model : Model) (value : Polynomial) : Polynomial :=
  add (multiply (derivative value 0) model.field0)
    (multiply (derivative value 1) model.field1)

def quadraticMatrix (p : Polynomial) : RatMatrix :=
  #[#[coefficient p (2, 0), coefficient p (1, 1) / 2],
    #[coefficient p (1, 1) / 2, coefficient p (0, 2)]]

/-- Exact bounded-dimensional Gaussian elimination, with no numeric oracle. -/
def solveLinear (matrix : RatMatrix) (rhs : Array ℚ) : Option (Array ℚ) := Id.run do
  let size := rhs.size
  let mut rows := matrix.mapIdx (fun index row => row.push rhs[index]!)
  for column in List.range size do
    let pivot := (List.range (size - column)).find? (fun offset =>
      (rows[column + offset]!)[column]! != 0)
    let some offset := pivot | return none
    let index := column + offset
    let original := rows[column]!
    rows := (rows.set! column rows[index]!).set! index original
    let divisor := (rows[column]!)[column]!
    rows := rows.set! column (rows[column]!.map (fun value => value / divisor))
    for i in List.range size do
      if i != column then
        let divisor := (rows[i]!)[column]!
        let mut row := rows[i]!
        for j in List.range (size + 1) do
          row := row.set! j (row[j]! - divisor * (rows[column]!)[j]!)
        rows := rows.set! i row
  return some (rows.map (fun row => row[size]!))

def lyapunovCandidate (model : Model) : Option (ℚ × ℚ × ℚ) := do
  let linear : Model :=
    ⟨model.field0.filter (fun t => t.powers.1 + t.powers.2 == 1),
      model.field1.filter (fun t => t.powers.1 + t.powers.2 == 1)⟩
  let images := #[lieDerivative linear (energy 1 0 0),
    lieDerivative linear (energy 0 1 0), lieDerivative linear (energy 0 0 1)]
  let matrix := #[(2, 0), (1, 1), (0, 2)].map (fun powers =>
    images.map (fun p => coefficient p powers))
  let answer ← solveLinear matrix #[-1, 0, -1]
  return (answer[0]!, answer[1]!, answer[2]!)

/-- Rational PSD elimination emits weighted squares, including singular cases.
A zero pivot with a nonzero off-diagonal entry must be rejected. -/
def ldlSOS (matrix : RatMatrix) (monomials : Array (ℕ × ℕ)) :
    Option (List WeightedSquare) := Id.run do
  let size := matrix.size
  let mut work := matrix
  let mut squares : List WeightedSquare := []
  for i in List.range size do
    for j in List.range size do
      if (work[i]!)[j]! != (work[j]!)[i]! then return none
  for pivot in List.range size do
    let weight := (work[pivot]!)[pivot]!
    if weight < 0 then return none
    if weight = 0 then
      if (List.range (size - pivot - 1)).any (fun offset =>
          (work[pivot]!)[pivot + offset + 1]! != 0) then return none
    else
      let mut factor : Polynomial := [⟨1, monomials[pivot]!⟩]
      for offset in List.range (size - pivot - 1) do
        let j := pivot + offset + 1
        factor := insertTerm factor ⟨(work[pivot]!)[j]! / weight, monomials[j]!⟩
      squares := squares ++ [⟨weight, factor⟩]
      for oi in List.range (size - pivot - 1) do
        let i := pivot + oi + 1
        let mut row := work[i]!
        for oj in List.range (size - pivot - 1) do
          let j := pivot + oj + 1
          row := row.set! j (row[j]! - (work[pivot]!)[i]! * (work[pivot]!)[j]! / weight)
        work := work.set! i row
  return some squares

def quarticGram (p : Polynomial) (free : ℚ) : RatMatrix :=
  let a := coefficient p (4, 0)
  let b := coefficient p (3, 1)
  let c := coefficient p (2, 2)
  let d := coefficient p (1, 3)
  let e := coefficient p (0, 4)
  #[#[a, b / 2, free], #[b / 2, c - 2 * free, d / 2], #[free, d / 2, e]]

/-- The binary-quartic Gram family has exactly one free rational parameter. -/
def quarticSOS (p : Polynomial) (numeratorBound denominatorBound : Nat) :
    Option (List WeightedSquare) := Id.run do
  let monomials := #[(2, 0), (1, 1), (0, 2)]
  if let some squares := ldlSOS (quarticGram p 0) monomials then return some squares
  for denominator in List.range denominatorBound do
    for numerator in List.range numeratorBound do
      let value := ((numerator + 1 : Nat) : ℚ) / ((denominator + 1 : Nat) : ℚ)
      if let some squares := ldlSOS (quarticGram p value) monomials then return some squares
      if let some squares := ldlSOS (quarticGram p (-value)) monomials then return some squares
  return none

def lowerBoundSOS (value : Polynomial) (steps : Nat) :
    Option (ℚ × List WeightedSquare) := Id.run do
  let mut lower : ℚ := 1
  for _ in List.range steps do
    if let some squares := ldlSOS (quadraticMatrix (add value (scale (-lower) normSquared)))
        #[(1, 0), (0, 1)] then return some (lower, squares)
    lower := lower / 2
  return none

def upperBoundSOS (value : Polynomial) (steps : Nat) :
    Option (ℚ × List WeightedSquare) := Id.run do
  let mut upper : ℚ := 1
  for _ in List.range steps do
    if let some squares := ldlSOS
        (quadraticMatrix (add (scale upper normSquared) (scale (-1) value)))
        #[(1, 0), (0, 1)] then return some (upper, squares)
    upper := upper * 2
  return none

def decaySOS (negativeLie value : Polynomial) (steps : Nat) :
    Option (ℚ × List WeightedSquare) := Id.run do
  let mut rate : ℚ := 1
  for _ in List.range steps do
    if let some squares := ldlSOS
        (quadraticMatrix (add negativeLie (scale (-rate) value)))
        #[(1, 0), (0, 1)] then return some (rate, squares)
    rate := rate / 2
  return none

structure SearchLimits where
  numeratorBound : Nat := 16
  denominatorBound : Nat := 12
  boundSteps : Nat := 32
  rateSteps : Nat := 32
  deriving Inhabited

/-- Only nonzero linear and cubic terms are searched. Other input degrees are
preserved in the model and cause failure rather than being silently truncated. -/
def supported (model : Model) : Bool :=
  (model.field0 ++ model.field1).all (fun term =>
    term.powers.1 + term.powers.2 == 1 || term.powers.1 + term.powers.2 == 3)

end Synthesis

/-- A bounded, exact, witness-free proposal search. `none` means UNPROVED.
Every returned witness still requires all `Accepted` obligations to be checked. -/
def synthesizeWithLimits (model : Model) (limits : Synthesis.SearchLimits) : Option Witness := do
  let normalized : Model := ⟨Synthesis.normalize model.field0, Synthesis.normalize model.field1⟩
  if !Synthesis.supported normalized then none else do
    let (p00, p01, p11) ← Synthesis.lyapunovCandidate normalized
    if p00 ≤ 0 || p00 * p11 - p01 * p01 ≤ 0 then none else do
      let value := Synthesis.energy p00 p01 p11
      let negativeLie := Synthesis.scale (-1) (Synthesis.lieDerivative normalized value)
      let quartic := negativeLie.filter (fun t => t.powers.1 + t.powers.2 == 4)
      let nonlinearSOS ← Synthesis.quarticSOS quartic limits.numeratorBound limits.denominatorBound
      let (lower, lowerSOS) ← Synthesis.lowerBoundSOS value limits.boundSteps
      let (upper, upperSOS) ← Synthesis.upperBoundSOS value limits.boundSteps
      let (rate, quadraticSOS) ← Synthesis.decaySOS negativeLie value limits.rateSteps
      return ⟨p00, p01, p11, lower, upper, rate, lowerSOS, upperSOS,
        quadraticSOS ++ nonlinearSOS⟩

def synthesize (model : Model) : Option Witness := synthesizeWithLimits model {}

end powerlib.Dynamics.Polynomial2
