import powerlib

open powerlib

example {n : ℕ} (m : LTI.Model n) (c : LTI.Accepted m) : LTI.ExponentiallyStable m := by aesop
example {n : ℕ} (m : LTI.Model n) (initial : LTI.State n) :
    LTI.IsTrajectory m (LTI.response m initial) := by aesop
example {n : ℕ} (m : LTI.Model n) (initial : LTI.State n) :
    LTI.response m initial 0 = initial := by simp
example {n : ℕ} (m : LTI.Model n) (c : LTI.Accepted m)
    (initial : LTI.State n) (t : ℝ) (ht : 0 ≤ t) :
    LTI.sqNorm (LTI.response m initial t) ≤
      (c.upper / c.lower) * Real.exp (-(t / c.upper)) * LTI.sqNorm initial := by aesop

-- Every named LTI theorem has a standard automation use case. None of these
-- proofs supplies a theorem name to aesop/simp; mere registry membership is
-- tested separately below and is not a substitute for actual proof search.
section LTIReuse
variable {n : ℕ} (m : LTI.Model n) (c : LTI.Accepted m)
  (x y : ℝ → LTI.State n) (hx : LTI.IsTrajectory m x) (hy : LTI.IsTrajectory m y)
  (t : ℝ) (ht : 0 ≤ t) (u v : LTI.State n)

example : m.field 0 = 0 := by simp
example : m.field (u + v) - m.field u = m.field v := by aesop
example : m.operator u = m.field u := by simp
example : LTI.sqNorm u = ‖LTI.euclidean u‖ ^ 2 := by aesop
example : ∃ z, LTI.IsTrajectory m z ∧ z 0 = u := by aesop
example : 0 ≤ LTI.sqNorm u := by aesop
example : LTI.sqNorm (0 : LTI.State n) = 0 := by simp
example : LTI.sqNorm u = 0 ↔ u = 0 := by simp

include hx in
example (P : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun s => LTI.energy P (x s))
      (dotProduct (m.field (x t)) (P.mulVec (x t)) +
       dotProduct (x t) (P.mulVec (m.field (x t)))) t := by aesop
example : dotProduct (m.field u) (c.P.mulVec u) +
    dotProduct u (c.P.mulVec (m.field u)) = -LTI.sqNorm u := by aesop
include hx in
example : HasDerivAt (fun s => LTI.energy c.P (x s)) (-LTI.sqNorm (x t)) t := by aesop
include hx ht in
example : LTI.energy c.P (x t) ≤ Real.exp (-(t / c.upper)) * LTI.energy c.P (x 0) := by aesop
include hx ht in
example : LTI.sqNorm (x t) ≤
    (c.upper / c.lower) * Real.exp (-(t / c.upper)) * LTI.sqNorm (x 0) := by aesop
include hx ht in
example : ‖LTI.euclidean (x t)‖ ≤ Real.sqrt (c.upper / c.lower) *
    Real.exp (-(t / c.upper) / 2) * ‖LTI.euclidean (x 0)‖ := by aesop
include c hx hy ht in
example (h0 : x 0 = y 0) : x t = y t := by aesop
include c hx ht in
example : x t = LTI.response m (x 0) t := by aesop
include c hx in
example : Filter.Tendsto (fun t => LTI.sqNorm (x t)) Filter.atTop (nhds 0) := by aesop
example : generated.linearField m.A u = m.A.mulVec u := by simp
end LTIReuse


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for root in powerlib.Registry.theoremNames env do
    if root.toString.startsWith "powerlib.LTI." || root == `powerlib.generated.linearField_spec then
      for axiomName in powerlib.Search.declarationAxioms env root do
        unless powerlib.Search.allowedAxiom axiomName do
          throwError "Unexpected axiom {axiomName} in {root}"
  logInfo "POWERLIB_LTI_REUSE_OK"
