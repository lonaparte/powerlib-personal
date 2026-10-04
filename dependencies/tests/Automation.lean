import powerlib

open powerlib

example (m : StateSpace) : toStateSpace (toImpedance m) = m := by simp
example (m : Impedance) : toImpedance (toStateSpace m) = m := by simp
example (x : Positive) : reciprocal (reciprocal x) = x := by simp
example (m : Impedance) (h : 0 < m.resistance) : (toStateSpace m).Stable := by
  simpa using h
example (m : Impedance) (initial : ℝ) : response m initial 0 = initial := by simp

example (m : Impedance) (c : Accepted m) : m.Stable := by aesop
example (m : Impedance) (c : Accepted m) (i : ℝ) :
    2 * c.p * i * (toStateSpace m).field i 0 = -i ^ 2 := by aesop
example (m : Impedance) (initial t : ℝ) :
    HasDerivAt (response m initial) ((toStateSpace m).field (response m initial t) 0) t := by
  aesop
example (m : Impedance) (c : Accepted m) (initial t : ℝ) :
    (response m initial t) ^ 2 = initial ^ 2 * Real.exp (-c.rate * t) := by aesop

example (m : LCL.Circuit) : LCL.toCircuit (LCL.toStateSpace m) = m := by simp
example (m : LCL.StateSpace) : LCL.toStateSpace (LCL.toCircuit m) = m := by simp
example (m : LCL.Circuit) (hp : m.Passive)
    (hd : m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0) :
    (LCL.toStateSpace m).Stable := by simpa [hp] using hd
example (m : LCL.Circuit) :
    (LCL.toStateSpace m).Stable ↔ m.Stable := by simp

example (m : LCL.Circuit) (c : LCL.Accepted m) : (LCL.toStateSpace m).Stable := by aesop
example (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ)
    (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < LCL.energy c.p x y z := by aesop
example (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ) :
    let f := (LCL.toStateSpace m).field x y z 0 0
    LCL.energyDerivative c.p x y z f.1 f.2.1 f.2.2 = -(x^2+y^2+z^2) := by aesop
example (m : LCL.Circuit) (h2 : 0 < m.a2) (h1 : 0 < m.a1) (h0 : 0 < m.a0)
    (hg : 0 < m.a2*m.a1-m.a3*m.a0) : m.Stable := by aesop

example (p q : LCL.SymmetricMatrix) (h11 : p.p11 = q.p11) (h12 : p.p12 = q.p12)
    (h13 : p.p13 = q.p13) (h22 : p.p22 = q.p22) (h23 : p.p23 = q.p23)
    (h33 : p.p33 = q.p33) : p = q := by ext <;> assumption

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

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let domains := Registry.theoremNames env (some .domain)
  let foundations := Registry.theoremNames env (some .foundation)
  for name in #[`powerlib.lcl_stable_iff, `powerlib.impedance_stable_iff,
      `powerlib.Accepted.stable, `powerlib.LCL.Accepted.stable,
      `powerlib.LTI.Accepted.exponentially_stable, `powerlib.LTI.trajectory_exists,
      `powerlib.LTI.Accepted.response_unique, `powerlib.LTI.Accepted.sqNorm_tendsto_zero] do
    unless domains.contains name do
      throwError "Public domain theorem missing from discovery: {name}"
  for name in #[`powerlib.state_roundtrip, `powerlib.LCL.circuit_roundtrip,
      `powerlib.generated.convert_spec, `powerlib.generated.convertLCL_spec,
      `powerlib.generated.linearField_spec, `powerlib.LTI.Model.perturbation] do
    unless foundations.contains name do
      throwError "Imported foundation theorem missing from discovery: {name}"
  unless (Registry.kindOf? env `powerlib.response).isNone do
    throwError "A definition was classified as a theorem"
  for name in Registry.theoremNames env do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Discovery returned a non-theorem: {name}"
  let ltiCoverage := #[`powerlib.LTI.Model.zero_equilibrium, `powerlib.LTI.Model.perturbation,
    `powerlib.LTI.Model.operator_apply, `powerlib.LTI.sqNorm_eq_norm_sq,
    `powerlib.LTI.response_initial, `powerlib.LTI.response_solves, `powerlib.LTI.trajectory_exists,
    `powerlib.LTI.sqNorm_nonneg, `powerlib.LTI.sqNorm_zero, `powerlib.LTI.sqNorm_eq_zero_iff,
    `powerlib.LTI.energy_derivative, `powerlib.LTI.lyapunov_dissipation,
    `powerlib.LTI.Accepted.energy_derivative, `powerlib.LTI.Accepted.energy_decay,
    `powerlib.LTI.Accepted.decay_bound, `powerlib.LTI.Accepted.norm_bound,
    `powerlib.LTI.Accepted.exponentially_stable, `powerlib.LTI.Accepted.response_bound,
    `powerlib.LTI.Accepted.trajectory_unique, `powerlib.LTI.Accepted.response_unique,
    `powerlib.LTI.Accepted.sqNorm_tendsto_zero]
  let ltiRegistered := (Registry.theoremNames env).filter (`powerlib.LTI).isPrefixOf
  unless ltiRegistered.size == ltiCoverage.size && ltiCoverage.all ltiRegistered.contains do
    throwError "Update LTI automation examples and their coverage inventory together"
  logInfo "POWERLIB_AUTOMATION_OK"
