import powerlib

open powerlib Filter
open scoped Topology

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

-- Ordinary callers use the default tactic interfaces, with no supplied rule lists.
example (m : Impedance) (e initial : ℝ) :
    equilibriumResponse m e initial 0 = initial := by simp
example (m : Impedance) : IsEquilibrium m 0 0 := by simp
example (m : Impedance) (v e : ℝ) (he : IsEquilibrium m v e) :
    AsymptoticallyStable m v e ↔ 0 < m.resistance := by simp [he]
example (m : Impedance) (v e : ℝ) (he : IsEquilibrium m v e) :
    GloballyAsymptoticallyStable m v e ↔ 0 < m.resistance := by simp [he]
example (m : Impedance) (hR : 0 < m.resistance) : Nonempty (Accepted m) := by
  simpa using hR

example (m : Impedance) (c : Accepted m) : AsymptoticallyStable m 0 0 := by aesop
example (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    LyapunovStable m v e ∧ GloballyAsymptoticallyStable m v e ∧
      GloballyExponentiallyStable m v e := by aesop
example (m : Impedance) (hR : 0 < m.resistance) (v e : ℝ)
    (he : IsEquilibrium m v e) : GloballyExponentiallyStable m v e := by aesop

-- Library search handles existence without putting a generic existential rule
-- into the default simplifier or Aesop rule set.
example (m : Impedance) (v e initial : ℝ) (he : IsEquilibrium m v e) :
    ∃ i, IsTrajectory m v i ∧ i 0 = initial := by exact?

example (m : Impedance) (hm : m.Stable) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) :
    Tendsto i atTop (𝓝 e) := by aesop
example (m : Impedance) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    |i t - e| = |i 0 - e| * Real.exp (-(toStateSpace m).decay * t) := by exact?
example (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    (i t - e) ^ 2 = (i 0 - e) ^ 2 * Real.exp (-(c.rate * t)) := by aesop
example (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => energy c.p (i s - e)) (-(i t - e) ^ 2) (Set.Ici 0) t := by
  aesop

-- Standard simplification also rejects nonpositive resistance at zero input.
example (m : Impedance) (hR : m.resistance ≤ 0) :
    ¬ GloballyAsymptoticallyStable m 0 0 := by simpa using hR

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

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let domains := Registry.theoremNames env (some .domain)
  let foundations := Registry.theoremNames env (some .foundation)
  for name in #[`powerlib.lcl_stable_iff, `powerlib.impedance_stable_iff,
      `powerlib.Accepted.stable, `powerlib.LCL.Accepted.stable,
      `powerlib.asymptoticallyStable_iff_resistance_pos,
      `powerlib.Accepted.globallyExponentiallyStable,
      `powerlib.Accepted.energy_derivative] do
    unless domains.contains name do
      throwError "Public domain theorem missing from discovery: {name}"
  for name in #[`powerlib.state_roundtrip, `powerlib.LCL.circuit_roundtrip,
      `powerlib.generated.convert_spec, `powerlib.generated.convertLCL_spec,
      `powerlib.trajectory_iff_circuit] do
    unless foundations.contains name do
      throwError "Imported foundation theorem missing from discovery: {name}"
  unless (Registry.kindOf? env `powerlib.response).isNone do
    throwError "A definition was classified as a theorem"
  for name in Registry.theoremNames env do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Discovery returned a non-theorem: {name}"
  logInfo "POWERLIB_AUTOMATION_OK"
