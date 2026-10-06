import powerlib

open powerlib

-- Public interfaces for simplification, extensionality, and supplied certificates.
example (m : Impedance) : toImpedance (toStateSpace m) = m := by simp
example (m : LCL.Circuit) : LCL.toCircuit (LCL.toStateSpace m) = m := by simp

example (p q : LCL.SymmetricMatrix) (h11 : p.p11 = q.p11) (h12 : p.p12 = q.p12)
    (h13 : p.p13 = q.p13) (h22 : p.p22 = q.p22) (h23 : p.p23 = q.p23)
    (h33 : p.p33 = q.p33) : p = q := by ext <;> assumption

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → E} {V : E → ℝ} {equilibrium : E}
    (certificate : Dynamics.QuadraticDecayCertificate f V equilibrium)
    (hf : ContDiff ℝ 1 f) :
    Dynamics.ForwardComplete f ∧ Dynamics.GloballyExponentiallyStable f equilibrium := by aesop

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`powerlib.generated.convert_spec, `powerlib.generated.convertLCL_spec,
      `powerlib.Dynamics.globallyAsymptoticallyStable_of_strictLyapunov,
      `powerlib.Dynamics.QuadraticDecayCertificate.globallyExponentiallyStable] do
    unless (powerlib.Registry.kindOf? env name).isSome do
      throwError "Public theorem missing from its classification: {name}"
  unless (powerlib.Registry.kindOf? env `powerlib.response).isNone do
    throwError "A definition was classified as a theorem"
  logInfo "POWERLIB_API_OK"
