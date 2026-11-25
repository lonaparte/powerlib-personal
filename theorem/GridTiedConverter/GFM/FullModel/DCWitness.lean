import theorem.GridTiedConverter.GFM.FullModel.Counterexample

/-! # The 16-state grid-forming converter with a DC link: a locally exponentially stable member

Model boundary.
The 16-state DC variant of `theorem/GridTiedConverter/GFM/FullModel/DC.lean` (`DCParams`: the AC
model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` with a constant-power DC source, a
DC link `C_dc`, a lossless averaged bridge not limited by `v_dc`, and a DC-voltage PI on the
filtered voltage setting the VSM set-point; state order, frames and directions of that module:
currents out of the converter positive, export-positive per-unit power) at one explicit rational
parameter point `dcWitness`: the AC parameters of the 13-state witness `witness` of
`theorem/GridTiedConverter/GFM/FullModel/Counterexample.lean` (`ω₀ = 1`, lossless filter and line,
`L_f = C_f = 1/10`, `L_g = 1`, `V = 1`, no virtual impedance, no droop, `M = D = 1/10`,
`P_ref = 0`, `E₀ = 2`, `ω_q = 1`) with `C_dc = v_ref = ω_f = 1`, `P_dc = 0`, DC-PI gains
`K_pdc = 1/2`, `K_idc = 1/20`, read about the quasi-steady point `δ* = 0`, `Q* = 2`, `ξ* = 0`,
`v_dc = v_f = v_ref` (`dcWitnessModel`). Continuous time, autonomous, no input. The time scale
`ε` of the electromagnetic and inner-loop states (`DCParams.timeScaled`) is the only quantity left
free. Level: the six-state reduced Jacobian at the point and local exponential stability of the
time-scaled model for small `ε`; nothing is claimed at `ε = 1`.

Source: the transfer law `dcFamily_exists_epsStar_mem_den_LES` of
`theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean` and the boundary layer of the 13-state
witness (`witness_fastBlock_spectrallyStable`). The DC gains were chosen by exact symbolic
computation (rational arithmetic; derivation notes outside the repository): at the point the
reduced characteristic polynomial is `(s + 1)(s⁵ + 2s⁴ + 21s³ + 20s² + 10s + 1)`, whose quintic
factor has the Hurwitz determinants `2, 22, 402, 3577, 3577`; the kernel checks the Hurwitz
property through a rational Lyapunov certificate (`lyapunov_certificate%`,
`theorem/Linear/Synthesis.lean`), not through these determinants.

Results.
* `witness_bridgeCoeff`: the harmonic coefficient of the quasi-steady bridge power of the witness
  is `κ = −j`; `witness_bridgeSlope`: `∂P_br/∂δ (0, 2) = 2`; `witness_PbrQ`: `P_br(0, 2) = 0`
  (lossless filter: the bridge power is the line power).
* `dcWitness_reducedJacobian`: the reduced Jacobian `DCParams.reducedJacobian 0 2 1` of the DC
  witness is the real image of the rational matrix `dcWitnessJac`
  `[[0, 1, 0, 0, 0, 0], [−20, −1, 0, 0, 1/2, 5], [0, 0, −1, 0, 0, 0], [−2, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, −1]]`;
  `dcWitness_isHurwitz_reducedJacobian`: it is Hurwitz (`dcWitnessCertificate`).

Family and connection conclusions.
* `dcWitness_exists_epsStar_mem_den_LES` (connection, family `FullModel.dcFamily`): there is
  `ε* > 0` such that the time-scaled DC witness `dcWitnessModel.timeScaled ε` is locally
  exponentially stable for every `ε ∈ (0, ε*)`: the denotation of local exponential stability of
  the DC-variant family is not empty (the family has no stability requirement of its own,
  `dcFamily`; its known members were the unstable ones of `dcFamily_mem_den_unstable`).
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex ComplexConjugate Matrix
open powerlib.Dynamics (State)

/-- The DC witness: the AC parameters of `witness` with `C_dc = 1`, `P_dc = 0`, `v_ref = 1`,
`K_pdc = 1/2`, `K_idc = 1/20`, `ω_f = 1`. -/
def dcWitness : DCParams := ⟨witness, 1, 0, 1, 1 / 2, 1 / 20, 1⟩

/-- The DC witness read about the quasi-steady point `δ* = 0`, `Q* = 2`, `ξ* = 0`. -/
def dcWitnessModel : DCModel := ⟨dcWitness, 0, 2, 0⟩

@[tmio M, powerlib_domain] private theorem witness_Zf : witness.Zf = (1 / 10 : ℂ) * I := by
  rw [Params.Zf_eq]; simp [witness]

/-- The harmonic coefficient of the quasi-steady bridge power of the witness, `κ = −j`. -/
@[tmio M, powerlib_domain] theorem witness_bridgeCoeff : witness.bridgeCoeff = -I := by
  simp only [Params.bridgeCoeff, Params.bridgeMu, Params.bridgeNu, Params.currentAl,
    Params.currentBe, witness_Zg, witness_Zv, witness_Zt, witness_Bf, witness_Zf]
  simp [witness]
  apply Complex.ext <;> simp

/-- The slope of the quasi-steady bridge power of the witness at `(δ, E) = (0, 2)`:
`∂P_br/∂δ = E |κ| cos(arg(jκ)) = 2`. -/
@[tmio M, powerlib_domain] theorem witness_bridgeSlope : witness.bridgeSlope 0 2 = 2 := by
  simp [Params.bridgeSlope, witness_bridgeCoeff]

/-- The quasi-steady bridge power of the witness at `(δ, E) = (0, 2)` vanishes. -/
@[tmio M, powerlib_domain] theorem witness_PbrQ : witness.PbrQ 0 2 = 0 := by
  rw [witness.PbrQ_eq (by rw [witness_Zt]; exact Complex.I_ne_zero), witness_bridgeCoeff]
  simp only [Params.bridgeOffset, Params.bridgeMu, Params.bridgeNu, Params.currentAl,
    Params.currentBe, witness_Zg, witness_Zv, witness_Zt, witness_Bf, witness_Zf]
  simp [witness]

/-- The reduced Jacobian of the DC witness at its point, order `(δ, Δω, Q_f, v_dc, ξ_dc, v_f)`. -/
def dcWitnessJac : Matrix (Fin 6) (Fin 6) ℚ :=
  !![0, 1, 0, 0, 0, 0; -20, -1, 0, 0, 1 / 2, 5; 0, 0, -1, 0, 0, 0; -2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1]

/-- A rational Lyapunov certificate of `dcWitnessJac`, produced by the verified synthesizer of
`theorem/Linear/Synthesis.lean` and checked by the kernel. -/
def dcWitnessCertificate : Linear.Certificate (Linear.Positive.real dcWitnessJac) :=
  lyapunov_certificate% dcWitnessJac

/-- The reduced Jacobian of the DC witness at `(δ*, Q*, v_ref) = (0, 2, 1)` is the real image of
`dcWitnessJac`: power–angle slope `2`, reactive slope `0`, bridge slope `2` and no droop. -/
@[tmio M, powerlib_domain] theorem dcWitness_reducedJacobian :
    dcWitness.reducedJacobian 0 2 1 = Linear.Positive.real dcWitnessJac := by
  have hP : witness.powerSlope 0 2 = 2 := by
    simp [Params.powerSlope, Params.Rt, Params.Xt, witness]
  have hQ : witness.reactiveSlope 0 2 = 0 := by
    simp [Params.reactiveSlope, Params.Rt, Params.Xt, witness]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DCParams.reducedJacobian, dcWitnessJac, dcWitness, witness_emf, hP, hQ,
      witness_bridgeSlope] <;> norm_num [witness]

/-- The reduced Jacobian of the DC witness is Hurwitz (`dcWitnessCertificate`). -/
@[tmio M, powerlib_domain] theorem dcWitness_isHurwitz_reducedJacobian :
    LinearSystems.IsHurwitz (dcWitness.reducedJacobian 0 2 1) := by
  rw [dcWitness_reducedJacobian]
  exact dcWitnessCertificate.isHurwitz

/-- **A locally exponentially stable DC variant (connection).** There is `ε* > 0` such that the
time-scaled DC witness is in the denotation of local exponential stability of the DC-variant
family for every `ε ∈ (0, ε*)`: the transfer `dcFamily_exists_epsStar_mem_den_LES` with the
boundary layer of the 13-state witness (`witness_fastBlock_spectrallyStable`), the balance
`P = P_ref`, `Q = Q*` (`witness_balance`), `P_br = P_dc` (`witness_PbrQ`) and the Hurwitz reduced
Jacobian (`dcWitness_isHurwitz_reducedJacobian`). -/
@[tmio TM, powerlib_domain] theorem dcWitness_exists_epsStar_mem_den_LES :
    connection% (∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      dcWitnessModel.timeScaled ε ∈ dcFamily.den (.flow .locallyExponentiallyStable)) :=
  dcFamily_exists_epsStar_mem_den_LES dcWitnessModel
    (by norm_num [dcWitnessModel, dcWitness, witness])
    (by norm_num [dcWitnessModel, dcWitness, witness])
    (by norm_num [dcWitnessModel, dcWitness, witness])
    (by norm_num [dcWitnessModel, dcWitness, witness])
    (by norm_num [dcWitnessModel, dcWitness, witness])
    (by rw [show dcWitnessModel.q.Zt = witness.Zt from rfl, witness_Zt]; exact I_ne_zero)
    (by norm_num [dcWitnessModel, dcWitness, witness])
    (by norm_num [dcWitnessModel, dcWitness, witness])
    (by norm_num [dcWitnessModel, dcWitness]) (by norm_num [dcWitnessModel, dcWitness])
    (by norm_num [dcWitnessModel, dcWitness])
    (by simpa [dcWitnessModel, dcWitness] using witness_balance.1) witness_balance.2
    (by simp [dcWitnessModel, dcWitness, witness_emf, witness_PbrQ])
    witness_fastBlock_spectrallyStable dcWitness_isHurwitz_reducedJacobian

end powerlib.GFM.FullModel
