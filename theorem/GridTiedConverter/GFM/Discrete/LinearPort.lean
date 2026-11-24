import theorem.GridTiedConverter.GFM.Discrete.SwingPort
import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.Numerics.ImplicitPorts

/-! # Linearized grid-forming port models: passivity, explicit Euler, the implicit midpoint rule
and backward Euler

The two grid-forming (GFM) synchronization models with the active-power set-point as input port
and the frequency deviation as output, linearized about a selected angle: the two-state swing
(`SwingPort.Model.plant`, from `theorem/GridTiedConverter/GFM/Discrete/SwingPort.lean`) and the
three-state VSM with a first-order power filter (`FilterPort.plant`, from the VSM + filter field
of `theorem/GridTiedConverter/GFM/VSMLPF.lean`). Each plant is the Jacobian of its nonlinear port
field at the selected point together with its input matrix (`SwingPort.hasFDerivAt_zeroInput`,
`FilterPort.hasFDerivAt_zeroInput`, the input entering affinely). The swing plant is passive with
the storage `½ K Δδ² + ½ M Δω²` whenever `K ≥ 0`; the filter plant is passive exactly when
`K ≤ D ω_c` (within positive `M, D, ω_c, K`), with the storage
`½ K Δδ² + ½ M Δω² + ½ β (ΔP_f − K Δδ)²`, `β = (2 D ω_c − K)/K²`, and for `K > D ω_c` a periodic
input at a low frequency, where `Re G(jw) < 0`, draws energy over every period. Discretized with a
step `h > 0`, the explicit Euler implementations are never passive, for any storage (the output
`Δω` does not see the input of the step); the implicit midpoint implementations are passive with
the continuous storage at every step whenever the continuous certificate exists, and for the
filter exactly when the continuous loop is: for `K > D ω_c` a discrete periodic input at a
frequency `θ = 2π/N` whose bilinear image `(2/h) tan(θ/2)` lies in the band `Re G(jw) < 0`
draws energy over every period. The backward Euler implementations (output at the end of the
step) keep the continuous storage, and for the filter they are passive exactly when
`K (2 − h ω_c) ≤ 2 D ω_c`: a large step makes a mismatched filter passive, with a step-dependent
storage, so the backward Euler realization of passivity is sound but not complete. Scaffold:
`theorem/Numerics/EulerPorts.agda`.

Model boundary.
* Two-state swing (`SwingPort.linearFamily`): state `(Δδ, Δω)` about `(δ*, 0)`, plant
  `A = [[0, 1], [−K/M, −D/M]]`, `B = (0, 1/M)ᵀ`, `C = (0, 1)`, no feedthrough, with the
  synchronizing coefficient `K = A cos(δ* − α)` of the one-harmonic power characteristic
  `P(δ) = c₀ + A sin(δ − α)`; the parameter ranges of `SwingPort.Params` (`M > 0`, `D ≥ 0`,
  `A > 0`). Export-positive power: `M Δω̇ = u − K Δδ − D Δω`.
* Three-state VSM + filter (`FilterPort.linearFamily`), over the models `VSMLPF.Model` of the
  lossless infinite bus: state `(Δδ, Δω, ΔP_f)` about `(δ*, 0, P₀)`, the port field
  `M ω̇ = P₀ + u − P_f − D ω` (the set-point deviation `u` added to `P₀`), plant
  `A = VSMLPF.jacobian δ*`, `B = (0, 1/M, 0)ᵀ`, `C = (0, 1, 0)`, no feedthrough, `K = K₀ cos δ*`.
* Continuous time; linearization about the selected point (an equilibrium when the angle is
  balanced, which the passivity statements do not need: they are statements about the plants).
* Discretizations (I): over `Numerics.EulerStep` (a model and a step `h > 0`): explicit Euler
  `x⁺ = x + h (A x + B u)`, output `C x` (`Numerics.eulerPortFamily`); implicit midpoint
  `x⁺ − x = h (A x̄ + B u)`, `x̄ = (x + x⁺)/2`, output `C x̄` (`Numerics.midpointPortFamily`);
  backward Euler `x⁺ − x = h (A x⁺ + B u)`, output `C x⁺` (`Numerics.backwardEulerPortFamily`);
  step length `h`, exact arithmetic, fixed step. Excluded: step-aware Euler outputs (in
  `theorem/GridTiedConverter/GFM/Discrete/StepAwareEuler.lean`), the nonlinear discrete gradient,
  step-size control, delays, PWM, inner loops, PLL, line dynamics.

Source: work-sync GFM study note t9 (scratchpad `gfm/t9-discrete/REPORT-coord.md`, (b) and (c):
2-state storage `diag(K, M)`; 3-state passive iff `K ≤ D ω_c` with the storage above, from the
real part `Re(1/G(jw)) = D − ω_c K/(w² + ω_c²)`; explicit Euler never passive; implicit midpoint
passive with the continuous storage; backward Euler passive iff `h ≥ (2/ω_c)(1 − D ω_c/K)` in
the band `D ω_c < K < D ω_c + D²/M`, script `s4_passive_schemes_linear.py` (5));
`theorem/Numerics/EulerPorts.lean` (`Numerics.eulerPortFamily_not_mem_den_passive_linear`,
`Numerics.midpointPortFamily_mem_den_passive`), `theorem/Numerics/ImplicitPorts.lean`
(`Numerics.midpointSystem_not_passive_of_phasor`, `Numerics.backwardEulerSystem_passiveWith_of`,
`Numerics.backwardEulerSystem_not_passive_of_phasor`,
`Numerics.backwardEulerPortFamily_mem_den_passive`), `theorem/Numerics/PeriodicInput.lean`
(`Numerics.exists_periodic_frequency`), `theorem/Linear/Family.lean`
(`Family.IsLinear.mem_den_passive`), `theorem/Port/Linear.lean` (KYP certificates); Willems,
"Dissipative dynamical systems", Arch. Rational Mech. Anal. 45 (1972) (storage functions,
periodic inputs); Brogliato, Lozano, Maschke and Egeland, *Dissipative Systems Analysis and
Control* (2007), §3 (KYP lemma, positive real transfer functions, the bilinear transform).

Results.
* `SwingPort.Model.K`, `SwingPort.Model.plant`; `SwingPort.hasFDerivAt_zeroInput` (the plant's
  `A` is the Jacobian of the centred zero-input field at the origin),
  `SwingPort.system_field_eq`, `SwingPort.system_output_eq` (input matrix `B`, output `C z`).
* `FilterPort.system` (the VSM + filter loop with the set-point port), `FilterPort.plant`;
  `FilterPort.hasFDerivAt_zeroInput`, `FilterPort.system_field_eq`,
  `FilterPort.system_output_eq`; `FilterPort.plant_phasor_complex` (the plant's phasor at a
  complex frequency `s`, output phasor `Δω = 1`).

Family and connection conclusions.
* `SwingPort.linearFamily`: every model read as the port system of its plant; requirements
  `synchronizing` (`K ≥ 0`) and `antiSynchronizing` (`K < 0`); passivity translates into
  `synchronizing`, the flow sentences have no translation (the whole, inconsistent, language), the
  envelope sentences into nothing. `SwingPort.linear_mem_den_passive` (passive with the storage
  `½ K Δδ² + ½ M Δω²`, a KYP certificate, for `K ≥ 0`); `SwingPort.linear_chain_le_semantics`.
* `FilterPort.linearFamily`: requirements `physical` (`M, D, ω_c > 0`), `synchronizing`
  (`K > 0`), `matched` (`K ≤ D ω_c`), `mismatched` (`D ω_c < K`); passivity translates into
  `physical`, `synchronizing`, `matched`. `FilterPort.linear_mem_den_passive` (the KYP storage
  above), `FilterPort.linear_not_mem_den_passive` (`K > D ω_c`, `D ≥ 0`, `ω_c > 0`, `M ≠ 0`: a
  periodic solution under a periodic input of frequency `w`, `D (w² + ω_c²) < ω_c K`, returns to
  its initial state while drawing `π/w (ω_c K/(w² + ω_c²) − D) > 0` per period, which no storage
  pays for), `FilterPort.linear_mem_den_passive_iff` (within positive `M, D, ω_c, K`: passive iff
  `K ≤ D ω_c`), `FilterPort.linear_exactUnder_passive` (the passivity translation is exact within
  `physical` and `synchronizing`), `FilterPort.linear_chain_le_semantics`.
* Explicit Euler (I): `SwingPort.linearEulerFamily`, `FilterPort.linearEulerFamily`;
  `SwingPort.linearEuler_not_mem_den_passive`, `FilterPort.linearEuler_not_mem_den_passive` — no
  discretization is passive, whatever its step and storage
  (`Numerics.eulerPortFamily_not_mem_den_passive_linear`, `C ≠ 0`).
* Implicit midpoint (I): `SwingPort.linearMidpointFamily`, `FilterPort.linearMidpointFamily`;
  `SwingPort.linearMidpoint_mem_den_passive` (`K ≥ 0`) and
  `FilterPort.linearMidpoint_mem_den_passive` (`0 < K ≤ D ω_c`) — passive at every step, with
  the continuous storage (`Numerics.midpointPortFamily_mem_den_passive`; the step is well posed,
  `det(I − (h/2) A) > 0`); `FilterPort.linearMidpoint_not_mem_den_passive` (`K > D ω_c`: no
  midpoint discretization is passive, at any step — the plant's phasor at a frequency `w` in the
  band, `w = 2 sin θ/(h (1 + cos θ))` with `θ = 2π/N`, refutes it,
  `Numerics.midpointSystem_not_passive_of_phasor`), `FilterPort.linearMidpoint_mem_den_passive_iff`
  (within positive `M, D, ω_c, K`: passive iff `K ≤ D ω_c`, at every step); the realization
  `FilterPort.linearMidpoint` (`Numerics.midpointPorts`) and
  `FilterPort.linearMidpoint_realizationExactUnder_passive` (exact within `physical` and
  `synchronizing`).
* Backward Euler (I): `SwingPort.linearBackwardEulerFamily`,
  `SwingPort.linearBackwardEuler_mem_den_passive` (`K ≥ 0`, every step, the continuous storage,
  `Numerics.backwardEulerPortFamily_mem_den_passive`); `FilterPort.linearBackwardEulerFamily`, the
  realization `FilterPort.linearBackwardEuler` (`Numerics.backwardEulerPorts`);
  `FilterPort.linearBackwardEuler_mem_den_passive` (`K (2 − h ω_c) ≤ 2 D ω_c`, with the storage
  `½ K Δδ² + ½ M Δω² + ½ b_h (ΔP_f − K Δδ)²`,
  `b_h = (2 D ω_c (2 + h ω_c) + K (h² ω_c² − 2))/(2 K²)`,
  `Numerics.backwardEulerSystem_passiveWith_of`),
  `FilterPort.linearBackwardEuler_not_mem_den_passive` (`K (2 − h ω_c) > 2 D ω_c`: the plant's
  phasor at `s = (1 − e^{−iθ})/h`, `θ = 2π/N` near zero,
  `Numerics.backwardEulerSystem_not_passive_of_phasor`),
  `FilterPort.linearBackwardEuler_mem_den_passive_iff` (within `M > 0`, `D ≥ 0`, `ω_c > 0`,
  `K > 0`: passive iff `K (2 − h ω_c) ≤ 2 D ω_c`, i.e. `h ≥ (2/ω_c)(1 − D ω_c/K)` — for every
  such `K`, not only in the stable band of the study);
  `FilterPort.linearBackwardEuler_realizationSoundUnder_passive` (backward Euler preserves
  passivity within `physical` and `synchronizing`) and
  `FilterPort.not_linearBackwardEuler_realizationCompleteUnder_passive` (spurious passivity: the
  mismatched model `M = D = ω_c = 1`, `K = 3/2` is not passive and its discretization with
  `h = 1` is).
-/

noncomputable section

namespace powerlib.GFM

open powerlib.Dynamics (State mk3 toEuclideanCLM_apply3)
open Matrix

namespace SwingPort

/-! ## The two-state swing -/

/-- The synchronizing coefficient `K = A cos(δ* − α)` at the selected angle. -/
def Model.K (m : Model) : ℝ := m.p.A * Real.cos (m.δs - m.p.α)

/-- The linearized swing port at the selected point: `A = [[0, 1], [−K/M, −D/M]]`,
`B = (0, 1/M)ᵀ`, `C = (0, 1)`, no feedthrough (`hasFDerivAt_zeroInput`, `system_field_eq`,
`system_output_eq`). -/
def Model.plant (m : Model) : Linear.Plant 2 1 :=
  ⟨!![0, 1; -m.K / m.p.M, -m.p.D / m.p.M], !![0; 1 / m.p.M], !![0, 1], 0⟩

/-- The plant's state matrix is the Jacobian of the centred zero-input field at the origin.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_zeroInput (m : Model) :
    HasFDerivAt m.system.zeroInput (Linear.op m.plant.A) 0 := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt
    (x := (0 : State 2))
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt
    (x := (0 : State 2))
  fin_cases i
  · convert h1 using 1
    · funext z
      simp [Model.system, Port.System.zeroInput, Params.field, Model.point]
    · apply ContinuousLinearMap.ext; intro v
      simp [Model.plant, PhasePlane.toEuclideanCLM_apply_zero]
  · have hs := (Real.hasDerivAt_sin (0 + m.δs - m.p.α)).comp_hasFDerivAt (0 : State 2)
      ((h0.add_const m.δs).sub_const m.p.α)
    have h := ((((hasFDerivAt_const (m.p.Pref - m.p.c0) (0 : State 2)).sub
      (hs.const_mul m.p.A)).sub (h1.const_mul m.p.D)).const_mul m.p.M⁻¹)
    convert h using 1
    · funext z
      simp [Model.system, Port.System.zeroInput, Params.field, Params.power, Model.point]
      rw [div_eq_inv_mul]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp [Model.plant, Model.K, PhasePlane.toEuclideanCLM_apply_one]
      ring

/-- The set-point enters through the plant's input matrix: `f(z, u) = f(z, 0) + B u`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem system_field_eq (m : Model) (z : State 2) (u : Fin 1 → ℝ) :
    m.system.field z u = m.system.zeroInput z + WithLp.toLp 2 (m.plant.B *ᵥ u) := by
  ext i
  fin_cases i
  · simp [Model.system, Port.System.zeroInput, Params.field, Model.plant]
  · simp [Model.system, Port.System.zeroInput, Params.field, Model.plant, dotProduct]
    ring

/-- The output is the plant's output `C z`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem system_output_eq (m : Model) (z : State 2) (u : Fin 1 → ℝ) :
    m.system.output z u = m.plant.C *ᵥ WithLp.ofLp z + m.plant.D *ᵥ u := by
  funext i
  fin_cases i
  simp [Model.system, Model.plant, dotProduct]

/-- Requirements of the linearized swing port. -/
inductive LinearRequirement
  /-- A nonnegative synchronizing coefficient `K ≥ 0`. -/
  | synchronizing
  /-- A negative synchronizing coefficient `K < 0`. -/
  | antiSynchronizing

/-- Satisfaction of a requirement. -/
def LinearMeets (m : Model) : LinearRequirement → Prop
  | .synchronizing => 0 ≤ m.K
  | .antiSynchronizing => m.K < 0

/-- Passivity translates into `K ≥ 0`; the flow sentences have no translation (the whole,
inconsistent, language); the envelope sentences translate into nothing. -/
def linearTranslate : Sentence → Set LinearRequirement
  | .passive => {.synchronizing}
  | .flow _ => Set.univ
  | .envelope _ => ∅

/-- The linearized swing port family: every model read as the port system of its plant. -/
def linearFamily : Family Model LinearRequirement 2 1 :=
  ⟨fun m => m.plant.system, LinearMeets, linearTranslate⟩

@[tmio M, powerlib_domain] theorem linearFamily_isLinear : linearFamily.IsLinear Model.plant :=
  fun _ => rfl

/-- The KYP certificate `P = diag(K, M)`: the storage `½ K Δδ² + ½ M Δω²`. -/
private def kyp (m : Model) (hK : 0 ≤ m.K) : Linear.KYP m.plant where
  P := !![m.K, 0; 0, m.p.M]
  symmetric := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  nonneg x := by
    have hM := m.p.M_pos
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    simp
    nlinarith [mul_nonneg hK (sq_nonneg (x 0)), mul_nonneg hM.le (sq_nonneg (x 1))]
  dissipation x := by
    have hM := m.p.M_pos.ne'
    have hD := m.p.D_nonneg
    rw [Linear.quadratic_sym (by ext i j; fin_cases i <;> fin_cases j <;> simp)]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    simp [Model.plant]
    field_simp
    nlinarith [mul_nonneg hD (sq_nonneg (x 1))]
  output := by
    have hM := m.p.M_pos.ne'
    ext i j
    fin_cases i
    fin_cases j <;> simp [Model.plant, Matrix.mul_apply, Fin.sum_univ_two, hM]
  feedthrough u := by simp [Model.plant]

/-- **The linearized swing port is passive** for `K ≥ 0`, with the storage
`½ K Δδ² + ½ M Δω²` (a KYP certificate: `d/dt` of the storage is `u Δω − D Δω²`). -/
@[tmio TM, powerlib_domain] theorem linear_mem_den_passive (m : Model) (hK : 0 ≤ m.K) :
    connection% (m ∈ linearFamily.den .passive) := by
  have h := linearFamily_isLinear.mem_den_passive (kyp m hK)
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- Every translation of the linearized swing port family is sound. -/
@[tmio TM, powerlib_domain] theorem linear_chain_le_semantics :
    connection% (∀ P, linearFamily.chain P ≤ linearFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine (connection_proof% Family.chain_le_semantics_iff).mpr fun s => ?_
  intro m hm
  rw [(connection_proof% TMIO.mem_realize)] at hm
  rcases s with P | _ | E
  · have h1 : LinearMeets m .synchronizing := hm .synchronizing (Set.mem_univ _)
    have h2 : LinearMeets m .antiSynchronizing := hm .antiSynchronizing (Set.mem_univ _)
    exact absurd h1 (not_le.mpr h2)
  · have h := linear_mem_den_passive m (hm .synchronizing rfl)
    unfold powerlib.TMIO.Statement at h
    exact h
  · rw [(connection_proof% linearFamily_isLinear.den_envelope)]
    trivial

/-- The discretizations of the linearized swing port: a model and a step `h > 0`. -/
abbrev LinearStep := Numerics.EulerStep Model

/-- The explicit Euler discretization family of the linearized swing port. -/
def linearEulerFamily : Family LinearStep LinearRequirement 2 1 :=
  Numerics.eulerPortFamily linearFamily (fun m => m.plant.system) Numerics.EulerStep.design
    Numerics.EulerStep.h

/-- The implicit midpoint discretization family of the linearized swing port. -/
def linearMidpointFamily : Family LinearStep LinearRequirement 2 1 :=
  Numerics.midpointPortFamily linearFamily Model.plant Numerics.EulerStep.design
    Numerics.EulerStep.h

@[tmio M, powerlib_domain] private theorem plant_C_ne_zero (m : Model) : m.plant.C ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [Model.plant] at this

/-- **No explicit Euler discretization of the linearized swing port is passive**, whatever its
step and storage (`Numerics.eulerPortFamily_not_mem_den_passive_linear`: `D = 0`, `C ≠ 0`). -/
@[tmio TM, powerlib_domain] theorem linearEuler_not_mem_den_passive :
    connection% (∀ (m : Model) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : LinearStep) ∉ linearEulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro m h hh
  exact (connection_proof% Numerics.eulerPortFamily_not_mem_den_passive_linear
    (F := linearFamily) (design := Numerics.EulerStep.design) (step := Numerics.EulerStep.h)
    (y := (⟨m, h, hh⟩ : LinearStep)) hh rfl (plant_C_ne_zero m))

/-- The midpoint step of the swing plant is well posed: `det(I − (h/2) A) =
1 + h D/(2M) + h² K/(4M) > 0` for `h ≥ 0`, `K ≥ 0`. -/
@[tmio M, powerlib_domain] private theorem isUnit_det_midpoint (m : Model) (hK : 0 ≤ m.K)
    {h : ℝ} (hh : 0 ≤ h) : IsUnit (1 - (h / 2) • m.plant.A).det := by
  have hM := m.p.M_pos
  have hD := m.p.D_nonneg
  have e : (1 - (h / 2) • m.plant.A).det =
      1 + h * m.p.D / (2 * m.p.M) + h ^ 2 * m.K / (4 * m.p.M) := by
    simp [Model.plant, Matrix.det_fin_two]
    field_simp
    ring
  rw [isUnit_iff_ne_zero, e]
  have : 0 ≤ h * m.p.D / (2 * m.p.M) := by positivity
  have : 0 ≤ h ^ 2 * m.K / (4 * m.p.M) := by positivity
  linarith

/-- **The implicit midpoint discretizations of the linearized swing port are passive** for
`K ≥ 0`, at every step, with the continuous storage `½ K Δδ² + ½ M Δω²`
(`Numerics.midpointPortFamily_mem_den_passive`). -/
@[tmio TM, powerlib_domain] theorem linearMidpoint_mem_den_passive (m : Model) (hK : 0 ≤ m.K)
    (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearMidpointFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  exact (connection_proof% Numerics.midpointPortFamily_mem_den_passive (F := linearFamily)
    (plant := Model.plant) (design := Numerics.EulerStep.design) (step := Numerics.EulerStep.h)
    (y := (⟨m, h, hh⟩ : LinearStep)) (kyp m hK) hh.le (isUnit_det_midpoint m hK hh.le))

/-- The backward Euler discretization family of the linearized swing port. -/
def linearBackwardEulerFamily : Family LinearStep LinearRequirement 2 1 :=
  Numerics.backwardEulerPortFamily linearFamily Model.plant Numerics.EulerStep.design
    Numerics.EulerStep.h

/-- **The backward Euler discretizations of the linearized swing port are passive** for `K ≥ 0`,
at every step, with the continuous storage `½ K Δδ² + ½ M Δω²`
(`Numerics.backwardEulerPortFamily_mem_den_passive`; the step is well posed,
`det(I − h A) = 1 + h D/M + h² K/M > 0`). -/
@[tmio TM, powerlib_domain] theorem linearBackwardEuler_mem_den_passive (m : Model)
    (hK : 0 ≤ m.K) (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearBackwardEulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  have hw := isUnit_det_midpoint m hK (h := 2 * h) (by positivity)
  rw [show 2 * h / 2 = h by ring] at hw
  exact (connection_proof% Numerics.backwardEulerPortFamily_mem_den_passive (F := linearFamily)
    (plant := Model.plant) (design := Numerics.EulerStep.design) (step := Numerics.EulerStep.h)
    (y := (⟨m, h, hh⟩ : LinearStep)) (kyp m hK) hh.le hw)

end SwingPort

/-! ## The three-state VSM with a power filter -/

namespace FilterPort

/-- The VSM + filter loop with the set-point port: `M ω̇ = P₀ + u − P_f − D ω`, in the
coordinates centred at `(δ*, 0, P₀)`, output the frequency deviation `ω`. -/
def system (m : VSMLPF.Model) : Port.System 3 1 :=
  ⟨fun z u => m.field z + WithLp.toLp 2 ![0, u 0 / m.g.M, 0], fun z _ => ![z 1]⟩

/-- The linearized loop: `A = VSMLPF.jacobian δ*`, `B = (0, 1/M, 0)ᵀ`, `C = (0, 1, 0)`, no
feedthrough (`hasFDerivAt_zeroInput`, `system_field_eq`, `system_output_eq`). -/
def plant (m : VSMLPF.Model) : Linear.Plant 3 1 :=
  ⟨m.g.jacobian m.δ, !![0; 1 / m.g.M; 0], !![0, 1, 0], 0⟩

/-- The plant's state matrix is the Jacobian of the centred zero-input field at the origin
(`VSMLPF.hasFDerivAt_field` at the selected point). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_zeroInput (m : VSMLPF.Model) :
    HasFDerivAt (system m).zeroInput (Linear.op (plant m).A) 0 := by
  have h := (m.g.hasFDerivAt_field (0 + m.point)).comp (0 : State 3)
    ((hasFDerivAt_id (0 : State 3)).add_const m.point)
  rw [ContinuousLinearMap.comp_id] at h
  convert h using 1
  · funext z
    simp [system, Port.System.zeroInput, VSMLPF.Model.field]
  · simp [plant, VSMLPF.Model.point, Linear.op]

/-- The set-point enters through the plant's input matrix: `f(z, u) = f(z, 0) + B u`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem system_field_eq (m : VSMLPF.Model) (z : State 3)
    (u : Fin 1 → ℝ) :
    (system m).field z u = (system m).zeroInput z + WithLp.toLp 2 ((plant m).B *ᵥ u) := by
  ext i
  fin_cases i <;> simp [system, Port.System.zeroInput, plant, dotProduct,
    div_eq_inv_mul, mul_comm]

/-- The output is the plant's output `C z`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem system_output_eq (m : VSMLPF.Model) (z : State 3)
    (u : Fin 1 → ℝ) :
    (system m).output z u = (plant m).C *ᵥ WithLp.ofLp z + (plant m).D *ᵥ u := by
  funext i
  fin_cases i
  simp [system, plant, dotProduct, Fin.sum_univ_three]

/-- Requirements of the linearized VSM + filter port. -/
inductive Requirement
  /-- Positive inertia, damping and filter bandwidth. -/
  | physical
  /-- A positive synchronizing coefficient `K = K₀ cos δ* > 0`. -/
  | synchronizing
  /-- A filter matched to the damping: `K ≤ D ω_c`. -/
  | matched
  /-- A filter slower than the damping allows: `D ω_c < K`. -/
  | mismatched

/-- Satisfaction of a requirement. -/
def Meets (m : VSMLPF.Model) : Requirement → Prop
  | .physical => 0 < m.g.M ∧ 0 < m.g.D ∧ 0 < m.g.ωc
  | .synchronizing => 0 < m.K
  | .matched => m.K ≤ m.g.D * m.g.ωc
  | .mismatched => m.g.D * m.g.ωc < m.K

/-- Passivity translates into `physical`, `synchronizing` and `matched`; the flow sentences have
no translation (the whole, inconsistent, language); the envelope sentences into nothing. -/
def translate : Sentence → Set Requirement
  | .passive => {.physical, .synchronizing, .matched}
  | .flow _ => Set.univ
  | .envelope _ => ∅

/-- The linearized VSM + filter port family: every model read as the port system of its plant. -/
def linearFamily : Family VSMLPF.Model Requirement 3 1 :=
  ⟨fun m => (plant m).system, Meets, translate⟩

@[tmio M, powerlib_domain] theorem linearFamily_isLinear : linearFamily.IsLinear plant :=
  fun _ => rfl

/-- The coefficient `β = (2 D ω_c − K)/K²` of the filter term of the storage. -/
private def β (m : VSMLPF.Model) : ℝ := (2 * m.g.D * m.g.ωc - m.K) / m.K ^ 2

/-- The storage matrix of `½ K Δδ² + ½ M Δω² + ½ b (ΔP_f − K Δδ)²`, for a coefficient `b`. -/
private def storageMatrix (m : VSMLPF.Model) (b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![m.K + b * m.K ^ 2, 0, -(b * m.K); 0, m.g.M, 0; -(b * m.K), 0, b]

@[tmio M, powerlib_domain] private theorem storageMatrix_symm (m : VSMLPF.Model) (b : ℝ) :
    (storageMatrix m b)ᵀ = storageMatrix m b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [storageMatrix]

@[tmio M, powerlib_domain] private theorem storage_quadratic (m : VSMLPF.Model) (b : ℝ)
    (x : Fin 3 → ℝ) :
    x ⬝ᵥ (storageMatrix m b *ᵥ x) =
      m.K * x 0 ^ 2 + m.g.M * x 1 ^ 2 + b * (x 2 - m.K * x 0) ^ 2 := by
  simp [storageMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- `xᵀ P A x = −(D x₁² + (1 + b K) x₁ ξ + b ω_c ξ²)`, `ξ = x₂ − K x₀`. -/
@[tmio M, powerlib_domain] private theorem storage_rate (m : VSMLPF.Model) (b : ℝ)
    (hM : m.g.M ≠ 0) (x : Fin 3 → ℝ) :
    x ⬝ᵥ (storageMatrix m b *ᵥ ((plant m).A *ᵥ x)) =
      -(m.g.D * x 1 ^ 2 + (1 + b * m.K) * x 1 * (x 2 - m.K * x 0) +
        b * m.g.ωc * (x 2 - m.K * x 0) ^ 2) := by
  simp [storageMatrix, plant, VSMLPF.jacobian, VSMLPF.Model.K, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem storage_output (m : VSMLPF.Model) (b : ℝ)
    (hM : m.g.M ≠ 0) : (plant m).Bᵀ * storageMatrix m b = (plant m).C := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [storageMatrix, plant, Matrix.mul_apply, Fin.sum_univ_three, hM]

/-- The KYP certificate of the matched filter: `M > 0`, `D ≥ 0`, `ω_c > 0`, `0 < K ≤ D ω_c`. -/
private def kyp (m : VSMLPF.Model) (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc)
    (hK : 0 < m.K) (hKD : m.K ≤ m.g.D * m.g.ωc) : Linear.KYP (plant m) where
  P := storageMatrix m (β m)
  symmetric := storageMatrix_symm m (β m)
  nonneg x := by
    rw [storage_quadratic]
    have hβ : 0 ≤ β m := by
      unfold β
      apply div_nonneg _ (sq_nonneg _)
      nlinarith [mul_nonneg hD hω.le]
    nlinarith [mul_nonneg hK.le (sq_nonneg (x 0)), mul_nonneg hM.le (sq_nonneg (x 1)),
      mul_nonneg hβ (sq_nonneg (x 2 - m.K * x 0))]
  dissipation x := by
    rw [Linear.quadratic_sym (storageMatrix_symm m _), storage_rate m _ hM.ne']
    have hK2 : m.K ^ 2 ≠ 0 := by positivity
    have hβ : β m * m.K ^ 2 = 2 * m.g.D * m.g.ωc - m.K := by
      unfold β
      field_simp
    set ξ := x 2 - m.K * x 0
    have key : m.K ^ 2 * (m.g.D * x 1 ^ 2 + (1 + β m * m.K) * x 1 * ξ +
        β m * m.g.ωc * ξ ^ 2) = m.g.D * (m.K * x 1 + m.g.ωc * ξ) ^ 2 +
        m.g.ωc * (m.g.D * m.g.ωc - m.K) * ξ ^ 2 := by
      linear_combination (m.K * x 1 * ξ + m.g.ωc * ξ ^ 2) * hβ
    have hr : 0 ≤ m.g.D * (m.K * x 1 + m.g.ωc * ξ) ^ 2 +
        m.g.ωc * (m.g.D * m.g.ωc - m.K) * ξ ^ 2 := by
      have := mul_nonneg hD (sq_nonneg (m.K * x 1 + m.g.ωc * ξ))
      have := mul_nonneg (mul_nonneg hω.le (sub_nonneg.mpr hKD)) (sq_nonneg ξ)
      linarith
    have hpos : 0 < m.K ^ 2 := by positivity
    have hq : 0 ≤ m.g.D * x 1 ^ 2 + (1 + β m * m.K) * x 1 * ξ + β m * m.g.ωc * ξ ^ 2 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    linarith
  output := storage_output m _ hM.ne'
  feedthrough u := by simp [plant]

/-- **The linearized VSM + filter port is passive when the filter is matched**, `K ≤ D ω_c`
(with `M > 0`, `D ≥ 0`, `ω_c > 0`, `K > 0`), with the storage
`½ K Δδ² + ½ M Δω² + ½ β (ΔP_f − K Δδ)²`, `β = (2 D ω_c − K)/K²`: its rate is
`u Δω − (D Δω² + (2 D ω_c/K) Δω ξ + β ω_c ξ²)`, `ξ = ΔP_f − K Δδ`, and the quadratic form is
`(D (K Δω + ω_c ξ)² + ω_c (D ω_c − K) ξ²)/K² ≥ 0`. -/
@[tmio TM, powerlib_domain] theorem linear_mem_den_passive (m : VSMLPF.Model) (hM : 0 < m.g.M)
    (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (hKD : m.K ≤ m.g.D * m.g.ωc) :
    connection% (m ∈ linearFamily.den .passive) := by
  have h := linearFamily_isLinear.mem_den_passive (kyp m hM hD hω hK hKD)
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-! ### The mismatched filter: a periodic input draws energy -/

/-- The periodic test motion at the frequency `w` (`r = 1/w`):
`(Δδ, Δω, ΔP_f) = (r sin(w t), cos(w t), a cos(w t) + b sin(w t))`. -/
private def orbit (w r a b t : ℝ) : State 3 :=
  Real.sin (w * t) • WithLp.toLp 2 ![r, 0, b] + Real.cos (w * t) • WithLp.toLp 2 ![0, 1, a]

/-- The input that holds the test motion: `u = M Δω̇ + D Δω + ΔP_f`. -/
private def orbitInput (m : VSMLPF.Model) (w a b t : ℝ) : Fin 1 → ℝ :=
  ![-(m.g.M * w * Real.sin (w * t)) + (m.g.D + a) * Real.cos (w * t) + b * Real.sin (w * t)]

@[tmio T, powerlib_foundation] private theorem orbit_hasDerivAt (w r a b t : ℝ) :
    HasDerivAt (orbit w r a b)
      ((Real.cos (w * t) * w) • WithLp.toLp 2 ![r, 0, b] +
        (-Real.sin (w * t) * w) • WithLp.toLp 2 ![0, 1, a]) t := by
  have hw : HasDerivAt (fun s => w * s) w t := by
    simpa using (hasDerivAt_id t).const_mul w
  exact ((Real.hasDerivAt_sin _).comp t hw).smul_const _ |>.add
    (((Real.hasDerivAt_cos _).comp t hw).smul_const _)

/-- With `r w = 1`, `b w = −ω_c a` and `a (w² + ω_c²) = −ω_c K` the test motion solves the
linearized loop under its input. -/
@[tmio M, powerlib_domain] private theorem orbit_field (m : VSMLPF.Model) (hM : m.g.M ≠ 0)
    {w r a b : ℝ} (hr : r * w = 1) (hb : b * w = -(m.g.ωc * a))
    (ha : a * (w ^ 2 + m.g.ωc ^ 2) = -(m.g.ωc * m.K)) (t : ℝ) :
    (plant m).system.field (orbit w r a b t) (orbitInput m w a b t) =
      (Real.cos (w * t) * w) • WithLp.toLp 2 ![r, 0, b] +
        (-Real.sin (w * t) * w) • WithLp.toLp 2 ![0, 1, a] := by
  ext i
  fin_cases i
  · simp [Linear.Plant.system, plant, VSMLPF.jacobian, orbit, dotProduct]
    linear_combination (-Real.cos (w * t)) * hr
  · simp [Linear.Plant.system, plant, VSMLPF.jacobian, orbit, dotProduct, orbitInput]
    field_simp
    ring
  · simp [Linear.Plant.system, plant, VSMLPF.jacobian, orbit, dotProduct]
    have hK : m.g.K0 * Real.cos m.δ = m.K := rfl
    rw [hK]
    linear_combination (Real.sin (w * t) * r) * ha +
      (-(Real.sin (w * t) * r * m.g.ωc) - Real.cos (w * t)) * hb +
      (Real.sin (w * t) * (m.g.ωc * b - w * a)) * hr

/-- The test motion returns to its initial state after one period, `w T = 2π`. -/
@[tmio T, powerlib_foundation] private theorem orbit_period {w r a b T : ℝ}
    (hwT : w * T = 2 * Real.pi) : orbit w r a b T = orbit w r a b 0 := by
  simp [orbit, hwT]

/-- The power supplied to the test motion: `u Δω`. -/
@[tmio M, powerlib_domain] private theorem orbit_supply (m : VSMLPF.Model) (w r a b t : ℝ) :
    (plant m).system.supply (orbit w r a b t) (orbitInput m w a b t) =
      (-(m.g.M * w * Real.sin (w * t)) + (m.g.D + a) * Real.cos (w * t) +
        b * Real.sin (w * t)) * Real.cos (w * t) := by
  simp [Port.System.supply, Linear.Plant.system, plant, orbitInput, orbit, dotProduct,
    Fin.sum_univ_three]

/-- The energy supplied over one period `T`, `w T = 2π` (`r w = 1`):
`∫₀ᵀ (−M w sin + (D + a) cos + b sin) cos = (D + a) T/2`. -/
@[tmio T, powerlib_foundation] private theorem integral_orbit_supply (M D a b : ℝ) {w r T : ℝ}
    (hr : r * w = 1) (hwT : w * T = 2 * Real.pi) :
    ∫ t in (0 : ℝ)..T, (-(M * w * Real.sin (w * t)) + (D + a) * Real.cos (w * t) +
      b * Real.sin (w * t)) * Real.cos (w * t) = (D + a) * (T / 2) := by
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt
      (fun t => (b - M * w) * (Real.sin (w * t) * Real.sin (w * t)) * r / 2 +
        (D + a) * (t / 2 + Real.sin (w * t) * Real.cos (w * t) * r / 2))
      ((-(M * w * Real.sin (w * t)) + (D + a) * Real.cos (w * t) +
        b * Real.sin (w * t)) * Real.cos (w * t)) t := by
    intro t _
    have hlin : HasDerivAt (fun s => w * s) w t := by
      simpa using (hasDerivAt_id t).const_mul w
    have hs := (Real.hasDerivAt_sin _).comp t hlin
    have hc := (Real.hasDerivAt_cos _).comp t hlin
    have h1 := (((hs.mul hs).const_mul (b - M * w)).mul_const r).div_const 2
    have h2 := (((hasDerivAt_id t).div_const 2).add
      (((hs.mul hc).mul_const r).div_const 2)).const_mul (D + a)
    refine (h1.add h2).congr_deriv ?_
    have hsc := Real.sin_sq_add_cos_sq (w * t)
    simp only [Function.comp_apply]
    linear_combination ((b - M * w) * Real.sin (w * t) * Real.cos (w * t) +
      (D + a) * (Real.cos (w * t) ^ 2 - Real.sin (w * t) ^ 2) / 2) * hr - ((D + a) / 2) * hsc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) 0 T)]
  simp [hwT]

/-- A frequency below the passive band: with `D ≥ 0`, `ω_c > 0`, `D ω_c < K` some `w > 0` has
`D (w² + ω_c²) < ω_c K`. -/
@[tmio T, powerlib_foundation] private theorem exists_frequency {D ωc K : ℝ} (hD : 0 ≤ D)
    (hω : 0 < ωc) (hKD : D * ωc < K) : ∃ w : ℝ, 0 < w ∧ D * (w ^ 2 + ωc ^ 2) < ωc * K := by
  have hc : 0 < ωc * K - D * ωc ^ 2 := by nlinarith
  have hden : 0 < ωc * K - D * ωc ^ 2 + D + 1 := by linarith
  refine ⟨(ωc * K - D * ωc ^ 2) / (ωc * K - D * ωc ^ 2 + D + 1), div_pos hc hden, ?_⟩
  have key : D * ((ωc * K - D * ωc ^ 2) / (ωc * K - D * ωc ^ 2 + D + 1)) ^ 2 <
      ωc * K - D * ωc ^ 2 := by
    rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
    have : D * (ωc * K - D * ωc ^ 2) < (ωc * K - D * ωc ^ 2 + D + 1) ^ 2 := by
      nlinarith [mul_nonneg hD hc.le]
    nlinarith
  nlinarith

/-- **The linearized VSM + filter port is not passive when the filter is mismatched**,
`D ω_c < K` (with `M ≠ 0`, `D ≥ 0`, `ω_c > 0`). At a frequency `w > 0` with
`D (w² + ω_c²) < ω_c K` (where `Re(1/G(jw)) = D − ω_c K/(w² + ω_c²) < 0`) the input
`u = M Δω̇ + D Δω + ΔP_f` holds the periodic motion
`(sin(w t)/w, cos(w t), a cos(w t) + b sin(w t))`, `a = −ω_c K/(w² + ω_c²)`, `b = −ω_c a/w`;
over one period `T = 2π/w` it returns to its initial state and the supplied energy is
`(D + a) T/2 < 0`, so no storage satisfies the dissipation inequality. -/
@[tmio TM, powerlib_domain] theorem linear_not_mem_den_passive (m : VSMLPF.Model)
    (hM : m.g.M ≠ 0) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hKD : m.g.D * m.g.ωc < m.K) :
    connection% (m ∉ linearFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% linearFamily_isLinear.mem_den_passive_iff)]
  rintro ⟨V, -, hV⟩
  obtain ⟨w, hw0, hDw⟩ := exists_frequency hD hω hKD
  have hwc : 0 < w ^ 2 + m.g.ωc ^ 2 := by positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a * (w ^ 2 + m.g.ωc ^ 2) = -(m.g.ωc * m.K) :=
    ⟨_, div_mul_cancel₀ _ hwc.ne'⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r * w = 1 := ⟨w⁻¹, inv_mul_cancel₀ hw0.ne'⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b * w = -(m.g.ωc * a) := ⟨_, div_mul_cancel₀ _ hw0.ne'⟩
  have hDa : m.g.D + a < 0 := by
    have : (m.g.D + a) * (w ^ 2 + m.g.ωc ^ 2) < 0 := by nlinarith
    by_contra hge
    push Not at hge
    nlinarith
  obtain ⟨T, hT, hwT⟩ : ∃ T : ℝ, 0 < T ∧ w * T = 2 * Real.pi :=
    ⟨2 * Real.pi / w, by positivity, by field_simp⟩
  have htraj : (plant m).system.IsTrajectoryOn (orbitInput m w a b) (orbit w r a b) 0 T := by
    intro t _
    change HasDerivWithinAt (orbit w r a b)
      ((plant m).system.field (orbit w r a b t) (orbitInput m w a b t)) _ t
    rw [orbit_field m hM hr hb ha t]
    exact (orbit_hasDerivAt w r a b t).hasDerivWithinAt
  have hsupply : (fun t => (plant m).system.supply (orbit w r a b t) (orbitInput m w a b t)) =
      fun t => (-(m.g.M * w * Real.sin (w * t)) + (m.g.D + a) * Real.cos (w * t) +
        b * Real.sin (w * t)) * Real.cos (w * t) :=
    funext (orbit_supply m w r a b)
  have hint : IntervalIntegrable
      (fun t => (plant m).system.supply (orbit w r a b t) (orbitInput m w a b t))
      MeasureTheory.volume 0 T := by
    rw [hsupply]
    exact (by fun_prop : Continuous _).intervalIntegrable 0 T
  have h := hV _ _ 0 T hT.le htraj hint
  rw [hsupply, integral_orbit_supply _ _ _ _ hr hwT, orbit_period hwT, sub_self] at h
  nlinarith

/-- **Passivity of the linearized VSM + filter port**: within positive `M, D, ω_c` and a positive
synchronizing coefficient, the loop is passive exactly when the filter is matched,
`K ≤ D ω_c`. -/
@[tmio TM, powerlib_domain] theorem linear_mem_den_passive_iff (m : VSMLPF.Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hK : 0 < m.K) :
    connection% (m ∈ linearFamily.den .passive ↔ m.K ≤ m.g.D * m.g.ωc) := by
  have hp := linear_mem_den_passive m hM hD.le hω hK
  have hn := linear_not_mem_den_passive m hM.ne' hD.le hω
  unfold powerlib.TMIO.Statement at hp hn ⊢
  exact ⟨fun h => not_lt.mp fun hlt => hn hlt h, hp⟩

/-- **The passivity translation is exact within positive `M, D, ω_c` and `K > 0`**
(`linear_mem_den_passive_iff`). -/
@[tmio TM, powerlib_domain] theorem linear_exactUnder_passive :
    connection% (linearFamily.ExactUnder {.physical, .synchronizing} .passive) := by
  unfold powerlib.TMIO.Statement
  refine (connection_proof% Spectral.exactUnder_iff_forall).mpr fun m hm => ?_
  rw [(connection_proof% TMIO.mem_realize)] at hm
  obtain ⟨hM, hD, hω⟩ : Meets m .physical := hm .physical (by simp)
  have hK : Meets m .synchronizing := hm .synchronizing (by simp)
  have h := linear_mem_den_passive_iff m hM hD hω hK
  unfold powerlib.TMIO.Statement at h
  rw [h, (connection_proof% TMIO.mem_realize)]
  change (∀ q ∈ ({.physical, .synchronizing, .matched} : Set Requirement), Meets m q) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => h.2.2, fun h => ⟨⟨hM, hD, hω⟩, hK, h⟩⟩

/-- Every translation of the linearized VSM + filter port family is sound. -/
@[tmio TM, powerlib_domain] theorem linear_chain_le_semantics :
    connection% (∀ P, linearFamily.chain P ≤ linearFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine (connection_proof% Family.chain_le_semantics_iff).mpr fun s => ?_
  intro m hm
  rw [(connection_proof% TMIO.mem_realize)] at hm
  rcases s with P | _ | E
  · have h1 : Meets m .matched := hm .matched (Set.mem_univ _)
    have h2 : Meets m .mismatched := hm .mismatched (Set.mem_univ _)
    exact absurd h1 (not_le.mpr h2)
  · obtain ⟨hM, hD, hω⟩ : Meets m .physical := hm .physical (by simp [linearFamily, translate])
    have h := linear_mem_den_passive m hM hD.le hω
      (hm .synchronizing (by simp [linearFamily, translate]))
      (hm .matched (by simp [linearFamily, translate]))
    unfold powerlib.TMIO.Statement at h
    exact h
  · rw [(connection_proof% linearFamily_isLinear.den_envelope)]
    trivial

/-- The discretizations of the linearized VSM + filter port: a model and a step `h > 0`. -/
abbrev LinearStep := Numerics.EulerStep VSMLPF.Model

/-- The explicit Euler discretization family of the linearized VSM + filter port. -/
def linearEulerFamily : Family LinearStep Requirement 3 1 :=
  Numerics.eulerPortFamily linearFamily (fun m => (plant m).system) Numerics.EulerStep.design
    Numerics.EulerStep.h

/-- The implicit midpoint discretization family of the linearized VSM + filter port. -/
def linearMidpointFamily : Family LinearStep Requirement 3 1 :=
  Numerics.midpointPortFamily linearFamily plant Numerics.EulerStep.design Numerics.EulerStep.h

@[tmio M, powerlib_domain] private theorem plant_C_ne_zero (m : VSMLPF.Model) :
    (plant m).C ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [plant] at this

/-- **No explicit Euler discretization of the linearized VSM + filter port is passive**, whatever
its step and storage (`Numerics.eulerPortFamily_not_mem_den_passive_linear`: `D = 0`,
`C ≠ 0`). -/
@[tmio TM, powerlib_domain] theorem linearEuler_not_mem_den_passive :
    connection% (∀ (m : VSMLPF.Model) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : LinearStep) ∉ linearEulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro m h hh
  exact (connection_proof% Numerics.eulerPortFamily_not_mem_den_passive_linear
    (F := linearFamily) (design := Numerics.EulerStep.design) (step := Numerics.EulerStep.h)
    (y := (⟨m, h, hh⟩ : LinearStep)) hh rfl (plant_C_ne_zero m))

/-- The midpoint step of the filter plant is well posed:
`det(I − c A) = 1 + c (D/M + ω_c) + c² D ω_c/M + c³ ω_c K/M > 0`, `c = h/2 ≥ 0`. -/
@[tmio M, powerlib_domain] private theorem isUnit_det_midpoint (m : VSMLPF.Model) (hM : 0 < m.g.M)
    (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hK : 0 ≤ m.K) {h : ℝ} (hh : 0 ≤ h) :
    IsUnit (1 - (h / 2) • (plant m).A).det := by
  have e : (1 - (h / 2) • (plant m).A).det = 1 + h / 2 * (m.g.D / m.g.M + m.g.ωc) +
      (h / 2) ^ 2 * (m.g.D * m.g.ωc / m.g.M) + (h / 2) ^ 3 * (m.g.ωc * m.K / m.g.M) := by
    simp [plant, VSMLPF.jacobian, VSMLPF.Model.K, Matrix.det_fin_three]
    field_simp
    ring
  rw [isUnit_iff_ne_zero, e]
  have : 0 ≤ h / 2 * (m.g.D / m.g.M + m.g.ωc) := by positivity
  have : 0 ≤ (h / 2) ^ 2 * (m.g.D * m.g.ωc / m.g.M) := by positivity
  have : 0 ≤ (h / 2) ^ 3 * (m.g.ωc * m.K / m.g.M) := by positivity
  linarith

/-- **The implicit midpoint discretizations of the matched linearized VSM + filter port are
passive**, at every step, with the continuous storage (`Numerics.midpointPortFamily_mem_den_passive`
with the certificate of `linear_mem_den_passive`). -/
@[tmio TM, powerlib_domain] theorem linearMidpoint_mem_den_passive (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hK : 0 < m.K)
    (hKD : m.K ≤ m.g.D * m.g.ωc) (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearMidpointFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  exact (connection_proof% Numerics.midpointPortFamily_mem_den_passive (F := linearFamily)
    (plant := plant) (design := Numerics.EulerStep.design) (step := Numerics.EulerStep.h)
    (y := (⟨m, h, hh⟩ : LinearStep)) (kyp m hM hD hω hK hKD) hh.le
    (isUnit_det_midpoint m hM hD hω hK.le hh.le))

/-! ### The mismatched filter: no midpoint discretization is passive -/

/-- The phasor of the test motion of `linear_not_mem_den_passive` at the frequency `w`: the state
`X_r = (0, 1, a)`, `X_i = (−r, 0, −b)` and input `U_r = D + a`, `U_i = M w − b`, with `r w = 1`,
`b w = −ω_c a`, `a (w² + ω_c²) = −ω_c K`, solve `A X + B U = i w X`. -/
@[tmio M, powerlib_domain] private theorem plant_phasor (m : VSMLPF.Model) (hM : m.g.M ≠ 0)
    {w r a b : ℝ} (hr : r * w = 1) (hb : b * w = -(m.g.ωc * a))
    (ha : a * (w ^ 2 + m.g.ωc ^ 2) = -(m.g.ωc * m.K)) :
    (plant m).A *ᵥ ![0, 1, a] + (plant m).B *ᵥ ![m.g.D + a] = (-w) • ![-r, 0, -b] ∧
      (plant m).A *ᵥ ![-r, 0, -b] + (plant m).B *ᵥ ![m.g.M * w - b] = w • ![0, 1, a] := by
  have hK : m.g.K0 * Real.cos m.δ = m.K := rfl
  constructor <;> ext i <;> fin_cases i <;>
    simp [plant, VSMLPF.jacobian, hK]
  · linear_combination -hr
  · field_simp
    ring
  · linear_combination -hb
  · field_simp
    ring
  · linear_combination (w * a - m.g.ωc * b) * hr + m.g.ωc * r * hb - r * ha

/-- **No midpoint discretization of the mismatched linearized VSM + filter port is passive**,
`D ω_c < K` (with `M > 0`, `D ≥ 0`, `ω_c > 0`), whatever the step `h > 0` and the storage. A
discrete frequency `θ = 2π/N` whose bilinear image `w = 2 sin θ/(h (1 + cos θ))` lies in the
band `D (w² + ω_c²) < ω_c K` exists (`Numerics.exists_periodic_frequency`: the band contains
`w = 0`), and the plant's phasor at `w` of `linear_not_mem_den_passive`, whose mean supplied
power is `D + a = D − ω_c K/(w² + ω_c²) < 0`, refutes passivity of the midpoint discretization
(`Numerics.midpointSystem_not_passive_of_phasor`). -/
@[tmio TM, powerlib_domain] theorem linearMidpoint_not_mem_den_passive (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hKD : m.g.D * m.g.ωc < m.K) (h : ℝ)
    (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearMidpointFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.midpointSystem (plant m) h).Passive
  have hK : 0 < m.K := lt_of_le_of_lt (mul_nonneg hD hω.le) hKD
  have hcont : ContinuousAt (fun θ => m.g.D * ((2 * Real.sin θ / (h * (1 + Real.cos θ))) ^ 2 +
      m.g.ωc ^ 2) - m.g.ωc * m.K) 0 := by
    have hden : h * (1 + Real.cos 0) ≠ 0 := by rw [Real.cos_zero]; positivity
    exact (continuousAt_const.mul ((((by fun_prop : ContinuousAt
      (fun θ => 2 * Real.sin θ) 0).div (by fun_prop) hden).pow 2).add continuousAt_const)).sub
      continuousAt_const
  obtain ⟨θ, N, hN, hper, hsin, hθ⟩ := Numerics.exists_periodic_frequency hcont (by
    simp only [Real.sin_zero, mul_zero, zero_div]
    nlinarith)
  have hc : 0 < 1 + Real.cos θ := by
    rcases (Real.neg_one_le_cos θ).lt_or_eq with h1 | h1
    · linarith
    · have := Real.sin_sq_add_cos_sq θ
      rw [← h1] at this
      nlinarith
  set w := 2 * Real.sin θ / (h * (1 + Real.cos θ)) with hwdef
  have hw0 : 0 < w := by positivity
  have hwθ : h * w * (1 + Real.cos θ) = 2 * Real.sin θ := by
    rw [hwdef]
    field_simp
  have hDw : m.g.D * (w ^ 2 + m.g.ωc ^ 2) < m.g.ωc * m.K := by linarith
  have hwc : 0 < w ^ 2 + m.g.ωc ^ 2 := by positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a * (w ^ 2 + m.g.ωc ^ 2) = -(m.g.ωc * m.K) :=
    ⟨_, div_mul_cancel₀ _ hwc.ne'⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r * w = 1 := ⟨w⁻¹, inv_mul_cancel₀ hw0.ne'⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b * w = -(m.g.ωc * a) := ⟨_, div_mul_cancel₀ _ hw0.ne'⟩
  have hDa : m.g.D + a < 0 := by
    have : (m.g.D + a) * (w ^ 2 + m.g.ωc ^ 2) < 0 := by nlinarith
    by_contra hge
    push Not at hge
    nlinarith
  obtain ⟨hr', hi'⟩ := plant_phasor m hM.ne' hr hb ha
  refine Numerics.midpointSystem_not_passive_of_phasor (plant m) hh
    (isUnit_det_midpoint m hM hD hω hK.le hh.le) hN hper hsin.ne' hwθ hr' hi' ?_
  simpa [plant, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hDa

/-- **Passivity of the midpoint discretizations of the linearized VSM + filter port**: within
positive `M, D, ω_c` and `K > 0`, a midpoint discretization with any step `h > 0` is passive
exactly when the filter is matched, `K ≤ D ω_c` — exactly when the continuous loop is
(`linear_mem_den_passive_iff`). -/
@[tmio TM, powerlib_domain] theorem linearMidpoint_mem_den_passive_iff (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearMidpointFamily.den .passive ↔
      m.K ≤ m.g.D * m.g.ωc) := by
  have hp := linearMidpoint_mem_den_passive m hM hD.le hω hK
  have hn := linearMidpoint_not_mem_den_passive m hM hD.le hω
  unfold powerlib.TMIO.Statement at hp hn ⊢
  exact ⟨fun hm => not_lt.mp fun hlt => hn hlt h hh hm, fun hle => hp hle h hh⟩

/-- The implicit midpoint realization of the linearized VSM + filter port: every discretization
realizes its model. -/
def linearMidpoint : Implementation VSMLPF.Model Requirement LinearStep Requirement 3 1 3 1 :=
  Numerics.midpointPorts linearFamily plant Numerics.EulerStep.design Numerics.EulerStep.h

/-- The requirements `physical` and `synchronizing` of a discretization's model. -/
@[tmio M, powerlib_domain] private theorem meets_of_realize {y : LinearStep}
    (hy : y ∈ TMIO.realize (fun y q => Meets (Numerics.EulerStep.design y) q)
      {.physical, .synchronizing}) :
    (0 < y.design.g.M ∧ 0 < y.design.g.D ∧ 0 < y.design.g.ωc) ∧ 0 < y.design.K := by
  rw [(connection_proof% TMIO.mem_realize)] at hy
  exact ⟨hy .physical (by simp), hy .synchronizing (by simp)⟩

/-- **The midpoint realization of passivity is exact within positive `M, D, ω_c` and `K > 0`**:
a discretization is passive, at any step, exactly when its model is
(`linearMidpoint_mem_den_passive_iff`, `linear_mem_den_passive_iff`). -/
@[tmio MI, powerlib_domain] theorem linearMidpoint_realizationExactUnder_passive :
    connection% (linearMidpoint.RealizationExactUnder {.physical, .synchronizing} .passive) := by
  unfold powerlib.TMIO.Statement
  refine (connection_proof% Implementation.realizationExactUnder_of_design
    (I := linearMidpoint) (design := Numerics.EulerStep.design) rfl ?_)
  ext y
  constructor
  · rintro ⟨hy, hΔ⟩
    obtain ⟨⟨hM, hD, hω⟩, hK⟩ := meets_of_realize hΔ
    have hi := linearMidpoint_mem_den_passive_iff y.design hM hD hω hK y.h y.pos
    have hc := linear_mem_den_passive_iff y.design hM hD hω hK
    unfold powerlib.TMIO.Statement at hi hc
    exact ⟨hc.mpr (hi.mp hy), hΔ⟩
  · rintro ⟨hy, hΔ⟩
    obtain ⟨⟨hM, hD, hω⟩, hK⟩ := meets_of_realize hΔ
    have hi := linearMidpoint_mem_den_passive_iff y.design hM hD hω hK y.h y.pos
    have hc := linear_mem_den_passive_iff y.design hM hD hω hK
    unfold powerlib.TMIO.Statement at hi hc
    exact ⟨hi.mpr (hc.mp hy), hΔ⟩

/-! ### Backward Euler: passivity preserved, and created by the step -/

/-- The backward Euler discretization family of the linearized VSM + filter port. -/
def linearBackwardEulerFamily : Family LinearStep Requirement 3 1 :=
  Numerics.backwardEulerPortFamily linearFamily plant Numerics.EulerStep.design
    Numerics.EulerStep.h

/-- The backward Euler realization of the linearized VSM + filter port. -/
def linearBackwardEuler :
    Implementation VSMLPF.Model Requirement LinearStep Requirement 3 1 3 1 :=
  Numerics.backwardEulerPorts linearFamily plant Numerics.EulerStep.design Numerics.EulerStep.h

/-- The backward Euler step of the filter plant is well posed for `h ≥ 0`, `K ≥ 0`
(`isUnit_det_midpoint` at the step `2 h`). -/
@[tmio M, powerlib_domain] private theorem isUnit_det_backward (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hK : 0 ≤ m.K) {h : ℝ} (hh : 0 ≤ h) :
    IsUnit (1 - h • (plant m).A).det := by
  have hw := isUnit_det_midpoint m hM hD hω hK (h := 2 * h) (by positivity)
  rwa [show 2 * h / 2 = h by ring] at hw

/-- The step-dependent storage coefficient
`b_h = (2 D ω_c (2 + h ω_c) + K (h² ω_c² − 2)) / (2 K²)` of backward Euler. -/
private def βBE (m : VSMLPF.Model) (h : ℝ) : ℝ :=
  (2 * m.g.D * m.g.ωc * (2 + h * m.g.ωc) + m.K * ((h * m.g.ωc) ^ 2 - 2)) / (2 * m.K ^ 2)

/-- **The backward Euler discretizations of the linearized VSM + filter port are passive when
`K (2 − h ω_c) ≤ 2 D ω_c`**, i.e. `h ≥ (2/ω_c)(1 − D ω_c/K)` (with `M > 0`, `D ≥ 0`,
`ω_c > 0`, `K > 0`, `h > 0`), with the storage `½ K Δδ² + ½ M Δω² + ½ b_h (ΔP_f − K Δδ)²`
(`βBE`). The step-dependent dissipation inequality of `Numerics.backwardEulerSystem_passiveWith_of`
reduces to the quadratic form
`(D + h K/2 + h b K²/2) Δω² + (1 + b K (1 + h ω_c)) Δω ξ + b ω_c (1 + h ω_c/2) ξ² ≥ 0`,
`ξ = ΔP_f − K Δδ`, whose discriminant condition is `−K² b² + L b − 1 ≥ 0`,
`L = 2 D ω_c (2 + h ω_c) + K (h² ω_c² − 2)`; at `b = L/(2K²)` it is `L ≥ 2 K`, that is
`(2 + h ω_c)(2 D ω_c + K (h ω_c − 2)) ≥ 0`. For `K ≤ D ω_c` this holds at every step; for
`K > D ω_c` the continuous loop is not passive (`linear_not_mem_den_passive`) and the large steps
are. -/
@[tmio TM, powerlib_domain] theorem linearBackwardEuler_mem_den_passive (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h)
    (hKh : m.K * (2 - h * m.g.ωc) ≤ 2 * m.g.D * m.g.ωc) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearBackwardEulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change (Numerics.backwardEulerSystem (plant m) h).Passive
  set b := βBE m h with hbdef
  set L := 2 * m.g.D * m.g.ωc * (2 + h * m.g.ωc) + m.K * ((h * m.g.ωc) ^ 2 - 2) with hL
  have hK2 : 0 < m.K ^ 2 := by positivity
  have hb : b * (2 * m.K ^ 2) = L := by
    rw [hbdef, βBE, div_mul_cancel₀ _ (by positivity), hL]
  have hL2 : 2 * m.K ≤ L := by
    have : 0 ≤ (2 + h * m.g.ωc) * (2 * m.g.D * m.g.ωc + m.K * (h * m.g.ωc - 2)) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hb0 : 0 ≤ b := by
    have : 0 ≤ b * (2 * m.K ^ 2) := by rw [hb]; linarith
    exact nonneg_of_mul_nonneg_left this (by positivity)
  refine ⟨_, Numerics.backwardEulerSystem_passiveWith_of (storageMatrix_symm m b) (fun x => ?_)
    (storage_output m b hM.ne') (fun u => by simp [plant]) hh.le
    (isUnit_det_backward m hM hD hω hK.le hh.le) (fun ξ u => ?_)⟩
  · rw [storage_quadratic]
    nlinarith [mul_nonneg hK.le (sq_nonneg (x 0)), mul_nonneg hM.le (sq_nonneg (x 1)),
      mul_nonneg hb0 (sq_nonneg (x 2 - m.K * x 0))]
  · rw [storage_rate m b hM.ne', storage_quadratic]
    have hK0 : m.g.K0 * Real.cos m.δ = m.K := rfl
    set v := (plant m).A *ᵥ ξ + (plant m).B *ᵥ u
    have hv0 : v 0 = ξ 1 := by
      simp [v, plant, VSMLPF.jacobian, dotProduct, Fin.sum_univ_three]
    have hv2 : v 2 - m.K * v 0 = -(m.g.ωc * (ξ 2 - m.K * ξ 0) + m.K * ξ 1) := by
      simp [v, plant, VSMLPF.jacobian, dotProduct, Fin.sum_univ_three, hK0]
      ring
    rw [hv2, hv0]
    set x1 := ξ 1
    set η := ξ 2 - m.K * ξ 0
    set A := m.g.D + h * m.K / 2 + h * b * m.K ^ 2 / 2
    set C := b * m.g.ωc * (1 + h * m.g.ωc / 2)
    set B := 1 + b * m.K * (1 + h * m.g.ωc)
    have hA : 0 < A := by positivity
    have hdisc : 0 ≤ 4 * A * C - B ^ 2 := by
      have e : 4 * A * C - B ^ 2 = -(m.K ^ 2 * b ^ 2) + L * b - 1 := by
        simp only [A, B, C, hL]
        ring
      have e2 : (-(m.K ^ 2 * b ^ 2) + L * b - 1) * (4 * m.K ^ 2) =
          (L - 2 * m.K) * (L + 2 * m.K) := by
        rw [← hb]
        ring
      have h5 : 0 ≤ (L - 2 * m.K) * (L + 2 * m.K) := mul_nonneg (by linarith) (by linarith)
      rw [e]
      rw [← e2] at h5
      exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h5
    have hQ : 0 ≤ A * x1 ^ 2 + B * x1 * η + C * η ^ 2 := by
      have key : 4 * A * (A * x1 ^ 2 + B * x1 * η + C * η ^ 2) =
          (2 * A * x1 + B * η) ^ 2 + (4 * A * C - B ^ 2) * η ^ 2 := by ring
      have : 0 ≤ 4 * A * (A * x1 ^ 2 + B * x1 * η + C * η ^ 2) := by
        rw [key]
        exact add_nonneg (sq_nonneg _) (mul_nonneg hdisc (sq_nonneg η))
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
    have hv : 0 ≤ h / 2 * (m.g.M * v 1 ^ 2) := by positivity
    have : h / 2 * (m.K * x1 ^ 2 + m.g.M * v 1 ^ 2 + b * (-(m.g.ωc * η + m.K * x1)) ^ 2) +
        (m.g.D * x1 ^ 2 + (1 + b * m.K) * x1 * η + b * m.g.ωc * η ^ 2) =
        (A * x1 ^ 2 + B * x1 * η + C * η ^ 2) + h / 2 * (m.g.M * v 1 ^ 2) := by
      simp only [A, B, C]
      ring
    linarith

/-- **The phasor of the filter plant at a complex frequency** `s = σ + i ω`: the output phasor
`Δω = 1`, the angle `1/s = p + i q`, the filter `ω_c K/(s (s + ω_c)) = a + i b` (in real form,
`h1`–`h4`), the input `M s + D + a + i b` solve `A X + B U = s X`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem plant_phasor_complex (m : VSMLPF.Model)
    (hM : m.g.M ≠ 0) {σ ω p q a b : ℝ} (h1 : σ * p - ω * q = 1) (h2 : ω * p + σ * q = 0)
    (h3 : (σ + m.g.ωc) * a - ω * b = m.g.ωc * m.K * p)
    (h4 : ω * a + (σ + m.g.ωc) * b = m.g.ωc * m.K * q) :
    (plant m).A *ᵥ ![p, 1, a] + (plant m).B *ᵥ ![m.g.M * σ + m.g.D + a] =
        σ • ![p, 1, a] - ω • ![q, 0, b] ∧
      (plant m).A *ᵥ ![q, 0, b] + (plant m).B *ᵥ ![m.g.M * ω + b] =
        ω • ![p, 1, a] + σ • ![q, 0, b] := by
  have hK : m.g.K0 * Real.cos m.δ = m.K := rfl
  constructor <;> ext i <;> fin_cases i <;>
    simp [plant, VSMLPF.jacobian, hK]
  · linear_combination -h1
  · field_simp
    ring
  · linear_combination -h3
  · linear_combination -h2
  · field_simp
    ring
  · linear_combination -h4

/-- **No backward Euler discretization of the linearized VSM + filter port with
`K (2 − h ω_c) > 2 D ω_c` is passive** (with `M > 0`, `D ≥ 0`, `ω_c > 0`, `K > 0`, `h > 0`),
whatever the storage. At the discrete frequency `θ` the end-of-step phasor is the plant's phasor
at `s = (1 − e^{−iθ})/h`; with the output phasor `Δω = 1` its mean supplied power is
`M σ + D + ω_c K (h ω_c − 2 cos θ)/(2 |s + ω_c|²)`, `σ = (1 − cos θ)/h`, continuous in `θ`, and at
`θ = 0` equal to `D + K (h ω_c − 2)/(2 ω_c) < 0`; a frequency `θ = 2π/N` near zero keeps it
negative (`Numerics.exists_periodic_frequency`,
`Numerics.backwardEulerSystem_not_passive_of_phasor`). -/
@[tmio TM, powerlib_domain] theorem linearBackwardEuler_not_mem_den_passive (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h)
    (hKh : 2 * m.g.D * m.g.ωc < m.K * (2 - h * m.g.ωc)) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearBackwardEulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.backwardEulerSystem (plant m) h).Passive
  set f : ℝ → ℝ := fun θ => m.g.M * ((1 - Real.cos θ) / h) + m.g.D +
    m.g.ωc * m.K * (h * m.g.ωc - 2 * Real.cos θ) /
      (2 * (((1 - Real.cos θ) / h + m.g.ωc) ^ 2 + (Real.sin θ / h) ^ 2)) with hfdef
  have hden0 : 2 * (((1 - Real.cos 0) / h + m.g.ωc) ^ 2 + (Real.sin 0 / h) ^ 2) ≠ 0 := by
    simp only [Real.cos_zero, Real.sin_zero, sub_self, zero_div, zero_add]
    positivity
  have hcont : ContinuousAt f 0 :=
    ((continuousAt_const.mul (by fun_prop)).add continuousAt_const).add
      ((by fun_prop : ContinuousAt (fun θ => m.g.ωc * m.K * (h * m.g.ωc - 2 * Real.cos θ)) 0).div
        (by fun_prop) hden0)
  have hf0 : f 0 < 0 := by
    simp only [hfdef, Real.cos_zero, Real.sin_zero, sub_self, zero_div, mul_zero, zero_add]
    have e : m.g.ωc * m.K * (h * m.g.ωc - 2 * 1) / (2 * (m.g.ωc ^ 2 + 0 ^ 2)) =
        m.K * (h * m.g.ωc - 2) / (2 * m.g.ωc) := by
      field_simp
      ring
    have e' : m.g.D + m.K * (h * m.g.ωc - 2) / (2 * m.g.ωc) =
        (2 * m.g.D * m.g.ωc + m.K * (h * m.g.ωc - 2)) / (2 * m.g.ωc) := by
      field_simp
    rw [e, e']
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  obtain ⟨θ, N, hN, hper, hsin, hθ⟩ := Numerics.exists_periodic_frequency hcont hf0
  set c := Real.cos θ
  set s := Real.sin θ
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  set σ := (1 - c) / h with hσdef
  set ω := s / h with hωdef
  have hσ : h * σ = 1 - c := by rw [hσdef]; field_simp
  have hω' : h * ω = s := by rw [hωdef]; field_simp
  have hσ0 : 0 ≤ σ := div_nonneg (by linarith [Real.cos_le_one θ]) hh.le
  have hω0 : 0 < ω := div_pos hsin hh
  have hS : 0 < σ ^ 2 + ω ^ 2 := by positivity
  have hE : 0 < (σ + m.g.ωc) ^ 2 + ω ^ 2 := by positivity
  set p := σ / (σ ^ 2 + ω ^ 2)
  set q := -ω / (σ ^ 2 + ω ^ 2)
  set a := m.g.ωc * m.K * (p * (σ + m.g.ωc) + q * ω) / ((σ + m.g.ωc) ^ 2 + ω ^ 2)
  set b := m.g.ωc * m.K * (q * (σ + m.g.ωc) - p * ω) / ((σ + m.g.ωc) ^ 2 + ω ^ 2)
  have h1 : σ * p - ω * q = 1 := by simp only [p, q]; field_simp; ring
  have h2 : ω * p + σ * q = 0 := by simp only [p, q]; field_simp; ring
  have h3 : (σ + m.g.ωc) * a - ω * b = m.g.ωc * m.K * p := by
    simp only [a, b]; field_simp; ring
  have h4 : ω * a + (σ + m.g.ωc) * b = m.g.ωc * m.K * q := by
    simp only [a, b]; field_simp; ring
  have ha : a = m.g.ωc * m.K * (h * m.g.ωc - 2 * c) / (2 * ((σ + m.g.ωc) ^ 2 + ω ^ 2)) := by
    have key : 2 * (p * (σ + m.g.ωc) + q * ω) = h * m.g.ωc - 2 * c := by
      have hh2 : h ^ 2 * (2 * (σ * (σ + m.g.ωc) - ω ^ 2) -
          (h * m.g.ωc - 2 * c) * (σ ^ 2 + ω ^ 2)) = 0 := by
        have e1 : h ^ 2 * σ ^ 2 = (1 - c) ^ 2 := by rw [← hσ]; ring
        have e2 : h ^ 2 * ω ^ 2 = s ^ 2 := by rw [← hω']; ring
        have e3 : h * σ * (h * m.g.ωc) = (1 - c) * (h * m.g.ωc) := by rw [hσ]
        linear_combination (2 - (h * m.g.ωc - 2 * c)) * e1 - (2 + (h * m.g.ωc - 2 * c)) * e2 +
          2 * e3 - (2 + (h * m.g.ωc - 2 * c)) * hsc
      have hne : σ ^ 2 + ω ^ 2 ≠ 0 := hS.ne'
      have : 2 * (σ * (σ + m.g.ωc) - ω ^ 2) = (h * m.g.ωc - 2 * c) * (σ ^ 2 + ω ^ 2) := by
        have := (mul_eq_zero.mp hh2).resolve_left (by positivity)
        linarith
      simp only [p, q]
      field_simp
      linear_combination this
    simp only [a]
    rw [← key]
    field_simp
  obtain ⟨hr', hi'⟩ := plant_phasor_complex m hM.ne' h1 h2 h3 h4
  refine Numerics.backwardEulerSystem_not_passive_of_phasor (plant m) hh
    (isUnit_det_backward m hM hD hω hK.le hh.le) hN hper hsin.ne' hσ hω' hr' hi' ?_
  have hfθ : f θ = m.g.M * σ + m.g.D + a := by rw [ha]
  simp [plant, dotProduct]
  linarith

/-- **Passivity of the backward Euler discretizations of the linearized VSM + filter port**:
within `M > 0`, `D ≥ 0`, `ω_c > 0`, `K > 0`, a discretization with step `h > 0` is passive
exactly when `K (2 − h ω_c) ≤ 2 D ω_c`. -/
@[tmio TM, powerlib_domain] theorem linearBackwardEuler_mem_den_passive_iff (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearBackwardEulerFamily.den .passive ↔
      m.K * (2 - h * m.g.ωc) ≤ 2 * m.g.D * m.g.ωc) := by
  have hp := linearBackwardEuler_mem_den_passive m hM hD hω hK h hh
  have hn := linearBackwardEuler_not_mem_den_passive m hM hD hω hK h hh
  unfold powerlib.TMIO.Statement at hp hn ⊢
  exact ⟨fun hm => not_lt.mp fun hlt => hn hlt hm, hp⟩

/-- **Backward Euler preserves passivity of the linearized VSM + filter port**: within positive
`M, D, ω_c` and `K > 0`, a passive model (`K ≤ D ω_c`) has passive backward Euler
discretizations at every step, `K (2 − h ω_c) < 2 K ≤ 2 D ω_c`. -/
@[tmio MI, powerlib_domain] theorem linearBackwardEuler_realizationSoundUnder_passive :
    connection% (linearBackwardEuler.RealizationSoundUnder {.physical, .synchronizing}
      .passive) := by
  unfold powerlib.TMIO.Statement
  rintro y ⟨hy, hΔ⟩
  rw [(connection_proof% Implementation.certify_realizes_of_design (I := linearBackwardEuler)
    (design := Numerics.EulerStep.design) rfl)] at hy
  obtain ⟨⟨hM, hD, hω⟩, hK⟩ := meets_of_realize hΔ
  have hc := linear_mem_den_passive_iff y.design hM hD hω hK
  unfold powerlib.TMIO.Statement at hc
  have hKD := hc.mp hy
  have hp := linearBackwardEuler_mem_den_passive y.design hM hD.le hω hK y.h y.pos (by
    nlinarith [mul_pos (mul_pos hK y.pos) hω])
  unfold powerlib.TMIO.Statement at hp
  exact hp

/-- A mismatched model, `M = D = ω_c = 1`, `K₀ = 3/2`, `P₀ = 0`, `δ* = 0` (`K = 3/2 > D ω_c`). -/
private def mismatchedModel : VSMLPF.Model := ⟨⟨1, 1, 1, 0, 3 / 2⟩, 0⟩

/-- **Backward Euler creates passivity: its realization of passivity is not complete** within
positive `M, D, ω_c` and `K > 0`. The mismatched model `mismatchedModel` is not passive
(`linear_not_mem_den_passive`, `K = 3/2 > D ω_c = 1`), and its discretization with the step
`h = 1` is (`K (2 − h ω_c) = 3/2 ≤ 2 D ω_c`, `linearBackwardEuler_mem_den_passive`): a spurious
passivity window `h ≥ (2/ω_c)(1 − D ω_c/K) = 2/3`. -/
@[tmio MI, powerlib_domain] theorem not_linearBackwardEuler_realizationCompleteUnder_passive :
    connection% (¬ linearBackwardEuler.RealizationCompleteUnder {.physical, .synchronizing}
      .passive) := by
  have hK : mismatchedModel.K = 3 / 2 := by simp [mismatchedModel, VSMLPF.Model.K]
  have hp := linearBackwardEuler_mem_den_passive mismatchedModel (by simp [mismatchedModel])
    (by simp [mismatchedModel]) (by simp [mismatchedModel]) (by rw [hK]; norm_num) 1 one_pos
    (by rw [hK]; simp [mismatchedModel]; norm_num)
  have hn := linear_not_mem_den_passive mismatchedModel (by simp [mismatchedModel])
    (by simp [mismatchedModel]) (by simp [mismatchedModel])
    (by rw [hK]; simp [mismatchedModel]; norm_num)
  unfold powerlib.TMIO.Statement at hp hn ⊢
  refine (connection_proof% Implementation.not_realizationCompleteUnder_of_design
    (I := linearBackwardEuler) (design := Numerics.EulerStep.design)
    (y := (⟨mismatchedModel, 1, one_pos⟩ : LinearStep)) rfl hp ?_ hn)
  rw [(connection_proof% TMIO.mem_realize)]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · change 0 < mismatchedModel.g.M ∧ 0 < mismatchedModel.g.D ∧ 0 < mismatchedModel.g.ωc
    simp [mismatchedModel]
  · change 0 < mismatchedModel.K
    rw [hK]
    norm_num

end FilterPort

end powerlib.GFM
