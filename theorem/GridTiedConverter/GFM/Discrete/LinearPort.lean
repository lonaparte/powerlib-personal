import theorem.GridTiedConverter.GFM.Discrete.SwingPort
import theorem.GridTiedConverter.GFM.VSMLPF

/-! # Linearized grid-forming port models: passivity, explicit Euler and the implicit midpoint rule

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
the continuous storage at every step whenever the continuous certificate exists.

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
  step length `h`, exact arithmetic, fixed step. Excluded: step-aware Euler outputs, backward
  Euler, the nonlinear discrete gradient, step-size control, delays, PWM, inner loops, PLL, line
  dynamics.

Source: work-sync GFM study note t9 (scratchpad `gfm/t9-discrete/REPORT-coord.md`, (b) and (c):
2-state storage `diag(K, M)`; 3-state passive iff `K ≤ D ω_c` with the storage above, from the
real part `Re(1/G(jw)) = D − ω_c K/(w² + ω_c²)`; explicit Euler never passive; implicit midpoint
passive with the continuous storage); `theorem/Numerics/EulerPorts.lean`
(`Numerics.eulerPortFamily_not_mem_den_passive_linear`,
`Numerics.midpointPortFamily_mem_den_passive`), `theorem/Linear/Family.lean`
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
  `FilterPort.system_output_eq`.

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
  `det(I − (h/2) A) > 0`). The converse (`K > D ω_c` ⇒ no midpoint discretization is passive) is
  not proved here.
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

/-- The storage matrix of `½ K Δδ² + ½ M Δω² + ½ β (ΔP_f − K Δδ)²`. -/
private def storageMatrix (m : VSMLPF.Model) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![m.K + β m * m.K ^ 2, 0, -(β m * m.K); 0, m.g.M, 0; -(β m * m.K), 0, β m]

@[tmio M, powerlib_domain] private theorem storageMatrix_symm (m : VSMLPF.Model) :
    (storageMatrix m)ᵀ = storageMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [storageMatrix]

@[tmio M, powerlib_domain] private theorem storage_quadratic (m : VSMLPF.Model) (x : Fin 3 → ℝ) :
    x ⬝ᵥ (storageMatrix m *ᵥ x) =
      m.K * x 0 ^ 2 + m.g.M * x 1 ^ 2 + β m * (x 2 - m.K * x 0) ^ 2 := by
  simp [storageMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- `xᵀ P A x = −(D x₁² + (1 + β K) x₁ ξ + β ω_c ξ²)`, `ξ = x₂ − K x₀`. -/
@[tmio M, powerlib_domain] private theorem storage_rate (m : VSMLPF.Model) (hM : m.g.M ≠ 0)
    (x : Fin 3 → ℝ) :
    x ⬝ᵥ (storageMatrix m *ᵥ ((plant m).A *ᵥ x)) =
      -(m.g.D * x 1 ^ 2 + (1 + β m * m.K) * x 1 * (x 2 - m.K * x 0) +
        β m * m.g.ωc * (x 2 - m.K * x 0) ^ 2) := by
  simp [storageMatrix, plant, VSMLPF.jacobian, VSMLPF.Model.K, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three]
  field_simp
  ring

/-- The KYP certificate of the matched filter: `M > 0`, `D ≥ 0`, `ω_c > 0`, `0 < K ≤ D ω_c`. -/
private def kyp (m : VSMLPF.Model) (hM : 0 < m.g.M) (hD : 0 ≤ m.g.D) (hω : 0 < m.g.ωc)
    (hK : 0 < m.K) (hKD : m.K ≤ m.g.D * m.g.ωc) : Linear.KYP (plant m) where
  P := storageMatrix m
  symmetric := storageMatrix_symm m
  nonneg x := by
    rw [storage_quadratic]
    have hβ : 0 ≤ β m := by
      unfold β
      apply div_nonneg _ (sq_nonneg _)
      nlinarith [mul_nonneg hD hω.le]
    nlinarith [mul_nonneg hK.le (sq_nonneg (x 0)), mul_nonneg hM.le (sq_nonneg (x 1)),
      mul_nonneg hβ (sq_nonneg (x 2 - m.K * x 0))]
  dissipation x := by
    rw [Linear.quadratic_sym (storageMatrix_symm m), storage_rate m hM.ne']
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
  output := by
    have hM' := hM.ne'
    ext i j
    fin_cases i
    fin_cases j <;> simp [storageMatrix, plant, Matrix.mul_apply, Fin.sum_univ_three, hM']
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

@[tmio M, powerlib_domain] private theorem orbit_hasDerivAt (w r a b t : ℝ) :
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
@[tmio M, powerlib_domain] private theorem orbit_period {w r a b T : ℝ}
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
@[tmio M, powerlib_domain] private theorem integral_orbit_supply (M D a b : ℝ) {w r T : ℝ}
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
@[tmio M, powerlib_domain] private theorem exists_frequency {D ωc K : ℝ} (hD : 0 ≤ D)
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

end FilterPort

end powerlib.GFM
