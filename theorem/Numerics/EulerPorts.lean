import theorem.Numerics.EulerRealization
import theorem.Numerics.DiscreteGradient
import theorem.Map.LinearReading
import theorem.Linear.Family
import theorem.TMIO.ClaimElab

/-! # The explicit Euler implementation of a model with ports: a realization (foundation)

A family of continuous-time port systems `ẋ = f(x, u)`, `y = h(x, u)` and its implementation by
the explicit Euler method with a step `h`: the discrete-time system with ports
`x⁺ = x + h f(x, u)` (the input held over the step), the same output map and step length `h`
(`eulerSystem`), which realizes the model it is designed from (`Implementation.ofDesign`). The
autonomous template `theorem/Numerics/EulerRealization.lean` covers the families without ports;
this module extends it to inputs. The flow sentences of a port system are read on its zero-input
field (`Sentence.holds`), and the zero-input map of the Euler discretization is the Euler map of
that field (`eulerSystem_zeroInput`), so the flow-sentence laws are those of the autonomous
template applied to the zero-input family (`zeroInputFamily`): realization of local exponential
stability for small steps, model by model with smoothness at the point, and not without a step
constraint. Passivity is different: explicit Euler does not preserve it. The Euler output is the
continuous output, which for a strictly proper model (output independent of the input) does not
see the input of the step, while one step with a large input draws energy without bound; a
nonnegative storage cannot pay for it (`Map.System.not_passive_of_supply_unbounded`). The
integrator `ẋ = u`, `y = x` is passive with storage `x²/2`, and its Euler discretization
`x⁺ = x + h u`, `y = x` is not passive for any storage at any step `h > 0`. The discrete gradient
method of `theorem/Numerics/DiscreteGradient.lean`, whose output `gᵀ ∇̄H(x, x⁺)` sees the step,
does realize passivity (`discreteGradient_passiveWith`). For linear plants `ẋ = Ax + Bu` the
Euler zero-input map is `I + hA`; a multiplier `1 + hλ` inside the unit disk forces `Re λ < 0`
(`isHurwitz_of_forwardEuler_schurStable`), so the realization of the attractive sentences is
complete at every positive step, and with the step threshold exact for small steps.
Scaffold: `theorem/EulerPorts.agda`.

Scope.
* A generic template, not a model. Model layer (M): an arbitrary family `F : Family X Q n p` of
  continuous-time port systems (`Family.IsPort F sys`: every complete system is `sys x`), read
  about the origin; linear families (`Family.IsLinear`, `theorem/Linear/Family.lean`) and
  port-Hamiltonian families (`Family.IsNonlinearPH`, `theorem/PH/Nonlinear.lean`) are families of
  port systems (`IsLinear.isPort`, `IsNonlinearPH.isPort`). Smoothness: the zero-input field
  `(sys x).zeroInput` of class `C¹` near the origin for the model a flow law speaks about.
* Implementation layer (I): an arbitrary type `Y` of implementations with a design model
  `design y` and a step `step y`; the system is `eulerSystem (sys (design y)) (step y)` (discrete
  time, the input held over each step, exact arithmetic, fixed step).
* The realization and denotation laws are connection statements about arbitrary families of
  `Type` (the definitions stay universe polymorphic); static facts (the Euler discretization, the
  integrator, linear algebra) and the passivity of systems are foundation lemmas. The instances
  apply the laws to their families (`IsPort`, `IsLinear`, the public smoothness lemma of the
  zero-input field) and publish what carries their own content — witnesses against soundness,
  passivity witnesses — in the `PortEuler.lean` modules of `theorem/GFL/DCLink/` (the linearized
  cascade), `theorem/Circuits/` (RL branch, LCL filter), `theorem/Synchronous/` (the classical,
  seven-state and 11-state single-machine pH systems) and `theorem/PLL/` (SRF-PLL as a
  port-Hamiltonian system).

Source: `theorem/Numerics/EulerRealization.lean` (`eulerMap`, `eulerFamily`, `euler`,
`euler_sound_small_step_local`, `not_euler_realizationSoundUnder_of_large_step_local`,
`exists_forwardEuler_schurStable`, `exists_forwardEuler_inverse_schurStable`),
`theorem/Numerics/LinearSchemes.lean` (`forwardEuler_schurStable_iff`),
`theorem/Map/LinearReading.lean` (`Map.holdsMap_op_iff_schurStable`),
`theorem/Linear/Family.lean` (`Family.IsLinear.den_hurwitz`), `theorem/Port/Linear.lean` (KYP
certificates), `theorem/Numerics/DiscreteGradient.lean` (`discreteGradient_dissipation`); the port
and map semantics (`theorem/Port/Defs.lean`, `theorem/Map/Defs.lean`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7 and `theory/T-ph.md` §2.5.

Results.
* `eulerSystem s h` (the Euler discretization of a port system), `eulerSystem_zeroInput` (its
  zero-input map is `eulerMap s.zeroInput h`).
* Passivity: `Map.System.not_passive_of_supply_unbounded` (a discrete system that can draw
  unboundedly much energy in one step from some state is not passive); `not_passive_eulerSystem`
  (an output independent of the input and nonzero at some state makes the Euler discretization
  not passive at every step `h > 0`); the integrator `integrator` (`ẋ = u`, `y = x`),
  `integrator_passiveWith` (storage `x²/2`, a KYP certificate) and
  `not_passive_eulerSystem_integrator` (not passive at any step `h > 0`);
  `discreteGradient_passiveWith` (contrast: a discrete system whose steps solve the
  discrete-gradient relation of a pH system and whose output is the discrete-gradient output is
  passive with storage `H`).
* Linear plants: `eulerMap_linear` (`eulerMap (Ax) h` is the linear map of `I + h A`),
  `isHurwitz_of_forwardEuler_schurStable` (a positive step with a Schur stable `I + h A` forces a
  Hurwitz `A`).

Family and connection conclusions.
* `Family.IsPort`; the zero-input family `zeroInputFamily F sys : Family X Q n 0`
  (`zeroInputFamily_isAutonomous`, `den_flow_zeroInputFamily`: same flow denotations); the
  template `eulerPortFamily F sys design step : Family Y Q n p` (requirements and translation of
  the design model) and the realization `eulerPorts F sys design step`
  (`Implementation.ofDesign design`); `eulerPortFamily_den_flow` (its flow denotations are those
  of the autonomous Euler family of the zero-input family) and
  `eulerPorts_realizationSoundUnder_flow_iff` (so are its flow realizations). These and the laws
  below are connection statements over families of `Type`.
* M–I laws for flow sentences, from the autonomous template:
  `eulerPorts_sound_small_step_local` (scaffold `sound-small-step`: a locally exponentially
  stable model whose zero-input field is `C¹` near the origin has a step `h₀ > 0` below which its
  Euler implementations are locally exponentially stable) and
  `not_eulerPorts_realizationSoundUnder_of_large_step_local` (scaffold `not-sound-large-step`,
  `n > 0`: without a step constraint the realization is not sound, given such a model with
  arbitrarily large steps).
* M–I laws for passivity: `eulerPortFamily_not_mem_den_passive` (an Euler
  implementation with a positive step of a model whose output is independent of the input and
  nonzero at some state is not passive, whatever the step);
  `not_eulerPorts_realizationSoundUnder_passive` (so the passivity realization is not sound
  within any requirement context the passive design meets, at any step);
  `not_eulerPorts_realizationSoundUnder_passive_of_integrator` (the integrator, at any positive
  step, is a witness).
* M–I laws for linear families: `eulerPortFamily_den_linear` (the attractive
  sentences and sampled contraction of the Euler implementations denote those with a Schur stable
  `I + h A`); `eulerPorts_realizationCompleteUnder_linear` (completeness of these sentences at
  every positive step, within every context); `eulerPorts_exact_small_step_linear` (every model
  has a step `h₀ > 0` below which its Euler implementations satisfy these sentences exactly when
  it does); `not_eulerPorts_realizationSoundUnder_of_large_step_linear` (`n > 0`: not sound
  without a step constraint, given a Hurwitz model with arbitrarily large steps).
-/

noncomputable section

namespace powerlib

open Matrix LinearSystems TMIO

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Families of port systems -/

namespace Family

variable {X Q : Type*}

/-- Every complete system of the family is the continuous-time port system `sys x`. -/
def IsPort (F : Family X Q n p) (sys : X → Port.System n p) : Prop :=
  ∀ x, F.system x = .continuous (sys x)

/-- A linear family is a family of port systems: the port systems of its plants. -/
@[powerlib_foundation] theorem IsLinear.isPort {F : Family X Q n p}
    {plant : X → Linear.Plant n p} (hF : F.IsLinear plant) :
    F.IsPort fun x => (plant x).system :=
  hF

/-- A port-Hamiltonian family is a family of port systems: the port systems of its pH
systems. -/
@[powerlib_foundation] theorem IsNonlinearPH.isPort {F : Family X Q n p}
    {model : X → PH.NonlinearModel n p} (hF : F.IsNonlinearPH model) :
    F.IsPort fun x => (model x).system :=
  hF

end Family

/-! ## Passivity of discrete-time systems -/

/-- A discrete-time system that can draw unboundedly much energy out of its ports in one step
from some state `x` is not passive: with a nonnegative storage `V`, one step from `x` delivers at
most `V x`. -/
@[powerlib_foundation] theorem Map.System.not_passive_of_supply_unbounded (s : Map.System n p)
    {x : ℝⁿ} (h : ∀ c : ℝ, ∃ u, s.supply x u < c) : ¬ s.Passive := by
  rintro ⟨V, hV0, hV⟩
  obtain ⟨u, hu⟩ := h (-V x)
  linarith [hV x u, hV0 (s.step x u)]

namespace Numerics

/-! ## The Euler discretization of a port system -/

/-- The explicit Euler discretization of a port system with step `h`: the state update
`x⁺ = x + h f(x, u)` with the input held over the step, the same output map, step length `h`. -/
def eulerSystem (s : Port.System n p) (h : ℝ) : Map.System n p :=
  ⟨fun x u => x + h • s.field x u, s.output, h⟩

/-- With the ports at zero the Euler discretization is the Euler map of the zero-input field. -/
@[simp, powerlib_foundation] theorem eulerSystem_zeroInput (s : Port.System n p) (h : ℝ) :
    (eulerSystem s h).zeroInput = eulerMap s.zeroInput h :=
  rfl

/-- **Explicit Euler loses passivity when the output does not see the input.** If at some state
`x` the output of a port system is a nonzero `y` whatever the input, then for every step `h > 0`
its explicit Euler discretization is not passive, for any storage: the input `u = −t y` draws the
energy `h t ‖y‖²` in one step from `x`, without bound in `t`. -/
@[powerlib_foundation] theorem not_passive_eulerSystem (s : Port.System n p) {h : ℝ} (hh : 0 < h)
    {x : ℝⁿ} {y : Fin p → ℝ} (hy : ∀ u, s.output x u = y) (hy0 : y ≠ 0) :
    ¬ (eulerSystem s h).Passive := by
  refine Map.System.not_passive_of_supply_unbounded _ (x := x) fun c => ?_
  have hyy : 0 < y ⬝ᵥ y :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (y i))
      fun h0 => hy0 (dotProduct_self_eq_zero.mp h0.symm)
  refine ⟨(-((|c| + 1) / (h * (y ⬝ᵥ y)))) • y, ?_⟩
  have hne : h * (y ⬝ᵥ y) ≠ 0 := (mul_pos hh hyy).ne'
  have hsupply : (eulerSystem s h).supply x ((-((|c| + 1) / (h * (y ⬝ᵥ y)))) • y) =
      -(|c| + 1) := by
    change h * ((-((|c| + 1) / (h * (y ⬝ᵥ y)))) • y ⬝ᵥ s.output x _) = _
    rw [hy, smul_dotProduct, smul_eq_mul]
    field_simp
  rw [hsupply]
  linarith [neg_abs_le c]

/-! ## The integrator -/

/-- The integrator `ẋ = u`, `y = x`: one state, one port. -/
def integrator : Linear.Plant 1 1 := ⟨0, 1, 1, 0⟩

/-- The KYP certificate `P = 1` of the integrator: its storage is `x²/2`. -/
private def integratorKYP : Linear.KYP integrator where
  P := 1
  symmetric := transpose_one
  nonneg x := by simpa [dotProduct] using mul_self_nonneg (x 0)
  dissipation x := by simp [integrator]
  output := by simp [integrator]
  feedthrough u := by simp [integrator]

/-- **The integrator is passive** with the storage `x²/2`: `d/dt (x²/2) = x u` is the supplied
power. -/
@[powerlib_foundation] theorem integrator_passiveWith :
    integrator.system.PassiveWith fun x => x 0 ^ 2 / 2 := by
  have h : integratorKYP.storage = fun x => x 0 ^ 2 / 2 := by
    funext x
    simp [Linear.KYP.storage, integratorKYP, dotProduct, sq]
  rw [← h]
  exact integratorKYP.passiveWith

/-- **The Euler discretization of the integrator is not passive at any step.** For every step
`h > 0` the system `x⁺ = x + h u`, `y = x` is not passive for any storage
(`not_passive_eulerSystem`: at `x = 1` the output is `1` whatever the input). -/
@[powerlib_foundation] theorem not_passive_eulerSystem_integrator {h : ℝ} (hh : 0 < h) :
    ¬ (eulerSystem integrator.system h).Passive :=
  not_passive_eulerSystem _ hh (x := WithLp.toLp 2 ![1]) (y := ![1])
    (fun u => by
      funext i
      fin_cases i
      simp [integrator, Linear.Plant.system])
    (by simp)

/-! ## Contrast: the discrete gradient realizes passivity -/

/-- **Contrast: the discrete gradient realizes passivity.** A discrete-time system whose every
step solves the discrete-gradient relation `x⁺ − x = T ((J − R) ∇̄H(x, x⁺) + g u)` of a pH system
with constant structure matrices (`J` skew, `R ⪰ 0`), with a nonnegative period `T` and the
discrete-gradient output `y = gᵀ ∇̄H(x, x⁺)`, is passive with the storage `H` when `H ≥ 0`
(`discreteGradient_dissipation`). Its output sees the input through `x⁺`; the explicit Euler
output `gᵀ ∇H(x)` does not, and the Euler discretization is not passive
(`not_passive_eulerSystem`). -/
@[tmio T, powerlib_foundation] theorem discreteGradient_passiveWith (s : Map.System n p)
    {H : (Fin n → ℝ) → ℝ} (G : DiscreteGradient H) {J R : Matrix (Fin n) (Fin n) ℝ}
    (g : Matrix (Fin n) (Fin p) ℝ) (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hH : ∀ z, 0 ≤ H z)
    (hT : 0 ≤ s.period)
    (hstep : ∀ x u, WithLp.ofLp (s.step x u) - WithLp.ofLp x =
      s.period • ((J - R) *ᵥ G.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u)) + g *ᵥ u))
    (hout : ∀ x u, s.output x u = gᵀ *ᵥ G.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u))) :
    s.PassiveWith fun x => H (WithLp.ofLp x) :=
  ⟨fun _ => hH _, fun x u => by
    rw [Map.System.supply, hout]
    exact discreteGradient_dissipation G g hJ hR hT u (hstep x u)⟩

/-! ## The implementation family -/

section Template

variable {X Y Q : Type*}

/-- The zero-input family of a family of port systems: every complete system read as the
autonomous field of its port system with the ports at zero; requirements and translation are
unchanged. -/
def zeroInputFamily (F : Family X Q n p) (sys : X → Port.System n p) : Family X Q n 0 where
  system x := .continuous (Port.System.autonomous (sys x).zeroInput)
  meets := F.meets
  translate := F.translate

@[powerlib_foundation] theorem zeroInputFamily_isAutonomous (F : Family X Q n p)
    (sys : X → Port.System n p) :
    (zeroInputFamily F sys).IsAutonomous fun x => (sys x).zeroInput :=
  fun _ => rfl

/-- The explicit Euler implementation family of a family of port systems, over an
implementation type `Y` whose members carry a design model `design y` and a step `step y`: every
implementation read as the Euler discretization of its design's port system with its step;
requirements and translation are those of its design model. -/
def eulerPortFamily (F : Family X Q n p) (sys : X → Port.System n p) (design : Y → X)
    (step : Y → ℝ) : Family Y Q n p where
  system y := .discrete (eulerSystem (sys (design y)) (step y))
  meets y := F.meets (design y)
  translate := F.translate

/-- The explicit Euler realization of a family of port systems: every Euler implementation
realizes its design model. -/
def eulerPorts (F : Family X Q n p) (sys : X → Port.System n p) (design : Y → X)
    (step : Y → ℝ) : Implementation X Q Y Q n p n p :=
  { model := F, impl := eulerPortFamily F sys design step,
    realizes := Implementation.ofDesign design }

end Template

/-! The laws are connection statements about arbitrary families of `Type`. -/

variable {X Y Q : Type}

/-- A family of port systems and its zero-input family have the same flow denotations. -/
@[tmio TM, powerlib_domain] theorem den_flow_zeroInputFamily {F : Family X Q n p}
    {sys : X → Port.System n p} (hF : F.IsPort sys) (P : Flow.Property) :
    connection% ((zeroInputFamily F sys).den (.flow P) = F.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  ext x
  rw [(connection_proof% (zeroInputFamily_isAutonomous F sys).mem_den_flow), (connection_proof% Family.mem_den), hF x]
  rfl

/-- The flow denotations of the Euler implementations of a family of port systems are those of
the autonomous Euler implementations of its zero-input family. -/
@[tmio TM, powerlib_domain] theorem eulerPortFamily_den_flow (F : Family X Q n p)
    (sys : X → Port.System n p) (design : Y → X) (step : Y → ℝ) (P : Flow.Property) :
    connection% ((eulerPortFamily F sys design step).den (.flow P) =
      (eulerFamily (zeroInputFamily F sys) (fun x => (sys x).zeroInput) design step).den
        (.flow P)) := by
  unfold powerlib.TMIO.Statement
  ext y
  rw [(connection_proof% (eulerFamily_isAutonomousMap _ _ design step).mem_den_flow), (connection_proof% Family.mem_den)]
  rfl

variable {F : Family X Q n p} {sys : X → Port.System n p} {design : Y → X} {step : Y → ℝ}

/-- The realization of a flow sentence by the Euler implementations of a family of port systems
is sound exactly when it is for the autonomous Euler implementations of its zero-input family. -/
@[tmio MI, powerlib_domain] theorem eulerPorts_realizationSoundUnder_flow_iff (hF : F.IsPort sys)
    {Δ : Set Q} {P : Flow.Property} :
    connection% ((eulerPorts F sys design step).RealizationSoundUnder Δ (.flow P) ↔
      (euler (zeroInputFamily F sys) (fun x => (sys x).zeroInput) design step).RealizationSoundUnder
        Δ (.flow P)) := by
  unfold powerlib.TMIO.Statement Implementation.RealizationSoundUnder
  change certify _ (F.den _) ∩ _ ⊆ (eulerPortFamily F sys design step).den _ ↔
    certify _ ((zeroInputFamily F sys).den _) ∩ _ ⊆ _
  rw [den_flow_zeroInputFamily hF, eulerPortFamily_den_flow]
  rfl

/-! ## The flow sentences -/

/-- **Small steps realize local exponential stability, for a model `C¹` near its point.** In a
family of port systems, a locally exponentially stable model whose zero-input field is `C¹` near
the origin has a step `h₀ > 0` such that every Euler implementation of it with a step in
`(0, h₀]` is locally exponentially stable (`euler_sound_small_step_local` on the zero-input
family). -/
@[tmio MI, powerlib_domain] theorem eulerPorts_sound_small_step_local (hF : F.IsPort sys) {x : X}
    (hC : ContDiffAt ℝ 1 (sys x).zeroInput 0)
    (hx : x ∈ F.den (.flow .locallyExponentiallyStable)) :
    connection% (∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y : Y, design y = x → step y ∈ Set.Ioc (0 : ℝ) h₀ →
      y ∈ (eulerPortFamily F sys design step).den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [eulerPortFamily_den_flow]
  rw [← den_flow_zeroInputFamily hF] at hx
  exact euler_sound_small_step_local (zeroInputFamily_isAutonomous F sys) hC hx

/-- **Large steps: without a step constraint the Euler realization of a family of port systems is
not sound, from a model `C¹` near its point** (`n > 0`). A locally exponentially stable model
whose zero-input field is `C¹` near the origin and whose Euler implementations include
arbitrarily large steps refutes realization soundness
(`not_euler_realizationSoundUnder_of_large_step_local` on the zero-input family). -/
@[tmio MI, powerlib_domain] theorem not_eulerPorts_realizationSoundUnder_of_large_step_local
    (hF : F.IsPort sys) (hn : 0 < n) {x : X} (hC : ContDiffAt ℝ 1 (sys x).zeroInput 0)
    (hx : x ∈ F.den (.flow .locallyExponentiallyStable))
    (hY : ∀ h₁ : ℝ, ∃ y : Y, design y = x ∧ h₁ ≤ step y) :
    connection% (¬ (eulerPorts F sys design step).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable)) := by
  have h := eulerPorts_realizationSoundUnder_flow_iff (design := design) (step := step)
    (Δ := ∅) (P := .locallyExponentiallyStable) hF
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  rw [← den_flow_zeroInputFamily hF] at hx
  exact not_euler_realizationSoundUnder_of_large_step_local (zeroInputFamily_isAutonomous F sys)
    hn hC hx hY

/-! ## Passivity -/

/-- **Explicit Euler implementations are not passive, at any step.** An Euler implementation with
a positive step of a model whose output, at some state, is a nonzero `v` whatever the input, is
not passive (`not_passive_eulerSystem`). -/
@[tmio TM, powerlib_domain] theorem eulerPortFamily_not_mem_den_passive {y : Y} (hh : 0 < step y)
    {x₀ : ℝⁿ} {v : Fin p → ℝ} (hv : ∀ u, (sys (design y)).output x₀ u = v) (hv0 : v ≠ 0) :
    connection% (y ∉ (eulerPortFamily F sys design step).den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  exact not_passive_eulerSystem _ hh hv hv0

/-- **The passivity realization of explicit Euler is not sound, at any step.** An Euler
implementation with a positive step of a passive design whose output, at some state, is a
nonzero `v` whatever the input refutes realization soundness of passivity within every
requirement context the design meets. -/
@[tmio MI, powerlib_domain] theorem not_eulerPorts_realizationSoundUnder_passive {Δ : Set Q} {y : Y}
    (hd : design y ∈ F.den .passive) (hΔ : design y ∈ realize F.meets Δ) (hh : 0 < step y)
    {x₀ : ℝⁿ} {v : Fin p → ℝ} (hv : ∀ u, (sys (design y)).output x₀ u = v) (hv0 : v ≠ 0) :
    connection% (¬ (eulerPorts F sys design step).RealizationSoundUnder Δ .passive) := by
  unfold powerlib.TMIO.Statement
  refine Implementation.not_realizationSoundUnder_of_design (I := eulerPorts F sys design step)
    rfl hd ?_ (eulerPortFamily_not_mem_den_passive hh hv hv0)
  change y ∈ realize (fun y q => F.meets (design y) q) Δ
  rw [TMIO.realize_comap]
  exact hΔ

/-- **The integrator is a witness.** In a family of one-state, one-port systems, an
implementation with a positive step whose design is the integrator `ẋ = u`, `y = x` (passive)
refutes realization soundness of passivity (`not_passive_eulerSystem_integrator`). -/
@[tmio MI, powerlib_domain] theorem not_eulerPorts_realizationSoundUnder_passive_of_integrator
    {F : Family X Q 1 1} {sys : X → Port.System 1 1} (hF : F.IsPort sys) (y : Y)
    (hx : sys (design y) = integrator.system) (hy : 0 < step y) :
    connection% (¬ (eulerPorts F sys design step).RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  refine Implementation.not_realizationSoundUnder_of_design (I := eulerPorts F sys design step)
    (y := y) rfl ?_ ?_ ?_
  · change design y ∈ F.den .passive
    rw [(connection_proof% Family.mem_den), hF, hx]
    exact ⟨_, integrator_passiveWith⟩
  · rw [TMIO.realize_empty]
    exact Set.mem_univ _
  · change y ∉ (eulerPortFamily F sys design step).den .passive
    rw [(connection_proof% Family.mem_den)]
    change ¬ (eulerSystem (sys (design y)) (step y)).Passive
    rw [hx]
    exact not_passive_eulerSystem_integrator hy

/-! ## Linear plants -/

/-- The Euler map of the linear field of `A` is the linear map of the forward Euler matrix
`I + h A`. -/
@[powerlib_foundation] theorem eulerMap_linear (A : Matrix (Fin n) (Fin n) ℝ) (h : ℝ) :
    eulerMap (affineLinearVectorField A 0) h = Map.op (forwardEulerMatrix h A) := by
  rw [Map.op, forwardEulerMatrix, map_add, map_smul, map_one]
  funext z
  simp [eulerMap, Linear.affine_apply]

/-- **A Schur stable Euler matrix at a positive step forces a Hurwitz matrix.** If `I + h A` is
Schur stable with `h > 0`, every eigenvalue `λ` of `A` has `|1 + hλ|² = 1 + h (2 Re λ + h |λ|²)
< 1`, so `Re λ < 0`. -/
@[powerlib_foundation] theorem isHurwitz_of_forwardEuler_schurStable
    {A : Matrix (Fin n) (Fin n) ℝ} {h : ℝ} (hh : 0 < h)
    (hS : LTI.SchurStable (forwardEulerMatrix h A)) : IsHurwitz A := by
  rw [Linear.isHurwitz_iff_forall_eigen]
  intro μ v hv heig
  have hlt := (forwardEuler_schurStable_iff hh.ne').mp hS μ v hv heig
  have hsq : ‖1 + (h : ℂ) * μ‖ ^ 2 < 1 := by
    have := norm_nonneg (1 + (h : ℂ) * μ)
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq
  simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.add_im,
    Complex.one_im, Complex.im_ofReal_mul, zero_add] at hsq
  by_contra hre
  have hre : 0 ≤ μ.re := not_lt.mp hre
  nlinarith [sq_nonneg (h * μ.im), sq_nonneg (h * μ.re), mul_nonneg hh.le hre]

variable {plant : X → Linear.Plant n p}

/-- **The linear reading of the Euler implementations.** For plants, the attractive sentences and
sampled contraction of the Euler implementations denote those with a Schur stable forward Euler
matrix `I + h A`. -/
@[tmio TM, powerlib_domain] theorem eulerPortFamily_den_linear {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((eulerPortFamily F (fun x => (plant x).system) design step).den (.flow P) =
      {y | LTI.SchurStable (forwardEulerMatrix (step y) (plant (design y)).A)}) := by
  unfold powerlib.TMIO.Statement
  ext y
  rw [(connection_proof% Family.mem_den), Set.mem_ofPred_eq]
  change P.holdsMap (step y) (eulerSystem (plant (design y)).system (step y)).zeroInput 0 ↔ _
  rw [eulerSystem_zeroInput, Linear.Plant.system_zeroInput, eulerMap_linear]
  exact Map.holdsMap_op_iff_schurStable hP _

/-- **Completeness at every step, for linear families.** Every Euler implementation with a
positive step that satisfies an attractive sentence (or sampled contraction) realizes only models
satisfying it: its multipliers `1 + hλ` lie in the unit disk, which forces `Re λ < 0`. -/
@[tmio MI, powerlib_domain] theorem eulerPorts_realizationCompleteUnder_linear
    (hF : F.IsLinear plant) (hstep : ∀ y, 0 < step y) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) (Δ : Set Q) :
    connection% ((eulerPorts F (fun x => (plant x).system) design step).RealizationCompleteUnder
      Δ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rintro y ⟨hy, -⟩
  rw [Implementation.certify_realizes_of_design
    (I := eulerPorts F (fun x => (plant x).system) design step) rfl]
  change y ∈ (eulerPortFamily F (fun x => (plant x).system) design step).den (.flow P) at hy
  change design y ∈ F.den (.flow P)
  rw [eulerPortFamily_den_linear hP] at hy
  rw [hF.den_hurwitz hP]
  exact isHurwitz_of_forwardEuler_schurStable (hstep y) hy

/-- **Exactness for small steps, for linear families.** Every model has a step `h₀ > 0` such that
its Euler implementations with a step in `(0, h₀]` satisfy an attractive sentence (or sampled
contraction) exactly when it does: soundness below the step threshold of a Hurwitz model
(`exists_forwardEuler_schurStable`), completeness at every positive step. -/
@[tmio MI, powerlib_domain] theorem eulerPorts_exact_small_step_linear (hF : F.IsLinear plant)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) (x : X) :
    connection% (∃ h₀ : ℝ, 0 < h₀ ∧ ∀ y : Y, design y = x → step y ∈ Set.Ioc (0 : ℝ) h₀ →
      (y ∈ (eulerPortFamily F (fun x => (plant x).system) design step).den (.flow P) ↔
        x ∈ F.den (.flow P))) := by
  unfold powerlib.TMIO.Statement
  rw [hF.den_hurwitz hP, eulerPortFamily_den_linear hP]
  by_cases hA : IsHurwitz (plant x).A
  · obtain ⟨h₀, hh₀, hS⟩ := exists_forwardEuler_schurStable hA
    refine ⟨h₀, hh₀, fun y hy hs => ?_⟩
    subst hy
    exact iff_of_true (hS _ hs) hA
  · refine ⟨1, one_pos, fun y hy hs => ?_⟩
    subst hy
    exact iff_of_false (fun hS => hA (isHurwitz_of_forwardEuler_schurStable hs.1 hS)) hA

/-- **Large steps: without a step constraint the Euler realization of a linear family is not
sound** (`n > 0`). A Hurwitz model whose Euler implementations include arbitrarily large steps
refutes realization soundness of every attractive sentence and of sampled contraction: above a
step threshold every multiplier `1 + hλ` lies outside the closed unit disk
(`exists_forwardEuler_inverse_schurStable`) and the implementation is unstable. -/
@[tmio MI, powerlib_domain] theorem not_eulerPorts_realizationSoundUnder_of_large_step_linear
    (hF : F.IsLinear plant) (hn : 0 < n) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) {x : X} (hx : IsHurwitz (plant x).A)
    (hY : ∀ h₁ : ℝ, ∃ y : Y, design y = x ∧ h₁ ≤ step y) :
    connection% (¬ (eulerPorts F (fun x => (plant x).system) design step).RealizationSoundUnder ∅
      (.flow P)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨h₁, -, hB⟩ := exists_forwardEuler_inverse_schurStable hx
  obtain ⟨y, rfl, hy⟩ := hY h₁
  obtain ⟨B, hB, hS⟩ := hB _ hy
  refine Implementation.not_realizationSoundUnder_of_design
    (I := eulerPorts F (fun x => (plant x).system) design step) (y := y) rfl ?_ ?_ ?_
  · change design y ∈ F.den (.flow P)
    rw [hF.den_hurwitz hP]
    exact hx
  · rw [TMIO.realize_empty]
    exact Set.mem_univ _
  · intro hy'
    change y ∈ (eulerPortFamily F (fun x => (plant x).system) design step).den (.flow P) at hy'
    rw [eulerPortFamily_den_linear hP] at hy'
    have hu := Map.unstable_of_inverse_schurStable
      (Map.op (forwardEulerMatrix (step y) (plant (design y)).A)).hasFDerivAt (map_zero _) hB hS hn
    exact hu (Map.globallyExponentiallyStable_of_schurStable
      hy').locallyExponentiallyStable.lyapunovStable

end Numerics

end powerlib
