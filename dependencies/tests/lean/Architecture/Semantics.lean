import theorem.TMIO.ClaimElab
import powerlib
import theorem.Architecture

open Lean Meta Elab Command

-- Single-semantics audit.
/-! Every behavioural notion of the library is defined once, in the semantic layer
(`theorem.Flow.Defs`, `theorem.Map.Defs`, `theorem.Port.Defs`); every other declaration reaches
behaviour only through it. The audit takes nothing but the semantic layer as input — no list of
notions or names.

* Time and signals are read from the semantic layer: time is the type over which its notions
  quantify both instants and functions; the signal spaces are the codomains of its quantified
  functions of time. A signal is a function from time — or from a subtype of or a wrapper around
  time — into values containing a signal-space value; functions, structures, subtypes and sets of
  signals carry signals. A sequence indexed by steps `ℕ` into such values is a discrete signal.
* Discrete evolution is an iterate of a self-map of values containing a signal-space value, or the
  one-step update of a discrete-time system.
* A predicate is behavioural when it is a statement about signals or discrete evolution, or refers
  to a behavioural predicate of the ambient libraries or of the semantic layer. This is computed over the actual
  definitions of Mathlib and LeanForControl, transitively.

Every declaration of the library outside the semantic layer must satisfy three rules:

* A. No proposition mentions a signal, bound, constructed or passed, or evolves a state
  discretely.
* B. No reference to a behavioural predicate of the ambient libraries: behaviour is reached
  through the semantic layer.
* T. No notion — the value of a predicate declaration, a proposition field of a structure, a
  constructor of an inductive predicate — binds a time variable or a function of time. This
  rejects behaviour stated through closed-form solutions evaluated pointwise in time.

The positive control is the semantic layer itself: each of its modules defines notions the
classification recognizes as behavioural. The negative controls are fixtures stating behaviour in
twenty different ways, continuous and discrete, all rejected, and fixtures pulling the semantics
back or stating static conditions, all accepted. -/

noncomputable section

namespace SemanticFixture

open powerlib LinearSystems Filter Topology NNReal NormedSpace

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! Ways of defining behaviour outside the semantic layer; each must be rejected. -/

def ownSolutions (f : ℝ² → ℝ²) : Prop :=
  ∀ φ : ℝ → ℝ², (∀ t, HasDerivAt φ (f (φ t)) t) → Tendsto φ atTop (𝓝 0)

def ownBehaviour (f : ℝ² → ℝ²) : Set (ℝ → ℝ²) := {φ | ∀ t, HasDerivAt φ (f (φ t)) t}

def continuousSignals (f : ℝ² → ℝ²) : Prop := ∀ φ : C(ℝ, ℝ²), φ 0 = 0 → f (φ 1) = 0

def nonnegativeTime (f : ℝ² → ℝ²) : Prop := ∀ φ : ℝ≥0 → ℝ², f (φ 0) = φ 1

def portSignals (y : ℝ → ℝ) : Prop := ∀ u : ℝ → Fin 1 → ℝ, u 0 0 ≤ y 0

structure TrajectoryCertificate (f : ℝ² → ℝ²) where
  energy : ℝ² → ℝ
  decay : ∀ φ : ℝ → ℝ², ∀ t ≥ 0, energy (φ t) ≤ energy (φ 0) + ‖f (φ 0)‖

def upstreamDirect (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  LyapunovStable (affineLinearVectorField A 0) 0

def upstreamTransitive : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {A | Unstable (affineLinearVectorField A 0) 0}

def upstreamValue : (ℝ² → ℝ²) → ℝ² → Prop := LocalAsymptoticStable

def upstreamDecided (A : Matrix (Fin 2) (Fin 2) ℝ) : Bool :=
  @decide (LyapunovStable (affineLinearVectorField A 0) 0) (Classical.dec _)

def closedForm (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ C a : ℝ, 0 < a ∧ ∀ t ≥ 0, ‖exp (t • Linear.op A)‖ ≤ C * Real.exp (-a * t)

def closedFormLimit (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Tendsto (fun t : ℝ => exp (t • Linear.op A)) atTop (𝓝 0)

def closedFormEventually (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ᶠ t in (atTop : Filter ℝ), ‖exp (t • Linear.op A)‖ < 1

def scalarSolutions (a : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, deriv φ = (a * φ ·) → Tendsto φ atTop (𝓝 0)

inductive Reach (f : ℝ² → ℝ²) : ℝ² → Prop
  | start : Reach f 0
  | step (t : ℝ) (x : ℝ²) : Reach f x → Reach f (x + t • f x)

/-- Time behind a wrapper. -/
structure Instant where
  val : ℝ

def wrappedTime (f : ℝ² → ℝ²) : Prop := ∀ φ : Instant → ℝ², f (φ ⟨0⟩) = 0

/-- Discrete behaviour through iterates of the state map. -/
def ownOrbits (F : ℝ² → ℝ²) : Prop := ∀ y, Tendsto (fun k : ℕ => F^[k] y) atTop (𝓝 0)

/-- Discrete behaviour through an iterate evaluated at a fixed number of steps. -/
def twoSteps (F : ℝ² → ℝ²) : Prop := ∀ y, ‖F^[2] y‖ ≤ ‖y‖

/-- Discrete behaviour through sequences of states. -/
def ownSequences (F : ℝ² → ℝ²) : Prop :=
  ∀ x : ℕ → ℝ², (∀ k, x (k + 1) = F (x k)) → Tendsto x atTop (𝓝 0)

/-- Discrete behaviour through the one-step update of a discrete system. -/
def ownDissipation (s : Map.System 2 1) : Prop := ∀ x u, ‖s.step x u‖ ≤ ‖x‖

/-! Notions that only pull the semantic layer back, or say nothing about time; each must pass. -/

def closedFormSolution (x₀ : ℝ²) : ℝ → ℝ² := fun t => Real.exp (-t) • x₀

def pulledBack (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Flow.Property.globallyExponentiallyStable.holds (affineLinearVectorField A 0) 0

structure StaticCertificate (A : Matrix (Fin 2) (Fin 2) ℝ) where
  P : Matrix (Fin 2) (Fin 2) ℝ
  positive : P.PosDef
  lyapunov : A.transpose * P + P * A = -1

def equilibrium (f : ℝ² → ℝ²) : Prop := IsEquilibrium f 0

def margin (δ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ Δ : Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, |Δ i j| < δ) → IsHurwitz (A + Δ)

structure Gain where
  gain : ℝ → ℝ
  monotone : StrictMono gain

def window (r : ℝ) : Set ℝ := Set.Icc (r - 1) (r + 1)

def pulledBackMap (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Flow.Property.globallyExponentiallyStable.holdsMap 1 (Matrix.toEuclideanLin A) 0

def fixedPoint (F : ℝ² → ℝ²) : Prop := F 0 = 0

/-- A statement naming a behavioural notion directly rather than through a denotation. -/
@[powerlib_foundation] theorem bypass (f : ℝ² → ℝ²) (h : LyapunovStable f 0) :
    LyapunovStable f 0 := h

/-- The same for a discrete notion. -/
@[powerlib_foundation] theorem bypassMap (F : ℝ² → ℝ²) (h : Map.LyapunovStable F 0) :
    Map.LyapunovStable F 0 := h

end SemanticFixture

end

open SemanticAudit in
run_meta do
  let (times, spaces) ← readSemantics
  let #[time] := times | throwError "The semantic layer does not determine one time axis: {times}"
  if spaces.isEmpty then throwError "The semantic layer quantifies over no signals"
  let signals ← IO.mkRef {}
  let contains ← IO.mkRef {}
  let behaviour ← IO.mkRef {}
  let ctx : Ctx := { time, spaces, signals, contains, behaviour }
  -- Positive control: every module of the semantic layer defines behavioural notions.
  let env ← getEnv
  let mut notions : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    unless semanticLayer.contains env.header.moduleNames[i]! do continue
    let mut found := false
    for c in env.header.moduleData[i]!.constNames do
      if ← behavioural ctx c then
        notions := notions.push c
        found := true
    unless found do
      throwError "No behavioural notion recognized in {env.header.moduleNames[i]!}"
  -- The library outside the semantic layer.
  let decls ← libraryDecls
  let mut violations : Array String := #[]
  for c in decls do
    if let some reason ← withCurrHeartbeats (scanDecl ctx (outside ctx) c) then
      violations := violations.push s!"{c}: {reason}"
  unless violations.isEmpty do
    throwError "Behaviour defined outside the semantic layer:\n{"\n".intercalate violations.toList}"
  -- Negative controls: every fixture defining behaviour is rejected, every pullback accepted.
  for c in #[``SemanticFixture.ownSolutions, ``SemanticFixture.ownBehaviour,
      ``SemanticFixture.continuousSignals, ``SemanticFixture.nonnegativeTime,
      ``SemanticFixture.portSignals, ``SemanticFixture.TrajectoryCertificate,
      ``SemanticFixture.upstreamDirect, ``SemanticFixture.upstreamTransitive,
      ``SemanticFixture.upstreamValue, ``SemanticFixture.upstreamDecided,
      ``SemanticFixture.closedForm, ``SemanticFixture.closedFormLimit,
      ``SemanticFixture.closedFormEventually, ``SemanticFixture.scalarSolutions,
      ``SemanticFixture.Reach, ``SemanticFixture.wrappedTime, ``SemanticFixture.ownOrbits,
      ``SemanticFixture.twoSteps, ``SemanticFixture.ownSequences,
      ``SemanticFixture.ownDissipation] do
    if (← scanDecl ctx (outside ctx) c).isNone then
      throwError "The audit accepted a behavioural definition: {c}"
  for c in #[``SemanticFixture.closedFormSolution, ``SemanticFixture.pulledBack,
      ``SemanticFixture.StaticCertificate, ``SemanticFixture.equilibrium, ``SemanticFixture.margin,
      ``SemanticFixture.Gain, ``SemanticFixture.window, ``SemanticFixture.pulledBackMap,
      ``SemanticFixture.fixedPoint] do
    if let some reason ← scanDecl ctx (outside ctx) c then
      throwError "The audit rejected a non-behavioural definition: {c}: {reason}"
  -- No bypass: a domain theorem of the library reaches behaviour only through a denotation, never
  -- by naming a behavioural notion of the semantic layer or of the ambient libraries.
  let mut domains : Nat := 0
  let mut bypasses : Array String := #[]
  for name in powerlib.Registry.theoremNames env (some .domain) do
    let some i := env.getModuleIdxFor? name | continue
    unless powerlib.Registry.isFirstPartyModule env.header.moduleNames[i.toNat]! do continue
    domains := domains + 1
    if let some reason ← powerlib.Architecture.rejection ctx (← getConstInfo name).type then
      bypasses := bypasses.push s!"{name}: {reason}"
  unless bypasses.isEmpty do
    throwError "Domain theorems naming behaviour directly:\n{"\n".intercalate bypasses.toList}"
  for c in #[``SemanticFixture.bypass, ``SemanticFixture.bypassMap] do
    let used := (← getConstInfo c).type.getUsedConstants
    unless ← used.anyM fun d => return (← (classify ctx).const d).isSome do
      throwError "The bypass audit accepted a statement naming behaviour directly: {c}"
  logInfo m!"POWERLIB_SINGLE_SEMANTICS_OK: time {time}; signal spaces {spaces.map (·.2)}; \
    {decls.size} declarations; notions {notions.qsort Name.quickLt}; {domains} domain theorems \
    reach behaviour through denotations"

noncomputable section

namespace SemanticsCases

open powerlib LinearSystems

-- The sentences are LeanForControl's definitions, not copies.
example {n : ℕ} : Flow.Property.holds (n := n) .lyapunovStable = LyapunovStable := rfl
example {n : ℕ} : Flow.Property.holds (n := n) .locallyExponentiallyStable =
    LocallyExponentiallyStable := rfl
example {n : ℕ} : Flow.Property.holds (n := n) .unstable = Unstable := rfl

-- The sentences of a system with ports read its zero-input field, and passivity its ports.
example {n p : ℕ} (P : Flow.Property) (s : Port.System n p) :
    (Sentence.flow P).holds (s : Behaviour n p) = P.holds s.zeroInput 0 := rfl
example {n p : ℕ} (s : Port.System n p) : Sentence.passive.holds (s : Behaviour n p) = s.Passive :=
  rfl

-- On a discrete-time system they read its zero-input map with its step length.
example {n p : ℕ} (P : Flow.Property) (s : Map.System n p) :
    (Sentence.flow P).holds (Behaviour.discrete s) = P.holdsMap s.period s.zeroInput 0 := rfl
example {n : ℕ} (T a : ℝ) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    Flow.Property.holdsMap (.decay a) T F 0 = Map.Decay F 0 (a * T) := rfl

-- A family's denotation is the semantics connection's generated value, and a linear family's
-- flow sentences are the hub's sentences of its zero-input plants.
example (s : Sentence) :
    Circuits.RL.family.den s = OrderDual.ofDual (TMIO.generate Circuits.RL.family.semantics {s}) :=
  rfl
example (P : Flow.Property) (m : Circuits.RL.Impedance) :
    m ∈ Circuits.RL.family.den (.flow P) ↔ P.holds (affineLinearVectorField m.plant.A 0) 0 :=
  Circuits.RL.family_isLinear.mem_den_flow

-- Both RL representations denote through the same plant.
example (s : Sentence) :
    (Circuits.RL.family.comap Circuits.RL.toImpedance).den s =
      Circuits.RL.toImpedance ⁻¹' Circuits.RL.family.den s :=
  Circuits.RL.family.den_comap _ s

/-! ## Semantic boundary: a stable linearization is not global stability -/

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- `x' = (‖x‖² - 1) x`: the linearization at the origin is `x' = -x`, and the unit sphere
consists of equilibria. -/
def field (x : ℝ¹) : ℝ¹ := (‖x‖ ^ 2 - 1) • x

def energy (x : ℝ¹) : ℝ := ‖x‖ ^ 2

def unit : ℝ¹ := EuclideanSpace.single 0 1

@[powerlib_foundation] theorem unit_norm : ‖unit‖ = 1 := by simp [unit]

@[powerlib_foundation] theorem field_unit : field unit = 0 := by simp [field, unit_norm]

@[powerlib_foundation] theorem field_contDiff : ContDiff ℝ 1 field :=
  ((contDiff_norm_sq ℝ).sub contDiff_const).smul contDiff_id

@[powerlib_foundation] theorem fderiv_field_zero :
    fderiv ℝ field 0 = Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) !![-1] := by
  have h := (((hasStrictFDerivAt_norm_sq (0 : ℝ¹)).hasFDerivAt.sub_const 1).smul
    (hasFDerivAt_id (0 : ℝ¹)))
  rw [show field = (fun x : ℝ¹ => ‖x‖ ^ 2 - 1) • id from rfl, h.fderiv]
  ext x i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]

-- Give the fixed boundary model its own domain: using Unit here would declare every
-- Unit-valued implementation detail a model in the complete-package inventory.
inductive BoundaryModel where
  | cubic

-- A semantic family makes this boundary a public connection conclusion.
def boundaryFamily : Family BoundaryModel Unit 1 0 :=
  ⟨fun _ => Port.System.autonomous field, fun _ _ => False, fun _ => Set.univ⟩

@[powerlib_foundation] theorem boundaryFamily_isAutonomous :
    boundaryFamily.IsAutonomous (fun _ => field) := fun _ => rfl

-- The linearization is Hurwitz: the origin is locally exponentially stable.
@[powerlib_domain] theorem locallyExponentiallyStable :
    connection% (BoundaryModel.cubic ∈ boundaryFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% boundaryFamily_isAutonomous.mem_den_flow)]
  exact hurwitz_linearization_locally_exponentially_stable !![-1] field_contDiff (by simp [field])
    fderiv_field_zero ((Linear.isHurwitz_one_iff (-1)).mpr (by norm_num))

-- The complete field has a nonzero constant solution, so global exponential stability is false.
@[powerlib_domain] theorem not_globallyExponentiallyStable :
    connection% (BoundaryModel.cubic ∉ boundaryFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% boundaryFamily_isAutonomous.mem_den_flow)]
  rintro ⟨-, -, C, a, hC, ha, hb⟩
  have hC1 : 0 < C + 1 := by linarith
  set T := Real.log (C + 1) / a with hT
  have hT0 : 0 ≤ T := div_nonneg (Real.log_nonneg (by linarith)) ha.le
  have hφ : IsTrajectoryOn (fun _ => unit) field 0 T := fun s _ => by
    simpa [field_unit] using (hasDerivAt_const s unit).hasDerivWithinAt
  have h := hb 0 T (fun _ => unit) hφ T ⟨hT0, le_rfl⟩
  simp only [sub_zero, unit_norm, mul_one] at h
  have hexp : Real.exp (-a * T) = (C + 1)⁻¹ := by
    rw [show -a * T = -Real.log (C + 1) by rw [hT]; field_simp, Real.exp_neg,
      Real.exp_log hC1]
  rw [hexp, ← div_eq_mul_inv, le_div_iff₀ hC1] at h
  linarith

@[powerlib_foundation] theorem energy_lie (x : ℝ¹) :
    fderiv ℝ energy x (field x) = 2 * (‖x‖ ^ 2 - 1) * ‖x‖ ^ 2 := by
  change fderiv ℝ (fun y : ℝ¹ => ‖y‖ ^ 2) x (field x) = _
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp only [smul_apply, innerSL_apply_apply]
  rw [field, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

-- The energy increases far from the origin, so it is not a global decay certificate.
@[powerlib_foundation] theorem energy_not_certificate :
    ¬ Nonempty (Flow.QuadraticDecay field energy 0) := by
  rintro ⟨c⟩
  have hd := c.dissipation ((2 : ℝ) • unit)
  have hn : ‖(2 : ℝ) • unit‖ = 2 := by rw [norm_smul, unit_norm]; norm_num
  rw [energy_lie, energy, hn] at hd
  nlinarith [c.rate_pos]

-- Global denotation includes existence through every state and convergence of every solution.
@[powerlib_domain] theorem cubic_global (n : ℕ) (α : Nonlinear.Cubic.Gain) :
    connection% (α ∈ (Nonlinear.Cubic.family (n := n)).den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Nonlinear.Cubic.family_isAutonomous.mem_den_flow)]
  exact (Nonlinear.Cubic.family_isAutonomous.mem_den_flow.mp
    (Nonlinear.Cubic.mem_den_globallyExponentiallyStable α)).globallyAsymptoticallyStable

-- A discrete family: the one-state map `x ↦ a x` with unit step length. Its sentences are read by
-- the map semantics, and its contraction is a public connection conclusion.
structure ScalarMap where
  a : ℝ

def mapFamily : Family ScalarMap Unit 1 0 :=
  ⟨fun g => .discrete (Map.System.autonomous 1 fun x => g.a • x), fun _ _ => False,
    fun _ => Set.univ⟩

@[powerlib_foundation] theorem mapFamily_isAutonomousMap :
    mapFamily.IsAutonomousMap (fun _ => 1) (fun g x => g.a • x) := fun _ => rfl

@[powerlib_domain] theorem contracting_mem_den (g : ScalarMap) (h : |g.a| < 1) :
    connection% (g ∈ mapFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mapFamily_isAutonomousMap.mem_den_flow)]
  refine ⟨by simp, 1, |g.a|, le_rfl, abs_nonneg _, h, fun y k => ?_⟩
  simp [smul_iterate, norm_smul]

-- The observation boundary: equal transfer functions with opposite stability, and the hidden
-- mode is exactly what minimality excludes.
@[powerlib_foundation] theorem transfer_boundary :
    Linear.transfer Linear.hiddenMode = Linear.transfer Linear.quietMode ∧
      ¬ IsHurwitz Linear.hiddenMode.A ∧ ¬ Linear.hiddenMode.Minimal :=
  ⟨Linear.transfer_not_determines_stability.1, Linear.transfer_not_determines_stability.2.2,
    Linear.hiddenMode_not_minimal⟩

end SemanticsCases

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := (powerlib.Registry.theoremNames env).filter (`SemanticsCases).isPrefixOf
  if roots.isEmpty then throwError "Semantic boundary discovery found no theorems"
  for root in roots do
    for ax in powerlib.Search.declarationAxioms env root do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected semantic boundary axiom {ax} in {root}"
  logInfo m!"POWERLIB_SEMANTIC_BOUNDARY_OK: {roots.size}"
