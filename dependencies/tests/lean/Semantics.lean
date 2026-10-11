import powerlib

-- Single-semantics audit.
/-! Every behavioural notion of the library is defined once, in the semantic layer
(`theorem.Flow.Defs`, `theorem.Port.Defs`); every other declaration reaches behaviour only through
it. The audit takes nothing but the semantic layer as input — no list of notions or names.

* Time and signals are read from the semantic layer: time is the type over which its notions
  quantify both instants and functions; the signal spaces are the codomains of its quantified
  functions of time. A signal is a function from time — or from a subtype of or a wrapper around
  time — into values containing a signal-space value; functions, structures, subtypes and sets of
  signals carry signals.
* A predicate is behavioural when it is a statement about signals, or refers to a behavioural
  predicate of the ambient libraries or of the semantic layer. This is computed over the actual
  definitions of Mathlib and LeanForControl, transitively.

Every declaration of the library outside the semantic layer must satisfy three rules:

* A. No proposition mentions a signal, bound, constructed or passed.
* B. No reference to a behavioural predicate of the ambient libraries: behaviour is reached
  through the semantic layer.
* T. No notion — the value of a predicate declaration, a proposition field of a structure, a
  constructor of an inductive predicate — binds a time variable or a function of time. This
  rejects behaviour stated through closed-form solutions evaluated pointwise in time.

The positive control is the semantic layer itself: each of its modules defines notions the
classification recognizes as behavioural. The negative controls are fixtures stating behaviour in
sixteen different ways, all rejected, and fixtures pulling the semantics back or stating static
conditions, all accepted. -/

open Lean Meta Elab Command

namespace SemanticAudit

/-- The declared semantic layer: the only input of the audit. -/
def semanticLayer : Array Name := #[`theorem.Flow.Defs, `theorem.Port.Defs]

def moduleOf? (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

def inLibrary (env : Environment) (c : Name) : Bool :=
  (moduleOf? env c).any (·.getRoot == `theorem)

def inSemantics (env : Environment) (c : Name) : Bool :=
  (moduleOf? env c).any semanticLayer.contains

structure Ctx where
  /-- The time axis. -/
  time : Expr
  /-- The spaces in which signals take values, abstracted over their parameters. -/
  spaces : Array (Nat × Expr)
  signals : IO.Ref (Std.HashMap Expr Bool)
  contains : IO.Ref (Std.HashMap Expr Bool)
  behaviour : IO.Ref (Std.HashMap Name Bool)

/-- Time up to unfolding, or a structure whose only data is a time value: a subtype of time or a
wrapper around it. -/
partial def isTime (time d : Expr) (fuel : Nat := 4) : MetaM Bool := do
  let d ← whnfD d
  if d == time then return true
  if fuel == 0 then return false
  let .const c us := d.getAppFn | return false
  let env ← getEnv
  let some (.inductInfo iv) := env.find? c | return false
  if isClass env c || iv.ctors.length != 1 || iv.numIndices != 0 then return false
  let args := d.getAppArgs
  if args.size != iv.numParams then return false
  let ci ← getConstInfo iv.ctors[0]!
  let ctorTy ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) args
  forallTelescopeReducing ctorTy fun fields _ => do
    let data ← fields.filterM fun f => return !(← isProof f)
    if h : data.size = 1 then isTime time (← inferType data[0]) (fuel - 1) else return false

/-- Values of this type are propositions or predicates. -/
def isPredicateType (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ b => return (← whnfD b).isProp

/-- Values of this type are types or families of types. -/
def isTypeFamily (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ b => do
    let b ← whnfD b
    return b.isSort && !b.isProp

/-- An instance of a signal space. -/
def isSpace (ctx : Ctx) (ty : Expr) : MetaM Bool :=
  ctx.spaces.anyM fun (holes, space) => withNewMCtxDepth do
    let (_, _, body) ← forallMetaBoundedTelescope space holes
    isDefEq body ty

/-- Values of a structure or inductive type, explored once per instance of its parameters:
`check` on the data fields, `stack` cutting recursive occurrences. -/
def anyField (cache : IO.Ref (Std.HashMap Expr Bool)) (ty : Expr) (stack : Array Expr)
    (check : Expr → Array Expr → MetaM Bool) : MetaM Bool := do
  let .const c us := ty.getAppFn | return false
  if c == ``Quot then return ← check (ty.getArg! 0) stack
  let env ← getEnv
  let some (.inductInfo iv) := env.find? c | return false
  if isClass env c then return false
  if ← isProp ty then return false
  let args := ty.getAppArgs
  if args.size < iv.numParams then return false
  let params := args.extract 0 iv.numParams
  let key := mkAppN (.const c us) params
  if stack.contains key then return false
  let closed := !key.hasFVar && !key.hasMVar
  if closed then
    if let some b := (← cache.get)[key]? then return b
  let mut result := false
  for ctor in iv.ctors do
    let ci ← getConstInfo ctor
    let ctorTy ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) params
    let found ← forallTelescopeReducing ctorTy fun fields _ => fields.anyM fun f => do
      let fty ← inferType f
      if ← isProp fty then return false
      check fty (stack.push key)
    if found then
      result := true
      break
  if closed then cache.modify (·.insert key result)
  return result

/-- Whether values of `ty` contain a value of a signal space. -/
partial def containsSpace (ctx : Ctx) (ty : Expr) (stack : Array Expr) : MetaM Bool := do
  if ← isSpace ctx ty then return true
  anyField ctx.contains (← whnfD ty) stack (containsSpace ctx)

/-- Whether a value of type `ty` carries a signal: a function from time into values containing a
signal-space value, or a function, structure or inductive value containing one. -/
partial def carriesSignalAux (ctx : Ctx) (ty : Expr) (stack : Array Expr) : MetaM Bool := do
  let ty ← whnfD ty
  match ty with
  | .forallE n d b bi =>
    if ← isProp ty then return false
    withLocalDecl n bi d fun x => do
      let body := b.instantiate1 x
      if ← isTypeFamily body <||> isPredicateType body then carriesSignalAux ctx d stack
      else if ← isTime ctx.time d then
        containsSpace ctx body #[] <||> carriesSignalAux ctx body stack
      else carriesSignalAux ctx d stack <||> carriesSignalAux ctx body stack
  | _ => anyField ctx.signals ty stack (carriesSignalAux ctx)

/-- A function from time. -/
def isTimeFunction (ctx : Ctx) (ty : Expr) : MetaM Bool := do
  let .forallE n d b bi ← whnfD ty | return false
  if ← isProp (.forallE n d b bi) then return false
  if !(← isTime ctx.time d) then return false
  withLocalDecl n bi d fun x => do
    let body := b.instantiate1 x
    return !(← isTypeFamily body) && !(← isPredicateType body)

def carriesSignal (ctx : Ctx) (ty : Expr) : MetaM Bool := do
  carriesSignalAux ctx (← instantiateMVars ty) #[]

structure Rules where
  /-- A binder inside a proposition; `quantifier` when it is quantified by a notion. -/
  binder : Expr → Bool → MetaM (Option String)
  /-- A value inside a proposition, with its type. -/
  term : Expr → Expr → MetaM (Option String)
  /-- Any constant occurrence. -/
  const : Name → MetaM (Option String)

instance : Inhabited Rules := ⟨⟨fun _ _ => pure none, fun _ _ => pure none, fun _ => pure none⟩⟩

def isEliminator (env : Environment) (c : Name) : Bool :=
  isAuxRecursor env c || isRecCore env c || isCasesOnLike env c || isMatcherCore env c

/-- Visit a value. `inProp`: inside a proposition. `notional`: inside a notion, the value of a
predicate declaration or a proposition field of a structure or inductive. `top`: in the
parameter telescope of the declaration. -/
partial def visit (R : Rules) (e : Expr) (inProp notional top : Bool) : MetaM (Option String) := do
  match e with
  | .bvar .. | .sort .. | .lit .. | .mvar .. => return none
  | .mdata _ b => return ← visit R b inProp notional top
  | _ => pure ()
  if ← isProof e then return none
  let ty ← inferType e
  if ← isTypeFamily ty then return none
  let isPropE ← isProp e
  let inProp := inProp || isPropE
  if inProp then
    if let some m ← R.term e ty then return some m
  match e with
  | .forallE n d b bi =>
    if let some m ← R.binder d notional then return some m
    if let some m ← visit R d inProp notional false then return some m
    withLocalDecl n bi d fun x => visit R (b.instantiate1 x) inProp notional false
  | .lam n d b bi =>
    if inProp && !top then
      if let some m ← R.binder d notional then return some m
    withLocalDecl n bi d fun x => visit R (b.instantiate1 x) inProp notional top
  | .letE n t v b _ =>
    if inProp then
      if let some m ← R.binder t false then return some m
    if let some m ← visit R v inProp false false then return some m
    withLetDecl n t v fun x => visit R (b.instantiate1 x) inProp notional false
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut elim := false
    match fn with
    | .const c _ =>
      if let some m ← R.const c then return some m
      elim := isEliminator (← getEnv) c
    | .fvar _ =>
      if inProp then
        if let some m ← R.term fn (← inferType fn) then return some m
    | _ => if let some m ← visit R fn inProp notional false then return some m
    let info ← getFunInfoNArgs fn args.size
    for h : i in [:args.size] do
      -- Implicit and instance arguments are determined by the explicit ones and their types.
      if let some p := info.paramInfo[i]? then
        if !p.isExplicit then continue
      let a := args[i]
      -- The binders of an eliminator's alternatives are pattern variables, not quantifiers.
      let r ← if elim then
          lambdaTelescope a fun xs body => do
            if inProp then
              for x in xs do
                if let some m ← R.binder (← inferType x) false then return some m
            visit R body inProp notional false
        else visit R a inProp notional false
      if r.isSome then return r
    return none
  | .proj _ _ s => visit R s inProp false false
  | .const c _ => R.const c
  | _ => return none

/-- Scan a declaration. A predicate declaration is a notion: its value is visited as one, and so
are the proposition fields of a structure and the constructors of an inductive predicate. -/
def scanDecl (ctx : Ctx) (R : Rules) (c : Name) : MetaM (Option String) := do
  let info ← getConstInfo c
  if ← isProp info.type then return none
  let pred ← isPredicateType info.type
  if pred then
    if ← forallTelescopeReducing info.type fun xs _ =>
        xs.anyM fun x => do carriesSignal ctx (← inferType x) then
      return some "is a predicate on signals"
  match info with
  | .defnInfo v => visit R v.value false pred true
  | .opaqueInfo v => visit R v.value false pred true
  | .inductInfo v =>
    for ctor in v.ctors do
      let ci ← getConstInfo ctor
      let r ← forallBoundedTelescope ci.type v.numParams fun _ rest => do
        if pred then return ← visit R rest true true false
        forallTelescopeReducing rest fun fields _ => do
          for f in fields do
            let fty ← inferType f
            if ← isProp fty then
              if let some m ← visit R fty true true false then return some m
          return none
      if r.isSome then return r
    return none
  | _ => return none

mutual
/-- A predicate is behavioural when it is a statement about signals, or refers to a behavioural
predicate of the ambient libraries or of the semantic layer. -/
partial def behavioural (ctx : Ctx) (c : Name) : MetaM Bool := do
  if let some b := (← ctx.behaviour.get)[c]? then return b
  ctx.behaviour.modify (·.insert c false)
  let info ← getConstInfo c
  let r ← if ← isPredicateType info.type then
      pure (← scanDecl ctx (classify ctx) c).isSome
    else pure false
  ctx.behaviour.modify (·.insert c r)
  return r

partial def classify (ctx : Ctx) : Rules where
  binder d _ := do
    if ← carriesSignal ctx d then return some s!"binds a signal of type {← ppExpr d}"
    return none
  term e ty := do
    if ← carriesSignal ctx ty then return some s!"contains the signal {← ppExpr e}"
    return none
  const c := do
    let env ← getEnv
    if inLibrary env c && !inSemantics env c then return none
    if ← behavioural ctx c then return some s!"refers to {c}"
    return none
end

/-- The rules for declarations outside the semantic layer. -/
def outside (ctx : Ctx) : Rules where
  binder d quantifier := do
    if ← carriesSignal ctx d then return some s!"binds a signal of type {← ppExpr d}"
    if quantifier then
      if ← isTime ctx.time d then return some "binds a time variable"
      if ← isTimeFunction ctx d then return some s!"binds a function of time of type {← ppExpr d}"
    return none
  term e ty := do
    if ← carriesSignal ctx ty then return some s!"contains the signal {← ppExpr e}"
    return none
  const c := do
    if inLibrary (← getEnv) c then return none
    if ← behavioural ctx c then
      return some s!"refers to the behavioural predicate {c} of an ambient library"
    return none

/-- Abstract the free variables of `e` into a closed pattern `∀ xs, e` with `xs.size` holes. -/
def pattern (e : Expr) : MetaM (Nat × Expr) := do
  let ids := (collectFVars {} e).fvarIds
  let decls ← ids.mapM (·.getDecl)
  let sorted := decls.qsort (·.index < ·.index)
  return (sorted.size, ← mkForallFVars (sorted.map (·.toExpr)) e)

/-- What the semantic layer quantifies over in its notions: the time axis is the type of its
quantified instants that is also the domain of its quantified functions; the signal spaces are
the codomains of its quantified functions of time. -/
def readSemantics : MetaM (Array Expr × Array (Nat × Expr)) := do
  let env ← getEnv
  let mut times : Array Expr := #[]
  let mut functions : Array (Expr × Nat × Expr) := #[]
  for i in [:env.header.moduleNames.size] do
    unless semanticLayer.contains env.header.moduleNames[i]! do continue
    for c in env.header.moduleData[i]!.constNames do
      let some (.defnInfo v) := env.find? c | continue
      let fns ← IO.mkRef (#[] : Array (Expr × Nat × Expr))
      let instants ← IO.mkRef (#[] : Array Expr)
      let R : Rules := {
        binder := fun d quantifier => do
          unless quantifier do return none
          let d ← whnfD d
          if let .forallE n dom b bi := d then
            unless ← isProp d do
              let dom ← whnfD dom
              let codomain? ← withLocalDecl n bi dom fun x => do
                let body := b.instantiate1 x
                if (← isTypeFamily body) || (← isPredicateType body) || body.hasLooseBVars then
                  return none
                return some (← pattern body)
              if let some codomain := codomain? then
                if !dom.hasFVar then fns.modify (·.push (dom, codomain))
          else if !d.hasFVar && !(← isProp d) && !d.isSort then instants.modify (·.push d)
          return none
        term := fun _ _ => return none
        const := fun _ => return none }
      discard <| visit R v.value false (← isPredicateType v.type) true
      for (dom, codomain) in ← fns.get do
        if (← instants.get).contains dom && !times.contains dom then times := times.push dom
        functions := functions.push (dom, codomain)
  let mut spaces : Array (Nat × Expr) := #[]
  for (dom, codomain) in functions do
    if times.contains dom && !spaces.contains codomain then spaces := spaces.push codomain
  return (times, spaces)

def libraryDecls : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    unless env.header.moduleNames[i]!.getRoot == `theorem do continue
    if semanticLayer.contains env.header.moduleNames[i]! then continue
    for c in env.header.moduleData[i]!.constNames do
      let some info := env.find? c | continue
      if info.isUnsafe then continue
      match info with
      | .defnInfo _ | .opaqueInfo _ | .inductInfo _ => out := out.push c
      | _ => pure ()
  return out

end SemanticAudit

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
      ``SemanticFixture.Reach, ``SemanticFixture.wrappedTime] do
    if (← scanDecl ctx (outside ctx) c).isNone then
      throwError "The audit accepted a behavioural definition: {c}"
  for c in #[``SemanticFixture.closedFormSolution, ``SemanticFixture.pulledBack,
      ``SemanticFixture.StaticCertificate, ``SemanticFixture.equilibrium, ``SemanticFixture.margin,
      ``SemanticFixture.Gain, ``SemanticFixture.window] do
    if let some reason ← scanDecl ctx (outside ctx) c then
      throwError "The audit rejected a non-behavioural definition: {c}: {reason}"
  logInfo m!"POWERLIB_SINGLE_SEMANTICS_OK: time {time}; signal spaces {spaces.map (·.2)}; \
    {decls.size} declarations; notions {notions.qsort Name.quickLt}"

noncomputable section

namespace SemanticsCases

open powerlib LinearSystems

-- The sentences are LeanForControl's definitions, not copies.
example {n : ℕ} : Flow.Property.holds (n := n) .lyapunovStable = LyapunovStable := rfl
example {n : ℕ} : Flow.Property.holds (n := n) .locallyExponentiallyStable =
    LocallyExponentiallyStable := rfl
example {n : ℕ} : Flow.Property.holds (n := n) .unstable = Unstable := rfl

-- A linear family's denotation is the Flow denotation of its zero-input fields.
example {X : Type*} {n p : ℕ} (plant : X → Linear.Plant n p) (P : Flow.Property) :
    Linear.den plant P = Flow.den (fun x => affineLinearVectorField (plant x).A 0) 0 P := rfl

-- Both RL representations denote through the same plant.
example (P : Flow.Property) :
    Linear.den Circuits.RL.StateSpace.plant P =
      Circuits.RL.toImpedance ⁻¹' Linear.den Circuits.RL.Impedance.plant P :=
  Circuits.RL.den_stateSpace P

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

-- The linearization is Hurwitz: the origin is locally exponentially stable.
@[powerlib_domain] theorem locallyExponentiallyStable :
    LocallyExponentiallyStable field 0 :=
  hurwitz_linearization_locally_exponentially_stable !![-1] field_contDiff (by simp [field])
    fderiv_field_zero ((Linear.isHurwitz_one_iff (-1)).mpr (by norm_num))

-- The complete field has a nonzero constant solution, so global exponential stability is false.
@[powerlib_domain] theorem not_globallyExponentiallyStable :
    ¬ Flow.GloballyExponentiallyStable field 0 := by
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
@[powerlib_domain] theorem energy_not_certificate :
    ¬ Nonempty (Flow.QuadraticDecay field energy 0) := by
  rintro ⟨c⟩
  have hd := c.dissipation ((2 : ℝ) • unit)
  have hn : ‖(2 : ℝ) • unit‖ = 2 := by rw [norm_smul, unit_norm]; norm_num
  rw [energy_lie, energy, hn] at hd
  nlinarith [c.rate_pos]

-- The cubic field: a solution through every state, and decay of every solution segment.
@[powerlib_domain] theorem cubic_every_state_has_solution (n : ℕ) (a : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ φ : ℝ → EuclideanSpace ℝ (Fin n), φ a = x₀ ∧
      IsIntegralCurveOn φ (fun _ x => Nonlinear.Cubic.field x) (Set.Ici a) :=
  (Nonlinear.Cubic.globallyExponentiallyStable n).2.1 a x₀

@[powerlib_domain] theorem cubic_every_solution_converges (n : ℕ) (a : ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin n))
    (hφ : IsIntegralCurveOn φ (fun _ x => Nonlinear.Cubic.field x) (Set.Ici a)) :
    Filter.Tendsto φ Filter.atTop (nhds 0) :=
  (Nonlinear.Cubic.globallyExponentiallyStable n).globallyAsymptoticallyStable.2.2.2 a φ hφ

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
