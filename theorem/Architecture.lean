import theorem.Family.Basic
import theorem.LibrarySearch
import theorem.TMIO.ClaimElab

/-! # Admission of the library (foundation)

Whole-package admission, with earlier feedback at module boundaries. Behavioural
predicates are followed transitively until a structurally certified connection endpoint.

Scope.
* Lean meta-programming, no mathematics. The semantic audit reads the time axis and the signal
  spaces from the declared semantic layer (`theorem/Flow/Defs.lean`, `theorem/Map/Defs.lean`,
  `theorem/Port/Defs.lean`) and recognizes behaviour — signals of time, sequences indexed by
  steps, iterates of a state map, the step of a discrete system — inside the semantic layer and
  rejects it outside.
* Model types are inferred from the actual `Family` definitions of first-party modules (with
  transparent aliases), not from a handwritten list. Private helpers and generic semantic support
  are implementation evidence; static mathematics needs no classification.
* Every public, model-specific behavioural conclusion must be a typed connection `Statement`,
  whatever its label; at a certified endpoint the inputs and structural maps are inspected while
  the semantic map stays abstract.

Source: the library rules (`Rules.md` §3a, generated connections and public conclusions) and the
design of public admission (`Architecture.md`); the connection grammar of
`theorem/TMIO/Claim.lean` and `theorem/TMIO/ClaimElab.lean`; the classification registry
(`theorem/Attributes.lean`) and the axiom audit (`theorem/LibrarySearch.lean`).

Results.
* The semantic audit (`SemanticAudit`): `semanticLayer`, `moduleOf?`, `inLibrary`,
  `inSemantics`, `Ctx`, `isTime`, `isPredicateType`, `isTypeFamily`, `isSpace`, `anyField`,
  `containsSpace`, `isStep`, `carriesSignalAux`, `evolvesDiscretely`, `isTimeFunction`,
  `carriesSignal`, `Rules`, `isEliminator`, `visit`, `scanDecl`, `behavioural`, `classify`,
  `outside`, `pattern`, `readSemantics`, `libraryDecls`.
* Admission (`powerlib.Architecture`): `conclusionOnConnection`, `statement?` (published claims
  carry the certificate in their type, independently of attributes), `context`, `rejection`,
  `audit`, `modelTypes`, `publicTypeRejection`, `declarationRejection`.
* `auditModules`: whole-package admission of the actual Lake module inventory, run by the build
  (`lakefile.lean`); it neither trusts source imports of the linter nor the classification
  registry, and rejects axioms outside the allowlist.
* `moduleLinter`, registered with `addModuleLinter`: earlier feedback for published connection
  statements at each module boundary.
-/

open Lean Meta Elab Command

namespace SemanticAudit

/-- The declared semantic definitions, from which signal spaces are inferred: continuous time
(`Flow`), discrete time (`Map`) and systems with ports (`Port`). -/
def semanticLayer : Array Name := #[`theorem.Flow.Defs, `theorem.Map.Defs, `theorem.Port.Defs]

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
  /-- Actual first-party modules selected by the admission build. -/
  owners : Array Name := #[]

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

/-- The step counter of discrete time: the type of the iteration count of `Nat.iterate`. -/
def isStep (d : Expr) : MetaM Bool := return (← whnfD d).isConstOf ``Nat

/-- Whether a value of type `ty` carries a signal: a function from time, or a sequence indexed by
steps (a discrete signal), into values containing a signal-space value, or a function, structure
or inductive value containing one. -/
partial def carriesSignalAux (ctx : Ctx) (ty : Expr) (stack : Array Expr) : MetaM Bool := do
  let ty ← whnfD ty
  match ty with
  | .forallE n d b bi =>
    if ← isProp ty then return false
    withLocalDecl n bi d fun x => do
      let body := b.instantiate1 x
      if ← isTypeFamily body <||> isPredicateType body then carriesSignalAux ctx d stack
      else if ← isTime ctx.time d <||> isStep d then
        containsSpace ctx body #[] <||> carriesSignalAux ctx body stack
      else carriesSignalAux ctx d stack <||> carriesSignalAux ctx body stack
  | _ => anyField ctx.signals ty stack (carriesSignalAux ctx)

/-- Discrete evolution: an iterate of a self-map of values containing a signal-space value, or the
one-step update of a discrete-time system. -/
def evolvesDiscretely (ctx : Ctx) (e : Expr) : MetaM Bool := do
  if e.isAppOf ``powerlib.Map.System.step then return true
  unless e.isAppOf ``Nat.iterate do return false
  let some α := e.getAppArgs[0]? | return false
  containsSpace ctx α #[]

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
  /-- At a certified endpoint, inspect its inputs while keeping its semantic map abstract. -/
  boundary : Expr → MetaM (Option (Array Expr)) := fun _ => pure none
  /-- A binder inside a proposition; `quantifier` when it is quantified by a notion. -/
  binder : Expr → Bool → MetaM (Option String)
  /-- A value inside a proposition, with its type. -/
  term : Expr → Expr → MetaM (Option String)
  /-- Any constant occurrence. -/
  const : Name → MetaM (Option String)

instance : Inhabited Rules := ⟨⟨fun _ => pure none, fun _ _ => pure none,
  fun _ _ => pure none, fun _ => pure none⟩⟩

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
  if let some inputs ← R.boundary e then
    for input in inputs do
      if let some reason ← visit R input inProp notional false then return some reason
    return none
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
  boundary e := do
    if ← isProp e then return none
    let ty ← inferType e
    if ty.getAppFn.isConstOf ``sInfHom then return some #[]
    unless ty.getAppFn.isConstOf ``Set || ty.getAppFn.isConstOf ``OrderDual do return none
    let some proof ← powerlib.TMIO.ClaimElab.endpoint? e | return none
    powerlib.TMIO.ClaimElab.endpointInputs? proof
  binder d _ := do
    if ← carriesSignal ctx d then return some s!"binds a signal of type {← ppExpr d}"
    return none
  term e ty := do
    if ← carriesSignal ctx ty then return some s!"contains the signal {← ppExpr e}"
    if ← evolvesDiscretely ctx e then return some s!"evolves a state discretely: {← ppExpr e}"
    return none
  const c := do
    let info ← getConstInfo c
    -- Maps carry preservation proofs in their types. Set-valued aliases must reduce
    -- to the closed Endpoint grammar, irrespective of their name or source module.
    if ← forallTelescopeReducing info.type fun _ body =>
        pure (body.getAppFn.isConstOf ``sInfHom) then return none
    if let .defnInfo d := info then
      if ← lambdaTelescope d.value fun _ body => do
          let ty ← inferType body
          unless ty.getAppFn.isConstOf ``Set || ty.getAppFn.isConstOf ``OrderDual do return false
          return (← powerlib.TMIO.ClaimElab.endpoint? body).isSome then return none
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
    if ← evolvesDiscretely ctx e then return some s!"evolves a state discretely: {← ppExpr e}"
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

namespace powerlib.Architecture

open Lean Meta Elab Command SemanticAudit

/-- Ordinary notation must compile to the kernel-checked closed grammar. -/
def conclusionOnConnection (e : Expr) : MetaM Bool := do
  try
    discard <| TMIO.ClaimElab.encode e
    return true
  catch _ => return false

/-- Published claims carry the certificate in their type, independently of attributes. -/
partial def statement? (e : Expr) (fuel : Nat := 24) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  if e.getAppFn.isConstOf ``TMIO.Statement then return some e.getAppArgs[0]!
  if let .forallE name ty body bi := e then
    return ← withLocalDecl name bi ty fun x => statement? (body.instantiate1 x) (fuel - 1)
  if let some unfolded ← unfoldDefinition? e then
    if unfolded != e then return ← statement? unfolded (fuel - 1)
  return none

def context (owners : Array Name := #[]) : MetaM Ctx := do
  let (times, spaces) ← readSemantics
  let #[time] := times | throwError "Expected one semantic time axis: {times}"
  let signals ← IO.mkRef {}
  let contains ← IO.mkRef {}
  let behaviour ← IO.mkRef {}
  return {time, spaces, signals, contains, behaviour, owners}

/-- A public domain contract is a connection conclusion with no direct or aliased behaviour.
This function is also used on intentionally rejected foundation fixtures. -/
def rejection (ctx : Ctx) (type : Expr) : MetaM (Option String) := do
  unless ← conclusionOnConnection type do
    return some "the conclusion is not a generated connection endpoint"
  -- Unwrap Statement so an unrelated behavioural expression on the other side of
  -- an equality cannot be hidden in its implicit proposition index.
  forallTelescope type fun xs body => do
    for x in xs do
      let ty ← inferType x
      if let some reason ← (classify ctx).binder ty false then return some reason
      let ty := (← statement? ty).getD ty
      if let some reason ← visit (classify ctx) ty true false false then return some reason
    let body := (← statement? body).getD body
    visit (classify ctx) body true false false

def audit (names : Array Name) : CommandElabM Unit := do
  liftTermElabM do
    let ctx ← context
    for name in names do
      if let some reason ← rejection ctx (← getConstInfo name).type then
        throwError "Domain theorem {name} violates connection admission: {reason}"

/-- Model types are inferred from the system-domain parameter of actual Family definitions.
This is a semantic ownership boundary, not a list of model or theorem names. -/
private partial def unfoldModelAlias (e : Expr) (owners : Array Name := #[])
    (seen : Array Expr := #[]) : MetaM Expr := do
  if seen.contains e then throwError "Cyclic model type alias during admission"
  if let .const c _ := e.getAppFn then
    let env ← getEnv
    let owner := (moduleOf? env c).getD env.mainModule
    if Registry.isFirstPartyModule owner || owners.contains owner then
      if let some (.defnInfo _) := (← getEnv).find? c then
        if let some unfolded ← unfoldDefinition? e then
          if unfolded != e then return ← unfoldModelAlias unfolded owners (seen.push e)
  return e

def modelTypes (owners : Array Name := #[]) : MetaM (Array (Nat × Expr)) := do
  let env ← getEnv
  let mut out : Array (Nat × Expr) := #[]
  for i in [:env.header.moduleNames.size] do
    unless if owners.isEmpty then Registry.isFirstPartyModule env.header.moduleNames[i]!
      else owners.contains env.header.moduleNames[i]! do continue
    for name in env.header.moduleData[i]!.constNames do
      let some info := env.find? name | continue
      if info matches .defnInfo _ | .opaqueInfo _ then
        if ← isProp info.type then continue
        let resultHead := info.type.getForallBody.getAppFn
        let isAlias := if let .const c _ := resultHead then
            match env.find? c with
            | some (.defnInfo _) =>
              let owner := (moduleOf? env c).getD env.mainModule
              Registry.isFirstPartyModule owner || owners.contains owner
            | _ => false
          else false
        unless info.type.getUsedConstants.contains ``Family || isAlias do continue
        let found ← forallTelescopeReducing info.type fun _ body => do
          let body ← whnf body
          unless body.getAppFn.isConstOf ``Family do return none
          let model := body.getAppArgs[0]!
          if model.isFVar then return none
          let model ← unfoldModelAlias model owners
          return some (← pattern model)
        if let some found := found then
          unless out.contains found do out := out.push found
  return out

private def canUnfoldModelAlias (e : Expr) (owners : Array Name) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  let env ← getEnv
  let owner := (moduleOf? env c).getD env.mainModule
  unless Registry.isFirstPartyModule owner || owners.contains owner do return false
  return (env.find? c).any fun info => info matches .defnInfo _

private abbrev ModelUseCache := IO.Ref (Std.HashMap (Expr × Array Name) Bool)

mutual
private partial def usesModelCached (cache : ModelUseCache) (models : Array (Nat × Expr))
    (e : Expr) (owners : Array Name) (expanded : Array Name := #[]) : MetaM Bool := do
  -- Free-variable IDs identify their immutable local declarations. Unresolved
  -- metavariables, in contrast, could change the answer later in the traversal.
  let cacheable := !e.hasMVar && !e.hasLevelMVar
  let key := (e, expanded)
  if cacheable then
    if let some result := (← cache.get)[key]? then return result
  let result ← usesModelCore cache models e owners expanded
  if cacheable then cache.modify (·.insert key result)
  return result

private partial def usesModelCore (cache : ModelUseCache) (models : Array (Nat × Expr))
    (e : Expr) (owners : Array Name) (expanded : Array Name) : MetaM Bool := do
  let eType ← inferType e
  let ty ← unfoldModelAlias eType owners
  for (holes, model) in models do
    let head := model.getForallBody.getAppFn
    if ty.getAppFn == head && (← withNewMCtxDepth do
        let (_, _, model) ← forallMetaBoundedTelescope model holes
        isDefEq model ty) then return true
  -- Only a matching head or an unfoldable first-party alias can match as a
  -- type-valued term. Avoid reducing the complete type telescope of every
  -- partial application merely to learn whether it returns a type.
  let mayUnfold ← canUnfoldModelAlias e owners
  if mayUnfold || models.any (fun (_, model) => model.getForallBody.getAppFn == e.getAppFn) then
    let value ← if mayUnfold && (← isTypeFamily eType) then unfoldModelAlias e owners else pure e
    for (holes, model) in models do
      if value.getAppFn == model.getForallBody.getAppFn && (← withNewMCtxDepth do
          let (_, _, model) ← forallMetaBoundedTelescope model holes
          isDefEq model value) then return true
  let uses := fun e => usesModelCached cache models e owners expanded
  let found ← match e with
  | .forallE n d b bi =>
    if ← uses d then pure true
    else withLocalDecl n bi d fun x => uses (b.instantiate1 x)
  | .lam n d b bi =>
    -- Match thunks introduce unused Unit binders; these are implementation data,
    -- not quantified models. Used model parameters are found in the lambda body.
    withLocalDecl n bi d fun x => uses (b.instantiate1 x)
  | .app f x => uses f <||> uses x
  | .mdata _ b => uses b
  | .proj _ _ s => uses s
  | .letE n t v b _ =>
    if ← uses t <||> uses v then pure true
    else withLetDecl n t v fun x => uses (b.instantiate1 x)
  | _ => pure false
  if found then return true
  -- A proposition alias can hide the complete model telescope, not just its conclusion.
  -- Expand fully applied propositions, not each partial application of a predicate.
  unless ← isProp e do return false
  let .const c _ := e.getAppFn | return false
  if expanded.contains c then return false
  let env ← getEnv
  let owner := (moduleOf? env c).getD env.mainModule
  unless Registry.isFirstPartyModule owner || owners.contains owner do return false
  let some (.defnInfo d) := env.find? c | return false
  unless ← isPredicateType d.type do return false
  let some unfolded ← unfoldDefinition? e | return false
  if unfolded == e then return false
  usesModelCached cache models unfolded owners (expanded.push c)
end

private def usesModel (models : Array (Nat × Expr)) (e : Expr)
    (owners : Array Name) : MetaM Bool := do
  -- Scope the cache to one model inventory, environment and traversal. Alias
  -- expansion paths are part of its key, so recursion cuts cannot poison it.
  let cache ← IO.mkRef {}
  usesModelCached cache models e owners

/-- Private proof helpers and generic semantic support are implementation evidence.
Every public, model-specific behavioural conclusion must use Statement; its label is irrelevant.
Static mathematics is checked normally and does not need a classification annotation. -/
def publicTypeRejection (ctx : Ctx) (models : Array (Nat × Expr)) (type : Expr) : MetaM (Option String) := do
  if (← statement? type).isSome then return ← rejection ctx type
  if ← usesModel models type ctx.owners then
    if let some reason ← visit (classify ctx) type true false false then
      return some s!"public model behaviour requires a typed connection Statement ({reason})"
    -- A connection-shaped model result carries its certificate, even if tagged foundation.
    if ← conclusionOnConnection type then
      return some "public connection conclusion requires a typed connection Statement"
  return none

def declarationRejection (ctx : Ctx) (models : Array (Nat × Expr)) (name : Name) : MetaM (Option String) := do
  let info ← getConstInfo name
  unless ← isProp info.type do return none
  if isPrivateName name then return none
  if (← statement? info.type).isNone && Registry.kindOf? (← getEnv) name == some .domain then
    return some "domain publication requires a typed connection Statement"
  publicTypeRejection ctx models info.type

/-- Whole-package admission uses the actual Lake module inventory, supplied by the build.
It neither trusts source imports of the linter nor the classification registry. -/
def auditModules (modules : Array Name) : CommandElabM Unit := do
  liftTermElabM do
    let ctx ← context modules
    let models ← modelTypes modules
    let env ← getEnv
    let mut checked : Nat := 0
    let mut claims : Nat := 0
    let mut rejected : Array String := #[]
    let mut roots : Array (Name × Name) := #[]
    for mod in modules do
      let some index := env.header.moduleNames.idxOf? mod |
        throwError "Built module missing from admission environment: {mod}"
      for name in env.header.moduleData[index]!.constNames do
        let some _ := env.find? name | continue
        -- Source declarations, including proof-valued definitions, are discovered from
        -- provenance. Compiler auxiliaries have no authored declaration range.
        unless (declRangeExt.find? env name).isSome do continue
        roots := roots.push (name, mod)
    if let some (name, ax) := Search.axiomViolation? env (roots.map (·.1)) then
      throwError "Admission rejected axiom {ax} in {name}"
    for (name, mod) in roots do
      let info ← getConstInfo name
      unless ← isProp info.type do continue
      checked := checked + 1
      if (← withCurrHeartbeats (statement? info.type)).isSome then claims := claims + 1
      if let some reason ← withCurrHeartbeats (declarationRejection ctx models name) then
        rejected := rejected.push s!"{name} in {mod}: {reason}"
    unless rejected.isEmpty do
      throwError "Admission rejected:\n{String.intercalate "\n" rejected.toList}"
    logInfo m!"POWERLIB_ADMISSION_OK: {modules.size} built modules; {checked} proofs; {claims} typed connection statements"

/-- Earlier feedback for published connection statements. The complete module inventory
is checked separately by the mandatory build target. -/
def moduleLinter : ModuleLinter where
  run commands := do
    let env ← getEnv
    unless Registry.isFirstPartyModule env.mainModule ||
        Registry.isIntegrationSource (← getFileName) do return
    let names ← Registry.authoredTheorems commands
    -- Fast feedback for explicitly published statements. Mandatory complete coverage
    -- is provided by auditModules after Lake builds every discovered source module.
    let published ← liftTermElabM <| names.filterM fun name =>
      return !isPrivateName name && (← statement? (← getConstInfo name).type).isSome
    audit published

initialize addModuleLinter moduleLinter

end powerlib.Architecture
