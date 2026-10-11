import theorem.Family.Basic
import theorem.LibrarySearch

/-! Architectural admission at every first-party module boundary. Behavioural predicates are
followed transitively until an explicitly marked generated connection endpoint is reached. -/

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
    if powerlib.Registry.connectionEndpoints.hasTag env c then return none
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

namespace powerlib.Architecture

open Lean Meta Elab Command SemanticAudit

/-- Check the conclusion, excluding the parameter and hypothesis telescope. Every branch of a
logical combination must itself be on a connection; an unrelated conjunct cannot launder a raw
behavioural conclusion. -/
partial def conclusionOnConnection (e : Expr) : MetaM Bool := do
  match e with
  | .forallE name ty body bi =>
    withLocalDecl name bi ty fun x => conclusionOnConnection (body.instantiate1 x)
  | _ =>
    let args := e.getAppArgs
    if e.getAppFn.isConstOf ``And || e.getAppFn.isConstOf ``Or then
      return (← conclusionOnConnection args[0]!) && (← conclusionOnConnection args[1]!)
    if e.getAppFn.isConstOf ``Not then return ← conclusionOnConnection args[0]!
    if e.getAppFn.isConstOf ``Exists then
      return ← lambdaTelescope args[1]! fun _ body => conclusionOnConnection body
    let env ← getEnv
    let head := e.getAppFn
    if let .const name _ := head then
      if Registry.connectionEndpoints.hasTag env name then return true
      -- Endpoint occurrences count only in logical relation operands, never inside an
      -- arbitrary model predicate's data arguments.
      if #[``Eq, ``Iff, ``LE.le, ``LT.lt, ``Membership.mem, ``Set.Subset].contains name &&
          e.getUsedConstants.any (Registry.connectionEndpoints.hasTag env) then return true
    if let some unfolded ← unfoldDefinition? e then
      if unfolded != e then return ← conclusionOnConnection unfolded
    return false

def context : MetaM Ctx := do
  let (times, spaces) ← readSemantics
  let #[time] := times | throwError "Expected one semantic time axis: {times}"
  let signals ← IO.mkRef {}
  let contains ← IO.mkRef {}
  let behaviour ← IO.mkRef {}
  return ⟨time, spaces, signals, contains, behaviour⟩

/-- A public domain contract is a connection conclusion with no direct or aliased behaviour.
This function is also used on intentionally rejected foundation fixtures. -/
def rejection (ctx : Ctx) (type : Expr) : MetaM (Option String) := do
  unless ← conclusionOnConnection type do
    return some "the conclusion is not a generated connection endpoint"
  visit (classify ctx) type true false false

def audit (names : Array Name) : CommandElabM Unit := do
  liftTermElabM do
    let ctx ← context
    for name in names do
      if let some reason ← rejection ctx (← getConstInfo name).type then
        throwError "Domain theorem {name} violates connection admission: {reason}"

/-- All named domain consumers are checked when their own module finishes, including tests,
examples and standalone integration sources. There is no theorem-name exemption list. -/
def moduleLinter : ModuleLinter where
  run commands := do
    let env ← getEnv
    unless Registry.isFirstPartyModule env.mainModule ||
        Registry.isIntegrationSource (← getFileName) do return
    let names ← Registry.authoredTheorems commands
    audit (names.filter fun name => Registry.kindOf? env name == some .domain)

initialize addModuleLinter moduleLinter

end powerlib.Architecture
