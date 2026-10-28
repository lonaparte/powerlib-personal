import theorem.TMIO.Claim
import theorem.TMIO.Relation
import theorem.TMIO.KnowledgeKind
import Lean

/-! # Elaboration of connection claims (foundation)

Compile ordinary connection notation to the closed kernel-checked grammar. This is
untrusted elaboration: a mistaken compiler cannot produce a well-typed certificate.

Scope.
* Lean meta-programming over the grammar of `theorem/TMIO/Claim.lean`; no mathematics. No names
  or tags of model families are trusted: aliases are unfolded until a typed map application or a
  structural powerset operation is reached, and there is no arbitrary-proposition fallback.
* Claims infer their endpoint and binder universes. Atomic certificates may use the two endpoint
  universes in either order; universal type parameters use `allType`, and existential binders
  may range over type universes when their bodies are genuine claims. A side condition is
  accepted only where the grammar
  has one: the right side of an iff whose left side is a claim, and the guard `A i` of an
  existential `∃ i, A i ∧ P i`.

Source: the closed grammar `Endpoint`, `Condition`, `ConnectionClaim`, `Statement`
(`theorem/TMIO/Claim.lean`) and the semantic constructors of `theorem/TMIO/Relation.lean`; the
admission rules of `Rules.md` §3a (`connection% (ordinary proposition)` constructs the
certificate, which Lean's kernel checks).

Results.
* `endpoint?`: an `Endpoint` certificate for a value, if one exists.
* `endpointInputs?`: the inputs and structural maps of an endpoint, derived from its certificate,
  so that an identity map cannot launder a behavioural set.
* `condition`: a `Condition` certificate of a side condition (comparisons of numbers, `¬`, `∧`,
  `∨`; `≥`, `>`, `≠` by unfolding).
* `encode`: a `ConnectionClaim` certificate of a proposition.
* The term elaborator `connection% P`: the `TMIO.Statement` of `P` with its generated certificate,
  checked again by the kernel; the trace class `powerlib.claim`.
-/

open Lean Meta Elab Term

namespace powerlib.TMIO.ClaimElab

initialize registerTraceClass `powerlib.claim

private def certConst (name : Name) : MetaM Expr :=
  mkConstWithFreshMVarLevels name

private def endpointType (value : Expr) (u v : Level) : MetaM Expr := do
  return mkApp2 (mkConst ``Endpoint [u,v]) (← inferType value) value

private def claimType (levels : List Level) (prop : Expr) : MetaM Expr :=
  pure <| mkApp (mkConst ``ConnectionClaim levels) prop

/-- Supply the expected index before finalizing implicit arguments. -/
private def buildWith (f : Expr) (xs : Array Expr) (target : Expr) : MetaM Expr := do
  let (args, bis, result) ← forallMetaTelescope (← inferType f)
  let mut index := 0
  for i in [:args.size] do
    if bis[i]!.isExplicit then
      unless index < xs.size do throwError "missing certificate argument"
      unless ← isDefEq args[i]! xs[index]! do throwError "certificate argument mismatch"
      index := index + 1
  unless ← isDefEq result target do throwError "certificate index mismatch"
  for i in [:args.size] do
    if bis[i]! == .instImplicit then
      let arg ← instantiateMVars args[i]!
      if arg.isMVar then arg.mvarId!.assign (← synthInstance (← inferType arg))
  return ← instantiateMVars (mkAppN f args)

private def build (ctor : Name) (xs : Array Expr) (target : Expr) : MetaM Expr := do
  buildWith (← certConst ctor) xs target

private def buildEndpoint (ctor : Name) (xs : Array Expr) (value : Expr) : MetaM Expr := do
  let u ← getDecLevel (← inferType value)
  let v ← if #[``Endpoint.upper, ``Endpoint.lower, ``Endpoint.closed].contains ctor then do
      let ty ← whnf (← inferType xs[0]!)
      let domain := ty.getAppArgs[if ctor == ``Endpoint.lower then 1 else 0]!
      getDecLevel domain
    else do
      let ty ← inferType xs.back!
      let .const _ levels := ty.getAppFn | throwError "endpoint proof expected"
      pure levels[1]!
  buildWith (mkConst ctor [u,v]) xs (← endpointType value u v)

private def attempt (k : MetaM Expr) : MetaM (Option Expr) :=
  withNewMCtxDepth do
    try return some (← k) catch ex =>
      trace[powerlib.claim] ex.toMessageData
      return none

private def certifyEndpoint (value proof : Expr) : MetaM (Option Expr) :=
  attempt do
    let ty ← inferType proof
    let .const _ levels := ty.getAppFn | throwError "endpoint proof expected"
    let target ← endpointType value levels[0]! levels[1]!
    unless ← isDefEq (← inferType proof) target do throwError "endpoint mismatch"
    return ← instantiateMVars proof

/-- No names or tags of model families are trusted. Unfold aliases until a typed map
application or a structural powerset operation is reached. -/
partial def endpoint? (e : Expr) (fuel : Nat := 32) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let e ← instantiateMVars e
  -- Endpoints live in lattices. Reject ordinary scalar/matrix calculations before
  -- unfolding their potentially large computational definitions.
  let ty ← inferType e
  if ← isProp ty then return none
  if !(← attempt do
      let lattice ← mkAppM ``CompleteLattice #[ty]
      synthInstance lattice).isSome then return none
  let args := e.getAppArgs
  let head := e.getAppFn
  trace[powerlib.claim] "endpoint {e}"
  if head.isConstOf ``OrderDual.ofDual || head.isConstOf ``OrderDual.toDual then
    if let some p ← endpoint? args.back! (fuel - 1) then
      let ctor := if head.isConstOf ``OrderDual.ofDual then ``Endpoint.dual else ``Endpoint.toDual
      if let some result ← attempt (buildEndpoint ctor #[p] e) then
        if let some result ← certifyEndpoint e result then return some result
  if let .app fn x := e then
    if let some closed := fn.find? fun sub =>
        sub.getAppFn.isConstOf ``closure && !sub.getAppArgs.isEmpty then
      if let some p ← attempt (buildEndpoint ``Endpoint.closed #[closed.getAppArgs.back!, x] e) then
        return some p
    if fn.getAppFn.isConstOf ``DFunLike.coe then
      let obj := fn.getAppArgs.back!
      if obj.isConstOf ``OrderDual.ofDual || obj.getAppFn.isConstOf ``OrderDual.ofDual ||
          obj.isConstOf ``OrderDual.toDual || obj.getAppFn.isConstOf ``OrderDual.toDual then
        if let some p ← endpoint? x (fuel - 1) then
          let ctor := if obj.getAppFn.isConstOf ``OrderDual.ofDual then ``Endpoint.dual
            else ``Endpoint.toDual
          if let some p ← attempt (buildEndpoint ctor #[p] e) then return some p
      let ty ← whnf (← inferType obj)
      if ty.getAppFn.isConstOf ``sInfHom then
        if let some p ← attempt (buildEndpoint ``Endpoint.upper #[obj, x] e) then
          if let some p ← certifyEndpoint e p then return some p
    if fn.getAppFn.isConstOf ``LowerAdjoint.toFun then
      let obj := fn.getAppArgs.back!
      if obj.getAppFn.isConstOf ``generate then
        if let some p ← attempt (buildEndpoint ``Endpoint.lower #[obj.getAppArgs.back!, x] e) then
          if let some p ← certifyEndpoint e p then return some p
  if head.isConstOf ``SetRel.core && args.size >= 2 then
    let rel := args[args.size - 2]!
    let input := args.back!
    if let some p ← attempt do
        let back ← mkAppM ``cover #[rel]
        buildEndpoint ``Endpoint.upper #[back, input] e then
      if let some p ← certifyEndpoint e p then return some p
  if head.isConstOf ``Set.preimage && args.size >= 2 then
    if let some p ← endpoint? args.back! (fuel - 1) then
      if let some p ← attempt (buildEndpoint ``Endpoint.preimage #[args[args.size - 2]!, p] e) then
        if let some p ← certifyEndpoint e p then return some p
  if head.isConstOf ``Compl.compl then
    if let some p ← endpoint? args.back! (fuel - 1) then
      if let some p ← attempt (buildEndpoint ``Endpoint.compl #[p] e) then
        if let some p ← certifyEndpoint e p then return some p
  if head.isConstOf ``Inter.inter || head.isConstOf ``Min.min then
    if args.size >= 2 then
      if let some p ← endpoint? args[args.size - 2]! (fuel - 1) then
        if let some q ← endpoint? args.back! (fuel - 1) then
          if let some p ← attempt (buildEndpoint ``Endpoint.inter #[p, q] e) then
            if let some p ← certifyEndpoint e p then return some p
  if let some unfolded ← unfoldDefinition? e then
    if unfolded != e then return ← endpoint? unfolded (fuel - 1)
  return none

/-- Inputs and structural maps remain outside the semantic-map abstraction boundary.
Derive them from the certificate, so an identity map cannot launder a behavioural set. -/
partial def endpointInputs? (proof : Expr) (fuel : Nat := 32) : MetaM (Option (Array Expr)) := do
  if fuel == 0 then return none
  let proof ← whnf proof
  let args := proof.getAppArgs
  let head := proof.getAppFn
  if #[``Endpoint.upper, ``Endpoint.lower, ``Endpoint.closed].any head.isConstOf then
    return some #[args.back!]
  if #[``Endpoint.dual, ``Endpoint.toDual, ``Endpoint.compl].any head.isConstOf then
    return ← endpointInputs? args.back! (fuel - 1)
  if head.isConstOf ``Endpoint.preimage then
    let some inputs ← endpointInputs? args.back! (fuel - 1) | return none
    return some (#[args[args.size - 3]!] ++ inputs)
  if head.isConstOf ``Endpoint.inter then
    let some left ← endpointInputs? args[args.size - 2]! (fuel - 1) | return none
    let some right ← endpointInputs? args.back! (fuel - 1) | return none
    return some (left ++ right)
  return none

private def certified (levels : List Level) (prop proof : Expr) : MetaM Expr := do
  let target ← claimType levels prop
  unless ← isDefEq (← inferType proof) target do
    throwError "Connection grammar certificate does not describe the requested proposition"
  return ← instantiateMVars proof

/-- Failed endpoint orientations must not constrain the remaining candidates' universe levels.
Use ordinary saved states here: unlike endpoint discovery, successful atoms must constrain the
shared universe metavariables of the enclosing claim. -/
private def atomic? (levels : List Level) (prop : Expr) (ctors : Array Name)
    (args : Array Expr) : MetaM (Option Expr) := do
  for ctor in ctors do
    let saved ← saveState
    try
      return some (← certified levels prop (← build ctor args (← claimType levels prop)))
    catch ex =>
      saved.restore
      trace[powerlib.claim] ex.toMessageData
  return none

/-- Build a certificate of a side condition: a comparison of numbers or a combination of such by
`¬`, `∧`, `∨`. -/
partial def condition (e : Expr) (fuel : Nat := 32) : MetaM Expr := do
  if fuel == 0 then throwError "Side condition unfolding exceeded its limit"
  let e ← instantiateMVars e
  let target := mkApp (mkConst ``Condition) e
  let check (proof : Expr) : MetaM Expr := do
    unless ← isDefEq (← inferType proof) target do
      throwError "Side condition certificate does not describe the requested proposition"
    instantiateMVars proof
  let args := e.getAppArgs
  let head := e.getAppFn
  if head.isConstOf ``Not then
    return ← check (← mkAppM ``Condition.not #[← condition args.back! (fuel - 1)])
  for (logical, ctor) in #[(``And, ``Condition.and), (``Or, ``Condition.or)] do
    if head.isConstOf logical then
      return ← check (← mkAppM ctor
        #[← condition args[0]! (fuel - 1), ← condition args[1]! (fuel - 1)])
  for (rel, ctor) in #[(``LE.le, ``Condition.le), (``LT.lt, ``Condition.lt),
      (``Eq, ``Condition.eq)] do
    if head.isConstOf rel && args.size ≥ 2 then
      let saved ← saveState
      try
        return ← check (← mkAppM ctor #[args[args.size - 2]!, args.back!])
      catch _ => saved.restore
  if let some unfolded ← unfoldDefinition? e then
    if unfolded != e then return ← check (← condition unfolded (fuel - 1))
  throwError "The side condition is not a comparison of numbers"

/-- Build a certificate of the closed claim grammar; no arbitrary-Prop fallback exists. -/
private partial def encodeWith (levels : List Level) (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "Connection conclusion unfolding exceeded its limit"
  let e ← instantiateMVars e
  if e.getAppFn.isConstOf ``Statement then
    return ← certified levels e e.getAppArgs.back!
  if let .forallE n ty body bi := e then
    return ← withLocalDecl n bi ty fun x => do
      let p ← encodeWith levels (body.instantiate1 x) (fuel - 1)
      -- A binder over `Type` (a sort other than `Prop`) is a binder over families' types.
      let ctor ← if ← isProp ty then pure ``ConnectionClaim.assuming
        else if (← whnf ty) matches .sort (.succ _) then pure ``ConnectionClaim.allType
        else pure ``ConnectionClaim.all
      certified levels e (← build ctor #[← mkLambdaFVars #[x] p] (← claimType levels e))
  let args := e.getAppArgs
  let head := e.getAppFn
  if head.isConstOf ``Not then
    return ← certified levels e (← build ``ConnectionClaim.not #[← encodeWith levels args.back! (fuel - 1)]
      (← claimType levels e))
  for (logical, ctor) in #[(``And, ``ConnectionClaim.and), (``Or, ``ConnectionClaim.or),
      (``Iff, ``ConnectionClaim.iff)] do
    if head.isConstOf logical then
      if head.isConstOf ``Iff then
        let left := args[0]!
        if left.getAppFn.isConstOf ``Membership.mem then
          let xs := left.getAppArgs
          if let some p ← endpoint? xs[xs.size - 2]! then
            let x := xs.back!
            let other ← withLocalDeclD `x (← inferType x) fun y => mkLambdaFVars #[y] args[1]!
            if let some proof ← atomic? levels e
                #[``ConnectionClaim.memberIff, ``ConnectionClaim.memberIffSwap] #[x, other, p] then
              return proof
        -- The right side is a claim, or else a side condition characterizing the left side.
        let left ← encodeWith levels args[0]! (fuel - 1)
        let saved ← saveState
        let right? ← try some <$> encodeWith levels args[1]! (fuel - 1) catch _ => do
          saved.restore
          pure none
        if let some right := right? then
          return ← certified levels e (← build ctor #[left, right] (← claimType levels e))
        return ← certified levels e (← build ``ConnectionClaim.iffCondition
          #[left, ← condition args[1]!] (← claimType levels e))
      return ← certified levels e (← build ctor #[← encodeWith levels args[0]! (fuel - 1),
        ← encodeWith levels args[1]! (fuel - 1)] (← claimType levels e))
  if head.isConstOf ``Exists then
    return ← lambdaTelescope args.back! fun xs body => do
      let saved ← saveState
      try
        let p ← encodeWith levels body (fuel - 1)
        certified levels e (← build ``ConnectionClaim.exists #[← mkLambdaFVars xs p] (← claimType levels e))
      catch ex =>
        -- `∃ i, A i ∧ P i`: a side condition `A i` guards the witness of the claim `P i`.
        saved.restore
        unless body.isAppOf ``And do throw ex
        let some guard ← (try some <$> condition body.getAppArgs[0]! catch _ => pure none) |
          throw ex
        let p ← encodeWith levels body.getAppArgs[1]! (fuel - 1)
        certified levels e (← build ``ConnectionClaim.existsGuard
          #[← mkLambdaFVars xs guard, ← mkLambdaFVars xs p] (← claimType levels e))
  if head.isConstOf ``Eq || head.isConstOf ``LE.le || head.isConstOf ``Set.Subset then
    let a := args[args.size - 2]!
    let b := args.back!
    if head.isConstOf ``Eq && (← whnf (← inferType a)).getAppFn.isConstOf ``sInfHom then
      if let some proof ← atomic? levels e
          #[``ConnectionClaim.mapsEq, ``ConnectionClaim.mapsEqSwap] #[a, b] then
        return proof
    let eq := head.isConstOf ``Eq
    if let some p ← endpoint? a then
      if let some proof ← atomic? levels e
          (if eq then #[``ConnectionClaim.eqLeft, ``ConnectionClaim.eqLeftSwap]
            else #[``ConnectionClaim.leLeft, ``ConnectionClaim.leLeftSwap]) #[p] then
        return proof
    if let some p ← endpoint? b then
      if let some proof ← atomic? levels e
          (if eq then #[``ConnectionClaim.eqRight, ``ConnectionClaim.eqRightSwap]
            else #[``ConnectionClaim.leRight, ``ConnectionClaim.leRightSwap]) #[p] then
        return proof
  if head.isConstOf ``Membership.mem then
    if let some p ← endpoint? args[args.size - 2]! then
      if let some proof ← atomic? levels e
          #[``ConnectionClaim.member, ``ConnectionClaim.memberSwap] #[p] then
        return proof
  if let some unfolded ← unfoldDefinition? e then
    if unfolded != e then return ← certified levels e (← encodeWith levels unfolded (fuel - 1))
  throwError "The conclusion is not in the closed connection grammar"

/-- Infer one pair of endpoint universes for the entire certificate. Atomic alternatives are
checked against that pair, including its reverse, rather than certifying each branch in isolation. -/
def encode (e : Expr) (fuel : Nat := 32) : MetaM Expr := do
  -- Caller-owned levels (including `Type*` parameters) must never be specialized by the
  -- certificate search. Only otherwise unconstrained levels created for the certificate default.
  withNewMCtxDepth do
    let existing := (← getMCtx).lDecls
    let .const _ levels ← certConst ``ConnectionClaim | throwError "Connection grammar expected"
    let shape ← instantiateMVars (← encodeWith levels e fuel)
    for level in (collectLevelMVars {} shape).result do
      unless existing.contains level do assignLevelMVar level .zero
    instantiateMVars shape

end powerlib.TMIO.ClaimElab

/-- The ordinary notation inside this term must compile to a genuine connection claim.
The generated certificate is checked again by Lean's kernel. -/
elab "connection% " p:term : term => do
  let prop ← elabTermEnsuringType p (mkSort .zero)
  synthesizeSyntheticMVarsNoPostponing
  let prop ← instantiateMVars prop
  let shape ← powerlib.TMIO.ClaimElab.encode prop
  let .const _ levels := (← inferType shape).getAppFn |
    throwError "Connection grammar certificate expected"
  return mkApp2 (mkConst ``powerlib.TMIO.Statement levels) prop shape
