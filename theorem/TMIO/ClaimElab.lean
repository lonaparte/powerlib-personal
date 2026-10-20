import theorem.TMIO.Claim
import theorem.TMIO.Relation
import Lean

/-! # Elaboration of connection claims (foundation)

Compile ordinary connection notation to the closed kernel-checked grammar. This is
untrusted elaboration: a mistaken compiler cannot produce a well-typed certificate.

Scope.
* Lean meta-programming over the grammar of `theorem/TMIO/Claim.lean`; no mathematics. No names
  or tags of model families are trusted: aliases are unfolded until a typed map application or a
  structural powerset operation is reached, and there is no arbitrary-proposition fallback.

Source: the closed grammar `Endpoint`, `ConnectionClaim`, `Statement`
(`theorem/TMIO/Claim.lean`) and the semantic constructors of `theorem/TMIO/Relation.lean`; the
admission rules of `Rules.md` §3a (`connection% (ordinary proposition)` constructs the
certificate, which Lean's kernel checks).

Results.
* `endpoint?`: an `Endpoint` certificate for a value, if one exists.
* `endpointInputs?`: the inputs and structural maps of an endpoint, derived from its certificate,
  so that an identity map cannot launder a behavioural set.
* `encode`: a `ConnectionClaim` certificate of a proposition.
* The term elaborator `connection% P`: the `TMIO.Statement` of `P` with its generated certificate,
  checked again by the kernel; the trace class `powerlib.claim`.
-/

open Lean Meta Elab Term

namespace powerlib.TMIO.ClaimElab

initialize registerTraceClass `powerlib.claim

private def certConst (name : Name) : MetaM Expr := do
  let info ← getConstInfo name
  return mkConst name (info.levelParams.map fun p => if p == `w then .succ .zero else .zero)

private def endpointType (value : Expr) (u v : Level) : MetaM Expr := do
  return mkApp2 (mkConst ``Endpoint [u,v]) (← inferType value) value

private def claimType (prop : Expr) : MetaM Expr := do
  return mkApp (← certConst ``ConnectionClaim) prop

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
          let ctor := if obj.getAppFn.isConstOf ``OrderDual.ofDual then ``Endpoint.dual else ``Endpoint.toDual
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

private def certified (prop proof : Expr) : MetaM Expr := do
  let target ← claimType prop
  unless ← isDefEq (← inferType proof) target do
    throwError "Connection grammar certificate does not describe the requested proposition"
  return ← instantiateMVars proof

/-- Build a certificate of the closed claim grammar; no arbitrary-Prop fallback exists. -/
partial def encode (e : Expr) (fuel : Nat := 32) : MetaM Expr := do
  if fuel == 0 then throwError "Connection conclusion unfolding exceeded its limit"
  let e ← instantiateMVars e
  if e.getAppFn.isConstOf ``Statement then return e.getAppArgs.back!
  if let .forallE n ty body bi := e then
    return ← withLocalDecl n bi ty fun x => do
      let p ← encode (body.instantiate1 x) (fuel - 1)
      let ctor := if ← isProp ty then ``ConnectionClaim.assuming else ``ConnectionClaim.all
      certified e (← build ctor #[← mkLambdaFVars #[x] p] (← claimType e))
  let args := e.getAppArgs
  let head := e.getAppFn
  if head.isConstOf ``Not then
    return ← certified e (← build ``ConnectionClaim.not #[← encode args.back! (fuel - 1)] (← claimType e))
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
            return ← certified e (← build ``ConnectionClaim.memberIff #[x, other, p] (← claimType e))
      return ← certified e (← build ctor #[← encode args[0]! (fuel - 1),
        ← encode args[1]! (fuel - 1)] (← claimType e))
  if head.isConstOf ``Exists then
    return ← lambdaTelescope args.back! fun xs body => do
      let p ← encode body (fuel - 1)
      certified e (← build ``ConnectionClaim.exists #[← mkLambdaFVars xs p] (← claimType e))
  if head.isConstOf ``Eq || head.isConstOf ``LE.le || head.isConstOf ``Set.Subset then
    let a := args[args.size - 2]!
    let b := args.back!
    if head.isConstOf ``Eq && (← whnf (← inferType a)).getAppFn.isConstOf ``sInfHom then
      return ← certified e (← build ``ConnectionClaim.mapsEq #[a, b] (← claimType e))
    let eq := head.isConstOf ``Eq
    if let some p ← endpoint? a then
      return ← certified e (← build (if eq then ``ConnectionClaim.eqLeft else ``ConnectionClaim.leLeft) #[p] (← claimType e))
    if let some p ← endpoint? b then
      return ← certified e (← build (if eq then ``ConnectionClaim.eqRight else ``ConnectionClaim.leRight) #[p] (← claimType e))
  if head.isConstOf ``Membership.mem then
    if let some p ← endpoint? args[args.size - 2]! then
      return ← certified e (← build ``ConnectionClaim.member #[p] (← claimType e))
  if let some unfolded ← unfoldDefinition? e then
    if unfolded != e then return ← certified e (← encode unfolded (fuel - 1))
  throwError "The conclusion is not in the closed connection grammar"

end powerlib.TMIO.ClaimElab

/-- The ordinary notation inside this term must compile to a genuine connection claim.
The generated certificate is checked again by Lean's kernel. -/
elab "connection% " p:term : term => do
  let prop ← elabTermEnsuringType p (mkSort .zero)
  synthesizeSyntheticMVarsNoPostponing
  let prop ← instantiateMVars prop
  let shape ← powerlib.TMIO.ClaimElab.encode prop
  return mkApp2 (mkConst ``powerlib.TMIO.Statement [.zero, .zero, .succ .zero]) prop shape
