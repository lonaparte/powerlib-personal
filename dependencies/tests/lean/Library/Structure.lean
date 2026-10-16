import powerlib

/-! # Library structure checks

Structural checks of the `theorem/` library beyond admission, read from the built environment of
`powerlib`. Each check logs `POWERLIB_LIBRARY_<NAME>_OK` or fails with the list of violations.

* `LAYERS`: every `theorem.*` module belongs to exactly one layer of the table below: the codex
  shared layer, generic mathematics, or engineering models. A new module is registered by its
  directory or by its own name; a new directory must be registered before it builds.
* `DEPENDENCIES`: a generic module imports no engineering-model module directly, and a codex
  module imports only codex modules (the shared layer stays self-contained).
* `BARE_BEHAVIOUR`: no public theorem outside `TMIO.Statement` applies a behavioural predicate of
  the semantic layer (`theorem/Flow/Defs.lean`, `theorem/Port/Defs.lean`, and the upstream
  predicates they are built from) to an argument mentioning a constant of an engineering-model
  module. Admission recognizes models by their `Family` types; this check also covers model
  fields, parameters and states that no family reads.
* `HEADERS`: the module docstring of every non-codex module starts with a `# ` title and contains
  `Source:`, `Results` and `Scope.` or `Model boundary.`; a module defining a `Family` value also
  contains `Family and connection conclusions`.
* `DUPLICATES`: no two public theorems of different non-codex modules have α-equivalent
  statements (universe parameters compared by position).

The layer table is the structural specification: moving a module across layers or adding a
directory changes this file. It classifies knowledge (shared framework, generic mathematics,
engineering content), not TMIO layers: an engineering module may organize models (M) or
implementations under realistic constraints (I), and `Library/TMIOIndex.lean` files its
connection statements by TMIO layer. -/

namespace LibraryStructure

open Lean Meta Elab Command

inductive Layer where
  | codex | generic | engineering
  deriving BEq, Inhabited

def Layer.label : Layer → String
  | .codex => "codex" | .generic => "generic" | .engineering => "engineering"

/-! ## Layer table -/

/-- The codex shared layer: the TMIO framework, families, the semantic layer, admission and the
codex reference models. Registered module by module. -/
def codexModules : Array Name := #[
  `theorem.Architecture, `theorem.Attributes, `theorem.LibrarySearch,
  `theorem.Circuits.Interconnection, `theorem.Circuits.LCL, `theorem.Circuits.LCLSynthesis,
  `theorem.Circuits.RL, `theorem.Circuits.RLMeasurement,
  `theorem.Data.Analysis, `theorem.Family.Basic,
  `theorem.Flow.Basic, `theorem.Flow.Certificate, `theorem.Flow.Defs,
  `theorem.Linear.Certificate, `theorem.Linear.Coordinates, `theorem.Linear.Family,
  `theorem.Linear.Jordan, `theorem.Linear.Plant, `theorem.Linear.Positive, `theorem.Linear.Rate,
  `theorem.Linear.Rational, `theorem.Linear.Realization, `theorem.Linear.Stability,
  `theorem.Linear.Synthesis, `theorem.Linear.Transfer, `theorem.Linear.VerifiedSynthesis,
  `theorem.Map.Defs,
  `theorem.Nonlinear.Cubic, `theorem.Nonlinear.Polynomial2,
  `theorem.Port.Basic, `theorem.Port.Defs, `theorem.Port.Linear, `theorem.Port.PortHamiltonian,
  `theorem.TMIO.Claim, `theorem.TMIO.ClaimElab, `theorem.TMIO.Compare, `theorem.TMIO.Derived,
  `theorem.TMIO.Generate, `theorem.TMIO.Instances.Finite, `theorem.TMIO.Relation,
  `theorem.TMIO.Representation,
  `theorem.generated.Conversion, `theorem.generated.ImpedanceInterconnection,
  `theorem.generated.LCLConversion]

/-- Generic mathematics: statements about arbitrary fields, matrices, polynomials, processes,
graphs and functions, with no engineering model. An entry is a directory (the modules directly
in it) or a single module.
* `Transform`: coordinate transformations and unit bases (Clarke, Park, space vectors, complex
  power in dq, per-unit scaling, circulant line matrices) are identities, not models.
* `Network`: only the graph and node-network modules (weighted Laplacians, synchronization of
  identical nodes, linear node networks); the power-flow and frequency-divider modules and
  `Network/Swing/` are models.
* `Numerics`: numerical methods; the EMT discretizations of circuit models in `Numerics/EMT/`
  are models.
* `PH`: generic port-Hamiltonian theory, including the mathematical counterexample family of
  `PH/Structure` (a tilted double well) and the lossless LC counterexample of `PH/Observability`;
  concrete circuit instances are in `PH/Models/`.
* `Spectral`: the spectral family template, parametrized by an arbitrary model type.
* `Stack`: the four-layer stack of models, implementations and records over arbitrary families.
* `Map.Basic`, `Map.Linearization`: general facts of the discrete-time semantic layer
  (`Map.Defs`, codex layer), registered module by module.
* `Linear.EigenMap`: eigenvalue maps of matrices (polynomial and Möbius images), general linear
  algebra beside the codex `Linear.*` modules, registered module by module. -/
def genericEntries : Array Name := #[
  `theorem.Asymptotics, `theorem.Asymptotics.Guard, `theorem.Averaging, `theorem.Criteria,
  `theorem.DAE, `theorem.Delay, `theorem.Dynamics, `theorem.Dynamics.Degenerate,
  `theorem.Dynamics.LaSalle, `theorem.Estimation, `theorem.Information, `theorem.LTI,
  `theorem.Linear.EigenMap, `theorem.LinearAlgebra, `theorem.Map.Basic,
  `theorem.Map.Linearization, `theorem.Modal,
  `theorem.Network.LinearSync, `theorem.Network.Synchronization, `theorem.Network.WeightedLaplacian,
  `theorem.NormalForm, `theorem.Numerics, `theorem.PDE, `theorem.PH, `theorem.ParametricResonance,
  `theorem.Periodic, `theorem.PhasePlane, `theorem.Potential, `theorem.SingularPerturbation,
  `theorem.SpecialFunctions, `theorem.Spectral, `theorem.Stack, `theorem.Stochastic,
  `theorem.Transform]

/-- Engineering models of power electronics and power systems: model families, their connection
conclusions and the static evidence about them. -/
def engineeringEntries : Array Name := #[
  `theorem.CurrentControl, `theorem.Drives, `theorem.Frequency,
  `theorem.GFL, `theorem.GFL.DCLink, `theorem.GFL.Impedance, `theorem.GFL.LCLine,
  `theorem.GFL.Noise, `theorem.GFL.Parametric, `theorem.GFL.PowerLoop,
  `theorem.GFM, `theorem.GFM.Matching, `theorem.Limiting, `theorem.Line,
  `theorem.Network.FrequencyDivider, `theorem.Network.PowerFlow, `theorem.Network.Swing,
  `theorem.Numerics.EMT, `theorem.PH.Models, `theorem.PLL, `theorem.Synchronous]

/-- The registrations of a module: its own name in any table, or its directory in the generic
or engineering table. -/
def registrations (m : Name) : Array Layer := Id.run do
  let mut out := #[]
  if codexModules.contains m then out := out.push .codex
  for (layer, entries) in #[(Layer.generic, genericEntries), (Layer.engineering, engineeringEntries)] do
    if entries.contains m then out := out.push layer
    if entries.contains m.getPrefix then out := out.push layer
  return out

def layerOf? (m : Name) : Option Layer :=
  match registrations m with
  | #[layer] => some layer
  | _ => none

def libraryModules (env : Environment) : Array (Nat × Name) := Id.run do
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m.getRoot == `theorem then out := out.push (i, m)
  return out

def report (header : String) (violations : Array String) : CommandElabM Unit := do
  unless violations.isEmpty do
    throwError "{header} ({violations.size}):\n{"\n".intercalate violations.toList}"

/-- Authored public theorems: compiler and equation auxiliaries carry no declaration range. -/
def authoredPublic (env : Environment) (name : Name) : Bool :=
  !isPrivateName name && (declRangeExt.find? env name).isSome

def statementType : Expr → Bool
  | .forallE _ _ body _ => statementType body
  | e => e.isAppOf ``powerlib.TMIO.Statement

/-! ## Bare behaviour detection -/

/-- The model constants used by arguments of behavioural predicates in `e`. -/
partial def bareUses (notions : NameSet) (isModel : Name → Bool) (e : Expr) : Array Name :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let here := match fn with
      | .const c _ =>
        if notions.contains c then
          args.foldl (fun acc a => acc ++ a.getUsedConstants.filter isModel) #[]
        else #[]
      | _ => #[]
    args.foldl (fun acc a => acc ++ bareUses notions isModel a) (here ++ bareUses notions isModel fn)
  | .lam _ t b _ | .forallE _ t b _ => bareUses notions isModel t ++ bareUses notions isModel b
  | .letE _ t v b _ =>
    bareUses notions isModel t ++ bareUses notions isModel v ++ bareUses notions isModel b
  | .mdata _ b | .proj _ _ b => bareUses notions isModel b
  | _ => #[]

/-- The behavioural predicates: the notions of the semantic layer, as recognized by the
single-semantics audit, and the upstream behavioural predicates their definitions use. -/
def behaviouralNotions : MetaM NameSet := do
  let env ← getEnv
  let ctx ← powerlib.Architecture.context
  let mut local_ : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    unless SemanticAudit.semanticLayer.contains env.header.moduleNames[i]! do continue
    for c in env.header.moduleData[i]!.constNames do
      if ← SemanticAudit.behavioural ctx c then local_ := local_.push c
  let mut notions : NameSet := local_.foldl (·.insert ·) {}
  for c in local_ do
    let some (.defnInfo v) := env.find? c | continue
    for d in v.value.getUsedConstants do
      if !SemanticAudit.inLibrary env d && !notions.contains d then
        if ← SemanticAudit.behavioural ctx d then notions := notions.insert d
  return notions

/-- Fixtures for the detector: a closed field and a generic one. -/
private def fixtureField (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) := -x

private theorem fixtureBare :
    powerlib.Flow.Property.lyapunovStable.holds fixtureField 0 → True := fun _ => trivial

private theorem fixtureGeneric (f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) :
    powerlib.Flow.Property.lyapunovStable.holds f 0 → True := fun _ => trivial

/-! ## Module headers -/

/-- The missing items of a module header. -/
def headerGaps (doc : String) (definesFamily : Bool) : Array String := Id.run do
  let has (part : String) := (doc.splitOn part).length > 1
  let mut gaps := #[]
  unless doc.trimAsciiStart.startsWith "# " do gaps := gaps.push "`# ` title first"
  for item in #["Source:", "Results"] do
    unless has item do gaps := gaps.push item
  unless has "Scope." || has "Model boundary." do gaps := gaps.push "Scope. or Model boundary."
  if definesFamily && !has "Family and connection conclusions" then
    gaps := gaps.push "Family and connection conclusions"
  return gaps

/-- A definition whose value is a model family (structure projections, such as the families of
a `Stack`, are not values). -/
def isFamilyValue (name : Name) : MetaM Bool := do
  if (← getEnv).isProjectionFn name then return false
  let some (.defnInfo v) := (← getEnv).find? name | return false
  forallTelescopeReducing v.type fun _ body => return (← whnf body).isAppOf ``powerlib.Family

/-! ## Duplicate statements -/

/-- Groups of α-equivalent statements from different modules, given `(name, module, type)`. -/
def duplicates (decls : Array (Name × Name × Expr)) : Array (Array (Name × Name)) := Id.run do
  let mut buckets : Std.HashMap UInt64 (Array (Name × Name × Expr)) := {}
  for d in decls do
    buckets := buckets.alter d.2.2.hash fun b => some ((b.getD #[]).push d)
  let mut groups := #[]
  for (_, bucket) in buckets.toList do
    let mut seen : Array Nat := #[]
    for i in [:bucket.size] do
      if seen.contains i then continue
      let mut group := #[(bucket[i]!.1, bucket[i]!.2.1)]
      for j in [i+1:bucket.size] do
        if !seen.contains j && bucket[j]!.2.2.eqv bucket[i]!.2.2 then
          seen := seen.push j
          group := group.push (bucket[j]!.1, bucket[j]!.2.1)
      let modules := group.foldl (fun (ms : Array Name) g =>
        if ms.contains g.2 then ms else ms.push g.2) #[]
      if modules.size > 1 then groups := groups.push group
  return groups

/-- The statement of a theorem with its universe parameters named by position. -/
def positionalType (info : ConstantInfo) : Expr :=
  info.type.instantiateLevelParams info.levelParams
    ((List.range info.levelParams.length).map fun i => .param (Name.mkSimple s!"u_{i}"))

end LibraryStructure

open Lean Meta Elab Command LibraryStructure

/-! ## Checks -/

run_cmd do
  let env ← getEnv
  let modules := libraryModules env
  let mut violations := #[]
  let mut counts : Array Nat := #[0, 0, 0]
  for (_, m) in modules do
    match registrations m with
    | #[layer] =>
      let k := match layer with | .codex => 0 | .generic => 1 | .engineering => 2
      counts := counts.modify k (· + 1)
    | #[] => violations := violations.push s!"{m}: unregistered (add its directory to a layer)"
    | layers => violations := violations.push s!"{m}: registered in {layers.map (·.label)}"
  -- Every entry names an existing module or directory.
  let names := modules.map (·.2)
  for entry in codexModules ++ genericEntries ++ engineeringEntries do
    unless names.any (fun m => m == entry || m.getPrefix == entry) do
      violations := violations.push s!"{entry}: registered but no such module or directory"
  report "Library modules outside the layer table" violations
  logInfo m!"POWERLIB_LIBRARY_LAYERS_OK: {modules.size} modules; codex {counts[0]!}, \
    generic {counts[1]!}, engineering {counts[2]!}"

run_cmd do
  let env ← getEnv
  let mut violations := #[]
  let mut generic : Nat := 0
  let mut codex : Nat := 0
  for (i, m) in libraryModules env do
    let some layer := layerOf? m | continue
    if layer == .generic then generic := generic + 1
    if layer == .codex then codex := codex + 1
    for imp in env.header.moduleData[i]!.imports do
      let target := layerOf? imp.module
      if layer == .generic && target == some .engineering then
        violations := violations.push s!"{m} imports {imp.module}"
      if layer == .codex && (target == some .generic || target == some .engineering) then
        violations := violations.push s!"{m} (codex) imports {imp.module}"
  report "Modules importing a higher layer" violations
  logInfo m!"POWERLIB_LIBRARY_DEPENDENCIES_OK: {generic} generic modules import no engineering \
    module; {codex} codex modules import only codex modules"

run_cmd liftTermElabM do
  let env ← getEnv
  let notions ← behaviouralNotions
  -- The predicates named by the semantic layer must all be recognized.
  for c in #[``powerlib.Flow.Property.holds, ``LyapunovStable, ``LocalAsymptoticStable,
      ``LocallyExponentiallyStable, ``Unstable, ``powerlib.Flow.GloballyAsymptoticallyStable,
      ``powerlib.Flow.GloballyExponentiallyStable, ``powerlib.Flow.Decay,
      ``powerlib.Flow.SampledContraction, ``powerlib.Flow.Conservative,
      ``powerlib.Port.System.Passive, ``powerlib.Port.System.PassiveWith,
      ``powerlib.Flow.Property.holdsMap, ``powerlib.Map.LyapunovStable,
      ``powerlib.Map.LocalAsymptoticStable, ``powerlib.Map.LocallyExponentiallyStable,
      ``powerlib.Map.GloballyAsymptoticallyStable, ``powerlib.Map.GloballyExponentiallyStable,
      ``powerlib.Map.Unstable, ``powerlib.Map.Decay, ``powerlib.Map.SampledContraction,
      ``powerlib.Map.Conservative, ``powerlib.Map.System.Passive,
      ``powerlib.Map.System.PassiveWith, ``powerlib.Sentence.holds] do
    unless notions.contains c do throwError "Behavioural predicate not recognized: {c}"
  -- Controls: a closed field is detected, a quantified one is not.
  let fixture := ``fixtureField
  if (bareUses notions (· == fixture) (← getConstInfo ``fixtureBare).type).isEmpty then
    throwError "The detector missed behaviour of a closed field"
  unless (bareUses notions (· == fixture) (← getConstInfo ``fixtureGeneric).type).isEmpty do
    throwError "The detector flagged behaviour of a quantified field"
  let mut modelModules : Std.HashSet Nat := {}
  let mut scanned : Nat := 0
  for (i, m) in libraryModules env do
    if layerOf? m == some .engineering then modelModules := modelModules.insert i
  let isModel (c : Name) : Bool := (env.getModuleIdxFor? c).any (modelModules.contains ·.toNat)
  let mut violations := #[]
  for (i, m) in libraryModules env do
    for name in env.header.moduleData[i]!.constNames do
      let some (.thmInfo v) := env.find? name | continue
      unless authoredPublic env name && !statementType v.type do continue
      scanned := scanned + 1
      let uses := (bareUses notions isModel v.type).foldl
        (fun (us : Array Name) u => if us.contains u then us else us.push u) #[]
      unless uses.isEmpty do
        violations := violations.push s!"{name} in {m}: behaviour of {uses}"
  unless violations.isEmpty do
    throwError "Public behaviour of model constants outside connection statements \
      ({violations.size}):\n{"\n".intercalate violations.toList}"
  logInfo m!"POWERLIB_LIBRARY_BARE_BEHAVIOUR_OK: {scanned} public non-statement theorems; \
    {notions.size} behavioural predicates; no behaviour of a model constant"

run_cmd liftTermElabM do
  let env ← getEnv
  let mut violations := #[]
  let mut checked : Nat := 0
  let mut families : Nat := 0
  for (i, m) in libraryModules env do
    if layerOf? m == some .codex then continue
    checked := checked + 1
    let definesFamily ← env.header.moduleData[i]!.constNames.anyM fun c => isFamilyValue c
    if definesFamily then families := families + 1
    match (getModuleDoc? env m).bind (·[0]?) with
    | none => violations := violations.push s!"{m}: no module docstring"
    | some doc =>
      let gaps := headerGaps doc.doc definesFamily
      unless gaps.isEmpty do violations := violations.push s!"{m}: missing {gaps}"
  unless violations.isEmpty do
    throwError "Module headers not in the library format ({violations.size}):\n\
      {"\n".intercalate violations.toList}"
  logInfo m!"POWERLIB_LIBRARY_HEADERS_OK: {checked} non-codex module headers, \
    {families} defining families"

run_cmd do
  let env ← getEnv
  -- Control: statements differing only in binder names are equal.
  let a ← liftTermElabM <| return (← getConstInfo ``fixtureGeneric).type
  let renamed := match a with
    | .forallE _ d body bi => Expr.forallE `g d body bi
    | e => e
  unless (duplicates #[(`a, `A, a), (`b, `B, renamed)]).size == 1 do
    throwError "The duplicate detector missed an α-equivalent statement"
  let mut decls := #[]
  for (i, m) in libraryModules env do
    if layerOf? m == some .codex then continue
    for name in env.header.moduleData[i]!.constNames do
      let some info@(.thmInfo _) := env.find? name | continue
      unless authoredPublic env name do continue
      decls := decls.push (name, m, positionalType info)
  let groups := duplicates decls
  report "Identical public statements in different modules" (groups.map fun g =>
    ", ".intercalate (g.map fun (n, m) => s!"{n} ({m})").toList)
  logInfo m!"POWERLIB_LIBRARY_DUPLICATES_OK: {decls.size} public theorems of non-codex modules, \
    no two statements identical"
