import powerlib

/-! # Library structure checks

Structural checks of the `theorem/` library beyond admission, read from the built environment of
`powerlib`. Each check logs `POWERLIB_LIBRARY_<NAME>_OK` or fails with the list of violations.

* `LAYERS`: every `theorem.*` module belongs to exactly one layer of the table below: generic
  mathematics (with the framework: TMIO, families, the semantic layer, linear systems) or
  engineering models. A new module is registered by its directory or by its own name; a new
  directory must be registered before it builds.
* `DEPENDENCIES`: a generic module imports no engineering-model module directly.
* `BARE_BEHAVIOUR`: no public theorem outside `TMIO.Statement` applies a behavioural predicate of
  the semantic layer (`theorem/Flow/Defs.lean`, `theorem/Port/Defs.lean`, and the upstream
  predicates they are built from) to an argument mentioning a constant of an engineering-model
  module. Admission recognizes models by their `Family` types; this check also covers model
  fields, parameters and states that no family reads.
* `HEADERS`: the module docstring of every module starts with a `# ` title and contains
  `Source:`, `Results` and `Scope.` or `Model boundary.`; a module defining a `Family` value also
  contains `Family and connection conclusions`.
* `DUPLICATES`: no two public theorems of different modules have α-equivalent
  statements (universe parameters compared by position).
* `RESTATEMENTS`: no theorem, public or private, states an instance of (or
  the same as) another theorem of the library that it could use — one in its own module or in a
  module that does not import it, not private to another module — without using it, directly,
  through intermediate theorems, or through a theorem at least as general; a theorem that is a
  stepping stone of the other is not a restatement. The remaining cases are listed with their
  reasons in `restatementExemptions`.
* `SCAFFOLDS`: a module with a public connection statement between contents — one whose
  proposition uses two model families, an implementation or stack, or an observation seed, each
  defined outside the framework (`TMIO`, `Family`, `Spectral`, `Stack`), or one that changes the
  representation inside a family — cites in its docstrings an Agda scaffold `theorem/<Name>.agda`
  whose row in the scaffold table of `Architecture.md` names the module (`Dir/Module`). Every
  cited scaffold exists, and every scaffold in `theorem/` is cited by some module and has a row.
  A change of representation inside one family is a statement whose claim is an iff or an
  equality with the same family's denotation of the same sentence on both sides and different
  models (`x ∈ F.den s ↔ g x ∈ F.den s`). The Lean names a scaffold's comments cite are public
  declarations or library modules. Run from the repository root.

The layer table is the structural specification: moving a module across layers or adding a
directory changes this file. It classifies knowledge (generic mathematics and the framework,
engineering content), not TMIO layers: an engineering module may organize models (M) or
implementations under realistic constraints (I), and `Library/TMIOIndex.lean` files its
connection statements by TMIO layer. -/

namespace LibraryStructure

open Lean Meta Elab Command

inductive Layer where
  | generic | engineering
  deriving BEq, Inhabited

def Layer.label : Layer → String
  | .generic => "generic" | .engineering => "engineering"

/-! ## Layer table -/

/-- Generic mathematics: statements about arbitrary fields, matrices, polynomials, processes,
graphs and functions, with no engineering model, and the framework that reads them: the TMIO
connections (`TMIO`), model families (`Family`), the semantic layer (`Flow`, `Map`, `Port`), linear
systems (`Linear`), the polynomial example families (`Nonlinear`), data analysis (`Data`), admission
and search (`Architecture`, `Attributes`, `LibrarySearch`). An entry is a directory (the modules
directly in it) or a single module.
* `Circuits.Interconnection` (and its generated block matrices): the interconnection of a source
  and a load plant with ports is linear-systems theory; the circuit models of `Circuits/` are
  engineering.
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
* `Stack`: the four-layer stack of models, implementations and records over arbitrary families. -/
def genericEntries : Array Name := #[
  `theorem.Architecture, `theorem.Attributes, `theorem.LibrarySearch,
  `theorem.Asymptotics, `theorem.Asymptotics.Guard, `theorem.Averaging,
  `theorem.Circuits.Interconnection, `theorem.Criteria, `theorem.DAE, `theorem.Data,
  `theorem.Delay, `theorem.Dynamics, `theorem.Dynamics.Degenerate, `theorem.Dynamics.LaSalle,
  `theorem.Estimation, `theorem.Family, `theorem.Flow, `theorem.Information, `theorem.LTI,
  `theorem.Linear, `theorem.LinearAlgebra, `theorem.Map, `theorem.Modal,
  `theorem.Network.LinearSync, `theorem.Network.Synchronization, `theorem.Network.WeightedLaplacian,
  `theorem.Nonlinear, `theorem.NormalForm, `theorem.Numerics, `theorem.PDE, `theorem.PH,
  `theorem.ParametricResonance, `theorem.Periodic, `theorem.PhasePlane, `theorem.Port,
  `theorem.Potential, `theorem.SingularPerturbation, `theorem.SpecialFunctions, `theorem.Spectral,
  `theorem.Stack, `theorem.Stochastic, `theorem.TMIO, `theorem.TMIO.Instances, `theorem.Transform,
  `theorem.generated.ImpedanceInterconnection]

/-- Engineering models of power electronics and power systems: model families, their connection
conclusions and the static evidence about them, including the circuit models of `Circuits/` (RL
branch, LCL filter) and their generated parameter conversions. -/
def engineeringEntries : Array Name := #[
  `theorem.Circuits.LCL, `theorem.Circuits.LCLSynthesis, `theorem.Circuits.PortEuler,
  `theorem.Circuits.RL, `theorem.Circuits.RLMeasurement, `theorem.generated.Conversion, `theorem.generated.LCLConversion,
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

/-- A definition whose value, as a function of its parameters, is an application of `head`
(structure projections, such as the families of a `Stack`, are not values). -/
def isValueOf (head name : Name) : MetaM Bool := do
  if (← getEnv).isProjectionFn name then return false
  let some (.defnInfo v) := (← getEnv).find? name | return false
  forallTelescopeReducing v.type fun _ body => return (← whnf body).isAppOf head

/-- A definition whose value is a model family. -/
def isFamilyValue (name : Name) : MetaM Bool := isValueOf ``powerlib.Family name

/-! ## Scaffolds -/

/-- Modules of the framework: their families, implementations and seeds are constructions over
arbitrary contents, not contents. -/
def frameworkModule (m : Name) : Bool :=
  [`theorem.Family, `theorem.TMIO, `theorem.Spectral, `theorem.Stack].any (·.isPrefixOf m)

/-- The contents a value of this definition is: `0` a model family, `1` an implementation or
stack, `2` an observation seed; `none` for anything else. -/
def contentKind (name : Name) : MetaM (Option Nat) := do
  if ← isFamilyValue name then return some 0
  if (← isValueOf ``powerlib.Implementation name) || (← isValueOf ``powerlib.Stack name) then
    return some 1
  if ← isValueOf ``powerlib.TMIO.Seed name then return some 2
  return none

/-- The `(family, sentence)` pairs of the `Family.den` applications in `e`. -/
partial def denApps (e : Expr) : Array (Expr × Expr) :=
  let here := if e.isAppOfArity ``powerlib.Family.den 6 then #[(e.getArg! 4, e.getArg! 5)] else #[]
  match e with
  | .app f a => here ++ denApps f ++ denApps a
  | .lam _ t b _ | .forallE _ t b _ => denApps t ++ denApps b
  | .letE _ t v b _ => denApps t ++ denApps v ++ denApps b
  | .mdata _ b | .proj _ _ b => denApps b
  | _ => here

/-- The body of `e` under its leading binders. -/
def stripForalls : Expr → Expr
  | .forallE _ _ b _ => stripForalls b
  | e => e

/-- A statement that changes the representation inside one family: its claim is an iff or an
equality whose two sides differ and use the denotation of the same family at the same sentence
(`x ∈ F.den s ↔ g x ∈ F.den s`, `F.den s = g ⁻¹' F.den s`). Implications between sentences of
one family are not changes of representation. -/
def representationChange (type : Expr) : Bool := Id.run do
  let body := stripForalls type
  unless body.isAppOf ``powerlib.TMIO.Statement do return false
  let some claim := body.getAppArgs[0]? | return false
  let claim := stripForalls claim
  let sides : Option (Expr × Expr) :=
    if claim.isAppOfArity ``Iff 2 then some (claim.getArg! 0, claim.getArg! 1)
    else if claim.isAppOfArity ``Eq 3 then some (claim.getArg! 1, claim.getArg! 2) else none
  let some (a, b) := sides | return false
  if a == b then return false
  let db := denApps b
  return (denApps a).any fun x => db.any fun y => x.1 == y.1 && x.2 == y.2

/-- The Agda files a text cites, as paths `theorem/….agda`. -/
def scaffoldCitations (text : String) : Array String := Id.run do
  let mut out := #[]
  for part in (text.splitOn "theorem/").drop 1 do
    let chars := part.toList
    let name := chars.takeWhile fun c => c.isAlphanum || c == '/' || c == '_'
    if (chars.drop name.length).take 5 == ".agda".toList then
      let path := s!"theorem/{String.ofList name}.agda"
      unless out.contains path do out := out.push path
  return out

/-- The backticked tokens of the comment lines of an Agda source. -/
def agdaCommentTokens (text : String) : Array String := Id.run do
  let mut out := #[]
  for line in text.splitOn "\n" do
    unless (line.toList.dropWhile (· == ' ')).take 2 == ['-', '-'] do continue
    let parts := (line.splitOn "`").toArray
    for i in [:parts.size] do
      if i % 2 == 1 then out := out.push parts[i]!
  return out

/-- The names an Agda source declares: modules, records and data types, and every name left of
` : ` in a signature, a field or a module parameter. -/
def agdaDeclared (text : String) (acc : Std.HashSet String) : Std.HashSet String := Id.run do
  let mut out := acc
  for line in text.splitOn "\n" do
    let words := (line.splitOn " ").filter (· != "")
    let some first := words.head? | continue
    if first.startsWith "--" then continue
    if ["module", "record", "data"].contains first then
      if let some n := words[1]? then out := out.insert n
    else if words.contains ":" then
      for w in words.takeWhile (· != ":") do
        out := out.insert (String.ofList (w.toList.dropWhile (fun c => c == '(' || c == '{')))
  return out

/-- A token that reads as a Lean name: an ASCII identifier with a namespace, or a long one with an
underscore. Short underscored tokens are notation (`K_R`, `V_dc`), and file names are paths. -/
def leanReference (tok : String) : Bool :=
  let cs := tok.toList
  match cs with
  | [] => false
  | c :: _ =>
    (c.isAlpha || c == '_') &&
    cs.all (fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'') &&
    (cs.contains '.' || (cs.contains '_' && cs.length > 6)) &&
    [".md", ".lean", ".agda", ".py"].all (fun e => !tok.endsWith e)

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
  let mut counts : Array Nat := #[0, 0]
  for (_, m) in modules do
    match registrations m with
    | #[layer] =>
      let k := match layer with | .generic => 0 | .engineering => 1
      counts := counts.modify k (· + 1)
    | #[] => violations := violations.push s!"{m}: unregistered (add its directory to a layer)"
    | layers => violations := violations.push s!"{m}: registered in {layers.map (·.label)}"
  -- Every entry names an existing module or directory.
  let names := modules.map (·.2)
  for entry in genericEntries ++ engineeringEntries do
    unless names.any (fun m => m == entry || m.getPrefix == entry) do
      violations := violations.push s!"{entry}: registered but no such module or directory"
  report "Library modules outside the layer table" violations
  logInfo m!"POWERLIB_LIBRARY_LAYERS_OK: {modules.size} modules; generic {counts[0]!}, \
    engineering {counts[1]!}"

run_cmd do
  let env ← getEnv
  let mut violations := #[]
  let mut generic : Nat := 0
  for (i, m) in libraryModules env do
    let some layer := layerOf? m | continue
    if layer == .generic then generic := generic + 1
    for imp in env.header.moduleData[i]!.imports do
      if layer == .generic && layerOf? imp.module == some .engineering then
        violations := violations.push s!"{m} imports {imp.module}"
  report "Modules importing a higher layer" violations
  logInfo m!"POWERLIB_LIBRARY_DEPENDENCIES_OK: {generic} generic modules import no engineering \
    module"

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
  logInfo m!"POWERLIB_LIBRARY_HEADERS_OK: {checked} module headers, \
    {families} defining families"

run_cmd liftTermElabM do
  let env ← getEnv
  let root ← IO.currentDir
  unless ← (root / "lakefile.lean").pathExists do
    throwError "The scaffold check reads `theorem/`: run the build from the repository root"
  let moduleOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  -- The scaffold table: one row per scaffold, keyed by its path.
  let table ← IO.FS.readFile (root / "Architecture.md")
  let rows : Std.HashMap String String := (table.splitOn "\n").foldl (init := {}) fun acc line =>
    if line.startsWith "| `theorem/" then
      match (line.splitOn "`")[1]? with
      | some path => acc.insert path line
      | none => acc
    else acc
  let mut kinds : NameMap (Option Nat) := {}
  let mut found : Array Nat := #[0, 0, 0, 0]
  let mut violations := #[]
  let mut connected : Nat := 0
  let mut cited : Std.HashSet String := {}
  for (i, m) in libraryModules env do
    let text := " ".intercalate
      (((getModuleDoc? env m).getD #[]).map (·.doc)).toList
    let citations := scaffoldCitations text
    for path in citations do
      cited := cited.insert path
      unless ← (root / path).pathExists do
        violations := violations.push s!"{m}: cites {path}, which does not exist"
    let mut witness : Option (Name × Nat) := none
    for name in env.header.moduleData[i]!.constNames do
      let some (.thmInfo v) := env.find? name | continue
      unless authoredPublic env name && statementType v.type do continue
      let mut uses : Array (Name × Nat) := #[]
      for c in v.type.getUsedConstants do
        let some cm := moduleOf c | continue
        unless cm.getRoot == `theorem && !frameworkModule cm do continue
        let kind ← match kinds.find? c with
          | some k => pure k
          | none => do
            let k ← contentKind c
            kinds := kinds.insert c k
            pure k
        if let some k := kind then uses := uses.push (c, k)
      let families := uses.filter (·.2 == 0)
      if let some (_, k) := uses.find? (·.2 != 0) then witness := some (name, k)
      else if families.size ≥ 2 then witness := some (name, 0)
      else if witness.isNone && !frameworkModule m && representationChange v.type then
        witness := some (name, 3)
    let some (name, k) := witness | continue
    connected := connected + 1
    found := found.modify k (· + 1)
    let path := "/".intercalate (m.components.drop 1 |>.map toString)
    if citations.isEmpty then
      violations := violations.push s!"{m}: connection {name} without a cited scaffold"
    else unless citations.any (fun a => ((rows.getD a "").splitOn s!"`{path}`").length > 1) do
      violations := violations.push
        s!"{m}: connection {name}; no row of a cited scaffold {citations} names `{path}`"
  -- Controls: each kind of connection is recognized somewhere in the library.
  for (k, label) in [(0, "two families"), (1, "an implementation"), (2, "an observation seed"),
      (3, "a change of representation")] do
    if found[k]! == 0 then throwError "The scaffold check recognized no connection of {label}"
  let scaffolds ← (root / "theorem").walkDir
  -- The Lean names a scaffold cites are public declarations or library modules; tokens that are
  -- Agda declarations or Agda modules are the scaffold's own.
  let agdaFiles := scaffolds.filter (·.extension == some "agda")
  let relOf (file : System.FilePath) : String :=
    String.ofList (file.toString.toList.drop (root.toString.length + 1))
  let mut texts : Array (String × String) := #[]
  for file in agdaFiles do
    texts := texts.push (relOf file, ← IO.FS.readFile file)
  let declared := texts.foldl (fun acc t => agdaDeclared t.2 acc) {}
  let agdaModules : Std.HashSet String := texts.foldl (init := {}) fun acc t =>
    acc.insert (".".intercalate ((String.ofList (t.1.toList.take (t.1.length - 5))).splitOn "/"))
  let modules : NameSet := env.header.moduleNames.foldl (·.insert ·) {}
  let mut wanted : Array (String × String) := #[]
  for (rel, text) in texts do
    for tok in agdaCommentTokens text do
      unless leanReference tok do continue
      if (tok.splitOn ".").all declared.contains then continue
      if agdaModules.contains tok then continue
      if modules.contains tok.toName || modules.contains (`theorem ++ tok.toName) then continue
      wanted := wanted.push (rel, tok)
  let lasts : Std.HashSet String :=
    wanted.foldl (fun acc w => acc.insert (w.2.splitOn ".").getLast!) {}
  let mut byLast : Std.HashMap String (Array (List String × Bool)) := {}
  for (n, _) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    let some last := n.components.getLast? | continue
    unless lasts.contains last.toString do continue
    byLast := byLast.alter last.toString fun a =>
      some ((a.getD #[]).push (n.components.map toString, isPrivateName n))
  for (rel, tok) in wanted do
    let comps := tok.splitOn "."
    let hits := (byLast.getD comps.getLast! #[]).filter fun (cs, _) =>
      cs.length ≥ comps.length && cs.drop (cs.length - comps.length) == comps
    if hits.any (fun (_, isPrivate) => !isPrivate) then continue
    violations := violations.push <| if hits.isEmpty then
      s!"{rel}: `{tok}` is no public declaration, library module or Agda declaration"
    else s!"{rel}: `{tok}` names a private declaration"
  let mut total : Nat := 0
  for file in scaffolds do
    unless file.extension == some "agda" do continue
    total := total + 1
    let pre := root.toString ++ "/"
    let rel := String.ofList (file.toString.toList.drop pre.length)
    unless cited.contains rel do violations := violations.push s!"{rel}: cited by no module"
    unless rows.contains rel do
      violations := violations.push s!"{rel}: no row in the scaffold table of Architecture.md"
  unless violations.isEmpty do
    throwError "Connections and scaffolds out of step ({violations.size}):\n\
      {"\n".intercalate violations.toList}"
  logInfo m!"POWERLIB_LIBRARY_SCAFFOLDS_OK: {connected} modules with connections between contents \
    (families {found[0]!}, implementations {found[1]!}, records {found[2]!}, representations \
    {found[3]!}) cite scaffolds; \
    {total} scaffolds, each cited and with a row naming its modules in Architecture.md; \
    {wanted.size} Lean references in scaffolds, all public"

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
    for name in env.header.moduleData[i]!.constNames do
      let some info@(.thmInfo _) := env.find? name | continue
      unless authoredPublic env name do continue
      decls := decls.push (name, m, positionalType info)
  let groups := duplicates decls
  report "Identical public statements in different modules" (groups.map fun g =>
    ", ".intercalate (g.map fun (n, m) => s!"{n} ({m})").toList)
  logInfo m!"POWERLIB_LIBRARY_DUPLICATES_OK: {decls.size} public theorems, \
    no two statements identical"

/-! ## Restatements -/

namespace LibraryStructure

open Lean Meta Elab Command

/-- `B` follows from `A` by instantiating `A`'s binders. -/
def instanceOf (A B : Name) : MetaM Bool := do
  let bInfo ← getConstInfo B
  let aInfo ← getConstInfo A
  forallTelescopeReducing bInfo.type fun bxs bconcl => do
    let lvls ← aInfo.levelParams.mapM fun _ => mkFreshLevelMVar
    let aType := aInfo.type.instantiateLevelParams aInfo.levelParams lvls
    let (axs, abis, aconcl) ← forallMetaTelescopeReducing aType
    unless ← withReducible (isDefEq aconcl bconcl) do return false
    -- Prop hypotheses first (matching them may assign data binders), then instances, then data
    for i in [:axs.size] do
      let x ← instantiateMVars axs[i]!
      unless x.isMVar do continue
      let ty ← instantiateMVars (← inferType x)
      if abis[i]!.isInstImplicit then continue
      unless ← isProp ty do continue
      let mut ok := false
      for h in bxs do
        if ← withReducible (isDefEq (← inferType h) ty) then
          if ← isDefEq x h then ok := true; break
      unless ok do return false
    for i in [:axs.size] do
      let x ← instantiateMVars axs[i]!
      unless x.isMVar do continue
      let ty ← instantiateMVars (← inferType x)
      if abis[i]!.isInstImplicit then
        let some inst ← synthInstance? ty | return false
        unless ← isDefEq x inst do return false
    for i in [:axs.size] do
      let x ← instantiateMVars axs[i]!
      if x.isMVar then return false
    return true

/-- `src`'s proof reaches `tgt` through theorems of the library (bounded search). -/
def usesTransitively (env : Environment) (src tgt : Name) (limit : Nat := 400) : Bool := Id.run do
  let mut todo := #[src]
  let mut seen : NameSet := {}
  let mut steps := 0
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    steps := steps + 1
    if steps > limit then return false
    let some (.thmInfo v) := env.find? c | continue
    for d in v.value.getUsedConstants do
      if d == tgt then return true
      let some idx := env.getModuleIdxFor? d | continue
      if (env.header.moduleNames[idx.toNat]!).getRoot == `theorem then todo := todo.push d
  return false

/-- The `theorem.*` modules each `theorem.*` module imports, transitively. -/
def importClosure (env : Environment) : NameMap NameSet := Id.run do
  let names := env.header.moduleNames
  let mut memo : NameMap NameSet := {}
  for i in [:names.size] do
    let m := names[i]!
    unless m.getRoot == `theorem do continue
    let mut acc : NameSet := {}
    for imp in env.header.moduleData[i]!.imports do
      let j := imp.module
      unless j.getRoot == `theorem do continue
      acc := acc.insert j
      if let some s := memo.find? j then
        for x in s do acc := acc.insert x
    memo := memo.insert m acc
  return memo

/-- Restatements that stay, with the reason: deriving them would bring a heavy, unrelated import
into a low module or change a public statement. Empty: every restatement found so far has been
derived from the theorem it restated. -/
def restatementExemptions : Array (String × String × String) := #[]

/-- Control: the general fixture. -/
theorem fixtureRestatedGeneral (n : ℕ) : n ≤ n + 1 := by omega

/-- Control: its instance at `n = 2`, proved again without it. -/
theorem fixtureRestatedInstance : (2 : ℕ) ≤ 2 + 1 := by decide

end LibraryStructure

set_option maxHeartbeats 0 in
open LibraryStructure in
run_cmd liftTermElabM do
  let env ← getEnv
  -- Control: an instance proved again without the general statement is a restatement.
  unless ← instanceOf ``fixtureRestatedGeneral ``fixtureRestatedInstance do
    throwError "The restatement detector missed an instance of a theorem"
  let clos := importClosure env
  let mut decls : Array (Name × Name) := #[]
  for (i, m) in libraryModules env do
    for c in env.header.moduleData[i]!.constNames do
      let some (.thmInfo _) := env.find? c | continue
      unless (declRangeExt.find? env c).isSome do continue
      decls := decls.push (c, m)
  let modOf : NameMap Name := decls.foldl (fun acc (c, m) => acc.insert c m) {}
  let mut tree : DiscrTree Name := {}
  for (c, _) in decls do
    let info ← getConstInfo c
    let keys ← withNewMCtxDepth do
      let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      let (_, _, concl) ← forallMetaTelescopeReducing
        (info.type.instantiateLevelParams info.levelParams lvls)
      DiscrTree.mkPath concl
    if keys.size ≤ 1 then continue
    tree := tree.insertKeyValue keys c
  let uses (x y : Name) : Bool := match env.find? x with
    | some (.thmInfo v) => v.value.getUsedConstants.contains y
    | _ => false
  let bounded (k : MetaM Bool) : MetaM Bool :=
    tryCatchRuntimeEx (withNewMCtxDepth (withTheReader Core.Context
      (fun ctx => { ctx with maxHeartbeats := 20000000 }) (withCurrHeartbeats k)))
      fun _ => pure false
  let mut violations : Array String := #[]
  let mut exempted : Array (String × String) := #[]
  let mut seen : Std.HashSet (Name × Name) := {}
  for (b, mb) in decls do
    let info ← getConstInfo b
    let cands ← withNewMCtxDepth <| forallTelescopeReducing info.type fun _ concl =>
      tree.getMatch concl
    for a in cands do
      if a == b then continue
      let some ma := modOf.find? a | continue
      -- B already uses A, or A is out of B's reach: private elsewhere, or above B
      if uses b a || uses a b then continue
      if isPrivateName a && ma != mb then continue
      if ma != mb && ((clos.find? ma).getD {}).contains mb then continue
      unless ← bounded (instanceOf a b) do continue
      -- derived through intermediate theorems, either way
      if usesTransitively env b a || usesTransitively env a b then continue
      -- B uses a theorem at least as general as A
      let mut general := false
      if let some (.thmInfo v) := env.find? b then
        for c in v.value.getUsedConstants do
          unless modOf.contains c do continue
          if c == a then continue
          if ← bounded (instanceOf c a) then
            general := true
            break
      if general then continue
      let key := if Name.quickLt a b then (a, b) else (b, a)
      if seen.contains key then continue
      seen := seen.insert key
      if restatementExemptions.any (fun (x, y, _) => x == b.toString && y == a.toString) then
        exempted := exempted.push (b.toString, a.toString)
        continue
      violations := violations.push s!"{b} ({mb}) restates {a} ({ma}) without using it"
  for (x, y, _) in restatementExemptions do
    unless exempted.contains (x, y) do
      violations := violations.push s!"stale exemption: {x} restating {y}"
  unless violations.isEmpty do
    throwError "Theorems restating another theorem they could use ({violations.size}):\n\
      {"\n".intercalate violations.toList}"
  logInfo m!"POWERLIB_LIBRARY_RESTATEMENTS_OK: {decls.size} theorems; none restates (an instance \
    of) another theorem it could use without using it; {exempted.size} documented exemptions"

