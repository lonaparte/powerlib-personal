import powerlib

/-! # Attribute-based index of the library's connection statements

The primary kind is the theorem's explicit `@[tmio T|M|TM|MI|IO]` attribute.
No type-role or proposition-keyword heuristic assigns ownership. This module
imports the public library and checks its imported public typed connections;
the default Lake target additionally checks the actual full module inventory.

For a smaller query, import the relevant model modules and
`theorem.TMIO.KnowledgeIndex`, then use `#tmio_edges` or `#tmio_edges TM`
(the other arguments are `T`, `M`, `MI`, `IO`). `#tmio_check` checks coverage
in that imported environment. The source preflight can run without compilation:
`python3 tools/tmio_classification.py check`.
-/

#tmio_edges
#tmio_check

open Lean Elab Command powerlib.Knowledge in
run_cmd do
  -- Regression boundaries from the semantic review: carrier names and use of
  -- certify do not determine a category, and Exact is not RealizationExact.
  for (name, expected) in #[
      (``powerlib.Circuits.Interconnection.portData_certified, Kind.TM),
      (``powerlib.CurrentControl.MismatchParams.den_eq_base, Kind.MI),
      (``powerlib.LTI.sampled_reading, Kind.MI),
      (``powerlib.LTI.sampled_exact_iff, Kind.TM),
      (``powerlib.Linear.Rational.realize_accepted, Kind.M),
      (``powerlib.GFM.VSMLPF.infer_not_truth_of_unstable_producer, Kind.IO)] do
    unless kindOf? (← getEnv) name == some expected do
      throwError "TMIO category regression: {name} must have {expected.label}"
  let entries ← entriesInEnvironment
  if entries.isEmpty then throwError "No connection theorems imported by powerlib"
  logInfo m!"POWERLIB_TMIO_INDEX_OK: {entries.size} attributed connection theorems"
