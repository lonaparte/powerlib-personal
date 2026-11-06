import powerlib

/-! # Attribute-based index of classified theorems

The primary kind is the theorem's explicit `@[tmio T|M|TM|MI|IO]` attribute.
No type-role or proposition-keyword heuristic assigns ownership. This module
imports the public library, lists all explicitly classified authored theorems,
and checks its imported public typed connections;
the default Lake target additionally checks the actual full module inventory.

For a smaller query, import the relevant model modules and
`theorem.TMIO.KnowledgeIndex`, then use `#tmio_edges` or `#tmio_edges TM`
(the other arguments are `T`, `M`, `MI`, `IO`). `#tmio_theorems` also includes
ordinary and private theorems carrying a source attribute. `#tmio_check` checks coverage
in that imported environment. The source preflight can run without compilation:
`python3 tools/tmio_classification.py check`.
-/

#tmio_theorems
#tmio_edges
#tmio_check

open Lean Elab Command powerlib.Knowledge in
run_cmd do
  let entries ← entriesInEnvironment
  if entries.isEmpty then throwError "No connection theorems imported by powerlib"
  logInfo m!"POWERLIB_TMIO_INDEX_OK: {entries.size} attributed connection theorems"
