# Repository conventions

Write the project name as `powerlib` in prose.

Keep build outputs, caches, downloaded dependencies, local tools, and temporary
run results out of Git. Before committing, inspect the staged paths for these
artifacts. Do not force-add ignored build files.

`Powerlib/Generated/Conversion.lean` and `agda/wire.json` are intentional,
versioned source inputs used to check the Agda-to-Lean interface.
