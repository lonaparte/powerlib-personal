import theorem.LibrarySearch

/-! Batch admission must make the same decision as Lean's public axiom
collector, including shared dependencies, declaration types and opaque bodies.
Negative declarations live only in a temporary kernel environment. -/

open Lean Meta Elab Command
open powerlib.Search

run_cmd do
  liftTermElabM do
    let check (roots : Array Name) : MetaM Unit := do
      let env ← getEnv
      let expected := roots.all fun root => (declarationAxioms env root).all allowedAxiom
      let actual := axiomViolation? env roots
      unless actual.isNone == expected do
        throwError "Batch axiom audit disagreed with CollectAxioms on {roots}"
      if let some (root, ax) := actual then
        unless roots.contains root && !allowedAxiom ax &&
            (declarationAxioms env root).contains ax do
          throwError "Batch axiom audit reported an incorrect dependency: {root}: {ax}"
    let clean := #[`True.intro, `Nat, `Nat.succ, `Nat.rec, `List, `List.cons,
      `List.rec, `Quot, `Quot.mk, `Quot.sound, `propext, `Classical.choice]
    check #[]
    check (clean ++ clean)
    check #[`sorryAx]
    withoutModifyingEnv do
      addDecl (.axiomDecl {
        name := `AxiomAudit.bad, levelParams := [], type := mkConst ``True, isUnsafe := false })
      addDecl (.defnDecl {
        name := `AxiomAudit.hidden, levelParams := [], type := mkConst ``True,
        value := mkConst `AxiomAudit.bad, hints := .opaque, safety := .safe })
      addDecl (.thmDecl {
        name := `AxiomAudit.theorem, levelParams := [], type := mkConst ``True,
        value := mkConst `AxiomAudit.hidden })
      addDecl (.opaqueDecl {
        name := `AxiomAudit.opaque, levelParams := [], type := mkConst ``True,
        value := mkConst `AxiomAudit.hidden, isUnsafe := false })
      addDecl (.axiomDecl {
        name := `AxiomAudit.carrier, levelParams := [], type := mkSort (.succ .zero), isUnsafe := false })
      let carrier := mkConst `AxiomAudit.carrier
      addDecl (.defnDecl {
        name := `AxiomAudit.identity, levelParams := [],
        type := .forallE `x carrier carrier .default,
        value := .lam `x carrier (.bvar 0) .default,
        hints := .opaque, safety := .safe })
      let box := mkConst `AxiomAudit.Box
      addDecl (.inductDecl [] 0 [{
        name := `AxiomAudit.Box, type := mkSort (.succ .zero), ctors := [
          { name := `AxiomAudit.Box.nil, type := box },
          { name := `AxiomAudit.Box.cons,
            type := .forallE `value carrier (.forallE `tail box box .default) .default }] }] false)
      for root in #[`AxiomAudit.bad, `AxiomAudit.hidden, `AxiomAudit.theorem,
          `AxiomAudit.opaque, `AxiomAudit.identity, `AxiomAudit.Box,
          `AxiomAudit.Box.nil, `AxiomAudit.Box.cons, `AxiomAudit.Box.rec] do
        check (clean ++ #[root, root])
      -- An earlier successful batch cannot supply a stale decision in the
      -- extended environment, and a failed batch cannot poison a clean one.
      check clean
    check clean
  logInfo "POWERLIB_BATCH_AXIOM_AUDIT_OK"
