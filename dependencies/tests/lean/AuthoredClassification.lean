import theorem.Attributes
import dependencies.Mathlib

namespace SourceClassificationCases

structure Packet where
  value : Nat

def packetValue (packet : Packet) : Nat := packet.value

@[simp, powerlib_foundation] theorem packet_value (value : Nat) :
    packetValue ⟨value⟩ = value := rfl

private theorem private_helper : True := True.intro

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let parsed ← Parser.testParseModule env (← getFileName) (← getFileMap).source
  let names ← powerlib.Registry.authoredTheorems parsed[1].getArgs
  unless names.any (fun name => privateToUserName name == `SourceClassificationCases.private_helper) do
    throwError "An authored private theorem was omitted"
  unless names.contains `SourceClassificationCases.packet_value do
    throwError "An authored public theorem was omitted"
  try
    powerlib.Registry.auditAuthoredTheorems parsed[1].getArgs
    throwError "An unclassified private theorem was accepted"
  catch ex =>
    unless (← ex.toMessageData.toString).contains "requires exactly one PowerLib classification" do
      throw ex

attribute [powerlib_foundation] private_helper

theorem delayed_classification (P : Prop) (h : P) : P := h

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let parsed ← Parser.testParseModule env (← getFileName) (← getFileMap).source
  try
    powerlib.Registry.auditAuthoredTheorems parsed[1].getArgs
    throwError "An unclassified public theorem was accepted"
  catch ex =>
    unless (← ex.toMessageData.toString).contains "SourceClassificationCases.delayed_classification" do
      throw ex

attribute [powerlib_foundation] delayed_classification


-- Use the actual standard alias imported through the dependency interface.
@[powerlib_foundation] lemma classified_alias (P : Prop) (h : P) : P := h

private lemma delayed_alias : True := True.intro

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let parsed ← Parser.testParseModule env (← getFileName) (← getFileMap).source
  let names ← powerlib.Registry.authoredTheorems parsed[1].getArgs
  unless names.contains `SourceClassificationCases.classified_alias &&
      names.any (fun name => privateToUserName name == `SourceClassificationCases.delayed_alias) do
    throwError "An authored public or private lemma alias was omitted"
  try
    powerlib.Registry.auditAuthoredTheorems parsed[1].getArgs
    throwError "An unclassified lemma alias was accepted"
  catch ex =>
    unless (← ex.toMessageData.toString).contains "SourceClassificationCases.delayed_alias" do
      throw ex

attribute [powerlib_foundation] delayed_alias

-- These declarations must not be mistaken for authored named theorems.
example (n : Nat) : n = n := rfl

def quotedDeclaration : Lean.Elab.Command.CommandElabM Lean.Syntax := do
  return (← `(theorem quoted_only : True := True.intro)).raw

end SourceClassificationCases

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let parsed ← Parser.testParseModule env (← getFileName) (← getFileMap).source
  let names ← powerlib.Registry.authoredTheorems parsed[1].getArgs
  unless names.size == 5 do
    throwError "Authored theorem discovery included generated, anonymous, or quoted declarations"
  unless env.find? `SourceClassificationCases.Packet.mk.injEq |>.isSome do
    throwError "The generated constructor-injectivity control is absent"
  if names.contains `SourceClassificationCases.Packet.mk.injEq then
    throwError "A generated constructor theorem was treated as authored"
  unless powerlib.Registry.kindOf? env `Nat.add_assoc |>.isNone do
    throwError "An upstream theorem was relabeled"
  unless !powerlib.Registry.isFirstPartyModule `External.Consumer &&
      powerlib.Registry.isFirstPartyModule `dependencies.tests.lean.AuthoredClassification do
    throwError "First-party classification enforcement has the wrong scope"
  for name in names do
    unless powerlib.Registry.kindOf? env name == some .foundation do
      throwError "A delayed or inline theorem classification was lost"
  powerlib.Registry.auditAuthoredTheorems parsed[1].getArgs
  logInfo "POWERLIB_AUTHORED_CLASSIFICATION_OK"
