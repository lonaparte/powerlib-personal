import Mathlib.Tactic

-- Aesop rule sets become available to modules importing this declaration.
declare_aesop_rule_sets [PowerLib]

-- Cache theorem names when the library is imported. Enumerating all constants
-- from inside an in-progress theorem can wait on that theorem's own async task.
initialize powerlibRuleAttribute : Lean.TagAttribute ←
  Lean.registerTagAttribute `powerlib_rule "Automatically reusable PowerLib theorem"
