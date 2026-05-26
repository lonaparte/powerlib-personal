# Project: pH-DAE Formalization for Power Electronics Systems

## System Convention

All .kyx files and Summary.md use the same convention:
- System: ω₁' = -D₁ω₁ - K·sinδ, ω₂' = -D₂ω₂ + K·sinδ (coupling K, not K/2)
- Hamiltonian: H = ω₁² + ω₂² + 2K(1-cosδ) (no 1/2 coefficient)
- Energy balance: Ḣ = -2D₁ω₁² - 2D₂ω₂² (factor 2 from H definition)
- Physical convention H_phys = H/2 gives Ḣ_phys = -D₁ω₁² - D₂ω₂²

Do NOT introduce alternative conventions. If a formula doesn't match the above, it's wrong.

## Formal Statement as Single Source of Truth

All claims — proved or unproved — must have a .kyx file as the authoritative source:
- **Proved**: .kyx file with Problem + Tactic, KeYmaera X reports `proved`.
- **Conjecture**: .kyx file with Problem only (no Tactic). File name prefixed `conjecture_`.
- **Summary.md** is an INDEX of .kyx files, not an independent source of claims. Natural language in Summary.md is commentary, not specification.

When a conjecture is proved, add the Tactic to the existing .kyx file. The Problem block does not change — this eliminates the gap between "what was claimed" and "what was proved".

## Proof Verification Protocol

Every time a conclusion is claimed as "proved" (已证明), the following checks MUST be performed before reporting:

1. **Open the .kyx file** and read the Problem block.
2. **Check system equations**: Every term of the ODE must be present and match the convention above. Missing dynamics (e.g., writing {s'=0} when the actual system has s'=c*(w1-w2)) invalidates the proof.
3. **Check proof goal**: Does the formal Problem match the natural-language claim?
   - Is the stability definition correct (Lyapunov vs asymptotic vs other)?
   - Are parameters symbolic or fixed values? If fixed, state which values.
   - Is the proof for the full claim or only a partial/indirect verification?
4. **Check Lie derivatives algebraically**: For every dI step, manually verify the Lie derivative computation. This catches factor-of-2 errors and sign errors.
5. **Report discrepancies**: If the formal proof proves something different from (or weaker than) the natural-language claim, flag it explicitly.

This is a DEFAULT requirement — do not wait for the user to ask.

## Pre-Proof Checklist (before writing a new .kyx file)

1. State the intended claim in natural language.
2. Write the Problem block in dL. Check: does it capture the claim exactly?
3. Verify manually: are all ODE terms present? Are constraints correct?
4. Only then write the Tactic and attempt to prove.
5. After proof: cross-validate the result numerically with at least 3 parameter combinations.

## Key Files

- `formalization/Summary.md` — Index of all proved results and formalized conjectures. References .kyx files as authoritative source.
- `formalization/archive/phdae/*.kyx` — All KeYmaera X proofs (with Tactic) and conjectures (without Tactic).
- `formalization/archive/phdae/*.lean` — Lean 4 algebraic proofs.

## Research Context

- Focus is on port-Hamiltonian DAE (pH-DAE) systems for power electronics-dominated power systems.
- The core unsolved problem: bridging pH algebraic structure with stability analysis when D₂ < 0. Formalized as `conjecture_ph_bridge.kyx`.
- Do NOT drift to linearization when the question is about nonlinear analysis.
- Cross-validate every conclusion numerically before claiming correctness.
- Do not make claims without verification ("不要口嗨").
