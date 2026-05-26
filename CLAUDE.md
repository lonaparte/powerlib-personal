# Project: pH-DAE Formalization for Power Electronics Systems

## Proof Verification Protocol

Every time a conclusion is claimed as "proved" (已证明), the following checks MUST be performed before reporting:

1. **Open the corresponding proof file** (`.kyx`, `.lean`, etc.)
2. **Check preconditions**: Are the system equations correct? Are parameter constraints what we claim?
3. **Check proof goal**: Does the formal statement match the natural-language claim? Specifically:
   - Is the stability definition correct (Lyapunov vs asymptotic vs other)?
   - Are parameters symbolic or fixed values? If fixed, state which values.
   - Is the proof for the full claim or only a partial/indirect verification?
4. **Report discrepancies**: If the formal proof proves something different from (or weaker than) the natural-language claim, flag it explicitly.

This is a DEFAULT requirement — do not wait for the user to ask. Every claim of "proved" must be accompanied by this audit.

## Key Files

- `formalization/Summary.md` — Authoritative document of verified conclusions. Only update with verified results.
- `formalization/archive/phdae/` — All KeYmaera X proofs and supporting scripts.

## Research Context

- Focus is on port-Hamiltonian DAE (pH-DAE) systems for power electronics-dominated power systems.
- The core unsolved problem: bridging pH algebraic structure (Ḣ = -D₁ω₁² + |D₂|ω₂²) with stability analysis when D₂ < 0.
- Do NOT drift to linearization when the question is about nonlinear analysis.
- Cross-validate every conclusion numerically before claiming correctness.
- Do not make claims without verification ("不要口嗨").
