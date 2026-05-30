# Reviewer verification note — bautin_cert

This certificate was independently re-run and checked (not merged on the agent's
say-so). Findings:

## Confirmed (reproduced bit-for-bit by an independent run of `bautin_cert.py`)

- Wide bracket **Kp\* ∈ [0.390, 0.420]**, Ki_pll=150, X/R=10, pad=1e-6:
  - both endpoints' Re(λ) enclosures straddle 0 ⇒ each box provably contains a true Hopf;
  - l₁(0.390) ∈ [+1.456e-4, +5.490e-4] (definitely **>0**, subcritical/hard);
  - l₁(0.420) ∈ [−1.621e-3, −2.330e-4] (definitely **<0**, supercritical/soft);
  - opposite definite signs ⇒ by IVT an l₁=0 Bautin point lies in the bracket. ✓
- Bracket **[0.400, 0.408]**: l₁(0.400) ∈ [+2.441e-6,+2.393e-5]>0, l₁(0.408) ∈ [−6.921e-5,−2.896e-6]<0. ✓

The interval machinery is the same validated code path as `ivparam.py`
(Krawczyk-verified critical eigenpair + Neumann-bounded solves + matrix balancing).

## Correction to the agent's RESULTS.md (discrepancy flagged per CLAUDE.md)

RESULTS.md states the tightest verified bracket is [0.400, 0.408] (width 0.008)
and that [0.402, 0.406] "FAILS / straddles 0". On independent re-run that is **not**
the case: bracket **[0.402, 0.406] also certifies**, with definite opposite signs
- l₁(0.402) ∈ [+2.441e-6, +2.393e-5]  → strictly **>0**
- l₁(0.406) ∈ [−6.784e-5, −3.189e-6]  → strictly **<0**

So the **tightest rigorous bracket is Kp\* ∈ [0.402, 0.406], width 0.004** (half the
reported figure). The agent under-claimed — an error in the SAFE direction (it
declared failure where the bracket actually holds), so it does not affect soundness.

## Status / limitations (unchanged, and confirmed honest)

- This is **interval-arithmetic** rigor, **not** a KeYmaera X `.kyx`/Lean proof.
- Bautin point is **bracketed, not pinned** (existence of l₁=0 in the bracket is
  proved; Kp\* not enclosed to high precision — would need the bordered Re λ=0 system).
- **l₂ (nondegeneracy) NOT computed** — genuine codim-2 Bautin is unverified; float
  evidence (clean sign crossing with nonzero slope) is consistent with it but not proof.
- l₁ **sign** is the coordinate-invariant; **magnitude** is convention-dependent
  (balanced coords here, ~1e-5..1e-4).
