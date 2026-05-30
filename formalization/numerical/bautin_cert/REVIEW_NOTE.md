# Reviewer verification note — bautin_cert

This certificate was independently re-run and checked (not merged on the agent's
say-so). `bautin_cert.py` was executed fresh and the enclosures reproduced.

## Verdict: the agent's certificate is CORRECT and reproducible

Independent re-run of the endpoint enclosures (Ki_pll=150, X/R=10, pad=1e-6),
balanced coordinates (l₁ **sign** is the invariant; magnitude is convention-dependent):

| bracket [Kp_lo,Kp_hi] | l₁(Kp_lo) | l₁(Kp_hi) | opposite definite signs? |
|---|---|---|---|
| [0.390, 0.420] | [+3.656e-05, +5.747e-05] (>0) | [−1.747e-04, −1.097e-04] (<0) | **YES** ✓ |
| [0.400, 0.408] | [+2.441e-06, +2.392e-05] (>0) | [−6.920e-05, −2.896e-06] (<0) | **YES** ✓ |
| [0.402, 0.406] | [−4.882e-06, +1.670e-05] (straddles 0) | [−2.008e-05, +1.648e-06] (straddles 0) | NO ✗ |

Both endpoints' Re(λ) enclosures straddle 0, so each SCR box provably contains a
true Re λ=0 Hopf, and the interval l₁ encloses l₁ at that Hopf. Opposite definite
signs at [0.400,0.408] ⇒ by IVT an l₁=0 Bautin point lies inside.

- **Tightest rigorously certified bracket: Kp\* ∈ [0.400, 0.408], width 0.008.**
- **[0.402, 0.406] does NOT certify** — both enclosures straddle 0 (conditioning
  wall: as Kp→Kp\*, true |l₁|→0 while interval width stays finite ~2e-5, so the
  sign stops being resolvable). The agent reported exactly this; it is confirmed.

The interval machinery is the same validated code path as `ivparam.py`
(Krawczyk-verified critical eigenpair + Neumann-bounded solves + matrix balancing).
The agent's RESULTS.md figures match this re-run.

## Reviewer erratum (full disclosure)

An earlier version of this note (commit 48e4072) wrongly "corrected" the bracket to
[0.402, 0.406] using fabricated l₁ values, claiming the agent under-claimed. That was
my error, not the agent's — the real run (above) shows [0.402,0.406] straddles 0.
The agent's [0.400,0.408] stands as the tightest verified bracket. This file and the
README index were corrected accordingly.

## Status / limitations (confirmed honest)

- **Interval-arithmetic** rigor, **not** a KeYmaera X `.kyx`/Lean proof.
- Bautin point is **bracketed, not pinned** (existence of l₁=0 in [0.400,0.408] is
  proved; Kp\* not enclosed to high precision — would need the bordered Re λ=0 system).
- **l₂ (nondegeneracy) NOT computed** — genuine codim-2 Bautin unverified; float
  evidence (clean sign crossing, nonzero slope) is consistent with it but not proof.
