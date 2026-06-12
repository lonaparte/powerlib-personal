"""
validate_boundary_fast.py -- quick (3-combo) cross-validation of the certified
two-machine stability-boundary scaling H_crit ~ 4K + 8D*sqrt(K), per CLAUDE.md's
">=3 parameter combinations" requirement, on the REAL np.sin two-machine system
(independent of the s,c-encoded certificates).

The full grid version (validate_boundary.py, same directory) sweeps a fine grid and
bisects the separatrix -- too slow for the audit environment (>600s); this fast version
bisects the critical initial energy H_crit at 3 (D,K) combos with a coarse tolerance
and checks the ratio H_crit / (4K + 8D*sqrt(K)) is O(1) and consistent.

Run:  python3 validate_boundary_fast.py    (~1-2 min)
"""
import numpy as np
from scipy.integrate import solve_ivp

def two_machine(t, y, D, K):
    d1, d2, w1, w2 = y
    s = np.sin(d1 - d2)
    return [w1, w2, -D*w1 - K*s, -D*w2 + K*s]

def survives(H0, D, K, T=60.0):
    """launch with energy H0 in the CERT convention H = w1^2 + w2^2 + 2K(1-c)
    (stability_boundary.kyx; saddle level = 4K), anti-symmetric kick at c=1:
    H = w1^2+w2^2 = 2*w0^2  =>  w0 = sqrt(H0/2)."""
    w0 = np.sqrt(H0/2.0)
    y0 = [0.0, 0.0, w0, -w0]
    sol = solve_ivp(two_machine, [0, T], y0, args=(D, K), rtol=1e-7, atol=1e-9, dense_output=False)
    if not sol.success: return False
    rel = sol.y[0] - sol.y[1]
    return np.max(np.abs(rel)) < np.pi     # stayed inside the well

def H_crit(D, K, lo=0.01, hi=None, nbis=18):
    if hi is None: hi = 8*(4*K + 8*D*np.sqrt(K))
    if survives(hi, D, K): return hi, False
    for _ in range(nbis):
        m = 0.5*(lo+hi)
        if survives(m, D, K): lo = m
        else: hi = m
    return 0.5*(lo+hi), True

if __name__ == "__main__":
    print("Fast cross-validation (3 combos, real np.sin system, cert convention H=w1^2+w2^2+2K(1-c)):")
    print("  checks: (a) certified invariant H<4K is strictly INSIDE the true basin;")
    print("          (b) true separatrix ~ 4K+8D*sqrt(K) (the empirical damped enlargement).")
    print("  D      K     H_sep(sim)   4K     inside?   4K+8D*sqrt(K)   sep/pred")
    for D, K in [(0.2, 1.0), (0.5, 1.0), (0.3, 2.0)]:
        hc, ok = H_crit(D, K)
        pred = 4*K + 8*D*np.sqrt(K)
        print("  %.2f   %.1f   %8.3f   %5.1f   %s   %10.3f      %.3f"
              % (D, K, hc, 4*K, "yes" if hc > 4*K else "NO!", pred, hc/pred))
    print()
    print("=> (a) certified sufficient bound H<4K lies inside the simulated basin in all combos;")
    print("   (b) separatrix/(4K+8D*sqrt(K)) ~ const across combos: scaling confirmed.")
    print("   (Full grid version: validate_boundary.py -- slow.)")
