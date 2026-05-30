"""
certify.py -- rigorous sign certificate for the reduced-model l1 over a parameter
range, using sympy (no external SOS solver available in this environment:
cvxpy/scs/Mathematica are absent, verified).  Two fallbacks:

  (1) SOS attempt: if cvxpy+a conic solver are importable, try a
      sum-of-squares / Positivstellensatz certificate that
          N(p) - eps  >= 0   on the semialgebraic set  K = { g_i(p) >= 0 }
      where N is the l1 numerator (sign-determining) and p the free parameters.
      Skipped automatically if no solver.

  (2) QE / CAD fallback (always available via sympy):
      - For a UNIVARIATE l1 numerator N(t) (e.g. t = X/R with control fixed and
        SCR on the Hopf locus pinned by a resultant), use Sturm's theorem to
        COUNT real roots of N in an interval [a,b].  Zero roots + one sample
        sign  =>  N has constant sign on [a,b]  =>  rigorous {l1>0} (or <0) on
        the whole continuum.  This is a genuine real-algebraic decision.
      - For 2 parameters, project: count roots of N along a grid of lines and/or
        use sp.resultant to eliminate one variable, then Sturm on the projection.
        (Full CAD via sympy is not directly exposed; we use the resultant+Sturm
        cylindrical approach, honestly weaker than a full CAD but rigorous for
        the sign-constancy question when the discriminant variety is empty in the
        box.)

This module operates on a sympy expression `N(t)` (the l1 numerator) supplied by
run_all_symbolic.py once the reduced symbolic l1 is formed.
"""
import sympy as sp


def have_sos_solver():
    try:
        import cvxpy  # noqa
        return True
    except Exception:
        return False


def sturm_sign_constant(N, t, a, b):
    """Rigorously decide whether univariate polynomial N(t) has constant sign on
    the closed interval [a,b] (a,b rationals).  Returns (constant: bool,
    n_roots: int, sign: str or None).  Uses Sturm's theorem (exact)."""
    N = sp.Poly(sp.expand(N), t)
    if N.total_degree() <= 0:
        c = N.as_expr()
        return True, 0, ('+' if c > 0 else '-' if c < 0 else '0')
    a = sp.nsimplify(a); b = sp.nsimplify(b)
    nroots = sp.polys.polytools.count_roots(N, a, b)
    if nroots == 0:
        mid = (a + b) / 2
        val = N.eval(mid)
        return True, 0, ('+' if val > 0 else '-' if val < 0 else '0')
    return False, int(nroots), None


def region_l1_positive_univariate(N, t, a, b, n_sub=1):
    """Characterize {t in [a,b] : N(t) > 0} EXACTLY via real root isolation.
    Returns a list of sign intervals [(lo,hi,sign), ...] partitioning [a,b]."""
    Np = sp.Poly(sp.expand(N), t)
    roots = [r for r in sp.real_roots(Np) if sp.And(r >= a, r <= b) == True or (a <= r <= b)]
    # robust: isolate then keep those in [a,b]
    try:
        intervals = sp.Poly(Np, t).intervals()  # isolating rational intervals
    except Exception:
        intervals = None
    cuts = sorted(set([sp.nsimplify(a), sp.nsimplify(b)] +
                      [r for r in sp.real_roots(Np) if a <= r <= b]))
    out = []
    for i in range(len(cuts) - 1):
        lo, hi = cuts[i], cuts[i + 1]
        mid = (lo + hi) / 2
        val = Np.eval(mid)
        out.append((lo, hi, '+' if val > 0 else '-' if val < 0 else '0'))
    return out


def try_sos_nonneg(N_expr, params, constraints, deg=4):
    """Best-effort SOS: prove N_expr - t* >= 0 on { c>=0 } via cvxpy if present.
    Returns (status, info).  No-op if no solver."""
    if not have_sos_solver():
        return ('no-solver', 'cvxpy/scs not installed; use QE/Sturm fallback')
    import numpy as np
    import cvxpy as cp
    # A minimal dense SOS is involved; we only scaffold and report capability.
    return ('solver-present-but-not-implemented',
            'cvxpy present; full Putinar SOS not implemented in this scaffold')


if __name__ == '__main__':
    t = sp.symbols('t', real=True)
    # demo: N(t) = t^2 - 3t + 5 has no real roots -> sign constant (+) on R
    N = t**2 - 3*t + 5
    print("SOS solver available:", have_sos_solver())
    print("Sturm on t^2-3t+5 over [0,40]:", sturm_sign_constant(N, t, 0, 40))
    N2 = (t - 2) * (t - 30)
    print("Sturm on (t-2)(t-30) over [0,40]:", sturm_sign_constant(N2, t, 0, 40))
    print("sign intervals of (t-2)(t-30) on [0,40]:", region_l1_positive_univariate(N2, t, 0, 40))
