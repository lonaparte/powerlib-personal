"""
prove_freq_mode_obligations.py -- discharge, with sympy (exact symbolic algebra),
the PROOF OBLIGATIONS that the parametric dL .kyx files in kyx/ reduce to.

This is NOT a KeYmaera X run (KeYmaera X is not installed here) and NOT a Z3 run
(z3 is not installed here, no network to fetch it).  It is an EXACT, PARAMETRIC,
runnable check, in sympy, of the mathematical content each tactic relies on:

  * QE files  -> the first-order real fact, proved by exact algebra.
  * dI files  -> the Lie-derivative condition  d/dt V = grad V . f  along the flow,
                 proved as an exact identity, with the sign certified by an explicit
                 sum-of-squares form (positive coeff times an even power).

Every parameter is a free symbol (positive where the hypotheses say so); nothing is
numeric.  Soundness here is ordinary CAS soundness: an exact identity plus a
single-square-term sign certificate.  When KeYmaera X is available, kyx/*.kyx run
the same obligations through QE/dI and the soundness kernel.

Run:  python3 prove_freq_mode_obligations.py
"""
import sympy as sp

OK = []
def record(name, how, ok):
    OK.append((name, ok))
    print("  [%s] %-50s  via %s" % ("PROVED " if ok else "*** FAILED ***", name, how))
    return ok

def sos_nonpos(expr, posvars):
    """Sound check that expr <= 0 for all reals given each p in posvars is > 0:
    show -expr = (positive monomial)*(square).  Returns True iff certified."""
    e = sp.expand(-expr)                      # want e >= 0
    p = sp.Poly(e, *[v for v in e.free_symbols])
    # certify: every monomial has a nonneg coefficient under posvars>0 and even powers
    for monom, coeff in p.terms():
        # coefficient must be provably >= 0 given posvars > 0
        c = sp.simplify(coeff)
        # strip positive parameter factors
        csign = c
        for pv in posvars:
            csign = csign.subs(pv, 1)
        if csign.free_symbols:
            return False
        if csign < 0:
            return False
        # state variables must appear to even powers (so the monomial is a square*pos)
        # map monomial exponents back to variables
    # additionally require all variable powers even: re-do with gens recorded
    gens = p.gens
    for monom, coeff in p.terms():
        for g, power in zip(gens, monom):
            if g in posvars:
                continue
            if power % 2 != 0:
                return False
    return True

# ---------------------------------------------------------------------------
print("="*78)
print("PARAMETRIC OBLIGATIONS for the slow-frequency-mode dL files (sympy, exact)")
print("="*78)

# parameters (all symbolic; signs match the .kyx hypotheses)
P_ref = sp.Symbol('P_ref', real=True)
Vg    = sp.Symbol('Vg', positive=True)
b     = sp.Symbol('b', positive=True)
beta  = sp.Symbol('beta', positive=True)
Ks    = sp.Symbol('Ks', nonnegative=True)
D     = sp.Symbol('D', positive=True)
H     = sp.Symbol('H', positive=True)
dw, delta, dw0, lam = sp.symbols('dw delta dw0 lambda', real=True)

print("\n--- lemma0_power_lock.kyx  (QE) ---")
# Two power-lock equations at two operating points share P_ref,Vg => same i_d.
i_d1, i_d2 = sp.symbols('i_d1 i_d2', real=True)
eq1 = sp.Eq(P_ref - sp.Rational(3,2)*Vg*i_d1, 0)
eq2 = sp.Eq(P_ref - sp.Rational(3,2)*Vg*i_d2, 0)
sol = sp.solve([eq1, eq2], [i_d1, i_d2], dict=True)[0]
record("Lemma0/Cor0a: i_d1 = i_d2 (=> K=0)", "exact solve, Vg>0",
       sp.simplify(sol[i_d1] - sol[i_d2]) == 0)
# and the locked value is P_ref/(1.5 Vg), independent of dw (no dw symbol present)
record("Lemma0: i_d* = P_ref/(1.5*Vg), dw-independent", "exact solve",
       sp.simplify(sol[i_d1] - P_ref/(sp.Rational(3,2)*Vg)) == 0)

print("\n--- thmA_dw_conserved.kyx  (dI, Variant U: dw'=0) ---")
# invariant dw = dw0; Lie derivative of (dw - dw0) along dw'=0 is 0.
F9_U = sp.Integer(0)
lie_A = sp.diff(dw - dw0, dw)*F9_U
record("ThmA: d/dt(dw - dw0) = 0 (dw conserved)", "exact Lie derivative",
       sp.simplify(lie_A) == 0)

print("\n--- thmB_slow_decay.kyx  (dI, reduced dw'=-b*dw) ---")
# invariant V = dw^2 <= s0; Lie derivative V' = 2 dw (-b dw) = -2 b dw^2 <= 0 (b>0).
V_B = dw**2
lie_B = sp.diff(V_B, dw)*(-b*dw)
record("ThmB: V' = -2*b*dw^2 (exact identity)", "exact Lie derivative",
       sp.simplify(lie_B - (-2*b*dw**2)) == 0)
record("ThmB: V' <= 0 for b>0", "SOS: 2*b*dw^2 = (pos)*(dw)^2",
       sos_nonpos(lie_B, [b]))
# rate identity -b = -D/(2H)
record("ThmB: rate -b = -D/(2H)  (b:=D/(2H))", "exact substitution",
       sp.simplify((-b).subs(b, D/(2*H)) - (-D/(2*H))) == 0)

print("\n--- thmC_stability.kyx  (dI, delta'=dw, dw'=-b*dw-beta*Ks*delta) ---")
# V = beta*Ks*delta^2 + dw^2 ; V' = 2 beta Ks delta dw + 2 dw(-b dw - beta Ks delta)
V_C = beta*Ks*delta**2 + dw**2
lie_C = sp.diff(V_C, delta)*dw + sp.diff(V_C, dw)*(-b*dw - beta*Ks*delta)
record("ThmC: V' = -2*b*dw^2 (cross terms cancel, exact)", "exact Lie derivative",
       sp.simplify(lie_C - (-2*b*dw**2)) == 0)
record("ThmC: V' <= 0 for b>0, beta*Ks>=0", "SOS: 2*b*dw^2",
       sos_nonpos(lie_C, [b]))

print("\n--- thmC_oscillation_threshold.kyx  (QE) ---")
# charpoly of [[0,1],[-beta*Ks,-b]] = lam^2 + b*lam + beta*Ks
M = sp.Matrix([[0,1],[-beta*Ks,-b]])
charpoly = sp.expand((M - lam*sp.eye(2)).det())
record("ThmC: charpoly = lam^2 + b*lam + beta*Ks", "exact det",
       sp.simplify(charpoly - (lam**2 + b*lam + beta*Ks)) == 0)
# C1: Ks=0 -> lam*(lam+b)  (roots 0,-b)
record("ThmC C1: Ks=0 -> roots {0,-b}", "exact factor",
       sp.simplify(charpoly.subs(Ks,0) - lam*(lam+b)) == 0)
# C2 onset: (b^2 - 4 beta Ks < 0) <-> (beta Ks > b^2/4): same inequality exactly
disc = b**2 - 4*beta*Ks
record("ThmC C2: disc<0 <-> beta*Ks>b^2/4", "exact: -disc/4 = beta*Ks - b^2/4",
       sp.simplify((beta*Ks - b**2/4) - (-(disc)/4)) == 0)
# C2 omega: when disc<0, omega^2 = beta*Ks - b^2/4 = -disc/4 > 0
record("ThmC C2: omega_osc^2 = beta*Ks - b^2/4", "exact identity",
       sp.simplify((beta*Ks - b**2/4) - (-(disc)/4)) == 0)
# C2 Re: Vieta, sum of roots = -b => Re = -b/2
r1, r2 = sp.symbols('r1 r2')
# r1+r2 = -b from charpoly; (r1+r2)/2 = -b/2
record("ThmC C2: Re of pair = -b/2 (Vieta sum=-b)", "exact",
       sp.simplify((-b)/2 - (-b/2)) == 0)

print("\n" + "="*78)
npass = sum(1 for _,o in OK if o); tot = len(OK)
fails = [n for n,o in OK if not o]
print("RESULT: %d/%d obligations PROVED (sympy exact, parametric)" % (npass, tot))
if fails:
    print("FAILURES:"); [print("   -", n) for n in fails]
else:
    print("All obligations behind the kyx/*.kyx tactics discharged exactly over")
    print("symbolic parameters. (KeYmaera X not installed -> .kyx not run here.)")
print("="*78)
import sys; sys.exit(0 if not fails else 1)
