"""The 1/X correction to Kramers, derived term by term rather than fitted.

kram2 showed the exact quadrature (Q) reproduces every measured escape time
and that T_exact/T_asym is a curve, not a constant.  A curve is only an
answer if its leading behaviour is derived, so: split (Q) into its two
factors and expand each.  T = Z_w * I_b / Dtilde with

    Z_w = INT_0^{rho_g} z e^{-U/D} dz            (well normalisation)
    I_b = INT (1/y) e^{U/D} dy   near rho_g      (barrier)

Well: substitute u = z^2 and expand e^{c1 u^2/(4D)} to first order,
    Z_w = (D/alpha)[1 + 2 c1 D/alpha^2] = (D/alpha)[1 + 1/(2X)] .
Barrier: expand U about rho_g to quartic and 1/y to second order,
    U = DU - alpha xi^2 - c1 rho_g xi^3 - (c1/4) xi^4 ,
    1/y = (1/rho_g)(1 - xi/rho_g + xi^2/rho_g^2) ,
with Gaussian moments of variance D/(2 alpha) the surviving terms are
    xi^2/rho_g^2 : +1/(8X)
    -c1 xi^4/(4D): -3/(64X)
    +c1^2 rho_g^2 xi^6/(2D^2) : +15/(64X)
    cross (-xi/rho_g)(-c1 rho_g xi^3/D) : +12/(64X)
summing to +1/(2X).  Hence

    T = sqrt(pi) sqrt(D Re c1)/alpha^2 e^X [1 + 1/X + O(1/X^2)]           (K)

The 1/X coefficient is 1 EXACTLY -- half from the well, half from the
barrier.  Below: (a) the two halves checked separately against numerics,
(b) the coefficient read off the exact ratio at large X, which must give
1.000 if the derivation is right, and (c) where 1 + 1/X equals sqrt(2).
"""
import math
import numpy as np
LOG = open('sweep20/kram2b.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()

C1 = 1.219123e+03
AE = 0.08


def halves(X, N=2000001):
    D = AE*AE/(4.0*C1*X)
    rg = math.sqrt(AE/C1)
    z = np.linspace(0.0, rg, N)
    U = AE*z*z/2.0 - C1*z**4/4.0
    Zw = float(np.trapezoid(z*np.exp(-U/D), z))
    y = np.linspace(rg - 12*math.sqrt(D/(2*AE)), rg + 12*math.sqrt(D/(2*AE)),
                    N)
    y = y[y > 0]
    Uy = AE*y*y/2.0 - C1*y**4/4.0
    DU = AE*AE/(4.0*C1)
    Ib = float(np.trapezoid(np.exp((Uy - DU)/D)/y, y))
    return Zw, Ib, D, rg, DU


out("=== the two halves of the 1/X correction, separately")
out("   X    | Zw/(D/alpha)-1 | 1/(2X) | Ib/(e^X sqrt(piD/alpha)/rho_g)-1 "
    "| 1/(2X)")
for X in (10.0, 20.0, 40.0, 80.0, 160.0):
    Zw, Ib, D, rg, DU = halves(X)
    zr = Zw/(D/AE) - 1.0
    ia = math.sqrt(math.pi*D/AE)/rg
    ir = Ib/ia - 1.0
    out(f"  {X:6.1f} | {zr:14.6f} | {1/(2*X):6.4f} | {ir:32.6f} | "
        f"{1/(2*X):6.4f}")

out("")
out("=== the coefficient read off the exact ratio (kram2's table)")
tab = []
for ln in open('sweep20/kram2.log').read().split('\n'):
    p = ln.split('|')
    if len(p) == 3 and p[0].strip().replace('.', '').isdigit():
        try:
            tab.append((float(p[0]), float(p[1])))
        except ValueError:
            pass
tab = [t for t in tab if t[0] >= 30.0]
if len(tab) >= 2:
    Xv = np.array([t[0] for t in tab]); Rv = np.array([t[1] for t in tab])
    A = np.vstack([1.0/Xv, 1.0/Xv**2]).T
    cf = np.linalg.lstsq(A, Rv - 1.0, rcond=None)[0]
    out(f"    T_exact/T_asym - 1 = {cf[0]:.4f}/X + {cf[1]:.3f}/X^2   "
        f"(derived: 1/X exactly)")
    out(f"    deviation of the 1/X coefficient from 1: "
        f"{(cf[0]-1)*100:+.2f}%")
out("")
out(f"    1 + 1/X = sqrt(2) at X = 1/(sqrt(2)-1) = {1/(math.sqrt(2)-1):.4f}")
out( "    the discarded fit window was X > 1.4, mean X ~ 2.4 -- so the")
out( "    'missing sqrt(2)' was 1 + 1/X evaluated at the X the simulation")
out( "    could afford.  There is no missing constant.")
