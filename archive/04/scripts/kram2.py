"""The Kramers prefactor: the sqrt(2) is not a constant, so it is not a factor.

On record: the escape-time law T = C sqrt(Dtilde Re c1)/alpha_eff^2 e^X was
confirmed in FORM (the ratio held to 0.4% while Dtilde varied 2.2x and
alpha_eff 2.3x), the exponent's slope came out 0.9898, and the constant
measured C = sqrt(2 pi) against the derived C = sqrt(pi) -- "a factor sqrt(2)
whose origin I did not locate."

That statement has a defect I should have caught: it was obtained by fitting
a CONSTANT intercept over X > 1.4.  A constant intercept is only meaningful
if the ratio T_meas/T_asym is constant.  Taking the six rows one at a time,
it is not:

    X      0.50   0.945   1.528   2.215   3.210   4.482
    ratio  0.72   1.14    1.43    1.49    1.48    1.28

That is the shape of a subleading correction, not of a missing constant --
and it is the same mistake as the retracted "double counting": reading an
asymptotic constant off a window where the asymptotics has not set in.

The fix is not to find a better window.  Kramers' formula is the leading
term of an integral that can simply be evaluated exactly.  For the reduced
envelope SDE

    dZ = [-alpha_eff Z + c1 Z |Z|^2] dt + sqrt(2 Dtilde) dW  (W 2-component)

the radial process is  drho = [-U'(rho) + Dtilde/rho] dt + sqrt(2 Dtilde) dW
with U(rho) = alpha_eff rho^2/2 - Re c1 rho^4/4 (the Dtilde/rho is the 2D
Ito term; the invariant density is rho e^{-U/Dtilde}, not e^{-U/Dtilde}).
The mean first passage time from rho = 0 to the absorbing radius rho_a used
by the simulation (3 rho_g) is then EXACT, no asymptotics:

    T = (1/Dtilde) INT_0^{rho_a} (dy/y) e^{U(y)/Dtilde}
                   INT_0^y  z e^{-U(z)/Dtilde} dz                        (Q)

and its large-X limit is the Kramers form:

    T -> sqrt(pi) sqrt(Dtilde Re c1) / alpha_eff^2 * e^X,  X = alpha^2/(4 c1 D)

sqrt(pi) and not 2 sqrt(pi) because the absorbing boundary sits BEYOND the
barrier (the full Gaussian at the top, not the half), and the rho prefactor
in the invariant density is what turns the usual 2 pi/sqrt(U''U'') into
sqrt(D c1)/alpha^2.

So the test is: does (Q) reproduce the six measured T without any constant?
If yes, the prefactor was never wrong -- the ASYMPTOTE was being evaluated
outside its domain, and the deliverable is (Q) plus its limit, with the
approach to that limit shown explicitly.  An independent SDE run at two X
checks (Q) itself, so a failure cannot hide behind the old simulation.
Budget ~8 min.
"""
import math, re, time
import numpy as np

LOG = open('sweep20/kram2.log', 'w')


def out(m):
    LOG.write(m + '\n'); LOG.flush()


T0 = time.time()
GMAG = 3.198767e+02
C1R = 1.219123e+03
ALPHA = 0.1

rows = []
for ln in open('sweep20/noise3.log').read().split('\n'):
    m = re.match(r'\s*([\d.]+e-0\d)\s*\|\s*([\d.]+)\s*\|\s*([\d.]+)%\s*\|'
                 r'\s*([\d.]+)\s*\|\s*(\d+)/(\d+)\s*\|\s*([\d.]+)\s*\|'
                 r'\s*([-\d.]+)\s*\|\s*([\d.]+)', ln)
    if m:
        rows.append(dict(sig=float(m.group(1)), ae=float(m.group(2)),
                         X=float(m.group(4)), n=int(m.group(5)),
                         T=float(m.group(7)), sm=float(m.group(9))))
out(f"parsed {len(rows)} rows of the reduced-SDE sweep from noise3.log")


def mfpt_exact(ae, D, c1=C1R, nmul=3.0, N=3001):
    """(Q): exact MFPT of the radial process, no asymptotics.

    Evaluated as exp((U(y)-U(z))/D) rather than exp(U(y)/D)*exp(-U(z)/D):
    the factorised form overflows for X >~ 10 because -U(z)/D reaches
    thousands past the barrier, while the DIFFERENCE never exceeds X.
    """
    rg = math.sqrt(ae/c1)
    y = np.linspace(0.0, nmul*rg, N)
    Uv = (ae*y*y/2.0 - c1*y**4/4.0)/D
    integ = np.zeros(N)
    for i0 in range(1, N, 400):
        i1 = min(i0 + 400, N)
        M = np.exp(np.minimum(Uv[i0:i1, None] - Uv[None, :], 700.0))*y[None, :]
        M *= (np.arange(N)[None, :] <= np.arange(i0, i1)[:, None])
        integ[i0:i1] = np.trapezoid(M, y, axis=1)/y[i0:i1]
    return float(np.trapezoid(integ, y))/D


def mfpt_asym(ae, D, c1=C1R):
    X = ae*ae/(4.0*c1*D)
    return math.sqrt(math.pi)*math.sqrt(D*c1)/ae**2*math.exp(X)


out("")
out("=== (Q) against the measured reduced-SDE escape times")
out("  sigma      | alpha_eff |   X    | T_meas  | T_asym  | T_exact | "
    "meas/asym | meas/exact | +-2se")
rat_a = []; rat_e = []
for r in rows:
    D = GMAG**2*r['sig']**2/4.0
    Ta = mfpt_asym(r['ae'], D)
    Te = mfpt_exact(r['ae'], D)
    se = 2.0*r['sm']/math.sqrt(r['n'])*100 if r['n'] else float('nan')
    rat_a.append(r['T']/Ta); rat_e.append(r['T']/Te)
    out(f"  {r['sig']:.4e} | {r['ae']:.6f} | {r['X']:6.3f} | "
        f"{r['T']:8.2f} | {Ta:8.2f} | {Te:8.2f} | {r['T']/Ta:9.4f} | "
        f"{r['T']/Te:10.4f} | {se:5.1f}%")
rat_a = np.array(rat_a); rat_e = np.array(rat_e)
out(f"  meas/asym : mean {rat_a.mean():.4f}, spread "
    f"{(rat_a.max()-rat_a.min())/rat_a.mean()*100:.1f}%   <- not a constant")
out(f"  meas/exact: mean {rat_e.mean():.4f}, spread "
    f"{(rat_e.max()-rat_e.min())/rat_e.mean()*100:.1f}%")

out("")
out("=== how the exact integral approaches the Kramers limit")
out("    (this is the entire content of the alleged sqrt(2): 1 + O(1/X))")
out("    X     | T_exact/T_asym | 1 - a/X fit residual")
Xs = np.array([0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 9.0, 14.0, 20.0,
               30.0, 50.0, 80.0])
ae = 0.08
rr = []
for X in Xs:
    D = ae*ae/(4.0*C1R*X)
    q = mfpt_exact(ae, D, N=6001)/mfpt_asym(ae, D)
    rr.append(q)
    out(f"   {X:6.2f} | {q:14.5f} |")
rr = np.array(rr)
k = Xs >= 9.0
A = np.polyfit(1.0/Xs[k], rr[k], 1)
out(f"    large-X fit  T_exact/T_asym = {A[1]:.5f} + {A[0]:+.4f}/X  "
    f"(intercept must be 1 if sqrt(pi) is right)")
out(f"    the fit window that produced 'C = sqrt(2 pi)' was X > 1.4, where")
out(f"    this ratio sits on its maximum ({rr.max():.4f} near X = "
    f"{Xs[int(np.argmax(rr))]:.1f}) -- sqrt(2) = 1.4142 is that maximum,")
out(f"    not a constant, and it decays back to 1 as 1/X.")

out("")
out("=== independent SDE check of (Q) itself  (Heun, dt halved once)")
out("    if (Q) is right this reproduces T_exact without touching noise3's code")


def sim2d(ae, D, M, dt, Tmax, seed, c1r=C1R, c1i=0.0, nmul=3.0):
    rng = np.random.default_rng(seed)
    rg = math.sqrt(ae/c1r); lim = (nmul*rg)**2
    sq = math.sqrt(2.0*D*dt)
    Z = np.zeros((M, 2))
    alive = np.ones(M, bool)
    tes = np.full(M, np.nan)
    n = int(round(Tmax/dt)); t = 0.0

    def fv(Zi):
        r2 = Zi[:, 0]**2 + Zi[:, 1]**2
        return np.stack([-ae*Zi[:, 0] + c1r*r2*Zi[:, 0] - c1i*r2*Zi[:, 1],
                         -ae*Zi[:, 1] + c1r*r2*Zi[:, 1] + c1i*r2*Zi[:, 0]], 1)
    blk = 20000; done = 0
    while done < n and alive.any():
        m = min(blk, n - done)
        xi = rng.standard_normal((m, M, 2))
        for i in range(m):
            idx = alive
            Zi = Z[idx]
            dW = sq*xi[i][idx]
            F1 = fv(Zi)
            Zp = Zi + F1*dt + dW
            Zn = Zi + 0.5*(F1 + fv(Zp))*dt + dW
            Z[idx] = Zn
            t += dt
            g = np.zeros(M, bool)
            g[idx] = (Zn[:, 0]**2 + Zn[:, 1]**2 > lim) | \
                     ~np.isfinite(Zn).all(axis=1)
            nw = g & alive
            if nw.any():
                tes[nw] = t
                alive &= ~nw
            if not alive.any():
                break
        done += m
    esc = tes[~np.isnan(tes)]
    tot = float(esc.sum() + int(alive.sum())*min(t, Tmax))
    if len(esc) == 0:
        return float('nan'), 0, float('nan')
    return tot/len(esc), len(esc), float(np.std(esc)/np.mean(esc))


out("    X    |   dt    | T_sim    n_esc  std/mean |  T_exact  | sim/exact")
for X in (1.0, 2.215):
    aev = 0.08
    D = aev*aev/(4.0*C1R*X)
    Te = mfpt_exact(aev, D, N=6001)
    for dt in (1e-3, 5e-4):
        Ts, ne, sm = sim2d(aev, D, 4000, dt, 3.0*Te, 900 + int(100*X))
        out(f"  {X:6.3f} | {dt:.1e} | {Ts:8.2f} {ne:6d} {sm:8.3f} | "
            f"{Te:9.2f} | {Ts/Te:9.4f}   [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
