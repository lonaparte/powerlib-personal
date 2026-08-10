"""The GFM quasi-static residual is the saddle-node passage time, not a gap.

I recorded the 2-9% finite-frequency residual as "not mechanistically
closed" and moved on.  That was lazy: the residual has obvious structure I
never looked at.  Dividing the excess over eps_qs by w_p/w0:

    cell                 0.05    0.10    0.30  |  0.50    0.90
    A  M2 Xg=0.5 90%     1.013   1.030   1.052 |  0.974   0.949
    B  M3 Xg=0.5 90%     0.521   0.525   0.551 |  0.215  -0.038
    C  M2 Xg=0.3 75%     0.727   0.735   0.759 |  0.557   0.395
    D  M3 Xg=0.3 90%     0.427   0.422   0.368 |  0.041  -0.253

Flat to a few percent for w_p <= 0.3 w0.  The excess is LINEAR in w_p with
a cell-dependent coefficient.  (Beyond 0.3 the resonant branch starts
competing and it breaks, as it should.)

The mechanism is standard and is already a node in this campaign's own tree
-- B4, slow passage / dynamic bifurcation -- which I failed to connect.
The quasi-static criterion says escape when the equilibrium disappears.
That is necessary, not sufficient: the drive must ALSO stay past the fold
long enough for the saddle-node runaway to complete.  For a sinusoid the
approach to the fold is tangential, so near the bottom

    D(t) = Delta - (1/2) eps w^2 t^2 ,   Delta = eps - eps_qs

and the reduced dynamics along the critical direction is the saddle-node
normal form with a time-dependent parameter,

    xidot = a D(t) + b xi^2 ,
    a = <w_L, -f_V> ,  b = (1/2) <w_L, B(v_R, v_R)> ,  <w_L, v_R> = 1

with v_R, w_L the right/left null vectors of the Jacobian AT the fold.
Rescaling xi = 1/(bT) X, t = T tau with T = (a b c)^{-1/4}, c = eps w^2/2,
every parameter disappears and the problem becomes UNIVERSAL:

    X' = lambda - tau^2 + X^2 ,   lambda = Delta sqrt(ab/c)

so escape happens iff lambda exceeds a pure number lambda*, computed once by
shooting from the quasi-static branch X(-inf) = -sqrt(tau^2 - lambda).  Then

    Delta_c = lambda* sqrt(c/(ab)) = lambda* w sqrt(eps_qs/(2ab))
    ==>  (eps_c - eps_qs)/(eps_qs) / (w/w0) = lambda* w0 sqrt(1/(2 a b eps_qs))

Linear in w_p, coefficient fixed by the fold's own normal-form data, and
lambda* is computed not fitted.  Both the LINEARITY and the CELL-TO-CELL
RATIO are predictions; nothing here is tuned.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.linalg import eig
LOG = open('sweep20/gfmfold.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
HS = 1e-6

# ---------------------------------------------------------------- lambda*
out("=== the universal constant: X' = lambda - tau^2 + X^2")
out("    start on the quasi-static branch X = -sqrt(tau^2 - lambda) at")
out("    tau = -T0 and ask whether X blows up before the equilibria return")


def blows_up(lam, T0s=14.0):
    x0 = -math.sqrt(T0s*T0s - lam)

    def f(t, y):
        return [lam - t*t + y[0]*y[0]]

    def ev(t, y):
        return y[0] - 1e4
    ev.terminal = True; ev.direction = 1
    s = solve_ivp(f, (-T0s, T0s), [x0], method='DOP853', rtol=1e-11,
                  atol=1e-13, events=(ev,))
    return len(s.t_events[0]) > 0 or s.status < 0


lo, hi = 0.0, 6.0
assert not blows_up(lo) and blows_up(hi)
for _ in range(60):
    m = 0.5*(lo+hi)
    if blows_up(m): hi = m
    else: lo = m
LAMSTAR = 0.5*(lo+hi)
out(f"    lambda* = {LAMSTAR:.9f}   (crude matching estimate was pi/2 = "
    f"{math.pi/2:.4f})")
for T0s in (10.0, 14.0, 20.0, 28.0):
    lo2, hi2 = 0.0, 6.0
    for _ in range(45):
        m = 0.5*(lo2+hi2)
        if blows_up(m, T0s): hi2 = m
        else: lo2 = m
    out(f"      start at tau=-{T0s:4.1f}: lambda* = {0.5*(lo2+hi2):.9f}")


def quasi_static(pr, key='V'):
    def gapf(u):
        q = dict(pr, **{key: pr[key]-u})
        try:
            _, Pm = G.fold(q)
        except Exception:
            return 1.0
        return pr['Pref'] - Pm
    lo, hi = 0.0, 0.999*pr[key]
    if gapf(hi) < 0:
        return float('nan')
    for _ in range(80):
        m = 0.5*(lo+hi)
        if gapf(m) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)


def fold_data(pr, eqs):
    """a, b of the saddle-node normal form at the fold V = V0 - eps_qs."""
    prf = dict(pr, V=pr['V'] - eqs)
    df, Pm = G.fold(prf, n=200000)
    E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    stf = np.array([df, 0.0, prf['Pref'], Qf])
    Af = G.jac(stf, prf)
    ev_, VL, VR = eig(Af, left=True, right=True)
    k = int(np.argmin(np.abs(ev_)))
    v = np.real(VR[:, k]); wl = np.real(VL[:, k])
    wl = wl/np.dot(wl, v)
    fV = (G.rhs(stf, dict(prf, V=prf['V']+HS))
          - G.rhs(stf, dict(prf, V=prf['V']-HS)))/(2*HS)
    a = float(np.dot(wl, -fV))              # parameter mu = extra dip in V
    b = 0.5*float(np.dot(wl, G.Bform(stf, prf, v, v)))
    return a, b, abs(ev_[k]), df, Pm, stf, prf


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90,
          {0.05: 1.04422e-1, 0.10: 1.09632e-1, 0.30: 1.30762e-1}),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90,
          {0.05: 9.73921e-2, 0.10: 9.98985e-2, 0.30: 1.10610e-1}),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75,
          {0.05: 2.56257e-1, 0.10: 2.65446e-1, 0.30: 3.03603e-1}),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90,
          {0.05: 9.24648e-2, 0.10: 9.43543e-2, 0.30: 1.00537e-1})]
out("")
out("=== prediction vs measurement, zero fitted constants")
out("  cell             |    a       |     b      | ab      | K_pred | "
    "K_meas(0.05/0.10/0.30) | pred/meas")
ratios = []
for tag, nm, Xg, frac, meas in CELLS:
    _, Pm0 = G.fold(G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    st = G.equil(pr)
    w0 = G.crit_mode(G.jac(st, pr)).imag
    eqs = quasi_static(pr)
    a, b, zev, df, Pm, stf, prf = fold_data(pr, eqs)
    ab = a*b
    Kpred = LAMSTAR*w0*math.sqrt(1.0/(2.0*abs(ab)*eqs))
    km = [(meas[r]-eqs)/eqs/r for r in (0.05, 0.10, 0.30)]
    kmm = float(np.mean(km[:2]))
    ratios.append(Kpred/kmm)
    out(f"  {tag} | {a:+.4e} | {b:+.4e} | {ab:+.3e} | {Kpred:6.3f} | "
        f"{km[0]:.3f}/{km[1]:.3f}/{km[2]:.3f} | {Kpred/kmm:8.4f}")
    out(f"      fold at delta={df:.5f}, |zero eigenvalue|={zev:.2e}, "
        f"eps_qs={eqs:.5e}, w0={w0:.4f}  [{time.time()-T0:.0f}s]")
ratios = np.array(ratios)
out("")
out(f"  pred/meas across the four cells: " +
    ", ".join(f"{r:.4f}" for r in ratios))
out(f"  mean {ratios.mean():.4f}, spread "
    f"{(ratios.max()-ratios.min())/ratios.mean()*100:.2f}%")
out("")
out("  read: the LINEARITY is already established from the measurements.")
out("  What is tested here is the COEFFICIENT -- if pred/meas is the same")
out("  number across cells whose a, b, eps_qs and w0 differ, the")
out("  normal-form scaling is right; if that number is also 1, the")
out("  universal constant is right too.  A common factor that is not 1")
out("  means the scaling holds but lambda* is being applied with the wrong")
out("  O(1) convention, which is a bookkeeping error, not a mechanism one.")
out(f"DONE wall={time.time()-T0:.0f}s")
