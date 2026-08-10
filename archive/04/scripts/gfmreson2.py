"""High-frequency half of the band, searched DOWNWARD from eps_qs.

gfmreson found "no bracket" for cell B at w_p >= 0.7 w0 because its search
started at eps_qs: the threshold there is BELOW the static fold offset.
That is not a numerical detail -- it says the escape at those frequencies
is not the boundary reaching the operating point at all (that needs the
drive to close a gap of size eps_qs), but the drive pumping the swing mode
resonantly, which needs less.  The criterion branch changes from B3-ii to
the parametric/forced-orbit side.  So: search from 0.05 eps_qs upward and
report where eps_c/eps_qs crosses 1, which is where the mechanism swaps.

Original header follows.

Clean-protocol thresholds across the whole resonant band.

Two reasons this has to be re-measured before anything is fitted to it:

 (1) §20.3 showed the recorded eps_c at w_p >= 0.15 w0 is protocol sensitive
     -- starting at the UNFORCED equilibrium (an O(eps) offset from the
     quasi-static branch) versus starting ON the branch moves delta by up to
     12%.  The band's numbers were taken with the contaminated protocol.
 (2) The band was only ever sampled at 0.05/0.10/0.30/0.50/0.90.  A Melnikov
     prediction is a FUNCTION of frequency; comparing it against five points,
     four of which are outside the band, tests almost nothing.

So: clean protocol (initial state = stable equilibrium of V0 + eps, zero
transient), ten frequencies from 0.10 to 0.90 w0, every point checked for
the escape set being an interval, and the period count checked for
convergence at three points.  Budget ~45 min.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

LOG = open('sweep20/gfmreson2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()


def Pmax(pr):
    h = 1e-6
    def dP(dd):
        return (G.P_of(dd+h, pr) - G.P_of(dd-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(dd, pr) for dd in dl])
    i = int(np.argmax(Pv))
    df = brentq(dP, dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)],
                xtol=1e-14, rtol=1e-15)
    return df, G.P_of(df, pr)


def eps_qs_of(pr):
    def gap(uu):
        return Pmax(dict(pr, V=pr['V']-uu))[1] - pr['Pref']
    hi = 0.98*pr['V']; n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, 0.0, hi, xtol=1e-14, rtol=1e-15)


def escaped(pr, eps, wp, dsad, nper):
    x0 = G.equil(dict(pr, V=pr['V']+eps))
    if x0 is None:
        return True
    def fun(t, x):
        return G.rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
    def ev(t, x):
        return x[0] - dsad
    ev.terminal = True; ev.direction = 1
    s = solve_ivp(fun, (0.0, nper*2*math.pi/wp), x0, method='DOP853',
                  rtol=1e-11, atol=1e-13, events=(ev,))
    return len(s.t_events[0]) > 0


def thr(pr, wp, dsad, eqs, nper, nit=32):
    lo, hi = eqs*0.05, eqs*1.5
    n = 0
    while not escaped(pr, hi, wp, dsad, nper) and n < 10:
        lo = hi; hi *= 1.35; n += 1
    if not escaped(pr, hi, wp, dsad, nper) or escaped(pr, lo, wp, dsad, nper):
        return float('nan')
    for _ in range(nit):
        m = 0.5*(lo+hi)
        if escaped(pr, m, wp, dsad, nper): hi = m
        else: lo = m
    return 0.5*(lo+hi)


CELLS = [('A', 'M2', 0.5, 0.90), ('B', 'M3', 0.5, 0.90),
         ('C', 'M2', 0.3, 0.75), ('D', 'M3', 0.3, 0.90)]
RATS = [0.60, 0.70, 0.80, 0.90]
out("  cell  w_p/w0    nu      eps_c        eps_c/eps_qs   d/nu   interval "
    "nper-conv")
DAT = {}
for tag, nm, Xg, frac in CELLS:
    _, Pm0 = Pmax(G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    st = G.equil(pr)
    w0 = G.crit_mode(G.jac(st, pr)).imag
    eqs = eps_qs_of(pr)
    prf = dict(pr, V=pr['V']-eqs)
    df, _ = Pmax(prf)
    E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    stf = np.array([df, 0.0, prf['Pref'], Qf])
    from scipy.linalg import eig
    evv, VL, VR = eig(G.jac(stf, prf), left=True, right=True)
    k = int(np.argmin(np.abs(evv)))
    vv = np.real(VR[:, k]); wv = np.real(VL[:, k]); wv = wv/np.dot(wv, vv)
    HS = 1e-6
    fV = (G.rhs(stf, dict(prf, V=prf['V']+HS))
          - G.rhs(stf, dict(prf, V=prf['V']-HS)))/(2*HS)
    ab = abs(float(np.dot(wv, -fV))
             * 0.5*float(np.dot(wv, G.Bform(stf, prf, vv, vv))))
    dsad = G.equil(pr, branch='saddle')[0]
    rows = []
    for r in RATS:
        wp = r*w0
        nper = 8
        ec = thr(pr, wp, dsad, eqs, nper)
        if ec != ec:
            out(f"   {tag}   {r:.2f}    ---  no bracket"); continue
        flips = 0; prev = None
        for f in (0.98, 1.0, 1.005, 1.02, 1.06, 1.12):
            g = escaped(pr, ec*f, wp, dsad, nper)
            if prev is not None and g != prev: flips += 1
            prev = g
        conv = ''
        if r in (0.20, 0.50, 0.90):
            e2 = thr(pr, wp, dsad, eqs, 2*nper)
            conv = f"{(e2/ec-1)*100:+.3f}%"
        nu = wp/math.sqrt(2.0*ab*eqs)
        rows.append((r, wp, nu, ec, ec/eqs))
        out(f"   {tag}   {r:.2f}  {nu:.4f}  {ec:.6e}   {ec/eqs:.5f}   "
            f"{(ec/eqs-1)/nu:.4f}  {'ok' if flips == 1 else f'FLIPS={flips}'}"
            f"  {conv}   [{time.time()-T0:.0f}s]")
    DAT[tag] = dict(eqs=eqs, w0=w0, ab=ab, rows=rows)
out("")
out("  eps_qs / w0 / ab per cell (for the Melnikov comparison):")
for tag in DAT:
    d = DAT[tag]
    out(f"   {tag}  eps_qs={d['eqs']:.6e}  w0={d['w0']:.5f}  ab={d['ab']:.5e}")
out(f"DONE wall={time.time()-T0:.0f}s")
