"""Does the OLD B3-ii formula already predict thresholds below eps_qs?

Last commit claimed: eps_c/eps_qs < 1 at high w_p proves the boundary-touching
object stopped being the binding constraint, because "the boundary has to
travel a distance eps_qs by definition".

That sentence is wrong if |s(w)| > s_0, because the recorded closed form is

    eps_uni(w) = eps_qs * s_0 / |s(w)| ,  s(w) = <n, H(w) - H_s(w)>

with H the operating point's linear response and H_s the SADDLE's.  At zero
frequency the two move quasi-statically and meet exactly at the fold, which
is why eps_uni(0) = eps_qs.  At finite frequency they move with different
transfer functions, so if the boundary responds MORE than the operating point
the two meet at a drive amplitude SMALLER than eps_qs -- boundary touching,
still, just with an amplified boundary.

So the claim is falsifiable in one line of linear algebra: compute
s_0/|s(w)| across the band.  If it drops below 1 where the measurement drops
below 1, the "branch change" reading is refuted and the old object still
applies (with the old accuracy problem, which is separate).

Second, independent discriminator, using data already in hand: a boundary
touching escapes on an early cycle, so its threshold is insensitive to the
number of drive periods simulated; a resonant PUMPING escape grows over many
cycles, so doubling the period count must lower the threshold appreciably.
The sweep already logged that check at three frequencies per cell.
"""
import math
import numpy as np
import gfmlib as G
from scipy.optimize import brentq
from scipy.linalg import eig

LOG = open('sweep20/scheck.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
HS = 1e-6


def Pmax(pr):
    h = 1e-6
    def dP(d):
        return (G.P_of(d+h, pr) - G.P_of(d-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(d, pr) for d in dl])
    i = int(np.argmax(Pv))
    return brentq(dP, dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)],
                  xtol=1e-14, rtol=1e-15)


def eps_qs_of(pr):
    def gap(u):
        q = dict(pr, V=pr['V']-u)
        return G.P_of(Pmax(q), q) - pr['Pref']
    hi = 0.98*pr['V']; n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, 0.0, hi, xtol=1e-14, rtol=1e-15)


def fu(x, pr):
    return (G.rhs(x, dict(pr, V=pr['V']+HS))
            - G.rhs(x, dict(pr, V=pr['V']-HS)))/(2*HS)


MEAS = {
 'A': {0.10: 1.10304, 0.15: 1.15703, 0.20: 1.21193, 0.30: 1.31720,
       0.40: 1.43558, 0.50: 1.52043, 0.60: 1.46975, 0.70: 1.49532,
       0.80: 1.60048, 0.90: 1.76181},
 'B': {0.10: 1.05259, 0.15: 1.07723, 0.20: 1.10252, 0.30: 1.15272,
       0.40: 1.09913, 0.50: 1.21024, 0.60: 1.08135, 0.70: 0.83483,
       0.80: 0.81338, 0.90: 0.93968},
 'C': {0.10: 1.07350, 0.15: 1.11001, 0.20: 1.14724, 0.30: 1.22025,
       0.40: 1.22605, 0.50: 1.34883, 0.60: 1.24086, 0.70: 1.04827,
       0.80: 1.18358, 0.90: 1.29158},
 'D': {0.10: 1.04226, 0.15: 1.06120, 0.20: 1.06618, 0.30: 1.11997,
       0.40: 0.98450, 0.50: 1.14332, 0.60: 0.99821, 0.70: 0.74520,
       0.80: 0.67411, 0.90: 0.78405}}
out("  the old B3-ii closed form across the band: does it ALSO go below 1?")
out("  cell  w_p/w0 |  s_0/|s(w)|  = eps_uni/eps_qs | measured eps_c/eps_qs |"
    " old-formula error")
for tag, nm, Xg, frac in [('A', 'M2', 0.5, 0.90), ('B', 'M3', 0.5, 0.90),
                          ('C', 'M2', 0.3, 0.75), ('D', 'M3', 0.3, 0.90)]:
    pr0 = G.mset(nm, Xg=Xg)
    pr = G.mset(nm, Xg=Xg, Pref=frac*G.P_of(Pmax(pr0), pr0))
    st = G.equil(pr); xs = G.equil(pr, branch='saddle')
    A0 = G.jac(st, pr); As = G.jac(xs, pr)
    w0 = G.crit_mode(A0).imag
    eqs = eps_qs_of(pr)
    evs, VLs, _ = eig(As, left=True, right=True)
    ks = int(np.argmax(evs.real))
    nv = np.real(VLs[:, ks]); nv = nv/np.linalg.norm(nv)
    if np.dot(nv, xs - st) < 0:
        nv = -nv
    f0 = fu(st, pr); fs = fu(xs, pr)
    s0 = abs(float(np.dot(nv, -np.linalg.solve(A0, f0)
                          + np.linalg.solve(As, fs))))
    for r in sorted(MEAS[tag]):
        wv = r*w0
        H = np.linalg.solve(1j*wv*np.eye(4) - A0, f0.astype(complex))
        Hs = np.linalg.solve(1j*wv*np.eye(4) - As, fs.astype(complex))
        sw = abs(np.dot(nv, H - Hs))
        rat = s0/sw
        em = MEAS[tag][r]
        out(f"   {tag}    {r:.2f}  |   {rat:9.5f}                | "
            f"{em:9.5f}             | {(rat-em)/em*100:+8.2f}%")
    out("")
out("  read: if s_0/|s| also dips below 1 where the measurement does, the")
out("  'boundary touching cannot produce eps_c < eps_qs' claim is refuted.")
