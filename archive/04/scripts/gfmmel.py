"""The GFM resonant band's named object, finally computed.

Every round has said the same thing: "the correct object for the resonant
band is a Melnikov-type adjoint integral along the boundary orbit, not
derived".  Naming an object five times is not deriving it.  Here it is.

The basin boundary is W^s(x_s) of the saddle.  The low-frequency criterion
already on record uses the boundary's LINEAR response at two points,
s(w) = <n, H(w) - H_s(w)>, and it fails in the band (-12.6...-56.8%) for a
stated reason: at threshold the forced displacement is 24-82% of the gap, so
a linearisation about the saddle is being asked to describe a boundary that
has moved most of the way to the operating point.

The Melnikov object replaces the saddle-local response by an integral along
the actual boundary orbit.  For a periodic perturbation eps cos(w t) entering
through f_V, the first-order normal displacement of W^s at a base point
x_b(0) is eps Re{ M(w) e^{i w t0} } with

    M_b(w) = INT_0^inf  <n(t), f_V(x_b(t))> e^{i w t} dt                 (M)

where x_b(t) is the orbit of W^s through the base point (x_b -> x_s as
t -> +inf) and n(t) solves the ADJOINT variational equation
ndot = -A(x_b(t))^T n with n -> n_s, the left eigenvector of the UNSTABLE
eigenvalue (which is exactly the normal to W^s at x_s).  n(t) decays like
e^{-lambda_u t}, so (M) converges.

The operating point moves too, so the closing distance is governed by

    S(w) = <n(0), H(w)> - M_b(w) ,   H(w) = (i w I - A_0)^{-1} f_V

and, normalising on the exact static fold offset so that nothing is fitted,

    eps_c(w_p) = eps_qs |S(0)| / |S(w_p)|                                (MB)

At w -> 0 this reduces to the recorded quasi-static construction with the
saddle-local response replaced by the integral, so (MB) is a strict
generalisation, not a different theory.

What is genuinely being tested is the SHAPE: |S(w)| is the Fourier transform
of a decaying oscillatory function whose oscillation frequency is set by the
boundary orbit's own dynamics, so it predicts WHERE the band is, not just how
deep.  A prediction that puts the peak at the wrong frequency is refuted
regardless of amplitude.

Two arbitrary choices are made explicit and their effect measured, rather
than buried: (i) which orbit of the 3-D W^s to use -- swept over all stable
eigendirections and both signs; (ii) where to put the base point -- swept
along the orbit.  If the ratio (MB) moves much under either, the object is
not yet canonical and that is the result.
"""
import math, time, re
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.linalg import eig

LOG = open('sweep20/gfmmel.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
HS = 1e-6

MEAS = {}
try:
    for ln in open('sweep20/gfmreson.log'):
        m = re.match(r'\s+([ABCD])\s+([\d.]+)\s+([\d.]+)\s+([\d.e+-]+)\s+'
                     r'([\d.]+)\s', ln)
        if m:
            MEAS.setdefault(m.group(1), []).append(
                (float(m.group(2)), float(m.group(4)), float(m.group(5))))
except FileNotFoundError:
    pass

CELLS = [('A', 'M2', 0.5, 0.90), ('B', 'M3', 0.5, 0.90),
         ('C', 'M2', 0.3, 0.75), ('D', 'M3', 0.3, 0.90)]
from scipy.optimize import brentq


def Pmax(pr):
    h = 1e-6
    def dP(dd):
        return (G.P_of(dd+h, pr) - G.P_of(dd-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(dd, pr) for dd in dl])
    i = int(np.argmax(Pv))
    return brentq(dP, dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)],
                  xtol=1e-14, rtol=1e-15)


def eps_qs_of(pr):
    def gap(uu):
        q = dict(pr, V=pr['V']-uu)
        return G.P_of(Pmax(q), q) - pr['Pref']
    hi = 0.98*pr['V']; n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, 0.0, hi, xtol=1e-14, rtol=1e-15)


def fV_at(x, pr):
    return (G.rhs(x, dict(pr, V=pr['V']+HS))
            - G.rhs(x, dict(pr, V=pr['V']-HS)))/(2*HS)


for tag, nm, Xg, frac in CELLS:
    Pm0 = G.P_of(Pmax(G.mset(nm, Xg=Xg)), G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    st = G.equil(pr); xs = G.equil(pr, branch='saddle')
    A0 = G.jac(st, pr); As = G.jac(xs, pr)
    w0 = G.crit_mode(A0).imag
    eqs = eps_qs_of(pr)
    evs, VLs, VRs = eig(As, left=True, right=True)
    ku = int(np.argmax(evs.real))
    lu = evs[ku].real
    ns = np.real(VLs[:, ku]); ns = ns/np.linalg.norm(ns)
    if np.dot(ns, st - xs) < 0:
        ns = -ns
    f0 = fV_at(st, pr)
    out(f"=== cell {tag}  eps_qs={eqs:.6e}  w0={w0:.4f}  lambda_u={lu:.4f}")

    best = None
    for j in range(4):
        if j == ku or abs(evs[j].imag) > 1e-9 and evs[j].imag < 0:
            continue
        if evs[j].real >= 0:
            continue
        for sgn in (+1.0, -1.0):
            e = np.real(VRs[:, j]); e = e/np.linalg.norm(e)
            x0 = xs + sgn*1e-6*e
            r = solve_ivp(lambda t, x: -G.rhs(x, pr), (0, 400.0), x0,
                          method='DOP853', rtol=1e-11, atol=1e-14,
                          dense_output=True,
                          events=[lambda t, x: np.linalg.norm(x - xs) - 3.0])
            Tb = r.t[-1]
            ts = np.linspace(0, Tb, 4001)
            XB = r.sol(ts)                       # backward time: XB[:,0]=x_s
            d = np.linalg.norm(XB - st[:, None], axis=0)
            i0 = int(np.argmin(d))
            if best is None or d[i0] < best[0]:
                best = (d[i0], j, sgn, ts, XB, i0, Tb)
    dmin, jb, sgnb, ts, XB, i0, Tb = best
    out(f"    boundary orbit: stable dir {jb} sign {sgnb:+.0f}, closest "
        f"approach to the operating point {dmin:.4e} at backward time "
        f"{ts[i0]:.3f} s of {Tb:.1f} s")

    # forward-time orbit from the base point to the saddle
    def melnikov(i_base):
        tf = ts[i_base] - ts[:i_base+1][::-1]        # 0 .. ts[i_base]
        XF = XB[:, :i_base+1][:, ::-1]               # base -> ... -> saddle
        Amat = [G.jac(XF[:, k], pr) for k in range(len(tf))]
        gvec = np.array([np.dot(ns, fV_at(XF[:, k], pr))
                         for k in range(len(tf))])
        # adjoint: ndot = -A^T n, n(T) = ns ; integrate backward
        def adj(t, n):
            k = min(len(tf)-1, max(0, int(np.searchsorted(tf, t))))
            return -Amat[k].T @ n
        rn = solve_ivp(adj, (tf[-1], 0.0), ns, method='DOP853',
                       rtol=1e-10, atol=1e-14, dense_output=True)
        NV = rn.sol(tf)
        gg = np.array([np.dot(NV[:, k], fV_at(XF[:, k], pr))
                       for k in range(len(tf))])
        n0 = NV[:, 0]
        return tf, gg, n0

    tf, gg, n0 = melnikov(i0)
    out(f"    adjoint-weighted sensitivity along the orbit: |g(0)|="
        f"{abs(gg[0]):.4e}, |g(T)|={abs(gg[-1]):.4e}, T={tf[-1]:.3f} s")

    def S(wv):
        Mb = np.trapezoid(gg*np.exp(1j*wv*tf), tf)
        H = np.linalg.solve(1j*wv*np.eye(4) - A0, f0.astype(complex))
        return np.dot(n0, H) - Mb
    S0 = abs(S(1e-9))
    # old construction for comparison
    fs = fV_at(xs, pr)
    s0_old = abs(np.dot(ns, -np.linalg.solve(A0, f0)
                        + np.linalg.solve(As, fs)))

    def S_old(wv):
        H = np.linalg.solve(1j*wv*np.eye(4) - A0, f0.astype(complex))
        Hs = np.linalg.solve(1j*wv*np.eye(4) - As, fs.astype(complex))
        return abs(np.dot(ns, H - Hs))
    out("    w_p/w0 | eps_c meas  | Melnikov (MB) |  err   | old s0/|s| |"
        "  err")
    for r, ec, rat in MEAS.get(tag, []):
        wv = r*w0
        pm = eqs*S0/abs(S(wv))
        po = eqs*s0_old/S_old(wv)
        out(f"     {r:.2f}  | {ec:.6e} | {pm:.6e}  | {(pm-ec)/ec*100:+7.2f}% "
            f"| {po:.6e} | {(po-ec)/ec*100:+7.2f}%")
    out("    base-point sensitivity of the (MB) ratio at w = 0.5 w0:")
    for frac_b in (0.5, 0.75, 1.0, 1.25):
        ib = int(min(len(ts)-2, max(2, i0*frac_b)))
        tf2, gg2, n02 = melnikov(ib)

        def S2(wv):
            Mb = np.trapezoid(gg2*np.exp(1j*wv*tf2), tf2)
            H = np.linalg.solve(1j*wv*np.eye(4) - A0, f0.astype(complex))
            return np.dot(n02, H) - Mb
        out(f"      base at {frac_b:.2f} x closest-approach: ratio "
            f"S(0)/|S(0.5w0)| = {abs(S2(1e-9))/abs(S2(0.5*w0)):.5f}")
    out(f"    [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
