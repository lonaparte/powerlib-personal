"""Same probe on the GFM: does the current lag hit it the way it hits the GFL?

The GFL result was that the inner loop's O(1/w_c) error lands on alpha, which
is the SMALLEST quantity in the model (alpha/w0 = 0.003), so the relative
error is amplified out of control.  Whether that happens on the GFM is not a
matter of opinion -- the GFM's critical mode has zeta = 0.115-0.326, i.e. it
is NOT a high-Q resonator, and its criteria are built on fold data (a, b,
eps_qs) which are O(1) quantities.  If the diagnosis is right, the GFM should
degrade as a plain O(1/w_c) with O(1) prefactors.

Probe (exactly analogous to the GFL 5-state, and equilibrium-preserving):
    4-state:  i = (E<0 - V<-delta)/(j Xg)          algebraic, instantaneous
    6-state:  di/dt = w_cur (i* - i),  Pe = E i_d, Qe = -E i_q
w_cur -> infinity returns the 4-state exactly, and at equilibrium i = i* so
the equilibrium SET is unchanged -- hence eps_qs (a property of where two
equilibria merge) is unchanged EXACTLY.  Only the normal-form data a, b and
the Hopf-side alpha, w0 can move.  That itself is a structural difference
from the GFL and is worth showing rather than asserting.
"""
import math, time
import numpy as np
import sympy as sp
from scipy.linalg import eig
from scipy.optimize import fsolve, brentq
import gfmlib as G

LOG = open('sweep20/gfminner.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

d6, om6, Pf6, Qf6, id6, iq6 = sp.symbols('d om Pf Qf i_d i_q', real=True)
Pr, Qr, Vv, Xg, Mm, Dd, mq, wcf, wcu = sp.symbols(
    'Pref Qref V Xg M D mq wc wcur', real=True)
X6 = (d6, om6, Pf6, Qf6, id6, iq6)
E6 = 1.0 - mq*(Qf6 - Qr)
ids = Vv*sp.sin(d6)/Xg
iqs = (Vv*sp.cos(d6) - E6)/Xg
f6 = sp.Matrix([om6, (Pr - Pf6 - Dd*om6)/Mm,
                wcf*(E6*id6 - Pf6), wcf*(-E6*iq6 - Qf6),
                wcu*(ids - id6), wcu*(iqs - iq6)])
PA = (Pr, Qr, Vv, Xg, Mm, Dd, mq, wcf, wcu)
AR = X6 + PA
f6n = sp.lambdify(AR, f6, 'numpy')
J6n = sp.lambdify(AR, f6.jacobian(sp.Matrix(X6)), 'numpy')
H6 = sp.lambdify(AR, sp.Array([[[sp.diff(f6[i], X6[j], X6[k])
                                 for k in range(6)] for j in range(6)]
                                for i in range(6)]), 'numpy')


def av6(x, pr):
    return tuple(x) + (pr['Pref'], pr['Qref'], pr['V'], pr['Xg'], pr['M'],
                       pr['D'], pr['mq'], pr['wc'], pr['wcur'])


def rhs6(x, pr):
    return np.array(f6n(*av6(x, pr)), float).ravel()


def jac6(x, pr):
    return np.array(J6n(*av6(x, pr)), float)


def lift(st4, pr):
    """4-state equilibrium -> 6-state (currents slaved exactly)"""
    dd = st4[0]; E = 1.0 - pr['mq']*(st4[3] - pr['Qref'])
    return np.array([st4[0], 0.0, st4[2], st4[3],
                     pr['V']*math.sin(dd)/pr['Xg'],
                     (pr['V']*math.cos(dd) - E)/pr['Xg']])


def Pmax(pr):
    h = 1e-6
    def dP(x):
        return (G.P_of(x+h, pr) - G.P_of(x-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(x, pr) for x in dl])
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


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90)]
out("=== GFM 6-state probe: current lag with w_cur, equilibrium preserved")
out("  cell             |  zeta  |  w0(4st) | alpha(4st) | w_filt/w0 | "
    "w_cur/w0 | d alpha/alpha | d w0/w0  | d(ab)/ab")
for tag, nm, Xg_, frac in CELLS:
    pr0 = G.mset(nm, Xg=Xg_)
    pr = G.mset(nm, Xg=Xg_, Pref=frac*G.P_of(Pmax(pr0), pr0))
    st4 = G.equil(pr)
    lam4 = G.crit_mode(G.jac(st4, pr))
    a4 = -lam4.real; w04 = lam4.imag; z4 = a4/abs(lam4)
    eqs = eps_qs_of(pr)
    # 4-state fold data
    prf = dict(pr, V=pr['V']-eqs)
    df = Pmax(prf); E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    stf = np.array([df, 0.0, prf['Pref'], Qf])
    ev_, VL, VR = eig(G.jac(stf, prf), left=True, right=True)
    k = int(np.argmin(np.abs(ev_)))
    v = np.real(VR[:, k]); w = np.real(VL[:, k]); w = w/np.dot(w, v)
    HS = 1e-6
    fV = (G.rhs(stf, dict(prf, V=prf['V']+HS))
          - G.rhs(stf, dict(prf, V=prf['V']-HS)))/(2*HS)
    ab4 = float(np.dot(w, -fV))*0.5*float(np.dot(w, G.Bform(stf, prf, v, v)))
    for fac in (1000.0, 100.0, 30.0, 10.0):
        pr6 = dict(pr, wcur=fac*w04)
        x0 = lift(st4, pr6)
        assert np.max(np.abs(rhs6(x0, pr6))) < 1e-8
        ev6 = np.linalg.eigvals(jac6(x0, pr6))
        cx = [e for e in ev6 if e.imag > 1e-9]
        lam6 = min(cx, key=lambda z: abs(z - lam4))
        a6 = -lam6.real; w06 = lam6.imag
        # fold data in the 6-state (same fold point, currents slaved)
        pr6f = dict(prf, wcur=fac*w04)
        x0f = lift(stf, pr6f)
        A6 = jac6(x0f, pr6f)
        e6, L6, R6 = eig(A6, left=True, right=True)
        kk = int(np.argmin(np.abs(e6)))
        v6 = np.real(R6[:, kk]); w6 = np.real(L6[:, kk])
        w6 = w6/np.dot(w6, v6)
        f6V = (rhs6(x0f, dict(pr6f, V=pr6f['V']+HS))
               - rhs6(x0f, dict(pr6f, V=pr6f['V']-HS)))/(2*HS)
        Hm = np.array(H6(*av6(x0f, pr6f)), float)
        B6 = np.einsum('ijk,j,k->i', Hm, v6, v6)
        ab6 = float(np.dot(w6, -f6V))*0.5*float(np.dot(w6, B6))
        out(f"  {tag} | {z4:.4f} | {w04:8.4f} | {a4:.6f}   | "
            f"{pr['wc']/w04:8.2f} | {fac:7.0f} | {(a6/a4-1)*100:+12.4f}% | "
            f"{(w06/w04-1)*100:+7.4f}% | {(ab6/ab4-1)*100:+8.4f}%")
    out("")
out(f"  (eps_qs is EXACTLY unchanged: the equilibrium set is the same, and a")
out(f"   saddle-node is a property of that set, not of the Jacobian's size.)")
out(f"DONE wall={time.time()-T0:.0f}s")
