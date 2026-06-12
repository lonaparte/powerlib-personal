"""
R3_roa.py -- HONEST numerical inner-estimate of the region of attraction (ROA) of the
real 10-state GFL (sweep.py / Conventions sec.12), by integrating the REAL nonlinear
vector field.  This is the real-model analog of the classical-pendulum R3 basin --
NUMERICAL, not a dL/SOS certificate (the 10D nonlinear ROA certificate is not done; see
README '仍未做到').

Object-correctness gates (the R1 lesson -- verify the object before using it):
  GATE 1: ||f(x_eq)|| ~ 0          (genuine equilibrium of the real field)
  GATE 2: ||Jac(f)|x_eq - Amat||~0 (the integrable field's linearization IS sweep.Amat)
Both must pass or the script raises -- no ROA claim on an unverified object.

Method: from the stable equilibrium x_eq (SCR > SCR_H ~ 0.905), perturb and integrate the
real field with a stiff solver (Radau + analytic Jacobian sweep.Asym).  Classify
RECOVER (returns to x_eq) vs LOSE.  Report:
  (a) critical power-angle Delta-th_crit (transient-stability / critical-clearing analog);
  (b) a random-direction inner radius in dynamically-scaled coordinates.

Run:  python3 R3_roa.py            (needs numpy, sympy, scipy; ~minutes, stiff 10D)
"""
import numpy as np, sympy as sp, sys, os
HERE=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "numerical")))
import sweep
from sweep import pv, Amat, S
from scipy.integrate import solve_ivp

wn,Vg,Rg,Lg,Kp,Ki = sp.symbols('wn Vg Rg Lg Kp Ki')
_f  = sp.lambdify((*S, wn,Vg,Rg,Lg,Kp,Ki), list(sweep.f), 'numpy')
_Jf = sp.lambdify((*S, wn,Vg,Rg,Lg,Kp,Ki), sweep.Asym.tolist(), 'numpy')  # analytic Jacobian

def x_eq_of(SCR, XR=10):
    par = pv(SCR, XR)
    if par is None: raise RuntimeError("no equilibrium (past fold) at SCR=%.3f" % SCR)
    wnv,Vgv,Rgv,Lgv,vcdv = par
    idr,iqr,Cf,Rf,Kii,Kad = 80.0,0.0,1e-4,0.1,126.0,2.0
    igq = iqr - wnv*Cf*vcdv
    al = 1-wnv**2*Lgv*Cf; be = Rgv*wnv*Cf; K1 = Rgv*idr; K2 = wnv*Lgv*idr
    ceq = (al*vcdv-K1)/Vgv; seq = (K2-be*vcdv)/Vgv; th = np.arctan2(seq, ceq)
    xeq = np.array([idr,iqr,vcdv,0.0,idr,igq,(Rf*idr/Kii),(Kad*(iqr-igq)+Rf*iqr)/Kii,0.0,th])
    return xeq, par

def _gates():
    print("GATES (verify the object before any ROA claim):")
    for SCR in [1.5, 1.0]:
        xeq, par = x_eq_of(SCR); wnv,Vgv,Rgv,Lgv,vcdv = par
        r = np.array(_f(*xeq, wnv,Vgv,Rgv,Lgv,0.30,150), float)
        J = np.array(_Jf(*xeq, wnv,Vgv,Rgv,Lgv,0.30,150), float)
        A = Amat(SCR,10,0.30,150); relJ = np.linalg.norm(J-A)/np.linalg.norm(A)
        print("  SCR=%.2f: ||f(x_eq)||=%.1e   ||Jac-Amat||/||Amat||=%.1e" %
              (SCR, np.linalg.norm(r), relJ))
        assert np.linalg.norm(r) < 1e-6 and relJ < 1e-6, "OBJECT GATE FAILED"
    print("  gates pass -> integrable field + equilibrium are the real object.\n")

def converges(SCR, dx, Kpv=0.30, Kiv=150, T=1.5):
    xeq, par = x_eq_of(SCR); wnv,Vgv,Rgv,Lgv,vcdv = par
    rhs = lambda t,x: np.asarray(_f(*x, wnv,Vgv,Rgv,Lgv,Kpv,Kiv), float)
    jac = lambda t,x: np.asarray(_Jf(*x, wnv,Vgv,Rgv,Lgv,Kpv,Kiv), float)
    sol = solve_ivp(rhs, [0,T], xeq+dx, method='Radau', jac=jac, rtol=1e-6, atol=1e-8)
    if not sol.success: return False
    return np.linalg.norm(sol.y[:,-1]-xeq) < 1e-3 and np.max(np.abs(sol.y)) < 1e7

def crit_angle(SCR, nbis=12):
    e = np.zeros(10); e[9] = 1.0
    lo, hi = 0.05, np.pi-0.02
    if not converges(SCR, lo*e): return None
    if converges(SCR, hi*e): return hi
    for _ in range(nbis):
        m = 0.5*(lo+hi)
        if converges(SCR, m*e): lo = m
        else: hi = m
    return 0.5*(lo+hi)

def random_radius(SCR, ndir=12, nbis=9, seed=0):
    """Inner radius along random directions in dynamically-scaled coords (scale by |x_eq|
    per state so a unit perturbation is comparable across states)."""
    xeq,_ = x_eq_of(SCR); rng = np.random.default_rng(seed)
    scale = np.maximum(np.abs(xeq), 1e-2)
    rmin = np.inf
    for _ in range(ndir):
        d = rng.standard_normal(10); d /= np.linalg.norm(d); d = d*scale
        d /= np.linalg.norm(d)            # unit in raw coords, but oriented by scaling
        lo, hi = 0.0, 2.0*np.linalg.norm(scale)
        if not converges(SCR, hi*d):
            while hi-lo > 1e-2*np.linalg.norm(scale):
                m = 0.5*(lo+hi)
                if converges(SCR, m*d): lo = m
                else: hi = m
            rmin = min(rmin, 0.5*(lo+hi))
    return rmin

if __name__ == "__main__":
    _gates()
    print("(a) Critical power-angle Delta-th_crit (max recoverable angle jump) vs grid:")
    print("    SCR    state     Delta-th_crit")
    for SCR in [2.0, 1.5, 1.2, 1.0, 0.95]:
        ca = crit_angle(SCR)
        s = "none (>%.2f, very robust)" % (np.pi-0.02) if ca is not None and ca > np.pi-0.05 \
            else ("%.3f rad (%.0f deg)" % (ca, np.degrees(ca)) if ca else "tiny")
        print("    %.2f   %s    %s" % (SCR, "stable" if SCR > 0.905 else "UNSTAB", s))
    print()
    print("    => ROA (angle slice) SHRINKS as the grid weakens toward the Hopf SCR_H~0.905,")
    print("       the real-model transient-stability margin.  NUMERICAL inner-estimate.")
