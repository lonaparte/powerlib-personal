"""Self-contained header: GFL model + NF coefficients (inline, wipe-proof)."""
import math, numpy as np, sympy as sp
from scipy.optimize import fsolve
from scipy.integrate import solve_ivp
from scipy.linalg import eig

def gset(name='G1', **over):
    base = dict(G1=dict(kp=50., ki=1000., kpv=1., kiv=50., C=0.01))[name]
    pr = dict(P=1.0, Q=0.0, V=1.0, Xg=0.5, **base)
    pr.update(over)
    return pr

def rhs(x, pr):
    th, xp, Vdc, xi = x
    idr = pr['kpv']*(1 - Vdc) + pr['kiv']*xi
    vgd = pr['V']*math.cos(th) - pr['Xg']*pr['Q']
    vgq = -pr['V']*math.sin(th) + pr['Xg']*idr
    Vs = Vdc if abs(Vdc) > 1e-6 else 1e-6
    return np.array([pr['kp']*vgq + pr['ki']*xp, vgq,
                     (pr['P'] + 1.5*(vgd*idr + vgq*pr['Q'])/Vs)/pr['C'],
                     1 - Vdc])

def equil(pr):
    def res(x): return rhs(x, pr)
    for t0 in (-0.3, -0.6, -0.9):
        i0 = -pr['P']/(1.5*(pr['V']*math.cos(t0) - pr['Xg']*pr['Q']))
        z, info, ier, _ = fsolve(res, [t0, 0., 1., i0/pr['kiv']],
                                 full_output=True)
        if ier == 1 and np.max(np.abs(res(z))) < 1e-9:
            return z
    return None

def jac(x, pr, h=1e-7):
    A = np.zeros((4, 4))
    for i in range(4):
        e = np.zeros(4); e[i] = h
        A[:, i] = (rhs(x+e, pr) - rhs(x-e, pr))/(2*h)
    return A

def crit_mode(A):
    ev = np.linalg.eigvals(A)
    cx = [e for e in ev if e.imag > 1e-9]
    return max(cx, key=lambda z: z.real) if cx else None

def margin_point(pr, PH, target):
    lo, hi = 0.5*PH, PH
    def g(P):
        q = dict(pr, P=P)
        return crit_mode(jac(equil(q), q)).real
    for _ in range(40):
        m = 0.5*(lo+hi)
        if g(m) < -target: lo = m
        else: hi = m
    return 0.5*(lo+hi)

_x = sp.symbols('th xp Vdc xi', real=True)
_pp = sp.symbols('P Q V Xg kp ki kpv kiv C', real=True)
th_, xp_, Vdc_, xi_ = _x
P_, Q_, V_, Xg_, kp_, ki_, kpv_, kiv_, C_ = _pp
idr_ = kpv_*(1 - Vdc_) + kiv_*xi_
vgd_ = V_*sp.cos(th_) - Xg_*Q_
vgq_ = -V_*sp.sin(th_) + Xg_*idr_
f_ = sp.Matrix([kp_*vgq_ + ki_*xp_, vgq_,
                (P_ + sp.Rational(3, 2)*(vgd_*idr_ + vgq_*Q_)/Vdc_)/C_,
                1 - Vdc_])
_args = _x + _pp
_Hl = [[[sp.lambdify(_args, sp.diff(f_[i], _x[j], _x[k]), 'numpy')
         for k in range(4)] for j in range(4)] for i in range(4)]
_Tl = [[[[sp.lambdify(_args, sp.diff(f_[i], _x[j], _x[k], _x[l]), 'numpy')
          for l in range(4)] for k in range(4)] for j in range(4)] for i in range(4)]

def _avl(st, pr):
    return tuple(st) + (pr['P'], pr['Q'], pr['V'], pr['Xg'],
                        pr['kp'], pr['ki'], pr['kpv'], pr['kiv'], pr['C'])

def nf_coeffs(pr):
    st = equil(pr)
    A = jac(st, pr)
    ev, vl, vr = eig(A, left=True, right=True)
    k = max((i for i in range(4) if ev[i].imag > 1e-9), key=lambda i: ev[i].real)
    lam = ev[k]
    q = vr[:, k]; p = vl[:, k]
    p = p/np.vdot(q, p)
    h = 1e-6
    BV = (rhs(st, dict(pr, V=pr['V']+h)) - rhs(st, dict(pr, V=pr['V']-h)))/(2*h)
    a = _avl(st, pr)
    def B2c(u, v):
        return np.array([sum(_Hl[i][j][kk](*a)*u[j]*v[kk]
                             for j in range(4) for kk in range(4))
                         for i in range(4)])
    def C3c(u, v, w):
        return np.array([sum(_Tl[i][j][kk][l](*a)*u[j]*v[kk]*w[l]
                             for j in range(4) for kk in range(4)
                             for l in range(4)) for i in range(4)])
    w0 = lam.imag
    h11 = np.linalg.solve(A, B2c(q, q.conj()))
    h20 = np.linalg.solve(2j*w0*np.eye(4) - A, B2c(q, q))
    g21 = np.vdot(p, C3c(q, q, q.conj())) - 2*np.vdot(p, B2c(q, h11)) \
          + np.vdot(p, B2c(q.conj(), h20))
    return dict(st=st, lam=lam, alpha=-lam.real, w0=w0, c1=g21/2,
                fcoef=np.vdot(p, BV), q=q, p=p)
