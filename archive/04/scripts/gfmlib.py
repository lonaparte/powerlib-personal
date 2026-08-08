"""Shared GFM (4-state minimal VSM) machinery for the parity campaign.
State x = (delta, omega, Pf, Qf).
E = Enom - mq*(Qf - Qref);  Pe = E*V*sin(d)/Xg;  Qe = (E^2 - E*V*cos(d))/Xg
f = [omega, (Pref - Pf - D*omega)/M, wc*(Pe - Pf), wc*(Qe - Qf)]
Identical to prior-session model (gfm_vsm4_hopf.py / gfm_close_gaps.py).
REBUILT after worker restart wiped the originals; includes both fixes:
 - equilibrium fsolve polish
 - left-eigenvector normalization p/np.vdot(q, p)  (<p,q> = 1, not c/cbar)
"""
import math, numpy as np, sympy as sp
from scipy.optimize import brentq
from scipy.integrate import solve_ivp

Enom = 1.0

_x = sp.symbols('d om Pf Qf', real=True)
_p = sp.symbols('Pref Qref V Xg M D mq wc', real=True)
d_, om_, Pf_, Qf_ = _x
Pref_, Qref_, V_, Xg_, M_, D_, mq_, wc_ = _p
E_ = Enom - mq_*(Qf_ - Qref_)
Pe_ = E_*V_*sp.sin(d_)/Xg_
Qe_ = (E_**2 - E_*V_*sp.cos(d_))/Xg_
f_ = sp.Matrix([om_, (Pref_ - Pf_ - D_*om_)/M_, wc_*(Pe_ - Pf_), wc_*(Qe_ - Qf_)])
_args = _x + _p
f_num = sp.lambdify(_args, f_, 'numpy')
J_ = f_.jacobian(sp.Matrix(_x))
J_num = sp.lambdify(_args, J_, 'numpy')
_H = [[[sp.lambdify(_args, sp.diff(f_[i], _x[j], _x[k]), 'numpy')
        for k in range(4)] for j in range(4)] for i in range(4)]
_T = [[[[sp.lambdify(_args, sp.diff(f_[i], _x[j], _x[k], _x[l]), 'numpy')
         for l in range(4)] for k in range(4)] for j in range(4)] for i in range(4)]

def _av(st, pr):
    return tuple(st) + (pr['Pref'], pr['Qref'], pr['V'], pr['Xg'],
                        pr['M'], pr['D'], pr['mq'], pr['wc'])

def rhs(st, pr):
    return np.array(f_num(*_av(st, pr)), float).ravel()

def jac(st, pr):
    return np.array(J_num(*_av(st, pr)), float)

def Bform(st, pr, u, v):
    a = _av(st, pr)
    return np.array([sum(_H[i][j][k](*a)*u[j]*v[k]
                         for j in range(4) for k in range(4)) for i in range(4)])

def Cform(st, pr, u, v, w):
    a = _av(st, pr)
    return np.array([sum(_T[i][j][k][l](*a)*u[j]*v[k]*w[l]
                         for j in range(4) for k in range(4) for l in range(4))
                     for i in range(4)])

def E_of(d, pr):
    a = pr['mq']/pr['Xg']
    b = 1 - pr['mq']*pr['V']*math.cos(d)/pr['Xg']
    c = -(Enom + pr['mq']*pr['Qref'])
    if a < 1e-12:
        return -c/b
    disc = b*b - 4*a*c
    return (-b + math.sqrt(disc))/(2*a)

def P_of(d, pr):
    E = E_of(d, pr)
    return E*pr['V']*math.sin(d)/pr['Xg']

def fold(pr, n=6000):
    dl = np.linspace(1e-3, math.pi - 1e-3, n)
    Pv = np.array([P_of(d, pr) for d in dl])
    i = int(np.argmax(Pv))
    return dl[i], Pv[i]

def equil(pr, branch='stable'):
    df, Pm = fold(pr)
    P = pr['Pref']
    if P >= Pm:
        return None
    if branch == 'stable':
        d = brentq(lambda x: P_of(x, pr) - P, 1e-6, df)
    else:
        d = brentq(lambda x: P_of(x, pr) - P, df, math.pi - 1e-3)
    E = E_of(d, pr)
    Qf = (E*E - E*pr['V']*math.cos(d))/pr['Xg']
    from scipy.optimize import fsolve
    def res(z):
        s = np.array([z[0], 0.0, P, z[1]])
        r = rhs(s, pr)
        return [r[2], r[3]]
    z = fsolve(res, [d, Qf], full_output=False)
    st = np.array([z[0], 0.0, P, z[1]])
    assert np.max(np.abs(rhs(st, pr))) < 1e-8, np.max(np.abs(rhs(st, pr)))
    return st

def crit_mode(A):
    ev = np.linalg.eigvals(A)
    cx = [e for e in ev if e.imag > 1e-9]
    if not cx:
        return None
    return max(cx, key=lambda z: z.real)

def maxre_cx(pr):
    st = equil(pr)
    if st is None:
        return None
    lam = crit_mode(jac(st, pr))
    return None if lam is None else lam.real

def hopf_in(pr, key, lo, hi, tol=1e-10):
    def g(v):
        q = dict(pr); q[key] = v
        return maxre_cx(q)
    glo, ghi = g(lo), g(hi)
    if glo is None or ghi is None or glo*ghi > 0:
        return None
    for _ in range(60):
        mid = 0.5*(lo + hi)
        gm = g(mid)
        if gm is None:
            return None
        if (gm > 0) == (glo > 0):
            lo = mid
        else:
            hi = mid
        if hi - lo < tol*max(1, abs(hi)):
            break
    q = dict(pr); q[key] = 0.5*(lo + hi)
    return q

def _eig_lr(A):
    from scipy.linalg import eig
    ev, vl, vr = eig(A, left=True, right=True)
    return ev, vl, vr

def hopf_c1(pr):
    st = equil(pr)
    A = jac(st, pr)
    lam = crit_mode(A)
    w0 = lam.imag
    ev, VL, VR = _eig_lr(A)
    k = int(np.argmin(np.abs(ev - lam)))
    q = VR[:, k]
    p = VL[:, k]
    p = p/np.vdot(q, p)                # <p,q> = 1  (divide by conj(p^H q))
    B = lambda u, v: Bform(st, pr, u, v)
    C = lambda u, v, w: Cform(st, pr, u, v, w)
    h11 = np.linalg.solve(A, B(q, q.conj()))
    h20 = np.linalg.solve(2j*w0*np.eye(4) - A, B(q, q))
    g21 = np.vdot(p, C(q, q, q.conj())) - 2*np.vdot(p, B(q, h11)) \
          + np.vdot(p, B(q.conj(), h20))
    return dict(st=st, lam=lam, w0=w0, c1=g21/2, q=q, p=p)

def simulate(pr, x0, T, forcing=None, events=None, rtol=1e-9, max_step=None):
    if forcing is None:
        fun = lambda t, x: rhs(x, pr)
    else:
        def fun(t, x):
            q = dict(pr)
            for k, dv in forcing(t).items():
                q[k] = pr[k] + dv
            return rhs(x, q)
    kw = dict(method='DOP853', rtol=rtol, atol=1e-12, dense_output=True)
    if events is not None:
        kw['events'] = events
    if max_step is not None:
        kw['max_step'] = max_step
    return solve_ivp(fun, (0, T), x0, **kw)

def escape_event(pr):
    ss = equil(pr, branch='saddle')
    dsad = ss[0] if ss is not None else math.pi
    def ev(t, x):
        return x[0] - dsad
    ev.terminal = True
    ev.direction = 1
    return ev, dsad

def mset(name, **over):
    base = dict(M1=dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*31),
                M2=dict(M=0.1, D=0.2, mq=0.05, wc=2*math.pi*10),
                M3=dict(M=0.005, D=0.02, mq=0.2, wc=2*math.pi*100),
                M4=dict(M=0.05, D=0.5, mq=0.1, wc=2*math.pi*5),
                M5=dict(M=0.02, D=0.02, mq=0.1, wc=2*math.pi*20))[name]
    pr = dict(Pref=0.5, Qref=0.0, V=1.0, Xg=0.1, **base)
    pr.update(over)
    return pr
