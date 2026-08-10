"""My own recorded 1100/x is a probe artifact -- check it.

gflinner.py measured the inner loop with a FIRST-ORDER lag,
    di/dt = w_c (i* - i)   =>  H1(s) = w_c/(s+w_c) = 1 - s/w_c + O(s^2)
whose deviation from ideal tracking is O(1/w_c).  A real current loop is PI,
whose closed loop (qaxis.py) is
    H(s) = (2 zc wc s + wc^2)/(s^2 + 2 zc wc s + wc^2) = 1 - s^2/wc^2 + ...
i.e. deviation O(1/w_c^2).  If alpha inherits the order of the tracking
error, the recorded law d alpha/alpha ~ 1100/x must become ~ K/x^2, and the
quoted number is then wrong by a factor x at realistic bandwidth.

Measured here, on the SAME operating point and the SAME 4-state reference:
absolute d alpha, relative d alpha/alpha, d w0, and -- the metric a boundary
study would actually use -- the shift of the Hopf point P_H and of the
crossing frequency, for BOTH loop forms.
"""
import math, time
import numpy as np
from scipy.linalg import eig
from scipy.optimize import fsolve
import sympy as sp
exec(open('selfhead.py').read())
_qsrc = open('qaxis.py').read()
exec(_qsrc.split('# ---------------------------------------------------'
                 '-------------- models')[1].split('M6 = build')[0])
LOG = open('sweep20/piscale.log', 'w')
def out(m):
    LOG.write(m+'\n'); LOG.flush()
T0 = time.time()

# ---- first-order-lag 5-state (the gflinner form), rebuilt here
TH1, XP1, VD1, XI1, ID1 = sp.symbols('th xp Vdc xi idl', real=True)
X5 = (TH1, XP1, VD1, XI1, ID1)
idr1 = skpv*(1-VD1) + skiv*XI1
vgd1 = sV*sp.cos(TH1) - sXg*sQ
vgq1 = -sV*sp.sin(TH1) + sXg*ID1
F5 = sp.Matrix([skp*vgq1 + ski*XP1, vgq1,
                (sP + sp.Rational(3,2)*(vgd1*ID1 + vgq1*sQ)/VD1)/sC,
                1-VD1, swc*(idr1-ID1)])
AR5 = X5 + PP
f5n = sp.lambdify(AR5, F5, 'numpy')
J5n = sp.lambdify(AR5, F5.jacobian(sp.Matrix(X5)), 'numpy')
def av5(x, pr):
    return tuple(x)+tuple(pr[k] for k in ('P','Q','V','Xg','kp','ki','kpv',
                                          'kiv','C','wc','zc','kq','Vref'))
def jac5(x, pr): return np.array(J5n(*av5(x, pr)), float)
def rhs5(x, pr): return np.array(f5n(*av5(x, pr)), float).ravel()

M6 = build('M6')
prb = gset('G1')
def crit_of(A, n):
    ev = np.linalg.eigvals(A)
    cx = [e for e in ev if e.imag > 1e-9]
    return max(cx, key=lambda z: z.real)

def alpha_at(P, x, form):
    pr = dict(prb, P=P, zc=0.707, kq=0., Vref=0., wc=x*W0REF)
    st4 = equil(pr)
    if st4 is None: return None
    idr = pr['kpv']*(1-st4[2]) + pr['kiv']*st4[3]
    if form == 'pi':
        st = np.array([st4[0], st4[1], st4[2], st4[3], idr, 0.0])
        A = jacn(M6, st, pr)
    else:
        st = np.array([st4[0], st4[1], st4[2], st4[3], idr])
        A = jac5(st, pr)
    return crit_of(A, len(st))

# 4-state reference
Ps = 3*prb['V']**2/(4*prb['Xg'])
grid = np.linspace(0.05, 0.985, 60)*Ps
va = []
for P in grid:
    qd = dict(prb, P=P); xx = equil(qd)
    cm = crit_mode(jac(xx, qd)) if xx is not None else None
    va.append(None if cm is None else cm.real)
for a_,b_,fa,fb in zip(grid[:-1],grid[1:],va[:-1],va[1:]):
    if fa is not None and fb is not None and fa<0<=fb:
        lo,hi=a_,b_
        for _ in range(50):
            mm=0.5*(lo+hi); qd=dict(prb,P=mm); xx=equil(qd)
            cm=crit_mode(jac(xx,qd)) if xx is not None else None
            if cm is None or cm.real>=0: hi=mm
            else: lo=mm
        PH4=0.5*(lo+hi); break
co4 = nf_coeffs(dict(prb, P=margin_point(prb, PH4, 0.10)))
W0REF = co4['w0']; A4 = co4['alpha']; P0 = margin_point(prb, PH4, 0.10)
lam4 = crit_of(jac(equil(dict(prb,P=PH4)), dict(prb,P=PH4)), 4)
out(f"4-state: P_H={PH4:.7f} (crossing w={lam4.imag:.4f}), "
    f"P0={P0:.7f}, alpha={A4:.7f}, w0={W0REF:.5f}")
out("")
out("=== alpha at the FIXED operating point P0 (margin 0.10)")
out("   x     PI: alpha      d alpha    d a/a      x^2*(da/a) |"
    "  1st-order: alpha    d a/a      x*(da/a)")
for x in (10., 30., 100., 300., 1000., 3000.):
    lp = alpha_at(P0, x, 'pi'); l1 = alpha_at(P0, x, 'lag')
    ap = -lp.real; a1 = -l1.real
    rp = (ap-A4)/A4; r1 = (a1-A4)/A4
    out(f" {x:6.0f}  {ap:.8f}  {ap-A4:+.3e}  {rp:+.5%}  {x*x*rp:8.1f}   |"
        f"  {a1:11.6f}  {r1:+.4%}  {x*r1:8.1f}")
out("")
out("=== the boundary itself: Hopf point and crossing frequency")
out("   x     form   P_Hopf       shift vs 4-state   crossing w")
for form in ('pi', 'lag'):
    for x in (10., 30., 100., 300., 1000.):
        def g(P):
            l = alpha_at(P, x, form)
            return None if l is None else l.real
        gr = np.linspace(0.5, 0.99, 120)*Ps
        vv = [g(P) for P in gr]; br=None
        for a_,b_,fa,fb in zip(gr[:-1],gr[1:],vv[:-1],vv[1:]):
            if fa is not None and fb is not None and fa<0<=fb:
                br=(a_,b_); break
        if br is None:
            out(f" {x:6.0f}  {form:4s}   no crossing in [0.5,0.99]Ps"); continue
        lo,hi=br
        for _ in range(50):
            mm=0.5*(lo+hi); v=g(mm)
            if v is None or v>=0: hi=mm
            else: lo=mm
        PHx=0.5*(lo+hi); lx = alpha_at(PHx, x, form)
        out(f" {x:6.0f}  {form:4s}   {PHx:.7f}  {(PHx-PH4)/PH4:+9.4%}   "
            f"w={lx.imag:8.4f}  (4-state {lam4.imag:.4f})")
out(f"DONE wall={time.time()-T0:.0f}s")
