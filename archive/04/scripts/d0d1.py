"""PR196 keeps two algebraic loops my model does not have.  How big are they HERE?

My GFL model freezes the line reactance: v_gq = -V sin(th) + Xg i_d, with no
dependence on the PLL frequency and no L_g di/dt.  PR196's carrier keeps both,
which closes two algebraic loops

    D0 = 1 - kp_pll L_g i_d                     (PLL side, speed emf)
    D1 = 1 + 1.5 kpv L_g i_d /(C V_dc)          (DC side, transformer emf)

Neither exists in my equations.  Their sizes depend on L_g = Xg/w_base, and my
model never declares w_base -- that is itself a gap.  Swept over w_base here,
with the whole 4-state rebuilt to carry both loops, so the answer is a measured
shift of alpha / w0 / P_Hopf, not an estimate.

    u D0 = kp(-V sin th + Xg i_d) + ki x_p
    v_gq = -V sin th + Xg i_d + u L_g i_d
    C D1 Vdc' = P + 1.5 i_d [V cos th + L_g kiv (1 - Vdc)]/Vdc
(i_q = 0 at this operating point, so the -(w+u)L_g i_q term in v_d drops out;
 R_g = 0, matching my model's other omission.)
"""
import math, time
import numpy as np, sympy as sp
from scipy.optimize import fsolve
exec(open('selfhead.py').read())
LOG = open('sweep20/d0d1.log', 'w')
def out(m): LOG.write(m+'\n'); LOG.flush()

TH,XP,VD,XI = sp.symbols('th xp Vdc xi', real=True)
P_,Q_,V_,Xg_,kp_,ki_,kpv_,kiv_,C_,Lg_ = sp.symbols(
    'P Q V Xg kp ki kpv kiv C Lg', real=True)
X = (TH,XP,VD,XI); PA = (P_,Q_,V_,Xg_,kp_,ki_,kpv_,kiv_,C_,Lg_)
idr = kpv_*(1-VD) + kiv_*XI
D0 = 1 - kp_*Lg_*idr
u  = (kp_*(-V_*sp.sin(TH) + Xg_*idr) + ki_*XP)/D0
vgq = -V_*sp.sin(TH) + Xg_*idr + u*Lg_*idr
D1 = 1 + sp.Rational(3,2)*kpv_*Lg_*idr/(C_*VD)
dV = (P_ + sp.Rational(3,2)*idr*(V_*sp.cos(TH) + Lg_*kiv_*(1-VD))/VD)/(C_*D1)
F = sp.Matrix([u, vgq, dV, 1-VD])
AR = X + PA
fn = sp.lambdify(AR, F, 'numpy')
Jn = sp.lambdify(AR, F.jacobian(sp.Matrix(X)), 'numpy')
D0n = sp.lambdify(AR, D0, 'numpy'); D1n = sp.lambdify(AR, D1, 'numpy')
def av(x, pr):
    return tuple(x)+tuple(pr[k] for k in ('P','Q','V','Xg','kp','ki','kpv',
                                          'kiv','C','Lg'))
def rh(x, pr): return np.array(fn(*av(x,pr)),float).ravel()
def jc(x, pr): return np.array(Jn(*av(x,pr)),float)
def eq(pr):
    for t0 in (-0.3,-0.6,-0.9):
        i0 = -pr['P']/(1.5*pr['V']*math.cos(t0))
        z,_,ier,_ = fsolve(lambda z: rh(z,pr), [t0,0.,1.,i0/pr['kiv']],
                           full_output=True)
        if ier==1 and np.max(np.abs(rh(z,pr)))<1e-10: return z
    return None
def crit(A):
    ev=np.linalg.eigvals(A); cx=[e for e in ev if e.imag>1e-9]
    return max(cx,key=lambda z:z.real) if cx else None

prb = gset('G1')
Ps = 3*prb['V']**2/(4*prb['Xg'])
def hopf(pr0):
    gr = np.linspace(0.3,0.99,150)*Ps; vv=[]
    for P in gr:
        q=dict(pr0,P=P); x=eq(q)
        c=crit(jc(x,q)) if x is not None else None
        vv.append(None if c is None else c.real)
    for a_,b_,fa,fb in zip(gr[:-1],gr[1:],vv[:-1],vv[1:]):
        if fa is not None and fb is not None and fa<0<=fb:
            lo,hi=a_,b_
            for _ in range(50):
                mm=0.5*(lo+hi); q=dict(pr0,P=mm); x=eq(q)
                c=crit(jc(x,q)) if x is not None else None
                if c is None or c.real>=0: hi=mm
                else: lo=mm
            return 0.5*(lo+hi)
    return None
# reference: Lg = 0 reproduces selfhead exactly
pr0 = dict(prb, Lg=0.0)
x0 = eq(pr0); ref = crit(jc(x0,pr0)); PH0 = hopf(pr0)
xs = equil(dict(prb,P=prb['P']))
out(f"consistency at Lg=0: this build vs selfhead rhs, max|diff| = "
    f"{np.max(np.abs(rh(xs,pr0)-rhs(xs,dict(prb,P=prb['P'])))):.2e}")
out(f"Lg=0: P_Hopf={PH0:.7f}   (selfhead 1.4551540)")
out("")
out("  w_base [rad/s]   L_g       D0       D1     P_Hopf      shift      "
    "alpha@P0       w0        d alpha    d w0")
P0 = margin_point(prb, 1.4551540, 0.10)
prr = dict(prb, P=P0, Lg=0.0); xr = eq(prr); lr = crit(jc(xr,prr))
out(f"   (Lg=0 ref)                            {PH0:.7f}     ---       "
    f"{-lr.real:.7f}  {lr.imag:.5f}     ---        ---")
for wb in (2*math.pi*50, 2*math.pi*60, 1000., 3000., 10000.):
    Lg = prb['Xg']/wb
    prl = dict(prb, P=P0, Lg=Lg)
    x = eq(prl)
    if x is None:
        out(f"  {wb:9.2f}  {Lg:.3e}  no equilibrium"); continue
    a = av(x, prl)
    l = crit(jc(x, prl)); PHl = hopf(dict(prb, Lg=Lg))
    out(f"  {wb:9.2f}  {Lg:.3e}  {float(D0n(*a)):+.4f}  {float(D1n(*a)):+.4f}  "
        f"{PHl:.7f}  {(PHl-PH0)/PH0:+8.4%}  {-l.real:.7f}  {l.imag:9.5f}  "
        f"{(-l.real+lr.real)/(-lr.real):+8.3%}  {(l.imag-lr.imag)/lr.imag:+7.3%}")
out("")
out("  note: i_d = -1.2304 here (IN-positive), so D1 < 1; PR196 uses")
out("  OUT-positive port current so their D1 = 1.28 > 1 -- same term.")
out("DONE")
