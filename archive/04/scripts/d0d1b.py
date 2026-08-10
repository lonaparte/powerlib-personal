"""Before quoting the D0/D1 shifts: is the critical mode still the same mode?

The previous sweep gave alpha jumping 0.1 -> 14.8 -> -3.4 -> +2.3 and a
P_Hopf shift decaying like L_g^0.3 instead of L_g^1.  Non-analytic decay and
sign flips are the signature of the max-Re pair changing identity -- the exact
mistake just caught in the 1100/x probe.  Both pairs are printed here, plus
the pair tracked by eigenvector overlap from L_g=0, plus the crossing
frequency at each Hopf point.
"""
import math
import numpy as np, sympy as sp
from scipy.linalg import eig
from scipy.optimize import fsolve
exec(open('selfhead.py').read())
exec(open('d0d1.py').read().split('prb = gset')[0].split(
     'LOG = open')[1].split('\n',1)[1])
LOG = open('sweep20/d0d1b.log','w')
def out(m): LOG.write(m+'\n'); LOG.flush()
prb = gset('G1'); Ps = 3*prb['V']**2/(4*prb['Xg'])
P0 = margin_point(prb, 1.4551540, 0.10)
pr0 = dict(prb, P=P0, Lg=0.0); x0 = eq(pr0)
ev0,_,VR0 = eig(jc(x0,pr0), left=True, right=True)
k0 = max((i for i in range(4) if ev0[i].imag>1e-9), key=lambda i: ev0[i].real)
q0 = VR0[:,k0]/np.linalg.norm(VR0[:,k0])
out("  at the FIXED operating point P0: both complex pairs, and the pair")
out("  tracked from Lg=0 by eigenvector overlap")
out("  w_base     L_g       pair1              pair2            tracked        ovl")
for wb in (1e12, 2*math.pi*50, 2*math.pi*60, 1000., 3000., 10000., 30000.):
    Lg = prb['Xg']/wb; prl = dict(prb, P=P0, Lg=Lg); x = eq(prl)
    if x is None:
        out(f"  {wb:9.0f}  {Lg:.2e}  no equilibrium"); continue
    ev,_,VR = eig(jc(x,prl), left=True, right=True)
    cx = sorted([i for i in range(4) if ev[i].imag>1e-9],
                key=lambda i: -ev[i].real)
    ov = [abs(np.vdot(q0, VR[:,i]/np.linalg.norm(VR[:,i]))) for i in range(4)]
    j = int(np.argmax(ov))
    s = "  ".join(f"{ev[i].real:+8.4f}{ev[i].imag:+8.3f}j" for i in cx)
    out(f"  {wb:9.0f}  {Lg:.2e}  {s}   a={-ev[j].real:+8.4f} w={ev[j].imag:7.3f}"
        f"  {ov[j]:.4f}")
out("")
out("  Hopf point: crossing frequency (is the boundary set by the same mode?)")
def hopf2(pr0d):
    gr = np.linspace(0.3,0.99,150)*Ps; vv=[]
    for P in gr:
        q=dict(pr0d,P=P); x=eq(q)
        c=crit(jc(x,q)) if x is not None else None
        vv.append(None if c is None else c.real)
    for a_,b_,fa,fb in zip(gr[:-1],gr[1:],vv[:-1],vv[1:]):
        if fa is not None and fb is not None and fa<0<=fb:
            lo,hi=a_,b_
            for _ in range(50):
                mm=0.5*(lo+hi); q=dict(pr0d,P=mm); x=eq(q)
                c=crit(jc(x,q)) if x is not None else None
                if c is None or c.real>=0: hi=mm
                else: lo=mm
            PH=0.5*(lo+hi); q=dict(pr0d,P=PH); return PH, crit(jc(eq(q),q))
    return None, None
PH0,l0 = hopf2(dict(prb, Lg=0.0))
out(f"   Lg=0        P_H={PH0:.7f}  crossing w={l0.imag:.4f}")
for wb in (2*math.pi*50, 1000., 3000., 10000., 30000., 100000.):
    Lg = prb['Xg']/wb
    PH,l = hopf2(dict(prb, Lg=Lg))
    if PH is None: out(f"  {wb:9.0f}  no crossing"); continue
    out(f"  {wb:9.0f}  L_g={Lg:.2e}  P_H={PH:.7f}  {(PH-PH0)/PH0:+8.4%}  "
        f"crossing w={l.imag:8.4f}   L_g*(shift)={Lg*(PH-PH0)/PH0:+.3e}")
out("DONE")
