"""Is the second-order collapse a property of the INTEGRATOR, or of zeta_c?

If the O(1/wc^2) law comes from the current loop's integrator (H(s)-1 = O(s^2)),
it must hold for every zeta_c, and the first-order lag must stay first order for
every choice of its pole.  If instead 0.707 was lucky, the exponent will move.
Fitted exponent from consecutive x, plus the prefactor.
"""
import math, time
import numpy as np, sympy as sp
exec(open('selfhead.py').read())
_qsrc = open('qaxis.py').read()
exec(_qsrc.split('# ---------------------------------------------------'
                 '-------------- models')[1].split('M6 = build')[0])
LOG = open('sweep20/piscale2.log', 'w')
def out(m): LOG.write(m+'\n'); LOG.flush()
M6 = build('M6')
prb = gset('G1')
Ps = 3*prb['V']**2/(4*prb['Xg'])
grid = np.linspace(0.05, 0.985, 60)*Ps
va=[]
for P in grid:
    qd=dict(prb,P=P); xx=equil(qd)
    cm=crit_mode(jac(xx,qd)) if xx is not None else None
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
P0=margin_point(prb,PH4,0.10); co4=nf_coeffs(dict(prb,P=P0))
W0=co4['w0']; A4=co4['alpha']
st4=equil(dict(prb,P=P0))
def alpha6(x, zc):
    pr=dict(prb,P=P0,zc=zc,kq=0.,Vref=0.,wc=x*W0)
    idr=pr['kpv']*(1-st4[2])+pr['kiv']*st4[3]
    A=jacn(M6,np.array([st4[0],st4[1],st4[2],st4[3],idr,0.0]),pr)
    ev=np.linalg.eigvals(A)
    return -max((e for e in ev if e.imag>1e-9), key=lambda z:z.real).real
out(f"4-state alpha={A4:.8f}  w0={W0:.5f}")
out(" zeta_c |   x=100 d a/a   x=300     x=1000  | fitted exponent (100->300, 300->1000)")
XS=[100.,300.,1000.]
for zc in (0.5, 0.707, 1.0, 2.0, 5.0):
    r=[(alpha6(x,zc)-A4)/A4 for x in XS]
    e1=math.log(r[0]/r[1])/math.log(XS[1]/XS[0])
    e2=math.log(r[1]/r[2])/math.log(XS[2]/XS[1])
    out(f"  {zc:5.3f} | {r[0]:+.6%}  {r[1]:+.6%}  {r[2]:+.6%} |"
        f"  {e1:.4f}   {e2:.4f}   K=x^2*(da/a)={XS[1]**2*r[1]:.1f}")
out("")
out("  same table for the FIRST-ORDER lag form (gflinner probe):")
TH1,XP1,VD1,XI1,ID1 = sp.symbols('th xp Vdc xi idl', real=True)
X5=(TH1,XP1,VD1,XI1,ID1)
idr1=skpv*(1-VD1)+skiv*XI1
vgd1=sV*sp.cos(TH1)-sXg*sQ; vgq1=-sV*sp.sin(TH1)+sXg*ID1
F5=sp.Matrix([skp*vgq1+ski*XP1, vgq1,
              (sP+sp.Rational(3,2)*(vgd1*ID1+vgq1*sQ)/VD1)/sC, 1-VD1,
              swc*(idr1-ID1)])
J5n=sp.lambdify(X5+PP, F5.jacobian(sp.Matrix(X5)), 'numpy')
def alpha5(x):
    pr=dict(prb,P=P0,zc=0.707,kq=0.,Vref=0.,wc=x*W0)
    idr=pr['kpv']*(1-st4[2])+pr['kiv']*st4[3]
    a=(st4[0],st4[1],st4[2],st4[3],idr)+tuple(pr[k] for k in
        ('P','Q','V','Xg','kp','ki','kpv','kiv','C','wc','zc','kq','Vref'))
    ev=np.linalg.eigvals(np.array(J5n(*a),float))
    return -max((e for e in ev if e.imag>1e-9), key=lambda z:z.real).real
r=[(alpha5(x)-A4)/A4 for x in (300.,1000.,3000.)]
e1=math.log(r[0]/r[1])/math.log(1000/300.); e2=math.log(r[1]/r[2])/math.log(3.)
out(f"    x=300 {r[0]:+.4%}  x=1000 {r[1]:+.4%}  x=3000 {r[2]:+.4%}"
    f"   exponents {e1:.4f} / {e2:.4f}")
out("DONE")
