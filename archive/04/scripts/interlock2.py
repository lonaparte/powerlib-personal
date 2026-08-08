import sys, math, itertools; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, sympy as sp, warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); CDC=0.01; KPP,KIP,KPV,KIV=50.0,1000.0,1.0,50.0
th,Xg,Q,Vg = sp.symbols('theta X_g Q V_g', real=True)
a=Vg*sp.cos(th); b=Vg*sp.sin(th); vgd0=a-Xg*Q; id0=b/Xg
Jsym=sp.Matrix([[-KPP*a,KIP,-KPP*Xg*KPV,KPP*Xg*KIV],[-a,0,-Xg*KPV,Xg*KIV],
 [sp.Rational(3,2)/CDC*(-b*id0-Q*a),0,sp.Rational(3,2)/CDC*(-(vgd0*KPV+Q*Xg*KPV+vgd0*id0)),
  sp.Rational(3,2)/CDC*(vgd0*KIV+Q*Xg*KIV)],[0,0,-1,0]])
Jf=sp.lambdify((th,Xg,Q,Vg),Jsym,'numpy')
def st(P0,Q0,V0,Xg0):
    p=S.make_p(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); eq=S.stable_eq(p,cfg)
    if eq is None: return None
    A=S.jacobian(eq,p,cfg)[:4,:4]
    if np.max(np.linalg.eigvals(A).real)>0: return None   # only stable pts
    return p,eq,A
def crit(A):
    ev,Ve=np.linalg.eig(A); W=np.linalg.inv(Ve)
    c=[i for i in range(4) if abs(ev[i].imag)>1e-6]
    if not c: return None
    i=c[int(np.argmax(ev[c].real))]; return ev[i],Ve[:,i],W[i,:]
def dRe(P0,Q0,V0,Xg0,kn,h=1e-4):
    m={'P':'idc_src','Q':'iq_ref','V':'Vg','Xg':'Xg'}[kn]; base=dict(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); k0=base[m]
    def mr(v):
        kk=dict(base); kk[m]=v; p=S.make_p(**kk); eq=S.stable_eq(p,cfg)
        if eq is None: return np.nan
        cc=[e for e in np.linalg.eigvals(S.jacobian(eq,p,cfg)[:4,:4]) if abs(e.imag)>1e-6]
        return max(cc,key=lambda z:z.real).real if cc else np.nan
    return (mr(k0+h)-mr(k0-h))/(2*h)
def dTh(P0,Q0,V0,Xg0,kn,h=1e-4):
    m={'P':'idc_src','Q':'iq_ref','V':'Vg','Xg':'Xg'}[kn]; base=dict(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); k0=base[m]
    def t(v):
        kk=dict(base); kk[m]=v; e=S.stable_eq(S.make_p(**kk),cfg); return e[0] if e is not None else np.nan
    return (t(k0+h)-t(k0-h))/(2*h)

grid=[]
for P0,Q0,V0 in itertools.product([0.3,0.5,0.8],[-0.2,0.0,0.2],[0.9,1.0,1.1]):
    SN=3*V0**2/(4*P0)
    for frac in [0.5,0.85,0.95]:
        if st(P0,Q0,V0,SN*frac): grid.append((P0,Q0,V0,SN*frac))
print(f"stable grid points: {len(grid)}\n")

e1=eQrel=e4=e5=0.0
for (P0,Q0,V0,Xg0) in grid:
    p,eq,An=st(P0,Q0,V0,Xg0); t=eq[0]
    e1=max(e1,np.max(np.abs(np.array(Jf(t,Xg0,Q0,V0),dtype=float)-An)))
    h=1e-5
    pP=p.copy();pP.iq_ref=Q0+h; pM=p.copy();pM.iq_ref=Q0-h
    dAQ=(S.jacobian(eq,pP,cfg)[:4,:4]-S.jacobian(eq,pM,cfg)[:4,:4])/(2*h)
    dAQa=np.zeros((4,4)); dAQa[2,0]=-1.5*V0*math.cos(t)/CDC; dAQa[2,2]=1.5*V0*math.sin(t)/CDC
    eQrel=max(eQrel,np.max(np.abs(dAQ-dAQa))/max(1.0,np.max(np.abs(dAQa))))
    f=Xg0*math.sin(t)/(V0*math.cos(2*t)); e5=max(e5,abs(f-dTh(P0,Q0,V0,Xg0,'Q')))
    cm=crit(An)
    if cm:
        lam,vi,wi=cm
        dRT=dRe(P0,Q0,V0,Xg0,'P')/dTh(P0,Q0,V0,Xg0,'P')
        ind=dRT*f; direct=float(np.real(wi@dAQa@vi))
        e4=max(e4,abs((ind+direct)-dRe(P0,Q0,V0,Xg0,'Q')))
print(f"TEST 1  analytic J == numeric J          : max|diff| = {e1:.2e}   {'PASS' if e1<1e-5 else 'FAIL'}")
print(f"TEST 2  ∂A/∂Q == analytic 2-entry (relerr): {eQrel:.2e}          {'PASS' if eQrel<1e-2 else 'FAIL'}")
print(f"TEST 3  ∂θ*/∂Q formula                    : max|diff| = {e5:.2e}   {'PASS' if e5<1e-3 else 'FAIL'}")
print(f"TEST 4  Q = indirect+direct == dRe/dQ     : max|diff| = {e4:.3f}    {'PASS' if e4<0.5 else 'CHECK'}")

bad=0; tot=0
for (P0,Q0,V0,Xg0) in grid:
    ss=[dRe(P0,Q0,V0,Xg0,k) for k in ['P','Q','V','Xg']]
    if any(math.isnan(x) for x in ss): continue
    tot+=1
    if not (ss[2]<0 and ss[0]>0 and ss[1]>0 and ss[3]>0): bad+=1
print(f"TEST 5  sign law (V<0; P,Q,Xg>0)          : {tot-bad}/{tot} points obey   {'PASS' if bad==0 else f'{bad} exceptions'}")

print("\nTEST 6  ratio |dRe/dθ| P:V:Xg  vs geometric 1/P:2/V:1/Xg  (convergence toward Hopf):")
for (P0,V0) in [(0.5,1.0),(0.8,1.1),(0.3,0.9)]:
    SN=3*V0**2/(4*P0); print(f"  P={P0} V={V0} (SN Xg={SN:.2f}):")
    for frac in [0.6,0.85,0.95,0.99]:
        Xg0=SN*frac
        if st(P0,0.0,V0,Xg0) is None: continue
        dP=abs(dRe(P0,0,V0,Xg0,'P'));dV=abs(dRe(P0,0,V0,Xg0,'V'));dX=abs(dRe(P0,0,V0,Xg0,'Xg'))
        num=np.array([dP,dV,dX])/dP; geo=np.array([1/P0,2/V0,1/Xg0]); geo=geo/geo[0]
        print(f"    %SN={frac:4.2f} Xg={Xg0:5.3f}: numeric {num[0]:.2f}:{num[1]:.2f}:{num[2]:.2f}   geom {geo[0]:.2f}:{geo[1]:.2f}:{geo[2]:.2f}")

print("\nTEST 7  Routh R sign flips exactly at Hopf (several P):")
for P0 in [0.4,0.7,1.0]:
    lam2=sp.symbols('L'); cp=sp.Poly(Jsym.charpoly(lam2).as_expr(),lam2)
    c3,c2,c1,c0=[cp.nth(k) for k in (3,2,1,0)]; Rf=sp.lambdify((th,Xg,Q,Vg),c1*c2*c3-c1**2-c0*c3**2,'numpy')
    SN=3/(4*P0); prev=None
    for Xg0 in np.linspace(0.3,SN*0.999,300):
        s=st(P0,0,1.0,Xg0)
        e=S.stable_eq(S.make_p(idc_src=P0,Xg=Xg0),cfg)
        if e is None: continue
        A=S.jacobian(e,S.make_p(idc_src=P0,Xg=Xg0),cfg)[:4,:4]; mr=np.max(np.linalg.eigvals(A).real); Rv=float(Rf(e[0],Xg0,0,1.0))
        if prev and prev[0]<0<=mr:
            print(f"    P={P0}: maxRe crosses 0 at Xg≈{Xg0:.3f}; R goes {prev[1]:+.1e} → {Rv:+.1e} (R=0 at Hopf)"); break
        prev=(mr,Rv)
