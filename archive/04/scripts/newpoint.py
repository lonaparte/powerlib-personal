import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, sympy as sp
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()
KPP,KIP,KPV,KIV,CDC = 50.0,1000.0,1.0,50.0,0.01
th,Xg,Q,Vg,P = sp.symbols('theta X_g Q V_g P', real=True)
a=Vg*sp.cos(th); b=Vg*sp.sin(th); vgd0=a-Xg*Q; id0=b/Xg
J=sp.Matrix([
 [-KPP*a, KIP, -KPP*Xg*KPV, KPP*Xg*KIV],
 [-a,0,-Xg*KPV,Xg*KIV],
 [sp.Rational(3,2)/CDC*(-b*id0-Q*a),0,
  sp.Rational(3,2)/CDC*(-(vgd0*KPV+Q*Xg*KPV+vgd0*id0)),
  sp.Rational(3,2)/CDC*(vgd0*KIV+Q*Xg*KIV)],
 [0,0,-1,0]])
lam=sp.symbols('lambda'); cp=sp.Poly(J.charpoly(lam).as_expr(),lam)
c3,c2,c1,c0=[cp.nth(k) for k in (3,2,1,0)]
R=c1*c2*c3-c1**2-c0*c3**2
E=P+sp.Rational(3,2)*vgd0*id0; Eth=sp.diff(E,th)
RP,RQ,RV,RX,Rth=[sp.diff(R,v) for v in (P,Q,Vg,Xg,th)]
EP,EQ,EV,EX=[sp.diff(E,v) for v in (P,Q,Vg,Xg)]

def maxRe(P0,Xg0):
    p=S.make_p(idc_src=P0,Xg=Xg0); eq=S.stable_eq(p,cfg)
    if eq is None: return None
    return float(np.linalg.eigvals(S.jacobian(eq,p,cfg)[:4,:4]).real.max())
def dRe_num(P0,Xg0,knob,h=1e-4):
    def mr(**kw):
        p=S.make_p(idc_src=P0,Xg=Xg0,**kw); eq=S.stable_eq(p,cfg)
        c=[e for e in np.linalg.eigvals(S.jacobian(eq,p,cfg)[:4,:4]) if abs(e.imag)>1e-6]
        return max(c,key=lambda z:z.real).real
    base={'iq_ref':0.0,'Vg':1.0}
    if knob=='P':
        return (mr()* 0 + ( (lambda: [ (lambda pp: max([e for e in np.linalg.eigvals(S.jacobian(S.stable_eq(pp,cfg),pp,cfg)[:4,:4]) if abs(e.imag)>1e-6],key=lambda z:z.real).real)(S.make_p(idc_src=P0+s*h,Xg=Xg0)) for s in (1,-1)] )() ) )[0:1] and None
    return None

def analytic_dR(P0,Xg0):
    p=S.make_p(idc_src=P0,Xg=Xg0); eq=S.stable_eq(p,cfg); t=eq[0]
    sub={th:t,Xg:Xg0,Q:0.0,Vg:1.0,P:P0}
    eth=float(Eth.subs(sub))
    def tot(Rp,Ep): return float(Rp.subs(sub))+float(Rth.subs(sub))*(-float(Ep.subs(sub))/eth)
    return dict(P=tot(RP,EP),Q=tot(RQ,EQ),V=tot(RV,EV),Xg=tot(RX,EX))

def numeric_dRe(P0,Xg0,h=1e-4):
    out={}
    for knob,kw in [('P','idc_src'),('Q','iq_ref'),('V','Vg'),('Xg','Xg')]:
        base=dict(idc_src=P0,Xg=Xg0)
        th0=getattr(S.make_p(**base),kw)
        def mr(val):
            kk=dict(base); kk[kw]=val; p=S.make_p(**kk); eq=S.stable_eq(p,cfg)
            c=[e for e in np.linalg.eigvals(S.jacobian(eq,p,cfg)[:4,:4]) if abs(e.imag)>1e-6]
            return max(c,key=lambda z:z.real).real
        out[knob]=(mr(th0+h)-mr(th0-h))/(2*h)
    return out

for P0 in [0.5,1.0]:
    SN=3*1.0/(4*P0*1.0)
    # find Hopf: scan Xg up toward SN
    lo,hi=0.1,SN*0.999; hopf=None; prev=maxRe(P0,lo)
    for Xg0 in np.linspace(lo,hi,200):
        m=maxRe(P0,Xg0)
        if m is None: break
        if prev is not None and prev<0<=m: hopf=Xg0; break
        prev=m
    Xg_test = (hopf*0.99 if hopf else hi*0.98)
    print("="*90)
    print(f"P={P0}: saddle-node Xg={SN:.3f}, Hopf≈{hopf if hopf else '>range'}, test point Xg={Xg_test:.4f}")
    dRe=numeric_dRe(P0,Xg_test); dR=analytic_dR(P0,Xg_test)
    # geometric prediction 1/P : 2/V : 1/Xg  (V=1)
    geo={'P':1/P0,'V':2/1.0,'Xg':1/Xg_test}
    print(f"  numeric dRe/dθ :  P={dRe['P']:+.1f}  Q={dRe['Q']:+.1f}  V={dRe['V']:+.1f}  Xg={dRe['Xg']:+.1f}")
    nP=abs(dRe['P'])
    print(f"     |ratio| P:Q:V:Xg = {abs(dRe['P'])/nP:.2f} : {abs(dRe['Q'])/nP:.2f} : {abs(dRe['V'])/nP:.2f} : {abs(dRe['Xg'])/nP:.2f}")
    print(f"  geometric predict P:V:Xg = {geo['P']/geo['P']:.2f} : {geo['V']/geo['P']:.2f} : {geo['Xg']/geo['P']:.2f}   (1/P : 2/V : 1/Xg)")
    print(f"  analytic dR/dθ signs   :  P={np.sign(dR['P']):+.0f} Q={np.sign(dR['Q']):+.0f} V={np.sign(dR['V']):+.0f} Xg={np.sign(dR['Xg']):+.0f}"
          f"   (dRe should be opposite)")
