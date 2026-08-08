import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); kp=50.0; ki=1000.0

def mode(**kw):
    p=S.make_p(**kw); eq=S.stable_eq(p,cfg); A=S.jacobian(eq,p,cfg)
    c=[e for e in np.linalg.eigvals(A) if abs(e.imag)>1e-6]; lam=max(c,key=lambda z:z.real)
    return lam, eq[0]
def dTheta(knob,base,h=1e-4):
    th0=getattr(S.make_p(**base),knob)
    _,tp=mode(**{**base,knob:th0+h}); _,tm=mode(**{**base,knob:th0-h}); return (tp-tm)/(2*h)
def dRe_num(knob,base,h=1e-4):
    th0=getattr(S.make_p(**base),knob)
    lp,_=mode(**{**base,knob:th0+h}); lm,_=mode(**{**base,knob:th0-h}); return (lp.real-lm.real)/(2*h)

print("A) frequency ω_n: formula sqrt(ki·V·cosΔθ*) vs actual")
for Xg in [0.5,1.0]:
    lam,th=mode(Xg=Xg)
    print(f"   Xg={Xg}:  ω_n pred={math.sqrt(ki*math.cos(th)):.1f}   actual={abs(lam.imag):.1f}")

print("\nB) δ formula never →0  → predicts NO Hopf:")
mind=9
for Xg in np.linspace(0.1,1.499,60):
    lam,th=mode(Xg=Xg); mind=min(mind,0.5*kp*math.cos(th))
print(f"   min of ½kp·V·cosΔθ* over stable range = {mind:.1f}  (actual δ reaches ~0 at Hopf)")

print("\nC) dRe/dθ  pure-PLL prediction  vs  numeric   (at Xg=0.5):")
base=dict(idc_src=0.5,iq_ref=0.0,Vg=1.0,Xg=0.5); _,th=mode(**base)
for knob,nm in [("Vg","V"),("idc_src","P"),("iq_ref","Q"),("Xg","grid")]:
    if knob=="Vg":
        pred=-0.5*kp*math.cos(th)                  # direct
    else:
        pred=0.5*kp*1.0*math.sin(th)*dTheta(knob,base)   # indirect only
    num=dRe_num(knob,base)
    frac=pred/num*100 if num!=0 else float('nan')
    print(f"   {nm:>5}: pred={pred:8.2f}   numeric={num:8.2f}   captured={frac:5.0f}%")
