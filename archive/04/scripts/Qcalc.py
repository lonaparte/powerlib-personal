import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); CDC=0.01

def stuff(Xg0):
    p=S.make_p(Xg=Xg0,iq_ref=0.0,idc_src=0.5,Vg=1.0); eq=S.stable_eq(p,cfg); A=S.jacobian(eq,p,cfg)[:4,:4]
    th=eq[0]; V=1.0
    ev,Vec=np.linalg.eig(A); Wl=np.linalg.inv(Vec)
    c=[i for i in range(4) if abs(ev[i].imag)>1e-6]; i=c[int(np.argmax(ev[c].real))]
    vi=Vec[:,i]; wi=Wl[i,:]
    return th,V,A,ev[i],vi,wi

def dRe(knob,Xg0,h=1e-4):
    base=dict(Xg=Xg0,iq_ref=0.0,idc_src=0.5,Vg=1.0); k0=base[knob] if knob in base else getattr(S.make_p(**base),knob)
    def mr(val):
        kk=dict(base); kk[knob]=val; p=S.make_p(**kk); eq=S.stable_eq(p,cfg)
        cc=[e for e in np.linalg.eigvals(S.jacobian(eq,p,cfg)[:4,:4]) if abs(e.imag)>1e-6]; return max(cc,key=lambda z:z.real).real
    return (mr(k0+h)-mr(k0-h))/(2*h)
def dTheta(knob,Xg0,h=1e-4):
    base=dict(Xg=Xg0,iq_ref=0.0,idc_src=0.5,Vg=1.0); k0=getattr(S.make_p(**base),knob)
    def t(val):
        kk=dict(base); kk[knob]=val; return S.stable_eq(S.make_p(**kk),cfg)[0]
    return (t(k0+h)-t(k0-h))/(2*h)

print(f"{'Xg':>6}{'∂θ*/∂Q formula':>16}{'∂θ*/∂Q num':>13}{'∂Re/∂θ*':>10}"
      f"{'Q_indirect':>12}{'Q_direct(proj)':>15}{'sum':>9}{'dRe/dQ num':>12}")
for Xg0 in [0.5,1.0,1.45]:
    th,V,A,lam,vi,wi=stuff(Xg0)
    # analytic ∂θ*/∂Q = Xg sinθ* /(V cos2θ*)
    dthQ_f = Xg0*math.sin(th)/(V*math.cos(2*th))
    dthQ_n = dTheta('iq_ref',Xg0)
    # ∂Re/∂θ* from P (P is PURELY indirect: idc_src absent from Jacobian)
    dReTheta = dRe('idc_src',Xg0)/dTheta('idc_src',Xg0)
    Q_ind = dReTheta*dthQ_f
    # analytic ∂A/∂Q : only Vdc-row entries, ∝ 1/Cdc
    dAQ=np.zeros((4,4))
    dAQ[2,0]=-1.5*V*math.cos(th)/CDC        # coupling Δθ -> Vdc
    dAQ[2,2]= 1.5*V*math.sin(th)/CDC        # Vdc self
    Q_dir = float(np.real(wi @ dAQ @ vi))   # modal projection (direct channel)
    print(f"{Xg0:>6.2f}{dthQ_f:>16.4f}{dthQ_n:>13.4f}{dReTheta:>10.2f}"
          f"{Q_ind:>12.2f}{Q_dir:>15.2f}{Q_ind+Q_dir:>9.2f}{dRe('iq_ref',Xg0):>12.2f}")
