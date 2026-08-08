import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from scipy.signal import find_peaks
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.fault_v2 import _rk4_step
cfg=S.make_cfg()
def eig(kw):
    p=S.make_p(**kw); e=S.stable_eq(p,cfg)
    if e is None: return None,None
    c=[z for z in np.linalg.eigvals(S.jacobian(e,p,cfg)[:4,:4]) if abs(z.imag)>1e-6]
    return (max(c,key=lambda z:z.real) if c else None), e
def td(kw,T=4.0,dt=2e-5,pert=1e-4):
    p=S.make_p(**kw); e=S.stable_eq(p,cfg)
    if e is None: return None
    x=e.copy().astype(float); x[0]+=pert; x[4]=p.omega0; ts=[];d=[]
    for k in range(int(T/dt)):
        x=_rk4_step(x,p,dt)
        if not math.isfinite(x[0]) or abs(x[0]-e[0])>0.5: break
        if k%10==0: ts.append(k*dt); d.append(x[0]-e[0])
    ts=np.array(ts); d=np.array(d)
    if len(ts)<50: return None
    m=ts>0.3; pk,_=find_peaks(d[m]); pk=[i for i in pk if d[m][i]>0]
    if len(pk)<3: return None
    tp=ts[m][pk]; ap=np.abs(d[m][pk])
    return np.polyfit(tp,np.log(ap),1)[0], 1.0/np.mean(np.diff(tp))
def scan(name,base,knob,vals):
    print(f"\n=== Xg=0.5  sweep {name}  (fixed { {k:v for k,v in base.items()} }) ===")
    print(f"  {name:>7}{'Reλ(eig)':>10}{'rate(TD)':>10}{'f_H[Hz]':>9}{'f TD':>8}{'  verdict':>16}")
    for v in vals:
        kw=dict(base); kw[knob]=v; lam,e=eig(kw)
        if lam is None: print(f"  {v:>7.3f}   no eq (past SN)"); continue
        t=td(kw); fe=abs(lam.imag)/(2*math.pi)
        r = f"{t[0]:>10.2f}" if t else f"{'—':>10}"; ft=f"{t[1]:>8.3f}" if t else f"{'—':>8}"
        print(f"  {v:>7.3f}{lam.real:>10.2f}{r}{fe:>9.3f}{ft}   {'STABLE' if lam.real<0 else 'UNSTABLE(grow)'}")
# P: SN at 1.5
scan("P", dict(iq_ref=0.0,Vg=1.0,Xg=0.5), "idc_src", [1.0,1.3,1.45,1.485,1.495,1.499])
# V: SN at V=sqrt(4*0.5*0.5/3)=0.577
scan("V", dict(idc_src=0.5,iq_ref=0.0,Xg=0.5), "Vg", [0.70,0.62,0.60,0.585,0.580,0.578])
# Q: scan up to find its SN/Hopf
scan("Q", dict(idc_src=0.5,Vg=1.0,Xg=0.5), "iq_ref", [0.5,0.9,1.1,1.2,1.25,1.30])
