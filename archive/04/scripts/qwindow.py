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
    x=e.copy().astype(float); x[0]+=pert; x[4]=p.omega0; ts=[]; d=[]
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
print("Q growing-oscillation window (P=0.5,V=1,Xg=1):")
print(f"  {'Q':>7}{'Reλ(eig)':>10}{'rate(TD)':>10}{'f_H[Hz]':>9}{'f TD':>8}{'  verdict':>16}")
for Q0 in [0.240,0.243,0.245,0.247,0.249]:
    kw=dict(idc_src=0.5,iq_ref=Q0,Vg=1.0,Xg=1.0); lam,e=eig(kw)
    if lam is None: print(f"  {Q0:>7.3f}   no eq (past SN)"); continue
    t=td(kw); fe=abs(lam.imag)/(2*math.pi)
    if t is None: print(f"  {Q0:>7.3f}{lam.real:>10.2f}{'—':>10}{fe:>9.3f}{'—':>8}"); continue
    print(f"  {Q0:>7.3f}{lam.real:>10.2f}{t[0]:>10.2f}{fe:>9.3f}{t[1]:>8.3f}   {'STABLE' if lam.real<0 else 'UNSTABLE(grow)'}")
