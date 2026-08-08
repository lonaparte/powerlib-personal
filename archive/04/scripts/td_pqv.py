import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from scipy.signal import find_peaks
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.fault_v2 import _rk4_step
cfg=S.make_cfg()

def eig_crit(kw):
    p=S.make_p(**kw); e=S.stable_eq(p,cfg)
    if e is None: return None,None
    ev=[z for z in np.linalg.eigvals(S.jacobian(e,p,cfg)[:4,:4]) if abs(z.imag)>1e-6]
    return (max(ev,key=lambda z:z.real) if ev else None), e

def td_measure(kw,T=4.0,dt=2e-5,pert=1e-4):
    p=S.make_p(**kw); eq=S.stable_eq(p,cfg)
    if eq is None: return None
    x=eq.copy().astype(float); x[0]+=pert; x[4]=p.omega0
    ts=[]; d=[]
    for k in range(int(T/dt)):
        x=_rk4_step(x,p,dt)
        if not math.isfinite(x[0]) or abs(x[0]-eq[0])>0.5: break
        if k%10==0: ts.append(k*dt); d.append(x[0]-eq[0])
    ts=np.array(ts); d=np.array(d)
    if len(ts)<50: return None
    m=ts>0.3; tsm=ts[m]; dm=d[m]
    pk,_=find_peaks(dm)
    pk=[i for i in pk if dm[i]>0]
    if len(pk)<3: return None
    tp=tsm[pk]; ap=np.abs(dm[pk])
    rate=np.polyfit(tp,np.log(ap),1)[0]; freq=1.0/np.mean(np.diff(tp))
    return rate,freq

def sweep(name, base, knob, vals):
    print(f"\n=== sweep {name}  (fixed { {k:v for k,v in base.items()} }) ===")
    print(f"  {name:>7}{'Reλ(eig)':>10}{'rate(TD)':>10}{'f_H eig[Hz]':>12}{'f TD[Hz]':>9}{'  verdict':>17}")
    for v in vals:
        kw=dict(base); kw[knob]=v
        lam,eq=eig_crit(kw)
        if lam is None:
            print(f"  {v:>7.3f}   no equilibrium (past saddle-node)"); continue
        fe=abs(lam.imag)/(2*math.pi); td=td_measure(kw)
        if td is None:
            print(f"  {v:>7.3f}{lam.real:>10.2f}{'—':>10}{fe:>12.3f}{'—':>9}   (TD: no clean fit)"); continue
        rate,ft=td
        print(f"  {v:>7.3f}{lam.real:>10.2f}{rate:>10.2f}{fe:>12.3f}{ft:>9.3f}   {'STABLE' if lam.real<0 else 'UNSTABLE(grow)'}")

sweep("P", dict(iq_ref=0.0,Vg=1.0,Xg=1.0), "idc_src", [0.60,0.70,0.735,0.742,0.746,0.749])
sweep("V", dict(idc_src=0.5,iq_ref=0.0,Xg=1.0), "Vg", [0.95,0.88,0.84,0.828,0.820,0.817])
sweep("Q", dict(idc_src=0.5,Vg=1.0,Xg=1.0), "iq_ref", [0.0,0.2,0.35,0.42,0.46,0.50])
