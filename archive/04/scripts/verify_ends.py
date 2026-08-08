import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from scipy.signal import find_peaks
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.system import find_eq
from gfl_5d_ou_sim.fault_v2 import _rk4_step
cfg=S.make_cfg()
def crit(A):
    c=[z for z in np.linalg.eigvals(A) if abs(z.imag)>1e-6]; return max(c,key=lambda z:z.real) if c else None
def td(P0,Xg0,th,T=6.0,dt=2e-5,pert=1e-6):
    p=S.make_p(idc_src=P0,Vg=1.0,iq_ref=0.0,Xg=Xg0); e=find_eq(p,th,cfg)
    if e is None: return None,None
    x=e.copy().astype(float); x[0]+=pert; x[4]=p.omega0; ts=[];d=[]
    for k in range(int(T/dt)):
        x=_rk4_step(x,p,dt)
        if not math.isfinite(x[0]) or abs(x[0]-e[0])>0.2: break
        if k%10==0: ts.append(k*dt); d.append(x[0]-e[0])
    ts=np.array(ts); d=np.array(d)
    if len(ts)<50: return crit(S.jacobian(e,p,cfg)[:4,:4]),None
    m=ts>0.2; pk,_=find_peaks(d[m]); pk=[i for i in pk if d[m][i]>0]
    lam=crit(S.jacobian(e,p,cfg)[:4,:4])
    if len(pk)<3: return lam,None
    tp=ts[m][pk]; ap=np.abs(d[m][pk]); return lam,(np.polyfit(tp,np.log(ap),1)[0],1.0/np.mean(np.diff(tp)))

print("Verify Hopf (growing oscillation, eq EXISTS) at the two new grids:")
print(f"  {'Xg':>5}{'P':>8}{'region':>22}{'Reλ(eig)':>10}{'rate TD':>9}{'f_H':>7}{'f TD':>7}")
for Xg0,pts,thg in [(0.1,[(1.48,'stable'),(1.50,'past Hopf'),(1.52,'past Hopf')],-0.10),
                    (1.5,[(0.495,'stable'),(0.498,'past Hopf'),(0.4995,'past Hopf')],-0.65)]:
    th=thg
    for P0,tag in pts:
        lam,t=td(P0,Xg0,th)
        if lam is None: print(f"  {Xg0:>5.2f}{P0:>8.4f}{'no eq (past SN)':>22}"); continue
        # update guess for continuation
        p=S.make_p(idc_src=P0,Vg=1.0,iq_ref=0.0,Xg=Xg0); e=find_eq(p,th,cfg); th=e[0]
        reg=("stable(decay)" if lam.real<0 else "UNSTABLE(grow)")
        r=f"{t[0]:>9.2f}" if t else f"{'—':>9}"; ft=f"{t[1]:>7.3f}" if t else f"{'—':>7}"
        print(f"  {Xg0:>5.2f}{P0:>8.4f}{reg:>22}{lam.real:>10.2f}{r}{abs(lam.imag)/2/math.pi:>7.2f}{ft}")
    # confirm SN: no eq past P_SN
    P_SN=3/(4*Xg0)
    e=S.stable_eq(S.make_p(idc_src=P_SN*1.001,Vg=1.0,Xg=Xg0),cfg)
    print(f"  {Xg0:>5.2f}  P_SN={P_SN:.3f}: eq at P=1.001·P_SN -> {'EXISTS' if e is not None else 'NONE (SN confirmed)'}")
