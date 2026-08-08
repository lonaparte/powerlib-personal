import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from scipy.signal import find_peaks
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.system import find_eq
from gfl_5d_ou_sim.fault_v2 import _rk4_step
cfg=S.make_cfg()
def crit(A):
    c=[z for z in np.linalg.eigvals(A) if abs(z.imag)>1e-6]; return max(c,key=lambda z:z.real) if c else None
def td_from(eq,p,T=6.0,dt=2e-5,pert=1e-5):
    x=eq.copy().astype(float); x[0]+=pert; x[4]=p.omega0; ts=[];d=[]
    for k in range(int(T/dt)):
        x=_rk4_step(x,p,dt)
        if not math.isfinite(x[0]) or abs(x[0]-eq[0])>0.3: break
        if k%10==0: ts.append(k*dt); d.append(x[0]-eq[0])
    ts=np.array(ts); d=np.array(d)
    if len(ts)<50: return None
    m=ts>0.3; pk,_=find_peaks(d[m]); pk=[i for i in pk if d[m][i]>0]
    if len(pk)<3: return None
    tp=ts[m][pk]; ap=np.abs(d[m][pk]); return np.polyfit(tp,np.log(ap),1)[0],1.0/np.mean(np.diff(tp))
print("Xg=0.5  P just past the Hopf (continuation, slow-growth window), V=1,Q=0:")
print(f"  {'P':>7}{'Δθ*':>9}{'n_unst':>7}{'Reλ':>9}{'rate(TD)':>10}{'f_H':>8}{'f TD':>8}")
th=-0.58
for P0 in [1.405,1.410,1.415,1.420,1.425]:
    p=S.make_p(idc_src=P0,Vg=1.0,iq_ref=0.0,Xg=0.5); e=find_eq(p,th,cfg)
    if e is None: print(f"  {P0:>7.3f}  no eq"); continue
    th=e[0]; A=S.jacobian(e,p,cfg)[:4,:4]; npos=int(np.sum(np.linalg.eigvals(A).real>1e-6)); lam=crit(A)
    t=td_from(e,p); r=f"{t[0]:>10.2f}" if t else f"{'—':>10}"; ft=f"{t[1]:>8.3f}" if t else f"{'—':>8}"
    print(f"  {P0:>7.3f}{e[0]:>9.4f}{npos:>7}{lam.real:>9.2f}{r}{abs(lam.imag)/2/math.pi:>8.3f}{ft}")
print("\nXg=0.5  Q boundary (P=0.5,V=1):")
for Q0 in [1.03,1.05,1.06,1.07,1.08]:
    p=S.make_p(idc_src=0.5,Vg=1.0,iq_ref=Q0,Xg=0.5); e=S.stable_eq(p,cfg)
    if e is None: print(f"  Q={Q0:.3f}  no eq (SN)"); continue
    A=S.jacobian(e,p,cfg)[:4,:4]; lam=crit(A)
    print(f"  Q={Q0:.3f}  Reλ={lam.real:+.2f}  f_H={abs(lam.imag)/2/math.pi:.3f}Hz  {'STABLE' if lam.real<0 else 'UNSTABLE'}")
