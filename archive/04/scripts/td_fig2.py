import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.fault_v2 import _rk4_step
cfg=S.make_cfg()
def run(kw,T=4.0,dt=2e-5,pert=1e-4):
    p=S.make_p(**kw); e=S.stable_eq(p,cfg)
    c=[z for z in np.linalg.eigvals(S.jacobian(e,p,cfg)[:4,:4]) if abs(z.imag)>1e-6]; lam=max(c,key=lambda z:z.real)
    x=e.copy().astype(float); x[0]+=pert; x[4]=p.omega0; ts=[];d=[]
    for k in range(int(T/dt)):
        x=_rk4_step(x,p,dt)
        if not math.isfinite(x[0]) or abs(x[0]-e[0])>0.3: break
        if k%5==0: ts.append(k*dt); d.append(x[0]-e[0])
    return np.array(ts),np.array(d),lam,pert
cases=[("increase P → 0.746 (Xg=1,V=1,Q=0)",dict(idc_src=0.746,iq_ref=0.0,Vg=1.0,Xg=1.0),"#c0392b"),
       ("decrease V → 0.817 (Xg=1,P=0.5,Q=0)",dict(idc_src=0.5,iq_ref=0.0,Vg=0.817,Xg=1.0),"#2980b9"),
       ("increase Q → 0.245 (Xg=1,P=0.5,V=1)",dict(idc_src=0.5,iq_ref=0.245,Vg=1.0,Xg=1.0),"#27ae60")]
fig,ax=plt.subplots(1,3,figsize=(15,4.3))
for i,(lab,kw,c) in enumerate(cases):
    ts,d,lam,p0=run(kw); env=p0*np.exp(lam.real*ts)
    ax[i].plot(ts,d*1e3,color=c,lw=0.8,label="Δθ(t) time-domain")
    ax[i].plot(ts,env*1e3,'k--',lw=1.2,label=f"predicted envelope e^({lam.real:.2f}t)")
    ax[i].plot(ts,-env*1e3,'k--',lw=1.2)
    ax[i].set_title(f"{lab}\neig: Reλ={lam.real:+.2f}/s, f={abs(lam.imag)/2/math.pi:.2f}Hz",fontsize=9)
    ax[i].set_xlabel("time [s]"); ax[i].set_ylabel("Δθ − Δθ* [mrad]"); ax[i].legend(fontsize=7.5)
plt.suptitle("Time-domain: varying the OPERATING POINT (P,Q,V) across the Hopf → growing oscillation matches the analytic eigenvalue",fontsize=10)
plt.tight_layout(); plt.savefig("/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/td_pqv.png",dpi=120)
print("saved")
