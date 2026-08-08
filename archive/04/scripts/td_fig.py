import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.fault_v2 import _saddle_eq_left, _rk4_step
B10=dict(Xg=1.0, idc_src=0.5, iq_ref=0.0, Vg=1.0)
p0=S.make_p(**B10); eq=S.stable_eq(p0); th0=eq[0]
sR=S.saddle_eq_right(p0)[0]; sL=_saddle_eq_left(p0)[0]; hi,lo=sR+0.5,sL-0.5
ev=np.linalg.eigvals(S.jacobian(eq,p0)); wn=abs(max([e for e in ev if abs(e.imag)>1e-6],key=lambda z:z.real).imag)

def traj(knob,eps,mod,Om=0.0,T=10.0,dt=5e-5,tau=0.02,seed=0,clip=None):
    base=getattr(p0,knob); rng=np.random.default_rng(seed); p=p0.copy()
    st=eq.copy().astype(float); st[4]=p0.omega0; n=int(T/dt); sq=math.sqrt(dt)
    ts=[]; ths=[]; ou=0.0; verdict='STABLE'
    for k in range(n):
        t=k*dt
        if mod=='sin': u=math.sin(Om*t)
        else: ou += -ou/tau*dt + math.sqrt(2/tau)*sq*rng.standard_normal(); u=ou
        if clip is not None: u=max(-clip,min(clip,u))
        setattr(p,knob, base*(1+eps*u)); st=_rk4_step(st,p,dt)
        if k%200==0: ts.append(t); ths.append(st[0])
        if st[0]>hi or st[0]<lo or st[2]<0.1: verdict='LOSS_OF_SYNC'; ts.append(t); ths.append(st[0]); break
    return np.array(ts),np.array(ths),verdict

cases=[
  ("V·sin @2ω_n ε=0.18 (bounded, frozen-stable)", traj('Vg',0.18,'sin',2*wn),  "#27ae60"),
  ("V·OU clipped ε=0.15 (bounded fast random)",   traj('Vg',0.15,'ou',clip=1.0), "#2980b9"),
  ("V·OU unclipped ε=0.15 (tail crosses SN)",     traj('Vg',0.15,'ou',clip=None),"#c0392b"),
]
fig,ax=plt.subplots(figsize=(9,4.8))
ax.axhline(th0,color='k',lw=.6,ls='-',label=f'stable eq Δθ*={th0:.2f}')
ax.axhline(hi,color='crimson',lw=1,ls='--',label='loss-of-sync threshold (saddle+0.5)')
ax.axhline(lo,color='crimson',lw=1,ls='--')
for lab,(t,x,v),c in cases:
    ax.plot(t,x,color=c,lw=1.3,label=f"{lab} → {v}")
ax.set_xlabel("time [s]"); ax.set_ylabel("Δθ(t) [rad]")
ax.set_title("GFL nonlinear time-domain under a FLUCTUATING operating point (V)\n"
             "bounded-inside-stable-set → STABLE;  fluctuation crossing the saddle-node → irreversible loss-of-sync")
ax.legend(fontsize=8,loc='upper left'); ax.set_ylim(lo-0.3, hi+0.3)
plt.tight_layout(); plt.savefig("/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/td_fig.png",dpi=120)
print("saddle+0.5=%.2f  eq=%.2f  wn=%.2f"%(hi,th0,wn))
for lab,(t,x,v),c in cases: print(f"{lab}: {v}, maxdev={np.max(np.abs(x-th0)):.3f}")
print("saved")
