"""Build the final figure from MEASURED lambda_top values (no re-simulation)."""
import sys; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()
def A_of(Xg):
    p=S.make_p(Xg=Xg); eq=S.stable_eq(p,cfg); return S.jacobian(eq,p,cfg)
OUT="/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad"

# panel (a) deterministic map (cheap: eigenvalues only)
Xgs=np.linspace(0.1,1.499,140); mre=np.array([np.linalg.eigvals(A_of(x)).real.max() for x in Xgs])
hopf=Xgs[np.where(mre<0)[0][-1]]
wn=16.65

# measured lambda_top (from converged simulations, seeds/T cross-checked)
Om=np.array([25,29,31,32,33,34,35,37]);
lam_nb=np.array([-3.387,-3.368,-1.764,-1.601,-1.581,-1.687,-1.972,-3.397])  # near boundary amp=0.021
lam_strong=-10.0  # flat over all Om (well damped -> OU mode dominates)
amps=np.array([0.004,0.008,0.012,0.016,0.020,0.0218])
lam_amp=np.array([-3.32,-2.97,-2.59,-2.18,-1.72,-1.50])                     # at Om=2wn=33.3

fig,ax=plt.subplots(1,3,figsize=(15,4.5))
c_nb,c_st="#c0392b","#27ae60"

ax[0].plot(Xgs,mre,color="#2c3e50",lw=1.6)
ax[0].axhline(0,color='k',lw=.6)
ax[0].axvline(1.5,color='r',ls='--',lw=.9,label='saddle-node  Xg=1.5')
ax[0].axvline(hopf,color='m',ls=':',lw=1.1,label=f'Hopf  Xg≈{hopf:.3f}')
ax[0].annotate("strong grid:\nheavily damped",(0.35,-9.3),fontsize=8,color="#555")
ax[0].annotate("thin lightly-\ndamped sliver",(1.15,-3.0),fontsize=8,color="#555")
ax[0].set_xlabel("Xg   (grid reactance = 1/strength) = operating point")
ax[0].set_ylabel("max Re eig(A)")
ax[0].set_title("(a) DETERMINISTIC map\nmoving operating point = adiabatic drift",fontsize=10)
ax[0].legend(fontsize=8); ax[0].set_ylim(-11,4)

ax[1].axhline(0,color='k',lw=.6,label='instability threshold')
ax[1].plot(Om/wn,lam_nb,'o-',color=c_nb,label='near Hopf (Xg=1.47), amp=0.021')
ax[1].hlines(lam_strong,Om.min()/wn,Om.max()/wn,color=c_st,lw=2,label='strong grid (Xg=0.1): flat −10 (immune)')
ax[1].axvline(2,color='gray',ls=':',lw=1,label='Ω = 2ω_n (parametric resonance)')
ax[1].set_xlabel("Ω / ω_n   (fast parametric modulation of Xg)")
ax[1].set_ylabel("λ_top  (sample-path growth rate)")
ax[1].set_title("(b) GENERATOR RANDOMIZATION\nsharp resonance at 2ω_n — only near boundary, only fast",fontsize=10)
ax[1].legend(fontsize=7.5,loc='lower right'); ax[1].set_ylim(-11,1)

ax[2].axhline(0,color='k',lw=.7,label='instability threshold (λ_top=0)')
ax[2].plot(amps,lam_amp,'o-',color=c_nb)
# linear extrapolation to show it heads toward but stops short of 0
ax[2].annotate("max depth keeping\nEVERY frozen A Hurwitz\n→ λ_top=−1.5 < 0",
               (0.0218,-1.5),xytext=(0.007,-0.9),fontsize=8,color=c_nb,
               arrowprops=dict(arrowstyle='->',color=c_nb))
ax[2].set_xlabel("parametric modulation amplitude in Xg   (at Ω=2ω_n)")
ax[2].set_ylabel("λ_top at resonance")
ax[2].set_title("(c) deepens with depth but stays SUB-CRITICAL\nmechanism latent, not triggered",fontsize=10)
ax[2].legend(fontsize=8); ax[2].set_ylim(-3.7,0.4)

plt.tight_layout(); plt.savefig(f"{OUT}/gfl_demo.png",dpi=120)
print("saved figure. hopf≈",round(hopf,3))
