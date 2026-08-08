import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.system import find_eq
cfg=S.make_cfg()
def P_hopf(Xg0):
    th=-0.05; prev=None; pv=None; P_SN=3/(4*Xg0)
    for P0 in np.linspace(0.1,P_SN*0.9999,500):
        p=S.make_p(idc_src=P0,Vg=1.0,iq_ref=0.0,Xg=Xg0); e=find_eq(p,th,cfg)
        if e is None: break
        th=e[0]; cx=[z for z in np.linalg.eigvals(S.jacobian(e,p,cfg)[:4,:4]) if abs(z.imag)>1e-6]
        m=max(z.real for z in cx) if cx else -9
        if prev is not None and prev<0<=m: return 0.5*(pv+P0)
        prev=m; pv=P0
    return None
Xgs=np.array([0.1,0.15,0.2,0.3,0.4,0.5,0.7,0.9,1.0,1.2,1.5])
PH=np.array([P_hopf(x) for x in Xgs]); PSN=3/(4*Xgs)
fig,ax=plt.subplots(figsize=(8.5,5.2))
xf=np.linspace(0.08,1.55,200); ax.plot(xf,3/(4*xf),'-',color="#e67e22",lw=2,label="SN  P_SN=3/(4Xg)  (平衡点消失)")
ax.plot(Xgs,PH,'o-',color="#c0392b",lw=2,label="Hopf  (平衡点存在但失稳=增长振荡)")
ax.fill_between(xf,0.3,3/(4*xf),color="#e8f5e9",alpha=0.6)
ax.fill_between(Xgs,PH,3/(4*Xgs),color="#fdecea",alpha=0.9)
ax.set_yscale('log'); ax.set_ylim(0.35,9); ax.set_xlim(0.08,1.55)
ax.set_xlabel("Xg  (电网电抗;  小=强网, 大=弱网)"); ax.set_ylabel("有功 P  (log)")
ax.annotate("稳定\n(平衡点存在, 衰减)",(0.55,0.55),fontsize=9,color="#2e7d32")
ax.annotate("Hopf 与 SN 之间:\n平衡点存在但增长振荡",(0.6,1.9),fontsize=8.5,color="#c0392b")
ax.annotate("无平衡点\n(过 SN)",(0.2,5.5),fontsize=9,color="#e67e22")
ax.annotate("强网: Hopf≪SN\n(振荡失稳窗口宽)",(0.11,2.3),fontsize=8,color="#555")
ax.annotate("弱网: Hopf≈SN\n(近 Bogdanov-Takens)",(1.15,0.55),fontsize=8,color="#555",
            arrowprops=dict(arrowstyle='->'),xytext=(0.95,0.42))
ax.set_title("Hopf 与 SN 随电网强度分开/合并 (P 方向, V=1,Q=0)\n弱网 → 两者塌到一起; 强网 → Hopf 远早于 SN",fontsize=11)
ax.legend(fontsize=9,loc='upper right')
plt.tight_layout(); plt.savefig("/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/hopf_sn.png",dpi=120)
print("P_Hopf:",[round(x,3) if x else None for x in PH]); print("saved")
