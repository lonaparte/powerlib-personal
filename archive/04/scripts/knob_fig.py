import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
# measured parametric-coupling numbers
# order: P, Q, V, grid-strength(1/SCR)
g_145=[319.9,349.3,331.9,109.9]      # coupling per pu (absolute)
g_147=[478.0,515.2,487.9,162.1]
labels=["P","Q","V","grid\nstrength"]
# fractional thresholds (P,V,gridstrength have fractional base; Q base=0 shown as abs)
knob3=["P","V","grid strength"]
eps_crit_145=[7.1,3.4,7.1]; sn_145=[3.8,1.9,3.8]
eps_crit_147=[3.0,1.5,3.1]; sn_147=[2.2,1.1,2.2]

fig,ax=plt.subplots(1,2,figsize=(13,4.7))
x=np.arange(4); w=0.38
ax[0].bar(x-w/2,g_145,w,label="Xg=1.45 (δ=5.7)",color="#5b8def")
ax[0].bar(x+w/2,g_147,w,label="Xg=1.47 (δ=3.6, closer to Hopf)",color="#c0392b")
ax[0].set_xticks(x); ax[0].set_xticklabels(labels)
ax[0].set_ylabel("parametric coupling g_θ  (per pu)")
ax[0].set_title("(1) mechanism strength per knob (absolute, per pu)\nP ≈ Q ≈ V ;  grid strength ~⅓",fontsize=10)
ax[0].legend(fontsize=8)

xx=np.arange(3); w=0.35
ax[1].bar(xx-w/2,eps_crit_147,w,label="ε_crit small-signal (paramres onset)",color="#27ae60")
ax[1].bar(xx+w/2,sn_147,w,label="ε_SN large-signal (equilibrium vanishes)",color="#e67e22")
for i in range(3):
    ax[1].annotate("SN\nfirst",(xx[i]+w/2,sn_147[i]+0.1),ha='center',fontsize=7.5,color="#e67e22")
ax[1].set_xticks(xx); ax[1].set_xticklabels(knob3)
ax[1].set_ylabel("critical fractional modulation  [%]  (at Xg=1.47)")
ax[1].set_title("(2) which limit bites first: SN (large-sig) < ε_crit (small-sig)\nfor every knob → small-signal mechanism is PREEMPTED",fontsize=10)
ax[1].legend(fontsize=8); ax[1].set_ylim(0,3.6)
plt.tight_layout(); plt.savefig("/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/knob_fig.png",dpi=120)
print("saved")
