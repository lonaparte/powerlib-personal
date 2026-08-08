import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
# dRe(lambda)/dtheta (signed) and |dlambda/dtheta|
Xg=[0.5,1.0,1.45]
dRe={'P':[3.43,24.94,259.97],'Q':[10.43,40.35,281.07],'V':[-28.51,-48.92,-264.63],'grid':[3.83,13.34,88.52]}
mag={'P':[4.1,26.3,318.1],'Q':[13.1,42.8,348.4],'V':[29.3,49.3,329.9],'grid':[4.4,13.8,109.9]}
col={'P':'#e67e22','Q':'#8e44ad','V':'#c0392b','grid':'#2c3e50'}

fig,ax=plt.subplots(1,2,figsize=(13,4.7))

# panel A: signed damping sensitivity at a representative point (Xg=0.5)
knobs=['P','Q','V','grid']; x=np.arange(4)
vals=[dRe[k][0] for k in knobs]
bars=ax[0].bar(x,vals,color=[col[k] for k in knobs])
ax[0].axhline(0,color='k',lw=.8)
ax[0].set_xticks(x); ax[0].set_xticklabels(['P','Q','V','grid\nreactance'])
ax[0].set_ylabel('dRe(λ)/dθ   (per pu)')
ax[0].set_title('(1) at a NORMAL operating point (Xg=0.5)\n'
                'V dominant & STABILISING (<0); P,Q,grid DESTABILISING (>0)',fontsize=10)
ax[0].annotate('raising V\nADDS damping',(2,-28.5),xytext=(1.4,-20),fontsize=8,color=col['V'],
               arrowprops=dict(arrowstyle='->',color=col['V']))
for b,v in zip(bars,vals): ax[0].annotate(f'{v:+.1f}',(b.get_x()+b.get_width()/2,v+ (1.5 if v>0 else -3)),ha='center',fontsize=8)

# panel B: |dlambda/dtheta| normalised to V vs Xg -> shows the collapse near the boundary
for k in ['P','Q','grid']:
    r=[mag[k][i]/mag['V'][i] for i in range(3)]
    ax[1].plot(Xg,r,'o-',color=col[k],lw=1.8,label=f'{k} / V')
ax[1].axhline(1.0,color=col['V'],ls='--',lw=1.4,label='V (reference)')
ax[1].axvline(1.49,color='gray',ls=':',lw=1); ax[1].annotate('Hopf',(1.46,0.15),fontsize=8,color='gray')
ax[1].set_xlabel('Xg  (→ toward the Hopf boundary)')
ax[1].set_ylabel('|dλ/dθ|  relative to V')
ax[1].set_title('(2) the "P≈Q≈V" is a NEAR-BOUNDARY artifact\n'
                'away from Hopf they separate (V≫P); they only converge at the Hopf',fontsize=10)
ax[1].legend(fontsize=8,loc='center left'); ax[1].set_ylim(0,1.2)
plt.tight_layout(); plt.savefig("/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/knob_fix_fig.png",dpi=120)
print("saved")
