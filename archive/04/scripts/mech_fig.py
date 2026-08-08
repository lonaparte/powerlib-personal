"""The small-signal 'new mechanism' curve: sample-path decay rate lambda_top
vs the operating-point fluctuation frequency and amplitude.  All within the
frozen-stable set (no SN crossing, purely small-signal)."""
import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
wn=16.65
# converged measured values (Xg fluctuating at near-boundary Xg=1.47)
Om   = np.array([25,29,31,32,33,34,35,37])
lam  = np.array([-3.387,-3.368,-1.764,-1.601,-1.581,-1.687,-1.972,-3.397])   # amp=0.021
frozen = -3.4   # off-resonance == what additive noise / frozen eigenvalue gives
amps = np.array([0.004,0.008,0.012,0.016,0.020,0.0218])
lam_a= np.array([-3.32,-2.97,-2.59,-2.18,-1.72,-1.50])                        # at Om=2wn

fig,ax=plt.subplots(1,2,figsize=(12.5,4.6))

ax[0].axhline(0,color='k',lw=1,label='instability threshold  λ_top=0')
ax[0].axhline(frozen,color='#888',ls='--',lw=1.4,
              label='additive noise / frozen damping (NO mechanism → flat)')
ax[0].plot(Om/wn, lam,'o-',color='#c0392b',lw=1.8,
           label='operating-point fluctuation (multiplicative)')
ax[0].axvline(2,color='gray',ls=':',lw=1)
ax[0].annotate('parametric resonance\nat Ω=2ω_n:\neffective damping\ncut by >½',
               (2,-1.58),xytext=(1.35,-0.9),fontsize=8.5,color='#c0392b',
               arrowprops=dict(arrowstyle='->',color='#c0392b'))
ax[0].set_xlabel('Ω / ω_n   (frequency of the operating-point fluctuation)')
ax[0].set_ylabel('λ_top   (mode effective decay rate)')
ax[0].set_title('(1) THE new mechanism: frequency-selective damping reduction\n'
                'additive = flat line;  multiplicative = the dip', fontsize=10)
ax[0].legend(fontsize=8,loc='lower right'); ax[0].set_ylim(-4.0,0.4)

ax[1].axhline(0,color='k',lw=1,label='instability threshold')
ax[1].plot(amps*100, lam_a,'o-',color='#c0392b',lw=1.8)
ax[1].annotate('deepens monotonically\ntoward 0 with amplitude\n(here stops at −1.5:\nSUB-CRITICAL in this model)',
               (2.18,-1.5),xytext=(0.5,-0.75),fontsize=8.5,color='#c0392b',
               arrowprops=dict(arrowstyle='->',color='#c0392b'))
ax[1].set_xlabel('operating-point fluctuation amplitude  [%]  (at Ω=2ω_n)')
ax[1].set_ylabel('λ_top at resonance')
ax[1].set_title('(2) mechanism strength ∝ fluctuation amplitude\n'
                'would reach λ_top=0 (instability) for a lighter-damped mode', fontsize=10)
ax[1].legend(fontsize=8); ax[1].set_ylim(-3.6,0.3)
plt.tight_layout(); plt.savefig("/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/mech_fig.png",dpi=120)
print("saved")
