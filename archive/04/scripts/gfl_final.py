"""Consolidated final demo + figure for the GFL generator-randomization test."""
import sys; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, matplotlib
matplotlib.use("Agg"); import matplotlib.pyplot as plt
from scipy.linalg import solve_continuous_lyapunov
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); np.random.seed(2); n=5
OUT="/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad"

def A_of(Xg):
    p=S.make_p(Xg=Xg); eq=S.stable_eq(p,cfg); return S.jacobian(eq,p,cfg)
def maxRe(A): return np.linalg.eigvals(A).real.max()

# ---- deterministic map ----
Xgs=np.linspace(0.1,1.499,120); mre=[]; wn=[]
for x in Xgs:
    ev=np.linalg.eigvals(A_of(x)); mre.append(ev.real.max())
    comp=[e for e in ev if abs(e.imag)>1e-6]; wn.append(abs(max(comp,key=lambda z:z.real).imag))
mre=np.array(mre); wn=np.array(wn)
hopf=Xgs[np.argmin(np.abs(mre[ (Xgs>1.3) ]))]  # rough
hopf=Xgs[np.where(mre<0)[0][-1]]  # last stable Xg on grid

# ---- lambda_top under sinusoidal Xg modulation ----
xs=np.linspace(1.40,1.4995,800); As=np.array([A_of(x) for x in xs])
def Aint(xg):
    i=np.clip(np.searchsorted(xs,xg)-1,0,len(xs)-2); t=(xg-xs[i])/(xs[i+1]-xs[i])
    return (1-t)*As[i]+t*As[i+1]
xs2=np.linspace(0.05,0.16,200); As2=np.array([A_of(x) for x in xs2])
def Aint2(xg):
    i=np.clip(np.searchsorted(xs2,xg)-1,0,len(xs2)-2); t=(xg-xs2[i])/(xs2[i+1]-xs2[i])
    return (1-t)*As2[i]+t*As2[i+1]
def ltop(Afun,Xg0,amp,Om,T=100,dt=5e-4):
    steps=int(T/dt); x=np.random.randn(n); x/=np.linalg.norm(x); s=0.;b=int(.25*steps);c=0
    for k in range(steps):
        t=k*dt
        A1=Afun(Xg0+amp*np.sin(Om*t)); k1=A1@x
        A2=Afun(Xg0+amp*np.sin(Om*(t+.5*dt))); k2=A2@(x+.5*dt*k1); k3=A2@(x+.5*dt*k2)
        A4=Afun(Xg0+amp*np.sin(Om*(t+dt))); k4=A4@(x+dt*k3)
        x=x+(dt/6)*(k1+2*k2+2*k3+k4); nr=np.linalg.norm(x)
        if k>=b: s+=np.log(nr); c+=1
        x/=nr
    return s/(c*dt)

_evb=np.linalg.eigvals(A_of(1.470)); _cb=[e for e in _evb if abs(e.imag)>1e-6]
wn_b=abs(max(_cb,key=lambda z:z.real).imag)   # least-damped complex mode
Oms=np.linspace(1.45*wn_b,2.45*wn_b,9)   # bracket principal resonance 2*wn
print("near-boundary Xg0=1.47, omega_n=%.2f, resonance expected at 2wn=%.1f"%(wn_b,2*wn_b))
gr_b_hi=[ltop(Aint,1.470,0.021,Om) for Om in Oms]
gr_b_lo=[ltop(Aint,1.470,0.010,Om) for Om in Oms]
# strong grid flat line (well-damped -> immune; few points suffice)
Oms_s=np.linspace(1.45*wn_b,2.45*wn_b,5)
gr_s=[ltop(Aint2,0.10,0.03,Om,T=30) for Om in Oms_s]
print("strong-grid lambda_top range: [%.2f, %.2f]"%(min(gr_s),max(gr_s)))
print("near-bnd amp0.021 min lambda_top=%.3f  amp0.010 min=%.3f"%(min(gr_b_hi),min(gr_b_lo)))

# amplitude sweep at the principal resonance Om=2*wn, pushing toward zero (stay Hurwitz: Xg0+amp<1.492)
Om_res=2.0*wn_b
amps=[0.004,0.008,0.012,0.016,0.020,0.0218]
gr_amp=[ltop(Aint,1.470,a,Om_res) for a in amps]
print("amp sweep at Om=%.1f:"%Om_res, [f"{a:.4f}:{g:+.2f}" for a,g in zip(amps,gr_amp)])

# ---- figure ----
fig,ax=plt.subplots(1,3,figsize=(15,4.4))
ax[0].plot(Xgs,mre,'b-'); ax[0].axhline(0,color='k',lw=.7)
ax[0].axvline(1.5,color='r',ls='--',lw=.8,label='saddle-node Xg=1.5')
ax[0].axvline(hopf,color='m',ls=':',lw=.8,label=f'Hopf ~{hopf:.3f}')
ax[0].set_xlabel('Xg  (grid reactance = 1/strength)'); ax[0].set_ylabel('max Re eig(A)')
ax[0].set_title('(a) DETERMINISTIC map\nvarying operating point = adiabatic drift'); ax[0].legend(fontsize=8)
ax[0].set_ylim(-12,4)

ax[1].axhline(0,color='k',lw=.7)
ax[1].plot(Oms/wn_b,gr_b_hi,'o-',color='crimson',label='near Hopf, amp=0.021')
ax[1].plot(Oms/wn_b,gr_b_lo,'s-',color='orange',label='near Hopf, amp=0.010')
ax[1].plot(Oms_s/wn_b,gr_s,'^-',color='green',label='strong grid, amp=0.03')
ax[1].axvline(2,color='gray',ls=':',lw=.8,label='Ω=2ω_n')
ax[1].set_xlabel('Ω / ω_n  (parametric modulation freq)'); ax[1].set_ylabel('λ_top  (growth rate)')
ax[1].set_title('(b) GENERATOR RANDOMIZATION\nresonance appears only near boundary, only when fast'); ax[1].legend(fontsize=8)

ax[2].axhline(0,color='k',lw=.7,label='instability threshold')
ax[2].plot(amps,gr_amp,'o-',color='crimson')
ax[2].set_xlabel('parametric modulation amplitude (in Xg)'); ax[2].set_ylabel('λ_top at resonance')
ax[2].set_title('(c) even at max frozen-Hurwitz depth,\nλ_top stays < 0  → sub-critical'); ax[2].legend(fontsize=8)
plt.tight_layout(); plt.savefig(f"{OUT}/gfl_demo.png",dpi=115)
print("saved", f"{OUT}/gfl_demo.png")
