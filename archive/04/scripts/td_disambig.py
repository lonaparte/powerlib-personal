"""Disambiguate the OU loss-of-sync: was it (a) genuine generator-randomization
escape within a frozen-stable set, or (b) the unbounded OU tail crossing the
saddle-node?  Clip the fluctuation to stay STRICTLY inside the frozen-stable
range and re-test.  Also extend T on the bounded sinusoid to check for slow
resonant build-up."""
import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.fault_v2 import _saddle_eq_left, _rk4_step

B10=dict(Xg=1.0, idc_src=0.5, iq_ref=0.0, Vg=1.0)

def frozen_range_ok(eps, knob='Vg', nsamp=11):
    p0=S.make_p(**B10); th=getattr(p0,knob); worst=-9
    for u in np.linspace(-1,1,nsamp):
        p=p0.copy(); setattr(p,knob,th*(1+eps*u)); eq=S.stable_eq(p)
        if eq is None: return False,None
        worst=max(worst, np.linalg.eigvals(S.jacobian(eq,p)).real.max())
    return True,worst

def run(knob,eps,mod,Om=0.0,T=8.0,dt=5e-5,tau=0.02,seed=0,clip=None):
    p0=S.make_p(**B10); eq=S.stable_eq(p0); th0=eq[0]
    sR=S.saddle_eq_right(p0)[0]; sL=_saddle_eq_left(p0)[0]; hi,lo=sR+0.5,sL-0.5
    base=getattr(p0,knob); rng=np.random.default_rng(seed); p=p0.copy()
    state=eq.copy().astype(float); state[4]=p0.omega0
    n=int(T/dt); sq=math.sqrt(dt); maxdev=0; ou=0.0; verdict=None; umax=0
    for k in range(n):
        t=k*dt
        if mod=='sin': u=math.sin(Om*t)
        else:
            ou += -ou/tau*dt + math.sqrt(2.0/tau)*sq*rng.standard_normal(); u=ou
        if clip is not None: u=max(-clip,min(clip,u))
        umax=max(umax,abs(u))
        setattr(p,knob, base*(1+eps*u))
        state=_rk4_step(state,p,dt)
        dev=abs(state[0]-th0); maxdev=max(maxdev,dev)
        if state[2]<0.10: verdict='VDC_COLLAPSE'; break
        if state[0]>hi or state[0]<lo: verdict='LOSS_OF_SYNC'; break
        if not (math.isfinite(state[0]) and math.isfinite(state[2])): verdict='NUMERIC'; break
    if verdict is None: verdict='STABLE'
    return verdict, maxdev, (k*dt if verdict!='STABLE' else T), umax

print("frozen-stable check (max Re eig over the modulation range):")
for eps in [0.10,0.12,0.15]:
    ok,w=frozen_range_ok(eps); print(f"  eps={eps}: Vg∈[{1-eps:.2f},{1+eps:.2f}]  frozen-stable={ok}  worst maxRe={w:.2f}")

print("\n(A) CLIPPED OU  |u|<=1  -> Vg stays STRICTLY inside the frozen-stable range:")
for eps in [0.10,0.12,0.15]:
    for seed in [0,1,2]:
        v,md,tf,um=run('Vg',eps,'ou',clip=1.0,seed=seed,T=10.0)
        print(f"  eps={eps} seed={seed}: {v:>13}  max|Δθ-Δθ*|={md:.3f}  t={tf:.2f}  (|u|max={um:.2f})")

print("\n(B) UNCLIPPED OU (Gaussian tails can dip below SN) for contrast:")
for eps in [0.10,0.12,0.15]:
    v,md,tf,um=run('Vg',eps,'ou',clip=None,seed=0,T=10.0)
    thr=(0.8/1.0-1)/(-1)  # |u| that reaches Vg=0.8 (approx SN) = 0.2/eps
    print(f"  eps={eps} seed=0: {v:>13}  max|Δθ-Δθ*|={md:.3f}  t={tf:.2f}  (|u|max={um:.2f}; |u|~{0.2/eps:.1f} reaches SN)")

print("\n(C) bounded sinusoid at resonance, EXTENDED T=20 (slow build-up?):")
wn=abs([e for e in np.linalg.eigvals(S.jacobian(S.stable_eq(S.make_p(**B10)),S.make_p(**B10))) if abs(e.imag)>1e-6][0].imag)
# use least-damped:
ev=np.linalg.eigvals(S.jacobian(S.stable_eq(S.make_p(**B10)),S.make_p(**B10)))
wn=abs(max([e for e in ev if abs(e.imag)>1e-6],key=lambda z:z.real).imag)
for eps in [0.12,0.15,0.18]:
    ok,w=frozen_range_ok(eps)
    v,md,tf,um=run('Vg',eps,'sin',Om=2*wn,T=20.0)
    print(f"  eps={eps} (frozen-stable={ok}): {v:>13}  max|Δθ-Δθ*|={md:.3f}  t={tf:.2f}")
print("\n[done]")
