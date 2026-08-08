"""
TRUE stability via full nonlinear time-domain, with a FLUCTUATING operating
point.  Reuses the model's own RK4 step and loss-of-sync detector.

Question: does the nonlinear trajectory confirm the linear verdict
(sub-critical / bounded), or does it lose synchronism (Δθ escapes the basin)
where λ_top said "stable"?  The escape channel is exactly what λ_top misses.

We keep the modulation range FROZEN-STABLE (every instantaneous operating
point still has a stable equilibrium) so that any instability is genuinely
from the time-variation, not from dragging the system across the
deterministic saddle-node/Hopf.
"""
import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.fault_v2 import _saddle_eq_left, _rk4_step

def frozen_ok(base_kw, knob, eps, nsamp=9):
    """Is every operating point in [θ(1-eps), θ(1+eps)] a stable equilibrium?"""
    p0=S.make_p(**base_kw); th=getattr(p0,knob)
    worst=-9
    for u in np.linspace(-1,1,nsamp):
        p=p0.copy(); setattr(p,knob,th*(1+eps*u))
        eq=S.stable_eq(p)
        if eq is None: return False,'SN(no eq)',None
        mr=np.linalg.eigvals(S.jacobian(eq,p)).real.max(); worst=max(worst,mr)
        if mr>0: return False,'frozen-unstable',worst
    return True,'ok',worst

def omega_n(base_kw):
    p=S.make_p(**base_kw); eq=S.stable_eq(p); ev=np.linalg.eigvals(S.jacobian(eq,p))
    comp=[e for e in ev if abs(e.imag)>1e-6]; return abs(max(comp,key=lambda z:z.real).imag)

def run(base_kw, knob=None, eps=0.0, Omega=0.0, mod='const',
        T=6.0, dt=5e-5, sigma_ou=0.0, tau_ou=0.02, seed=0, rec=False):
    p0=S.make_p(**base_kw); eq=S.stable_eq(p0); th0=eq[0]
    sR=S.saddle_eq_right(p0)[0]; sL=_saddle_eq_left(p0)[0]
    hi, lo = sR+0.5, sL-0.5
    base_val=getattr(p0,knob) if knob else 0.0
    rng=np.random.default_rng(seed); p=p0.copy()
    state=eq.copy().astype(float); state[4]=p0.omega0
    n=int(T/dt); sq=math.sqrt(dt); maxdev=0.0; verdict=None; ou=0.0; traj=[]
    for k in range(n):
        t=k*dt
        if knob:
            if mod=='sin': u=math.sin(Omega*t)
            elif mod=='ou':
                ou += -ou/tau_ou*dt + math.sqrt(2.0/tau_ou)*sq*rng.standard_normal(); u=ou
            else: u=0.0
            setattr(p,knob, base_val*(1+eps*u))
        state=_rk4_step(state,p,dt)
        if sigma_ou>0: state[4]+= sigma_ou*sq*rng.standard_normal()
        dev=abs(state[0]-th0); maxdev=max(maxdev,dev)
        if rec and k%400==0: traj.append((t,float(state[0]),float(state[2])))
        if state[2]<0.10: verdict='VDC_COLLAPSE'; break
        if state[0]>hi or state[0]<lo: verdict='LOSS_OF_SYNC'; break
        if not (math.isfinite(state[0]) and math.isfinite(state[2])): verdict='NUMERIC'; break
    if verdict is None: verdict='STABLE'
    return dict(verdict=verdict, maxdev=maxdev,
                t_fail=(k*dt if verdict!='STABLE' else T), traj=traj)

B10=dict(Xg=1.0, idc_src=0.5, iq_ref=0.0, Vg=1.0)   # comfortable margin
B145=dict(Xg=1.45, idc_src=0.5, iq_ref=0.0, Vg=1.0) # near boundary
wn10=omega_n(B10); wn145=omega_n(B145)
print(f"base Xg=1.0: ω_n={wn10:.2f} (2ω_n={2*wn10:.1f}); base Xg=1.45: ω_n={wn145:.2f} (2ω_n={2*wn145:.1f})")
print(f"{'scenario':<52}{'frozen-stable?':>16}{'verdict':>14}{'max|Δθ-Δθ*|':>14}{'t_fail':>8}")
print("-"*104)

def line(tag, base, knob, eps, Om, mod, **kw):
    ok=('—','—',None)
    if knob and mod!='const':
        f,why,worst=frozen_ok(base,knob,eps); ok=(f,why,worst)
    r=run(base, knob, eps, Om, mod, **kw)
    fs = f"{ok[1]}(mR={ok[2]:.2f})" if ok[2] is not None else str(ok[1])
    print(f"{tag:<52}{fs:>16}{r['verdict']:>14}{r['maxdev']:>14.3f}{r['t_fail']:>8.2f}")
    return r

# baselines: additive omega_g noise only (degree)
line("Xg=1.0 fixed + ω_g noise σ=0.05 (additive baseline)", B10, None,0,0,'const', sigma_ou=0.05)
line("Xg=1.0 fixed + ω_g noise σ=0.5  (large additive)",   B10, None,0,0,'const', sigma_ou=0.5)

# V (strongest lever) sinusoidal at resonance, ramp eps, frozen-stable range
for eps in [0.05,0.10,0.15,0.20]:
    line(f"Xg=1.0  V·sin @2ω_n  eps={eps}", B10,'Vg',eps,2*wn10,'sin')
# V slow (adiabatic)
line("Xg=1.0  V·sin @Ω=2 (adiabatic) eps=0.20", B10,'Vg',0.20,2.0,'sin')
# P (pure-indirect knob) at resonance
for eps in [0.10,0.30,0.60]:
    line(f"Xg=1.0  P·sin @2ω_n  eps={eps}", B10,'idc_src',eps,2*wn10,'sin')
# V fast stochastic OU
line("Xg=1.0  V·OU fast τ=0.02 eps=0.15 (stochastic)", B10,'Vg',0.15,0,'ou',tau_ou=0.02)
line("Xg=1.0  V·OU fast τ=0.02 eps=0.25 (stochastic)", B10,'Vg',0.25,0,'ou',tau_ou=0.02)

# near boundary: weak (frozen-stable) vs SN-crossing
line("Xg=1.45 V·sin @2ω_n eps=0.010 (weak, frozen-stable)", B145,'Vg',0.010,2*wn145,'sin')
line("Xg=1.45 V·sin @2ω_n eps=0.050 (crosses SN)",           B145,'Vg',0.050,2*wn145,'sin')

# record two trajectories for plotting: a STABLE and (if any) a LOSS case
rec_stable=run(B10,'Vg',0.15,2*wn10,'sin',rec=True)
rec_pbig=run(B10,'idc_src',0.60,2*wn10,'sin',rec=True)
np.savez("/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/td_out.npz",
         traj_stable=np.array(rec_stable['traj']), traj_pbig=np.array(rec_pbig['traj']),
         v_stable=rec_stable['verdict'], v_pbig=rec_pbig['verdict'])
print("\n[done] trajectories saved")
