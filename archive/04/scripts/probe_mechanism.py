"""Can a FROZEN-HURWITZ parametric fluctuation of Xg actually drive lambda_top>0
in this GFL model?  Try (1) large-amp sinusoid, (2) square-wave switching
between two Hurwitz operating points (the non-commuting / no-common-Lyapunov
route, which is the most effective)."""
import sys; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); np.random.seed(1); n=5

def A_of(Xg):
    p=S.make_p(Xg=Xg); eq=S.stable_eq(p,cfg)
    return S.jacobian(eq,p,cfg)
def maxRe(A): return np.linalg.eigvals(A).real.max()

# table
xs=np.linspace(1.40,1.4995,800); As=np.array([A_of(x) for x in xs])
def Aint(xg):
    i=np.clip(np.searchsorted(xs,xg)-1,0,len(xs)-2)
    t=(xg-xs[i])/(xs[i+1]-xs[i]); return (1-t)*As[i]+t*As[i+1]

def lyap_top(Xg_fun, T, dt):
    steps=int(T/dt); x=np.random.randn(n); x/=np.linalg.norm(x)
    logs=0.0; burn=int(0.25*steps); cnt=0
    for k in range(steps):
        tt=k*dt
        A1=Aint(Xg_fun(tt)); k1=A1@x
        A2=Aint(Xg_fun(tt+0.5*dt)); k2=A2@(x+0.5*dt*k1); k3=A2@(x+0.5*dt*k2)
        A4=Aint(Xg_fun(tt+dt)); k4=A4@(x+dt*k3)
        x=x+(dt/6)*(k1+2*k2+2*k3+k4)
        nr=np.linalg.norm(x)
        if k>=burn: logs+=np.log(nr); cnt+=1
        x/=nr
    return logs/(cnt*dt)

print("frozen check: maxRe at 1.45,1.47,1.487,1.49,1.499 =",
      [round(maxRe(A_of(x)),3) for x in (1.45,1.47,1.487,1.49,1.499)])

# (1) large-amp sinusoid near boundary, fine Omega sweep
print("\n(1) sinusoid Xg0=1.470 amp=0.021 (range[1.449,1.491], all Hurwitz):")
best=-9
for Om in np.arange(24,41,1.5):
    g=lyap_top(lambda t,Om=Om: 1.470+0.021*np.sin(Om*t), T=120, dt=5e-4)
    best=max(best,g)
    print(f"   Om={Om:5.1f}: lambda_top={g:+.3f}" + ("  <-- UNSTABLE" if g>0 else ""))
print(f"   best={best:+.3f}")

# (2) square-wave switching between two Hurwitz points (non-commuting route)
print("\n(2) square-wave switch Xg in {1.450, 1.490} (both Hurwitz), sweep half-period:")
for Th in [0.03,0.05,0.08,0.12,0.18,0.25,0.35]:
    def xf(t,Th=Th): return 1.490 if (int(t/Th)%2==0) else 1.450
    g=lyap_top(xf, T=200, dt=4e-4)
    print(f"   half-period={Th:4.2f}s (f={1/(2*Th):5.2f}Hz): lambda_top={g:+.3f}"
          + ("  <-- UNSTABLE" if g>0 else ""))

# (3) even more aggressive: switch {1.44, 1.491}, and 3-point
print("\n(3) aggressive switch Xg in {1.440, 1.491}:")
for Th in [0.04,0.06,0.09,0.14,0.2]:
    def xf(t,Th=Th): return 1.491 if (int(t/Th)%2==0) else 1.440
    g=lyap_top(xf, T=200, dt=4e-4)
    print(f"   half-period={Th:4.2f}s: lambda_top={g:+.3f}"
          + ("  <-- UNSTABLE" if g>0 else ""))
