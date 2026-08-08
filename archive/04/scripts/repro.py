import sys; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); n=5
def A_of(Xg):
    p=S.make_p(Xg=Xg); eq=S.stable_eq(p,cfg); return S.jacobian(eq,p,cfg)
xs=np.linspace(1.40,1.4995,800); As=np.array([A_of(x) for x in xs])
def Aint(xg):
    i=np.clip(np.searchsorted(xs,xg)-1,0,len(xs)-2); t=(xg-xs[i])/(xs[i+1]-xs[i]); return (1-t)*As[i]+t*As[i+1]
def ltop(Xg0,amp,Om,T,dt,seed):
    np.random.seed(seed); steps=int(T/dt); x=np.random.randn(n); x/=np.linalg.norm(x); s=0.;b=int(.3*steps);c=0
    for k in range(steps):
        t=k*dt
        A1=Aint(Xg0+amp*np.sin(Om*t)); k1=A1@x
        A2=Aint(Xg0+amp*np.sin(Om*(t+.5*dt))); k2=A2@(x+.5*dt*k1); k3=A2@(x+.5*dt*k2)
        A4=Aint(Xg0+amp*np.sin(Om*(t+dt))); k4=A4@(x+dt*k3)
        x=x+(dt/6)*(k1+2*k2+2*k3+k4); nr=np.linalg.norm(x)
        if k>=b: s+=np.log(nr); c+=1
        x/=nr
    return s/(c*dt)
print("convergence at Om=33 (2wn), amp=0.021, Xg0=1.47:")
for T in [60,120,200]:
    for seed in [1,2]:
        print(f"  T={T:4d} seed={seed}: {ltop(1.47,0.021,33.0,T,4e-4,seed):+.3f}")
print("\nfine Omega scan around resonance (T=150,dt=4e-4,seed=1):")
for Om in [25,29,31,32,33,34,35,37]:
    print(f"  Om={Om:5.1f}: {ltop(1.47,0.021,Om,150,4e-4,1):+.3f}")
print("\nbaseline amp=0 (no modulation) T=150:", f"{ltop(1.47,0.0,33.0,150,4e-4,1):+.3f}")
