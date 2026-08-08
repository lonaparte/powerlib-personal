import sys; sys.path.insert(0,'src')
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()
def spec(Xg):
    p=S.make_p(Xg=Xg); eq=S.stable_eq(p,cfg)
    if eq is None: return None,None
    A=S.jacobian(eq,p,cfg); return A,np.linalg.eigvals(A)
print(f"{'Xg':>7} {'core_pair_Re':>13} {'omega_n':>9}")
for Xg in np.linspace(1.40,1.499,20):
    A,ev=spec(Xg)
    if ev is None: print(f"{Xg:7.4f}  no-eq"); continue
    # exclude the ~-10 OU mode; find least-damped complex core mode
    comp=[e for e in ev if abs(e.imag)>1e-6]
    e=max(comp,key=lambda z:z.real)
    print(f"{Xg:7.4f} {e.real:13.4f} {abs(e.imag):9.3f}")
