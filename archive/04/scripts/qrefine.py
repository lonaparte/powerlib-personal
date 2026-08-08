import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()
def info(P0,Q0,V0,Xg0):
    p=S.make_p(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); e=S.stable_eq(p,cfg)
    if e is None: return None,None,None
    A=S.jacobian(e,p,cfg)[:4,:4]; ev=np.linalg.eigvals(A)
    c=[z for z in ev if abs(z.imag)>1e-6]; lam=max(c,key=lambda z:z.real) if c else None
    return lam, ev.real.max(), e[0]
print("Q sweep refine (P=0.5,V=1,Xg=1):  does Q reach a Hopf (Reλ→0) or the SN (no eq) first?")
print(f"  {'Q':>6}{'Reλ_crit':>11}{'maxRe':>9}{'Δθ*':>9}")
for Q0 in [0.20,0.24,0.26,0.28,0.29,0.295,0.30,0.305,0.31,0.32]:
    lam,mr,th=info(0.5,Q0,1.0,1.0)
    if lam is None: print(f"  {Q0:>6.3f}   no equilibrium (SN)"); continue
    print(f"  {Q0:>6.3f}{lam.real:>11.2f}{mr:>9.2f}{th:>9.4f}")
# also check negative Q (capacitive) - does decreasing Q toward negative do anything?
print("\n negative-Q side (P=0.5,V=1,Xg=1):")
for Q0 in [0.0,-0.3,-0.6,-0.9,-1.2]:
    lam,mr,th=info(0.5,Q0,1.0,1.0)
    if lam is None: print(f"  Q={Q0:>5.2f}  no eq"); continue
    print(f"  Q={Q0:>5.2f}  Reλ={lam.real:8.2f}  Δθ*={th:.4f}")
