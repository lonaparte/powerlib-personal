import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()
def critmode(P0,Xg0):
    p=S.make_p(idc_src=P0,Xg=Xg0); e=S.stable_eq(p,cfg)
    if e is None: return None
    ev=np.linalg.eigvals(S.jacobian(e,p,cfg)[:4,:4]); c=[z for z in ev if abs(z.imag)>1e-6]
    return max(c,key=lambda z:z.real)
P0=0.5; XgH=1.4928; dRe_dXg=246.1; fH=1.921
print(f"Worked example at P={P0}, Hopf Xg={XgH} (f_H={fH} Hz, dRe/dXg={dRe_dXg}):")
print(f"  {'ΔXg':>8}{'Xg':>9}{'pred Reλ=dRe/dXg·ΔXg':>22}{'actual Reλ':>13}{'actual f[Hz]':>13}")
for dX in [-0.01,0.0,0.01,0.02]:
    Xg0=XgH+dX; lam=critmode(P0,Xg0)
    if lam is None: 
        print(f"  {dX:>8.3f}{Xg0:>9.4f}   (no equilibrium — past saddle-node)"); continue
    pred=dRe_dXg*dX
    print(f"  {dX:>8.3f}{Xg0:>9.4f}{pred:>22.2f}{lam.real:>13.2f}{abs(lam.imag)/(2*math.pi):>13.3f}")
