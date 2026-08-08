import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()
def critmode(P0,Xg0):
    p=S.make_p(idc_src=P0,Xg=Xg0); e=S.stable_eq(p,cfg)
    if e is None: return None,None
    ev=np.linalg.eigvals(S.jacobian(e,p,cfg)[:4,:4]); c=[z for z in ev if abs(z.imag)>1e-6]
    return max(c,key=lambda z:z.real), e[0]
for P0,XgH,SN,dReXg,fH in [(0.5,1.4928,1.500,246.1,1.921),(1.0,0.7370,0.750,385.9,3.079)]:
    print(f"\nP={P0}: Hopf Xg={XgH}, SN Xg={SN} (gap={SN-XgH:.4f}), f_H={fH}Hz, dRe/dXg={dReXg}")
    print(f"   {'Xg':>8}{'region':>16}{'Reλ actual':>12}{'pred(linear)':>13}{'f[Hz]':>8}")
    for Xg0 in [XgH-0.01, XgH-0.003, XgH, XgH+0.002, XgH+0.004, (SN+XgH)/2, SN+0.005]:
        lam,th=critmode(P0,Xg0)
        if lam is None:
            print(f"   {Xg0:>8.4f}{'past SN (no eq)':>16}"); continue
        reg = "stable" if lam.real<-1e-3 else ("~Hopf" if abs(lam.real)<0.5 else "UNSTABLE(grow)")
        print(f"   {Xg0:>8.4f}{reg:>16}{lam.real:>12.2f}{dReXg*(Xg0-XgH):>13.2f}{abs(lam.imag)/(2*math.pi):>8.3f}")
