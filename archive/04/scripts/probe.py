import sys; sys.path.insert(0,'src')
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()  # Mode1 PU
def A_of_Xg(Xg):
    p=S.make_p(Xg=Xg)
    eq=S.stable_eq(p,cfg)
    if eq is None: return None,None,None
    A=S.jacobian(eq,p,cfg)
    return A,np.linalg.eigvals(A),eq
print("SN Xg =", S.saddle_node_Xg(S.make_p()))
print(f"{'Xg':>6} {'maxReEig':>12} {'crit_pair_omega':>16} {'stable?':>8}")
Xgs=np.linspace(0.1,1.45,28)
hopf=None; prev=None
for Xg in Xgs:
    A,ev,eq=A_of_Xg(Xg)
    if A is None: 
        print(f"{Xg:6.3f}   no-eq"); continue
    re=ev.real; mx=re.max()
    # frequency of the least-damped complex pair
    idx=np.argsort(re)[::-1]
    om=abs(ev[idx[0]].imag)
    print(f"{Xg:6.3f} {mx:12.4f} {om:16.3f} {str(mx<0):>8}")
    if prev is not None and prev<0<=mx and hopf is None:
        hopf=Xg
    prev=mx
print("approx Hopf Xg ~", hopf)
# baseline spectrum
A,ev,eq=A_of_Xg(0.1)
print("\nBaseline Xg=0.1 eigenvalues:")
for e in sorted(ev,key=lambda z:z.real): print("  ", np.round(e,4))
