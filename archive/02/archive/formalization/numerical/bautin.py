import numpy as np
from sweep import hopf_SCR, l1   # validated l1 pipeline (balanced match to interval)
XR=10.0
Kps=[0.05,0.1,0.2,0.3,0.5,0.8,1.2,1.8]
Kis=[10,30,60,100,150,250,400,700]
print("BAUTIN SCAN: sign of l1 at the weak-grid Hopf (X/R=10) over PLL gains (Kp_pll,Ki_pll)")
print("  nominal=(0.30,150).  value = l1 (unbalanced-norm; SIGN is the invariant).  '.'=no weak-grid Hopf")
print()
print("  Ki \\ Kp |"+"".join("%9.2f"%k for k in Kps))
print("  --------+"+"-"*9*len(Kps))
grid={}
for Ki in Kis:
    cells=[]
    for Kp in Kps:
        sh=hopf_SCR(XR,Kp,Ki)
        if sh is None: grid[(Kp,Ki)]=None; cells.append("    .    "); continue
        v,_,_=l1(sh,XR,Kp,Ki); grid[(Kp,Ki)]=v
        cells.append("%+9.2e"%v)
    print("  %6d  |"%Ki+"".join(cells))
# trace the Bautin curve: for each Ki, the Kp where l1 crosses 0 (+ -> -, hard->soft)
print("BAUTIN CURVE  l1=0  (hard subcritical  <->  soft supercritical):")
print("  Ki_pll   Kp*(Bautin)   [nominal Kp=0.30 is HARD iff 0.30 < Kp*]")
for Ki in [10,30,60,100,150,250,400,700]:
    Kpscan=np.linspace(0.03,1.8,90); prev=None; star=None
    for Kp in Kpscan:
        sh=hopf_SCR(XR,Kp,Ki)
        if sh is None: prev=None; continue
        v=l1(sh,XR,Kp,Ki)[0]
        if prev is not None and prev[1]>0 and v<0:
            lo,hi=prev[0],Kp
            for _ in range(44):
                m=(lo+hi)/2; shm=hopf_SCR(XR,m,Ki); vm=l1(shm,XR,m,Ki)[0]
                if vm>0: lo=m
                else: hi=m
            star=(lo+hi)/2; break
        prev=(Kp,v)
    if star: print("  %5d     %.4f        nominal(0.30) is %s"%(Ki,star,"HARD (subcritical)" if 0.30<star else "SOFT (supercritical)"))
    else: print("  %5d     (no +->- crossing in Kp in [0.03,1.8])"%Ki)
