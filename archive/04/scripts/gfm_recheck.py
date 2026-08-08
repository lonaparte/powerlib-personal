import numpy as np, sympy as sp
from scipy.optimize import brentq
# ---------- 沿平衡流形按 δ 参数化：E(δ) 闭式（消无功下垂），Pref(δ) ----------
# 无功下垂 E=Enom-mq(Q-Qref)，Q=(E^2-EVcosδ)/Xg  ⇒  (mq/Xg)E^2+(1-mq V cosδ/Xg)E-(Enom+mq Qref)=0
def E_of(delta,V,Xg,mq,Enom=1.0,Qref=0.0):
    a=mq/Xg; b=1-mq*V*np.cos(delta)/Xg; c=-(Enom+mq*Qref)
    if abs(a)<1e-14: return Enom  # mq=0
    disc=b*b-4*a*c; E=(-b+np.sqrt(disc))/(2*a)
    return E
def Pref_of(delta,V,Xg,mq):
    E=E_of(delta,V,Xg,mq); return E*V/Xg*np.sin(delta)
def Q_of(delta,V,Xg,mq):
    E=E_of(delta,V,Xg,mq); return (E**2-E*V*np.cos(delta))/Xg

print("=== 复查 SN(折叠)：按 δ 扫 Pref(δ)，峰值=折叠 ===")
print(f"{'Xg':>5}{'mq':>6}{'δ*_fold[deg]':>13}{'Pref_fold':>11}{'(mq=0理论)':>16}")
for Xg in [0.1,0.3,0.5,1.0]:
    for mq in [0.0,0.1,0.3]:
        dl=np.linspace(0.01,np.pi/2-1e-4,20000)
        Pr=np.array([Pref_of(d,1.0,Xg,mq) for d in dl])
        i=int(np.argmax(Pr)); dstar=dl[i]
        theo = f"δ=90°,Pref={1.0/Xg:.3f}" if mq==0 else ""
        print(f"{Xg:>5.2f}{mq:>6.2f}{np.degrees(dstar):>13.2f}{Pr[i]:>11.3f}{theo:>16}")
