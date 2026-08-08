import numpy as np, math
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
def drift4(x,P,Q,V,Xg,g):
    th,xp,Vdc,xi=x
    idr=g['kpv']*(1-Vdc)+g['kiv']*xi
    vgd=V*math.cos(th)-Xg*Q; vgq=-V*math.sin(th)+Xg*idr
    Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
    return np.array([g['kp']*vgq+g['ki']*xp, vgq, (P+1.5*(vgd*idr+vgq*Q)/Vs)/g['C'], 1-Vdc])
def state(P,Q,V,Xg,g):
    th=equilibrium_angle(P,Q,V,Xg)
    return None if th is None else np.array([th,0.0,1.0,V*math.sin(th)/Xg/g['kiv']])
def Amat(P,Q,V,Xg,g,h=1e-7):
    x=state(P,Q,V,Xg,g)
    if x is None:return None
    A=np.zeros((4,4))
    for j in range(4):
        a=x.copy();b=x.copy();a[j]+=h;b[j]-=h
        A[:,j]=(drift4(a,P,Q,V,Xg,g)-drift4(b,P,Q,V,Xg,g))/(2*h)
    return A
def Psn(Q,V,Xg):
    if Q==0.0: return 0.75*V*V/Xg
    lo,hi=0.01,3*V*V/Xg
    for _ in range(50):
        mid=0.5*(lo+hi)
        if equilibrium_angle(mid,Q,V,Xg) is None: hi=mid
        else: lo=mid
    return lo
def first_crossing(g,Xg,Q=0.0,V=1.0,n=400):
    """沿 P 找首次失稳:返回 (P_cross, 类型, 频率)。类型:complex=Hopf, real=实根过零"""
    ps=Psn(Q,V,Xg);prev=None
    for P in np.linspace(0.25*ps,0.99995*ps,n):
        A=Amat(P,Q,V,Xg,g)
        if A is None:break
        ev=np.linalg.eigvals(A)
        i=int(np.argmax(ev.real));lam=ev[i]
        if prev is not None and prev<0<=lam.real:
            typ='complex' if abs(lam.imag)>1e-6 else 'REAL'
            return P, typ, abs(lam.imag)/2/math.pi, ps
        prev=lam.real
    return None,None,None,ps
GAINS={"G7(极慢PLL)":dict(kp=10,ki=100,kpv=1,kiv=50,C=0.01),
       "G8(极快PLL)":dict(kp=200,ki=8000,kpv=1,kiv=50,C=0.01),
       "G9(极快压环小电容)":dict(kp=50,ki=1000,kpv=5,kiv=200,C=0.002),
       "G10(极慢压环大电容)":dict(kp=50,ki=1000,kpv=0.2,kiv=5,C=0.1),
       "G11(混合慢快)":dict(kp=20,ki=200,kpv=2,kiv=100,C=0.005)}
XGS=[0.15,0.3,0.5,0.8,1.1,1.5]
print("== 攻击线1+3: 极端增益 × 6点Xg网格 (Q=0,V=1) ==")
for name,g in GAINS.items():
    row=[];ok_order=True;gaps=[];types=set()
    for Xg in XGS:
        pc,typ,f,ps=first_crossing(g,Xg)
        if pc is None: row.append(f"Xg={Xg}:无失稳直至SN");gaps.append(None);continue
        types.add(typ);gap=ps-pc;gaps.append(gap)
        if pc>=ps: ok_order=False
        row.append(f"{gap:.3f}({f:.1f}Hz)")
    gv=[x for x in gaps if x is not None]
    mono=all(gv[i]>gv[i+1]-1e-12 for i in range(len(gv)-1)) if len(gv)>1 else None
    print(f"  {name}: gap 序列 {row}")
    print(f"      Hopf<SN 全部={ok_order}  gap 单调降={mono}  失稳类型={types}")
print()
print("== 攻击线2: 非零 Q 与 V≠1 基点 (G1 增益) ==")
g1=dict(kp=50,ki=1000,kpv=1,kiv=50,C=0.01)
for tag,Q,V in [("Q=+0.2(吸收)",0.2,1.0),("Q=-0.2(注入)",-0.2,1.0),("V=0.9",0.0,0.9),("V=1.1",0.0,1.1)]:
    row=[];oko=True;gaps=[];types=set()
    for Xg in XGS:
        pc,typ,f,ps=first_crossing(g1,Xg,Q=Q,V=V)
        if pc is None: row.append(f"Xg={Xg}:无");gaps.append(None);continue
        types.add(typ);gaps.append(ps-pc)
        if pc>=ps: oko=False
        row.append(f"{ps-pc:.3f}")
    gv=[x for x in gaps if x is not None]
    mono=all(gv[i]>gv[i+1]-1e-12 for i in range(len(gv)-1)) if len(gv)>1 else None
    print(f"  [{tag}] gap={row}  Hopf<SN={oko} 单调降={mono} 类型={types}")
