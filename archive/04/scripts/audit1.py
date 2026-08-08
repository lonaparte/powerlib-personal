import numpy as np, math
from scipy.optimize import brentq
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
W0=100*math.pi
# ---------- GFL 可变增益框架 ----------
G={ "G1":dict(kp=50,ki=1000,kpv=1,kiv=50,C=0.01),
    "G2":dict(kp=20,ki=200,kpv=1,kiv=50,C=0.01),
    "G3":dict(kp=100,ki=4000,kpv=1,kiv=50,C=0.01),
    "G4":dict(kp=50,ki=1000,kpv=0.5,kiv=20,C=0.05),
    "G5":dict(kp=50,ki=1000,kpv=2,kiv=100,C=0.005)}
def drift4(x,P,Q,V,Xg,g):
    th,xp,Vdc,xi=x
    idr=g['kpv']*(1-Vdc)+g['kiv']*xi
    vgd=V*math.cos(th)-Xg*Q; vgq=-V*math.sin(th)+Xg*idr
    Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
    return np.array([g['kp']*vgq+g['ki']*xp, vgq, (P+1.5*(vgd*idr+vgq*Q)/Vs)/g['C'], 1-Vdc])
def state(P,Q,V,Xg,g):
    th=equilibrium_angle(P,Q,V,Xg)
    if th is None: return None
    return np.array([th,0.0,1.0,V*math.sin(th)/Xg/g['kiv']])
def Amat(P,Q,V,Xg,g,x=None,h=1e-7):
    x=state(P,Q,V,Xg,g) if x is None else x
    if x is None:return None
    A=np.zeros((4,4))
    for j in range(4):
        xp_=x.copy();xm=x.copy();xp_[j]+=h;xm[j]-=h
        A[:,j]=(drift4(xp_,P,Q,V,Xg,g)-drift4(xm,P,Q,V,Xg,g))/(2*h)
    return A
def mrc(A):
    ev=np.linalg.eigvals(A);cx=[e for e in ev if abs(e.imag)>1e-6]
    return max(cx,key=lambda z:z.real) if cx else None
def sens(P,Q,V,Xg,g,w,h=2e-6):
    a=[P,Q,V,Xg];i={"P":0,"Q":1,"V":2,"Xg":3}[w]
    ap=a.copy();am=a.copy();ap[i]+=h;am[i]-=h
    lp=mrc(Amat(*ap,g));lm=mrc(Amat(*am,g))
    if lp is None or lm is None:return None
    return (lp.real-lm.real)/(2*h)
def Psn(Q,V,Xg):
    lo,hi=0.01,3*V*V/Xg
    for _ in range(60):
        mid=0.5*(lo+hi)
        if equilibrium_angle(mid,Q,V,Xg) is None: hi=mid
        else: lo=mid
    return lo
def Phopf(g,Xg,V=1.0,Q=0.0,n=300):
    ps=Psn(Q,V,Xg);prev=None
    for P in np.linspace(0.05*ps,0.9999*ps,n):
        lam=mrc(Amat(P,Q,V,Xg,g))
        if lam is None:continue
        if prev is not None and prev<0<=lam.real:return P,abs(lam.imag)/2/math.pi
        prev=lam.real
    return None,None
print("== L2: ∂A/∂P≡0（冻结状态,P±h）==")
for k,g in G.items():
    x=state(0.6,0.1,1.0,0.8,g)
    d=np.max(np.abs(Amat(0.605,0.1,1.0,0.8,g,x=x)-Amat(0.595,0.1,1.0,0.8,g,x=x)))
    print(f"  {k}: max|ΔA|={d:.1e}")
print("== L3: ∂A/∂Q 仅 (3,1),(3,3) 非零 ==")
for k,g in G.items():
    x=state(0.6,0.1,1.0,0.8,g)
    D=(Amat(0.6,0.1001,1.0,0.8,g,x=x)-Amat(0.6,0.0999,1.0,0.8,g,x=x))/2e-4
    off=max(abs(D[i,j]) for i in range(4) for j in range(4) if (i,j) not in [(2,0),(2,2)])
    print(f"  {k}: (3,1)={D[2,0]:+.1f} (3,3)={D[2,2]:+.1f} 其余max={off:.1e}")
print("== L1: dλ=w(ΔA)v 一阶恒等式 ==")
for k,g in G.items():
    P,Q,V,Xg=0.6,0.1,1.0,0.8;h=1e-5
    A0=Amat(P,Q,V,Xg,g);ev,Vc=np.linalg.eig(A0);W=np.linalg.inv(Vc)
    i=int(np.argmax([e.real if abs(e.imag)>1e-6 else -1e9 for e in ev]))
    v,wv=Vc[:,i],W[i,:]
    dA=(Amat(P+h,Q,V,Xg,g)-Amat(P-h,Q,V,Xg,g))/(2*h)
    pred=complex(wv@dA@v)
    lp=mrc(Amat(P+h,Q,V,Xg,g));lm=mrc(Amat(P-h,Q,V,Xg,g));brute=(lp-lm)/(2*h)
    print(f"  {k}: |pred-brute|/|brute|={abs(pred-brute)/abs(brute):.1e}")
print("== L5: ∂θ*/∂Q ÷ ∂θ*/∂P = -(3/2)V sinθ*（增益无关,多工况）==")
for (P,Q,V,Xg) in [(0.5,0.0,1.0,1.0),(0.8,0.3,0.9,0.6),(1.2,-0.3,1.1,0.5),(0.3,0.15,1.0,1.4),(2.0,-0.2,1.2,0.3)]:
    h=1e-6
    r=((equilibrium_angle(P,Q+h,V,Xg)-equilibrium_angle(P,Q-h,V,Xg))/
       (equilibrium_angle(P+h,Q,V,Xg)-equilibrium_angle(P-h,Q,V,Xg)))
    th=equilibrium_angle(P,Q,V,Xg);pred=-1.5*V*math.sin(th)
    print(f"  (P,Q,V,Xg)=({P},{Q},{V},{Xg}): 比={r:+.6f} 预测={pred:+.6f} 差={abs(r-pred):.1e}")
print("== L4: 近折叠比例 1/P:2/V:1/Xg（P=0.99·P_SN, 跨增益）==")
for k,g in G.items():
    for (Xg,V) in [(1.0,1.0),(0.5,1.0)] if k=="G1" else [(1.0,1.0)]:
        P=0.99*Psn(0,V,Xg)
        s={w:sens(P,0,V,Xg,g,w) for w in ("P","V","Xg")}
        if None in s.values(): print(f"  {k} Xg={Xg}: 无复模态,跳过");continue
        n=np.array([abs(s['P']),abs(s['V']),abs(s['Xg'])]);n/=n[0]
        ge=np.array([1/P,2/V,1/Xg]);ge/=ge[0]
        print(f"  {k} Xg={Xg},V={V}: 实测 1:{n[1]:.2f}:{n[2]:.2f}  几何 1:{ge[1]:.2f}:{ge[2]:.2f}")
print("== L6: |dQ/dV|=Xg/(2cosθ*)（P=0.99·P_SN, 跨增益×Xg）==")
for k in ("G1","G3","G4"):
    g=G[k]
    for Xg in (0.5,1.0,1.5):
        P=0.99*Psn(0,1.0,Xg);th=equilibrium_angle(P,0,1.0,Xg)
        sq,sv=sens(P,0,1.0,Xg,g,"Q"),sens(P,0,1.0,Xg,g,"V")
        if sq is None:continue
        print(f"  {k} Xg={Xg}: 实测={abs(sq/sv):.3f} 预测={Xg/(2*math.cos(th)):.3f}")
print("== L7: GFL Q 中性面存在（dRe/dQ 随 Xg 变号）==")
for k in ("G1","G3","G4"):
    g=G[k];row=[]
    for Xg in (0.05,0.1,0.2,0.5,1.0):
        P=0.7*Psn(0,1.0,Xg);s=sens(P,0,1.0,Xg,g,"Q")
        row.append(f"{Xg}:{s:+.2f}" if s is not None else f"{Xg}:—")
    print(f"  {k}: "+"  ".join(row))
print("== L8: Hopf<SN 且 gap 随 Xg 缩（跨增益）==")
for k,g in G.items():
    row=[]
    ok=True;prevgap=None
    for Xg in (0.2,0.7,1.5):
        ps=Psn(0,1.0,Xg);ph,fh=Phopf(g,Xg)
        if ph is None: row.append(f"Xg={Xg}:无Hopf(SN={ps:.2f})");ok=None;continue
        gap=ps-ph;row.append(f"Xg={Xg}:H={ph:.3f}<SN={ps:.3f} gap={gap:.3f}")
        if prevgap is not None and gap>prevgap: ok=False
        prevgap=gap
    print(f"  {k} [{'PASS' if ok else ok}]: "+" | ".join(row))
print("== L17-GFL: ζ(V) 单调升（P=0.5,Xg=1,跨增益）==")
for k,g in G.items():
    zs=[]
    for V in (0.85,1.0,1.15):
        lam=mrc(Amat(0.5,0,V,1.0,g));zs.append(-lam.real/abs(lam) if lam else float('nan'))
    mono=all(zs[i]<zs[i+1] for i in range(2))
    print(f"  {k}: ζ={['%.3f'%z for z in zs]} 单调升={mono}")
print("== L19-GFL: 折叠 V 弹性=2（Q=0数值）==")
for V in (0.9,1.0,1.1):
    h=1e-4;e=(math.log(Psn(0,V+h,1.0))-math.log(Psn(0,V-h,1.0)))/(math.log(V+h)-math.log(V-h))
    print(f"  V={V}: 弹性={e:.4f}")
print("== L20: |dRe/dP|@Hopf 随 gap 缩而增（跨增益）==")
for k in ("G1","G3","G4"):
    g=G[k];row=[]
    for Xg in (0.1,1.0,1.5):
        ph,_=Phopf(g,Xg)
        if ph is None: row.append(f"Xg={Xg}:无Hopf");continue
        s=sens(ph*0.999,0,1.0,Xg,g,"P");row.append(f"Xg={Xg}:{abs(s):.0f}")
    print(f"  {k}: "+"  ".join(row))
print("== L22-GFL: f_c(P) 是否单调（P∈0.4..0.98·SN, Xg=1）==")
for k in ("G1","G3","G4"):
    g=G[k];fs=[]
    for P in np.linspace(0.3,0.98*Psn(0,1,1.0),12):
        lam=mrc(Amat(P,0,1.0,1.0,g));fs.append(abs(lam.imag)/2/math.pi if lam else float('nan'))
    diffs=np.diff([f for f in fs if not math.isnan(f)])
    mono=bool(np.all(diffs<0) or np.all(diffs>0))
    print(f"  {k}: f 序列={['%.1f'%f for f in fs]} 单调={mono}")
