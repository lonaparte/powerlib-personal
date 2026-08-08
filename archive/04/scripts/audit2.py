import numpy as np, math
from scipy.optimize import brentq
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
Enom=1.0
MS={"M1":dict(M=0.02,D=0.05,mq=0.1,wc=2*np.pi*31),
    "M2":dict(M=0.1,D=0.2,mq=0.05,wc=2*np.pi*10),
    "M3":dict(M=0.005,D=0.02,mq=0.2,wc=2*np.pi*100),
    "M4":dict(M=0.05,D=0.5,mq=0.1,wc=2*np.pi*5),
    "M5":dict(M=0.02,D=0.02,mq=0.1,wc=2*np.pi*20)}
def E_of(d,V,Xg,mq,Q):
    if mq<1e-12:return Enom
    a=mq/Xg;b=1-mq*V*math.cos(d)/Xg;c=-(Enom+mq*Q)
    return (-b+math.sqrt(b*b-4*a*c))/(2*a)
def Pc(d,V,Xg,mq,Q):return E_of(d,V,Xg,mq,Q)*V/Xg*math.sin(d)
def fold(V,Xg,mq,Q):
    dl=np.linspace(0.01,np.pi/2-1e-4,3000);Pr=[Pc(x,V,Xg,mq,Q) for x in dl]
    i=int(np.argmax(Pr));return dl[i],Pr[i]
def eq(P,Q,V,Xg,mq):
    df,Pm=fold(V,Xg,mq,Q)
    if P>=Pm:return None
    d=brentq(lambda x:Pc(x,V,Xg,mq,Q)-P,1e-4,df)
    E=E_of(d,V,Xg,mq,Q);return np.array([d,0.0,P,(E*E-E*V*math.cos(d))/Xg])
def rhs(s,P,Q,V,Xg,m):
    d,om,Pf,Qf=s;E=Enom-m['mq']*(Qf-Q)
    Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
    return np.array([om,(P-Pf-m['D']*om)/m['M'],m['wc']*(Pe-Pf),m['wc']*(Qe-Qf)])
def eigs(P,Q,V,Xg,m,h=1e-7):
    st=eq(P,Q,V,Xg,m['mq'])
    if st is None:return None
    A=np.zeros((4,4))
    for j in range(4):
        sp=st.copy();sm=st.copy();sp[j]+=h;sm[j]-=h
        A[:,j]=(rhs(sp,P,Q,V,Xg,m)-rhs(sm,P,Q,V,Xg,m))/(2*h)
    return np.linalg.eigvals(A)
def mrc(ev):
    cx=[e for e in ev if abs(e.imag)>1e-7]
    return max(cx,key=lambda z:z.real) if cx else None
print("== L15: 轻载 Hopf 存在性 ⇔ ωc<K/D−D/M（P=0.3,Xg=0.1）+ 加载单调稳定化 ==")
for k,m in MS.items():
    st=eq(0.3,0,1.0,0.1,m['mq']);d0=st[0];E0=E_of(d0,1.0,0.1,m['mq'],0)
    K=E0*1.0/0.1*math.cos(d0);cond=m['wc']<K/m['D']-m['D']/m['M']
    lam=mrc(eigs(0.3,0,1.0,0.1,m))
    res=[]
    prev=None;mono=True
    for P in (0.3,1.0,3.0,5.0,6.5):
        ev=eigs(P,0,1.0,0.1,m)
        if ev is None:break
        l=mrc(ev)
        if l is None:break
        if prev is not None and l.real>prev+1e-9: mono=False
        prev=l.real;res.append(l.real)
    pred='不稳' if cond else '稳'; act='不稳' if lam.real>0 else '稳'
    print(f"  {k}: 预测={pred} 实测={act} {'✓' if pred==act else '✗'} | Re(P↑)={['%.3f'%r for r in res]} 单调降={mono}")
print("== L16: 近折叠(0.995·Pfold)复对保持阻尼、频率坍缩 ==")
for k,m in MS.items():
    _,Pm=fold(1.0,0.1,m['mq'],0);ev=eigs(0.995*Pm,0,1.0,0.1,m)
    c=mrc(ev);rl=max((e.real for e in ev if abs(e.imag)<=1e-7),default=None)
    if c is None: print(f"  {k}: 复对已并入实轴; max实根={rl:.3f}"); continue
    print(f"  {k}: 复对 Re={c.real:+.3f} f={abs(c.imag)/2/np.pi:.2f}Hz  max实根={rl if rl is not None else float('nan'):+.3f}")
print("== L17-GFM: ζ(V) 单调降（P=1.3,Xg=0.1）==")
for k,m in MS.items():
    zs=[]
    for V in (0.85,1.0,1.15):
        ev=eigs(1.3,0,V,0.1,m);l=mrc(ev) if ev is not None else None
        zs.append(-l.real/abs(l) if l else float('nan'))
    good=[z for z in zs if not math.isnan(z)]
    mono=all(good[i]>good[i+1] for i in range(len(good)-1))
    print(f"  {k}: ζ={['%.4f'%z for z in zs]} 单调降={mono}")
print("== L18: dRe/dQref>0 遍历（P=1.3,Xg=0.1）==")
h=1e-5
for k,m in MS.items():
    lp=mrc(eigs(1.3,h,1.0,0.1,m));lm=mrc(eigs(1.3,-h,1.0,0.1,m))
    print(f"  {k}: dRe/dQref={(lp.real-lm.real)/(2*h):+.4f}")
print("== L19-GFM: 折叠 V 弹性（V=1）==")
for mq in (0.0,0.1,0.3):
    h=1e-4
    e=(math.log(fold(1+h,0.1,mq,0)[1])-math.log(fold(1-h,0.1,mq,0)[1]))/(math.log(1+h)-math.log(1-h))
    print(f"  mq={mq}: 弹性={e:.4f}")
print("== L22-GFM: f(P) 单调降 ==")
for k,m in MS.items():
    fs=[]
    for P in (0.5,2.0,4.0,6.0,6.7):
        ev=eigs(P,0,1.0,0.1,m);l=mrc(ev) if ev is not None else None
        fs.append(abs(l.imag)/2/np.pi if l else float('nan'))
    good=[f for f in fs if not math.isnan(f)]
    mono=all(good[i]>good[i+1] for i in range(len(good)-1))
    print(f"  {k}: f={['%.2f'%f for f in fs]} 单调降={mono}")
