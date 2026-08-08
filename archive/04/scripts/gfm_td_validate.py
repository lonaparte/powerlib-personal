import numpy as np
from scipy.optimize import brentq
from scipy.signal import find_peaks
Enom=1.0
# 基准 VSM 配置（强网，摆-Hopf 存在）
BASE=dict(Xg=0.1,M=0.02,D=0.05,mq=0.1,wc=2*np.pi*31.0)
def E_of(d,V,Xg,mq,Q):
    a=mq/Xg;b=1-mq*V*np.cos(d)/Xg;c=-(Enom+mq*Q)
    return Enom if abs(a)<1e-14 else (-b+np.sqrt(b*b-4*a*c))/(2*a)
def Pf_(d,V,Xg,mq,Q): E=E_of(d,V,Xg,mq,Q); return E*V/Xg*np.sin(d)
def dfold(V,Xg,mq,Q):
    dl=np.linspace(0.01,np.pi/2-1e-4,6000);Pr=[Pf_(d,V,Xg,mq,Q) for d in dl]
    i=int(np.argmax(Pr));return dl[i],Pr[i]
def equil(P,Q,V,Xg,mq):
    df,Pmax=dfold(V,Xg,mq,Q)
    if P>=Pmax: return None
    d=brentq(lambda x:Pf_(x,V,Xg,mq,Q)-P,1e-4,df)
    E=E_of(d,V,Xg,mq,Q);Qf=(E**2-E*V*np.cos(d))/Xg
    return np.array([d,0.0,P,Qf])
def rhs(st,P,Q,V,Xg,M,D,mq,wc):
    d,om,Pf,Qf=st;E=Enom-mq*(Qf-Q)
    Pe=E*V/Xg*np.sin(d);Qe=(E**2-E*V*np.cos(d))/Xg
    return np.array([om,(P-Pf-D*om)/M,wc*(Pe-Pf),wc*(Qe-Qf)])
def A_of(P,Q,V,Xg,M,D,mq,wc,h=1e-7):
    st=equil(P,Q,V,Xg,mq)
    if st is None:return None
    A=np.zeros((4,4))
    for j in range(4):
        sp=st.copy();sp[j]+=h;sm=st.copy();sm[j]-=h
        A[:,j]=(rhs(sp,P,Q,V,Xg,M,D,mq,wc)-rhs(sm,P,Q,V,Xg,M,D,mq,wc))/(2*h)
    return A
def critc(A):
    ev=np.linalg.eigvals(A);cx=[e for e in ev if abs(e.imag)>1e-7]
    return max(cx,key=lambda z:z.real) if cx else None
def td(P,Q,V,Xg,M,D,mq,wc,T=6.0,dt=5e-5,pert=1e-4):
    st0=equil(P,Q,V,Xg,mq)
    if st0 is None:return None
    ds=st0[0];st=st0.copy();st[0]+=pert;a=(P,Q,V,Xg,M,D,mq,wc)
    n=int(T/dt);tr=np.empty(n)
    for k in range(n):
        k1=rhs(st,*a);k2=rhs(st+.5*dt*k1,*a);k3=rhs(st+.5*dt*k2,*a);k4=rhs(st+dt*k3,*a)
        st=st+dt/6*(k1+2*k2+2*k3+k4);tr[k]=st[0]-ds
    t=np.arange(n)*dt;pk,_=find_peaks(tr)
    if len(pk)<5:return None
    tp,ap=t[pk],tr[pk];s=int(0.35*len(tp))
    rate=np.polyfit(tp[s:],np.log(np.abs(ap[s:])),1)[0]
    freq=1.0/np.mean(np.diff(tp[s:]))
    return rate,freq

def find_cross(var,lo,hi,base,fixed,n=140):
    xs=np.linspace(lo,hi,n);prev=None;cr=None
    for x in xs:
        p=dict(fixed);p[var]=x
        A=A_of(p['P'],p['Q'],p['V'],base['Xg'],base['M'],base['D'],base['mq'],base['wc'])
        if A is None:continue
        lam=critc(A);r=lam.real if lam else None
        if r is None:continue
        if prev is not None and ((prev[1]<0<=r) or (prev[1]>=0>r)):cr=0.5*(prev[0]+x)
        prev=(x,r)
    return cr

fixed0=dict(P=0.5,Q=0.0,V=1.0)
print("定位 Hopf 交叉点（基准 Xg=0.1,M=0.02,D=0.05,mq=0.1,fc=31Hz）：")
cP=find_cross('P',0.2,3.0,BASE,fixed0)
cV=find_cross('V',0.80,1.30,BASE,dict(P=0.8,Q=0.0,V=1.0))
cQ=find_cross('Q',-0.6,1.0,BASE,dict(P=0.5,Q=0.0,V=1.0))
print(f"  P 向: Hopf@P≈{cP};  V 向: Hopf@V≈{cV};  Q 向: Hopf@Q≈{cQ}")

def validate(name,var,fixed,c,dstab,dunst):
    print(f"\n── {name} 扫描（穿越 Hopf 双向）──  固定 {fixed}")
    print(f"  {name:>6}{'Reλ(eig)':>10}{'rate(TD)':>10}{'f_H[Hz]':>9}{'f(TD)':>8}{'  判定':>16}")
    for x in [c+dstab, c-1e-9, c+dunst] if dstab<0 else [c+dstab,c+dunst]:
        pass
    for tag,x in [("稳侧",c+dstab),("不稳侧",c+dunst)]:
        p=dict(fixed);p[var]=x
        A=A_of(p['P'],p['Q'],p['V'],BASE['Xg'],BASE['M'],BASE['D'],BASE['mq'],BASE['wc'])
        lam=critc(A);fe=abs(lam.imag)/2/np.pi
        r=td(p['P'],p['Q'],p['V'],BASE['Xg'],BASE['M'],BASE['D'],BASE['mq'],BASE['wc'])
        if r is None:
            print(f"  {x:>6.3f}{lam.real:>10.3f}{'—':>10}{fe:>9.3f}{'—':>8}");continue
        rate,ft=r;verd='STABLE' if lam.real<0 else 'UNSTABLE(grow)'
        ok='✓' if (lam.real<0)==(rate<0) else '✗不符'
        print(f"  {x:>6.3f}{lam.real:>10.3f}{rate:>10.3f}{fe:>9.3f}{ft:>8.3f}   {verd} {ok}")

# P：低P不稳、高P稳（K随δ增而降）→ 稳侧=c+，不稳侧=c-
if cP: validate("P","P",dict(P=0,Q=0.0,V=1.0),cP,+0.15,-0.15)
# V：高V不稳（K∝V）→ 稳侧=c-，不稳侧=c+
if cV: validate("V","V",dict(P=0.8,Q=0.0,V=0),cV,-0.05,+0.05)
# Q：高Q不稳（抬E→抬K）→ 稳侧=c-，不稳侧=c+
if cQ: validate("Q","Q",dict(P=0.5,Q=0,V=1.0),cQ,-0.15,+0.15)

print("\n=== 加验：P 大范围扫（Q=0,V=1），看特征值与时域在远离边界处也咬合 ===")
print(f"  {'P':>6}{'δ*[deg]':>9}{'K':>7}{'Reλ(eig)':>10}{'rate(TD)':>10}{'f_H':>7}{'f(TD)':>7}{'  判定':>18}")
for P in [0.45,0.60,0.80,0.955,1.10,1.30,1.60]:
    A=A_of(P,0.0,1.0,BASE['Xg'],BASE['M'],BASE['D'],BASE['mq'],BASE['wc'])
    st=equil(P,0.0,1.0,BASE['Xg'],BASE['mq']); ds=st[0]
    E=E_of(ds,1.0,BASE['Xg'],BASE['mq'],0.0); K=E*1.0/BASE['Xg']*np.cos(ds)
    lam=critc(A); fe=abs(lam.imag)/2/np.pi
    r=td(P,0.0,1.0,BASE['Xg'],BASE['M'],BASE['D'],BASE['mq'],BASE['wc'])
    rate,ft=r if r else (float('nan'),float('nan'))
    verd=('STABLE' if lam.real<0 else 'UNSTABLE(grow)')
    ok='✓' if (lam.real<0)==(rate<0) else '✗'
    print(f"  {P:>6.3f}{np.degrees(ds):>9.2f}{K:>7.3f}{lam.real:>10.3f}{rate:>10.3f}{fe:>7.2f}{ft:>7.2f}   {verd} {ok}")
print("  K_crit=Dωc+D²/M = %.3f（K>K_crit→不稳，与上表 Re 变号点一致）"%(BASE['D']*BASE['wc']+BASE['D']**2/BASE['M']))
