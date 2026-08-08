import numpy as np, math
from scipy.optimize import brentq
from scipy.signal import hilbert
Enom=1.0
def E_of(d,V,Xg,mq,Q):
    a=mq/Xg;b=1-mq*V*math.cos(d)/Xg;c=-(Enom+mq*Q)
    return (-b+math.sqrt(b*b-4*a*c))/(2*a)
def Pf_(d,V,Xg,mq,Q): return E_of(d,V,Xg,mq,Q)*V/Xg*math.sin(d)
def dfold(V,Xg,mq,Q):
    dl=np.linspace(0.01,np.pi/2-1e-4,8000);Pr=[Pf_(d,V,Xg,mq,Q) for d in dl]
    i=int(np.argmax(Pr));return dl[i],Pr[i]
def equil(P,V,Xg,mq,Q):
    df,Pm=dfold(V,Xg,mq,Q)
    if P>=Pm:return None
    d=brentq(lambda x:Pf_(x,V,Xg,mq,Q)-P,1e-4,df);E=E_of(d,V,Xg,mq,Q);Qf=(E*E-E*V*math.cos(d))/Xg
    return d,E,Qf

# ---------- 缺口1：SN 时域——越过折叠是否真的失同步发散 ----------
def rhs_vsm(s,P,Q,V,Xg,M,D,mq,wc):
    d,om,Pf,Qf=s;E=Enom-mq*(Qf-Q)
    Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
    return np.array([om,(P-Pf-D*om)/M,wc*(Pe-Pf),wc*(Qe-Qf)])
def sim_vsm(P,Q,V,Xg,M,D,mq,wc,s0,T=3.0,dt=1e-4):
    s=s0.copy();n=int(T/dt);dtr=np.empty(n)
    for k in range(n):
        k1=rhs_vsm(s,P,Q,V,Xg,M,D,mq,wc);k2=rhs_vsm(s+.5*dt*k1,P,Q,V,Xg,M,D,mq,wc)
        k3=rhs_vsm(s+.5*dt*k2,P,Q,V,Xg,M,D,mq,wc);k4=rhs_vsm(s+dt*k3,P,Q,V,Xg,M,D,mq,wc)
        s=s+dt/6*(k1+2*k2+2*k3+k4);dtr[k]=s[0]
    return np.arange(n)*dt,dtr

Xg,M,D,mq,wc=0.5,0.02,0.5,0.1,2*np.pi*20
dfd,Pfold=dfold(1.0,Xg,mq,0.0)
print(f"=== 缺口1 SN 时域验证：Xg={Xg},mq={mq} 折叠 Pref={Pfold:.3f}, δ_fold={math.degrees(dfd):.1f}° ===")
# 起点取折叠前平衡（Pref=0.98*fold），然后把 Pref 阶跃到折叠两侧
d0,E0,Qf0=equil(0.98*Pfold,1.0,Xg,mq,0.0); s0=np.array([d0,0.0,0.98*Pfold,Qf0])
for tag,Pset in [("折叠下 0.99×",0.99*Pfold),("折叠上 1.02×",1.02*Pfold)]:
    t,dtr=sim_vsm(Pset,0.0,1.0,Xg,M,D,mq,wc,s0)
    dend=math.degrees(dtr[-1]); grew=dtr[-1]-dtr[0]
    verdict = "失同步：δ 越过 90° 持续增长（发散）" if dtr[-1]>np.pi/2 and grew>0.3 else "锁定：δ 收敛到新平衡"
    print(f"  Pref={Pset:.3f} ({tag}): δ(0)={math.degrees(dtr[0]):.1f}° → δ(3s)={dend:.1f}°  → {verdict}")

# ---------- 缺口2：最小下垂无 Hopf——代表点时域是否只衰减不增长 ----------
def rhs_droop(s,P,Q,V,Xg,mp,mq,wc):
    d,Pf,Qf=s;E=Enom-mq*(Qf-Q)
    Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
    return np.array([-mp*(Pf-P),wc*(Pe-Pf),wc*(Qe-Qf)])
def A_droop(P,Q,V,Xg,mp,mq,wc,h=1e-7):
    eq=equil(P,V,Xg,mq,Q); s=np.array([eq[0],P,eq[2]]);A=np.zeros((3,3))
    for j in range(3):
        sp=s.copy();sp[j]+=h;sm=s.copy();sm[j]-=h
        A[:,j]=(rhs_droop(sp,P,Q,V,Xg,mp,mq,wc)-rhs_droop(sm,P,Q,V,Xg,mp,mq,wc))/(2*h)
    return A
def sim_droop(P,Q,V,Xg,mp,mq,wc,T=12.0,dt=2e-4,pert=1e-4,skip=1.5):
    eq=equil(P,V,Xg,mq,Q);ds=eq[0];s=np.array([ds+pert,P,eq[2]]);n=int(T/dt);tr=np.empty(n)
    for k in range(n):
        k1=rhs_droop(s,P,Q,V,Xg,mp,mq,wc);k2=rhs_droop(s+.5*dt*k1,P,Q,V,Xg,mp,mq,wc)
        k3=rhs_droop(s+.5*dt*k2,P,Q,V,Xg,mp,mq,wc);k4=rhs_droop(s+dt*k3,P,Q,V,Xg,mp,mq,wc)
        s=s+dt/6*(k1+2*k2+2*k3+k4);tr[k]=s[0]-ds
    i0=int(skip/dt);sig=tr[i0:];t=np.arange(len(sig))*dt
    env=np.abs(hilbert(sig));m=len(env);a,b=int(.05*m),int(.95*m)
    return np.polyfit(t[a:b],np.log(env[a:b]),1)[0]
print(f"\n=== 缺口2 下垂无 Hopf 时域验证：代表点扰动率 rate(TD) vs Reλ(eig) ===")
print(f"  {'(Xg,mp,mq,wc,P)':>26}{'Reλ_c(eig)':>12}{'rate(TD)':>11}{'  一致?':>8}")
cases=[(1.0,2.0,0.02,5,0.30),(0.3,0.5,0.1,20,0.60),(0.5,0.1,0.3,100,0.90),(0.1,0.1,0.1,50,0.50)]
for Xg2,mp,mq2,wc2,fr in cases:
    df2,Pf2=dfold(1.0,Xg2,mq2,0.0);P=fr*Pf2
    A=A_droop(P,0.0,1.0,Xg2,mp,mq2,wc2);ev=np.linalg.eigvals(A)
    cx=[e for e in ev if abs(e.imag)>1e-7];rec=max(cx,key=lambda z:z.real).real if cx else max(ev.real)
    rate=sim_droop(P,0.0,1.0,Xg2,mp,mq2,wc2)
    ok='✓ 都衰减' if (rec<0 and rate<0) else '✗'
    print(f"  {str((Xg2,mp,mq2,wc2,round(P,2))):>26}{rec:>12.4f}{rate:>11.4f}{ok:>10}")
