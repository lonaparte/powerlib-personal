import numpy as np, math
from scipy.optimize import brentq
Enom=1.0
def E_of(d,V,Xg,mq,Q):
    a=mq/Xg;b=1-mq*V*math.cos(d)/Xg;c=-(Enom+mq*Q)
    return (-b+math.sqrt(b*b-4*a*c))/(2*a)
def Pf_(d,V,Xg,mq,Q): return E_of(d,V,Xg,mq,Q)*V/Xg*math.sin(d)
def dfold(V,Xg,mq,Q):
    dl=np.linspace(0.01,np.pi/2-1e-4,8000);Pr=[Pf_(d,V,Xg,mq,Q) for d in dl]
    i=int(np.argmax(Pr));return dl[i],Pr[i]
def rhs(s,P,Q,V,Xg,M,D,mq,wc):
    d,om,Pf,Qf=s;E=Enom-mq*(Qf-Q)
    Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
    return np.array([om,(P-Pf-D*om)/M,wc*(Pe-Pf),wc*(Qe-Qf)])
def sim(P,Q,V,Xg,M,D,mq,wc,d_init,T=30.0,dt=1e-4):
    E=E_of(d_init,V,Xg,mq,Q);s=np.array([d_init,0.0,Pf_(d_init,V,Xg,mq,Q),(E*E-E*V*math.cos(d_init))/Xg])
    n=int(T/dt);samp={}
    for k in range(n):
        k1=rhs(s,P,Q,V,Xg,M,D,mq,wc);k2=rhs(s+.5*dt*k1,P,Q,V,Xg,M,D,mq,wc)
        k3=rhs(s+.5*dt*k2,P,Q,V,Xg,M,D,mq,wc);k4=rhs(s+dt*k3,P,Q,V,Xg,M,D,mq,wc)
        s=s+dt/6*(k1+2*k2+2*k3+k4)
        tt=(k+1)*dt
        for T_ in (5,10,20,30):
            if abs(tt-T_)<dt/2: samp[T_]=(math.degrees(s[0]),s[1])
    return s,samp

Xg,M,D,mq,wc=0.5,0.02,0.1,0.1,2*np.pi*20
dfd,Pfold=dfold(1.0,Xg,mq,0.0)
print(f"=== 缺口1 重做：SN 时域（Xg={Xg},mq={mq},D={D}），折叠 Pref={Pfold:.3f}, δ_fold={math.degrees(dfd):.1f}° ===")
print(f"  起点 δ=45°，跑 30s，看 δ(t)：")
for tag,Pset in [("折叠下 0.955×",0.955*Pfold),("折叠上 1.045×",1.045*Pfold)]:
    s,samp=sim(Pset,0.0,1.0,Xg,M,D,mq,wc,math.radians(45.0))
    traj=" ".join(f"{T_}s:{samp[T_][0]:.1f}°" for T_ in (5,10,20,30))
    dfin,omfin=math.degrees(s[0]),s[1]
    if dfin>90 and omfin>0.02:
        v=f"失同步发散（δ 越 90° 且 dδ/dt={omfin:.3f}>0 持续增长）"
    elif omfin<1e-3 and dfin<90:
        v=f"锁定收敛（dδ/dt→{omfin:.1e}≈0，δ 稳定）"
    else:
        v=f"过渡中（dδ/dt={omfin:.3f}）"
    print(f"  Pref={Pset:.3f} ({tag}):  {traj}  → {v}")
