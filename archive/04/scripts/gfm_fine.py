import numpy as np, math
from scipy.optimize import brentq
from scipy.signal import hilbert
Enom=1.0; Xg=0.1; M=0.02; D=0.05; mq=0.1; wc=2*np.pi*31.0
def E_of(d,V,Q):
    a=mq/Xg;b=1-mq*V*math.cos(d)/Xg;c=-(Enom+mq*Q)
    return (-b+math.sqrt(b*b-4*a*c))/(2*a)
def Pf_(d,V,Q): return E_of(d,V,Q)*V/Xg*math.sin(d)
def dfold(V,Q):
    dl=np.linspace(0.01,np.pi/2-1e-4,6000);Pr=[Pf_(d,V,Q) for d in dl]
    i=int(np.argmax(Pr));return dl[i],Pr[i]
def equil(P,Q,V):
    df,Pm=dfold(V,Q)
    if P>=Pm:return None
    d=brentq(lambda x:Pf_(x,V,Q)-P,1e-4,df);E=E_of(d,V,Q);Qf=(E*E-E*V*math.cos(d))/Xg
    return d,E,Qf
def rhs_t(d,om,Pf,Qf,P,Q,V):
    E=Enom-mq*(Qf-Q)
    Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
    return om,(P-Pf-D*om)/M,wc*(Pe-Pf),wc*(Qe-Qf)
def A_of(P,Q,V,h=1e-7):
    eq=equil(P,Q,V)
    if eq is None:return None
    st=np.array([eq[0],0.0,P,eq[2]]);A=np.zeros((4,4))
    def rr(s):return np.array(rhs_t(s[0],s[1],s[2],s[3],P,Q,V))
    for j in range(4):
        sp=st.copy();sp[j]+=h;sm=st.copy();sm[j]-=h;A[:,j]=(rr(sp)-rr(sm))/(2*h)
    return A
def crit(A):
    ev=np.linalg.eigvals(A);cx=[e for e in ev if abs(e.imag)>1e-7]
    return max(cx,key=lambda z:z.real) if cx else None
def td(P,Q,V,T=20.0,dt=2e-4,pert=1e-5,skip=3.0):
    eq=equil(P,Q,V)
    if eq is None:return None
    ds=eq[0];d,om,Pf,Qf=ds+pert,0.0,P,eq[2]
    n=int(T/dt);tr=np.empty(n)
    for k in range(n):
        k1=rhs_t(d,om,Pf,Qf,P,Q,V)
        k2=rhs_t(d+.5*dt*k1[0],om+.5*dt*k1[1],Pf+.5*dt*k1[2],Qf+.5*dt*k1[3],P,Q,V)
        k3=rhs_t(d+.5*dt*k2[0],om+.5*dt*k2[1],Pf+.5*dt*k2[2],Qf+.5*dt*k2[3],P,Q,V)
        k4=rhs_t(d+dt*k3[0],om+dt*k3[1],Pf+dt*k3[2],Qf+dt*k3[3],P,Q,V)
        d+=dt/6*(k1[0]+2*k2[0]+2*k3[0]+k4[0]); om+=dt/6*(k1[1]+2*k2[1]+2*k3[1]+k4[1])
        Pf+=dt/6*(k1[2]+2*k2[2]+2*k3[2]+k4[2]); Qf+=dt/6*(k1[3]+2*k2[3]+2*k3[3]+k4[3])
        tr[k]=d-ds
    i0=int(skip/dt); sig=tr[i0:]; t=np.arange(len(sig))*dt
    an=hilbert(sig); env=np.abs(an)
    # 裁掉 Hilbert 边缘各 5%
    m=len(env); a,b=int(0.05*m),int(0.95*m)
    rate=np.polyfit(t[a:b],np.log(env[a:b]),1)[0]
    ph=np.unwrap(np.angle(an)); freq=np.polyfit(t[a:b],ph[a:b],1)[0]/(2*np.pi)
    return rate,freq

print("=== 细扫 P（步长 0.02，Q=0，V=1），Hilbert 包络，T=20s ===")
print(f"  {'P':>6}{'Reλ(eig)':>11}{'rate(TD)':>11}{'|Δrate|':>10}{'f_H':>8}{'f(TD)':>8}{'|Δf|':>8}")
Ps=np.round(np.arange(0.80,1.161,0.02),3)
reig=[];rtd=[]
for P in Ps:
    A=A_of(P,0.0,1.0);lam=crit(A);fe=abs(lam.imag)/2/np.pi
    r=td(P,0.0,1.0);rate,ft=r
    reig.append(lam.real);rtd.append(rate)
    print(f"  {P:>6.2f}{lam.real:>11.5f}{rate:>11.5f}{abs(lam.real-rate):>10.1e}{fe:>8.4f}{ft:>8.4f}{abs(fe-ft):>8.1e}")
reig=np.array(reig);rtd=np.array(rtd)
# 从两条曲线各自插值出过零点
def zero(x,y):
    for i in range(len(y)-1):
        if y[i]*y[i+1]<0: return x[i]-y[i]*(x[i+1]-x[i])/(y[i+1]-y[i])
Pc_e=zero(Ps,reig);Pc_t=zero(Ps,rtd)
print(f"\n  Hopf 交叉点：特征值插值 P={Pc_e:.4f}   时域插值 P={Pc_t:.4f}   差={abs(Pc_e-Pc_t):.1e}")
print(f"  全表 max|Δrate|={np.max(np.abs(reig-rtd)):.1e}")
