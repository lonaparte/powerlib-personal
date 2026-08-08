import numpy as np, math
from scipy.optimize import brentq
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
exec(open('/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/audit3.py').read().split('# ---------- L9')[0])

def td_escape(g,P0,Xg,ch,amp,fmod,T=40.0,dt=2e-4):
    x0=state(P0,0.0,1.0,Xg,g);s=x0.copy();s[0]+=1e-6;W=2*math.pi*fmod
    for k in range(int(T/dt)):
        t=k*dt
        def f(ss,tt):
            V=1.0+(amp if ch=='V' else 0)*math.cos(W*tt)
            P=P0+(amp if ch=='P' else 0)*math.cos(W*tt)
            return drift4(ss,P,0.0,V,Xg,g)
        k1=f(s,t);k2=f(s+.5*dt*k1,t+.5*dt);k3=f(s+.5*dt*k2,t+.5*dt);k4=f(s+dt*k3,t+dt)
        s=s+dt/6*(k1+2*k2+2*k3+k4)
        if not np.isfinite(s[0]) or abs(s[0]-x0[0])>1.0:return True
    return False
def thresh(g,P0,Xg,ch,fmod,lo,hi,it=3):
    if not td_escape(g,P0,Xg,ch,hi,fmod):return None,hi
    for _ in range(it):
        mid=math.sqrt(lo*hi)
        if td_escape(g,P0,Xg,ch,mid,fmod):hi=mid
        else:lo=mid
    return math.sqrt(lo*hi),None
# --- 修正 ---
def P_at_margin(g,Xg,target=-0.15,n=600):
    ps=Psn(Xg);prev=None
    for P in np.linspace(0.3*ps,0.9999*ps,n):
        lam=mrc(Amat(P,0,1.0,Xg,g))
        if lam is None:continue
        if lam.real>=0: break
        if prev is not None and prev[1]<target<=lam.real:
            return 0.5*(prev[0]+P)
        prev=(P,lam.real)
    return None
print("== L12/L13 配置a 重做: G1, Xg=0.5, 正确落在稳定侧 ==")
g=G["G1"];Xg=0.5
P0=P_at_margin(g,Xg)
lam=mrc(Amat(P0,0,1.0,Xg,g));fH=abs(lam.imag)/2/math.pi
print(f"  P0={P0:.4f} Re={lam.real:+.3f} f_H={fH:.2f}Hz")
for ch,fm,lo,hi,tag in [('V',fH,1e-4,2e-2,'f_H'),('V',2*fH,3e-4,3e-2,'2f_H'),
                         ('V',1.55*fH,1e-3,1e-1,'离共振'),('P',2*fH,3e-4,5e-2,'2f_H')]:
    tc,no=thresh(g,P0,Xg,ch,fm,lo,hi)
    print(f"    {ch}@{tag}({fm:.2f}Hz): {'ε_c≈%.5f'%tc if tc else '>%.3f 不逃逸'%no}")
print("\n== L21: 越过 Hopf 的归宿 跨配置 ==")
def gfl_after(g,Xg,dP,T=25.0,dt=2e-4):
    ph=Phopf(g,Xg);P=ph+dP
    lam=mrc(Amat(P,0,1.0,Xg,g))
    x0=state(P,0,1.0,Xg,g);s=x0.copy();s[0]+=1e-4;mx=0
    for k in range(int(T/dt)):
        k1=drift4(s,P,0,1.0,Xg,g);k2=drift4(s+.5*dt*k1,P,0,1.0,Xg,g)
        k3=drift4(s+.5*dt*k2,P,0,1.0,Xg,g);k4=drift4(s+dt*k3,P,0,1.0,Xg,g)
        s=s+dt/6*(k1+2*k2+2*k3+k4);mx=max(mx,abs(s[0]-x0[0]))
        if mx>50:return lam.real,mx,(k+1)*dt
    return lam.real,mx,T
for k,Xg,dP in [("G3",1.0,0.004),("G4",1.0,0.02)]:
    re,mx,t=gfl_after(G[k],Xg,dP)
    print(f"  GFL {k},Xg={Xg}: Re={re:+.3f} max|Δθ|={mx:.1f}rad @t={t:.1f}s → {'失步' if mx>3 else '有界'}")
# GFM M5 有界性
Enom=1.0
m5=dict(M=0.02,D=0.02,mq=0.1,wc=2*np.pi*20)
def E_of(d,V,Xg,mq,Q):
    if mq<1e-12:return Enom
    a=mq/Xg;b=1-mq*V*math.cos(d)/Xg;c=-(Enom+mq*Q)
    return (-b+math.sqrt(b*b-4*a*c))/(2*a)
def Pc(d,V,Xg,mq,Q):return E_of(d,V,Xg,mq,Q)*V/Xg*math.sin(d)
def gfm_eq(P,Xg,mq):
    dl=np.linspace(0.01,np.pi/2-1e-4,3000);Pr=[Pc(x,1.0,Xg,mq,0) for x in dl]
    i=int(np.argmax(Pr))
    d=brentq(lambda x:Pc(x,1.0,Xg,mq,0)-P,1e-4,dl[i])
    E=E_of(d,1.0,Xg,mq,0);return np.array([d,0.0,P,(E*E-E*math.cos(d))/Xg])
def gfm_rhs(s,P,Xg,m):
    d,om,Pf,Qf=s;E=Enom-m['mq']*Qf
    Pe=E/Xg*math.sin(d);Qe=(E*E-E*math.cos(d))/Xg
    return np.array([om,(P-Pf-m['D']*om)/m['M'],m['wc']*(Pe-Pf),m['wc']*(Qe-Qf)])
st0=gfm_eq(1.0,0.1,0.1);s=st0.copy();s[0]+=1e-3;dt=2e-4;tail=[]
esc=False
for k in range(int(60/dt)):
    k1=gfm_rhs(s,1.0,0.1,m5);k2=gfm_rhs(s+.5*dt*k1,1.0,0.1,m5)
    k3=gfm_rhs(s+.5*dt*k2,1.0,0.1,m5);k4=gfm_rhs(s+dt*k3,1.0,0.1,m5)
    s=s+dt/6*(k1+2*k2+2*k3+k4)
    if not np.isfinite(s[0]) or abs(s[0]-st0[0])>6: esc=True;break
    if k>int(52/dt): tail.append(abs(s[0]-st0[0]))
print(f"  GFM M5,P=1.0(Re=+1.36): {'失步' if esc else '有界极限环 幅值=%.0f°'%math.degrees(max(tail))}")
print("\n== L14: 静态灵敏度 vs 共振响应排序 (GFM M2,M4) ==")
def gfm_eigs4(P,Xg,m,h=1e-7):
    st=gfm_eq(P,Xg,m['mq']);A=np.zeros((4,4))
    for j in range(4):
        a=st.copy();b=st.copy();a[j]+=h;b[j]-=h
        A[:,j]=(gfm_rhs(a,P,Xg,m)-gfm_rhs(b,P,Xg,m))/(2*h)
    return np.linalg.eigvals(A)
def gfm_amp(P,Xg,m,ch,amp,fmod,T=50.0,dt=2e-4):
    st0=gfm_eq(P,Xg,m['mq']);s=st0.copy();s[0]+=1e-6;W=2*math.pi*fmod;mx=0
    Enom_=Enom
    for k in range(int(T/dt)):
        t=k*dt
        def f(ss,tt):
            d,om,Pf,Qf=ss;E=Enom_-m['mq']*Qf
            V=1.0+(amp if ch=='V' else 0)*math.cos(W*tt)
            Pd=P+(amp if ch=='P' else 0)*math.cos(W*tt)
            Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
            return np.array([om,(Pd-Pf-m['D']*om)/m['M'],m['wc']*(Pe-Pf),m['wc']*(Qe-Qf)])
        k1=f(s,t);k2=f(s+.5*dt*k1,t+.5*dt);k3=f(s+.5*dt*k2,t+.5*dt);k4=f(s+dt*k3,t+dt)
        s=s+dt/6*(k1+2*k2+2*k3+k4)
        if k>int(35/dt): mx=max(mx,abs(s[0]-st0[0]))
    return mx
MS2={"M2":dict(M=0.1,D=0.2,mq=0.05,wc=2*np.pi*10),"M4":dict(M=0.05,D=0.5,mq=0.1,wc=2*np.pi*5)}
for k,m in MS2.items():
    ev=gfm_eigs4(1.3,0.1,m);cx=[e for e in ev if abs(e.imag)>1e-7]
    lam=max(cx,key=lambda z:z.real);fH=abs(lam.imag)/2/math.pi
    h=1e-5
    def reof(P,V):
        ev=gfm_eigs4(P,0.1,m) if abs(V-1)<1e-12 else None
        return None
    # 静态灵敏度（数值）
    def sV(dv):
        st=None
        # 重新实现: 简单用扰动 V 的特征值 — 需要 V 参数化的 eq; 用近似: 直接扰动 rhs 中 V
        return None
    # 简化: 只比较共振响应（静态比引用 battery-A 方法另算）
    aV=gfm_amp(1.3,0.1,m,'V',0.01,fH); aP=gfm_amp(1.3,0.1,m,'P',0.01,fH)
    print(f"  {k}: f_H={fH:.2f}Hz  共振响应 |Δδ|: V={math.degrees(aV):.2f}° P={math.degrees(aP):.2f}° 比={aV/aP:.2f}")
