import numpy as np, math
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
g1=dict(kp=50,ki=1000,kpv=1,kiv=50,C=0.01)
def drift4(x,P,Q,V,Xg,g):
    th,xp,Vdc,xi=x
    idr=g['kpv']*(1-Vdc)+g['kiv']*xi
    vgd=V*math.cos(th)-Xg*Q; vgq=-V*math.sin(th)+Xg*idr
    Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
    return np.array([g['kp']*vgq+g['ki']*xp, vgq, (P+1.5*(vgd*idr+vgq*Q)/Vs)/g['C'], 1-Vdc])
def state(P,Q,V,Xg,g):
    th=equilibrium_angle(P,Q,V,Xg)
    return None if th is None else np.array([th,0.0,1.0,V*math.sin(th)/Xg/g['kiv']])
def Amat(P,Q,V,Xg,g,x=None,h=1e-7):
    x=state(P,Q,V,Xg,g) if x is None else x
    if x is None:return None
    A=np.zeros((4,4))
    for j in range(4):
        a=x.copy();b=x.copy();a[j]+=h;b[j]-=h
        A[:,j]=(drift4(a,P,Q,V,Xg,g)-drift4(b,P,Q,V,Xg,g))/(2*h)
    return A
def mrc(A):
    if A is None:return None
    ev=np.linalg.eigvals(A);cx=[e for e in ev if abs(e.imag)>1e-6]
    return max(cx,key=lambda z:z.real) if cx else None
def Psn_num(Q,V,Xg):
    lo,hi=0.01,3*V*V/Xg
    for _ in range(50):
        mid=0.5*(lo+hi)
        if equilibrium_angle(mid,Q,V,Xg) is None: hi=mid
        else: lo=mid
    return lo
def P_margin(g,Q,V,Xg,target=-0.15,n=700):
    ps=Psn_num(Q,V,Xg);prev=None
    for P in np.linspace(0.3*ps,0.9999*ps,n):
        lam=mrc(Amat(P,Q,V,Xg,g))
        if lam is None:continue
        if lam.real>=0:break
        if prev is not None and prev[1]<target<=lam.real:return 0.5*(prev[0]+P)
        prev=(P,lam.real)
    return None
def pump(P,Q,V,Xg,g,ch,h=1e-6):
    x=state(P,Q,V,Xg,g);A0=Amat(P,Q,V,Xg,g)
    ev,Vc=np.linalg.eig(A0);W=np.linalg.inv(Vc)
    i=int(np.argmax([e.real if abs(e.imag)>1e-6 else -1e9 for e in ev]))
    v,w=Vc[:,i],W[i,:]
    if ch=='V': Ap=Amat(P,Q,V+h,Xg,g,x=x);Am=Amat(P,Q,V-h,Xg,g,x=x)
    else:       Ap=Amat(P,Q+h,V,Xg,g,x=x);Am=Amat(P,Q-h,V,Xg,g,x=x)
    C=(Ap-Am)/(2*h);return abs(w@C@v)
def esc(g,P0,Q,V,Xg,ch,amp,fmod,T=40.0,dt=2e-4):
    x0=state(P0,Q,V,Xg,g);s=x0.copy();s[0]+=1e-6;W=2*math.pi*fmod
    for k in range(int(T/dt)):
        t=k*dt
        def f(ss,tt):
            Vt=V*(1+(amp if ch=='V' else 0)*math.cos(W*tt))
            Pt=P0+(amp if ch=='P' else 0)*math.cos(W*tt)
            return drift4(ss,Pt,Q,Vt,Xg,g)
        k1=f(s,t);k2=f(s+.5*dt*k1,t+.5*dt);k3=f(s+.5*dt*k2,t+.5*dt);k4=f(s+dt*k3,t+dt)
        s=s+dt/6*(k1+2*k2+2*k3+k4)
        if not np.isfinite(s[0]) or abs(s[0]-x0[0])>1.0:return True
    return False
def thr(g,P0,Q,V,Xg,ch,fmod,lo,hi,it=3):
    if not esc(g,P0,Q,V,Xg,ch,hi,fmod):return None,hi
    for _ in range(it):
        mid=math.sqrt(lo*hi)
        if esc(g,P0,Q,V,Xg,ch,mid,fmod):hi=mid
        else:lo=mid
    return math.sqrt(lo*hi),None
for tag,Q,V,Xg in [("C1:Xg=0.7",0.0,1.0,0.7),("C2:Xg=1.5(近BT)",0.0,1.0,1.5),("C3:Q基点=0.15",0.15,1.0,1.0)]:
    P0=P_margin(g1,Q,V,Xg)
    if P0 is None: print(f"[{tag}] 找不到裕度点"); continue
    lam=mrc(Amat(P0,Q,V,Xg,g1));fH=abs(lam.imag)/2/math.pi
    gV=pump(P0,Q,V,Xg,g1,'V');gQ=pump(P0,Q,V,Xg,g1,'Q')
    print(f"[{tag}] P0={P0:.4f} Re={lam.real:+.3f} f_H={fH:.2f}Hz 泵增益|wCv|: V={gV:.0f} Q={gQ:.0f}")
    for ch,fm,lo,hi,t in [('V',fH,3e-5,2e-2,'f_H'),('V',2*fH,1e-4,3e-2,'2f_H'),
                           ('V',1.55*fH,3e-4,1e-1,'离共振'),('P',2*fH,1e-4,5e-2,'2f_H')]:
        tc,no=thr(g1,P0,Q,V,Xg,ch,fm,lo,hi)
        print(f"    {ch}@{t}({fm:.2f}Hz): {'ε_c≈%.5f'%tc if tc else '>%.3f 不逃逸'%no}")
