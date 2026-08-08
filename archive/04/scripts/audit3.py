import numpy as np, math
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
G={ "G1":dict(kp=50,ki=1000,kpv=1,kiv=50,C=0.01),
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
    return None if th is None else np.array([th,0.0,1.0,V*math.sin(th)/Xg/g['kiv']])
def Amat(P,Q,V,Xg,g,h=1e-7):
    x=state(P,Q,V,Xg,g)
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
def Psn(Xg,V=1.0):return 0.75*V*V/Xg
def Phopf(g,Xg,n=400):
    ps=Psn(Xg);prev=None
    for P in np.linspace(0.3*ps,0.9999*ps,n):
        lam=mrc(Amat(P,0,1.0,Xg,g))
        if lam is None:continue
        if prev is not None and prev<0<=lam.real:return P
        prev=lam.real
    return None
# ---------- L9: 角点(临界频率跳变)跨增益 ----------
print("== L9: 边界临界频率沿 Q 的跳变（角点）跨增益 ==")
for k in ("G4","G5"):
    g=G[k];found=[]
    for Xg in (0.3,0.45,0.6):
        fseq=[]
        for Q in np.linspace(-0.05,0.25,7):
            ps=None;prev=None;hit=None
            for P in np.linspace(0.3,1.6*Psn(Xg),260):
                A=Amat(P,Q,1.0,Xg,g)
                if A is None:break
                lam=mrc(A)
                if lam is None:continue
                if prev is not None and prev<0<=lam.real: hit=abs(lam.imag)/2/math.pi;break
                prev=lam.real
            fseq.append(hit)
        good=[(q,f) for q,f in zip(np.linspace(-0.05,0.25,7),fseq) if f]
        jumps=[(good[i][0],good[i][1],good[i+1][1]) for i in range(len(good)-1)
               if good[i+1][1] and max(good[i][1],good[i+1][1])/max(1e-9,min(good[i][1],good[i+1][1]))>1.5]
        if jumps: found.append((Xg,jumps[0]))
        print(f"  {k} Xg={Xg}: 边界f(Q)={['%.1f'%f if f else '—' for f in fseq]}"+("  ←跳变" if jumps else ""))
    print(f"  {k}: 角点{'找到 '+str([(x,round(j[1],1),round(j[2],1)) for x,j in found]) if found else '未在扫描窗内找到'}")
# ---------- L12/L13: 阈值谷 3 配置 ----------
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
print("\n== L12/L13: 阈值谷（3 个差异大的配置）==")
CFG=[("G1",0.5),("G3",1.0),("G4",1.0)]
for k,Xg in CFG:
    g=G[k];ph=Phopf(g,Xg)
    # 设裕度 ~0.15
    h=2e-6;lp=mrc(Amat(ph+h,0,1,Xg,g));lm=mrc(Amat(ph-h,0,1,Xg,g))
    slope=(lp.real-lm.real)/(2*h);P0=ph-0.15/slope
    lam=mrc(Amat(P0,0,1,Xg,g));fH=abs(lam.imag)/2/math.pi
    print(f"  [{k},Xg={Xg}] P0={P0:.4f} Re={lam.real:+.3f} f_H={fH:.2f}Hz")
    for ch,fm,lo,hi,tag in [('V',fH,1e-4,2e-2,'f_H'),('V',2*fH,3e-4,3e-2,'2f_H'),
                             ('V',1.55*fH,1e-3,1e-1,'离共振'),('P',2*fH,3e-4,5e-2,'2f_H')]:
        tc,no=thresh(g,P0,Xg,ch,fm,lo,hi)
        print(f"    {ch}@{tag}({fm:.2f}Hz): {'ε_c≈%.5f'%tc if tc else '>%.3f 不逃逸'%no}")
