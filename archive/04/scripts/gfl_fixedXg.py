import numpy as np, math
from scipy.signal import hilbert
from gfl_operating_point_stability_sim.system import make_p, make_cfg, stable_eq
from gfl_operating_point_stability_sim.analysis import A_of, critical_mode
cfg=make_cfg(); XG=1.0   # ★ 恒定电网
def rhs(dth,xp,Vdc,xiv,omg,p):
    idr=p.kp_v*(p.Vdc_ref-Vdc)+p.ki_v*xiv; iqr=p.iq_ref
    vgd=p.Vg*math.cos(dth)-p.Xg*iqr; vgq=-p.Vg*math.sin(dth)+p.Xg*idr
    Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
    return (p.omega0-omg+p.kp_pll*vgq+p.ki_pll*xp, vgq,
            (p.idc_src+1.5*(vgd*idr+vgq*iqr)/Vs)/p.Cdc, p.Vdc_ref-Vdc, -(omg-p.omega0)/p.tau_g)
def td(P,Q,V,T=14.0,dt=1.5e-4,pert=1e-6,skip=2.0):
    p=make_p(idc_src=P,iq_ref=Q,Vg=V,Xg=XG,sigma_ou=0.0); eq=stable_eq(p,cfg)
    if eq is None: return None
    d0=eq[0]; d,xp,Vdc,xiv,omg=eq[0]+pert,eq[1],eq[2],eq[3],eq[4]; n=int(T/dt); tr=np.empty(n)
    for k in range(n):
        k1=rhs(d,xp,Vdc,xiv,omg,p); k2=rhs(d+.5*dt*k1[0],xp+.5*dt*k1[1],Vdc+.5*dt*k1[2],xiv+.5*dt*k1[3],omg+.5*dt*k1[4],p)
        k3=rhs(d+.5*dt*k2[0],xp+.5*dt*k2[1],Vdc+.5*dt*k2[2],xiv+.5*dt*k2[3],omg+.5*dt*k2[4],p)
        k4=rhs(d+dt*k3[0],xp+dt*k3[1],Vdc+dt*k3[2],xiv+dt*k3[3],omg+dt*k3[4],p)
        d+=dt/6*(k1[0]+2*k2[0]+2*k3[0]+k4[0]); xp+=dt/6*(k1[1]+2*k2[1]+2*k3[1]+k4[1])
        Vdc+=dt/6*(k1[2]+2*k2[2]+2*k3[2]+k4[2]); xiv+=dt/6*(k1[3]+2*k2[3]+2*k3[3]+k4[3])
        omg+=dt/6*(k1[4]+2*k2[4]+2*k3[4]+k4[4]); tr[k]=d-d0
    i0=int(skip/dt); sig=tr[i0:]; t=np.arange(len(sig))*dt
    an=hilbert(sig); env=np.abs(an); m=len(env); a,b=int(.06*m),int(.94*m)
    return np.polyfit(t[a:b],np.log(env[a:b]),1)[0], np.polyfit(t[a:b],np.unwrap(np.angle(an))[a:b],1)[0]/(2*np.pi)
def Re_of(P,Q,V):
    A=A_of(P,Q,V,XG); return None if A is None else critical_mode(A)
def locate(var,base,lo,hi,n=240):
    xs=np.linspace(lo,hi,n); prev=None
    for x in xs:
        kw=dict(base); kw[var]=x; lam=Re_of(kw['P'],kw['Q'],kw['V'])
        if lam is None: continue
        if prev is not None and prev[1]*lam.real<0: return 0.5*(prev[0]+x)
        prev=(x,lam.real)
    return None
def finesweep(name,var,base,xc):
    # 自适应步长：让 eig Re 在窗口两端 ~±0.2
    d=1e-4; kp=dict(base);kp[var]=xc+d; km=dict(base);km[var]=xc-d
    slope=(Re_of(kp['P'],kp['Q'],kp['V']).real-Re_of(km['P'],km['Q'],km['V']).real)/(2*d)
    hr=0.2/abs(slope); step=hr/5; xs=xc+np.arange(-5,6)*step
    print(f"\n── 固定 Xg={XG}，改变 {name}（其余固定 {base}）── Hopf@{name}≈{xc:.4f}, dRe/d{name}≈{slope:.0f}")
    print(f"  {name:>8}{'Reλ(eig)':>11}{'rate(TD)':>11}{'|Δrate|':>9}{'f_H':>7}{'f(TD)':>7}{'  状态':>10}")
    re=[];rt=[];xv=[]
    for x in xs:
        kw=dict(base); kw[var]=x; lam=Re_of(kw['P'],kw['Q'],kw['V'])
        if lam is None: print(f"  {x:>8.4f}  过SN无平衡"); continue
        r=td(kw['P'],kw['Q'],kw['V']); 
        if r is None: continue
        rate,ft=r; fe=abs(lam.imag)/2/np.pi; re.append(lam.real);rt.append(rate);xv.append(x)
        st='不稳(增长)' if lam.real>0 else '稳(衰减)'
        print(f"  {x:>8.4f}{lam.real:>11.5f}{rate:>11.5f}{abs(lam.real-rate):>9.1e}{fe:>7.2f}{ft:>7.2f}   {st}")
    re,rt,xv=np.array(re),np.array(rt),np.array(xv)
    def z(a,b):
        for i in range(len(b)-1):
            if b[i]*b[i+1]<0: return a[i]-b[i]*(a[i+1]-a[i])/(b[i+1]-b[i])
    print(f"  → 交叉：eig 插值 {name}={z(xv,re):.4f}, 时域插值 {name}={z(xv,rt):.4f}, 差={abs(z(xv,re)-z(xv,rt)):.1e}; max|Δrate|={np.max(np.abs(re-rt)):.1e}")

cP=locate('P',dict(P=0,Q=0.0,V=1.0),0.60,0.749)
cV=locate('V',dict(P=0.5,Q=0.0,V=0),0.70,1.05)
cQ=locate('Q',dict(P=0.5,Q=0,V=1.0),-0.1,0.6)
print(f"固定 Xg={XG}：Hopf 位置  P→{cP:.4f}(升P失稳)  V→{cV:.4f}(降V失稳)  Q→{cQ:.4f}(升Q失稳)")
finesweep('P','P',dict(P=0,Q=0.0,V=1.0),cP)
finesweep('V','V',dict(P=0.5,Q=0.0,V=0),cV)
finesweep('Q','Q',dict(P=0.5,Q=0,V=1.0),cQ)
