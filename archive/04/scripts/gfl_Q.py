import numpy as np, math
from scipy.signal import hilbert
from gfl_operating_point_stability_sim.system import make_p, make_cfg, stable_eq
from gfl_operating_point_stability_sim.analysis import A_of, critical_mode
cfg=make_cfg(); XG=1.0
def rhs(dth,xp,Vdc,xiv,omg,p):
    idr=p.kp_v*(p.Vdc_ref-Vdc)+p.ki_v*xiv; iqr=p.iq_ref
    vgd=p.Vg*math.cos(dth)-p.Xg*iqr; vgq=-p.Vg*math.sin(dth)+p.Xg*idr
    Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
    return (p.omega0-omg+p.kp_pll*vgq+p.ki_pll*xp, vgq,
            (p.idc_src+1.5*(vgd*idr+vgq*iqr)/Vs)/p.Cdc, p.Vdc_ref-Vdc, -(omg-p.omega0)/p.tau_g)
def td(P,Q,V,T=16.0,dt=1.5e-4,pert=1e-6,skip=2.5):
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
def lam_of(Q):
    A=A_of(0.5,Q,1.0,XG); return None if A is None else critical_mode(A)
# 精定位 Q-Hopf：细扫找 critical 复模态 Re 过零
Qs=np.arange(0.235,0.250,0.0002); prev=None; cQ=None
for q in Qs:
    l=lam_of(q)
    if prev is not None and prev[1]<0<=l.real: cQ=0.5*(prev[0]+q); break
    prev=(q,l.real)
print(f"固定 Xg={XG}, P=0.5, V=1：重定位 Q-Hopf = {cQ:.4f}")
d=1e-4; slope=(lam_of(cQ+d).real-lam_of(cQ-d).real)/(2*d); step=(0.2/abs(slope))/5
print(f"  dRe/dQ≈{slope:.0f}；细扫 Q（步长 {step:.1e}）跨越交叉点：")
print(f"  {'Q':>8}{'Reλ(eig)':>11}{'rate(TD)':>11}{'|Δrate|':>9}{'f_H':>7}{'f(TD)':>7}{'  状态':>10}")
xs=cQ+np.arange(-5,6)*step; re=[];rt=[];xv=[]
for q in xs:
    l=lam_of(q); r=td(0.5,q,1.0)
    if l is None or r is None: continue
    rate,ft=r; fe=abs(l.imag)/2/np.pi; re.append(l.real);rt.append(rate);xv.append(q)
    st='不稳(增长)' if l.real>0 else '稳(衰减)'
    print(f"  {q:>8.4f}{l.real:>11.5f}{rate:>11.5f}{abs(l.real-rate):>9.1e}{fe:>7.2f}{ft:>7.2f}   {st}")
re,rt,xv=np.array(re),np.array(rt),np.array(xv)
def z(a,b):
    for i in range(len(b)-1):
        if b[i]*b[i+1]<0: return a[i]-b[i]*(a[i+1]-a[i])/(b[i+1]-b[i])
    return None
ze,zt=z(xv,re),z(xv,rt)
print(f"  → 交叉：eig 插值 Q={ze:.4f}, 时域插值 Q={zt:.4f}, 差={abs(ze-zt):.1e}; 近交叉 max|Δrate|={np.max(np.abs(re-rt)[np.abs(re)<0.25]):.1e}")
