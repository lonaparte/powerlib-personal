import numpy as np, math
from scipy.signal import hilbert
from gfl_operating_point_stability_sim.system import make_p, make_cfg, stable_eq, _drift_pu
from gfl_operating_point_stability_sim.analysis import A_of, critical_mode
cfg=make_cfg()
def rhs(dth,xp,Vdc,xiv,omg,p):
    idr=p.kp_v*(p.Vdc_ref-Vdc)+p.ki_v*xiv; iqr=p.iq_ref
    vgd=p.Vg*math.cos(dth)-p.Xg*iqr; vgq=-p.Vg*math.sin(dth)+p.Xg*idr
    Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
    return (p.omega0-omg+p.kp_pll*vgq+p.ki_pll*xp, vgq,
            (p.idc_src+1.5*(vgd*idr+vgq*iqr)/Vs)/p.Cdc, p.Vdc_ref-Vdc, -(omg-p.omega0)/p.tau_g)
# 校验 scalar rhs == 模型 _drift_pu
p=make_p(idc_src=1.0,iq_ref=0.0,Vg=1.0,Xg=0.1,sigma_ou=0.0)
eq=stable_eq(p,cfg); s0=eq.copy(); s0[0]+=1e-3
a=np.array(rhs(*s0,p)); b=_drift_pu(s0,p)
print(f"[校验] scalar rhs vs 模型 _drift_pu 最大差={np.max(np.abs(a-b)):.2e}  (应≈0)")

def td(P,Q,V,Xg,T,dt,pert=1e-5,skip=1.5):
    p=make_p(idc_src=P,iq_ref=Q,Vg=V,Xg=Xg,sigma_ou=0.0)
    eq=stable_eq(p,cfg)
    if eq is None: return None
    d0=eq[0]; d,xp,Vdc,xiv,omg=eq[0]+pert,eq[1],eq[2],eq[3],eq[4]
    n=int(T/dt); tr=np.empty(n)
    for k in range(n):
        k1=rhs(d,xp,Vdc,xiv,omg,p)
        k2=rhs(d+.5*dt*k1[0],xp+.5*dt*k1[1],Vdc+.5*dt*k1[2],xiv+.5*dt*k1[3],omg+.5*dt*k1[4],p)
        k3=rhs(d+.5*dt*k2[0],xp+.5*dt*k2[1],Vdc+.5*dt*k2[2],xiv+.5*dt*k2[3],omg+.5*dt*k2[4],p)
        k4=rhs(d+dt*k3[0],xp+dt*k3[1],Vdc+dt*k3[2],xiv+dt*k3[3],omg+dt*k3[4],p)
        d+=dt/6*(k1[0]+2*k2[0]+2*k3[0]+k4[0]); xp+=dt/6*(k1[1]+2*k2[1]+2*k3[1]+k4[1])
        Vdc+=dt/6*(k1[2]+2*k2[2]+2*k3[2]+k4[2]); xiv+=dt/6*(k1[3]+2*k2[3]+2*k3[3]+k4[3])
        omg+=dt/6*(k1[4]+2*k2[4]+2*k3[4]+k4[4]); tr[k]=d-d0
    i0=int(skip/dt); sig=tr[i0:]; t=np.arange(len(sig))*dt
    an=hilbert(sig); env=np.abs(an); m=len(env); a_,b_=int(.06*m),int(.94*m)
    rate=np.polyfit(t[a_:b_],np.log(env[a_:b_]),1)[0]
    freq=np.polyfit(t[a_:b_],np.unwrap(np.angle(an))[a_:b_],1)[0]/(2*np.pi)
    return rate,freq

def sweep(Xg,Ps,T,dt):
    print(f"\n=== 细扫 P 穿 Hopf @ Xg={Xg}（Q=0,V=1，T={T}s,dt={dt}）===")
    print(f"  {'P':>6}{'Reλ(eig)':>11}{'rate(TD)':>11}{'|Δrate|':>9}{'f_H':>8}{'f(TD)':>8}{'|Δf|':>8}{'  判定':>8}")
    re=[];rt=[]
    for P in Ps:
        A=A_of(P,0.0,1.0,Xg); lam=critical_mode(A); fe=abs(lam.imag)/2/np.pi
        r=td(P,0.0,1.0,Xg,T,dt); 
        if r is None: continue
        rate,ft=r; re.append(lam.real); rt.append(rate)
        vd='不稳' if lam.real>0 else '稳'
        print(f"  {P:>6.3f}{lam.real:>11.4f}{rate:>11.4f}{abs(lam.real-rate):>9.1e}{fe:>8.3f}{ft:>8.3f}{abs(fe-ft):>8.1e}   {vd}")
    re=np.array(re);rt=np.array(rt)
    def z(x,y):
        for i in range(len(y)-1):
            if y[i]*y[i+1]<0: return x[i]-y[i]*(x[i+1]-x[i])/(y[i+1]-y[i])
    print(f"  → Hopf: eig 插值 P={z(np.array(Ps[:len(re)]),re):.4f}, 时域插值 P={z(np.array(Ps[:len(rt)]),rt):.4f}; max|Δrate|={np.max(np.abs(re-rt)):.1e}")

sweep(0.1, np.round(np.arange(1.44,1.561,0.01),3), 8.0, 1e-4)
sweep(1.5, np.round(np.arange(0.46,0.541,0.005),3), 12.0, 2e-4)
