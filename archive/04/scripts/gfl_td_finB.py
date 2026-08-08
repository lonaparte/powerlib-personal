import numpy as np, math
from scipy.signal import hilbert
from gfl_operating_point_stability_sim.system import make_p, make_cfg, stable_eq
from gfl_operating_point_stability_sim.analysis import A_of, critical_mode, sensitivity
cfg=make_cfg()
def rhs(dth,xp,Vdc,xiv,omg,p):
    idr=p.kp_v*(p.Vdc_ref-Vdc)+p.ki_v*xiv; iqr=p.iq_ref
    vgd=p.Vg*math.cos(dth)-p.Xg*iqr; vgq=-p.Vg*math.sin(dth)+p.Xg*idr
    Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
    return (p.omega0-omg+p.kp_pll*vgq+p.ki_pll*xp, vgq,
            (p.idc_src+1.5*(vgd*idr+vgq*iqr)/Vs)/p.Cdc, p.Vdc_ref-Vdc, -(omg-p.omega0)/p.tau_g)
def td(P,Q,V,Xg,T=8.0,dt=1e-4,pert=1e-6,skip=1.5):
    p=make_p(idc_src=P,iq_ref=Q,Vg=V,Xg=Xg,sigma_ou=0.0); eq=stable_eq(p,cfg)
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

def sweep(Xg,Ps,T,dt,label):
    print(f"\n=== {label}：细扫 P 穿 Hopf @ Xg={Xg}（Q=0,V=1，T={T}s,dt={dt}）===")
    print(f"  {'P':>7}{'Reλ(eig)':>11}{'rate(TD)':>11}{'|Δrate|':>9}{'f_H':>8}{'f(TD)':>8}{'|Δf|':>8}")
    re=[];rt=[];Pv=[]
    for P in Ps:
        A=A_of(P,0.0,1.0,Xg)
        if A is None: print(f"  {P:>7.4f}   —（过 SN，无平衡）"); continue
        lam=critical_mode(A); fe=abs(lam.imag)/2/np.pi
        r=td(P,0.0,1.0,Xg,T,dt)
        if r is None: continue
        rate,ft=r; re.append(lam.real);rt.append(rate);Pv.append(P)
        print(f"  {P:>7.4f}{lam.real:>11.5f}{rate:>11.5f}{abs(lam.real-rate):>9.1e}{fe:>8.3f}{ft:>8.3f}{abs(fe-ft):>8.1e}")
    re,rt,Pv=np.array(re),np.array(rt),np.array(Pv)
    def z(x,y):
        for i in range(len(y)-1):
            if y[i]*y[i+1]<0: return x[i]-y[i]*(x[i+1]-x[i])/(y[i+1]-y[i])
    ze,zt=z(Pv,re),z(Pv,rt)
    print(f"  → Hopf 交叉：eig 插值 P={ze:.4f}, 时域插值 P={zt:.4f}, 差={abs(ze-zt):.1e}; max|Δrate|={np.max(np.abs(re-rt)):.1e}")

sweep(0.1, np.round(np.arange(1.478,1.5121,0.002),4), 8.0, 1e-4, "Xg=0.1 强网")
sweep(1.5, np.round(np.arange(0.4972,0.49901,0.0002),4), 16.0, 2e-4, "Xg=1.5 弱网(近 SN，步长 2e-4)")

# ---------- Part B：强网灵敏度排序（V 主导/Q≈0）时域验证 ----------
print("\n=== Part B：强网灵敏度排序时域验证 @ Xg=0.1, 中心(P=1.49,Q=0,V=1) ===")
Xg=0.1; P0,Q0,V0=1.49,0.0,1.0
s_eig=sensitivity(P0,Q0,V0,Xg)
hs={'P':0.002,'Q':0.05,'V':0.002}
print(f"  {'θ':>3}{'dRe/dθ(eig灵敏度)':>18}{'d(rate)/dθ(时域中心差分)':>24}{'  相对差':>9}")
td_slopes={}
for th,h in hs.items():
    kw=dict(P=P0,Q=Q0,V=V0); kp=dict(kw); kp[th]+=h; km=dict(kw); km[th]-=h
    rp=td(kp['P'],kp['Q'],kp['V'],Xg); rm=td(km['P'],km['Q'],km['V'],Xg)
    slope=(rp[0]-rm[0])/(2*h); td_slopes[th]=slope
    print(f"  {th:>3}{s_eig[th]:>18.3f}{slope:>24.3f}{abs(slope-s_eig[th])/max(1,abs(s_eig[th])):>9.1e}")
ne=np.array([abs(s_eig['P']),abs(s_eig['Q']),abs(s_eig['V'])]); ne/=ne[0]
nt=np.array([abs(td_slopes['P']),abs(td_slopes['Q']),abs(td_slopes['V'])]); nt/=nt[0]
print(f"  排序 |P:Q:V|  eig灵敏度 = {ne[0]:.2f}:{ne[1]:.2f}:{ne[2]:.2f}   时域 = {nt[0]:.2f}:{nt[1]:.2f}:{nt[2]:.2f}")
print(f"  → V 主导({nt[2]:.2f}×P)、Q≈0({nt[1]:.2f})：时域独立复现强网排序")
