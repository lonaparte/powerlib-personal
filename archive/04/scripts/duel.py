import numpy as np, math
from scipy.optimize import brentq
from gfl_operating_point_stability_sim.analysis import (A_of, critical_mode,
    sensitivity, find_hopf, saddle_node, equilibrium_angle)
# ---------------- GFM (minimal VSM) ----------------
Enom=1.0; M,D,WC=0.02,0.05,2*np.pi*31.0
def E_of(d,V,Xg,mq,Q):
    a=mq/Xg;b=1-mq*V*math.cos(d)/Xg;c=-(Enom+mq*Q)
    return (-b+math.sqrt(b*b-4*a*c))/(2*a)
def Pcurve(d,V,Xg,mq,Q): return E_of(d,V,Xg,mq,Q)*V/Xg*math.sin(d)
def fold(V,Xg,mq,Q):
    dl=np.linspace(0.01,np.pi/2-1e-4,4000);Pr=[Pcurve(x,V,Xg,mq,Q) for x in dl]
    i=int(np.argmax(Pr));return dl[i],Pr[i]
def gfm_eq(P,Q,V,Xg,mq):
    df,Pm=fold(V,Xg,mq,Q)
    if P>=Pm:return None
    d=brentq(lambda x:Pcurve(x,V,Xg,mq,Q)-P,1e-4,df)
    E=E_of(d,V,Xg,mq,Q);Qf=(E*E-E*V*math.cos(d))/Xg
    return np.array([d,0.0,P,Qf])
def gfm_rhs(s,P,Q,V,Xg,mq,Dv=None):
    d,om,Pf,Qf=s;E=Enom-mq*(Qf-Q);Dv=D if Dv is None else Dv
    Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
    return np.array([om,(P-Pf-Dv*om)/M,WC*(Pe-Pf),WC*(Qe-Qf)])
def gfm_eigs(P,Q,V,Xg,mq,Dv=None,h=1e-7):
    st=gfm_eq(P,Q,V,Xg,mq)
    if st is None:return None
    A=np.zeros((4,4))
    for j in range(4):
        sp=st.copy();sp[j]+=h;sm=st.copy();sm[j]-=h
        A[:,j]=(gfm_rhs(sp,P,Q,V,Xg,mq,Dv)-gfm_rhs(sm,P,Q,V,Xg,mq,Dv))/(2*h)
    return np.linalg.eigvals(A)
def gfm_crit(P,Q,V,Xg,mq,Dv=None):
    ev=gfm_eigs(P,Q,V,Xg,mq,Dv)
    if ev is None: return None
    cx=[e for e in ev if abs(e.imag)>1e-7]
    return max(cx,key=lambda z:z.real) if cx else None
print("== E1. GFM 沿 P 到折叠（Xg=0.1, mq=0.1, Q=0, V=1；折叠 P=%.3f）=="%fold(1,0.1,0.1,0)[1])
print(f"{'P':>6}{'Re_cx':>9}{'f[Hz]':>7}{'maxRe_real':>11}")
for P in [0.5,0.9,0.955,2.0,4.0,6.0,6.5,6.75,6.80,6.817]:
    ev=gfm_eigs(P,0,1,0.1,0.1)
    if ev is None: print(f"{P:>6.3f}  过折叠"); continue
    cx=[e for e in ev if abs(e.imag)>1e-7]; rl=[e.real for e in ev if abs(e.imag)<=1e-7]
    c=max(cx,key=lambda z:z.real) if cx else None
    print(f"{P:>6.3f}{(c.real if c else float('nan')):>9.4f}{(abs(c.imag)/2/np.pi if c else 0):>7.2f}{(max(rl) if rl else float('nan')):>11.4f}")
print("\n== E2. GFL 对照：Xg=1, Q=0, V=1，Hopf=0.7424, SN=0.75 ==")
for P in [0.70,0.7424,0.746,0.7495]:
    lam=critical_mode(A_of(P,0,1,1.0))
    print(f"  P={P}: Re={lam.real:+.3f}, f={abs(lam.imag)/2/np.pi:.2f}Hz")
print("\n== E3. V 的双重作用 ==")
print("GFM (P=1.3, Xg=0.1, mq=0.1): V → Re_cx / 折叠裕度P_fold")
for V in [0.7,0.85,1.0,1.15]:
    c=gfm_crit(1.3,0,V,0.1,0.1); _,Pm=fold(V,0.1,0.1,0)
    print(f"  V={V}: Re={c.real:+.4f}  P_fold={Pm:.2f}")
print("GFL (P=0.5, Xg=1.0): V → Re_cx / P_SN=3V²/4")
for V in [0.85,1.0,1.15]:
    lam=critical_mode(A_of(0.5,0,V,1.0))
    print(f"  V={V}: Re={lam.real:+.4f}  P_SN={0.75*V*V:.3f}")
print("\n== E4. Q 的双重作用 ==")
print("GFM: Qref → Re_cx / P_fold  (P=1.3,Xg=0.1,mq=0.1)")
for Q in [-0.3,0.0,0.3]:
    c=gfm_crit(1.3,Q,1.0,0.1,0.1); _,Pm=fold(1.0,0.1,0.1,Q)
    print(f"  Qref={Q:+.1f}: Re={c.real:+.4f}  P_fold={Pm:.2f}")
print("GFL: Q → Re_cx / 有效SN（最大可解P）  (P=0.5,Xg=1.0)")
for Q in [-0.2,0.0,0.2]:
    lam=critical_mode(A_of(0.5,Q,1.0,1.0))
    Pmax=0.3
    for Pt in np.linspace(0.3,1.3,500):
        if equilibrium_angle(Pt,Q,1.0,1.0) is None: break
        Pmax=Pt
    print(f"  Q={Q:+.1f}: Re={lam.real:+.4f}  P_max(eq)={Pmax:.3f}")
print("\n== E5. 阻尼比 ζ 随 V ==")
for V in [0.85,1.0,1.15]:
    lg=critical_mode(A_of(0.5,0,V,1.0)); zg=-lg.real/abs(lg)
    cm=gfm_crit(1.3,0,V,0.1,0.1); zm=-cm.real/abs(cm)
    print(f"  V={V}: GFL ζ={zg:+.4f}   GFM ζ={zm:+.5f}")
print("\n== E6. GFM dRe/dQref 符号遍历 + mq=0 ==")
h=1e-5
for Xg,mq in [(0.1,0.05),(0.1,0.2),(0.3,0.1),(0.5,0.1),(0.1,0.0)]:
    P=1.0 if Xg>0.15 else 1.3
    cp=gfm_crit(P,h,1.0,Xg,mq);cm_=gfm_crit(P,-h,1.0,Xg,mq)
    print(f"  Xg={Xg},mq={mq}: dRe/dQref={(cp.real-cm_.real)/(2*h):+.4f}")
print("\n== E7. 各自 Hopf 处 |dRe/dP| ==")
s=sensitivity(0.7424*0.999,0.0,1.0,1.0)
c1=gfm_crit(0.975,0,1,0.1,0.1);c2=gfm_crit(0.935,0,1,0.1,0.1)
print(f"  GFL @P_hopf(Xg=1): {s['P']:.0f}    GFM @P_hopf: {(c1.real-c2.real)/0.04:+.4f}")
print("\n== E8. 越过 Hopf 后的时域归宿 ==")
from gfl_operating_point_stability_sim.system import make_p, make_cfg, stable_eq
cfg=make_cfg()
def gfl_run(P,T=25.0,dt=1e-4,kick=1e-4):
    p=make_p(idc_src=P,iq_ref=0.0,Vg=1.0,Xg=1.0,sigma_ou=0.0);eq=stable_eq(p,cfg)
    s=eq.copy();s[0]+=kick;mx=0
    def f(ss):
        dth,xp,Vdc,xiv,omg=ss
        idr=p.kp_v*(p.Vdc_ref-Vdc)+p.ki_v*xiv
        vgd=p.Vg*math.cos(dth);vgq=-p.Vg*math.sin(dth)+p.Xg*idr
        Vs=Vdc if abs(Vdc)>1e-6 else 1e-6
        return np.array([p.omega0-omg+p.kp_pll*vgq+p.ki_pll*xp,vgq,
            (p.idc_src+1.5*vgd*idr/Vs)/p.Cdc,p.Vdc_ref-Vdc,-(omg-p.omega0)/p.tau_g])
    for k in range(int(T/dt)):
        k1=f(s);k2=f(s+.5*dt*k1);k3=f(s+.5*dt*k2);k4=f(s+dt*k3);s=s+dt/6*(k1+2*k2+2*k3+k4)
        mx=max(mx,abs(s[0]-eq[0]))
        if mx>50: return mx,(k+1)*dt
    return mx,T
mx,tesc=gfl_run(0.746)
print(f"  GFL P=0.746 (Re=+1.69): max|Δθ|={mx:.1f} rad @t={tesc:.1f}s → {'失步(无界)' if mx>3 else '有界'}")
def gfm_run(P,Dv,T=60.0,dt=2e-4,kick=1e-3):
    st0=gfm_eq(P,0,1.0,0.1,0.1);s=st0.copy();s[0]+=kick;tail=[]
    for k in range(int(T/dt)):
        k1=gfm_rhs(s,P,0,1.0,0.1,0.1,Dv);k2=gfm_rhs(s+.5*dt*k1,P,0,1.0,0.1,0.1,Dv)
        k3=gfm_rhs(s+.5*dt*k2,P,0,1.0,0.1,0.1,Dv);k4=gfm_rhs(s+dt*k3,P,0,1.0,0.1,0.1,Dv)
        s=s+dt/6*(k1+2*k2+2*k3+k4)
        if not np.isfinite(s[0]) or abs(s[0]-st0[0])>6: return None,(k+1)*dt
        if k>int((T-8)/dt): tail.append(abs(s[0]-st0[0]))
    return max(tail),T
c=gfm_crit(0.5,0,1,0.1,0.1,Dv=0.02)
amp,_=gfm_run(0.5,0.02)
print(f"  GFM P=0.5, D=0.02 (Re={c.real:+.2f}): 稳态幅值={math.degrees(amp) if amp else float('nan'):.1f}° → {'有界极限环' if amp else '失步'}")
print("\n== E9. 频率随 P、V 的走向 ==")
fP_gfl=[abs(critical_mode(A_of(P,0,1,1.0)).imag)/2/np.pi for P in [0.5,0.65,0.74]]
fV_gfl=[abs(critical_mode(A_of(0.5,0,V,1.0)).imag)/2/np.pi for V in [0.85,1.0,1.15]]
fP_gfm=[abs(gfm_crit(P,0,1,0.1,0.1).imag)/2/np.pi for P in [0.5,3.0,6.0]]
fV_gfm=[abs(gfm_crit(1.3,0,V,0.1,0.1).imag)/2/np.pi for V in [0.7,1.0,1.15]]
print(f"  GFL f(P↑)={[f'{x:.2f}' for x in fP_gfl]}  f(V↑)={[f'{x:.2f}' for x in fV_gfl]}")
print(f"  GFM f(P↑)={[f'{x:.2f}' for x in fP_gfm]}  f(V↑)={[f'{x:.2f}' for x in fV_gfm]}")
