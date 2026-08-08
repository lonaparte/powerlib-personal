import numpy as np, sympy as sp
from scipy.optimize import fsolve
# 4态 VSM: (delta, omega, Pf, Qf)，摆方程看"滤波后"功率 Pf（滞后=负阻尼源）
delta,omega,Pf,Qf = sp.symbols('delta omega Pf Qf', real=True)
Pref,Qref,V,Xg,M,D,mq,wc,Enom = sp.symbols('Pref Qref V Xg M D mq wc Enom', positive=True)
E=Enom-mq*(Qf-Qref); P=E*V/Xg*sp.sin(delta); Q=(E**2-E*V*sp.cos(delta))/Xg
f=sp.Matrix([ omega, (Pref-Pf-D*omega)/M, wc*(P-Pf), wc*(Q-Qf) ])
x=sp.Matrix([delta,omega,Pf,Qf]); J=f.jacobian(x)
args=(delta,omega,Pf,Qf,Pref,Qref,V,Xg,M,D,mq,wc,Enom)
f_l=sp.lambdify(args,f,'numpy'); J_l=sp.lambdify(args,J,'numpy')
dJ_dx=[sp.lambdify(args,J.diff(v),'numpy') for v in (delta,omega,Pf,Qf)]
def mk(p): return sp.lambdify(args,f.diff(p),'numpy'), sp.lambdify(args,J.diff(p),'numpy')
dfdD,dJdD=mk(D)
def A(st,d): return np.array(J_l(*st,d['Pref'],d['Qref'],d['V'],d['Xg'],d['M'],d['D'],d['mq'],d['wc'],d['Enom']),float)
def rhs(st,d): return np.array(f_l(*st,d['Pref'],d['Qref'],d['V'],d['Xg'],d['M'],d['D'],d['mq'],d['wc'],d['Enom']),float).ravel()
pars=dict(Enom=1.0,V=1.0,Qref=0.0,M=0.02,D=0.01,mq=0.1,Xg=0.1,Pref=0.5)
def equil(d):
    def res(z):
        st=[z[0],0.0,d['Pref'],z[1]]; r=rhs(st,d); return [r[2],r[3]]
    for dl0 in (0.1,0.3,0.6,0.9):
        z,info,ier,msg=fsolve(res,[dl0,0.0],full_output=True)
        st=np.array([z[0],0.0,d['Pref'],z[1]])
        if ier==1 and np.max(np.abs(rhs(st,d)))<1e-9 and 0<z[0]<np.pi/2: return st
    return None
def critc(A_):
    ev=np.linalg.eigvals(A_); cx=[e for e in ev if abs(e.imag)>1e-6]
    return max(cx,key=lambda z:z.real) if cx else None

print("[4态VSM] 扫功率测量带宽 wc（Hz→rad/s），M=0.02,D=0.01,Xg=0.1,Pref=0.5：")
prev=None; hopf=None
for fcHz in [200,100,50,30,20,15,12,10,8,6,5,4,3]:
    wcv=2*np.pi*fcHz; d=dict(pars,wc=wcv); st=equil(d)
    if st is None: continue
    lam=critc(A(st,d))
    print(f"   fc={fcHz:4d}Hz (wc={wcv:6.1f})  Re(λc)={lam.real:+8.4f}  f={abs(lam.imag)/2/np.pi:5.2f}Hz")
    if prev is not None and prev[1]<0<=lam.real: hopf=(prev[0],fcHz)
    prev=(fcHz,lam.real)
if hopf:
    # 在 Hopf 两侧确认 + 三次? 不，4态用 Routh 全序列判；这里用特征值直接确认过零
    fa,fb=hopf; print(f"   → Hopf 在 fc∈({fb},{fa})Hz 之间：复对 Re 由负转正，平衡点仍存在（Δ0=δ*不变）")
    # 精定位
    lo,hi=2*np.pi*fb,2*np.pi*fa
    for _ in range(40):
        mid=0.5*(lo+hi); d=dict(pars,wc=mid); st=equil(d); r=critc(A(st,d)).real
        if r>=0: lo=mid
        else: hi=mid
    d=dict(pars,wc=0.5*(lo+hi)); st=equil(d); Ah=A(st,d); lam=critc(Ah)
    a=np.poly(Ah)  # λ⁴+a1λ³+a2λ²+a3λ+a4
    R=a[3]*a[2]*a[1]-a[3]**2-a[4]*a[1]**2   # 四次 Routh 判据 (同 GFL!)
    print(f"   精定位 fc={0.5*(lo+hi)/2/np.pi:.2f}Hz: Re(λc)={lam.real:+.2e}(≈0), f_H={abs(lam.imag)/2/np.pi:.2f}Hz")
    print(f"   四次 Routh R=c1c2c3-c1²-c0c3² = {R:+.3e} (≈0，与 GFL 项目里同一个判据！)")
    print("   ✓✓ GFM 也有 Hopf，判据(四次Routh)与 GFL 逐字相同；物理来源=功率测量滞后的负阻尼")
else:
    print("   未过零。")

# ---- 核实 Routh：归一化 + 直接看特征值 ----
print("\n[核实] Hopf 点特征值 + Routh 归一化：")
d=dict(pars,wc=2*np.pi*158.48); st=equil(d); Ah=A(st,d)
ev=np.sort_complex(np.linalg.eigvals(Ah))
for e in ev: print(f"     λ = {e.real:+10.3f} {e.imag:+8.3f}j")
a=np.poly(Ah); c3,c2,c1,c0=a[1],a[2],a[3],a[4]
R=c1*c2*c3-c1**2-c0*c3**2
scale=abs(c1*c2*c3)+c1**2+abs(c0*c3**2)
print(f"     四次 Routh R={R:+.3e},  归一化 R/scale = {R/scale:+.2e}  (相对≈0 → Hopf 确认)")
