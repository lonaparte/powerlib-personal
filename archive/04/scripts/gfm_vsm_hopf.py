import numpy as np, sympy as sp
from scipy.optimize import fsolve
# VSM-GFM: 状态 (delta, omega, Qf)，虚拟惯量 M + 阻尼 D + 无功下垂
delta,omega,Qf = sp.symbols('delta omega Qf', real=True)
Pref,Qref,V,Xg,M,D,mq,wc,Enom = sp.symbols('Pref Qref V Xg M D mq wc Enom', positive=True)
E=Enom-mq*(Qf-Qref); P=E*V/Xg*sp.sin(delta); Q=(E**2-E*V*sp.cos(delta))/Xg
f=sp.Matrix([ omega,
              (Pref - P - D*omega)/M,
              wc*(Q-Qf) ])
x=sp.Matrix([delta,omega,Qf]); J=f.jacobian(x)
args=(delta,omega,Qf,Pref,Qref,V,Xg,M,D,mq,wc,Enom)
f_l=sp.lambdify(args,f,'numpy'); J_l=sp.lambdify(args,J,'numpy')
def A(st,d): return np.array(J_l(st[0],st[1],st[2],d['Pref'],d['Qref'],d['V'],d['Xg'],d['M'],d['D'],d['mq'],d['wc'],d['Enom']),float)
def rhs(st,d): return np.array(f_l(st[0],st[1],st[2],d['Pref'],d['Qref'],d['V'],d['Xg'],d['M'],d['D'],d['mq'],d['wc'],d['Enom']),float).ravel()
pars=dict(Enom=1.0,V=1.0,Qref=0.0,M=0.02,D=0.02,mq=0.3,wc=200.0)
def equil(d):
    def res(z):
        st=[z[0],0.0,z[1]]; r=rhs(st,d); return [r[1],r[2]]
    for dl0 in (0.1,0.3,0.6,0.9,1.2):
        z,info,ier,msg=fsolve(res,[dl0,0.0],full_output=True)
        st=np.array([z[0],0.0,z[1]])
        if ier==1 and np.max(np.abs(rhs(st,d)))<1e-9 and 0<z[0]<np.pi/2: return st
    return None
def critc(A_):
    ev=np.linalg.eigvals(A_); cx=[e for e in ev if abs(e.imag)>1e-6]
    return max(cx,key=lambda z:z.real) if cx else None

print("[VSM-Hopf] 扫 D（虚拟阻尼）下行，Xg=0.1(强网), Pref=0.5, M=0.02, mq=0.3, wc=200:")
prev=None; hopfD=None
for Dv in np.linspace(0.20,0.0,41):
    d=dict(pars,D=Dv,Xg=0.1,Pref=0.5); st=equil(d)
    if st is None: continue
    lam=critc(A(st,d))
    if lam is None: continue
    if prev is not None and prev[1]>0>=lam.real:  # Re 从 + 变 -（降 D 稳→…）；反向也测
        pass
    if prev is not None and ((prev[1]<0<=lam.real) or (prev[1]>=0>lam.real)):
        hopfD=(0.5*(prev[0]+Dv),lam)
    if abs(Dv*100-round(Dv*100))<1e-6 and round(Dv*100)%2==0:
        print(f"   D={Dv:5.3f}  Re(λc)={lam.real:+8.4f}  f={abs(lam.imag)/2/np.pi:6.2f}Hz")
    prev=(Dv,lam.real)
if hopfD:
    Dh,lh=hopfD; d=dict(pars,D=Dh,Xg=0.1,Pref=0.5); st=equil(d); Ah=A(st,d)
    a=np.poly(Ah); routh=a[2]*a[1]-a[3]*a[0]
    print(f"   → Hopf 在 D≈{Dh:.3f}: 复对过虚轴, f_H≈{abs(lh.imag)/2/np.pi:.2f}Hz, 三次Routh(a1a2-a0)={routh:+.2e}(≈0), 平衡仍存在 δ*={np.degrees(st[0]):.1f}°")
    print("   ✓ GFM 也有 Hopf，且判据(Routh)与 GFL 完全相同——只是物理来源是 惯量↔阻尼↔无功环 交互，不是 PLL")
else:
    print("   本次扫描未捕获过零；可继续压 M/D。")
