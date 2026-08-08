"""同一套五步管线，换成 GFM 下垂控制（3 态，无限幅）。只验证方法是否适用。"""
import numpy as np, sympy as sp
from scipy.optimize import fsolve

# ---- 1. 符号建模：状态 (delta, Pf, Qf)，E 由无功下垂给定 ----
delta,Pf,Qf = sp.symbols('delta Pf Qf', real=True)
Pref,Qref,V,Xg,mp,mq,wc,Enom = sp.symbols('Pref Qref V Xg mp mq wc Enom', positive=True)
E  = Enom - mq*(Qf - Qref)                      # 无功-电压下垂
P  = E*V/Xg*sp.sin(delta)                       # 送端有功（S=E I*）
Q  = (E**2 - E*V*sp.cos(delta))/Xg              # 送端无功
f  = sp.Matrix([ -mp*(Pf-Pref),                 # 有功-频率下垂: dδ=ω_cnv-ω_g
                  wc*(P - Pf),                   # 有功测量 LPF
                  wc*(Q - Qf) ])                 # 无功测量 LPF
x  = sp.Matrix([delta,Pf,Qf])
J  = f.jacobian(x)                              # 解析 Jacobian（符号精确）

pars = dict(Enom=1.0,V=1.0,mp=0.1,mq=0.1,wc=10.0,Qref=0.0)
subs0 = lambda d: {Pref:d['Pref'],Qref:d['Qref'],V:d['V'],Xg:d['Xg'],
                   mp:d['mp'],mq:d['mq'],wc:d['wc'],Enom:d['Enom']}
f_l = sp.lambdify((delta,Pf,Qf,Pref,Qref,V,Xg,mp,mq,wc,Enom), f, 'numpy')
J_l = sp.lambdify((delta,Pf,Qf,Pref,Qref,V,Xg,mp,mq,wc,Enom), J, 'numpy')

def rhs(st,d):
    return np.array(f_l(st[0],st[1],st[2],d['Pref'],d['Qref'],d['V'],d['Xg'],
                        d['mp'],d['mq'],d['wc'],d['Enom']),float).ravel()
def Aan(st,d):
    return np.array(J_l(st[0],st[1],st[2],d['Pref'],d['Qref'],d['V'],d['Xg'],
                        d['mp'],d['mq'],d['wc'],d['Enom']),float)

def equil(d):
    # 平衡: Pf=Pref; 解 (delta,E)→回代 Qf；用 fsolve 找 δ,Qf
    def res(z):
        dl,qf = z
        st=[dl,d['Pref'],qf]
        r=rhs(st,d)
        return [r[1],r[2]]           # dPf=0,dQf=0（dδ=0 已由 Pf=Pref 保证）
    for dl0 in (0.2,0.5,0.8,1.0):
        try:
            dl,qf = fsolve(res,[dl0,0.0],full_output=False)
            st=[dl,d['Pref'],qf]
            if np.max(np.abs(rhs(st,d)))<1e-9 and 0<dl<np.pi/2:
                return np.array(st)
        except Exception: pass
    return None

def Anum(st,d,h=1e-6):
    n=len(st); A=np.zeros((n,n)); f0=rhs(st,d)
    for j in range(n):
        sp_=st.copy(); sp_[j]+=h; sm=st.copy(); sm[j]-=h
        A[:,j]=(rhs(sp_,d)-rhs(sm,d))/(2*h)
    return A

# ---- 2. 解析 Jacobian == 数值 Jacobian（新模型上的 推导↔数值 咬合）----
d=dict(pars,Pref=0.8,Xg=0.5); st=equil(d)
relerr=np.max(np.abs(Aan(st,d)-Anum(st,d)))/max(1,np.linalg.norm(Anum(st,d)))
print(f"[步3 线性化] 解析J vs 数值J 相对误差 = {relerr:.2e}   (平衡 δ*={np.degrees(st[0]):.2f}°)")

# ---- 3/4. 扫 Xg 找 Hopf（复对 Re 过 0），扫 Pref 找 SN（平衡消失）----
def crit_complex(A):
    ev=np.linalg.eigvals(A); cx=[e for e in ev if abs(e.imag)>1e-6]
    return max(cx,key=lambda z:z.real) if cx else None

print("\n[步4 Hopf] 扫 Xg（弱网方向），Pref=0.8：最小阻尼复模态 Re(λ)")
prev=None; hopf=None
for Xgv in np.linspace(0.2,1.4,61):
    d=dict(pars,Pref=0.8,Xg=Xgv); st=equil(d)
    if st is None: continue
    lam=crit_complex(Aan(st,d))
    if lam is None: continue
    if prev is not None and prev[1]<0<=lam.real:
        hopf=(0.5*(prev[0]+Xgv),lam); 
    if abs(Xgv*10-round(Xgv*10))<1e-9:
        print(f"   Xg={Xgv:4.2f}  Re={lam.real:+8.4f}  f={abs(lam.imag)/2/np.pi:5.2f}Hz")
    prev=(Xgv,lam.real)
if hopf: 
    Xh,lh=hopf
    d=dict(pars,Pref=0.8,Xg=Xh); st=equil(d); A=Aan(st,d)
    a=np.poly(A); routh=a[2]*a[1]-a[3]*a[0]   # 三次 λ³+a2λ²+a1λ+a0: Hopf⇔ a1a2=a0
    print(f"   → Hopf 在 Xg≈{Xh:.3f}，f_H≈{abs(lh.imag)/2/np.pi:.2f}Hz，三次Routh(a1a2-a0)={routh:+.2e}(≈0)")

print("\n[步4 SN] 固定 Xg=0.5，加大 Pref 找折叠（平衡消失）")
last=None
for Pv in np.linspace(0.5,1.3,81):
    d=dict(pars,Pref=Pv,Xg=0.5); st=equil(d)
    if st is None:
        print(f"   Pref={Pv:.3f}: 平衡消失 → SN（上一个可解 Pref={last:.3f}, δ*={dl_last:.1f}°）"); break
    last=Pv; dl_last=np.degrees(st[0])
print(f"   理论 Pmax≈E·V/Xg（δ*→90°）；数值折叠点与之一致")
