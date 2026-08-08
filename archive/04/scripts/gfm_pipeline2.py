import numpy as np, sympy as sp
from scipy.optimize import fsolve
delta,Pf,Qf = sp.symbols('delta Pf Qf', real=True)
Pref,Qref,V,Xg,mp,mq,wc,Enom = sp.symbols('Pref Qref V Xg mp mq wc Enom', positive=True)
E=Enom-mq*(Qf-Qref); P=E*V/Xg*sp.sin(delta); Q=(E**2-E*V*sp.cos(delta))/Xg
f=sp.Matrix([-mp*(Pf-Pref), wc*(P-Pf), wc*(Q-Qf)]); x=sp.Matrix([delta,Pf,Qf]); J=f.jacobian(x)
args=(delta,Pf,Qf,Pref,Qref,V,Xg,mp,mq,wc,Enom)
f_l=sp.lambdify(args,f,'numpy'); J_l=sp.lambdify(args,J,'numpy')
# 灵敏度用的符号导数
th=sp.symbols('th'); 
dJ_dx=[sp.lambdify(args,J.diff(v),'numpy') for v in (delta,Pf,Qf)]     # ∂A/∂x_k
def make(pv): return sp.lambdify(args,f.diff(pv),'numpy'), sp.lambdify(args,J.diff(pv),'numpy')
dfdXg,dJdXg = make(Xg); dfdPref,dJdPref = make(Pref)
pars=dict(Enom=1.0,V=1.0,mp=0.1,mq=0.1,wc=10.0,Qref=0.0)
def A(st,d): return np.array(J_l(st[0],st[1],st[2],d['Pref'],d['Qref'],d['V'],d['Xg'],d['mp'],d['mq'],d['wc'],d['Enom']),float)
def rhs(st,d): return np.array(f_l(st[0],st[1],st[2],d['Pref'],d['Qref'],d['V'],d['Xg'],d['mp'],d['mq'],d['wc'],d['Enom']),float).ravel()
def equil(d):
    def res(z):
        st=[z[0],d['Pref'],z[1]]; r=rhs(st,d); return [r[1],r[2]]
    for dl0 in (0.1,0.3,0.6,0.9,1.2,1.4):
        z,info,ier,msg=fsolve(res,[dl0,0.0],full_output=True)
        st=np.array([z[0],d['Pref'],z[1]])
        if ier==1 and np.max(np.abs(rhs(st,d)))<1e-9 and 0<z[0]<np.pi/2: return st
    return None
def critc(A_):
    ev=np.linalg.eigvals(A_); cx=[e for e in ev if abs(e.imag)>1e-6]
    return max(cx,key=lambda z:z.real) if cx else None

# ---- SN: 推 Pref 到折叠 ----
print("[SN] Xg=0.5，Pref 上行到折叠：")
last=None
for Pv in np.linspace(0.5,2.05,156):
    d=dict(pars,Pref=Pv,Xg=0.5); st=equil(d)
    if st is None:
        print(f"   Pref={Pv:.3f} 平衡消失→SN；最后可解 Pref={last:.3f}, δ*={dll:.1f}°  (理论 Pmax=E·V/Xg=2.0, δ*→90°)"); break
    last=Pv; dll=np.degrees(st[0])

# ---- Hopf 搜索：GFM 在强网/高带宽失稳，扫 (wc, Xg) ----
print("\n[Hopf] 扫 (wc, Xg) 找复对 Re 过 0（Pref=0.5）：")
found=[]
for wcv in [10,30,60,120,250,500,1000]:
    row=[]
    for Xgv in [0.05,0.1,0.2,0.4,0.8]:
        d=dict(pars,wc=wcv,Xg=Xgv,Pref=0.5); st=equil(d)
        if st is None: row.append("  no-eq"); continue
        lam=critc(A(st,d))
        if lam is None: row.append("  real "); continue
        row.append(f"{lam.real:+7.3f}")
        if lam.real>0: found.append((wcv,Xgv,lam))
    print(f"   wc={wcv:5.0f} | Xg: "+" ".join(f"{v}:{r}" for v,r in zip([0.05,0.1,0.2,0.4,0.8],row)))
if found:
    print(f"   → 存在不稳定复模态（Hopf 已被跨越），例: wc={found[0][0]}, Xg={found[0][1]}, f_H={abs(found[0][2].imag)/2/np.pi:.1f}Hz")
else:
    print("   → 扫描范围内复对 Re 恒<0：此最小下垂模型过阻尼，无 Hopf（需虚拟惯量/内环才有）。方法照样能判——判据同 GFL。")

# ---- 两通道灵敏度 vs 暴力总差分（验证 IFT 分解在新模型上成立）----
print("\n[灵敏度] 两通道 dλ=w(∂A/∂θ)v  vs  暴力总差分 dRe(λ)/dθ：")
d=dict(pars,Pref=0.8,Xg=0.5); st=equil(d)
A0=A(st,d); ev,Vec=np.linalg.eig(A0); W=np.linalg.inv(Vec)
i=int(np.argmax(ev.real)); v=Vec[:,i]; w=W[i,:]; v=v/(w@v)  # 归一 w v=1
argv=(st[0],st[1],st[2],d['Pref'],d['Qref'],d['V'],d['Xg'],d['mp'],d['mq'],d['wc'],d['Enom'])
def two_channel(dfdp,dJdp):
    dfth=np.array(dfdp(*argv),float).ravel()
    dxdth=-np.linalg.solve(A0,dfth)                       # ∂x*/∂θ = -A^{-1} ∂f/∂θ
    dA=np.array(dJdp(*argv),float)                        # ∂A/∂θ|_expl
    for k in range(3): dA=dA+np.array(dJ_dx[k](*argv),float)*dxdth[k]  # + Σ ∂A/∂x_k · dx_k
    return float(np.real(w@dA@v))
def brute(param):
    h=1e-5; d1=dict(d); d1[param]+=h; d2=dict(d); d2[param]-=h
    l1=ev_c(equil(d1),d1); l2=ev_c(equil(d2),d2); return (l1-l2)/(2*h)
def ev_c(st,d):
    e=np.linalg.eigvals(A(st,d)); return max(e.real)
for name,dfdp,dJdp in [("Xg",dfdXg,dJdXg),("Pref",dfdPref,dJdPref)]:
    tc=two_channel(dfdp,dJdp); bf=brute(name)
    print(f"   dRe(λ)/d{name:5s}: 两通道={tc:+9.4f}   暴力总差分={bf:+9.4f}   相对差={abs(tc-bf)/max(1,abs(bf)):.1e}")
