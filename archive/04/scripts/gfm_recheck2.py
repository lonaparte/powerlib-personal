import numpy as np, sympy as sp
from scipy.optimize import brentq
def E_of(delta,V,Xg,mq,Enom=1.0,Qref=0.0):
    a=mq/Xg; b=1-mq*V*np.cos(delta)/Xg; c=-(Enom+mq*Qref)
    if abs(a)<1e-14: return Enom
    return (-b+np.sqrt(b*b-4*a*c))/(2*a)
def Pref_of(d,V,Xg,mq): E=E_of(d,V,Xg,mq); return E*V/Xg*np.sin(d)
def dfold(V,Xg,mq):
    dl=np.linspace(0.01,np.pi/2-1e-4,8000); Pr=[Pref_of(d,V,Xg,mq) for d in dl]
    i=int(np.argmax(Pr)); return dl[i],Pr[i]
def delta_star(Pref,V,Xg,mq):     # 稳定支：Pref(δ)=Pref 在 [0,δ_fold] 的根
    df,Pf=dfold(V,Xg,mq)
    if Pref>=Pf: return None
    return brentq(lambda d:Pref_of(d,V,Xg,mq)-Pref,1e-4,df)

# ---- 符号 Jacobian：droop 3态 与 VSM 4态 ----
d_,om,Pf_,Qf_=sp.symbols('d om Pf Qf',real=True)
Pr,Qr,V,Xg,mp,mq,wc,M,D,En=sp.symbols('Pr Qr V Xg mp mq wc M D En',positive=True)
E=En-mq*(Qf_-Qr); P=E*V/Xg*sp.sin(d_); Q=(E**2-E*V*sp.cos(d_))/Xg
Jd=sp.Matrix([-mp*(Pf_-Pr),wc*(P-Pf_),wc*(Q-Qf_)]).jacobian([d_,Pf_,Qf_])
Jv=sp.Matrix([om,(Pr-Pf_-D*om)/M,wc*(P-Pf_),wc*(Q-Qf_)]).jacobian([d_,om,Pf_,Qf_])
Jd_l=sp.lambdify((d_,Pf_,Qf_,Pr,Qr,V,Xg,mp,mq,wc,En),Jd,'numpy')
Jv_l=sp.lambdify((d_,om,Pf_,Qf_,Pr,Qr,V,Xg,M,D,mq,wc,En),Jv,'numpy')
def eqpoint(Pref,V,Xg,mq):
    ds=delta_star(Pref,V,Xg,mq)
    if ds is None: return None
    E=E_of(ds,V,Xg,mq); Qf=(E**2-E*V*np.cos(ds))/Xg
    return ds,E,Qf
def maxRe_complex(ev):
    cx=[e for e in ev if abs(e.imag)>1e-7]
    return max((e.real for e in cx),default=None)

print("=== 复查B：最小下垂(3态)会不会 Hopf？广扫 4×4×3×4×4=768 例 ===")
gmax=-9; where=None; ncomplex=0; nunstable=0; N=0
for Xg in [0.1,0.3,0.5,1.0]:
  for mp in [0.02,0.1,0.5,2.0]:
    for mq in [0.02,0.1,0.3]:
      for wc in [5,20,100,500]:
        for fr in [0.3,0.6,0.9,0.99]:
          df,Pfold=dfold(1.0,Xg,mq); Pref=fr*Pfold
          ep=eqpoint(Pref,1.0,Xg,mq)
          if ep is None: continue
          ds,Ev,Qf=ep; N+=1
          A=np.array(Jd_l(ds,Pref,Qf,Pref,0.0,1.0,Xg,mp,mq,wc,1.0),float)
          ev=np.linalg.eigvals(A); mr=maxRe_complex(ev)
          if mr is not None:
            ncomplex+=1
            if mr>=0: nunstable+=1
            if mr>gmax: gmax=mr; where=(Xg,mp,mq,wc,fr)
print(f"  跑了 {N} 个可解工作点；有复模态的 {ncomplex} 个；复模态 Re≥0(不稳/Hopf) 的 {nunstable} 个")
print(f"  全局最大 复模态 Re = {gmax:+.4f}  @ (Xg,mp,mq,wc,frac)={where}")
print(f"  → 结论：{'仍全部<0，最小下垂确无 Hopf（我之前结论成立）' if nunstable==0 else '发现 Hopf！之前结论错'}")

print("\n=== 复查C：VSM(4态) Hopf 数值 vs 闭式 ωc_crit=K/D-D/M ===")
print(f"{'Xg':>5}{'M':>6}{'D':>6}{'Pref':>6}{'K=∂P/∂δ':>9}{'fc_num[Hz]':>11}{'fc_closed[Hz]':>14}{'差%':>7}")
for (Xg,M,D,Pref) in [(0.1,0.02,0.01,0.5),(0.1,0.05,0.02,0.5),(0.3,0.02,0.02,0.5),
                       (0.1,0.02,0.005,0.8),(0.5,0.03,0.05,0.6),(0.1,0.1,0.05,0.5)]:
    mq=0.1
    ep=eqpoint(Pref,1.0,Xg,mq)
    if ep is None: print(f"{Xg:>5}{M:>6}{D:>6}{Pref:>6}  no-eq"); continue
    ds,Ev,Qf=ep; K=Ev*1.0/Xg*np.cos(ds)
    def reC(fc):
        A=np.array(Jv_l(ds,0.0,Pref,Qf,Pref,0.0,1.0,Xg,M,D,mq,2*np.pi*fc,1.0),float)
        return maxRe_complex(np.linalg.eigvals(A))
    # 扫 fc 找过零
    fcs=np.linspace(2,400,4000); prev=None; hit=None
    for fc in fcs:
        r=reC(fc)
        if r is None: continue
        if prev is not None and ((prev[1]<0<=r) or (prev[1]>=0>r)):
            hit=brentq(lambda f:reC(f), prev[0], fc); break
        prev=(fc,r)
    fc_closed=(K/D-D/M)/(2*np.pi)
    if hit:
        print(f"{Xg:>5.2f}{M:>6.3f}{D:>6.3f}{Pref:>6.2f}{K:>9.3f}{hit:>11.2f}{fc_closed:>14.2f}{100*abs(hit-fc_closed)/fc_closed:>6.1f}%")
    else:
        print(f"{Xg:>5.2f}{M:>6.3f}{D:>6.3f}{Pref:>6.2f}{K:>9.3f}   无过零(此参数无Hopf)  闭式fc={fc_closed:.1f}")
