import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
from gfl_5d_ou_sim.system import find_eq
cfg=S.make_cfg()
def eig_at(P0,Q0,V0,Xg0,th_guess):
    p=S.make_p(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); e=find_eq(p,th_guess,cfg)
    if e is None or np.max(np.abs(S.drift(e,p,cfg)))>1e-6: return None,th_guess
    A=S.jacobian(e,p,cfg)[:4,:4]; ev=np.linalg.eigvals(A)
    return (ev,e[0]), e[0]

def find_hopf_along(knob, base, Xg0, lo, hi, sndir):
    """bisect where max Re of COMPLEX eigenvalues crosses 0 (Hopf); eq must exist."""
    def maxRe_cplx(val, th):
        kw=dict(base); kw[knob]=val; kw['Xg']=Xg0
        r,th2=eig_at(kw['idc_src'],kw['iq_ref'],kw['Vg'],kw['Xg'],th)
        if r is None: return None,th
        ev,_=r; cx=[e for e in ev if abs(e.imag)>1e-6]
        return (max(e.real for e in cx) if cx else -9), th2
    # continuation guess sweep to find bracket
    th=-0.3; grid=np.linspace(lo,hi,400) if sndir>0 else np.linspace(hi,lo,400)
    prev=None; pv=None; fH=None
    for v in grid:
        m,th=maxRe_cplx(v,th)
        if m is None: break
        if prev is not None and ((prev<0<=m) or (prev>=0>m)):
            # Hopf crossing between pv and v
            kw=dict(base); kw[knob]=v; kw['Xg']=Xg0
            r,_=eig_at(kw['idc_src'],kw['iq_ref'],kw['Vg'],kw['Xg'],th)
            cx=[e for e in r[0] if abs(e.imag)>1e-6]; fH=abs(max(cx,key=lambda z:z.real).imag)/(2*math.pi)
            return 0.5*(pv+v), fH
        prev=m; pv=v
    return None,None

print("Hopf 与 SN 明确分开（P 扫描，V=1, Q=0；SN = 平衡点消失 = 3/(4Xg)）")
print(f"  {'Xg':>5}{'P_Hopf':>9}{'f_H[Hz]':>9}{'P_SN':>8}{'gap(SN-Hopf)':>14}{'  谁先(增P)':>12}")
for Xg0 in [0.1,0.5,1.0,1.5]:
    P_SN=3.0/(4*Xg0)
    PH,fH=find_hopf_along('idc_src', dict(idc_src=0,iq_ref=0.0,Vg=1.0), Xg0, 0.05, P_SN*0.9999, +1)
    if PH is None:
        print(f"  {Xg0:>5.2f}{'—(无Hopf)':>9}{'—':>9}{P_SN:>8.3f}{'—':>14}{'  直接到SN':>12}")
    else:
        print(f"  {Xg0:>5.2f}{PH:>9.4f}{fH:>9.3f}{P_SN:>8.3f}{P_SN-PH:>14.4f}{'  Hopf先':>12}")

print("\nHopf 与 SN（V 扫描，P=0.5, Q=0；SN = V_SN = sqrt(4·P·Xg/3)，减 V 去稳定）")
print(f"  {'Xg':>5}{'V_Hopf':>9}{'f_H[Hz]':>9}{'V_SN':>8}{'gap(Hopf-SN)':>14}")
for Xg0 in [0.1,0.5,1.0,1.5]:
    V_SN=math.sqrt(4*0.5*Xg0/3)
    VH,fH=find_hopf_along('Vg', dict(idc_src=0.5,iq_ref=0.0,Vg=0), Xg0, V_SN*1.0001, 2.5, -1)
    if VH is None:
        print(f"  {Xg0:>5.2f}{'—(无Hopf)':>9}{'—':>9}{V_SN:>8.3f}{'—':>14}")
    else:
        print(f"  {Xg0:>5.2f}{VH:>9.4f}{fH:>9.3f}{V_SN:>8.3f}{VH-V_SN:>14.4f}")
