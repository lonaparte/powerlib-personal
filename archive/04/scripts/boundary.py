import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, sympy as sp, warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); CDC=0.01; KPP,KIP,KPV,KIV=50.0,1000.0,1.0,50.0
th,Xg,Q,Vg,P=sp.symbols('theta X_g Q V_g P',real=True)
a=Vg*sp.cos(th); b=Vg*sp.sin(th); vgd0=a-Xg*Q; id0=b/Xg
J=sp.Matrix([[-KPP*a,KIP,-KPP*Xg*KPV,KPP*Xg*KIV],[-a,0,-Xg*KPV,Xg*KIV],
 [sp.Rational(3,2)/CDC*(-b*id0-Q*a),0,sp.Rational(3,2)/CDC*(-(vgd0*KPV+Q*Xg*KPV+vgd0*id0)),
  sp.Rational(3,2)/CDC*(vgd0*KIV+Q*Xg*KIV)],[0,0,-1,0]])
E=P+sp.Rational(3,2)*vgd0*id0
Jf=sp.lambdify((th,Xg,Q,Vg),J,'numpy')
dJth=sp.lambdify((th,Xg,Q,Vg),sp.diff(J,th),'numpy')
dJV =sp.lambdify((th,Xg,Q,Vg),sp.diff(J,Vg),'numpy')
dJX =sp.lambdify((th,Xg,Q,Vg),sp.diff(J,Xg),'numpy')
dJQ =sp.lambdify((th,Xg,Q,Vg),sp.diff(J,Q),'numpy')
Eth=sp.lambdify((th,Xg,Q,Vg,P),sp.diff(E,th),'numpy')
EP =sp.lambdify((th,Xg,Q,Vg,P),sp.diff(E,P),'numpy')
EV =sp.lambdify((th,Xg,Q,Vg,P),sp.diff(E,Vg),'numpy')
EX =sp.lambdify((th,Xg,Q,Vg,P),sp.diff(E,Xg),'numpy')
EQ =sp.lambdify((th,Xg,Q,Vg,P),sp.diff(E,Q),'numpy')
lam=sp.symbols('L'); cp=sp.Poly(J.charpoly(lam).as_expr(),lam)
c3,c2,c1,c0=[sp.lambdify((th,Xg,Q,Vg),cp.nth(k),'numpy') for k in (3,2,1,0)]

def theta_star(P0,Xg0,V0=1.0):     # exact stable-branch equilibrium (Q=0)
    return 0.5*math.asin(max(-1,min(1,-4*P0*Xg0/(3*V0**2))))
def critvec(t,Xg0,Q0,V0):
    A=np.array(Jf(t,Xg0,Q0,V0),dtype=float); ev,Ve=np.linalg.eig(A); W=np.linalg.inv(Ve)
    c=[i for i in range(4) if abs(ev[i].imag)>1e-6]; i=c[int(np.argmax(ev[c].real))]
    return ev[i],Ve[:,i],W[i,:],A
def dlam_exact(P0,Xg0,Q0,V0):      # analytic dλ/dθ = w (dJ_total) v, machine precision
    t=theta_star(P0,Xg0,V0); lam0,v,w,A=critvec(t,Xg0,Q0,V0)
    eth=Eth(t,Xg0,Q0,V0,P0)
    def tot(dJexpl,Ep): 
        dth=-Ep/eth; return dJexpl + np.array(dJth(t,Xg0,Q0,V0),dtype=float)*dth
    out={}
    out['P']=complex(w@ (np.array(dJth(t,Xg0,Q0,V0),dtype=float)*(-EP(t,Xg0,Q0,V0,P0)/eth)) @v)
    out['V']=complex(w@ tot(np.array(dJV(t,Xg0,Q0,V0),dtype=float), EV(t,Xg0,Q0,V0,P0)) @v)
    out['Xg']=complex(w@ tot(np.array(dJX(t,Xg0,Q0,V0),dtype=float), EX(t,Xg0,Q0,V0,P0)) @v)
    out['Q']=complex(w@ tot(np.array(dJQ(t,Xg0,Q0,V0),dtype=float), EQ(t,Xg0,Q0,V0,P0)) @v)
    return out,lam0

# ---------- PART A: precision ----------
print("PART A — precision: analytic dRe/dθ (machine precision) vs Richardson-extrapolated FD")
P0,Xg0=0.5,1.2; ex,_=dlam_exact(P0,Xg0,0.0,1.0)
def dRe_fd(knob,h):
    m={'P':'idc_src','V':'Vg','Xg':'Xg'}[knob]; base=dict(idc_src=P0,Xg=Xg0,Vg=1.0)
    def mr(v):
        kk=dict(base); kk[m]=v; e=S.stable_eq(S.make_p(**kk),cfg)
        cc=[z for z in np.linalg.eigvals(S.jacobian(e,S.make_p(**kk),cfg)[:4,:4]) if abs(z.imag)>1e-6]
        return max(cc,key=lambda z:z.real).real
    return (mr(base[m]+h)-mr(base[m]-h))/(2*h)
for k in ['P','V','Xg']:
    d1=dRe_fd(k,1e-3); d2=dRe_fd(k,5e-4); rich=(4*d2-d1)/3   # Richardson O(h^4)
    print(f"   {k}: analytic={ex[k].real:+.10f}   Richardson-FD={rich:+.10f}   |diff|={abs(ex[k].real-rich):.2e}")

# ---------- PART B: transfer to the Hopf boundary ----------
print("\nPART B — at the Hopf boundary R=0 (for time-domain cross-check):")
print(f"  {'P':>5}{'Xg_Hopf':>9}{'f_H[Hz]':>9}{'dRe/dP':>10}{'dRe/dQ':>10}{'dRe/dV':>10}{'dRe/dXg':>10}")
def R_of(P0,Xg0): 
    t=theta_star(P0,Xg0); return c1(t,Xg0,0,1.)*c2(t,Xg0,0,1.)*c3(t,Xg0,0,1.)-c1(t,Xg0,0,1.)**2-c0(t,Xg0,0,1.)*c3(t,Xg0,0,1.)**2
for P0 in [0.4,0.5,0.6,0.8,1.0]:
    SN=3/(4*P0); lo,hi=0.3,SN*0.99999
    # bisect R=0 to high precision
    for _ in range(80):
        mid=0.5*(lo+hi)
        if R_of(P0,lo)*R_of(P0,mid)<=0: hi=mid
        else: lo=mid
    XgH=0.5*(lo+hi); t=theta_star(P0,XgH)
    # Hopf frequency ω_H = sqrt(c1/c3) ; f=ω/2π
    wH=math.sqrt(c1(t,XgH,0,1.)/c3(t,XgH,0,1.)); fH=wH/(2*math.pi)
    ex,lam0=dlam_exact(P0,XgH,0.0,1.0)
    print(f"  {P0:>5.2f}{XgH:>9.4f}{fH:>9.3f}{ex['P'].real:>10.1f}{ex['Q'].real:>10.1f}{ex['V'].real:>10.1f}{ex['Xg'].real:>10.1f}"
          f"   (Re λ_crit={lam0.real:+.2e}, ω_H={wH:.2f} rad/s)")
print("\n  time-domain prediction: at (P, Xg_Hopf) the response oscillates at f_H [Hz];")
print("  push Xg by ΔXg past the boundary → envelope grows as exp(dRe/dXg · ΔXg · t).")
