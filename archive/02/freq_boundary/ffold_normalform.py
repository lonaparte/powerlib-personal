"""
ffold_normalform.py -- OBJECT GATE + anchors for the parametric cycle-fold certificate
(kyx/ffold_cyclefold_normalform.kyx).  Confirms the task model actually obeys the Hopf
normal form and locates its Bautin organizing center, so the certified normal-form
structure applies to THIS model (not assumed).

(A) Normal-form validity: near the supercritical Hopf the limit-cycle amplitude^2 must be
    LINEAR in the growth-rate proxy mu (rho = r^2 ~ -mu/l1).  We measure amplitude^2 vs
    (SCR_H - SCR) for small offsets and check linearity.
(B) Bautin point: l1 at the Hopf changes sign at Kp* (l1>0 subcritical / l1<0 supercritical);
    Sigma_fold (the certified cycle fold) emanates from this codim-2 point.

l2 (second Lyapunov coeff, nondegeneracy) is NOT computed (needs the 5th-order normal form;
bautin_cert makes the same honest omission) -- so the EXISTENCE/location of the actual fold
curve stays numerical-continuation work; the fold STRUCTURE is the certified part.
"""
import numpy as np
from fh_gate import grid_RL, equilibrium
from fh_model_sym import rhs, jac
from scipy.integrate import solve_ivp

XR, Ki = 10.0, 150.0

def hopf_SCR(Kp):
    def mr(SCR):
        Rg,Lg=grid_RL(SCR,XR); x,r,_=equilibrium(SCR,Kp,Ki,XR)
        return np.max(np.linalg.eigvals(jac(x,Rg,Lg,Kp,Ki)).real) if r<1e-6 else None
    lo,hi=0.6,1.5
    for _ in range(40):
        m=(lo+hi)/2; v=mr(m)
        if v is None: lo=m; continue
        (lo,hi)=(m,hi) if v>0 else (lo,m)
    return (lo+hi)/2

def tensors(xeq,Rg,Lg,Kp,h=1e-3):
    n=10; B=np.zeros((n,n,n)); C=np.zeros((n,n,n,n))
    J=lambda x: jac(x,Rg,Lg,Kp,Ki)
    for k in range(n):
        ek=np.zeros(n); ek[k]=h; B[:,:,k]=(J(xeq+ek)-J(xeq-ek))/(2*h)
    for k in range(n):
        for l in range(n):
            ek=np.zeros(n); ek[k]=h; el=np.zeros(n); el[l]=h
            C[:,:,k,l]=(J(xeq+ek+el)-J(xeq+ek-el)-J(xeq-ek+el)+J(xeq-ek-el))/(4*h*h)
    return B,C

def l1_at(SCR,Kp):
    Rg,Lg=grid_RL(SCR,XR); xeq,r,_=equilibrium(SCR,Kp,Ki,XR); assert r<1e-6
    A=jac(xeq,Rg,Lg,Kp,Ki); w,V=np.linalg.eig(A); k=np.argmin(np.abs(w.real))
    lam=w[k]; om=abs(lam.imag); q=V[:,k]
    wL,VL=np.linalg.eig(A.T); kl=np.argmin(np.abs(wL-np.conj(lam))); p=VL[:,kl]
    p=p/np.conj(np.vdot(p,q))
    B,C=tensors(xeq,Rg,Lg,Kp)
    Bf=lambda u,v: np.einsum('ijk,j,k->i',B,u,v); Cf=lambda u,v,t: np.einsum('ijkl,j,k,l->i',C,u,v,t)
    qb=np.conj(q); I=np.eye(10)
    h11=np.linalg.solve(A,Bf(q,qb)); h20=np.linalg.solve(2j*om*I-A,Bf(q,q))
    g21=np.vdot(p,Cf(q,q,qb))-2*np.vdot(p,Bf(q,h11))+np.vdot(p,Bf(qb,h20))
    return np.real(g21)/(2*om)

def amplitude2(Kp,SCR,settle=6.0):
    Rg,Lg=grid_RL(SCR,XR); xeq,r,_=equilibrium(SCR,Kp,Ki,XR); assert r<1e-6
    f=lambda t,x: rhs(x,Rg,Lg,Kp,Ki); J=lambda t,x: jac(x,Rg,Lg,Kp,Ki)
    s=solve_ivp(f,[0,settle],xeq+1e-3*np.ones(10),method='Radau',jac=J,rtol=1e-7,atol=1e-9)
    y=s.y[:,s.t>settle*0.7]; amp=0.5*(y[9].max()-y[9].min())
    return amp*amp

if __name__=="__main__":
    print("(A) Normal-form validity at Kp=0.50 (supercritical): amplitude^2 vs mu-proxy (SCR_H-SCR)")
    Kp=0.50; SCRh=hopf_SCR(Kp); print("    SCR_H=%.4f"%SCRh)
    print("    delta=SCR_H-SCR   amplitude^2 (rho)   rho/delta (should be ~const if rho~ -mu/l1)")
    rows=[]
    for d in [0.002,0.004,0.006,0.008]:
        rho=amplitude2(Kp,SCRh-d); rows.append((d,rho)); print("    %.3f             %.4f            %.2f"%(d,rho,rho/d))
    # linear fit rho = k*delta through small-delta points
    ds=np.array([r[0] for r in rows]); rs=np.array([r[1] for r in rows])
    A=np.vstack([ds,np.ones_like(ds)]).T; k,b=np.linalg.lstsq(A,rs,rcond=None)[0]
    print("    linear fit rho = %.2f*delta + %.4f  (small intercept => normal form valid)"%(k,b))
    print()
    print("(B) Bautin point: l1 at the Hopf vs Kp (sign change = where Sigma_fold originates)")
    print("    Kp     SCR_H     l1            type")
    prev=None; star=None
    for Kp in [0.20,0.30,0.36,0.40,0.45,0.55]:
        sh=hopf_SCR(Kp); v=l1_at(sh,Kp)
        print("    %.2f   %.4f    %+.3e   %s"%(Kp,sh,v,"subcritical(l1>0)" if v>0 else "supercritical(l1<0)"))
        if prev and prev[1]*v<0: star=(prev[0]+Kp)/2
        prev=(Kp,v)
    print("    => Bautin Kp* ~ %s (l1 sign change). Sigma_fold (certified normal-form cycle"%(("%.2f"%star) if star else "?"))
    print("       fold) emanates from here; l2!=0 (nondegeneracy) + the fold curve = numerical")
    print("       continuation, not done (same honest omission as numerical/bautin_cert).")
