"""
ffold_cycle.py -- F-fold F1: a STABLE limit cycle exists past Sigma_H (supercritical Hopf).
Computer-assisted-style verification on the real 10-state task model (fh_gate.rhs):
locate the periodic orbit via a Poincare section, then compute the FLOQUET multipliers
from the monodromy matrix (variational equation over one period).  A stable cycle has the
trivial multiplier ~1 (flow direction) and ALL nontrivial |mu|<1.

Numerical here (solid evidence for F1); the interval-Floquet enclosure (rigorous, CAPD-
style) is attempted in ffold_floquet_interval.py.  F2 (the cycle fold itself) and a fully
rigorous orbit enclosure remain validated-numerics / open (see README, honest layering).
"""
import numpy as np
from fh_gate import grid_RL, equilibrium
from fh_model_sym import rhs, jac          # fast analytic rhs + Jacobian
from scipy.integrate import solve_ivp

Kp, Ki, XR = 0.50, 150.0, 10.0

def hopf_SCR():
    def mr(SCR):
        Rg,Lg=grid_RL(SCR,XR); x,r,_=equilibrium(SCR,Kp,Ki,XR)
        return np.max(np.linalg.eigvals(jac(x,Rg,Lg,Kp,Ki)).real) if r<1e-6 else None
    lo,hi=0.6,1.1
    for _ in range(36):
        m=(lo+hi)/2; v=mr(m)
        if v is None: lo=m; continue
        (lo,hi)=(m,hi) if v>0 else (lo,m)
    return (lo+hi)/2

def setup(SCR):
    Rg,Lg=grid_RL(SCR,XR); xeq,r,_=equilibrium(SCR,Kp,Ki,XR); assert r<1e-6
    f=lambda t,x: rhs(x,Rg,Lg,Kp,Ki); Jf=lambda t,x: jac(x,Rg,Lg,Kp,Ki)
    return xeq,Rg,Lg,f,Jf

def find_orbit(SCR, settle=8.0, win=2.0):
    """Settle onto the cycle; return a point x0 on a Poincare section th_e=c (d th_e/dt>0)
    and the period T from consecutive crossings.  Returns None if no clean cycle is found
    (e.g. diverged past the cycle fold)."""
    xeq,Rg,Lg,f,Jf=setup(SCR)
    s0=solve_ivp(f,[0,settle],xeq+1e-3*np.ones(10),method='Radau',jac=Jf,rtol=1e-9,atol=1e-11,dense_output=True)
    if not s0.success or np.max(np.abs(s0.y))>1e5: return None
    tt=np.linspace(settle-win,settle,40000); Y=s0.sol(tt)
    amp=Y[9].max()-Y[9].min()
    if amp<1e-5: return None                         # collapsed to equilibrium
    c=0.5*(Y[9].max()+Y[9].min())
    cr=[]
    for i in range(len(tt)-1):
        if Y[9,i]<c<=Y[9,i+1]:
            a=(c-Y[9,i])/(Y[9,i+1]-Y[9,i]); cr.append((tt[i]+a*(tt[i+1]-tt[i]), Y[:,i]+a*(Y[:,i+1]-Y[:,i])))
    if len(cr)<2: return None
    T=cr[1][0]-cr[0][0]; x0=cr[0][1]
    return x0,T,c,Rg,Lg,f,Jf

def monodromy(x0,T,Rg,Lg):
    """Integrate the variational equation (x,Y') over one period; return M=Y(T)."""
    def aug(t,z):
        x=z[:10]; Y=z[10:].reshape(10,10)
        dx=rhs(x,Rg,Lg,Kp,Ki); dY=jac(x,Rg,Lg,Kp,Ki)@Y
        return np.concatenate([dx,dY.ravel()])
    z0=np.concatenate([x0,np.eye(10).ravel()])
    s=solve_ivp(aug,[0,T],z0,method='Radau',rtol=1e-9,atol=1e-11)
    return s.y[10:,-1].reshape(10,10), s.y[:10,-1]

if __name__=="__main__":
    SCRh=hopf_SCR(); print("task model Hopf at Kp=0.50: SCR_H=%.4f"%SCRh)
    # Floquet at a representative point past Sigma_H (delta=0.01, settles cleanly)
    SCR=SCRh-0.01; r=find_orbit(SCR, settle=6.0); assert r is not None, "no cycle at SCR=%.4f"%SCR
    x0,T,c,Rg,Lg,f,Jf=r
    s=solve_ivp(f,[0,T],x0,method='Radau',jac=Jf,rtol=1e-9,atol=1e-11,dense_output=True)
    print("  settled limit cycle: th_e p2p amplitude=%.4f rad, period T=%.5f s"%(np.ptp(s.sol(np.linspace(0,T,2000))[9]),T))
    M,xret=monodromy(x0,T,Rg,Lg)
    mu=np.linalg.eigvals(M); mu=mu[np.argsort(-np.abs(mu))]
    print("\nF1 at SCR=%.4f (past Sigma_H), period T=%.5f s (%.2f Hz):"%(SCR,T,1/T))
    print("  return error ||P(x0)-x0|| = %.2e (orbit closure)"%np.linalg.norm(xret-x0))
    print("  Floquet multipliers |mu| (sorted):")
    for m in mu: print("     |mu|=%.5f   mu=%.4f%+.4fj"%(abs(m),m.real,m.imag))
    triv_idx=int(np.argmin(np.abs(np.abs(mu)-1.0)))     # trivial multiplier ~1 (flow direction)
    nontriv=np.delete(mu,triv_idx)
    nontriv_max=float(np.max(np.abs(nontriv)))
    print("  trivial multiplier ~1: |mu|=%.5f ; max NONTRIVIAL |mu|=%.5f"%(abs(mu[triv_idx]),nontriv_max))
    print("  => %s (max nontrivial |mu|<1 => orbitally STABLE limit cycle: F1 holds)"
          %("STABLE" if nontriv_max<1 else "NOT stable"))
