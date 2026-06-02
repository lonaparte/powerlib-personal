"""
risk_numerical.py -- numerical computations underpinning the R1/R2/R3 certificates.
All results are SANITY/witness numerics; the load-bearing claims are the KeYmaera X
certificates in ../kyx/.  Reproduces the figures cited in README.md.

Run:  python3 risk_numerical.py        (needs numpy, sympy, scipy)
The l1 parts additionally import the validated pipeline in
  formalization/numerical/sweep.py
"""
import numpy as np, math, sys, os
import scipy.linalg as sla

# ---------------------------------------------------------------------------
# R1: electrical onset Sigma_1 = {Delta_7(g)=0}, omega0 vs omega_LCL, transversality
# ---------------------------------------------------------------------------
def Ae_num(gv):
    """8-state PLL-frozen electrical Jacobian, g=1/Lg (representative LCL+current loop)."""
    A=np.zeros((8,8))
    A[0,0]=-2.1/0.001; A[0,2]=-1000; A[0,4]=2000; A[0,6]=126000
    A[1,1]=-2.1/0.001; A[1,3]=-1000; A[1,5]=2000; A[1,7]=126000
    A[2,0]=1e4; A[2,4]=-1e4; A[2,3]=314
    A[3,1]=1e4; A[3,5]=-1e4; A[3,2]=-314
    A[4,2]=gv; A[4,4]=-0.05*gv; A[4,5]=314
    A[5,3]=gv; A[5,5]=-0.05*gv; A[5,4]=-314
    A[6,0]=-1.26; A[7,1]=-1.26
    return A

def r1():
    print("="*70); print("R1  electrical onset Sigma_1"); print("="*70)
    # onset roots of Delta_7(g): found symbolically (deg-13); here verify the two crossings
    for gv in [10.128111641, 206.551223968]:
        ev=np.linalg.eigvals(Ae_num(gv))
        print("  g*=%.4f Lg*=%.5f H : rightmost eigs=%s  maxRe=%.2e"
              % (gv, 1/gv, np.round(ev[np.argsort(-ev.real)][:2],4), ev.real.max()))
    # physical (subsynchronous) onset g*=206.55:
    gv=206.551223968; ev=np.linalg.eigvals(Ae_num(gv))
    rc=[e for e in ev if abs(e.real)<0.5 and abs(e.imag)>1]
    w0=abs(rc[0].imag); Lg=1/gv
    wLCL=math.sqrt((0.001+Lg)/(0.001*Lg*1e-4))
    print("  onset Lg*=%.5f: omega0=%.2f (%.2f Hz) vs omega_LCL=%.2f (%.2f Hz) -> omega0 != omega_LCL"
          % (Lg, w0, w0/2/math.pi, wLCL, wLCL/2/math.pi))
    # transversality dMaxRe/dLg at onset
    def maxre(g): return np.linalg.eigvals(Ae_num(g)).real.max()
    h=1e-6; L0=1/gv; dRe=(maxre(1/(L0+h))-maxre(1/(L0-h)))/(2*h)
    print("  dMaxRe/dLg at onset = %+.1f  (>0 => weak grid pushes pair into RHP)" % dRe)

# ---------------------------------------------------------------------------
# R2: fold Sigma_2 = {|M|=Vg}, M=id_ref*wn*Lg+iq_ref*Rg (symbolic closed form)
# ---------------------------------------------------------------------------
def r2():
    print("="*70); print("R2  synchronization fold Sigma_2"); print("="*70)
    import sympy as sp
    Vg,Rg,Lg,wn,idr,iqr=sp.symbols('Vg Rg Lg wn id_ref iq_ref',positive=True)
    M=idr*wn*Lg+iqr*Rg; Phi=sp.expand(M**2-Vg**2)
    print("  M = id_ref*wn*Lg + iq_ref*Rg")
    print("  Sigma_2 (fully symbolic, 6 params): Phi(p) = M^2 - Vg^2 =")
    print("     ", Phi)
    print("  below fold (2 equilibria node+saddle) iff Phi<0; past fold (0 equilibria) iff Phi>0")
    print("  classical limit (Cf->0, Kpi,Kii->inf): recovers |id_ref*wn*Lg+iq_ref*Rg|=Vg (Wu)")

# ---------------------------------------------------------------------------
# R3a: tilted-energy barrier on the sync core; exact Vdot=-b*dw^2; basin c*=V(saddle)
# ---------------------------------------------------------------------------
def r3a():
    print("="*70); print("R3a  tilted-energy barrier (no SOS solver needed)"); print("="*70)
    b,K,Pm=0.1,1.0,0.3; d0=math.asin(Pm/K); cc=math.cos(d0)
    def Vdot(delta,w):
        s=math.sin(delta); fdw=-b*w-K*s+Pm
        return w*fdw + (K*math.sin(delta)-Pm)*w
    err=max(abs(Vdot(d0+dd,w)-(-b*w**2)) for dd in np.linspace(-.5,.5,11) for w in np.linspace(-1,1,11))
    Vsad=(0.5*0 + K*(cc-math.cos(math.pi-d0)) - Pm*((math.pi-d0)-d0))
    print("  V = 1/2 dw^2 + K(cos d* - cos d) - Pm(d - d*)  => Vdot = -b*dw^2  (max err %.1e)" % err)
    print("  certified basin level c* = V(saddle) - V(eq) = %.4f  (LaSalle: Vdot=0 only on dw=0)" % Vsad)

# ---------------------------------------------------------------------------
# R3b: certified basin level c*(b) monotone increasing in PLL-damping proxy b
# ---------------------------------------------------------------------------
def r3b():
    print("="*70); print("R3b  basin c*(zeta) monotone in PLL damping"); print("="*70)
    K,Pm=1.0,0.3; d0=math.asin(Pm/K); cc=math.cos(d0)
    def cstar(b):
        P=sla.solve_continuous_lyapunov(np.array([[0,1],[-K*cc,-b]]).T,-np.eye(2))
        def viol(cl):
            for dd in np.linspace(-1.4,1.4,61):
                for ww in np.linspace(-3,3,61):
                    x=np.array([dd,ww])
                    if x@P@x<=cl:
                        delta=d0+dd
                        Vd=(2*P@x)[0]*ww+(2*P@x)[1]*(-b*ww-K*math.sin(delta)+Pm)
                        if Vd>1e-9: return 1
            return 0
        lo,hi=0.0,40.0
        for _ in range(24):
            m=(lo+hi)/2
            if viol(m)==0: lo=m
            else: hi=m
        return lo
    print("   b (damping proxy) : c*")
    prev=None; mono=True
    for b in [0.05,0.1,0.2,0.4]:
        cs=cstar(b)
        if prev is not None and cs<prev-1e-3: mono=False
        print("     %.2f : %.3f" % (b,cs)); prev=cs
    print("   monotone increasing:", mono)

# ---------------------------------------------------------------------------
# R3-note: open set with l1<0 (Bautin-safe) AND past fold |M|>Vg (loss of sync)
#   uses the validated weak-grid l1 pipeline in formalization/numerical/sweep.py
# ---------------------------------------------------------------------------
def r3note():
    print("="*70); print("R3-note  l1<0 yet past-fold (sign l1 not the loss-of-sync test)"); print("="*70)
    here=os.path.dirname(os.path.abspath(__file__))
    swp=os.path.normpath(os.path.join(here,"..","..","numerical"))
    sys.path.insert(0,swp)
    try:
        from sweep import hopf_SCR, l1, pv
    except Exception as e:
        print("  (skipped: could not import sweep.py:", e, ")"); return
    Kp,Ki=0.8,150; iqref=0.0
    for SCR,idref in [(0.40,80.0),(0.40,120.0),(0.40,160.0)]:
        wn,Vg,Rg,Lg,vcd=pv(SCR,10); M=abs(idref*wn*Lg+iqref*Rg); ratio=M/Vg
        sh=hopf_SCR(10,Kp,Ki); l1s=int(np.sign(l1(sh,10,Kp,Ki)[0])) if sh else 0
        tag=" <== l1<0 AND past fold" if (l1s<0 and ratio>1) else ""
        print("  SCR=%.2f id_ref=%.0f: l1_sign=%+d  |M|/Vg=%.3f  past_fold=%s%s"
              % (SCR,idref,l1s,ratio,ratio>1,tag))

if __name__=="__main__":
    r1(); print(); r2(); print(); r3a(); print(); r3b(); print(); r3note()
