"""
Compute dA/dtheta for each operating-point knob of the GFL-5d-ou model, to
decide (at the SYSTEM level, not by eyeballing terms) which knobs are
additive-only (degree) vs multiplicative (mechanism-eligible).

For a fluctuating parameter theta, linearizing about the moving equilibrium
x*(theta) gives

    d(dx)/dt = A dx  +  B dtheta            (additive forcing)
                     +  (dA/dtheta dtheta) dx   (multiplicative / parametric)

with
    A(theta)      = jacobian(eq(theta), p(theta))      (equilibrium MOVES with theta)
    B(theta)      = df/dtheta  at fixed x*             (additive push per unit theta)
    dA/dtheta     = TOTAL sensitivity of the generator
                  = DIRECT (theta in Jacobian entries, eq fixed)
                  + INDIRECT (through the equilibrium shift dx*/dtheta)

A knob is:
    * additive-only (pure degree)      iff dA/dtheta == 0
    * multiplicative (mechanism cand.) iff dA/dtheta != 0
and the "no common Lyapunov / mode rotates" strength is how fast the
least-damped eigenvECTOR (mode shape) turns with theta.
"""
import sys; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); np.set_printoptions(precision=3, suppress=True, linewidth=130)

# ---------- building blocks ----------
def eqA(**kw):
    p=S.make_p(**kw); eq=S.stable_eq(p,cfg)
    return eq, S.jacobian(eq,p,cfg), p

def jac_at(eq, **kw):
    """Jacobian evaluated at a GIVEN point eq, with parameters kw."""
    p=S.make_p(**kw); return S.jacobian(eq,p,cfg)

def drift_at(eq, **kw):
    p=S.make_p(**kw); return S.drift(eq,p,cfg)

def least_damped_mode(A):
    ev,V=np.linalg.eig(A)
    comp=[i for i in range(len(ev)) if abs(ev[i].imag)>1e-6]
    i=comp[int(np.argmax(ev[comp].real))]
    v=V[:,i]
    Q=np.linalg.qr(np.column_stack([v.real, v.imag]))[0]   # ortho 2D real invariant subspace
    return ev[i], Q

def subspace_angle(Q1,Q2):
    s=np.linalg.svd(Q1.T@Q2, compute_uv=False)
    s=np.clip(s,-1,1)
    return float(np.arccos(s.min()))     # largest principal angle [rad]

def sens(base, knob, h):
    """Return dict of additive/total/direct/indirect dA/dtheta norms + rotation."""
    eq0,A0,p0=eqA(**base)
    th0=getattr(S.make_p(**base), knob)     # effective base value (defaults if not in base)
    thp={**base, knob: th0+h}
    thm={**base, knob: th0-h}
    # additive forcing B = df/dtheta at fixed x*=eq0
    B=(drift_at(eq0,**thp)-drift_at(eq0,**thm))/(2*h)
    # TOTAL dA/dtheta: equilibrium moves
    eqp,Ap,_=eqA(**thp); eqm,Am,_=eqA(**thm)
    dA_tot=(Ap-Am)/(2*h)
    # DIRECT dA/dtheta: eq fixed at eq0, only parameter in jacobian changes
    dA_dir=(jac_at(eq0,**thp)-jac_at(eq0,**thm))/(2*h)
    dA_ind=dA_tot-dA_dir
    # mode-shape rotation of least-damped mode per unit theta
    _,Qp=least_damped_mode(Ap); _,Qm=least_damped_mode(Am)
    rot=subspace_angle(Qp,Qm)/(2*h)      # rad per unit theta
    return dict(
        theta0=th0,
        B=np.linalg.norm(B),
        tot=np.linalg.norm(dA_tot), dir=np.linalg.norm(dA_dir), ind=np.linalg.norm(dA_ind),
        elasticity=(abs(th0) if th0!=0 else 1.0)*np.linalg.norm(dA_tot)/np.linalg.norm(A0),
        rot=rot, rot_frac=rot*(abs(th0) if th0!=0 else 1.0),
        dA_tot=dA_tot, is_zero_base=(th0==0),
    )

KNOBS=[("idc_src","P (active-power source)",1e-4),
       ("iq_ref", "Q (reactive current ref)",1e-4),
       ("Vg",     "V (grid voltage)",        1e-4),
       ("Xg",     "1/SCR (grid strength)",   1e-4),
       ("kp_pll", "PLL prop. gain (control)",1e-2)]

def run_base(base,title):
    eq0,A0,p0=eqA(**base)
    ev0,_=least_damped_mode(A0)
    print("="*100)
    print(f"BASE OPERATING POINT: {title}")
    print(f"  params: idc_src(P)={base['idc_src']}, iq_ref(Q)={base['iq_ref']}, Vg(V)={base['Vg']}, Xg={base['Xg']}")
    print(f"  equilibrium Δθ*={eq0[0]:+.4f} rad, Vdc*={eq0[2]:.4f}")
    print(f"  least-damped mode: {ev0.real:+.3f} ± {abs(ev0.imag):.3f}j   ||A||_F={np.linalg.norm(A0):.2f}")
    print(f"\n  {'knob':<26}{'||B||':>9}{'||dA/dθ||':>11}{'  (direct':>10}{'indirect)':>11}"
          f"{'elasticity':>12}{'moderot[rad/θ]':>16}{'moderot·θ':>11}")
    print(f"  {'':<26}{'(additive)':>9}{'(total)':>11}{'':>10}{'':>11}{'(mult.,dimless)':>12}{'':>16}{'(dimless)':>11}")
    print("  "+"-"*104)
    rows={}
    for knob,label,h in KNOBS:
        r=sens(base,knob,h); rows[knob]=r
        verdict = "ADDITIVE-only" if r['tot']<1e-6*np.linalg.norm(A0) else "multiplicative"
        print(f"  {label:<26}{r['B']:>9.3f}{r['tot']:>11.3f}{r['dir']:>10.3f}{r['ind']:>11.3f}"
              f"{r['elasticity']:>12.4f}{r['rot']:>16.4f}{r['rot_frac']:>11.4f}   [{verdict}]")
    return rows

# strong / normal grid
run_base(dict(idc_src=0.5, iq_ref=0.0, Vg=1.0, Xg=0.5), "NORMAL grid (Xg=0.5), P=0.5, Q=0, V=1.0")
# near-boundary
run_base(dict(idc_src=0.5, iq_ref=0.0, Vg=1.0, Xg=1.45), "NEAR HOPF (Xg=1.45), P=0.5, Q=0, V=1.0")

# trend of the two most relevant quantities vs Xg
print("\n"+"="*100)
print("TREND vs Xg (how ||dA/dXg|| and least-damped mode-shape rotation grow toward the Hopf):")
print(f"  {'Xg':>6}{'||dA/dXg||':>12}{'moderot[rad/Xg]':>18}{'maxRe(eig)':>12}")
for Xg in [0.1,0.5,1.0,1.3,1.45,1.48]:
    base=dict(idc_src=0.5, iq_ref=0.0, Vg=1.0, Xg=Xg)
    r=sens(base,"Xg",1e-4)
    _,A0,_=eqA(**base)
    print(f"  {Xg:>6.2f}{r['tot']:>12.3f}{r['rot']:>18.3f}{np.linalg.eigvals(A0).real.max():>12.3f}")
