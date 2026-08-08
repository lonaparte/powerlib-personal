"""
How strongly does each operating-point knob (P, Q, V) drive the small-signal
parametric-resonance mechanism (the λ_top dip at Ω=2ω_n)?

For the least-damped mode i (eigenvalue λ_i = -δ_i ± jω_n, right eigenvector
v_i, left eigenvector w_i with w_i·v_i = 1), a modulation θ(t)=θ0+a·cos(Ωt)
couples mode i to its conjugate at the principal resonance Ω=2ω_n with strength

    g_θ = | w_i · (∂A/∂θ) · conj(v_i) |          [parametric coupling]

The resonant growth rate is  s ≈ a·g_θ/2 − δ_i, so the mode is destabilised
when the modulation exceeds

    a_crit = 2 δ_i / g_θ         (absolute)     ε_crit = a_crit / |θ0|  (fractional)

Smaller ε_crit  ⇒  the knob drives the mechanism harder (more dangerous).
We also report the fractional amplitude at which that knob first crosses the
saddle-node (large-signal limit), so we can see which limit bites first.
"""
import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); np.set_printoptions(precision=4, suppress=True)

def eqA(**kw):
    p=S.make_p(**kw); eq=S.stable_eq(p,cfg); return eq, S.jacobian(eq,p,cfg), p

def dAdtheta(base, knob, h):
    th0=getattr(S.make_p(**base),knob)
    _,Ap,_=eqA(**{**base,knob:th0+h}); _,Am,_=eqA(**{**base,knob:th0-h})
    return (Ap-Am)/(2*h), th0

def mode_and_coupling(base, knobs):
    eq,A,p=eqA(**base)
    ev,V=np.linalg.eig(A); W=np.linalg.inv(V)            # rows of W = left eigenvectors
    comp=[i for i in range(len(ev)) if abs(ev[i].imag)>1e-6]
    i=comp[int(np.argmax(ev[comp].real))]                # least-damped complex mode
    lam=ev[i]; delta=-lam.real; wn=abs(lam.imag)
    vi=V[:,i]; wi=W[i,:]                                  # w_i·v_i = 1 by construction
    res={}
    for knob,h in knobs:
        dA,th0=dAdtheta(base,knob,h)
        g=abs(wi @ dA @ np.conj(vi))                      # parametric coupling
        a_crit=2*delta/g if g>0 else np.inf
        eps_crit=a_crit/abs(th0) if th0!=0 else a_crit    # for Q (θ0=0): report absolute a_crit
        res[knob]=dict(g=g, dAnorm=np.linalg.norm(dA), th0=th0,
                       a_crit=a_crit, eps_crit=eps_crit, gfrac=g*(abs(th0) if th0!=0 else 1.0))
    return lam, delta, wn, res

def sn_cross_frac(base, knob):
    """Fractional |Δθ0| that first makes the equilibrium vanish (saddle-node)."""
    th0=getattr(S.make_p(**base),knob)
    lo,hi=1e-4, 5.0
    def has_eq(frac,sign):
        kw={**base}; kw[knob]= (th0*(1+sign*frac) if th0!=0 else sign*frac)
        return S.stable_eq(S.make_p(**kw)) is not None
    best=np.inf
    for sign in (-1,1):
        f=0.001
        while f<3.0:
            if not has_eq(f,sign): best=min(best,f); break
            f*=1.15
    return best

KNOBS=[("idc_src",1e-4),("iq_ref",1e-4),("Vg",1e-4),("Xg",1e-4)]
NAME={"idc_src":"P (idc_src)","iq_ref":"Q (iq_ref)","Vg":"V (Vg)","Xg":"1/SCR (Xg)"}

for Xg in [1.45, 1.47]:
    base=dict(idc_src=0.5, iq_ref=0.0, Vg=1.0, Xg=Xg)
    lam,delta,wn,res=mode_and_coupling(base,KNOBS)
    print("="*92)
    print(f"BASE Xg={Xg}, P=0.5,Q=0,V=1.0   least-damped mode  λ={lam.real:+.3f}±{wn:.3f}j  "
          f"(δ={delta:.3f}, ω_n={wn:.3f}, 2ω_n={2*wn:.2f})")
    print(f"  {'knob':<14}{'g_θ coupling':>14}{'g·|θ0| (frac)':>15}{'ε_crit (small-sig)':>20}{'SN-cross frac':>15}{'which bites first':>18}")
    print("  "+"-"*88)
    for knob,_ in KNOBS:
        r=res[knob]; snc=sn_cross_frac(base,knob)
        epslabel = f"{r['eps_crit']*100:.1f}%" if r['th0']!=0 else f"a={r['a_crit']:.3f}"
        first = "small-sig (paramres)" if (r['th0']!=0 and r['eps_crit']<snc) else "large-sig (SN)"
        if r['th0']==0: first="(Q: base 0)"
        print(f"  {NAME[knob]:<14}{r['g']:>14.1f}{r['gfrac']:>15.1f}{epslabel:>20}{snc*100:>13.1f}%{first:>18}")

# validation note vs measured Xg time-domain at Xg=1.47:
base=dict(idc_src=0.5, iq_ref=0.0, Vg=1.0, Xg=1.47)
lam,delta,wn,res=mode_and_coupling(base,[("Xg",1e-4)])
g=res["Xg"]["g"]; a=0.021*1.47
pred=-delta*(1-a/(2*delta/g))
print("\nVALIDATION @Xg=1.47: measured λ_top(2ω_n, ε=2.1%) = -1.58;  "
      f"predicted from g_Xg={g:.1f}: {pred:+.2f}")
