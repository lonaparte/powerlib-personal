"""
Is 'P≈Q≈V' real or an artifact of measuring the wrong coupling?

Two DIFFERENT 'influences on stability' of the least-damped GFL mode i
(λ_i = -δ ± jω, right/left eigvec v_i, w_i with w_i·v_i=1):

  DIAGONAL   dλ_i/dθ = w_i (∂A/∂θ) v_i        <- how θ moves THIS mode's own
                                                 damping/frequency (the standard
                                                 'which parameter affects the mode')
  CONJUGATE  g_θ      = |w_i (∂A/∂θ) conj(v_i)| <- 2ω_n parametric-pumping term
                                                  (what I reported before)

Also report ∂Δθ*/∂θ (how much each knob moves the equilibrium angle), because
if the ∂A/∂θ are all dominated by the SAME equilibrium-shift direction, the
couplings collapse together artificially.

Computed at WELL-CONDITIONED points first (Xg=0.5, 1.0), then near boundary,
with an h-convergence check.
"""
import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); np.set_printoptions(precision=4, suppress=True)

def eqA(**kw):
    p=S.make_p(**kw); eq=S.stable_eq(p,cfg); return eq, S.jacobian(eq,p,cfg)

def dAdtheta(base, knob, h):
    th0=getattr(S.make_p(**base),knob)
    eqp,Ap=eqA(**{**base,knob:th0+h}); eqm,Am=eqA(**{**base,knob:th0-h})
    dTheta=(eqp[0]-eqm[0])/(2*h)          # ∂Δθ*/∂θ
    return (Ap-Am)/(2*h), th0, dTheta

def analyze(base, knobs, h=1e-4):
    eq,A=eqA(**base)
    ev,V=np.linalg.eig(A); W=np.linalg.inv(V)
    comp=[i for i in range(len(ev)) if abs(ev[i].imag)>1e-6]
    i=comp[int(np.argmax(ev[comp].real))]            # least-damped complex = GFL mode
    lam=ev[i]; vi=V[:,i]; wi=W[i,:]
    rows={}
    for knob,_ in knobs:
        dA,th0,dTh=dAdtheta(base,knob,h)
        dlam=wi @ dA @ vi                            # diagonal (eigenvalue sensitivity)
        g   =abs(wi @ dA @ np.conj(vi))              # conjugate (parametric pump)
        rows[knob]=dict(th0=th0, dTheta=dTh,
                        dRe=dlam.real, dIm=dlam.imag, dabs=abs(dlam), g=g)
    return lam, rows

KN=[("idc_src",0),("iq_ref",0),("Vg",0),("Xg",0)]
NM={"idc_src":"P","iq_ref":"Q","Vg":"V","Xg":"grid-str(Xg)"}

for Xg in [0.5, 1.0, 1.45]:
    base=dict(idc_src=0.5, iq_ref=0.0, Vg=1.0, Xg=Xg)
    lam,rows=analyze(base,KN)
    print("="*104)
    print(f"BASE Xg={Xg}  GFL mode λ={lam.real:+.3f}±{abs(lam.imag):.3f}j   (δ={-lam.real:.3f}, ω_n={abs(lam.imag):.3f})")
    print(f"  {'knob':<13}{'∂Δθ*/∂θ':>12}{'dRe(λ)/dθ':>13}{'|dλ/dθ|':>12}{'g (conj/pump)':>15}"
          f"{'  |dλ/dθ|·|θ0|':>15}{'g·|θ0|':>10}")
    print("  "+"-"*98)
    for knob,_ in KN:
        r=rows[knob]; sc=abs(r['th0']) if r['th0']!=0 else 1.0
        print(f"  {NM[knob]:<13}{r['dTheta']:>12.2f}{r['dRe']:>13.2f}{r['dabs']:>12.1f}{r['g']:>15.1f}"
              f"{r['dabs']*sc:>15.1f}{r['g']*sc:>10.1f}")

# h-convergence check at the near-boundary point (where fsolve warned)
print("\n" + "="*104)
print("h-convergence of dλ/dθ and g at Xg=1.45 (guard against SN-region numerical noise):")
base=dict(idc_src=0.5, iq_ref=0.0, Vg=1.0, Xg=1.45)
for h in [1e-3,3e-4,1e-4,3e-5]:
    lam,rows=analyze(base,KN,h=h)
    r=rows['Vg']; rp=rows['idc_src']
    print(f"  h={h:.0e}:  V: dRe={r['dRe']:8.2f} g={r['g']:8.1f}   |   P: dRe={rp['dRe']:8.2f} g={rp['g']:8.1f}")
