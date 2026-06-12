#!/usr/bin/env python3
"""Independent (numpy) cross-validation of the ScrHopf4D Lean literals.
Catches transcription errors the Lean proofs cannot (internally-consistent typos)."""
import numpy as np, re
b=open('/tmp/chi4_lean.txt').read()
def grab(tag):
    s=b.split(tag+':=\n',1)[1]; return s.split('\n\n',1)[0].strip()
def pyify(e):
    e=e.replace('^','**').replace('(1:ℝ)','1').replace('(2:ℝ)','2').replace('(3:ℝ)','3')
    e=e.replace('gθ','g').replace('Kp_pll','Kp').replace('Ki_pll','Ki')
    return e
A1,A2,A3,A4,ERR0,DROOP=[pyify(grab(t)) for t in ['A1','A2','A3','A4','ERR0','DROOP']]
def ev(expr,P): return eval(expr,{'__builtins__':{}},P)
rng=np.random.default_rng(7); maxerr=0.0
print("set |  Δcharpoly(numpy vs literals)  |  Δdecomp(χ4-(err0+droop)) | Δerr0(χ4|J03=J13=0 - ERR0) | hopf ω²=a3/a1")
for k in range(6):
    v={n:float(rng.normal()) for n in ['J00','J01','J03','J10','J11','J13','J20','J21','g','Kp','Ki']}
    M=np.array([[v['J00'],v['J01'],0,v['J03']],
                [v['J10'],v['J11'],0,v['J13']],
                [v['J20'],v['J21'],0,v['g']],
                [-v['Kp']*v['J20'],-v['Kp']*v['J21'],-v['Ki'],-v['Kp']*v['g']]])
    npoly=np.poly(M)            # [1, a1, a2, a3, a4] = det(λI−M), independent of sympy
    lit=[1.0,ev(A1,v),ev(A2,v),ev(A3,v),ev(A4,v)]
    d_cp=max(abs(npoly[i]-lit[i]) for i in range(5))
    chi4=lit[1]*lit[2]*lit[3]-lit[3]**2-lit[1]**2*lit[4]
    d_dec=abs(chi4-(ev(ERR0,v)+ev(DROOP,v)))
    v0=dict(v,J03=0.0,J13=0.0)
    chi4_0=ev(A1,v0)*ev(A2,v0)*ev(A3,v0)-ev(A3,v0)**2-ev(A1,v0)**2*ev(A4,v0)
    d_e0=abs(chi4_0-ev(ERR0,v0))
    # hopf_deg4: force χ4=0 via a4, need a1,a3>0; check (iω)^4+...=0 at ω=√(a3/a1)
    a1,a2,a3=abs(ev(A1,v))+0.5,ev(A2,v),abs(ev(A3,v))+0.5
    a4=(a1*a2*a3-a3**2)/a1**2          # forces χ4=0
    w=np.sqrt(a3/a1); z=1j*w
    res=z**4+a1*z**3+a2*z**2+a3*z+a4
    d_hopf=abs(res)
    maxerr=max(maxerr,d_cp,d_dec,d_e0,d_hopf)
    print(f" {k}  |  {d_cp:.2e}  |  {d_dec:.2e}  |  {d_e0:.2e}  |  ω²={w*w:.3f}>0 res={d_hopf:.1e}")
print(f"\nMAX abs error across all checks/sets: {maxerr:.3e}  ->",
      "PASS" if maxerr<1e-9 else "FAIL")
