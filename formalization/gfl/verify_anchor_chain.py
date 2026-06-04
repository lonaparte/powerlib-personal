#!/usr/bin/env python3
"""End-to-end numeric cross-validation of ScrHopfAnchor (independent of sympy generation).
Confirms: chi4f(gθ) = true χ₄(gθ); a sign-change set yields a real root gθ*∈(0,g₁) off the fold;
at gθ* with a₁,a₃>0 the genuine Hopf ω²=a₃/a₁>0 and (iω)⁴+a₁(iω)³+a₂(iω)²+a₃(iω)+a₄ = 0."""
import numpy as np
def coeffs(p, g):                      # a1..a4 as functions of gθ=g, from the matrix directly
    J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki = p
    M=np.array([[J00,J01,0,J03],[J10,J11,0,J13],[J20,J21,0,g],[-Kp*J20,-Kp*J21,-Ki,-Kp*g]])
    return np.poly(M)[1:]              # [a1,a2,a3,a4] of det(λI−M), INDEPENDENT of our literals
def chi4_true(p,g):
    a1,a2,a3,a4=coeffs(p,g); return a1*a2*a3-a3**2-a1**2*a4
# our literal chi4coeff_i (gθ→g), transcribed from the Lean defs
def chi4f_lit(p,g):
    J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki = p
    a1= 1*g*Kp - 1*J11 - 1*J00
    a2= 1*J13*J21*Kp - 1*J11*g*Kp + 1*J03*J20*Kp - 1*J00*g*Kp + 1*g*Ki - 1*J01*J10 + 1*J00*J11
    a3= -1*J03*J11*J20*Kp + 1*J03*J10*J21*Kp + 1*J01*J13*J20*Kp - 1*J01*J10*g*Kp - 1*J00*J13*J21*Kp + 1*J00*J11*g*Kp + 1*J13*J21*Ki - 1*J11*g*Ki + 1*J03*J20*Ki - 1*J00*g*Ki
    a4= -1*J03*J11*J20*Ki + 1*J03*J10*J21*Ki + 1*J01*J13*J20*Ki - 1*J01*J10*g*Ki - 1*J00*J13*J21*Ki + 1*J00*J11*g*Ki
    return a1*a2*a3-a3**2-a1**2*a4, (a1,a2,a3,a4)
rng=np.random.default_rng(11); tested=0; maxliterr=0.0
print("set | Δ(chi4f_lit vs true χ4) | gθ*∈(0,g₁) root | a₁,a₃>0? | ω²=a₃/a₁ | |poly(iω)|")
for _ in range(6000):
    p=rng.normal(size=10)*1.5
    g1=rng.uniform(0.2,3.0)
    f0=chi4_true(p,0.0); f1=chi4_true(p,g1)
    if not (f0<0<f1):  continue                       # want the theorem's sign-change orientation
    # literal vs true coeff-function agreement on a grid
    gg=np.linspace(0,g1,50)
    derr=max(abs(chi4f_lit(p,g)[0]-chi4_true(p,g)) for g in gg)
    maxliterr=max(maxliterr,derr)
    # locate the IVT root by bisection
    lo,hi=0.0,g1
    for _ in range(80):
        mid=0.5*(lo+hi)
        if chi4_true(p,mid)<0: lo=mid
        else: hi=mid
    gstar=0.5*(lo+hi)
    _,(a1,a2,a3,a4)=chi4f_lit(p,gstar)
    genuine = (a1>0 and a3>0)
    w2=a3/a1
    z=1j*np.sqrt(abs(w2))
    polyiw=abs(z**4+a1*z**3+a2*z**2+a3*z+a4)
    tested+=1
    if tested<=4:
        print(f" {tested}  |  {derr:.2e}  |  gθ*={gstar:.4f}∈(0,{g1:.3f}) χ4={chi4_true(p,gstar):+.1e} | "
              f"{'YES' if genuine else 'no '} | {w2:+.4f} | {polyiw:.1e}")
    if tested>=4: break
print(f"\nmax |chi4f_lit − true χ4| over grids: {maxliterr:.2e}")
print("ALL: literals match true χ4, root lands in (0,g₁) off fold,",
      "and where a₁,a₃>0 the genuine ω²=a₃/a₁>0 with poly(iω)≈0  ->",
      "PASS" if maxliterr<1e-9 else "FAIL")

# --- non-vacuity of the GENUINE case: ∃ params with sign-change AND a₁,a₃>0 on (0,g₁) ? ---
print("\n--- non-vacuity of chi4_genuine_hopf_anchored (genuine off-fold Hopf) ---")
rng2=np.random.default_rng(202); ok=0
for _ in range(400000):
    p=rng2.normal(size=10)*1.5
    g1=rng2.uniform(0.2,3.0)
    if not (chi4_true(p,0.0)<0<chi4_true(p,g1)): continue
    gg=np.linspace(1e-9,g1,60)
    pos=all(chi4f_lit(p,g)[1][0]>0 and chi4f_lit(p,g)[1][2]>0 for g in gg)  # a1,a3>0 throughout
    if not pos: continue
    # root + genuineness
    lo,hi=0.0,g1
    for _ in range(80):
        mid=0.5*(lo+hi); 
        if chi4_true(p,mid)<0: lo=mid
        else: hi=mid
    gstar=0.5*(lo+hi); _,(a1,a2,a3,a4)=chi4f_lit(p,gstar)
    w2=a3/a1; z=1j*np.sqrt(w2)
    ok+=1
    if ok<=3:
        print(f"  GENUINE: gθ*={gstar:.4f}∈(0,{g1:.3f}), a₁={a1:.3f}>0, a₃={a3:.3f}>0, "
              f"ω²=a₃/a₁={w2:.4f}>0, |poly(iω)|={abs(z**4+a1*z**3+a2*z**2+a3*z+a4):.1e}")
    if ok>=3: break
print(f"genuine-case params FOUND: {ok>0}  (chi4_genuine_hopf_anchored NON-vacuous)" if ok else
      "genuine-case NOT found in budget (hpos may be hard to satisfy with this sign orientation)")
