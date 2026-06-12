#!/usr/bin/env python3
"""Verify the structural facts the anchor proofs rely on:
   (i) err0 vanishes at gθ=0 (so χ₄|_fold = droop|_fold);
   (ii) a₁,a₂,a₃,a₄ are AFFINE in gθ (⟹ χ₄(gθ) is a degree≤3 polynomial, continuous);
   (iii) the sign-change hypothesis is SATISFIABLE (χ₄(gθ) really flips sign on some (0,g₁))."""
import sympy as sp, numpy as np
J00,J01,J03,J10,J11,J13,J20,J21,g,Kp,Ki=sp.symbols('J00 J01 J03 J10 J11 J13 J20 J21 g Kp Ki')
M=sp.Matrix([[J00,J01,0,J03],[J10,J11,0,J13],[J20,J21,0,g],[-Kp*J20,-Kp*J21,-Ki,-Kp*g]])
lam=sp.symbols('lam'); co=M.charpoly(lam).all_coeffs()
a1,a2,a3,a4=[sp.expand(c) for c in co[1:5]]
chi4=sp.expand(a1*a2*a3-a3**2-a1**2*a4)
err0=sp.expand(chi4.subs([(J03,0),(J13,0)])); droop=sp.expand(chi4-err0)
print("(i)  err0|_{g=0} == 0 :", sp.expand(err0.subs(g,0))==0)
print("     droop|_{g=0} (the fold value of χ₄, = what pushes Hopf off fold):",
      "nonzero-in-general" if sp.expand(droop.subs(g,0))!=0 else "ZERO")
print("(ii) deg_g a1,a2,a3,a4 :", [sp.degree(sp.Poly(x,g)) if x.has(g) else 0 for x in (a1,a2,a3,a4)],
      "(all ≤1 ⟹ affine in g)")
print("     deg_g chi4 :", sp.degree(sp.Poly(chi4,g)))
# (iii) satisfiability: random params, scan gθ, look for a sign flip of χ4(gθ) on gθ>0
f=sp.lambdify((J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki,g),chi4,'numpy')
rng=np.random.default_rng(3); found=0
for _ in range(2000):
    p={s:rng.normal()*1.5 for s in [J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki]}
    args=[float(p[s]) for s in [J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki]]
    gs=np.linspace(1e-6,3.0,400)
    vals=f(*args,gs)
    s0=np.sign(vals[0])
    idx=np.where(np.sign(vals)!=s0)[0]
    if len(idx):
        found+=1
        if found<=3:
            k=idx[0]
            print(f"     flip: χ4(0+)={vals[0]:+.3g} → χ4({gs[k]:.3f})={vals[k]:+.3g}  (root in (0,{gs[k]:.3f}))")
    if found>=3: break
print("(iii) sign-change on gθ∈(0,3) is SATISFIABLE:", found>0, f"(hypotheses non-vacuous)")
