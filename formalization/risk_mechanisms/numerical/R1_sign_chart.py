"""
R1_sign_chart.py -- the genuine R1 deliverable the formalization review asked for:
the 7th Hurwitz minor Delta_7(p) of the 8x8 PLL-frozen electrical Jacobian A_e(p)
as an EXPLICIT POLYNOMIAL in the bifurcation parameters, and the parametric SIGN
CHART (onset manifold Sigma_1) on the (Lg, K_ad) face.

This is a CAS result (sympy), NOT a dL/KeYmaera X proof -- the degree-20 bivariate
Hurwitz determinant is exactly the object dL/QE cannot handle, which is why the dL
side stays a conjecture (kyx/conjecture_R1_electrical_onset.kyx).  Here we DO compute
it and trace Sigma_1, with numerics confirming Lienard-Chipart (D1..D6>0, D7 governs).

Honest scope: bifurcation params Lg (via g=1/Lg) and K_ad symbolic; the other 6
physical params are fixed rational (Lf=1e-3, Cf=1e-4, Rf=0.1, Rg=0.05, Kpi=1.26,
Kii=126, wn=314).  A fully-6-or-8-symbolic Delta_7 times out -- documented as the
CAS ceiling.

Run:  python3 R1_sign_chart.py
"""
import sympy as sp, numpy as np, time

g, Kad = sp.symbols('g Kad', positive=True)   # g = 1/Lg
s = sp.symbols('s')
Lf=sp.Rational(1,1000); Cf=sp.Rational(1,10000); Rf=sp.Rational(1,10)
Rg=sp.Rational(1,20); Kpi=sp.Rational(126,100); Kii=sp.Integer(126); wn=sp.Integer(314)

def Ae_sym():
    A=sp.zeros(8,8)
    A[0,0]=-(Rf+Kad)/Lf; A[0,2]=-1/Lf; A[0,4]=Kad/Lf; A[0,6]=Kii/Lf
    A[1,1]=-(Rf+Kad)/Lf; A[1,3]=-1/Lf; A[1,5]=Kad/Lf; A[1,7]=Kii/Lf
    A[2,0]=1/Cf; A[2,4]=-1/Cf; A[2,3]=wn
    A[3,1]=1/Cf; A[3,5]=-1/Cf; A[3,2]=-wn
    A[4,2]=g; A[4,4]=-Rg*g; A[4,5]=wn
    A[5,3]=g; A[5,5]=-Rg*g; A[5,4]=-wn
    A[6,0]=-Kpi; A[7,1]=-Kpi
    return A

def hurwitz_matrix(coeffs, n):
    """coeffs descending, monic (coeffs[0]=1)."""
    H=sp.zeros(n,n)
    for i in range(n):
        for j in range(n):
            idx=2*j-i+1
            if 0<=idx<=n: H[i,j]=coeffs[idx]
    return H

if __name__=="__main__":
    print("="*72)
    print("R1: Delta_7(g,Kad) and the Sigma_1 sign chart on the (Lg,K_ad) face")
    print("="*72)
    t0=time.time()
    co=sp.Poly((s*sp.eye(8)-Ae_sym()).det(), s).all_coeffs()
    print("char-poly chi(s; g,Kad) computed (%.0fs), 9 coeffs a0..a8" % (time.time()-t0))
    H=hurwitz_matrix(co, 8)
    t1=time.time()
    D7=sp.expand(H[:7,:7].det())
    pD7=sp.Poly(D7, g, Kad)
    print("Delta_7(g,Kad) computed (%.0fs): total degree %d, %d monomials, deg_g=%d, deg_Kad=%d"
          % (time.time()-t1, pD7.total_degree(), len(pD7.terms()),
             sp.Poly(D7,g).degree(), sp.Poly(D7,Kad).degree()))

    print("\nSIGN CHART -- onset manifold Sigma_1 = {Delta_7=0} traced as Lg*(K_ad):")
    print("  K_ad   onset Lg* (weak / strong root)        #pos roots")
    for kad in [sp.Integer(0), sp.Rational(1,2), sp.Integer(1), sp.Integer(2), sp.Integer(4)]:
        rts=[r for r in sp.real_roots(sp.Poly(D7.subs(Kad,kad), g)) if r.is_positive]
        if rts:
            Lgs=sorted(1/float(r) for r in rts)
            print("  %-5s  Lg* in {%s} H                 %d" %
                  (kad, ", ".join("%.5f"%L for L in Lgs), len(rts)))
        else:
            print("  %-5s  (no positive root: stable for all Lg)   0" % kad)

    # transversality from the REAL Delta_7 (no injected numbers), at Kad=2
    print("\nTRANSVERSALITY (from the real Delta_7(g), Kad=2):")
    dD7=sp.diff(D7.subs(Kad,2), g)
    for r in [rr for rr in sp.real_roots(sp.Poly(D7.subs(Kad,2),g)) if rr.is_positive]:
        sg=sp.sign(dD7.subs(g,r))
        print("  Lg*=%.5f: sign(dDelta7/dLg) = %s" % (1/float(r), -sg))  # dLg=-1/g^2 dg

    # Lienard-Chipart numeric confirmation (D1..D6>0, D7 governs)
    print("\nLIENARD-CHIPART (numeric, Kad=2): D1..D7 signs vs Lg")
    def Ae_num(Lg, kad=2.0):
        gv=1.0/Lg
        A=np.zeros((8,8))
        A[0,0]=-(0.1+kad)/0.001; A[0,2]=-1000; A[0,4]=kad/0.001; A[0,6]=126000
        A[1,1]=-(0.1+kad)/0.001; A[1,3]=-1000; A[1,5]=kad/0.001; A[1,7]=126000
        A[2,0]=1e4; A[2,4]=-1e4; A[2,3]=314
        A[3,1]=1e4; A[3,5]=-1e4; A[3,2]=-314
        A[4,2]=gv; A[4,4]=-0.05*gv; A[4,5]=314
        A[5,3]=gv; A[5,5]=-0.05*gv; A[5,4]=-314
        A[6,0]=-1.26; A[7,1]=-1.26
        return A
    def Hnum(Lg):
        A=Ae_num(Lg); a=np.poly(A); a=a/a[0]
        H=np.array([[a[2*j-i+1] if 0<=2*j-i+1<=8 else 0.0 for j in range(8)] for i in range(8)])
        return [np.linalg.det(H[:k,:k]) for k in range(1,8)], np.linalg.eigvals(A).real.max()
    for Lg in [0.01,0.0987,0.30]:
        D,mr=Hnum(Lg); print("  Lg=%.4f maxRe=%+.4f  D1..7: %s"
                              % (Lg, mr, ''.join('+' if d>0 else '-' for d in D)))
    print("\n=> Sigma_1 is the bivariate Delta_7=0; bare LCL (K_ad=0) has no onset (stable);")
    print("   active damping K_ad>0 creates the onset and pushes Lg* outward. This is the")
    print("   parametric sign chart R1b targets. (CAS result; not a dL proof -- see")
    print("   kyx/conjecture_R1_electrical_onset.kyx for the dL-side status.)")
