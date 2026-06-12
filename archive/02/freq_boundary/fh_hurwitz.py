"""
fh_hurwitz.py -- F-H boundary Sigma_H of the TASK model (fh_gate.rhs): verify the
Lienard-Chipart Hopf signature and the crossing properties (H2),(H3) on the real model.

chi(s;p) = det(sI - J(p)) = s^10 + a1 s^9 + ... + a10.  Hurwitz minors Delta_1..Delta_10.
A simple Hopf (one imaginary pair, rest LHP) is the Lienard-Chipart signature
   Sigma_H := { Delta_9 = 0,  Delta_k>0 (k=1..8),  a10>0 }     (Delta_10 = a10*Delta_9).

Checks (numerical, on the real task model -- numbers only cross-check, the claims are
the signature relations):
  (H1) J Hurwitz  <=>  all Delta_k>0           (verify on the stable side)
  (H2) at Sigma_H exactly one conj pair on iR; omega_H from even part E(W)=0, W=omega^2
  (H3) along g=1/Lg increasing, Delta_9: + -> -, and dRe(lambda)/dg > 0
"""
import numpy as np
from fh_gate import grid_RL, equilibrium, jac

def char_coeffs(J):
    # chi(s)=det(sI-J)= s^n + a1 s^{n-1}+...+an ; numpy poly gives [1,a1,...,an]
    return np.poly(np.linalg.eigvals(J)).real

def hurwitz_minors(a):
    # a = [1,a1,...,an]; build n x n Hurwitz matrix, return Delta_1..Delta_n
    n = len(a)-1
    H = np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            idx = 2*j - i + 1
            H[i,j] = a[idx] if 0 <= idx <= n else 0.0
    return [np.linalg.det(H[:k,:k]) for k in range(1,n+1)], H

def even_part_roots(a):
    # Re chi(i*omega) = E(W), W=omega^2. coeff of s^(10-k) is a[k]; at s=i*omega the even
    # powers (k even) contribute a[k]*(-1)^m * W^m with m=(10-k)/2.  Signs matter:
    n=len(a)-1
    Ecoef=[a[2*j]*((-1)**(n//2 - j)) for j in range(0, n//2+1)]  # W^(n/2)..W^0, highest first
    roots=np.roots(Ecoef)
    return np.array([r.real for r in roots if abs(r.imag)<1e-3 and r.real>0])  # W=omega^2>0

def J_at(SCR,Kp=0.30,Ki=150.0,XR=10.0):
    Rg,Lg=grid_RL(SCR,XR); x,res,ier=equilibrium(SCR,Kp,Ki,XR)
    assert res<1e-6, "no equilibrium at SCR=%.3f"%SCR
    return jac(x,Rg,Lg,Kp,Ki)

if __name__=="__main__":
    print("F-H signature of the TASK model around its Hopf SCR_H~0.950 (Ki=150,Kp=0.30,X/R=10):")
    print("  SCR     maxRe(J)   Delta_8     Delta_9     a10      Hurwitz?  signature")
    for SCR in [1.00,0.97,0.955,0.950,0.945,0.93,0.90]:
        J=J_at(SCR); mr=np.max(np.linalg.eigvals(J).real)
        a=char_coeffs(J); D,_=hurwitz_minors(a)
        allpos=all(d>0 for d in D)
        sig = (D[8-1]>0 and abs(D[9-1])<0.02*max(1,abs(D[7-1])) and a[10]>0)  # near Delta_9=0
        print("  %.3f   %+.4f   %+.2e  %+.2e  %+.1e   %s    %s"
              %(SCR,mr,D[7],D[8],a[10],"yes" if allpos else "NO ",
                "<-Sigma_H (Delta_9~0)" if abs(D[8])<0.05*abs(D[7]) else ""))
    # H2: omega_H from even part at the Hopf, vs actual imaginary eigenvalue
    print("\n(H2) at the Hopf: frequency from even part E(W)=0 vs actual Im(lambda):")
    # locate Hopf precisely
    lo,hi=0.90,1.00
    for _ in range(40):
        m=(lo+hi)/2; J=J_at(m); mr=np.max(np.linalg.eigvals(J).real)
        if mr>0: lo=m
        else: hi=m
    SCRh=(lo+hi)/2; J=J_at(SCRh); ev=np.linalg.eigvals(J)
    a=char_coeffs(J); W=even_part_roots(a)
    pair=ev[np.argsort(-ev.real)][:2]
    print("    SCR_H=%.4f: critical eigs=%s"%(SCRh,np.round(pair,3)))
    print("    omega_H from |Im lambda| = %.3f rad/s (%.2f Hz)"%(abs(pair[0].imag),abs(pair[0].imag)/2/np.pi))
    print("    omega_H from even-part E(W)=0 roots sqrt(W) = %s rad/s"%np.round(np.sqrt(np.sort(W))[:3],3))
    D,_=hurwitz_minors(a)
    print("    Delta_9 at Hopf = %.3e (should be ~0); Delta_1..8 all >0: %s; a10>0: %s"
          %(D[8], all(d>0 for d in D[:8]), a[10]>0))
    # H3: transversality dRe/dg, g=1/Lg
    print("\n(H3) transversality at Sigma_H (g=1/Lg increasing = weaker grid):")
    eps=1e-4
    mr_hi=np.max(np.linalg.eigvals(J_at(SCRh-eps)).real)  # smaller SCR = larger Lg = larger g
    mr_lo=np.max(np.linalg.eigvals(J_at(SCRh+eps)).real)
    # g increases as SCR decreases; dRe/dg ~ (mr at smaller SCR - mr at larger SCR)/...>0 if mr rises as SCR falls
    print("    maxRe(SCR=%.4f)=%+.4f  >  maxRe(SCR=%.4f)=%+.4f  => dRe/dg>0 (weaker grid -> RHP) %s"
          %(SCRh-eps,mr_hi,SCRh+eps,mr_lo,"OK" if mr_hi>mr_lo else "FAIL"))
    a_lo,_=hurwitz_minors(char_coeffs(J_at(SCRh+eps)))
    a_hi,_=hurwitz_minors(char_coeffs(J_at(SCRh-eps)))
    print("    Delta_9: SCR>SCR_H -> %+.2e (stable side >0),  SCR<SCR_H -> %+.2e (unstable <0)"
          %(a_lo[8],a_hi[8]))
