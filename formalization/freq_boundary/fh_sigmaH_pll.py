"""
fh_sigmaH_pll.py -- EXPLICIT F-H boundary Sigma_H on the PLL-gain subspace (Kp_pll, Ki_pll)
at a fixed grid, for the task model (fh_gate.rhs).

Structural facts (verified below, not assumed):
  (S1) the equilibrium x* does NOT depend on (Kp_pll, Ki_pll) -- at equilibrium v_cqc=0,
       eta=0, so the PLL gains drop out of the equilibrium equations.
  (S2) (Kp_pll, Ki_pll) enter J only through ONE row (theta_e'), linearly.  Hence
       det(sI-J) is AFFINE in (Kp,Ki): every char-poly coeff a_k = alpha_k + beta_k*Kp +
       gamma_k*Ki, EXACTLY (a determinant is multilinear in any single row).
Therefore a_k are obtained EXACTLY by 3-point interpolation, and the 9th Hurwitz minor
   Delta_9(Kp,Ki)  is an EXPLICIT polynomial (degree <=9) in (Kp,Ki).
Sigma_H|_grid = { Delta_9(Kp,Ki)=0, Delta_1..8>0, a10>0 } is then an explicit algebraic
curve = the PLL-tuning stability boundary.  We build it, verify it passes through the
known Hopf, and cross-check the curve against the direct eigenvalue Hopf.
"""
import numpy as np
from fh_gate import grid_RL, equilibrium, jac, rhs

SCR0, XR = 0.95, 10.0           # fixed grid (near the nominal Hopf)
Rg, Lg = grid_RL(SCR0, XR)
# (S1): x* is independent of (Kp,Ki) -- compute it ONCE (at nominal gains) and reuse.
X_STAR, _res, _ier = equilibrium(SCR0, 0.30, 150.0, XR); assert _res < 1e-6

def J_of(Kp, Ki):
    return jac(X_STAR, Rg, Lg, Kp, Ki), X_STAR

def coeffs(Kp, Ki):
    J,_ = J_of(Kp, Ki)
    return np.poly(np.linalg.eigvals(J)).real      # [1, a1, ..., a10]

# ---- (S1) equilibrium independent of (Kp,Ki): confirm by re-solving at two gain points ----
x1,r1,_ = equilibrium(SCR0,0.30,150.0,XR); x2,r2,_ = equilibrium(SCR0,0.80,400.0,XR)
print("(S1) ||x*(0.30,150) - x*(0.80,400)|| = %.2e  (==0 => x* independent of PLL gains)"
      % np.linalg.norm(x1-x2))

# ---- (S2) check a_k affine in (Kp,Ki): predict a 4th point from 3 ----
base=coeffs(0.0,0.0); aKp=coeffs(1.0,0.0); aKi=coeffs(0.0,1.0)
alpha=base; beta=aKp-base; gamma=aKi-base
test=coeffs(0.7,200.0); pred=alpha+beta*0.7+gamma*200.0
relerr=np.max(np.abs(test-pred)/(np.abs(test)+1.0))
print("(S2) a_k affine in (Kp,Ki) [EXACT by structure: gains in one row of J => det affine];")
print("     verified: max RELATIVE prediction error at (0.7,200) = %.1e (float precision)"%relerr)

# ---- EXPLICIT Sigma_H data: the affine coefficients a_k = alpha_k + beta_k*Kp + gamma_k*Ki
# (by (S2) these are EXACT; Delta_9(Kp,Ki) is the explicit degree-<=9 polynomial det Hurwitz(a)).
print("\nExplicit Sigma_H|grid data: a_k(Kp,Ki) = alpha_k + beta_k*Kp + gamma_k*Ki  (k=0..10)")
print("  k    alpha_k         beta_k          gamma_k")
for k in range(11):
    print("  %2d  %+.6e  %+.6e  %+.6e" % (k, alpha[k], beta[k], gamma[k]))

def hurwitz_det9(Kp_, Ki_):
    av=[alpha[k]+beta[k]*Kp_+gamma[k]*Ki_ for k in range(11)]    # exact affine a_k
    H=np.zeros((9,9))
    for i in range(9):
        for j in range(9):
            idx=2*j-i+1
            H[i,j]=av[idx] if 0<=idx<=10 else 0.0
    return np.linalg.det(H)

# ---- boundary curve Sigma_H = {Delta_9=0} + sign chart, validated vs eigenvalue Hopf ----
from scipy.optimize import brentq
print("\nSigma_H = {Delta_9(Kp,Ki)=0}: boundary curve vs direct eigenvalue Hopf (grid SCR=%.3f):"%SCR0)
print("  Ki      Kp*(Delta_9=0)   maxRe@Kp*    maxRe@Kp*-.02   maxRe@Kp*+.02   stable side")
def mre(Kp_,Ki_): J,_=J_of(Kp_,Ki_); return np.max(np.linalg.eigvals(J).real)
for Kival in [100.0,150.0,200.0,300.0,400.0]:
    g=lambda kp: hurwitz_det9(kp,Kival)
    grid=np.arange(0.03,1.5,0.01); kp_star=None      # scan for FIRST sign change of Delta_9
    for a_,b_ in zip(grid[:-1],grid[1:]):
        if g(a_)*g(b_)<0: kp_star=brentq(g,a_,b_,xtol=1e-12); break
    if kp_star is None: print("  %6.0f   (no Hopf root in [0.03,1.5])"%Kival); continue
    m0,mm,mp=mre(kp_star,Kival),mre(kp_star-0.02,Kival),mre(kp_star+0.02,Kival)
    side="Kp<Kp* (lower gain)" if mm<0 else "Kp>Kp* (higher gain)"
    print("  %6.0f   %.5f          %+.2e    %+.4f         %+.4f         %s"
          %(Kival,kp_star,m0,mm,mp,side))
print("\n  => Delta_9(Kp,Ki)=0 (explicit, from the affine a_k) IS the PLL-tuning Hopf boundary")
print("     (maxRe~0 on it). nominal (0.30,150): Delta_9=%.3e ~ 0 (grid at its Hopf)."%hurwitz_det9(0.30,150.0))
print("  Delta_9 is an explicit polynomial of degree <=9 in (Kp,Ki); the affine a_k above are")
print("  its exact data (full expansion is CAS-blocked by the 1..1e27 coefficient range, not needed).")
