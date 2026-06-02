#!/usr/bin/env python3
"""
(A) Parametric symbolic derivation toward the GFL-VSC F-H (Hopf) surface Σ_H (sympy, CAS).
Fully symbolic in p and θ_e* (C=cosθ_e*, S=sinθ_e*).  Not a Lean certificate.

CORRECTION (vs an earlier run): the full 10×10 characteristic polynomial is NOT a wall — that was an
algorithm-choice error (berkowitz determinant).  `J.charpoly` (Faddeev–LeVerrier, fraction-free)
computes it in ~3.6 s with COMPACT coefficients.

WHAT COMPUTES (run this file):
  * general char poly a_k(x;p,C,S) via J.charpoly — 3.6 s, coeff op-counts
        [1, 37, 388, 1288, 3509, 6630, 10221, 11739, 8893, 3113, 529].
  * equilibrium x*(p,C,S) in closed form (i_d,i_q = rotation of refs; electrical & integrator states
    by linear solve; η*=0), and the implicit-angle constraint
        g(p,C,S) := v_cqc(x*) = 0      (a clean rational function — defines θ_e*).
WHERE THE COST NOW LIVES (the genuine remaining work, = the problem's "(p,θ_e*) 有理函数 + 消元"):
  * substituting x*(p,C,S) into the char poly coeffs blows them up (a_5 ~1.8e5, a_6 ~2.7e5 ops);
  * so the closed-form Σ_H = {Δ₉(p,θ_e*)=0} needs a Gröbner/resultant elimination, which is the large
    step — but the determinant obstruction is gone.  The deg-2/3 Lean blocks (`GFL/HopfFold.lean`)
    discharge the Schur-reduced low-degree factors.
"""
import sympy as sp, time, pickle
t0 = time.time()
def log(m): print(f"[{time.time()-t0:6.1f}s] {m}", flush=True)

wn, Vg, Lf, Cf, Rf, Lg, Rg = sp.symbols('wn Vg Lf Cf Rf Lg Rg', positive=True)
Kpi, Kii, K_ad, Kp_pll, Ki_pll = sp.symbols('Kpi Kii K_ad Kp_pll Ki_pll', positive=True)
id_ref, iq_ref = sp.symbols('id_ref iq_ref', real=True)
i_d, i_q, v_cd, v_cq, i_gd, i_gq, xi_dc, xi_qc, eta, th = sp.symbols(
    'i_d i_q v_cd v_cq i_gd i_gq xi_dc xi_qc eta theta_e', real=True)
X = [i_d, i_q, v_cd, v_cq, i_gd, i_gq, xi_dc, xi_qc, eta, th]
c, s = sp.cos(th), sp.sin(th)
i_dc = c*i_d - s*i_q;  i_qc = s*i_d + c*i_q
v_cdc = c*v_cd - s*v_cq;  v_cqc = s*v_cd + c*v_cq
i_Cdc = c*(i_d-i_gd) - s*(i_q-i_gq);  i_Cqc = s*(i_d-i_gd) + c*(i_q-i_gq)
err_d = id_ref - i_dc;  err_q = iq_ref - i_qc
u_dc = Kpi*err_d + Kii*xi_dc - wn*Lf*i_qc + v_cdc - K_ad*i_Cdc
u_qc = Kpi*err_q + Kii*xi_qc + wn*Lf*i_dc + v_cqc - K_ad*i_Cqc
u_d = c*u_dc + s*u_qc;  u_q = -s*u_dc + c*u_qc
f = sp.Matrix([
    (u_d - v_cd - Rf*i_d + wn*Lf*i_q)/Lf, (u_q - v_cq - Rf*i_q - wn*Lf*i_d)/Lf,
    (i_d - i_gd + wn*Cf*v_cq)/Cf, (i_q - i_gq - wn*Cf*v_cd)/Cf,
    (v_cd - Vg - Rg*i_gd + wn*Lg*i_gq)/Lg, (v_cq - Rg*i_gq - wn*Lg*i_gd)/Lg,
    err_d, err_q, v_cqc, -Kp_pll*v_cqc - Ki_pll*eta])

J = f.jacobian(X)
C, S = sp.symbols('C S', real=True)
J = J.subs([(sp.cos(th), C), (sp.sin(th), S)])
lam = sp.symbols('lam')

cp = J.charpoly(lam)                       # Faddeev–LeVerrier — the working method
co = cp.all_coeffs()
log(f"general char poly a_k(x;p,C,S): op-counts {[sp.count_ops(x) for x in co]}")

# closed-form equilibrium x*(p,C,S):
ids = C*id_ref + S*iq_ref;  iqs = C*iq_ref - S*id_ref
vcd_s, vcq_s, igd_s, igq_s = list(sp.linsolve(
    [f[k].subs([(i_d, ids), (i_q, iqs)]) for k in [2, 3, 4, 5]], [v_cd, v_cq, i_gd, i_gq]))[0]
base = [(i_d, ids), (i_q, iqs), (v_cd, vcd_s), (v_cq, vcq_s), (i_gd, igd_s), (i_gq, igq_s), (eta, 0)]
xstar = list(sp.linsolve([f[0].subs(base), f[1].subs(base)], [xi_dc, xi_qc]))[0]
g = sp.simplify(S*vcd_s + C*vcq_s)
log(f"implicit-angle constraint  g(p,C,S) = v_cqc* = {g}")
log("(g = 0 defines θ_e*; with C²+S²=1.  a_1 = −trace is the first Hurwitz coeff.)")
print("\na_1 = -trace(J) (general) =", sp.factor(co[1]))
pickle.dump({'coeffs': [str(x) for x in co], 'g': str(g)}, open('/tmp/gfl_charpoly.pkl', 'wb'))
log("saved general char poly + θ_e* constraint to /tmp/gfl_charpoly.pkl")
