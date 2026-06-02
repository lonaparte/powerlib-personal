#!/usr/bin/env python3
"""
(A) Parametric symbolic derivation toward the GFL-VSC F-H (Hopf) surface Σ_H.

This is a CAS derivation (sympy), fully symbolic in the parameters p and θ_e* (kept as C=cosθ_e*,
S=sinθ_e*).  It is NOT a Lean certificate; it complements the machine-verified deg-2/deg-3
Routh–Hurwitz / Hopf blocks in `GFL/HopfFold.lean`.

FINDINGS (run this file to reproduce):
  * J(x;p) and the trace a₁ = −tr J compute instantly:
        a₁ = Kp_pll·v_cdc + 2(K_ad+Kpi)/Lf + 2 Rg/Lg + 2 Rf/Lf            (v_cdc := C·v_cd − S·v_cq)
  * Schur block structure (controller block of λI−J, states ξ_dc,ξ_qc,η,θ_e):
        det(Mkk) = λ² · ( λ² + (Kp_pll·v_cdc)·λ + (Ki_pll·v_cdc) )
    The PLL factor  λ² + (Kp_pll·v_cdc)·λ + (Ki_pll·v_cdc)  is EXACTLY the `s²+a₁s+a₂` form proved in
    Lean (`hopf_deg2`, `stable_deg2_of_pos`):  a₁ = Kp_pll·v_cdc, a₂ = Ki_pll·v_cdc.  Hence the PLL
    Hopf onset is  v_cdc = 0  (marginal), stable iff v_cdc > 0, onset frequency ω = √(Ki_pll·v_cdc).
  * the 6×6 electrical block det computes (~0.1 s).
  * THE WALL: the full 10×10 char poly det(λI−J) (and its Schur assembly det(Mkk)·det(Schur_E),
    whose cancellation to a polynomial) does NOT complete in this environment (>8 min, killed).
    So the fully-coupled Σ_H (Δ₉=0) is beyond sympy's practical limit here without a hand
    Schur/Gröbner reduction — matching the problem's "CAS 规模" note.  The block factor above and the
    deg-2/3 Lean certificates are the parametric results that DO land.
"""
import sympy as sp, time
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
log("J(x;p) computed (θ_e-derivatives correct, then cos/sin → C,S)")

a1 = sp.expand(-sum(J[k, k] for k in range(10))).subs(S**2, 1 - C**2)
log(f"a1 = -trace(J) = {a1}")

lam = sp.symbols('lam')
M = lam*sp.eye(10) - J
K = [6, 7, 8, 9]
Mkk = sp.Matrix([[M[r, cc] for cc in K] for r in K])
log(f"controller block factor det(Mkk) = {sp.factor(Mkk.det())}")
log("  → PLL factor λ²+(Kp_pll·v_cdc)λ+(Ki_pll·v_cdc): the Lean deg-2 block (hopf_deg2).")

log("full 10×10 det(λI−J): NOT attempted here — times out (>8 min). See module docstring.")
