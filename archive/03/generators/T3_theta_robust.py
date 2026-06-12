#!/usr/bin/env python3
"""
Robustness of the reduced-model finding (D|_{Kp_P=Kp_Q} ≡ 0 at general θ_e*):
  (a) hold for general Q_ref too (not only the i_q*=0 slice)?
  (b) is θ_e GENUINELY active — i.e. does G = D/(Kp_P−Kp_Q) actually depend on θ_e?
      (rules out the trivial "θ_e decoupled, so of course nothing changes" explanation)
  (c) sanity: Σ_iq and Σ_id each DO depend on θ_e; it's only their DIFFERENCE that is gain-driven.
"""
import sympy as sp, time
t0 = time.time()
def log(m): print(f"[{time.time()-t0:6.1f}s] {m}", flush=True)

C, S, P_ref, Q_ref, Kp_P, Kp_Q = sp.symbols('C S P_ref Q_ref Kp_P Kp_Q', real=True)
i_d, i_q, eta, th = sp.symbols('i_d i_q eta theta_e', real=True)
X = [i_d, i_q, eta, th]
Vg = sp.Integer(1); wn = sp.Integer(1)
Lf = sp.Rational(1, 20); Rf = sp.Rational(1, 200)
Lg = sp.Rational(3, 10); Rg = sp.Rational(3, 100)
Kpi = sp.Rational(1, 2); Kp_pll = sp.Integer(2); Ki_pll = sp.Integer(20)

Lt = Lf + Lg; Rt = Rf + Rg; gam = (Lf*Rg - Rf*Lg)/Lt
c, s = sp.cos(th), sp.sin(th)
err_P = P_ref - sp.Rational(3, 2)*Vg*i_d
err_Q = Q_ref + sp.Rational(3, 2)*Vg*i_q
i_dc = c*i_d - s*i_q; i_qc = s*i_d + c*i_q
err_d = Kp_P*err_P - i_dc; err_q = -Kp_Q*err_Q - i_qc
u_dc = (Lt/Lf)*(Kpi*err_d - wn*Lf*i_qc + (Lf/Lt)*c*Vg + gam*i_dc)
u_qc = (Lt/Lf)*(Kpi*err_q + wn*Lf*i_dc + (Lf/Lt)*s*Vg + gam*i_qc)
u_d = c*u_dc + s*u_qc; u_q = -s*u_dc + c*u_qc
vPCCd = (Lg/Lt)*u_d + (Lf/Lt)*Vg + gam*i_d; vPCCq = (Lg/Lt)*u_q + gam*i_q
v_cqc = s*vPCCd + c*vPCCq
F = sp.Matrix([(u_d - Vg - Rt*i_d + Lt*wn*i_q)/Lt,
               (u_q - Rt*i_q - Lt*wn*i_d)/Lt,
               v_cqc, -Kp_pll*v_cqc - Ki_pll*eta])
J = F.jacobian(X)
ID = P_ref/(sp.Rational(3, 2)*Vg); IQ = -Q_ref/(sp.Rational(3, 2)*Vg)
sub = [(i_d, ID), (i_q, IQ), (eta, 0)]
Je = sp.Matrix(4, 4, lambda i, j:
               sp.cancel(J[i, j].subs(sub).subs([(sp.sin(th), S), (sp.cos(th), C)])))
log("Je formed (general Q_ref, general θ_e)")
sm = sp.symbols('lam')
def Sig(keep):
    rem = [k for k in range(4) if k not in keep]
    M = Je[keep, keep] - Je[keep, rem]*Je[rem, rem].inv()*Je[rem, keep]
    co = sp.Matrix(M).charpoly(sm).all_coeffs()
    return sp.cancel(co[1]*co[2] - co[3])
Diq = Sig([1, 2, 3]); Did = Sig([0, 2, 3])
D = sp.cancel(Diq - Did); log(f"D formed ops={sp.count_ops(D)}")

# (a) general Q_ref:
Dsym = sp.simplify(D.subs(Kp_Q, Kp_P))
print("\n(a) D|_{Kp_P=Kp_Q} ≡ 0 for GENERAL Q_ref and general θ_e* ? :", Dsym == 0)

# (b) is G = D/(Kp_P−Kp_Q) θ_e-dependent?  diff wrt C and S, evaluate generically.
num = sp.fraction(sp.together(D))[0]
G = sp.cancel(sp.div(sp.expand(num), (Kp_P - Kp_Q), Kp_P)[0])
dG_dS = sp.diff(G, S)
testpt = [(C, sp.Rational(4, 5)), (S, sp.Rational(3, 5)), (P_ref, sp.Rational(1, 2)),
          (Q_ref, sp.Rational(1, 7)), (Kp_P, sp.Rational(1, 50)), (Kp_Q, sp.Rational(1, 30))]
print("(b) ∂G/∂S at a generic point (≠0 ⇒ θ_e genuinely active):",
      sp.N(dG_dS.subs(testpt)))
print("    G at θ_e=0 (S=0,C=1) vs at θ_e=30° — different ⇒ angle matters:")
print("       G|_{θ=0}  =", sp.N(G.subs([(S, 0), (C, 1), (P_ref, sp.Rational(1,2)),
      (Q_ref, sp.Rational(1,7)), (Kp_P, sp.Rational(1,50)), (Kp_Q, sp.Rational(1,30))])))
print("       G|_{θ=30°}=", sp.N(G.subs([(S, sp.Rational(1,2)), (C, sp.sqrt(3)/2),
      (P_ref, sp.Rational(1,2)), (Q_ref, sp.Rational(1,7)), (Kp_P, sp.Rational(1,50)),
      (Kp_Q, sp.Rational(1,30))])))

# (c) Σ_iq, Σ_id individually depend on θ_e (so the cancellation in the difference is nontrivial):
pt0 = [(S, 0), (C, 1), (P_ref, sp.Rational(1,2)), (Q_ref, 0), (Kp_P, sp.Rational(1,50)), (Kp_Q, sp.Rational(1,50))]
pt3 = [(S, sp.Rational(1,2)), (C, sp.sqrt(3)/2), (P_ref, sp.Rational(1,2)), (Q_ref, 0),
       (Kp_P, sp.Rational(1,50)), (Kp_Q, sp.Rational(1,50))]
print("\n(c) at SYMMETRIC gains Kp_P=Kp_Q=1/50, Q_ref=0:")
print("    Σ_iq|_{θ=0}  =", sp.N(Diq.subs(pt0)), "   Σ_id|_{θ=0}  =", sp.N(Did.subs(pt0)))
print("    Σ_iq|_{θ=30°}=", sp.N(Diq.subs(pt3)), "   Σ_id|_{θ=30°}=", sp.N(Did.subs(pt3)))
print("    ⇒ each Σ moves with θ_e, but Σ_iq−Σ_id stays 0 at symmetric gains.")
log("done")
