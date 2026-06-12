#!/usr/bin/env python3
"""
T3 re-examined at the PHYSICAL power angle θ_e* ≠ 0 (NOT the θ_e*=0 slice used in LFilterT3.lean).

User's objection: PLL lock ⇒ v_cqc(x*)=0 ⇒ θ_e* = arg(V_PCC); with real power through Lg this is
nonzero (grows with load: SCR↓ ⇒ |θ_e*|↑).  On the TRUE fixed point, is the clean (Kp_P−Kp_Q)
factorisation of D = Σ_iq − Σ_id still valid, or is it an artifact of θ_e*=0?

Strategy (tractable where T3_theta.py timed out): keep θ_e (C,S), P_ref, Kp_P, Kp_Q SYMBOLIC,
fix the background params to EXACT rationals.  The `rem` block is 1×1 so the Schur complement is a
rank-1 update — the cost was charpoly+cancel over {C,S}∪12 params, now reduced to 5 live symbols.

Two questions, answered exactly:
  (Q1) does (Kp_P − Kp_Q) still divide numerator(D) at general θ_e*?  (factor survives vs polluted)
  (Q2) is D|_{Kp_P=Kp_Q} ≡ 0 (my θ_e*=0 claim) or ∝ sin θ_e* (vanishing only at θ_e*=0)?
"""
import sympy as sp, time
t0 = time.time()
def log(m): print(f"[{time.time()-t0:6.1f}s] {m}", flush=True)

# --- symbolic: power angle (C,S), load (P_ref), and the two outer gains ---
C, S, P_ref, Kp_P, Kp_Q = sp.symbols('C S P_ref Kp_P Kp_Q', real=True)
i_d, i_q, eta, th = sp.symbols('i_d i_q eta theta_e', real=True)
X = [i_d, i_q, eta, th]

# --- background params: EXACT rationals (generic, lossy, weak grid SCR≈ Vg^2/(P*Lg*wn)) ---
Vg = sp.Integer(1); wn = sp.Integer(1)
Lf = sp.Rational(1, 20); Rf = sp.Rational(1, 200)     # filter
Lg = sp.Rational(3, 10); Rg = sp.Rational(3, 100)     # weak grid
Kpi = sp.Rational(1, 2)                                # inner P gain
Kp_pll = sp.Integer(2); Ki_pll = sp.Integer(20)        # PLL
Q_ref = sp.Integer(0)                                  # user's slice: i_q* = 0

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
               v_cqc,
               -Kp_pll*v_cqc - Ki_pll*eta])
J = F.jacobian(X)
log("J built (symbolic θ_e, P_ref, Kp_P, Kp_Q; rational background)")

# equilibrium currents from full-model integrators; θ_e KEPT symbolic (NOT 0):
ID = P_ref/(sp.Rational(3, 2)*Vg); IQ = -Q_ref/(sp.Rational(3, 2)*Vg)
sub = [(i_d, ID), (i_q, IQ), (eta, 0)]
Je = sp.Matrix(4, 4, lambda i, j:
               sp.cancel(J[i, j].subs(sub).subs([(sp.sin(th), S), (sp.cos(th), C)])))
log("Je(C,S,P_ref,Kp_P,Kp_Q) formed — θ_e* GENERAL, no θ_e=0 substitution")

sm = sp.symbols('lam')
def Sig(keep):
    rem = [k for k in range(4) if k not in keep]
    M = Je[keep, keep] - Je[keep, rem]*Je[rem, rem].inv()*Je[rem, keep]
    co = sp.Matrix(M).charpoly(sm).all_coeffs()      # s³ + A s² + B s + Cc
    return sp.cancel(co[1]*co[2] - co[3])            # Σ = A·B − Cc

Diq = Sig([1, 2, 3]); log("Σ_iq done")
Did = Sig([0, 2, 3]); log("Σ_id done")
D = sp.cancel(Diq - Did); log(f"D formed, ops={sp.count_ops(D)}")

num = sp.fraction(sp.together(D))[0]
q, r = sp.div(sp.expand(num), (Kp_P - Kp_Q), Kp_P)
print("\n========== (Q1) does (Kp_P − Kp_Q) divide numerator(D) at general θ_e*? ==========")
print("   remainder == 0 :", sp.expand(r) == 0)

print("\n========== (Q2) D at SYMMETRIC gains Kp_P = Kp_Q, general θ_e* ==========")
Dsym = sp.cancel(D.subs(Kp_Q, Kp_P))
print("   D|_{Kp_P=Kp_Q} ≡ 0 ? :", sp.simplify(Dsym) == 0)
print("   D|_{Kp_P=Kp_Q} at θ_e*=0  (S=0, C=1) :", sp.simplify(Dsym.subs([(S, 0), (C, 1)])))
Dsym_num = sp.fraction(sp.together(Dsym))[0]
print("\n   numerator(D|_{Kp_P=Kp_Q}), factored:")
sp.pprint(sp.factor(Dsym_num))

# Is the symmetric-gain residual ∝ sin θ_e*?  Evaluate along the unit circle C=cosθ, S=sinθ.
print("\n========== rel. growth of D|_{Kp_P=Kp_Q} with the power angle θ_e* ==========")
print("   (rel = |D_sym| / |Σ_id| at Kp_P=Kp_Q=1/50, P_ref chosen so i_d*=2/3·P_ref)")
Kpv = sp.Rational(1, 50)
for deg in [0, 2, 5, 10, 20, 30, 45]:
    th_val = sp.rad(deg)
    Cv = sp.cos(th_val); Sv = sp.sin(th_val)
    # pick P_ref consistent with this angle via the leading load-flow relation sinθ ≈ Pf·Lg·wn/Vg^2:
    Pv = sp.nsimplify(float(Sv) * float(Vg)**2 / (float(Lg)*float(wn)) / 1.5)  # rough; angle is what matters
    subn = [(Kp_P, Kpv), (Kp_Q, Kpv), (C, Cv), (S, Sv), (P_ref, Pv)]
    dn = float(sp.N(Dsym.subs(subn)))
    did = float(sp.N(Did.subs([(Kp_P, Kpv), (Kp_Q, Kpv), (C, Cv), (S, Sv), (P_ref, Pv)])))
    rel = abs(dn)/abs(did) if did != 0 else float('nan')
    print(f"   θ_e*={deg:3d}°  S={float(Sv):+.4f}   D_sym={dn:+.6e}   rel={rel:.4%}")
log("done")
