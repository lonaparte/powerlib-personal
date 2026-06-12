#!/usr/bin/env python3
"""Numerical cross-validation of the formal claims against the §3-§4 GFL-VSC model.

This implements the *problem's* 9-state model (§3 algebra, §4 vector field) verbatim,
builds an equilibrium analytically from the equilibrium relations, verifies the
inner field vanishes there, and checks the spectral content of Theorems A/B/C.

NOTE: this is a different (9-state, outer-loop + swing) model from
work-sync/.../models.py (10-state, frozen current ref, no swing), so the absolute
number i_d* depends on P_ref; what we verify are the *structural* claims that the
formal proof captures (Lemma 0 / Cor 0a, Thm A/B/C), exactly as in §7.
"""
import numpy as np

class P:
    # filter / line (Lf,Lg,Rf,Rg>0); shared physical scale with the project model
    Lf, Lg, Rf, Rg = 1.0e-3, 1.5e-3, 0.1, 0.0471
    fn = 50.0
    wn = 2*np.pi*fn
    Vg = 380.0*np.sqrt(2.0/3.0)          # peak phase voltage ~310.27 V
    # current loop PI ; PLL PI
    Kpi, Kii = 1.26, 126.0
    Kp_pll, Ki_pll = 0.0902, 1.289
    # outer P/Q loop PI (Kp_*,Ki_*>0)
    Kp_P, Ki_P = 1.0e-4, 1.0e-2
    Kp_Q, Ki_Q = 1.0e-4, 1.0e-2
    # setpoints (P_ref>0)
    Q_ref = 0.0
    P_ref = 1.5*Vg*80.0                  # so that i_d* = P_ref/(1.5 Vg) = 80 A exactly
    # swing
    H, D, Sn = 5.0, 1.0, 100e3

    @property
    def Ltot(self): return self.Lf+self.Lg
    @property
    def Rtot(self): return self.Rf+self.Rg
    @property
    def g(self):    return (self.Lf*self.Rg - self.Rf*self.Lg)/self.Ltot
    @property
    def kappa(self): return self.wn/(2*self.H*self.Sn)
    @property
    def b(self):     return self.D/(2*self.H)
    @property
    def beta(self):  return self.wn/(2*self.H)

def algebraics(y, p):
    """§3 algebraic definitions; returns dict of all intermediates."""
    i_d, i_q, xi_dc, xi_qc, eta, th, xi_P, xi_Q, dw = y
    c, s = np.cos(th), np.sin(th)
    wg = p.wn + dw
    Ltot, g = p.Ltot, p.g
    P_meas = 1.5*p.Vg*i_d
    Q_meas = -1.5*p.Vg*i_q
    e_P = p.P_ref - P_meas
    e_Q = p.Q_ref - Q_meas
    i_d_ref = p.Kp_P*e_P + p.Ki_P*xi_P
    i_q_ref = -(p.Kp_Q*e_Q + p.Ki_Q*xi_Q)
    i_dc = c*i_d - s*i_q
    i_qc = s*i_d + c*i_q
    e_d = i_d_ref - i_dc
    e_q = i_q_ref - i_qc
    K_d = p.Kpi*e_d + p.Kii*xi_dc - p.wn*p.Lf*i_qc + (p.Lf/Ltot)*c*p.Vg + g*i_dc
    K_q = p.Kpi*e_q + p.Kii*xi_qc + p.wn*p.Lf*i_dc + (p.Lf/Ltot)*s*p.Vg + g*i_qc
    u_dc = (Ltot/p.Lf)*K_d
    u_qc = (Ltot/p.Lf)*K_q
    u_d = c*u_dc + s*u_qc
    u_q = -s*u_dc + c*u_qc
    v_d = (p.Lg/Ltot)*u_d + (p.Lf/Ltot)*p.Vg + g*i_d
    v_q = (p.Lg/Ltot)*u_q + g*i_q
    v_cqc = s*v_d + c*v_q
    return dict(c=c, s=s, wg=wg, e_P=e_P, e_Q=e_Q, e_d=e_d, e_q=e_q,
               i_dc=i_dc, i_qc=i_qc, u_d=u_d, u_q=u_q, v_cqc=v_cqc, P_meas=P_meas)

def F(y, p, variant):
    """§4 vector field. variant in {'U','S'}."""
    i_d, i_q, xi_dc, xi_qc, eta, th, xi_P, xi_Q, dw = y
    a = algebraics(y, p)
    Ltot, Rtot = p.Ltot, p.Rtot
    F1 = (a['u_d'] - p.Vg - Rtot*i_d + Ltot*a['wg']*i_q)/Ltot
    F2 = (a['u_q']            - Rtot*i_q - Ltot*a['wg']*i_d)/Ltot
    F3 = a['e_d']
    F4 = a['e_q']
    F5 = a['v_cqc']
    F6 = -p.Kp_pll*a['v_cqc'] - p.Ki_pll*eta - dw
    F7 = a['e_P']
    F8 = a['e_Q']
    F9 = 0.0 if variant == 'U' else (p.kappa*a['e_P'] - p.b*dw)
    return np.array([F1, F2, F3, F4, F5, F6, F7, F8, F9])

def equilibrium(dw, p):
    """Analytic equilibrium z*(dw) of F_inner (works for any dw; §5/W3 branch)."""
    i_d = p.P_ref/(1.5*p.Vg)            # Lemma 0
    i_q = -p.Q_ref/(1.5*p.Vg)
    wg = p.wn + dw
    Ltot, g = p.Ltot, p.g
    # F1=F2=0  ->  required grid-frame controller output
    u_d = p.Vg + p.Rtot*i_d - Ltot*wg*i_q
    u_q =        p.Rtot*i_q + Ltot*wg*i_d
    v_d = (p.Lg/Ltot)*u_d + (p.Lf/Ltot)*p.Vg + g*i_d
    v_q = (p.Lg/Ltot)*u_q + g*i_q
    th = np.arctan2(-v_q, v_d)           # F5: s*v_d + c*v_q = 0
    c, s = np.cos(th), np.sin(th)
    eta = -dw/p.Ki_pll                   # F6 with v_cqc=0
    i_dc = c*i_d - s*i_q
    i_qc = s*i_d + c*i_q
    xi_P = i_dc/p.Ki_P                   # F3: i_d_ref = i_dc, e_P=0
    xi_Q = -i_qc/p.Ki_Q                  # F4: i_q_ref = i_qc, e_Q=0
    u_dc = c*u_d - s*u_q                 # inverse rotation
    u_qc = s*u_d + c*u_q
    K_d = (p.Lf/Ltot)*u_dc
    K_q = (p.Lf/Ltot)*u_qc
    xi_dc = (K_d + p.wn*p.Lf*i_qc - (p.Lf/Ltot)*c*p.Vg - g*i_dc)/p.Kii  # e_d=0
    xi_qc = (K_q - p.wn*p.Lf*i_dc - (p.Lf/Ltot)*s*p.Vg - g*i_qc)/p.Kii  # e_q=0
    return np.array([i_d, i_q, xi_dc, xi_qc, eta, th, xi_P, xi_Q, dw])

def jac(y, p, variant, h=1e-6):
    n = len(y); J = np.zeros((n, n))
    for k in range(n):
        hk = h*(abs(y[k])+1.0)
        yp = y.copy(); yp[k] += hk
        ym = y.copy(); ym[k] -= hk
        J[:, k] = (F(yp, p, variant) - F(ym, p, variant))/(2*hk)
    return J

def main():
    p = P()
    ok = True
    print(f"params: kappa={p.kappa:.6e}  b={p.b:.6f}  beta={p.beta:.6f}  Vg={p.Vg:.4f}")
    print(f"        -D/(2H) = {-p.D/(2*p.H):.6f}   i_d* target = {p.P_ref/(1.5*p.Vg):.10f}\n")

    # --- Lemma 0 / Cor 0a : i_d* pinned & constant in dw ; residual ~ 0 ---
    print("== Lemma 0 / Cor 0a : Power Lock ==")
    idstar = []
    for dw in [0.0, 5.0, 20.0, 50.0, 100.0]:
        z = equilibrium(dw, p)
        res = np.linalg.norm(F(z, p, 'U')[:8])     # inner residual
        idstar.append(z[0])
        print(f"  dw={dw:6.1f}  ||F_inner||={res:.2e}  i_d*={z[0]:.12f}  "
              f"e_P={algebraics(z,p)['e_P']:.2e}")
        ok &= res < 1e-6
    spread = max(idstar)-min(idstar)
    print(f"  i_d* spread over dw = {spread:.3e}  (K = dP_meas/dd = 1.5*Vg*spread/Δd ~ 0)")
    ok &= spread < 1e-9
    ok &= abs(idstar[0] - p.P_ref/(1.5*p.Vg)) < 1e-9

    # --- Theorem A : Variant U has exactly one zero eigenvalue ; last row 0 ---
    print("\n== Theorem A : zero eigenvalue (Variant U) ==")
    z0 = equilibrium(0.0, p)
    JU = jac(z0, p, 'U')
    evU = np.linalg.eigvals(JU)
    nzero = int(np.sum(np.abs(evU) < 1e-6))
    lastrow = np.linalg.norm(JU[8, :])
    e9JU = np.linalg.norm(JU[8, :])       # e9^T J = last row
    print(f"  #|eig|<1e-6 = {nzero}   ||last row (rho^T|j99)|| = {lastrow:.2e}")
    print(f"  smallest |eig| = {np.min(np.abs(evU)):.2e}")
    ok &= (nzero == 1) and (lastrow < 1e-9)

    # --- Theorem B : Variant S slow eigenvalue = -b ; Schur term 0 ---
    print("\n== Theorem B : slow eigenvalue -b = -D/(2H) (Variant S) ==")
    for (H, D) in [(2,.5),(5,.5),(5,1),(5,2),(10,1),(3,.3),(8,4)]:
        p.H, p.D = H, D
        zS = equilibrium(0.0, p)          # dw*=0 (Cor 0b)
        JS = jac(zS, p, 'S')
        A = JS[:8, :8]; cvec = JS[:8, 8]; rho = JS[8, :8]; j99 = JS[8, 8]
        ev = np.linalg.eigvals(JS)
        # slow eigenvalue = real eigenvalue closest to -b
        real_ev = ev[np.abs(ev.imag) < 1e-6].real
        lam_slow = real_ev[np.argmin(np.abs(real_ev - (-D/(2*H))))]
        schur = rho @ np.linalg.solve(A, cvec)     # rho^T A^{-1} c
        print(f"  H={H:<4} D={D:<4} lam_slow={lam_slow:+.6f}  -D/2H={-D/(2*H):+.6f}  "
              f"|diff|={abs(lam_slow+D/(2*H)):.1e}  rho^T A^-1 c={schur:+.2e}  "
              f"rho[0]={rho[0]:+.4e} (-1.5kVg={-1.5*p.kappa*p.Vg:+.4e}) j99={j99:+.4f}")
        ok &= abs(lam_slow + D/(2*H)) < 1e-3
        ok &= abs(schur) < 1e-6
    p.H, p.D = 5.0, 1.0

    # --- Theorem C : oscillation onset ; companion-matrix eigenvalues ---
    print("\n== Theorem C : oscillation onset (companion matrix) ==")
    b, beta = p.b, p.beta
    print(f"  b={b}  beta={beta}  threshold beta*Ks > b^2/4 = {b**2/4:.4e}")
    for Ks in [0.0, 0.01, 0.05, 0.2, 1.0]:
        s = beta*Ks
        M = np.array([[0.0, 1.0], [-s, -b]])
        ev = np.linalg.eigvals(M)
        disc = b**2 - 4*s
        if Ks == 0.0:
            real_pair = sorted(ev.real)
            print(f"  Ks=0    eig={real_pair}  (expect 0,-b={-b})")
            ok &= np.allclose(sorted(ev.real), sorted([0.0, -b]), atol=1e-9) and np.all(np.abs(ev.imag) < 1e-12)
        else:
            osc = s > b**2/4
            w = np.sqrt(max(s - b**2/4, 0.0))
            re = ev.real[0]
            print(f"  Ks={Ks:<5} osc={osc!s:5} Re={re:+.4f} (-b/2={-b/2:+.4f}) "
                  f"w_osc={w:.4f} f={w/(2*np.pi):.4f}Hz  numpy_imag={abs(ev.imag[0]):.4f}")
            if osc:
                ok &= abs(re + b/2) < 1e-9
                ok &= abs(abs(ev.imag[0]) - w) < 1e-6

    print("\n" + ("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
