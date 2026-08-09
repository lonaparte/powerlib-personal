"""GFM: bring omega_g and X_g to the same depth as V/Pref/Qref.
omega_g enters the angle equation additively (deltadot = om - dw), so
f_dw = -e1 and M1 = 0 -- structurally identical to the GFL case.
X_g enters Pe, Qe multiplicatively.
 (0) five-channel coupling table;
 (1) frozen-spectrum sensitivity d(Re lam)/du -> does B4 exist;
 (2) B2 tongue pred vs monodromy (3 sets, both channels);
 (3) B3-ii direct-forcing desync at resonance (M2, M5, both channels),
     compound events kept separate (DESYNC / E<=0 / solver).
Budget ~25 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event, Bform, Enom)
from scipy.integrate import solve_ivp
from scipy.linalg import eig as _eig
LOG = open('sweep20/chan45gfm.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def rhs_w(x, pr):
    y = rhs(x, pr).copy()
    y[0] -= pr.get('dw', 0.0)
    return y

def build(name, Xg):
    pr = mset(name, Xg=Xg)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    if q is None: return None
    P_H = q['Pref']
    def g(P):
        r = maxre_cx(dict(pr, Pref=P))
        return 1.0 if r is None else r
    Phi_ = min(0.95*Pm, 2.5*P_H)
    tt = 0.10
    if g(Phi_) > -tt:
        tt = max(0.3*abs(g(Phi_)), 0.02)
    lo2, hi2 = P_H, Phi_
    for _ in range(45):
        m = 0.5*(lo2+hi2)
        if g(m) > -tt: lo2 = m
        else: hi2 = m
    return dict(pr, Pref=0.5*(lo2+hi2), dw=0.0)

SETS = [('M3', 0.05, False), ('M2', 0.03, True), ('M5', 0.15, True)]
for name, Xg, do_desync in SETS:
    pr = build(name, Xg)
    if pr is None:
        out(f"{name}@{Xg}: no window"); continue
    st = equil(pr)
    A = jac(st, pr)
    lam = crit_mode(A)
    w0 = lam.imag; alpha = -lam.real
    ev0, dsad = escape_event(pr)
    ev, VL, VR = _eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev - lam)))
    qv = VR[:, k]; pv = VL[:, k]
    pv = pv/np.vdot(qv, pv)
    V0 = pr['V']; hq = 1e-6
    fs = {}
    for key in ('V', 'Pref', 'Qref', 'Xg'):
        b = pr[key]
        d = hq*max(abs(b), 1.0)
        fs[key] = (rhs(st, dict(pr, **{key: b+d}))
                   - rhs(st, dict(pr, **{key: b-d})))/(2*d)
    fs['dw'] = np.array([-1., 0., 0., 0.])
    qn = qv/np.linalg.norm(qv)
    out(f"{name}@{Xg}: P0={pr['Pref']:.4f} w0={w0:.3f} alpha={alpha:.4f} "
        f"|q|=({abs(qn[0]):.3f},{abs(qn[1]):.3f},{abs(qn[2]):.3f},"
        f"{abs(qn[3]):.3f})")
    out("  coupling |<p,f_u>|: " + "  ".join(
        f"{k}={abs(np.vdot(pv, v)):.4g}" for k, v in fs.items()))
    sens = {}
    for key in ('V', 'Pref', 'Qref', 'Xg'):
        b = pr[key]; d = 1e-4*max(abs(b), 1.0)
        try:
            a1 = crit_mode(jac(equil(dict(pr, **{key: b+d})),
                               dict(pr, **{key: b+d}))).real
            a2 = crit_mode(jac(equil(dict(pr, **{key: b-d})),
                               dict(pr, **{key: b-d}))).real
            sens[key] = abs((a1-a2)/(2*d))
        except Exception:
            sens[key] = float('nan')
    # dw: equilibrium unchanged except it is absorbed by the swing eq?
    # deltadot = om - dw = 0 at equilibrium -> om* = dw, which changes
    # the damping term D*om -> genuine shift.  measure numerically.
    def equil_w(prq):
        from scipy.optimize import fsolve
        def res(x): return rhs_w(x, prq)
        z, info, ier, _ = fsolve(res, st.copy(), full_output=True)
        return z if ier == 1 and np.max(np.abs(res(z))) < 1e-9 else None
    d = 1e-4
    s1 = equil_w(dict(pr, dw=d)); s2 = equil_w(dict(pr, dw=-d))
    if s1 is not None and s2 is not None:
        a1 = crit_mode(jac(s1, dict(pr, dw=d))).real
        a2 = crit_mode(jac(s2, dict(pr, dw=-d))).real
        sens['dw'] = abs((a1-a2)/(2*d))
    out("  |d(Re lam)/du|: " + "  ".join(f"{k}={v:.4g}"
                                          for k, v in sens.items()))
    # ---- (2) tongues ----
    wp = 2*w0; Tdp = 2*math.pi/wp
    for key in ('dw', 'Xg'):
        fu = fs[key]
        if key == 'Xg':
            b = pr['Xg']; d = hq*max(abs(b), 1.0)
            M1 = (jac(st, dict(pr, Xg=b+d))
                  - jac(st, dict(pr, Xg=b-d)))/(2*d)
        else:
            M1 = np.zeros((4, 4))
        hF = np.linalg.solve(2j*w0*np.eye(4) - A, fu)
        pi_eff = (np.vdot(pv, M1 @ np.conj(qv))
                  + np.vdot(pv, Bform(st, pr, hF, np.conj(qv))))
        if abs(pi_eff) < 1e-12:
            out(f"  TONGUE u={key}: |pi|~0, tongue absent"); continue
        eps_t = 2*alpha/abs(pi_eff)
        def strobe(x0, eps, kk):
            def f(t, y):
                x = y[:4]
                qq = dict(pr, **{kk: pr.get(kk, 0.0)
                                 + eps*math.cos(wp*t)})
                Phi = y[4:].reshape(4, 4)
                return np.concatenate([rhs_w(x, qq),
                                       (jac(x, qq) @ Phi).ravel()])
            s = solve_ivp(f, (0, Tdp),
                          np.concatenate([x0, np.eye(4).ravel()]),
                          method='DOP853', rtol=1e-10, atol=1e-12)
            return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
        def newton_fp(xg0, eps, kk, itmax=25):
            x = xg0.copy(); M = None
            for it in range(itmax):
                xT, M = strobe(x, eps, kk)
                Fx = xT - x
                if np.max(np.abs(Fx)) < 1e-10:
                    return x, M, True
                try:
                    dx = np.linalg.solve(M - np.eye(4), -Fx)
                except np.linalg.LinAlgError:
                    return x, M, False
                n = np.max(np.abs(dx))
                if n > 0.3: dx *= 0.3/n
                x = x + dx
            return x, M, np.max(np.abs(Fx)) < 1e-8
        def stab(e):
            xn, Mn, okn = newton_fp(st.copy(), e, key)
            if not okn: return False
            return float(np.max(np.abs(np.linalg.eigvals(Mn)))) < 1.0
        cap = 0.5*pr['Xg'] if key == 'Xg' else 50.0
        elo, ehi = 0.6*eps_t, min(1.6*eps_t, cap)
        n = 0
        while not stab(elo) and n < 6:
            elo /= 1.7; n += 1
        n = 0
        while stab(ehi) and ehi < cap and n < 6:
            ehi = min(ehi*1.7, cap); n += 1
        if stab(elo) and not stab(ehi):
            for _ in range(12):
                em = 0.5*(elo+ehi)
                if stab(em): elo = em
                else: ehi = em
            e_meas = 0.5*(elo+ehi)
            extra = (f" = {e_meas/pr['Xg']*100:.3f}% of Xg" if key == 'Xg'
                     else f" = {e_meas/(2*math.pi)*1e3:.2f} mHz")
            out(f"  TONGUE u={key}: |pi|={abs(pi_eff):.4g} "
                f"pred={eps_t:.4e} meas={e_meas:.4e}{extra} "
                f"err={(eps_t-e_meas)/e_meas*100:+.2f}% "
                f"[{time.time()-T0:.0f}s]")
        else:
            out(f"  TONGUE u={key}: bracket failed (pred {eps_t:.3e})")
    if not do_desync:
        continue
    # ---- (3) B3-ii direct desync at resonance ----
    for key in ('dw', 'Xg'):
        wpp = w0
        base = pr.get(key, 0.0)
        def probe(a, T=60.0):
            def f(t, x):
                return rhs_w(x, dict(pr,
                                     **{key: base + a*math.cos(wpp*t)}))
            def e_d(t, x): return x[0] - dsad
            def e_E(t, x):
                return (Enom - pr['mq']*(x[3] - pr['Qref'])) - 1e-3
            e_d.terminal = True; e_d.direction = 1
            e_E.terminal = True; e_E.direction = -1
            s = solve_ivp(f, (0, T), st.copy(), method='DOP853',
                          rtol=1e-9, atol=1e-12, events=(e_d, e_E))
            gd = len(s.t_events[0]) > 0; gE = len(s.t_events[1]) > 0
            if gd and gE:
                return 'DESYNC' if s.t_events[0][0] < s.t_events[1][0] \
                    else 'E<=0'
            if gd: return 'DESYNC'
            if gE: return 'E<=0'
            if s.status < 0: return 'SOLVER'
            return None
        cap = 0.45*pr['Xg'] if key == 'Xg' else 20.0
        alo, ahi = (1e-3*pr['Xg'] if key == 'Xg' else 1e-2), None
        ahi = 2*alo
        n = 0
        while probe(ahi) is None and ahi < cap and n < 20:
            alo = ahi; ahi = min(ahi*1.5, cap); n += 1
        if probe(min(ahi, cap)) is None:
            extra = (f"{cap/pr['Xg']*100:.0f}% of Xg" if key == 'Xg'
                     else f"{cap:.1f} rad/s")
            out(f"  DESYNC u={key}: none up to {extra} "
                f"[{time.time()-T0:.0f}s]")
            continue
        ahi = min(ahi, cap)
        for _ in range(13):
            am = 0.5*(alo+ahi)
            if probe(am) is not None: ahi = am
            else: alo = am
        ac = 0.5*(alo+ahi)
        kind = probe(ahi)
        extra = (f" = {ac/pr['Xg']*100:.3f}% of Xg" if key == 'Xg'
                 else f" = {ac/(2*math.pi)*1e3:.1f} mHz "
                      f"(phase amp {math.degrees(ac/wpp):.4f} deg)")
        out(f"  DESYNC u={key}: threshold {ac:.4e}{extra} type={kind} "
            f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
