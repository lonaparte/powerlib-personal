"""GFM exhaustive closure of the remaining mechanism slots.
  D: 2:1 parametric tongue — pump V at 2*w_mode at margin points of
     M1/M2; Floquet threshold of the forced response; consequence check
     (supercritical => expect bounded, no escape).
  E: erosion of the velocity-kick escape threshold by sustained V
     oscillation (resonant at w_mode, off-resonant 0.7*w_mode):
     dwc(eps_bg)/dwc(0) for eps_bg in {0.5%, 1%, 2%} — the priority
     "oscillation x transient" cross term.
  F: slow Pref oscillation dipping through the light-load Hopf boundary
     P_H: delayed onset, bounded amplitude, no escape (supercritical).
Usage: python gfmcases.py {D|E|F}
"""
import sys
MODE = sys.argv[1]
import math, numpy as np, time, os
from scipy.integrate import solve_ivp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    simulate, escape_event, mset, fold)
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/gfm-{MODE}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def build(name, target=0.10):
    pr = mset(name)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    if q is None:
        return None
    P_H = q['Pref']
    # margin point above P_H (stable side): Re = -target
    def g(P):
        r = maxre_cx(dict(pr, Pref=P))
        return 1.0 if r is None else r
    Phi_ = min(0.95*Pm, 2.5*P_H)
    tt = target
    if g(Phi_) > -tt:
        tt = max(0.3*abs(g(Phi_)), 0.02)
    lo2, hi2 = P_H, Phi_
    for _ in range(45):
        m = 0.5*(lo2+hi2)
        if g(m) > -tt: lo2 = m
        else: hi2 = m
    P0 = 0.5*(lo2+hi2)
    prm = dict(pr, Pref=P0)
    st = equil(prm)
    lam = crit_mode(jac(st, prm))
    return dict(pr=prm, st=st, P_H=P_H, Pm=Pm, alpha=-lam.real,
                w0=lam.imag, target=tt)

def strobe_var(x0, pr, eps, wp, Td):
    def f(t, y):
        x = y[:4]
        qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wp*t)))
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, qq), (jac(x, qq) @ Phi).ravel()])
    y0 = np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-10, atol=1e-12)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)

def newton_fp(xg, pr, eps, wp, Td, itmax=25):
    x = xg.copy(); M = None
    for it in range(itmax):
        xT, M = strobe_var(x, pr, eps, wp, Td)
        Fx = xT - x
        if np.max(np.abs(Fx)) < 1e-10:
            return x, M, True
        try:
            dx = np.linalg.solve(M - np.eye(4), -Fx)
        except np.linalg.LinAlgError:
            return x, M, False
        n = np.max(np.abs(dx))
        if n > 0.3:
            dx *= 0.3/n
        x = x + dx
    return x, M, np.max(np.abs(Fx)) < 1e-8

# ---------------------- D: 2:1 parametric tongue --------------------------
if MODE == 'D':
    for name in ('M1', 'M2'):
        b = build(name)
        if b is None:
            out(f"{name}: no Hopf boundary found — skip")
            continue
        pr, st, w0, alpha = b['pr'], b['st'], b['w0'], b['alpha']
        out(f"{name}: P_H={b['P_H']:.4f} P0={pr['Pref']:.4f} "
            f"alpha={alpha:.4f} w0={w0:.4f} pump 2*w0={2*w0:.4f}")
        wp = 2.0*w0
        Td = 2*math.pi/wp
        xL = st.copy()
        eps = 0.0
        deps = 2e-3
        cross = None
        hist = []
        while eps < 0.10:
            e_try = eps + deps
            xn, Mn, okn = newton_fp(xL.copy(), pr, e_try, wp, Td)
            if not okn:
                deps *= 0.5
                if deps < 1e-5:
                    out(f"  stall at eps={eps:.4e}")
                    break
                continue
            mu = np.linalg.eigvals(Mn)
            am = float(np.max(np.abs(mu)))
            k = int(np.argmax(np.abs(mu)))
            hist.append((e_try, am, mu[k]))
            if am > 1.0:
                elo, ehi = eps, e_try
                xb = xL.copy()
                for _ in range(12):
                    em = 0.5*(elo+ehi)
                    xm, Mm, okm = newton_fp(xb.copy(), pr, em, wp, Td)
                    if not okm:
                        ehi = em; continue
                    if float(np.max(np.abs(np.linalg.eigvals(Mm)))) > 1.0:
                        ehi = em
                    else:
                        elo = em; xb = xm
                mu_at = hist[-1][2]
                typ = ('PD' if abs(mu_at.imag) < 5e-2 and mu_at.real < 0
                       else 'fold' if abs(mu_at.imag) < 5e-2 else 'NS')
                cross = (0.5*(elo+ehi), typ)
                break
            xL, eps = xn, e_try
            deps = min(deps*1.4, 5e-3)
        for e, am, m in hist[-4:]:
            out(f"    eps={e:.4e} max|mult|={am:.5f} mult={m:.4f}")
        if cross is None:
            out(f"  RESULT D {name}: no tongue below eps=0.10 (10% V pump)")
        else:
            et, typ = cross
            # consequence: simulate at 1.3x threshold, check bounded
            ev, dsad = escape_event(pr)
            frc = lambda t: {'V': pr['V']*1.3*et*math.cos(wp*t)}
            s = simulate(pr, st + np.array([1e-4, 0, 0, 0]), 120.0,
                         forcing=frc, events=ev, rtol=1e-9)
            esc = len(s.t_events[0]) > 0
            dmax = float(np.max(np.abs(s.y[0] - st[0])))
            wmax = float(np.max(np.abs(s.y[1])))
            out(f"  RESULT D {name}: tongue eps={et:.4e} type={typ}; "
                f"at 1.3x: escape={esc} max|d-d0|={dmax:.4f} "
                f"max|om|={wmax:.4f}  (supercritical => bounded expected)")
    out(f"DONE wall={time.time()-T0:.0f}s")

# ---------------------- E: kick-threshold erosion -------------------------
elif MODE == 'E':
    for name in ('M1', 'M2'):
        b = build(name)
        if b is None:
            out(f"{name}: no Hopf boundary — skip")
            continue
        pr, st, w0, alpha = b['pr'], b['st'], b['w0'], b['alpha']
        ev, dsad = escape_event(pr)
        out(f"{name}: P0={pr['Pref']:.4f} alpha={alpha:.4f} w0={w0:.4f} "
            f"d0={st[0]:.4f} d_saddle={dsad:.4f}")
        def kick_escapes(eps, wpb, xb, tk, dw, Tf=80.0):
            xk = xb.copy(); xk[1] += dw
            def f(t, x):
                qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wpb*t)))
                return rhs(x, qq)
            s = solve_ivp(f, (tk, tk+Tf), xk, method='DOP853', rtol=1e-9,
                          atol=1e-12, events=ev)
            return len(s.t_events[0]) > 0
        def dwc(eps, wpb):
            # settle under forcing, then worst over 4 drive phases
            if eps > 0:
                Tset = 60.0
                def f(t, x):
                    qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wpb*t)))
                    return rhs(x, qq)
                s = solve_ivp(f, (0, Tset), st.copy(), method='DOP853',
                              rtol=1e-9, atol=1e-12)
                xb0 = s.y[:, -1]
                Tdp = 2*math.pi/wpb
            else:
                Tset, xb0, Tdp = 0.0, st.copy(), 1.0
            vals = []
            for jph in range(4 if eps > 0 else 1):
                tk = Tset + jph*Tdp/4
                if eps > 0 and jph > 0:
                    def f(t, x):
                        qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wpb*t)))
                        return rhs(x, qq)
                    s2 = solve_ivp(f, (Tset, tk), xb0, method='DOP853',
                                   rtol=1e-10, atol=1e-13)
                    xb = s2.y[:, -1]
                else:
                    xb = xb0.copy()
                lo2, hi2 = 0.0, 2.0
                while not kick_escapes(eps, wpb, xb, tk, hi2) and hi2 < 40:
                    hi2 *= 2
                for _ in range(9):
                    dm = 0.5*(lo2+hi2)
                    if kick_escapes(eps, wpb, xb, tk, dm): hi2 = dm
                    else: lo2 = dm
                vals.append(0.5*(lo2+hi2))
            return min(vals), vals
        d0, _ = dwc(0.0, w0)
        out(f"  dwc(0) = {d0:.4f} rad/s")
        for wpb, tag in ((w0, 'res'), (0.7*w0, 'off')):
            for eb in (0.005, 0.01, 0.02):
                if tag == 'off' and eb != 0.01:
                    continue
                dmin, vals = dwc(eb, wpb)
                out(f"  RESULT E {name} {tag} eps_bg={eb:.3f}: "
                    f"dwc={dmin:.4f}  erosion={1-dmin/d0:+.1%}  "
                    f"(phases: " + ", ".join(f"{v:.3f}" for v in vals) + ")")
    out(f"DONE wall={time.time()-T0:.0f}s")

# ---------------------- F: slow drift through P_H -------------------------
elif MODE == 'F':
    b = build('M1')
    if b is None:
        out("M1: no Hopf boundary — abort"); sys.exit()
    pr, st, P_H, alpha, w0 = b['pr'], b['st'], b['P_H'], b['alpha'], b['w0']
    P0 = pr['Pref']
    dP = P0 - P_H
    ev, dsad = escape_event(pr)
    out(f"M2: P_H={P_H:.4f} P0={P0:.4f} margin dP={dP:.4f} "
        f"alpha={alpha:.4f} w0={w0:.4f}")
    for ws in (0.1, 0.5):
        for fdip in (0.5, 1.5, 3.0):
            a = fdip*dP
            frc = lambda t: {'Pref': -a*math.sin(ws*t)}
            Tt = 2*(2*math.pi/ws)
            s = simulate(pr, st + np.array([1e-5, 0, 0, 0]), Tt,
                         forcing=frc, events=ev, rtol=1e-9)
            esc = len(s.t_events[0]) > 0
            tt = np.linspace(0, s.t[-1], 6000)
            ys = s.sol(tt)
            wmax = float(np.max(np.abs(ys[1])))
            dmax = float(np.max(np.abs(ys[0] - st[0])))
            # onset delay for the dipping case: first time |omega|
            # exceeds 10x its pre-dip level vs time Pref first < P_H
            det = ''
            if fdip > 1.0 and not esc:
                tin = (math.asin(min(1, dP/a)))/ws
                base = np.max(np.abs(ys[1][tt < 0.5*tin])) + 1e-12
                idx = np.where((np.abs(ys[1]) > 10*base) & (tt > tin))[0]
                if len(idx):
                    det = f" onset_delay={tt[idx[0]]-tin:.2f}s"
            out(f"  RESULT F ws={ws} dip={fdip:.1f}x margin: escape={esc} "
                f"max|om|={wmax:.4f} max|d-d0|={dmax:.4f}{det}")
    out(f"DONE wall={time.time()-T0:.0f}s")
