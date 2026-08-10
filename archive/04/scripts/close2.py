"""Two things I left as "named absences" instead of predicting a number.

The recurring failure across three self-audit rounds is stopping where a
cause can be NAMED rather than where a number can be PREDICTED.  Two items
currently on record are exactly that, and both are implementable now.

 (1) Multi-tone residual 0.5% (max 1.54%).  Recorded as "two named
     contributors, which dominates is unseparated".  One of the two -- the
     fifth-order terms in non-autonomous form -- was not implemented, and
     that is a choice, not a limitation.  The consistent form follows from
     the same rule that fixed c_x: every place the autonomous theory writes
     |a|^2, the non-autonomous one writes the INSTANTANEOUS squared
     envelope.  With E2(t) = |sum_k a_k e^{i w_k t}|^2 and E(t) the c_x-
     weighted version already in use,

         zetadot = lam zeta + [c1 + c_xx E2(t)] zeta |zeta|^2
                   + c2 zeta |zeta|^4 + [E(t) + c_a4 E2(t)^2] zeta

     (the a^4 term enters with a PLUS, like the c_x term, because
     alpha_eff = alpha - Re c_x|a|^2 - Re c_a4|a|^4 and lam = -alpha + i w0;
     and E2^2 rather than sum_k |a_k|^4 is what the degenerate-limit
     argument in noise1h established.)  Previous attempt used the
     time-averaged a2t for c_xx and the per-tone sum for c_a4 -- both
     inconsistent, which is why that control was inconclusive.

 (2) GFM at w_p = 0.3 w0 still leaves 1.30-1.50%.  I dropped the transfer
     factor s_0/|s(w)| when I added the passage term, but that factor is
     ~1.7% at rat = 0.3 -- the same size as the leftover.  The two
     corrections address different things and should compose: the transfer
     factor converts drive amplitude into static-equivalent gap closure,
     the passage term says how far past the static fold you must go.  So

         eps_c |s(w_p)|/s_0 = eps_qs + w_p sqrt(eps_qs/(2ab))
         ==>  eps_c = (s_0/|s(w_p)|) [ eps_qs + w_p sqrt(eps_qs/(2ab)) ]

     Neither piece is new; what was missing is putting them together.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re, math
import numpy as np
LOG = open('sweep20/close2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']
hs = 1e-6

# ================================================================ part 1
prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
w0H = coH['w0']
AH = jac(stH, prH)
evH, VLH, VRH = eig(AH, left=True, right=True)
kH = max((i for i in range(4) if evH[i].imag > 1e-9),
         key=lambda i: evH[i].real)
lamH = evH[kH]; qH = VRH[:, kH]; pH = VLH[:, kH]; pH = pH/np.vdot(qH, pH)
fuH = (rhs(stH, dict(prH, V=prH['V']+hs))
       - rhs(stH, dict(prH, V=prH['V']-hs)))/(2*hs)
SYH = {P_: prH['P'], Q_: prH['Q'], V_: prH['V'], Xg_: prH['Xg'],
       kp_: prH['kp'], ki_: prH['ki'], kpv_: prH['kpv'],
       kiv_: prH['kiv'], C_: prH['C']}
DkV = make_tensors5(sp, f_, _x, SYH, prH, stH, V_)
R5 = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H, DkV, param=True)
R5a = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H, DkV, param=False)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr)
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx_ref = cx_hand(A, st, pr, qv, pv, w0, 0.90*w0, fV).real
dpar = R5['c_x'].real - R5a['c_x'].real
par_frac = dpar/(cx_ref + dpar)
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
c1r = c1.real; rg0 = math.sqrt(alpha/c1r)
_cache = {}


def cx_of(wk):
    k = round(wk, 9)
    if k not in _cache:
        _cache[k] = cx_hand(A, st, pr, qv, pv, w0, wk, fV).real \
            / (1.0 - par_frac)
    return _cache[k]


def patch(N, lo, hi, seed):
    rng = np.random.default_rng(seed)
    rs = np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)])
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


def kick_c(tu, eps):
    Z = 0.0 + 0j
    for wk, rk, ph in tu:
        aa = 0.5*eps*rk*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (aa*np.vdot(pv, Hp) + np.conj(aa)*np.vdot(pv, Hm))
    return Z


def red_escape(tu, eps, mode):
    ws = np.array([wk for wk, _, _ in tu])
    aa = np.array([0.5*eps*rk*np.exp(1j*ph) for _, rk, ph in tu])
    cxv = np.array([cx_of(wk) for wk in ws])
    ac = cxv*aa
    Z0 = kick_c(tu, eps)
    lim = 3.0*rg0

    def EE(t):
        e = np.exp(1j*ws*t)
        s1 = np.dot(aa, e)
        return (float(np.real(np.dot(ac, e)*np.conj(s1))),
                float(abs(s1)**2))

    def f(t, y):
        z = y[0] + 1j*y[1]
        r2 = abs(z)**2
        Ecx, E2 = EE(t)
        if mode == 'cubic':
            dz = (-alpha + 0j)*z + c1*z*r2 + Ecx*z
        else:                       # consistent non-autonomous fifth order
            dz = ((-alpha + 0j)*z + (c1 + cxxr*E2)*z*r2 + c2r*z*r2*r2
                  + (Ecx + ca4r*E2*E2)*z)
        return [dz.real, dz.imag]

    def ev(t, y):
        return math.hypot(y[0], y[1]) - lim
    ev.terminal = True; ev.direction = 1

    def dead(t, y):
        return math.hypot(y[0], y[1]) - 1e-4*rg0
    dead.terminal = True; dead.direction = -1
    s = solve_ivp(f, (0, 60.0/alpha), [Z0.real, Z0.imag], method='DOP853',
                  rtol=1e-9, atol=1e-18, events=(ev, dead))
    return len(s.t_events[0]) > 0 or s.status < 0


def red_thr(tu, seed, mode):
    lo, hi = 0.6*seed, 1.4*seed
    n = 0
    while not red_escape(tu, hi, mode) and n < 14:
        lo = hi; hi *= 1.25; n += 1
    n = 0
    while red_escape(tu, lo, mode) and n < 14:
        hi = lo; lo *= 0.8; n += 1
    if red_escape(tu, lo, mode) or not red_escape(tu, hi, mode):
        return float('nan')
    for _ in range(24):
        m = 0.5*(lo+hi)
        if red_escape(tu, m, mode): hi = m
        else: lo = m
    return 0.5*(lo+hi)


CASES = []
for ln in open('sweep20/noise1b.log').read().split('\n'):
    m = re.match(r'\s*(\d+)\s*\|\s*[\d.]+\s*\|\s*[\d.]+\s*\|\s*'
                 r'([\d.eE+-]+)\s*\|', ln)
    if m:
        CASES.append((f'0.85-0.95 s7  N={m.group(1):>3s}',
                      patch(int(m.group(1)), 0.85, 0.95, 7),
                      float(m.group(2))))
for ln in open('sweep20/noise1c.log').read().split('\n'):
    m = re.match(r'\s*([\d.]+)-([\d.]+)\s+s(\d+)\s*\|\s*(\d+)\s*\|'
                 r'\s*[\d.]+\s*\|\s*([\d.eE+-]+)\s*\|', ln)
    if m:
        lo_, hi_ = float(m.group(1)), float(m.group(2))
        if hi_ > 0.93:
            continue
        CASES.append((f'{lo_}-{hi_} s{m.group(3):<2s} N={m.group(4):>3s}',
                      patch(int(m.group(4)), lo_, hi_, int(m.group(3))),
                      float(m.group(5))))

out("=== 1. multi-tone: consistent non-autonomous fifth order")
out("   every |a|^2 of the autonomous theory becomes the instantaneous")
out("   |alpha_tot(t)|^2; c_a4 uses E2^2 (degenerate-limit form), not "
    "sum_k|a_k|^4")
out("  cell                    | cubic ODE | +consistent 5th | a^4/alpha")
e3 = []; e5 = []
for tag, tu, em in CASES:
    p3 = red_thr(tu, em, 'cubic')
    p5 = red_thr(tu, p3 if p3 == p3 else em, 'fifth')
    d3 = (p3-em)/em*100; d5 = (p5-em)/em*100
    e3.append(abs(d3)); e5.append(abs(d5))
    a4f = ca4r*(0.25*em*em)**2/alpha*100
    out(f"  {tag} | {d3:+8.2f}% | {d5:+14.2f}% | {a4f:6.2f}%")
e3 = np.array(e3); e5 = np.array(e5)
out(f"    mean |err|  cubic {e3.mean():.3f}%  ->  fifth {e5.mean():.3f}%")
out(f"    max  |err|  cubic {e3.max():.3f}%  ->  fifth {e5.max():.3f}%")
out(f"    cells improved: {int((e5 < e3).sum())}/{len(e3)}   "
    f"[{time.time()-T0:.0f}s]")

# ================================================================ part 2
import gfmlib as G
from scipy.linalg import eig as _eig
HS = 1e-6
out("")
out("=== 2. GFM: transfer factor and passage term composed")
out("    eps_c = (s_0/|s(w)|) [ eps_qs + w sqrt(eps_qs/(2ab)) ]")


def quasi_static(prq):
    def gapf(u):
        q = dict(prq, V=prq['V']-u)
        try:
            _, Pm = G.fold(q)
        except Exception:
            return 1.0
        return prq['Pref'] - Pm
    lo, hi = 0.0, 0.999*prq['V']
    for _ in range(80):
        m = 0.5*(lo+hi)
        if gapf(m) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)


def fu_of(stx, prx):
    return (G.rhs(stx, dict(prx, V=prx['V']+HS))
            - G.rhs(stx, dict(prx, V=prx['V']-HS)))/(2*HS)


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90,
          {0.05: 1.04422e-1, 0.10: 1.09632e-1, 0.30: 1.30762e-1}),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90,
          {0.05: 9.73921e-2, 0.10: 9.98985e-2, 0.30: 1.10610e-1}),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75,
          {0.05: 2.56257e-1, 0.10: 2.65446e-1, 0.30: 3.03603e-1}),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90,
          {0.05: 9.24648e-2, 0.10: 9.43543e-2, 0.30: 1.00537e-1})]
out("  cell |  w/w0 | passage only | + transfer factor | s_0/|s|")
allp = []; allt = []
for tag, nm, Xg, frac, meas in CELLS:
    _, Pm0 = G.fold(G.mset(nm, Xg=Xg))
    prg = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    stg = G.equil(prg); Ag = G.jac(stg, prg)
    w0g = G.crit_mode(Ag).imag
    eqs = quasi_static(prg)
    prf = dict(prg, V=prg['V'] - eqs)
    df, _ = G.fold(prf, n=200000)
    E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    stf = np.array([df, 0.0, prf['Pref'], Qf])
    evf, VLf, VRf = _eig(G.jac(stf, prf), left=True, right=True)
    kf = int(np.argmin(np.abs(evf)))
    vR = np.real(VRf[:, kf]); wL = np.real(VLf[:, kf]); wL = wL/np.dot(wL, vR)
    a_sn = float(np.dot(wL, -fu_of(stf, prf)))
    b_sn = 0.5*float(np.dot(wL, G.Bform(stf, prf, vR, vR)))
    ab = abs(a_sn*b_sn)
    xs = G.equil(prg, branch='saddle'); As = G.jac(xs, prg)
    evs, VLs, _ = _eig(As, left=True, right=True)
    ks = int(np.argmax(evs.real))
    nv = np.real(VLs[:, ks]); nv = nv/np.linalg.norm(nv)
    if np.dot(nv, xs - stg) < 0:
        nv = -nv
    fu0 = fu_of(stg, prg); fus = fu_of(xs, prg)
    s0 = abs(float(np.dot(nv, -np.linalg.solve(Ag, fu0)
                          + np.linalg.solve(As, fus))))
    for r in (0.05, 0.10, 0.30):
        wp = r*w0g
        I = np.eye(4)
        H = np.linalg.solve(1j*wp*I - Ag, fu0.astype(complex))
        Hs = np.linalg.solve(1j*wp*I - As, fus.astype(complex))
        sw = abs(np.dot(nv, H - Hs))
        base = eqs + wp*math.sqrt(eqs/(2*ab))
        p_pass = base
        p_full = base*s0/sw
        m_ = meas[r]
        allp.append(abs((p_pass-m_)/m_*100)); allt.append(abs((p_full-m_)/m_*100))
        out(f"   {tag[0]}   | {r:.2f}  | {(p_pass-m_)/m_*100:+11.2f}% | "
            f"{(p_full-m_)/m_*100:+16.2f}% | {s0/sw:.5f}")
allp = np.array(allp); allt = np.array(allt)
out(f"    max |err|  passage only {allp.max():.2f}%  ->  "
    f"+transfer {allt.max():.2f}%")
out(f"    mean |err| passage only {allp.mean():.2f}%  ->  "
    f"+transfer {allt.mean():.2f}%   [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
