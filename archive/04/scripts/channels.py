"""Frequency-channel vs amplitude-channel decomposition.
GFL: freq channel = (theta, x_pll); amp channel = (Vdc, xi).
GFM: freq channel = (delta, omega); amp channel = (Qf -> E).
Per case: (1) critical-mode channel shares from the eigenvector;
(2) escape trajectory: which channel limit trips first
    (|dtheta|>1.2 vs |dVdc|>{2%,5%,10%}; delta>dsad vs |dE|>{2%,5%,10%});
(3) bounded states (weak-class jump / GFM forced response): per-channel
    swings. Budget: ~5 min (short integrations only).
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/channels.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def build_gfl(over, marg):
    prb = gset('G1', **over)
    Psn = 3*prb['V']**2/(4*prb['Xg'])
    def reA(P):
        q = dict(prb, P=P)
        x = equil(q)
        if x is None: return None
        cm = crit_mode(jac(x, q))
        return None if cm is None else cm.real
    grid = np.linspace(0.05, 0.985, 60)*Psn
    va = [reA(P) for P in grid]
    br = None
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a, b); break
    lo, hi = br
    for _ in range(45):
        m = 0.5*(lo+hi)
        v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    P = margin_point(prb, 0.5*(lo+hi), marg)
    pr = dict(prb, P=P)
    return pr, nf_coeffs(pr)

GFL = [
    ('G1 ref',   {},              0.10, 1.1865e-4, 'strong'),
    ('Xg=0.70',  dict(Xg=0.70),   0.10, 4.0434e-4, 'strong'),
    ('C=0.02',   dict(C=0.02),    0.10, 8.2643e-4, 'strong'),
    ('V=1.06',   dict(V=1.06),    0.10, 6.6170e-3, 'weak'),
]
for tag, over, marg, epsc, cls in GFL:
    pr, co = build_gfl(over, marg)
    st = co['st']; w0 = co['w0']
    qn = co['q']/np.linalg.norm(co['q'])
    sf = math.hypot(abs(qn[0]), abs(qn[1]))
    sa = math.hypot(abs(qn[2]), abs(qn[3]))
    out(f"{tag} ({cls}): f0={w0/2/math.pi:.2f}Hz "
        f"|q|=({abs(qn[0]):.3f},{abs(qn[1]):.3f},{abs(qn[2]):.3f},"
        f"{abs(qn[3]):.3f}) freq_share={sf:.3f} amp_share={sa:.3f}")
    wd = 0.9*w0
    eps = 1.1*epsc
    def f(t, x):
        qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return rhs(x, qq)
    evs = []
    def ev_th(t, x): return abs(x[0] - st[0]) - 1.2
    ev_th.terminal = (cls == 'strong'); ev_th.direction = 1
    def ev_v2(t, x): return abs(x[2] - st[2]) - 0.02
    def ev_v5(t, x): return abs(x[2] - st[2]) - 0.05
    def ev_v10(t, x): return abs(x[2] - st[2]) - 0.10
    for e in (ev_v2, ev_v5, ev_v10):
        e.terminal = False; e.direction = 1
    T = 250 if cls == 'weak' else 400
    s = solve_ivp(f, (0, T), st.copy(), method='DOP853', rtol=1e-9,
                  atol=1e-12, events=[ev_th, ev_v2, ev_v5, ev_v10],
                  dense_output=True)
    tth = s.t_events[0][0] if len(s.t_events[0]) else None
    tv = [s.t_events[i][0] if len(s.t_events[i]) else None
          for i in (1, 2, 3)]
    if cls == 'strong':
        if tth is not None:
            xa = s.sol(np.linspace(0, tth, 2000))
            vmax = float(np.max(np.abs(xa[2] - st[2])))
            out(f"  escape@1.1x eps_c: theta hits 1.2 at t={tth:.1f}s; "
                f"max|dVdc| before = {vmax:.4f} "
                f"(Vdc 2%/5%/10% crossings at t={tv})")
        else:
            out("  no theta escape in window?!")
    else:
        tt = np.linspace(0.4*T, T, 3000)
        xa = s.sol(tt)
        out(f"  bounded jump state @1.1x flip: theta-swing="
            f"{float(np.max(np.abs(xa[0]-st[0]))):.3f} rad, "
            f"Vdc-swing={float(np.max(np.abs(xa[2]-st[2]))):.4f} pu "
            f"(2%/5%/10% crossings: t={tv}); theta hit 1.2: "
            f"{'yes' if tth is not None else 'no'}")

# ---- GFM M1 ----
import importlib
sys_path_hack = True
from gfmlib import (rhs as grhs, jac as gjac, equil as gequil,
                    crit_mode as gcrit, maxre_cx, hopf_in, mset, fold,
                    escape_event, Enom)
from scipy.linalg import eig as _eig
pr = mset('M1', Xg=0.10)
dfold, Pm = fold(pr)
qh = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
P_H = qh['Pref']
def g(P):
    r = maxre_cx(dict(pr, Pref=P))
    return 1.0 if r is None else r
Phi_ = min(0.95*Pm, 2.5*P_H)
tt_ = 0.10
if g(Phi_) > -tt_:
    tt_ = max(0.3*abs(g(Phi_)), 0.02)
lo2, hi2 = P_H, Phi_
for _ in range(45):
    m = 0.5*(lo2+hi2)
    if g(m) > -tt_: lo2 = m
    else: hi2 = m
prm = dict(pr, Pref=0.5*(lo2+hi2))
stm = gequil(prm)
A = gjac(stm, prm)
lam = gcrit(A)
ev_, VL, VR = _eig(A, left=True, right=True)
k = int(np.argmin(np.abs(ev_ - lam)))
qn = VR[:, k]/np.linalg.norm(VR[:, k])
# E sensitivity: dE = -mq*dQf
E0 = Enom - prm['mq']*(stm[3] - prm['Qref'])
sf = math.hypot(abs(qn[0]), abs(qn[1]))
sE = prm['mq']*abs(qn[3])
out(f"GFM M1: f0={lam.imag/2/math.pi:.2f}Hz "
    f"|q|=({abs(qn[0]):.3f},{abs(qn[1]):.3f},{abs(qn[2]):.3f},"
    f"{abs(qn[3]):.3f}) freq_share={sf:.3f} |dE|-weight={sE:.4f} E0={E0:.3f}")
evx, dsad = escape_event(prm)
dw0 = 32.8125
xk = stm.copy(); xk[1] += 1.05*dw0
def fg(t, x): return grhs(x, prm)
def eE2(t, x): return abs((Enom - prm['mq']*(x[3]-prm['Qref'])) - E0) - 0.02*E0
def eE5(t, x): return abs((Enom - prm['mq']*(x[3]-prm['Qref'])) - E0) - 0.05*E0
def eE10(t, x): return abs((Enom - prm['mq']*(x[3]-prm['Qref'])) - E0) - 0.10*E0
for e in (eE2, eE5, eE10):
    e.terminal = False; e.direction = 1
s = solve_ivp(fg, (0, 40), xk, method='DOP853', rtol=1e-9, atol=1e-12,
              events=[evx, eE2, eE5, eE10], dense_output=True)
tds = s.t_events[0][0] if len(s.t_events[0]) else None
tE = [s.t_events[i][0] if len(s.t_events[i]) else None for i in (1, 2, 3)]
if tds is not None:
    xa = s.sol(np.linspace(0, tds, 2000))
    Ee = Enom - prm['mq']*(xa[3]-prm['Qref'])
    out(f"  kick escape @1.05x dw0: delta over saddle at t={tds:.2f}s; "
        f"max|dE|/E0 before = {float(np.max(np.abs(Ee-E0)))/E0:.4f} "
        f"(E 2%/5%/10% crossings t={tE})")
# forced response 1% resonant: per-channel swings
wp = lam.imag
def ff(t, x):
    qq = dict(prm, V=prm['V']*(1 + 0.01*math.cos(wp*t)))
    return grhs(x, qq)
s = solve_ivp(ff, (0, 100), stm.copy(), method='DOP853', rtol=1e-9,
              atol=1e-12, dense_output=True)
tt2 = np.linspace(60, 100, 3000)
xa = s.sol(tt2)
Ee = Enom - prm['mq']*(xa[3]-prm['Qref'])
out(f"  forced 1% resonant: delta-swing="
    f"{float(np.max(np.abs(xa[0]-stm[0]))):.4f} rad, om-swing="
    f"{float(np.max(np.abs(xa[1]))):.3f}, |dE|/E0-swing="
    f"{float(np.max(np.abs(Ee-E0)))/E0:.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
