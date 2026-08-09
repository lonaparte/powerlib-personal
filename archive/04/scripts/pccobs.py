"""Restate the threshold in the quantities that are actually measured at
the point of connection, and separate the two disturbance protocols.

pccmap already showed that the critical PCC state is nearly independent
of which channel drove it (G1: |v| swing 0.53-0.55%, P swing 0.44-0.46%
at 0.9 eps_c on the V, P and Q channels), which is what makes a
PCC-referred criterion possible at all.  Two things were missing.

(1) The observable set stopped at |v|, P, Q.  Instability is seen as
    frequency and current oscillation too, so both are added here:
    GFL frequency is the PLL output thetadot = kp v_gq + ki x_pll, and
    the PCC current is (i_d, i_q) = (kpv(1-Vdc)+kiv xi, Q).

(2) Only the sudden-onset protocol was measured.  The closed form gives
    the two protocols as two different branches of the same equation:
      switched on at once -> the switch-on kick |Z(0)| = eps J must
                             already exceed the shrunken guard rho_g;
      raised slowly       -> no kick, so escape waits until the guard
                             itself vanishes, alpha_eff = 0, i.e.
                             eps_ramp = 2 sqrt(alpha / Re c_x).
    Both are measured against the prediction, and the PCC observables are
    reported at each.
Sets: G1 (angle family) and idx2 (DC family), V channel, r = 0.9.
Budget ~15 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/pccobs.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'm4', 'exec'), _ns)
cx_hand = _ns['cx_hand']; hopf = _ns['hopf']

def obs(x, prq):
    """PCC observables from the state."""
    th, xp, Vdc, xi = x
    idq = prq['kpv']*(1 - Vdc) + prq['kiv']*xi
    iq = prq['Q']
    vd = prq['V']*math.cos(th) - prq['Xg']*iq
    vq = -prq['V']*math.sin(th) + prq['Xg']*idq
    Pp = 1.5*(vd*idq + vq*iq)
    Qp = 1.5*(vq*idq - vd*iq)
    fr = (prq['kp']*vq + prq['ki']*xp)/(2*math.pi)
    return dict(Vm=math.hypot(vd, vq), P=Pp, Q=Qp,
                Im=math.hypot(idq, iq), f=fr, Vdc=Vdc)
KEYS = ('Vm', 'P', 'Q', 'Im', 'f', 'Vdc')

for tag, over in (('G1 angle family', {}),
                  ('idx2 DC family', dict(kp=30., ki=600.))):
    prb = gset('G1', **over)
    PH = hopf(prb)
    P0 = margin_point(prb, PH, 0.10)
    pr = dict(prb, P=P0); co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']
    lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
    A = jac(st, pr); rg = math.sqrt(alpha/c1.real)
    dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
    wp = 0.9*w0; Td = 2*math.pi/wp
    hs = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+hs))
          - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
    cx = cx_hand(A, st, pr, qv, pv, w0, wp, fV)
    J = abs(lam)*abs(np.vdot(pv, fV))/abs(wp**2 + lam**2)
    o0 = obs(st, pr)
    out(f"=== {tag}: P0={P0:.5f}, w0={w0:.3f} rad/s ({w0/(2*math.pi):.2f} Hz)"
        f", r_g={rg:.4e}")
    out("    steady PCC: " + "  ".join(f"{k}={o0[k]:+.5f}" for k in KEYS))
    def run(eps, ramp, NP=400):
        """ramp=0: switched on at t=0; ramp>0: envelope raised over
        `ramp` drive periods, then held."""
        def f(t, x):
            e = eps*min(1.0, t/(ramp*Td)) if ramp > 0 else eps
            return rhs(x, dict(pr, V=pr['V'] + e*math.cos(wp*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, (NP+ramp)*Td), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi),
                      dense_output=True)
        esc = any(len(t) > 0 for t in s.t_events) or s.status < 0
        return esc, s
    def thr(ramp, seed):
        lo, hi = 0.5*seed, 1.6*seed
        n = 0
        while not run(hi, ramp)[0] and n < 14:
            lo = hi; hi *= 1.3; n += 1
        n = 0
        while run(lo, ramp)[0] and n < 14:
            hi = lo; lo *= 0.75; n += 1
        for _ in range(15):
            m = 0.5*(lo+hi)
            if run(m, ramp)[0]: hi = m
            else: lo = m
        return 0.5*(lo+hi)
    seed = rg/J
    e_sud = thr(0, seed)
    e_ramp = thr(300, seed)
    e_sud_pred = None
    lo, hi = 1e-12, 8*seed
    for _ in range(200):
        m = 0.5*(lo+hi); a2 = 0.25*m*m
        aeff = alpha - cx.real*a2
        rgv = math.sqrt(aeff/c1.real) if aeff > 0 else -1.0
        if rgv < 0 or m*J > rgv: hi = m
        else: lo = m
    e_sud_pred = 0.5*(lo+hi)
    e_ramp_pred = 2*math.sqrt(alpha/cx.real)
    out(f"    threshold, switched on : measured {e_sud:.5e}  closed form "
        f"{e_sud_pred:.5e} ({(e_sud_pred-e_sud)/e_sud*100:+.2f}%)")
    out(f"    threshold, raised slowly: measured {e_ramp:.5e}  closed form "
        f"2 sqrt(alpha/Re c_x) = {e_ramp_pred:.5e} "
        f"({(e_ramp_pred-e_ramp)/e_ramp*100:+.2f}%)   slow/sudden = "
        f"{e_ramp/e_sud:.3f}  [{time.time()-T0:.0f}s]")
    for lab, eps in (('0.9 x sudden threshold', 0.9*e_sud),
                     ('0.9 x slow threshold', 0.9*e_ramp)):
        esc, s = run(eps, 300, NP=120)
        tt = np.linspace(s.t[-1]-40*Td, s.t[-1], 4000)
        Y = s.sol(tt)
        rec = {k: [] for k in KEYS}
        for i in range(len(tt)):
            o = obs(Y[:, i], dict(pr, V=pr['V']+eps*math.cos(wp*tt[i])))
            for k in KEYS:
                rec[k].append(o[k])
        out(f"    PCC swing at {lab} (eps={eps:.4e}):")
        line = []
        for k in KEYS:
            arr = np.array(rec[k]); sw = 0.5*(arr.max()-arr.min())
            base = abs(o0[k]) if abs(o0[k]) > 1e-9 else 1.0
            pctref = ('%' if abs(o0[k]) > 1e-9 else ' abs')
            line.append(f"{k} {sw:.4e}"
                        + (f" ({sw/base*100:.3f}%)" if pctref == '%' else ""))
        out("        " + " | ".join(line) + f"  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
