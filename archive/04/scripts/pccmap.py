"""Re-express the criteria in PCC observables (the physically measured
port quantities), and check the network constraint.

Exogenous causes (independent): V = far grid EMF behind Xg, P = DC-side
power, Q = reactive current command.
PCC quantities (dependent, 2 DOF under the network constraint):
  v_d = V cos(th) - Xg*Q,  v_q = -V sin(th) + Xg*i_d   (PLL frame)
  |v|, P_pcc = 1.5(v_d i_d + v_q i_q), Q_pcc = 1.5(v_q i_d - v_d i_q)
with i_d = kpv(1-Vdc)+kiv*xi, i_q = Q.

Per set, at EACH channel's own critical amplitude (0.9 x eps_c, safely
inside), measure the PCC-side oscillation triple and:
 (1) test channel-independence of the critical PCC state;
 (2) extract each channel's PCC signature (relative amplitudes/phases)
     -> a source-identification rule;
 (3) verify the network constraint P_pcc = |v| V sin(ang)/Xg pointwise.
Sets: G1 (strong/angle family), idx2 (weak/DC family). Budget ~6 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/pccmap.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

SETS = [
    dict(tag='G1 strong', over={}, marg=0.10,
         eps={'V': 1.1865e-4, 'P': 2.7914e-4, 'Q': 3.0097e-4}),
    dict(tag='idx2 weak', over=dict(kp=30., ki=600.), marg=0.10,
         eps={'V': 7.40969e-3, 'P': 1.0855e-2, 'Q': 1.3119e-2}),
]

def pcc(x, prq):
    th, xp, Vdc, xi = x
    idq = prq['kpv']*(1 - Vdc) + prq['kiv']*xi
    iq = prq['Q']
    vd = prq['V']*math.cos(th) - prq['Xg']*iq
    vq = -prq['V']*math.sin(th) + prq['Xg']*idq
    Vm = math.hypot(vd, vq)
    Ppcc = 1.5*(vd*idq + vq*iq)
    Qpcc = 1.5*(vq*idq - vd*iq)
    # angle of v_pcc relative to the far EMF (EMF is at angle -th)
    ang_v = math.atan2(vq, vd)
    ang_e = math.atan2(-prq['V']*math.sin(th), prq['V']*math.cos(th))
    return Vm, Ppcc, Qpcc, (ang_v - ang_e), idq, iq

for S in SETS:
    prb = gset('G1', **S['over'])
    Psn = 3*prb['V']**2/(4*prb['Xg'])
    def reA(P):
        q = dict(prb, P=P); x = equil(q)
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
        m = 0.5*(lo+hi); v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    P0 = margin_point(prb, 0.5*(lo+hi), S['marg'])
    pr = dict(prb, P=P0)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; wd = 0.9*w0
    Vm0, Pp0, Qp0, angp0, id0, iq0 = pcc(st, pr)
    out(f"{S['tag']}: P0={P0:.5f} w0={w0:.3f} | PCC steady: "
        f"|v|={Vm0:.5f} P={Pp0:.5f} Q={Qp0:.5f} "
        f"ang(v,e)={math.degrees(angp0):+.3f}deg i_d={id0:.4f}")
    # network constraint check at the operating point
    Pnet = Vm0*pr['V']*math.sin(-angp0)/pr['Xg']
    out(f"  network check: P_pcc(direct)={Pp0:.5f} vs "
        f"|v|V sin/Xg={Pnet:.5f} (ratio {Pp0/Pnet:.4f} = 1.5 power scaling)")
    for key in ('V', 'P', 'Q'):
        u0 = pr[key]; a = 0.9*S['eps'][key]
        def f(t, x):
            return rhs(x, dict(pr, **{key: u0 + a*math.cos(wd*t)}))
        s = solve_ivp(f, (0, 220.0), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, dense_output=True)
        Tp = 2*math.pi/wd
        tt = np.linspace(220 - 6*Tp, 220, 8000)
        X = s.sol(tt)
        arr = np.array([pcc(X[:, i],
                            dict(pr, **{key: u0 + a*math.cos(wd*tt[i])}))
                        for i in range(len(tt))])
        Vm, Pp, Qp, angp = arr[:, 0], arr[:, 1], arr[:, 2], arr[:, 3]
        dV = 0.5*(Vm.max()-Vm.min())
        dP = 0.5*(Pp.max()-Pp.min())
        dQ = 0.5*(Qp.max()-Qp.min())
        dVdc = 0.5*(X[2].max()-X[2].min())
        # relative phases (fundamental, via projection on drive)
        c = np.cos(wd*tt); sn = np.sin(wd*tt)
        def ph(y):
            yy = y - y.mean()
            A = 2*np.mean(yy*c); B = 2*np.mean(yy*sn)
            return math.degrees(math.atan2(B, A)), math.hypot(A, B)
        phV, amV = ph(Vm); phP, amP = ph(Pp); phQ, amQ = ph(Qp)
        out(f"  u={key} @0.9eps_c={a:.3e}:  PCC |v| swing={dV:.4e} "
            f"({dV/Vm0*100:.3f}%)  P swing={dP:.4e} ({dP/abs(Pp0)*100:.3f}%)"
            f"  Q swing={dQ:.4e}  Vdc swing={dVdc:.4e}")
        out(f"       signature (fund. amp; phase rel. drive): "
            f"|v|={amV:.3e}@{phV:+.1f}deg  P={amP:.3e}@{phP:+.1f}deg  "
            f"Q={amQ:.3e}@{phQ:+.1f}deg   dP/dV={amP/amV:.3f} "
            f"dQ/dV={amQ/amV:.3f} [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
